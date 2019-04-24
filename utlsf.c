#include <assert.h>
#include <unistd.h>
#include <stdio.h>
#include <stdint.h>
#include <stdalign.h>
#include <stddef.h>
#include <string.h>

typedef void* utlsf_ptr_t;
typedef uint32_t utlsf_size_t;

static inline void* utlsf_zptrd(utlsf_ptr_t ptr)
{
    return ptr;
}

static inline utlsf_ptr_t utlsf_zptre(void* ptr)
{
    return ptr;
}

enum utlsf_private
{
    SL_INDEX_COUNT_LOG2 = 2,
    /* All allocation sizes and addresses are aligned to 4 bytes. */
    ALIGN_SIZE_LOG2 = 2,

    ALIGN_SIZE = (1 << ALIGN_SIZE_LOG2),

    /*
     ** We support allocations of sizes up to (1 << FL_INDEX_MAX) bits.
     ** However, because we linearly subdivide the second-level lists, and
     ** our minimum size granularity is 4 bytes, it doesn't make sense to
     ** create first-level lists for sizes smaller than SL_INDEX_COUNT * 4,
     ** or (1 << (SL_INDEX_COUNT_LOG2 + 2)) bytes, as there we will be
     ** trying to split size ranges into more slots than we have available.
     ** Instead, we calculate the minimum threshold size, and place all
     ** blocks below that size into the 0th first-level list.
     */

    FL_INDEX_MAX = 16,
    SL_INDEX_COUNT = (1 << SL_INDEX_COUNT_LOG2),
    FL_INDEX_SHIFT = (SL_INDEX_COUNT_LOG2 + ALIGN_SIZE_LOG2),
    FL_INDEX_COUNT = (FL_INDEX_MAX - FL_INDEX_SHIFT + 1),

    SMALL_BLOCK_SIZE = (1 << FL_INDEX_SHIFT),
};

#define BLOCK_NULL &utlsf->block_null

typedef struct {
    utlsf_ptr_t prev_phys_block;
    utlsf_size_t size;
    utlsf_ptr_t next_free;
    utlsf_ptr_t prev_free;
} utlsf_block_hdr_t;

typedef struct {
    /* maximum allocation size for this utlsf instance */
    utlsf_size_t max_alloc_size_log2;

    /* Empty lists point at this block to indicate they are free. */
    utlsf_block_hdr_t block_null;

    /* Bitmaps for free lists. */
    unsigned int fl_bitmap;
    uint8_t *sl_bitmap;

    /* Head of free lists. */
    utlsf_ptr_t data[];
} utlsf_t;

static inline utlsf_ptr_t *get_free_list_head(utlsf_t *utlsf, unsigned fl, unsigned sl)
{
    return (utlsf_ptr_t *)((uintptr_t)utlsf->data + (((fl * SL_INDEX_COUNT) + sl) * sizeof(utlsf_ptr_t)));
}

static inline int fls(unsigned int word)
{
    const int bit = word ? 32 - __builtin_clz(word) : 0;
    return bit - 1;
}

static inline int ffs(unsigned int word)
{
    return __builtin_ffs(word) - 1;
}

/*
 * Cast and min/max macros.
 */

#define utlsf_cast(t, exp)	((t) (exp))
#define utlsf_min(a, b)		((a) < (b) ? (a) : (b))
#define utlsf_max(a, b)		((a) > (b) ? (a) : (b))

/*
 * Since block sizes are always at least a multiple of 4, the two least
 * significant bits of the size field are used to store the block status:
 * - bit 0: whether block is busy or free
 * - bit 1: whether previous block is busy or free
*/
static const size_t block_header_free_bit = 1 << 0;
static const size_t block_header_prev_free_bit = 1 << 1;

/*
 * The size of the block header exposed to used blocks is the size field.
 * The prev_phys_block field is stored *inside* the previous free block.
*/
static const size_t block_header_overhead = sizeof(utlsf_size_t);

/* User data starts directly after the size field in a used block. */
static const size_t block_start_offset =
    offsetof(utlsf_block_hdr_t, size) + sizeof(utlsf_size_t);

/*
 * A free block must be large enough to store its header minus the size of
 * the prev_phys_block field, and no larger than the number of addressable
 * bits for FL_INDEX.
*/
static const size_t block_size_min =
    sizeof(utlsf_block_hdr_t) - sizeof(utlsf_ptr_t);
static const size_t block_size_max = utlsf_cast(size_t, 1) << FL_INDEX_MAX;

/*
 * utlsf_block_hdr_t member functions.
*/

static size_t block_size(const utlsf_block_hdr_t *block)
{
    return block->size & ~(block_header_free_bit | block_header_prev_free_bit);
}

static void block_set_size(utlsf_block_hdr_t *block, size_t size)
{
    const size_t oldsize = block->size;

    block->size = size | (oldsize & (block_header_free_bit | block_header_prev_free_bit));
}

static int block_is_last(const utlsf_block_hdr_t *block)
{
    return 0 == block_size(block);
}

static int block_is_free(const utlsf_block_hdr_t *block)
{
    return utlsf_cast(int, block->size & block_header_free_bit);
}

static void block_set_free(utlsf_block_hdr_t *block)
{
    block->size |= block_header_free_bit;
}

static void block_set_used(utlsf_block_hdr_t *block)
{
    block->size &= ~block_header_free_bit;
}

static int block_is_prev_free(const utlsf_block_hdr_t *block)
{
    return utlsf_cast(int, block->size & block_header_prev_free_bit);
}

static void block_set_prev_free(utlsf_block_hdr_t *block)
{
    block->size |= block_header_prev_free_bit;
}

static void block_set_prev_used(utlsf_block_hdr_t *block)
{
    block->size &= ~block_header_prev_free_bit;
}

static utlsf_block_hdr_t *block_from_ptr(const void *ptr)
{
    return utlsf_cast(utlsf_block_hdr_t *,
                     utlsf_cast(unsigned char *, ptr) - block_start_offset);
}

static void *block_to_ptr(const utlsf_block_hdr_t *block)
{
    return utlsf_cast(void *,
                     utlsf_cast(unsigned char *, block) + block_start_offset);
}

/* Return location of next block after block of given size. */
static utlsf_block_hdr_t *offset_to_block(const void *ptr, size_t size)
{
    return utlsf_cast(utlsf_block_hdr_t *, utlsf_cast(ptrdiff_t, ptr) + size);
}

/* Return location of previous block. */
static utlsf_block_hdr_t *block_prev(const utlsf_block_hdr_t *block)
{
    return block->prev_phys_block;
}

/* Return location of next existing block. */
static utlsf_block_hdr_t *block_next(const utlsf_block_hdr_t *block)
{
    utlsf_block_hdr_t *next = offset_to_block(block_to_ptr(block),
                                              block_size(block) - block_header_overhead);

    assert(!block_is_last(block));
    return next;
}

/* Link a new block with its physical neighbor, return the neighbor. */
static utlsf_block_hdr_t *block_link_next(utlsf_block_hdr_t *block)
{
    utlsf_block_hdr_t *next = block_next(block);

    next->prev_phys_block = block;
    return next;
}

static void block_mark_as_free(utlsf_block_hdr_t *block)
{
    /* Link the block to the next block, first. */
    utlsf_block_hdr_t *next = block_link_next(block);

    block_set_prev_free(next);
    block_set_free(block);
}

static void block_mark_as_used(utlsf_block_hdr_t *block)
{
    utlsf_block_hdr_t *next = block_next(block);

    block_set_prev_used(next);
    block_set_used(block);
}

static size_t align_up(size_t x, size_t align)
{
    assert(0 == (align & (align - 1)) && "must align to a power of two");
    return (x + (align - 1)) & ~(align - 1);
}

static size_t align_down(size_t x, size_t align)
{
    assert(0 == (align & (align - 1)) && "must align to a power of two");
    return x - (x & (align - 1));
}

static void *align_ptr(const void *ptr, size_t align)
{
    const ptrdiff_t aligned =
        (utlsf_cast(ptrdiff_t, ptr) + (align - 1)) & ~(align - 1);

    assert(0 == (align & (align - 1)) && "must align to a power of two");
    return utlsf_cast(void *, aligned);
}

/*
 * Adjust an allocation size to be aligned to word size, and no smaller
 * than internal minimum.
 */
static size_t adjust_request_size(size_t size, size_t align)
{
    size_t adjust = 0;

    if (size && size < block_size_max) {
        const size_t aligned = align_up(size, align);
        adjust = utlsf_max(aligned, block_size_min);
    }
    return adjust;
}

static void mapping_insert(size_t size, int *fli, int *sli)
{
    int fl, sl;

    if (size < SMALL_BLOCK_SIZE) {
        /* Store small blocks in first list. */
        fl = 0;
        sl = utlsf_cast(int, size) / (SMALL_BLOCK_SIZE / SL_INDEX_COUNT);
    }
    else {
        fl = fls(size);
        sl = utlsf_cast(int, size >> (fl - SL_INDEX_COUNT_LOG2)) ^ (1 << SL_INDEX_COUNT_LOG2);
        fl -= (FL_INDEX_SHIFT - 1);
    }
    *fli = fl;
    *sli = sl;
}

/* This version rounds up to the next block size (for allocations) */
static void mapping_search(size_t size, int* fli, int* sli)
{
    if (size >= (1 << SL_INDEX_COUNT_LOG2))
    {
        const size_t round = (1 << (fls(size) - SL_INDEX_COUNT_LOG2)) - 1;
        size += round;
    }
    mapping_insert(size, fli, sli);
}

static utlsf_block_hdr_t* search_suitable_block(utlsf_t *pool, int* fli, int* sli)
{
    int fl = *fli;
    int sl = *sli;

    /*
     ** First, search for a block in the list associated with the given
     ** fl/sl index.
     */
    unsigned int sl_map = pool->sl_bitmap[fl] & (~0U << sl);
    if (!sl_map)
    {
        /* No block exists. Search in the next largest first-level list. */
        const unsigned int fl_map = pool->fl_bitmap & (~0U << (fl + 1));
        if (!fl_map)
        {
            /* No free blocks available, memory has been exhausted. */
            return 0;
        }

        fl = ffs(fl_map);
        *fli = fl;
        sl_map = pool->sl_bitmap[fl];
    }
    assert(sl_map && "internal error - second level bitmap is null");
    sl = ffs(sl_map);
    *sli = sl;

    /* Return the first block in the free list. */
    return (utlsf_block_hdr_t*)*get_free_list_head(pool, fl, sl);
}

/* Remove a free block from the free list.*/
static void remove_free_block(utlsf_t *utlsf, utlsf_block_hdr_t *block, int fl, int sl)
{
    utlsf_block_hdr_t *prev = block->prev_free;
    utlsf_block_hdr_t *next = block->next_free;

    //assert(prev && "prev_free field can not be null");
    //assert(next && "next_free field can not be null");
    if (next) {
        next->prev_free = prev;
    }
    if (prev) {
        prev->next_free = next;
    }

    utlsf_block_hdr_t **list_head = get_free_list_head(utlsf, fl, sl);
    /* If this block is the head of the free list, set new head. */
    if (*list_head == block) {
        *list_head = next;

        /* If the new head is null, clear the bitmap. */
        if (next == BLOCK_NULL) {
            utlsf->sl_bitmap[fl] &= ~(1 << sl);

            /* If the second bitmap is now empty, clear the fl bitmap. */
            if (!utlsf->sl_bitmap[fl]) {
                utlsf->fl_bitmap &= ~(1 << fl);
            }
        }
    }
}

/* Insert a free block into the free block list. */
static void insert_free_block(utlsf_t *utlsf, utlsf_block_hdr_t *block, int fl, int sl)
{
    utlsf_block_hdr_t **list_head = get_free_list_head(utlsf, fl, sl);
    utlsf_block_hdr_t *current = *list_head;

    printf("current=%p %p\n", current, list_head);
    assert(current && "free list cannot have a null entry");
    assert(block && "cannot insert a null entry into the free list");
    block->next_free = current;
    block->prev_free = BLOCK_NULL;
    current->prev_free = block;

    assert(block_to_ptr(block) == align_ptr(block_to_ptr(block), ALIGN_SIZE)
           && "block not aligned properly");
    /*
    ** Insert the new block at the head of the list, and mark the first-
    ** and second-level bitmaps appropriately.
    */
    *list_head = block;
    utlsf->fl_bitmap |= (1 << fl);
    utlsf->sl_bitmap[fl] |= (1 << sl);
}

/* Remove a given block from the free list. */
static void block_remove(utlsf_t *utlsf, utlsf_block_hdr_t *block)
{
    int fl, sl;

    mapping_insert(block_size(block), &fl, &sl);
    remove_free_block(utlsf, block, fl, sl);
}

/* Insert a given block into the free list. */
static void block_insert(utlsf_t *utlsf, utlsf_block_hdr_t *block)
{
    int fl, sl;

    mapping_insert(block_size(block), &fl, &sl);
    printf("block_insert() fl=%i sl=%i\n", fl, sl);
    insert_free_block(utlsf, block, fl, sl);
}

static int block_can_split(utlsf_block_hdr_t *block, size_t size)
{
    return block_size(block) >= sizeof(utlsf_block_hdr_t) + size;
}

/* Split a block into two, the second of which is free. */
static utlsf_block_hdr_t *block_split(utlsf_block_hdr_t *block, size_t size)
{
    /* Calculate the amount of space left in the remaining block. */
    utlsf_block_hdr_t *remaining =
        offset_to_block(block_to_ptr(block), size - block_header_overhead);

    const size_t remain_size = block_size(block) - (size + block_header_overhead);

    assert(block_to_ptr(remaining) == align_ptr(block_to_ptr(remaining), ALIGN_SIZE)
           && "remaining block not aligned properly");

    assert(block_size(block) == remain_size + size + block_header_overhead);
    block_set_size(remaining, remain_size);
    assert(block_size(remaining) >= block_size_min && "block split with invalid size");

    block_set_size(block, size);
    block_mark_as_free(remaining);

    return remaining;
}

/* Absorb a free block's storage into an adjacent previous free block. */
static utlsf_block_hdr_t *block_absorb(utlsf_block_hdr_t *prev, utlsf_block_hdr_t *block)
{
    assert(!block_is_last(prev) && "previous block can't be last!");
    /* Note: Leaves flags untouched. */
    prev->size += block_size(block) + block_header_overhead;
    block_link_next(prev);
    return prev;
}

/* Merge a just-freed block with an adjacent previous free block. */
static utlsf_block_hdr_t *block_merge_prev(utlsf_t *utlsf, utlsf_block_hdr_t *block)
{
    if (block_is_prev_free(block)) {
        utlsf_block_hdr_t *prev = block_prev(block);
        assert(prev && "prev physical block can't be null");
        assert(block_is_free(prev) && "prev block is not free though marked as such");
        block_remove(utlsf, prev);
        block = block_absorb(prev, block);
    }

    return block;
}

/* Merge a just-freed block with an adjacent free block. */
static utlsf_block_hdr_t *block_merge_next(utlsf_t *utlsf, utlsf_block_hdr_t *block)
{
    utlsf_block_hdr_t *next = block_next(block);

    assert(next && "next physical block can't be null");

    if (block_is_free(next)) {
        assert(!block_is_last(block) && "previous block can't be last!");
        block_remove(utlsf, next);
        block = block_absorb(block, next);
    }

    return block;
}

/* Trim any trailing block space off the end of a block, return to pool. */
static void block_trim_free(utlsf_t *utlsf, utlsf_block_hdr_t *block, size_t size)
{
    assert(block_is_free(block) && "block must be free");
    if (block_can_split(block, size)) {
        utlsf_block_hdr_t *remaining_block = block_split(block, size);
        block_link_next(block);
        block_set_prev_free(remaining_block);
        block_insert(utlsf, remaining_block);
    }
}

/* Trim any trailing block space off the end of a used block, return to pool. */
static void block_trim_used(utlsf_t *utlsf, utlsf_block_hdr_t *block, size_t size)
{
    assert(!block_is_free(block) && "block must be used");
    if (block_can_split(block, size)) {
        /* If the next block is free, we must coalesce. */
        utlsf_block_hdr_t *remaining_block = block_split(block, size);
        block_set_prev_used(remaining_block);

        remaining_block = block_merge_next(utlsf, remaining_block);
        block_insert(utlsf, remaining_block);
    }
}

static utlsf_block_hdr_t *block_trim_free_leading(utlsf_t *utlsf, utlsf_block_hdr_t *block, size_t size)
{
    utlsf_block_hdr_t *remaining_block = block;

    if (block_can_split(block, size)) {
        /* We want the 2nd block. */
        remaining_block = block_split(block, size - block_header_overhead);
        block_set_prev_free(remaining_block);

        block_link_next(block);
        block_insert(utlsf, block);
    }

    return remaining_block;
}

static utlsf_block_hdr_t *block_locate_free(utlsf_t *utlsf, size_t size)
{
    int fl = 0, sl = 0;
    utlsf_block_hdr_t *block = 0;

    if (size) {
        mapping_search(size, &fl, &sl);
        printf("block_locate_free() fl=%i sl=%i\n", fl, sl);
        block = search_suitable_block(utlsf, &fl, &sl);
    }

    if (block) {
        assert(block_size(block) >= size);
        remove_free_block(utlsf, block, fl, sl);
    }

    return block;
}

static void *block_prepare_used(utlsf_t *utlsf, utlsf_block_hdr_t *block, size_t size)
{
    void *p = 0;

    if (block) {
        block_trim_free(utlsf, block, size);
        block_mark_as_used(block);
        p = block_to_ptr(block);
    }
    return p;
}

void *utlsf_malloc(utlsf_t *utlsf, size_t size)
{
    const size_t adjust = adjust_request_size(size, ALIGN_SIZE);
    printf("utlsf_malloc() adjust=%u\n", adjust);
    utlsf_block_hdr_t* block = block_locate_free(utlsf, adjust);
    return block_prepare_used(utlsf, block, adjust);
}

void utlsf_free(utlsf_t *utlsf, void* ptr)
{
    /* Don't attempt to free a NULL pointer. */
    if (ptr)
    {
        utlsf_block_hdr_t* block = block_from_ptr(ptr);
        assert(!block_is_free(block) && "block already marked as free");
        block_mark_as_free(block);
        block = block_merge_prev(utlsf, block);
        block = block_merge_next(utlsf, block);
        block_insert(utlsf, block);
    }
}

static unsigned _utlsf_fl_index_count(unsigned max_alloc_size_log2)
{
    return max_alloc_size_log2 - FL_INDEX_SHIFT + 1;
}

size_t utlsf_create(void *buf, utlsf_size_t max_alloc_size)
{
    unsigned max_alloc_size_log2 = fls(max_alloc_size) + 1;
    unsigned fl_index_count = _utlsf_fl_index_count(max_alloc_size_log2);
    printf("max_alloc_size_log2=%u fl_index_count=%u\n", max_alloc_size_log2, fl_index_count);
    unsigned free_list_count = (fl_index_count * SL_INDEX_COUNT) + 1;
    unsigned free_list_size = free_list_count * sizeof(uintptr_t);
    unsigned sl_bitmap_size = fl_index_count;
    unsigned total_size = sizeof(utlsf_t) + free_list_size + sl_bitmap_size;

    if (buf) {
        /* make sure heap is aligned to 8 bytes */
        assert (!((uintptr_t)buf & 0x7));

        utlsf_t *utlsf = buf;
        memset(utlsf, '\0', total_size);

        utlsf->max_alloc_size_log2 = max_alloc_size_log2;

        for (unsigned i = 0; i < free_list_count; i++) {
            utlsf_block_hdr_t **next = (utlsf_block_hdr_t**)((uintptr_t)utlsf->data + (i * sizeof(utlsf_ptr_t)));
            *next = &utlsf->block_null;
        }

        utlsf->sl_bitmap = buf + sizeof(utlsf_t) + free_list_size;

    }

    printf("utlsf: utlsf_t=%u free_list_size=%u fl_index_count=%u sl_bitmap_size=%u total=%u\n", \
            sizeof(utlsf_t), free_list_size, fl_index_count, sl_bitmap_size, total_size);

    return total_size;
}

/*
 * Overhead of the uTLSF structures in a given memory block passes to
 * utlsf_add_pool, equal to the overhead of a free block and the
 * sentinel block.
 */
size_t utlsf_pool_overhead()
{
    return 2 * block_header_overhead;
}

size_t utlsf_alloc_overhead()
{
    return block_header_overhead;
}

static size_t _utlsf_add_pool(utlsf_t *utlsf, void *mem, size_t bytes)
{
    utlsf_block_hdr_t* block;
    utlsf_block_hdr_t* next;

    const size_t pool_overhead = utlsf_pool_overhead();
    const size_t pool_bytes = align_down(bytes - pool_overhead, ALIGN_SIZE);

    printf("utlsf_add_pool() pool_overhead=%u pool_bytes=%u\n", pool_overhead, pool_bytes);
    assert(((ptrdiff_t)mem % ALIGN_SIZE) == 0);

    /*
     ** Create the main free block. Offset the start of the block slightly
     ** so that the prev_phys_block field falls outside of the pool -
     ** it will never be used.
     */
    block = offset_to_block(mem, -(ptrdiff_t)block_header_overhead);
    block_set_size(block, pool_bytes);
    block_set_free(block);
    block_set_prev_used(block);
    block_insert(utlsf, block);

    /* Split the block to create a zero-size sentinel block. */
    next = block_link_next(block);
    block_set_size(next, 0);
    block_set_used(next);
    block_set_prev_free(next);
    return pool_bytes + pool_overhead;
}

static void default_walker(void *ptr, size_t size, int used, void *user)
{
    (void)user;
    printf("\t%p %s size: %x (%p)\n", ptr, used ? "used" : "free", (unsigned int)size, block_from_ptr(ptr));
}

typedef void (*utlsf_walker_t)(void *ptr, size_t size, int used, void *user);

void utlsf_walk_pool(void* pool, utlsf_walker_t walker, void *user)
{
    utlsf_walker_t pool_walker = walker ? walker : default_walker;
    utlsf_block_hdr_t *block =
        offset_to_block(pool, -(int)block_header_overhead);

    while (block && !block_is_last(block)) {
        pool_walker(
            block_to_ptr(block),
            block_size(block),
            !block_is_free(block),
            user);
        block = block_next(block);
    }
}

void utlsf_walk_free(utlsf_t *utlsf)
{
    unsigned fl_index_count = _utlsf_fl_index_count(utlsf->max_alloc_size_log2);

    for (int i = 0; i < fl_index_count; ++i) {
        for (int j = 0; j < SL_INDEX_COUNT; ++j) {
            utlsf_block_hdr_t **_list_head = get_free_list_head(utlsf, i, j);
            utlsf_block_hdr_t *next = *_list_head;
            while (next != &utlsf->block_null) {
                printf("free block: %p %u\n", next, block_size(next));
                next = next->next_free;
            }
        }
    }
}

void utlsf_add_pool(utlsf_t *utlsf, void *mem, size_t bytes)
{
    void *mem_pos = mem;
    size_t left = bytes;
    size_t max_alloc_size = (size_t)1 << utlsf->max_alloc_size_log2;

    while (left > utlsf_pool_overhead()) {
        size_t pool_bytes = _utlsf_add_pool(utlsf, mem_pos, utlsf_min(max_alloc_size + utlsf_pool_overhead(), left));
        left -= pool_bytes;
        printf("utlsf: added pool at %p using %u bytes.\n", mem_pos, (unsigned) pool_bytes);
        mem_pos += pool_bytes;
    }
}

utlsf_t utlsf;
char heap[512*1024];

int main()
{
    printf("sizeof(utlsf) == %u\n", sizeof(utlsf));
    printf("FL_INDEX_COUNT == %u\n", FL_INDEX_COUNT);
    printf("SL_INDEX_COUNT == %u\n", SL_INDEX_COUNT);
    utlsf_create(&utlsf, (1<<17)-1);

    utlsf_add_pool(&utlsf, heap, sizeof(heap));
//    utlsf_walk_free(&utlsf);

    void *found = utlsf_malloc(&utlsf, 0x7fff);
    printf("got: %p\n", found);

//    void *found2 = utlsf_malloc(&utlsf, 257);
//    printf("got2: %p\n", found2);
//
//    void *found3 = utlsf_malloc(&utlsf, 60000);
//    printf("got3: %p\n", found3);

    utlsf_free(&utlsf, found);
    puts("freed 0");
}
