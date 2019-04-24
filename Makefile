all: utlsf

utlsf : utlsf.c
	$(CC) -Og -g -std=c99 -static -m32 $< -o $@

CLEAN=$(filter clean,$(MAKECMDGOALS))

.PHONY: clean
all: | $(CLEAN)

clean:
	rm -f utlsf
