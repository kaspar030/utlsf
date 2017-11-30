all: utlsf

utlsf : utlsf.c
	$(CC) -Og -g -std=c99 -static -m32 $< -o $@

.PHONY: clean
all: | clean
clean:
	rm -f utlsf
