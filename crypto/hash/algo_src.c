#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <string.h>
#include <intrin.h>

#define C1 0x5D7E0D1F2E0F1F84
#define C2 0x388D76AEE8CB1500
#define C3 0xD2E9EE7E83C4285B

uint64_t hash(uint64_t v)
{
	v*=C1;
	v=_lrotr(v, v&0xF); // rotate right
	v^=C2;
	v=_lrotl(v, v&0xF); // rotate left
	v+=C3;
	v=_lrotl(v, v % 60); // rotate left
	return v;
};

int main()
{
	printf ("%llu\n", hash(...));
};
