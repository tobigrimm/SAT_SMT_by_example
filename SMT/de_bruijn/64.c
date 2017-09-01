#include <stdint.h>
#include <stdio.h>
#include <assert.h>

#define MAGIC 0x79c52dd0991abf60

int magic_tbl[64];

// returns single bit position counting from LSB
// not works for i==0
int bitpos (uint64_t i)
{
	return magic_tbl[(MAGIC/i) & 0x3F];
};

// count trailing zeroes
// not works for i==0
int tzcnt (uint64_t i)
{
	uint64_t a=i & (-i);
	return magic_tbl[(MAGIC/a) & 0x3F];
};

int main()
{
	// construct magic table
	// may be omitted in production code
	for (int i=0; i<64; i++)
		magic_tbl[(MAGIC/(1ULL<<i)) & 0x3F]=i;

	// test
	for (int i=0; i<64; i++)
	{
		printf ("input=0x%llx, result=%d\n", 1ULL<<i, bitpos (1ULL<<i));
		assert(bitpos(1ULL<<i)==i);
	};
	assert(tzcnt (0xFFFF0000)==16);
	assert(tzcnt (0xFFFF0010)==4);
};

