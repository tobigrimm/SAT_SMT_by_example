#include <assert.h>
#include <string.h>
#include <stdio.h>
#include <stdint.h>

// helpers:

uint32_t bitrev32(uint32_t x)
{
        uint32_t __x = x;
        __x = (__x >> 16) | (__x << 16);
        __x = ((__x & (uint32_t)0xFF00FF00UL) >> 8) | ((__x & (uint32_t)0x00FF00FFUL) << 8);
        __x = ((__x & (uint32_t)0xF0F0F0F0UL) >> 4) | ((__x & (uint32_t)0x0F0F0F0FUL) << 4);
        __x = ((__x & (uint32_t)0xCCCCCCCCUL) >> 2) | ((__x & (uint32_t)0x33333333UL) << 2);
        __x = ((__x & (uint32_t)0xAAAAAAAAUL) >> 1) | ((__x & (uint32_t)0x55555555UL) << 1);
        return __x;
}

uint32_t swap_endianness32 (uint32_t a)
{
        return ((a>>24)&0xff) |
                ((a<<8)&0xff0000) |
                ((a>>8)&0xff00) |
                ((a<<24)&0xff000000);
};

#define CRC32POLY 0x04c11db7

uint8_t *buf;
int buf_pos;
int buf_bit_pos;

int get_bit()
{
	if (buf_pos==-1)
		return -1; // end

	int rt=(buf[buf_pos] >> buf_bit_pos) & 1;
	if (buf_bit_pos==0)
	{
		buf_pos--;
		buf_bit_pos=7;
	}
	else
		buf_bit_pos--;
	return rt;
};

uint32_t remainder_arith(uint32_t dividend, uint32_t divisor)
{
	buf=(uint8_t*)&dividend;
	buf_pos=3;
	buf_bit_pos=7;

	uint32_t tmp=0;

	for(;;)
	{
		int bit=get_bit();
		if (bit==-1)
		{
			printf ("exit. remainder=%d\n", tmp);
			return tmp;
		};

		tmp=tmp<<1;
		tmp=tmp|bit;

		if (tmp>=divisor)
		{
			printf ("%d greater or equal to %d\n", tmp, divisor);
			tmp=tmp-divisor;
			printf ("new tmp=%d\n", tmp);
		}
		else
			printf ("tmp=%d, can't subtract\n", tmp);
	};
}

uint32_t remainder_GF2(uint32_t dividend, uint32_t divisor)
{
	// necessary bit shuffling/negation to make it compatible with other CRC32 implementations.
	// N.B.: input data is not an array, but a 32-bit integer, hence we need to swap endiannes.
	uint32_t dividend_negated_swapped = ~swap_endianness32(bitrev32(dividend));
	buf=(uint8_t*)&dividend_negated_swapped;
	buf_pos=3;
	buf_bit_pos=7;

	uint32_t tmp=0;

	// process 32 bits from the input + 32 zero bits:
	for(int i=0; i<32+32; i++)
	{
		int bit=get_bit();
		int shifted_bit=tmp>>31;

		// fetch next bit:
		tmp=tmp<<1;
		if (bit==-1)
		{
			// no more bits, but continue, we fetch 32 more zero bits.
			// shift left operation set leftmost bit to zero.
		}
		else
		{
			// append next bit at right:
			tmp=tmp|bit;
		};

		// at this point, tmp variable/value has 33 bits: shifted_bit + tmp
		// now take the most significant bit (33th) and test it:
		// 33th bit of polynomial (not present in "divisor" variable is always 1
		// so we have to only check shifted_bit value
		if (shifted_bit)
		{
			// use only 32 bits of polynomial, ingore 33th bit, which is always 1:
			tmp=tmp^divisor;
		};
	};
	// bit shuffling/negation for compatibility once again:
	return ~bitrev32(tmp);
}

int main ()
{
	assert (remainder_arith (1234567, 813) == 1234567 % 813);

	assert (remainder_GF2 (0, CRC32POLY) == 0x2144df1c);
	assert (remainder_GF2 (1, CRC32POLY) == 0x5643ef8a);
	assert (remainder_GF2 (0x10000000, CRC32POLY) == 0x715d8883);
	assert (remainder_GF2 (0x12345678, CRC32POLY) == 0x4a090e98);
	assert (remainder_GF2 (0xffffffff, CRC32POLY) == 0xffffffff);
};

