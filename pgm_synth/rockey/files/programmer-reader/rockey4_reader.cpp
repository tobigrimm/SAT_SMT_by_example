#include <windows.h>
#include <stdio.h>
#include <assert.h>

#include "ryvc32.h"

// rand

/* Period parameters */  
#define N 624
#define M 397
#define MATRIX_A 0x9908b0df   /* constant vector a */
#define UPPER_MASK 0x80000000 /* most significant w-r bits */
#define LOWER_MASK 0x7fffffff /* least significant r bits */

/* Tempering parameters */   
#define TEMPERING_MASK_B 0x9d2c5680
#define TEMPERING_MASK_C 0xefc60000
#define TEMPERING_SHIFT_U(y)  (y >> 11)
#define TEMPERING_SHIFT_S(y)  (y << 7)
#define TEMPERING_SHIFT_T(y)  (y << 15)
#define TEMPERING_SHIFT_L(y)  (y >> 18)

static unsigned long mt[N]; /* the array for the state vector  */
static int mti=N+1; /* mti==N+1 means mt[N] is not initialized */

/* initializing the array with a NONZERO seed */
void sgenrand (unsigned long seed)
{
	/* setting initial seeds to mt[N] using         */
	/* the generator Line 25 of Table 1 in          */
	/* [KNUTH 1981, The Art of Computer Programming */
	/*    Vol. 2 (2nd Ed.), pp102]                  */
	mt[0]= seed & 0xffffffff;
	for (mti=1; mti<N; mti++)
		mt[mti] = (69069 * mt[mti-1]) & 0xffffffff;
}

unsigned long genrand()
{
	unsigned long y;
	static unsigned long mag01[2]={0x0, MATRIX_A};
	/* mag01[x] = x * MATRIX_A  for x=0,1 */

	if (mti >= N) { /* generate N words at one time */
		int kk;

		if (mti == N+1)   /* if sgenrand() has not been called, */
			sgenrand(4357); /* a default initial seed is used   */

		for (kk=0;kk<N-M;kk++) {
			y = (mt[kk]&UPPER_MASK)|(mt[kk+1]&LOWER_MASK);
			mt[kk] = mt[kk+M] ^ (y >> 1) ^ mag01[y & 0x1];
		}
		for (;kk<N-1;kk++) {
			y = (mt[kk]&UPPER_MASK)|(mt[kk+1]&LOWER_MASK);
			mt[kk] = mt[kk+(M-N)] ^ (y >> 1) ^ mag01[y & 0x1];
		}
		y = (mt[N-1]&UPPER_MASK)|(mt[0]&LOWER_MASK);
		mt[N-1] = mt[M-1] ^ (y >> 1) ^ mag01[y & 0x1];

		mti = 0;
	}

	y = mt[mti++];
	y ^= TEMPERING_SHIFT_U(y);
	y ^= TEMPERING_SHIFT_S(y) & TEMPERING_MASK_B;
	y ^= TEMPERING_SHIFT_T(y) & TEMPERING_MASK_C;
	y ^= TEMPERING_SHIFT_L(y);

	return y; 
}

int rand_reg (int begin, int end)
{
	if (end<=begin)
	{
		printf ("rand_reg (%d, %d)\n", begin, end);
		assert (0);
	};

	return (genrand()/(0xFFFFFFFF/(end-begin+1)))+begin;
};

int main(int argc, char* argv[])
{
	WORD handle[16], p1, p2, p3, p4, retcode;
	DWORD lp1, lp2;
	BYTE buffer[1024];
	WORD rc[4];
	int passwords[4];

	printf ("ROCKEY4 dongle reader <dennis@yurichev.com>\n");

	if (argc!=5)
	{
		printf ("Usage: %s password1 password2 password3 password4\n");
		printf ("Passwords must be in hexadecimal form.\n");
		return 5;
	};

	for (int i=0; i<4; i++)
		if (sscanf (argv[1+i], "%x", &passwords[i])!=1)
		{
			printf ("Password %s not parsed\n", argv[1+i]);
			return 5;
		};

	p1=passwords[0];
	p2=passwords[1];
	p3=passwords[2];
	p4=passwords[3];

	retcode = Rockey(RY_FIND, &handle[0], &lp1, &lp2, &p1, &p2, &p3, &p4, buffer);
	if (retcode)
	{
		printf ("Error while RY_FIND: ");
		if (retcode==ERR_INVALID_PASSWORD)
			printf ("Found rockey dongle, but base password is wrong\n");
		else
			printf ("%d\n", retcode);
		return 1;
	}
	printf("ROCKEY4 Hardware ID (HID): 0x%08X\n", lp1);
	retcode = Rockey(RY_OPEN, &handle[0], &lp1, &lp2, &p1, &p2, &p3, &p4, buffer);
	if (retcode)
	{
		printf ("Error while RY_OPEN: %d\n", retcode);
		return 2;
	}

	// read memory
	for (WORD i=0;i!=1024;i++)
	{
		p1=i;
		p2=1;
		retcode = Rockey(RY_READ, &handle[0], &lp1, &lp2, &p1, &p2, &p3, &p4, buffer);
		if (retcode==0)
			printf ("memory cell 0x%04X: 0x%02X\n", i, buffer[0]);
		else
			break;
	};

	// check module presence
	for (WORD i=0;i!=16;i++)
	{
		p1=i;
		retcode = Rockey(RY_CHECK_MOUDLE, &handle[0], &lp1, &lp2, &p1, &p2, &p3, &p4, buffer);
		if (retcode)
		{
			printf ("Error while RY_CHECK_MOUDLE: ");
			printf ("%d\n", retcode);
			return 2;
		}
		if (p2)
			printf ("module %d may be used and not zero\n", i);
	};
	
	sgenrand(GetTickCount());

	for (int i=0; i<1000; i++)
	{
		lp1 = 0; // start point of calculation
		lp2 = 0; // module number
		p1 = genrand()&0xFFFF;
		p2 = genrand()&0xFFFF;
		p3 = genrand()&0xFFFF;
		p4 = genrand()&0xFFFF;
		printf ("RY_CALCULATE1: (input) p1=%d p2=%d p3=%d p4=%d ", p1, p2, p3, p4);
		retcode = Rockey(RY_CALCULATE1, &handle[0], &lp1, &lp2, &p1, &p2, &p3, &p4, buffer);
		if (retcode!=0)
		{
			printf ("Error while RY_CALCULATE1: %d\n", retcode);
			break;
	        };
		printf ("(output) p1=%d p2=%d p3=%d p4=%d\n", p1, p2, p3, p4);
	};

	retcode = Rockey(RY_CLOSE, &handle[0], &lp1, &lp2, &p1, &p2, &p3, &p4, buffer);
	if (retcode)
	{
		printf ("Error while RY_CLOSE: %d\n", retcode);
		return 4;
	}

	return 0;
}
