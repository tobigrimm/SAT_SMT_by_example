#include <assert.h>
#include <stdio.h>
#include <stdint.h>

// copypasted and reworked from MMIXware:
uint64_t MOR(uint64_t y, uint64_t z)
{
  uint64_t o,x,a,c;
  int k;
  for (k=0,o=y,x=0; o; k++,o=o>>8)
    if (o&0xff) {
      a=((z>>k)&0x0101010101010101)*0xff;
      c=(o&0xff)*0x0101010101010101;
      x|=a&c;
    }
  return x;
}


uint64_t a;
uint64_t b;
uint64_t c;
uint64_t d;
uint64_t e;

uint64_t pgm(uint64_t x)
{
    uint64_t t=MOR(x,a);
    uint64_t s=t<<4;
    t=s^t;
    t=t&b;
    t=t+c;
    s=MOR(d,t);
    t=t+e;
    uint64_t y=t+s;
    return y;
	
};

char *hex="0123456789abcdef";

uint64_t method2(uint64_t x)
{
	uint64_t rt=0;
	for (int i=0; i<8; i++)
		rt|=(uint64_t)hex[(x >> i*4)&0xf] << i*8;
	return rt;
};

int main()
{
// D.Knuth:
	a=0x0008000400020001;
	b=0x0f0f0f0f0f0f0f0f;
	c=0x0606060606060606;
	d=0x0000002700000000;
	e=0x2a2a2a2a2a2a2a2a;
/*
	a=0x8000400020001;
	b=0xf0f0f0f0f0f0f0f;
	c=0x56d656d616969616;
	d=0x411a00000000;
	e=0xbf3fbf3fff7f8000;
*/
	for (uint32_t i=0; ; i++)
	{
		if (pgm(i)!=method2(i))
		{
			printf ("i=%llx\n", i);
			printf ("your version=%llx\n", pgm(i));
			printf ("must be=%llx\n", method2(i));
		};
		if (i==0xffffffff)
			break;
	};
};

