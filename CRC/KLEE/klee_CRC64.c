#include <string.h>
#include <stdint.h>

uint64_t crc64(uint64_t crc, unsigned char *buf, int len)
{
	int k;

	crc = ~crc;
	while (len--)
	{
		crc ^= *buf++;
		for (k = 0; k < 8; k++)
			crc = crc & 1 ? (crc >> 1) ^ 0x42f0e1eba9ea3693 : crc >> 1;
	}
	return crc;
}

int main()
{
#define HEAD_STR "Hello, world!.. "
#define HEAD_SIZE strlen(HEAD_STR)
#define TAIL_STR " ... and goodbye"
#define TAIL_SIZE strlen(TAIL_STR)
#define MID_SIZE 14 // work
#define BUF_SIZE HEAD_SIZE+TAIL_SIZE+MID_SIZE

	char buf[BUF_SIZE];
  
	klee_make_symbolic(buf, sizeof buf, "buf");

	klee_assume (memcmp (buf, HEAD_STR, HEAD_SIZE)==0);

	for (int i=0; i<MID_SIZE; i++)
		klee_assume (buf[HEAD_SIZE+i]>='a' && buf[HEAD_SIZE+i]<='z');

	klee_assume (memcmp (buf+HEAD_SIZE+MID_SIZE, TAIL_STR, TAIL_SIZE)==0);
	
	klee_assume (crc64 (0, buf, BUF_SIZE)==0x12345678abcdef12);

	klee_assert(0);

	return 0;
}
