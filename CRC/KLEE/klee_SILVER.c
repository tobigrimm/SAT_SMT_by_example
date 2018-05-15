#include <stdint.h>
#include <stdbool.h>

uint32_t crc32(uint32_t crc, unsigned char *buf, int len)
{
    int k;

    crc = ~crc;
    while (len--)
    {
        crc ^= *buf++;
        for (k = 0; k < 8; k++)
            crc = crc & 1 ? (crc >> 1) ^ 0xedb88320 : crc >> 1;
    }
    return ~crc;
}

#define SIZE 6

bool find_string(char str[SIZE])
{
	int i=0;
	for (i=0; i<SIZE; i++)
		if (str[i]<'A' || str[i]>'Z')
			return false;

	if (crc32(0, &str[0], SIZE)!=0xDFA3DFDD)
		return false;

	// OK, input str is valid
	klee_assert(0); // force KLEE to produce .err file
	return true;
};

int main()
{
	uint8_t str[SIZE];
  
	klee_make_symbolic(str, sizeof str, "str");

	find_string(str);

	return 0;
}

