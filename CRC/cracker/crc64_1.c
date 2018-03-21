#include <stdio.h>
#include <stdint.h>
#include <inttypes.h>

uint64_t CRC64(uint64_t crc, uint8_t *buf, size_t len)
{
        int k;

        crc = ~crc;
        while (len--)
        {
                crc ^= *buf++;
                for (k = 0; k < 8; k++)
                        crc = crc & 1UL ? (crc >> 1) ^ 0x42f0e1eba9ea3693UL : crc >> 1;
        }
        return crc;
}

int main()
{
	printf ("%"PRIx64"\n", CRC64 (0, "\x01", 1));
	printf ("%"PRIx64"\n", CRC64 (0, "\x02", 1));
};
