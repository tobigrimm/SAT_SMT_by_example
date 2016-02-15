// copypasted from http://www.opensource.apple.com/source/boot/boot-132/i386/boot2/lzss.c
//
#include <string.h>
#include <stdint.h>
#include <stdbool.h>

//#define N         4096  /* size of ring buffer - must be power of 2 */
#define N         32  /* size of ring buffer - must be power of 2 */
#define F         18    /* upper limit for match_length */
#define THRESHOLD 2     /* encode string into position and length
                           if match_length is greater than this */
#define NIL       N     /* index for root of binary search trees */
   
int
decompress_lzss(uint8_t *dst, uint8_t *src, uint32_t srclen)
{
    /* ring buffer of size N, with extra F-1 bytes to aid string comparison */
    uint8_t *dststart = dst;
    uint8_t *srcend = src + srclen;
    int  i, j, k, r, c;
    unsigned int flags;
    uint8_t text_buf[N + F - 1];
    
    dst = dststart;
    srcend = src + srclen;
    for (i = 0; i < N - F; i++)
        text_buf[i] = ' ';
    r = N - F;
    flags = 0;
    for ( ; ; ) {
        if (((flags >>= 1) & 0x100) == 0) {
            if (src < srcend) c = *src++; else break;
            flags = c | 0xFF00;  /* uses higher byte cleverly */
        }   /* to count eight */
        if (flags & 1) {
            if (src < srcend) c = *src++; else break;
            *dst++ = c;
            text_buf[r++] = c;
            r &= (N - 1);
        } else {
            if (src < srcend) i = *src++; else break;
            if (src < srcend) j = *src++; else break;
            i |= ((j & 0xF0) << 4);
            j  =  (j & 0x0F) + THRESHOLD;
            for (k = 0; k <= j; k++) {
                c = text_buf[(i + k) & (N - 1)];
                *dst++ = c;
                text_buf[r++] = c;
                r &= (N - 1);
            }
        }
    }
    
    return dst - dststart;
}

int main()
{
#define COMPRESSED_LEN 15
	uint8_t input[COMPRESSED_LEN];
	uint8_t plain[24];
	uint32_t size=COMPRESSED_LEN;
  
	klee_make_symbolic(input, sizeof input, "input");
	
	decompress_lzss(plain, input, size);

	// https://en.wikipedia.org/wiki/Buffalo_buffalo_Buffalo_buffalo_buffalo_buffalo_Buffalo_buffalo
	for (int i=0; i<23; i++)
		klee_assume (plain[i]=="Buffalo buffalo Buffalo"[i]);

	klee_assert(0);
	
	return 0;
}
