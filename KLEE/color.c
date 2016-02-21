#include <string.h>
#include <stdio.h>
#include <stdint.h>

void HTML_color(uint8_t R, uint8_t G, uint8_t B, char* out)
{
	if (R==0xFF && G==0 && B==0)
	{
		strcpy (out, "red");
		return;
	};
	
	if (R==0x0 && G==0xFF && B==0)
	{
		strcpy (out, "green");
		return;
	};
	
	if (R==0 && G==0 && B==0xFF)
	{
		strcpy (out, "blue");
		return;
	};
	
	// abbreviated hexadecimal
	if (R>>4==(R&0xF) && G>>4==(G&0xF) && B>>4==(B&0xF))
	{
		sprintf (out, "#%X%X%X", R&0xF, G&0xF, B&0xF);
		return;
	};

	// last resort
	sprintf (out, "#%02X%02X%02X", R, G, B);
};

int main()
{
	uint8_t R, G, B;
	klee_make_symbolic (&R, sizeof R, "R");
	klee_make_symbolic (&G, sizeof R, "G");
	klee_make_symbolic (&B, sizeof R, "B");
	
	char tmp[16];

	HTML_color(R, G, B, tmp);
};

