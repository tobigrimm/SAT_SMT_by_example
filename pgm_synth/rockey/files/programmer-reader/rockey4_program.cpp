#include <windows.h>
#include <stdio.h>
#include <assert.h>

#include "ryvc32.h"

int main(int argc, char* argv[])
{
	WORD handle[16], p1, p2, p3, p4, retcode;
	DWORD lp1, lp2;
	BYTE buffer[1024];
	WORD rc[4];
	int passwords[4];

	printf ("ROCKEY4 dongle programmer <dennis@yurichev.com>\n");

	if (argc!=6)
	{
		printf ("Usage: %s password1 password2 password3 password4 \"algorithm string\"\n", argv[0]);
		printf ("Passwords should be in hexadecimal form.\n");
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

	p1=0;
	retcode = Rockey(RY_WRITE_ARITHMETIC, &handle[0], &lp1, &lp2, &p1, &p2, &p3, &p4, (BYTE*)argv[5]);
	if (retcode)
	{
		printf ("Error while RY_WRITE_ARITHMETIC: ");
		if (retcode==ERR_AR_WRONGBEGIN)
			printf ("Const number can't use on first arithmetic instruction\n");
		else if (retcode==ERR_AR_WRONG_END)
		        printf ("Const number can't use on last arithmetic instruction\n");
		else if (retcode==ERR_AR_VALUEOVERFLOW)
		        printf ("Const number > 63\n");
		else if (retcode==ERR_AR_UNKNOWN_OPCODE)
		        printf ("Arithmetic operator error\n");
		else
			printf ("%d\n", retcode);
		return 3;
	}

	retcode = Rockey(RY_CLOSE, &handle[0], &lp1, &lp2, &p1, &p2, &p3, &p4, buffer);
	if (retcode)
	{
		printf ("Error while RY_CLOSE: %d\n", retcode);
		return 4;
	}

	printf ("Success (algorithm string=\"%s\")\n", argv[5]);
	return 0;
}
