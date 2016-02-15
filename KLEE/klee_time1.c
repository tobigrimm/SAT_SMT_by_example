#include <stdint.h>
#include <time.h>
#include <assert.h>

/*
 * copypasted and reworked from
 * http://www.cise.ufl.edu/~cop4600/cgi-bin/lxr/http/source.cgi/lib/ansi/loc_time.h
 * http://www.cise.ufl.edu/~cop4600/cgi-bin/lxr/http/source.cgi/lib/ansi/misc.c
 * http://www.cise.ufl.edu/~cop4600/cgi-bin/lxr/http/source.cgi/lib/ansi/gmtime.c
 */

#define YEAR0           1900 
#define EPOCH_YR        1970
#define SECS_DAY        (24L * 60L * 60L)
#define YEARSIZE(year)  (LEAPYEAR(year) ? 366 : 365)

const int _ytab[2][12] = 
{
	{ 31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31 },
	{ 31, 29, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31 }
};

const char *_days[] =
{
	"Sunday", "Monday", "Tuesday", "Wednesday",
	"Thursday", "Friday", "Saturday"
};

const char *_months[] =
{
	"January", "February", "March",
	"April", "May", "June",
	"July", "August", "September",
	"October", "November", "December"
};

#define LEAPYEAR(year)  (!((year) % 4) && (((year) % 100) || !((year) % 400)))

void decode_UNIX_time(const time_t time)
{
	unsigned int dayclock, dayno;
	int year = EPOCH_YR;

	dayclock = (unsigned long)time % SECS_DAY;
	dayno = (unsigned long)time / SECS_DAY;

	int seconds = dayclock % 60;
	int minutes = (dayclock % 3600) / 60;
	int hour = dayclock / 3600;
	int wday = (dayno + 4) % 7;
	while (dayno >= YEARSIZE(year))
	{
		dayno -= YEARSIZE(year);
		year++;
	}

	year = year - YEAR0;

	int month = 0;

	while (dayno >= _ytab[LEAPYEAR(year)][month])
	{
		dayno -= _ytab[LEAPYEAR(year)][month];
		month++;
	}
	
	char *s;
	switch (month)
	{
		case 0: s="January"; break;
		case 1: s="February"; break;
		case 2: s="March"; break;
		case 3: s="April"; break;
		case 4: s="May"; break;
		case 5: s="June"; break;
		case 6: s="July"; break;
		case 7: s="August"; break;
		case 8: s="September"; break;
		case 9: s="October"; break;
		case 10: s="November"; break;
		case 11: s="December"; break;
		default:
			 assert(0);
	};

	printf ("%04d-%s-%02d %02d:%02d:%02d\n", YEAR0+year, s, dayno+1, hour, minutes, seconds);
	printf ("week day: %s\n", _days[wday]);	
}

int main()
{
	uint32_t time;

	klee_make_symbolic(&time, sizeof time, "time");
	
	decode_UNIX_time(time);

	return 0;
}

