#include <stdint.h>
#include <time.h>
#include <assert.h>

#define YEAR0           1900 
#define EPOCH_YR        1970
#define SECS_DAY        (24L * 60L * 60L)
#define YEARSIZE(year)  (LEAPYEAR(year) ? 366 : 365)

const int _ytab[2][12] = 
{
	{ 31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31 },
	{ 31, 29, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31 }
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

	int month = 0;

	while (dayno >= _ytab[LEAPYEAR(year)][month])
	{
		dayno -= _ytab[LEAPYEAR(year)][month];
		month++;
	}
	year = year - YEAR0;
	
	if (YEAR0+year==2022 && month==1 && dayno+1==22)
		klee_assert(0);
}
int main()
{
	uint32_t time;

	klee_make_symbolic(&time, sizeof time, "time");
	
	decode_UNIX_time(time);

	return 0;
}

