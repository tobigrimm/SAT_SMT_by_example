#include <stdio.h>

unsigned int divide(unsigned int dividend, unsigned int divisor)
{
	unsigned int tmp = dividend;
	unsigned int denom = divisor;
	unsigned int current = 1;
	unsigned int answer = 0;

	if (denom > tmp)
		return 0;

	if (denom == tmp)
		return 1;

	// align divisor:
	while (denom <= tmp)
	{
		denom = denom << 1;
		current = current << 1;
	}

	denom = denom >> 1;
	current = current >> 1;

	while (current!=0)
	{
		printf ("current=%d, denom=%d\n", current, denom);
		if (tmp >= denom)
		{
			tmp -= denom;
			answer |= current;
		}
		current = current >> 1;
		denom = denom >> 1;
	}
	printf ("tmp/remainder=%d\n", tmp); // remainder!
	return answer;
}

int main ()
{
	printf ("%d\n", divide (1234567, 813));
};

