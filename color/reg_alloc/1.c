#include <stdlib.h>
#include <stdio.h>
#include <string.h>

char *kmp_search(char *haystack, size_t haystack_size, char *needle, size_t needle_size);

int64_t T[1024];

char *kmp_search(char *haystack, size_t haystack_size, char *needle, size_t needle_size)
{
	//int *T;
	int64_t i, j;
	char *result = NULL;
 
	if (needle_size==0)
		return haystack;
 
	/* Construct the lookup table */
	//T = (int*) malloc((needle_size+1) * sizeof(int));
	T[0] = -1;
	for (i=0; i<needle_size; i++)
	{
		T[i+1] = T[i] + 1;
		while (T[i+1] > 0 && needle[i] != needle[T[i+1]-1])
			T[i+1] = T[T[i+1]-1] + 1;
	}
 
	/* Perform the search */
	for (i=j=0; i<haystack_size; )
	{
		if (j < 0 || haystack[i] == needle[j])
		{
			++i, ++j;
			if (j == needle_size) 
			{
				result = haystack+i-j;
				break;
			}
		}
		else j = T[j];
	}
 
	//free(T);
	return result;
}

char* helper(char* haystack, char* needle)
{
	return kmp_search(haystack, strlen(haystack), needle, strlen(needle));
};

int main()
{
	printf ("%s\n", helper("hello world", "world"));
	printf ("%s\n", helper("hello world", "ell"));
};

