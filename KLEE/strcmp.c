int my_strcmp(const char *s1, const char *s2)
{
	int ret = 0;

	while (1)
	{
		ret = *(unsigned char *) s1 - *(unsigned char *) s2;
		if (ret!=0)
			break;
		if ((*s1==0) || (*s2)==0)
			break;
		s1++;
		s2++;
	};

	if (ret < 0) 
	{
		return -1;
	} else if (ret > 0) 
	{
		return 1;
	}

	return 0;
}

int main()
{
	char input1[2];
	char input2[2];
	
	klee_make_symbolic(input1, sizeof input1, "input1");
	klee_make_symbolic(input2, sizeof input2, "input2");
	
	klee_assume((input1[0]>='a') && (input1[0]<='z'));
	klee_assume((input2[0]>='a') && (input2[0]<='z'));

	klee_assume(input1[1]==0);
	klee_assume(input2[1]==0);

	my_strcmp (input1, input2);
};

