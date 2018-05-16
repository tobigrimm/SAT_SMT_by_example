// find CNF for a (small) function in bruteforce manner

// coded in spirit of "aha! hacker assistant" by Henry Warren

// dennis(a)yurichev.com 2015-2017

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <memory.h>

// octothorpe
#include <stuff.h>
#include <octomath.h>

#define VARIABLES 4
#define MAX_CLAUSES 10

// CryptoMiniSat?
//#define XOR_CNF true
#define XOR_CNF false

bool func(bool v[VARIABLES])
{

	// ITE:

	bool tmp;
	if (v[0]==0)
		tmp=v[1];
	else
		tmp=v[2];

	return tmp==v[3];

	//return v[3]==0;

	//return (v[0] | v[1] | v[2]) == v[3];
	//return (v[0] & v[1]) | (v[2] & v[3]);
	//return (v[0] & v[1] & v[2]) == v[3];
	//return (v[0] & (v[1] ^ v[2])) == v[3];
	//return v[0]^v[1]==v[2];
	//return v[0]==v[1];
	//return v[0]^v[1];

	//return v[0] ^ v[1] ^ v[2] ^ v[3];
	//return v[0] ^ v[1] ^ v[2] == v[3];
	//return (!v[0]) ^ v[1] ^ v[2] ^ v[3];
	//return (!v[0]) | v[1] | v[2];
	//return (!v[0]) ^ v[1] ^ v[2];
	//return v[0] ^ v[1] ^ v[2];
	//return v[0] ^ v[1] ^ v[2] ^ v[3];
	
	//return v[0] | v[1] | v[2] | v[3];
	//return v[0] | (v[1] & v[2]);

	// 2-bit half-adder
	//return ((((v[0]<<1) | v[1]) + ((v[2]<<1) | v[3])) & 3) == 3;

	//int tmp=(v[0]<<3) | (v[1]<<2) | (v[2]<<1) | v[3];
	//return popcnt32(tmp)==1;
};

unsigned int possible_clauses;

struct clause
{
	bool xor; // false - absent
	int v[VARIABLES]; // 0 - absent; 1 - present; 2 - present and negated
};

struct clause clauses[MAX_CLAUSES];

void print_clause(struct clause *c)
{
	if (c->xor)
		printf ("x");
	for (int i=0; i<VARIABLES; i++)
		switch (c->v[i])
		{
			case 0:
				break;
			case 1:
				printf ("%d ", i+1);
				break;
			case 2:
				printf ("-%d ", i+1);
				break;
			default:
				assert(0);
				break;
		};
	printf ("0\n");
};

void print_CNF (int CNF_len)
{
	printf ("p cnf %d %d\n", VARIABLES, CNF_len);
	for (int i=0; i<CNF_len; i++)
		print_clause(&clauses[i]);
};

void gen_clause (unsigned int i, struct clause *c)
{
	assert(i<possible_clauses);
		
	unsigned int t=i;

	for (int i=0; i<VARIABLES; i++)
	{
		c->v[i]=t % 3;
		t=t/3;
	};

	// XOR must be the last one:
	assert(t<=1);
	if (XOR_CNF)
		c->xor=t;
	else
		c->xor=false;
};

bool eval_clause_for_variables(struct clause *c, bool v[VARIABLES])
{
	if (c->xor)
	{
		// we have to evaluate all terms for XOR clause:
		bool rt=false;
		for (int var=0; var<VARIABLES; var++)
		{
			assert(c->v[var]<=2);

			if (c->v[var]==1)
				rt^=v[var];

			if (c->v[var]==2)
				rt^=!v[var];
		};
		return rt;
	};

	// for non-XOR clause, it's enough to find one TRUE and return it
	for (int var=0; var<VARIABLES; var++)
	{
		assert(c->v[var]<=2);

		if (c->v[var]==1 && v[var])
			return true;

		if (c->v[var]==2 && !v[var])
			return true;
	};
	return false;
};

bool check_CNF_for_variables (int CNF_len, bool v[VARIABLES])
{
	bool func_must_be=func (v);
	assert(func_must_be<=1);

	// if func_must_be==1, all clauses must return 1
	// if func_must_be==0, there must be at least one clause returning 0
	int rt=1;
	for (int c=0; c<CNF_len; c++)
	{
		// check each clause and AND result with rt
		rt&=eval_clause_for_variables(&clauses[c], v);
	};
	return func_must_be==rt;
};

void check_CNF (int CNF_len)
{
	for (int i=0; i<(1<<VARIABLES); i++)
	{
		bool v[VARIABLES];

		for (int j=0; j<VARIABLES; j++)
			v[j]=(i>>j)&1;

		if (check_CNF_for_variables(CNF_len, v)==false)
			return;
	};
	printf ("found a CNF:\n");
	print_CNF(CNF_len);
	exit(0);
};

void try_all_CNFs_of_len (int CNF_len)
{
	printf ("%s(%d)\n", __FUNCTION__, CNF_len);
	// cleanup
	bzero (clauses, sizeof(clauses));

	unsigned int upper_bound=ipow (possible_clauses, CNF_len);
	for (unsigned i=0;i<upper_bound;i++)
	{
		check_CNF(CNF_len);

		unsigned int tmp=i;
		for (int c=0; c<CNF_len; c++)
		{
			gen_clause(tmp % possible_clauses, &clauses[c]);
			tmp=tmp/possible_clauses;
		};
	};
};

int main()
{
	possible_clauses=ipow(3,VARIABLES);
	if (XOR_CNF)
		possible_clauses*=2;

	for (int i=1; i<MAX_CLAUSES; i++)
		try_all_CNFs_of_len(i);

	return 0;
};

