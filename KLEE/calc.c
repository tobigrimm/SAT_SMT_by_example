// copypasted from http://stackoverflow.com/a/13895198 and reworked

// Bare bones scanner and parser for the following LL(1) grammar:
// expr -> term { [+-] term }     ; An expression is terms separated by add ops.
// term -> factor { [*/] factor } ; A term is factors separated by mul ops.
// factor -> unsigned_factor      ; A signed factor is a factor, 
//         | - unsigned_factor    ;   possibly with leading minus sign
// unsigned_factor -> ( expr )    ; An unsigned factor is a parenthesized expression 
//         | NUMBER               ;   or a number
//
// The parser returns the floating point value of the expression.

#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>

char input[128];
int input_idx=0;

char my_getchar()
{
	char rt=input[input_idx];
	input_idx++;
	return rt;
};

// The token buffer. We never check for overflow! Don't so in production code.
// it's deliberately smaller than input[] so KLEE could find buffer overflow
char buf[64];
int n = 0;

// The current character.
int ch;

// The look-ahead token.  This is the 1 in LL(1).
enum { ADD_OP, MUL_OP, LEFT_PAREN, RIGHT_PAREN, NOT_OP, NUMBER, END_INPUT } look_ahead;

// Forward declarations.
void init(void);
void advance(void);
int expr(void);
void error(char *msg);

// Parse expressions, one per line. 
int main(void)
{
	// take input expression from input[]
	//input[0]=0;
	//strcpy (input, "2+2");
	klee_make_symbolic(input, sizeof input, "input");
	input[127]=0;

	init();
	while (1)
	{
		int val = expr();
		printf("%d\n", val);

		if (look_ahead != END_INPUT)
			error("junk after expression");
		advance();  // past end of input mark
	}
	return 0;
}

// Just die on any error.
void error(char *msg)
{
	fprintf(stderr, "Error: %s. Exiting.\n", msg);
	exit(1);
}

// Buffer the current character and read a new one.
void read()
{
	buf[n++] = ch;
	buf[n] = '\0';  // Terminate the string.
	ch = my_getchar();
}

// Ignore the current character.
void ignore()
{
	ch = my_getchar();
}

// Reset the token buffer.
void reset()
{
	n = 0;
	buf[0] = '\0';
}

// The scanner.  A tiny deterministic finite automaton.
int scan()
{
	reset();
START:
	// first character is digit?
	if (isdigit (ch))
		goto DIGITS;

	switch (ch)
	{
		case ' ': case '\t': case '\r':
			ignore();
			goto START;

		case '-': case '+': case '^':
			read();
			return ADD_OP;

		case '~':
			read();
			return NOT_OP;

		case '*': case '/': case '%':
			read();
			return MUL_OP;

		case '(':
			read();
			return LEFT_PAREN;

		case ')':
			read();
			return RIGHT_PAREN;
		
		case 0:
		case '\n':
			ch = ' ';    // delayed ignore()
			return END_INPUT;

		default:
			printf ("bad character: 0x%x\n", ch);
			exit(0);
	}

DIGITS:
	if (isdigit (ch))
	{
		read();
		goto DIGITS;
	}
	else	
		return NUMBER;
}

// To advance is just to replace the look-ahead.
void advance()
{
	look_ahead = scan();
}

// Clear the token buffer and read the first look-ahead.
void init()
{
	reset();
	ignore(); // junk current character
	advance();
}
			
int get_number(char *buf)
{
	char *endptr;

	int rt=strtoul (buf, &endptr, 10);

	// is the whole buffer has been processed?
	if (strlen(buf)!=endptr-buf)
	{
		fprintf (stderr, "invalid number: %s\n", buf);
		exit(0);
	};
	return rt;
};

int unsigned_factor()
{
	int rtn = 0;
	switch (look_ahead)
	{
		case NUMBER:
			rtn=get_number(buf);
			advance();
			break;

		case LEFT_PAREN:
			advance();
			rtn = expr();
			if (look_ahead != RIGHT_PAREN) error("missing ')'");
			advance();
			break;

		default:
			printf("unexpected token: %d\n", look_ahead);
			exit(0);
	}
	return rtn;
}

int factor()
{
	int rtn = 0;
	// If there is a leading minus...
	if (look_ahead == ADD_OP && buf[0] == '-')
	{
		advance();
		rtn = -unsigned_factor();
	}
	else
		rtn = unsigned_factor();

	return rtn;
}

int term()
{
	int rtn = factor();
	while (look_ahead == MUL_OP)
	{
		switch(buf[0])
		{
			case '*':
				advance(); 
				rtn *= factor(); 
				break; 

			case '/':
				advance();
				rtn /= factor();
				break;
			case '%':
				advance();
				rtn %= factor();
				break;
		}
	}
	return rtn;
}

int expr()
{
	int rtn = term();
	while (look_ahead == ADD_OP)
	{
		switch(buf[0])
		{
			case '+': 
				advance();
				rtn += term(); 
				break; 

			case '-':
				advance();
				rtn -= term();
				break;
		}
	}
	return rtn;
}

