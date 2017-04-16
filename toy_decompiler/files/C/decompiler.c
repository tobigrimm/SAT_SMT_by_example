// Toy decompiler by dennis(a)yurichev, April 2016.

// octothorpe library:
#include "dmalloc.h"
#include "files.h"
#include "stuff.h"
#include "strbuf.h"
#include "ostrings.h"
#include "oassert.h"
#include "regex.h"
#include "regex_helpers.h"

// boehm GC:
#include <gc.h>

// std C:
#include <stdio.h>
#include <strings.h>
#include <math.h>
#include <inttypes.h>

// forward declarations
struct expr;
bool expr_eq (struct expr* n1, struct expr* n2);

enum reg
{
	R_RAX=0, R_RBX, R_RCX, R_RDX, R_RSI, R_RDI, R_UNKNOWN, R_DUMMY_LAST
};

const char* reg_names[]={"rax", "rbx", "rcx", "rdx", "rsi", "rdi"};

enum expr_type
{
	EXPR_SYMBOL, EXPR_VALUE, EXPR_OP,

	// used in match():
	EXPR_WILDCARD, EXPR_PTR_TO_EXPR, EXPR_PTR_TO_VAL
};

enum expr_op
{
	OP_SHIFT_LEFT=0, OP_SHIFT_RIGHT, OP_SUB, OP_ADD, OP_MUL, OP_DIV, OP_NOT, OP_NEG, OP_AND, OP_OR, OP_XOR, OP_REMAINDER, OP_DUMMY_LAST
};

const char* op_names[]={"<<", ">>", "-", "+", "*", "/", "~", "-", "&", "|", "^", "%"};

struct expr
{
	enum expr_type t;
	
	// for EXPR_SYMBOL
	char *sym;
	
	// for EXPR_VALUE
	int64_t val;

	// for EXPR_OP
	enum expr_op op;
	struct expr *op1;
	struct expr *op2;

	// for EXPR_PTR_TO_EXPR
	struct expr **binded_expr;

	// for EXPR_PTR_TO_VAL	
	int64_t *binded_val;
};

struct expr* registers[R_DUMMY_LAST];

struct expr* bind_expr (struct expr **in)
{
	struct expr *n=GC_malloc(sizeof(struct expr));
	n->t=EXPR_PTR_TO_EXPR;
	n->binded_expr=in;
	return n;
};

struct expr* bind_val (int64_t* val)
{
	struct expr *n=GC_malloc(sizeof(struct expr));
	n->t=EXPR_PTR_TO_VAL;
	n->binded_val=val;
	return n;
};

struct expr* match_wildcard ()
{
	struct expr *n=GC_malloc(sizeof(struct expr));
	n->t=EXPR_WILDCARD;
	return n;
};

bool match (struct expr* n, struct expr *pat)
{
	switch (pat->t)
	{
		case EXPR_SYMBOL:
			// do we really need it?
			return expr_eq (n, pat);

		case EXPR_VALUE:
			return expr_eq (n, pat);

		case EXPR_OP:
			if (pat->t != n->t)
				return false;
			if (pat->op != n->op)
				return false;
			if (match (n->op1, pat->op1)==false)
				return false;
			if (pat->op2 && match (n->op2, pat->op2)==false)
				return false;
			return true;

		case EXPR_PTR_TO_EXPR:
			*pat->binded_expr=n;
			return true;

		case EXPR_PTR_TO_VAL:
			if (n->t!=EXPR_VALUE)
				return false;
			*pat->binded_val=n->val;
			return true;

		case EXPR_WILDCARD:
			return true;

		default:
			oassert(0);
	};
};

void print_val(int64_t val)
{
	if (val>=0 && val<10000)
		printf ("%" PRIu64, val);
	else
		printf ("0x%" PRIx64, val);
		//printf ("0x%" PRIx64 "(%" PRIu64")", val, val);
};

void print_expr (struct expr *n)
{
	switch (n->t)
	{
		case EXPR_PTR_TO_EXPR:
			printf ("EXPR_PTR_TO_EXPR");
			break;

		case EXPR_PTR_TO_VAL:
			printf ("EXPR_PTR_TO_VAL");
			break;
		
		case EXPR_WILDCARD:
			printf ("EXPR_WILDCARD");
			break;


		case EXPR_SYMBOL:
			printf ("%s", n->sym);
			break;

		case EXPR_VALUE:
			print_val(n->val);
			break;

		case EXPR_OP:
			if (n->op==OP_NOT || n->op==OP_NEG)
			{
				// unary (like NOT, NEG)
				printf ("(");
				printf ("%s ", op_names[n->op]);
				print_expr (n->op1);
				printf (")");
			}
			else
			{
				// binary
				printf ("(");
				print_expr (n->op1);
				oassert(n->op < OP_DUMMY_LAST);
				printf (" %s ", op_names[n->op]);
				print_expr (n->op2);
				printf (")");
			};
			break;
		default:
			oassert(0);
	};
};

bool expr_eq (struct expr* n1, struct expr* n2)
{
	if (n1->t != n2->t)
		return false;

	switch (n1->t)
	{
		case EXPR_SYMBOL:
			return streq (n1->sym, n2->sym);

		case EXPR_VALUE:
			return n1->val == n2->val;

		case EXPR_OP:
			if (n1->op != n2->op)
				return false;

			if (expr_eq (n1->op1, n2->op1)==false)
				return false;
			
			// if op2 is present, test it as well:
			if (n1->op2 && expr_eq (n1->op2, n2->op2)==false)
				return false;

			return true;

		default:
			oassert(0);
	};
};

struct expr* create_expr_sym (char *s)
{
	struct expr *n=GC_malloc(sizeof(struct expr));
	n->t=EXPR_SYMBOL;
	n->sym=GC_strdup(s);
	return n;
};

struct expr* create_expr_val (int64_t v)
{
	struct expr *n=GC_malloc(sizeof(struct expr));
	n->t=EXPR_VALUE;
	n->val=v;
	return n;
};

struct expr* create_unary_expr (enum expr_op op, struct expr* op1)
{
	struct expr *n=GC_malloc(sizeof(struct expr));
	n->t=EXPR_OP;
	n->op=op;
	n->op1=op1;
	n->op2=NULL;
	return n;
};

struct expr* create_binary_expr (enum expr_op op, struct expr* op1, struct expr* op2)
{
	struct expr *n=GC_malloc(sizeof(struct expr));
	n->t=EXPR_OP;
	n->op=op;
	n->op1=op1;
	n->op2=op2;
	return n;
};

bool reduced_something;

struct expr* dbg_print_reduced_expr (const char *fn, struct expr* src, struct expr* dst)
{
	printf ("reduction in %s(): ", fn);
	print_expr(src);
	printf (" -> ");
	print_expr(dst);
	printf ("\n");

	reduced_something=true; // side effect
	
	return dst; // for neat chaining
};

struct expr *reduce_OR(struct expr *n)
{
	struct expr *X1, *X2;

	// X | X -> X
	if (match (n, create_binary_expr(OP_OR, bind_expr(&X1), bind_expr (&X2))) && expr_eq(X1, X2))
		n=dbg_print_reduced_expr(__FUNCTION__, n, X1);
	
	return n;
};

// for commutative operations
bool match_comm (struct expr* e, enum expr_op op, struct expr* pat1, struct expr *pat2)
{
	// test as is:
	if (match (e, create_binary_expr(op, pat1, pat2)))
		return true;
	// test as swapped:
	if (match (e, create_binary_expr(op, pat2, pat1)))
		return true;
	return false;
};

struct expr *reduce_AND(struct expr *n)
{
	struct expr *X1, *X2;

	// (commutative) X & (X | ...) -> X
	if (match_comm (n, OP_AND, bind_expr(&X1), create_binary_expr(OP_OR, bind_expr (&X2), match_wildcard())) && expr_eq (X1, X2))
		n=dbg_print_reduced_expr(__FUNCTION__, n, X1);

	// X & X -> X
	if (match (n, create_binary_expr(OP_AND, bind_expr(&X1), bind_expr (&X2))) && expr_eq(X1, X2))
		n=dbg_print_reduced_expr(__FUNCTION__, n, X1);

	return n;
};

struct expr *reduce_SHL(struct expr *n)
{
	struct expr *X;
	int64_t val_n, val_m;

	// X<<n -> X*(2^n)
	if (match (n, create_binary_expr(OP_SHIFT_LEFT, bind_expr(&X), bind_val(&val_n))))
		n=dbg_print_reduced_expr(__FUNCTION__, n, create_binary_expr(OP_MUL, X, create_expr_val(1UL<<val_n)));

	return n;
};

struct expr *reduce_SHR(struct expr *n)
{
	struct expr *X;
	int64_t val_n, val_m;

	// this rule must be first:
	// (X>>n)>>m -> X>>(n+m)
	if (match (n, create_binary_expr(OP_SHIFT_RIGHT, create_binary_expr(OP_SHIFT_RIGHT, bind_expr(&X), bind_val (&val_n)), bind_val(&val_m))))
		n=dbg_print_reduced_expr(__FUNCTION__, n, create_binary_expr(OP_SHIFT_RIGHT, X, create_expr_val(val_n+val_m)));
	
	// X>>n -> X/(2^n)
	if (match (n, create_binary_expr(OP_SHIFT_RIGHT, bind_expr(&X), bind_val(&val_n))))
	{
		if (val_n<64)
		{
			n=dbg_print_reduced_expr(__FUNCTION__, n, create_binary_expr(OP_DIV, X, create_expr_val(1UL<<val_n)));
		}
		else
		{
			// shifting value is too big, probably generated in handle_unary_MUL_IMUL(), so postpone it
			// we don't handle values >2^64 anyway
		};
	};

	return n;
};

double get_divisor (uint64_t n /* magic number */, uint64_t m /* shifting coefficient */)
{
	return 1 / (((double)n)/pow(2, m));
};

struct expr *reduce_mul_by_div (struct expr *n)
{
	struct expr *X;
	uint64_t val_n, val_m, val_q;

	// (X*n)>>m, where m>=64 -> X/...
	if (match (n, create_binary_expr(OP_SHIFT_RIGHT,
			create_binary_expr(OP_MUL, bind_expr(&X), bind_val (&val_n)), bind_val(&val_m))) &&
			val_m>=64)
	{
		double divisor=get_divisor(val_n, val_m);
		if (IsInteger(divisor))
			n=dbg_print_reduced_expr(__FUNCTION__, n, create_binary_expr(OP_DIV, X, create_expr_val((int)divisor)));
	};
	return n;
};

struct expr *reduce_ADD(struct expr *n)
{
	// X+X -> X*2
	if (n->t==EXPR_OP && n->op==OP_ADD && expr_eq (n->op1, n->op2))
		n=dbg_print_reduced_expr(__FUNCTION__, n, create_binary_expr(OP_MUL, n->op1, create_expr_val(2)));

	struct expr *X1, *X2;
	int64_t val_n, val_m;
	// (commutative) (X*n)+X -> X*(n+1)
	if (match_comm (n, OP_ADD, create_binary_expr(OP_MUL, bind_expr(&X1), bind_val(&val_n)), bind_expr(&X2)) &&
			expr_eq (X1, X2))
		n=dbg_print_reduced_expr(__FUNCTION__, n, create_binary_expr(OP_MUL, X1, create_expr_val(val_n+1)));
	
	// (commutative) (X+n)+m -> X+(n+m)
	struct expr *X;
	if (match_comm (n, OP_ADD, create_binary_expr(OP_ADD, bind_expr(&X), bind_val(&val_n)), bind_val(&val_m)))
		n=dbg_print_reduced_expr(__FUNCTION__, n, create_binary_expr(OP_ADD, X, create_expr_val(val_n+val_m)));

	// (commutative) (~X)+1 -> -X
	if (match_comm (n, OP_ADD, create_unary_expr(OP_NOT, bind_expr(&X)), create_expr_val(1)))
		n=dbg_print_reduced_expr(__FUNCTION__, n, create_unary_expr(OP_NEG, X));
	
	// (X*n)+(X*m) -> X*(n+m)
	if (match (n, create_binary_expr(OP_ADD, 
					create_binary_expr(OP_MUL, bind_expr(&X1), bind_val(&val_n)), 
					create_binary_expr(OP_MUL, bind_expr(&X2), bind_val(&val_m))
				    )) &&
			expr_eq (X1, X2))
		n=dbg_print_reduced_expr(__FUNCTION__, n, create_binary_expr(OP_MUL, X1, create_expr_val(val_n+val_m)));
	
	return n;
};

struct expr *reduce_SUB(struct expr *n)
{
	struct expr *X, *Y, *X1, *X2;
	int64_t val_n, val_m;
	
	// (X*n)-X -> X*(n-1)
	if (match (n, create_binary_expr(OP_SUB, create_binary_expr(OP_MUL, bind_expr(&X1), bind_val(&val_n)), bind_expr(&X2))) &&
			expr_eq (X1, X2))
		n=dbg_print_reduced_expr(__FUNCTION__, n, create_binary_expr(OP_MUL, X1, create_expr_val(val_n-1)));
	
	// (-X) - Y -> X+Y
	if (match (n, create_binary_expr(OP_SUB, create_unary_expr(OP_NEG, bind_expr(&X)), bind_expr(&Y))))
		n=dbg_print_reduced_expr(__FUNCTION__, n, create_binary_expr(OP_ADD, X, Y));

	// (X - Y) - X -> Y
	if (match (n, create_binary_expr(OP_SUB, create_binary_expr(OP_SUB, bind_expr(&X1), bind_expr(&Y)), bind_expr(&X2))) &&
			expr_eq(X1, X2))
		n=dbg_print_reduced_expr(__FUNCTION__, n, create_unary_expr(OP_NEG, Y));
	
	// (X-n)-m -> X-(n+m)
	if (match (n, create_binary_expr(OP_SUB, create_binary_expr(OP_SUB, bind_expr(&X), bind_val(&val_n)), bind_val(&val_m))))
		n=dbg_print_reduced_expr(__FUNCTION__, n, create_binary_expr(OP_SUB, X, create_expr_val(val_n+val_m)));
	
	return n;
};

struct expr *reduce_XOR(struct expr *n)
{
	// (commutative) (X^n)^m -> X^(n^m)
	struct expr *X, *Y1, *Y2, *Z;
	int64_t val_n, val_m;
	
	if (match_comm (n, OP_XOR, create_binary_expr(OP_XOR, bind_expr(&X), bind_val(&val_n)), bind_val(&val_m)))
		n=dbg_print_reduced_expr(__FUNCTION__, n, create_binary_expr(OP_XOR, X, create_expr_val(val_n^val_m)));

	// (commutative) X^(-1) -> ~X
	if (match_comm (n, OP_XOR, bind_expr(&X), create_expr_val(~0)))
		n=dbg_print_reduced_expr(__FUNCTION__, n, create_unary_expr(OP_NOT, X));
	
	// (commutative) X^0 -> X
	if (match_comm (n, OP_XOR, bind_expr(&X), create_expr_val(0)))
		n=dbg_print_reduced_expr(__FUNCTION__, n, X);
	
	// (commutative) ((X^Y)^Z)^Y -> X^Z
	if (match_comm (n, OP_XOR, 
					create_binary_expr(OP_XOR, 
						create_binary_expr(OP_XOR, 
							bind_expr(&X), 
							bind_expr(&Y1)),
						bind_expr(&Z)),
					bind_expr(&Y2)) && expr_eq(Y1, Y2))
		n=dbg_print_reduced_expr(__FUNCTION__, n, create_binary_expr(OP_XOR, X, Z));
	
	// (commutative) (X^Y)^Y -> X
	if (match_comm (n, OP_XOR, 
					create_binary_expr(OP_XOR,
						bind_expr(&X),
						bind_expr(&Y1)),
					bind_expr(&Y2)) && expr_eq (Y1, Y2))
		n=dbg_print_reduced_expr(__FUNCTION__, n, X);
	
	return n;
};

struct expr *reduce_MUL(struct expr *n)
{
	struct expr *X, *X1, *X2;
	int64_t val_n, val_m;
	
	// (commutative) (X*n)*m -> X*(n*m)
	if (match_comm (n, OP_MUL, create_binary_expr(OP_MUL, bind_expr(&X), bind_val(&val_n)), bind_val(&val_m)))
		n=dbg_print_reduced_expr(__FUNCTION__, n, create_binary_expr(OP_MUL, X, create_expr_val(val_n*val_m)));

	// (commutative) (X/(2^m))*(2^n), where m==n -> X&...
	if (match_comm (n, OP_MUL, create_binary_expr(OP_DIV, bind_expr(&X), bind_val(&val_m)), bind_val(&val_n)) &&
			val_n==val_m &&
			uint64_is_2n(val_n))
		n=dbg_print_reduced_expr(__FUNCTION__, n, create_binary_expr(OP_AND, X, create_expr_val(~((1UL<<uint64_log2(val_n))-1))));

	// (X*n)*(X*m) -> X*(n*m)
	if (match (n, create_binary_expr(OP_MUL, 
					create_binary_expr(OP_MUL, bind_expr(&X1), bind_val(&val_m)), 
					create_binary_expr(OP_MUL, bind_expr(&X2), bind_val(&val_n))))
				&& expr_eq(X1, X2))
		n=dbg_print_reduced_expr(__FUNCTION__, n, create_binary_expr(OP_MUL, X1, create_expr_val(val_m*val_n)));
	
	return n;
};

struct expr *reduce_DIV(struct expr *n)
{
	// (X/n)/m -> X/(n*m)
	struct expr *X;
	int64_t val_n, val_m;
	if (match (n, create_binary_expr(OP_DIV, create_binary_expr(OP_DIV, bind_expr(&X), bind_val(&val_n)), bind_val(&val_m))))
		n=dbg_print_reduced_expr(__FUNCTION__, n, create_binary_expr(OP_DIV, X, create_expr_val(val_n*val_m)));

	return n;
};

struct expr *reduce_NEG_and_co(struct expr *n)
{
	// (- (~X)) -> X+1
	struct expr *X;
	if (match (n, create_unary_expr(OP_NEG, create_unary_expr(OP_NOT, bind_expr(&X)))))
		n=dbg_print_reduced_expr(__FUNCTION__, n, create_binary_expr(OP_ADD, X, create_expr_val(1)));
	
	// (~ (-X)) -> X-1
	if (match (n, create_unary_expr(OP_NOT, create_unary_expr(OP_NEG, bind_expr(&X)))))
		n=dbg_print_reduced_expr(__FUNCTION__, n, create_binary_expr(OP_SUB, X, create_expr_val(1)));
	
	// (-(-X)) -> X
	if (match (n, create_unary_expr(OP_NEG, create_unary_expr(OP_NEG, bind_expr(&X)))))
		n=dbg_print_reduced_expr(__FUNCTION__, n, X);

	return n;
};

// https://en.wikipedia.org/wiki/De_Morgan's_laws
struct expr *reduce_De_Morgan(struct expr *n)
{
	// ~X | ~Y -> ~(X & Y)
	struct expr *X, *Y;
	if (match (n, create_binary_expr(OP_OR, 
					create_unary_expr(OP_NOT, bind_expr(&X)),
					create_unary_expr(OP_NOT, bind_expr(&Y)))))
		n=dbg_print_reduced_expr(__FUNCTION__, n, create_unary_expr(OP_NOT, create_binary_expr(OP_AND, X, Y)));
	
	// ~X & ~Y -> ~(X | Y)
	if (match (n, create_binary_expr(OP_AND, 
					create_unary_expr(OP_NOT, bind_expr(&X)),
					create_unary_expr(OP_NOT, bind_expr(&Y)))))
		n=dbg_print_reduced_expr(__FUNCTION__, n, create_unary_expr(OP_NOT, create_binary_expr(OP_OR, X, Y)));
	
	return n;
};

struct expr *reduce_step(struct expr *n)
{
	// for child(-ren) of the current node:
	if (n->t==EXPR_OP)
	{
		n->op1=reduce_step (n->op1);
		if (n->op2)
			n->op2=reduce_step (n->op2);
	};

	// for the whole expression:
	n=reduce_AND(n);
	n=reduce_MUL(n);
	n=reduce_DIV(n);
	n=reduce_OR(n);
	n=reduce_XOR(n);
	n=reduce_ADD(n);
	n=reduce_SHL(n);
	n=reduce_SHR(n);
	n=reduce_SUB(n);
	n=reduce_NEG_and_co(n);
	n=reduce_De_Morgan(n);
	n=reduce_mul_by_div(n);

	return n;
};

struct expr *reduce(struct expr *n)
{
	int step=1;

	reduced_something=true;
	while (reduced_something)
	{
		reduced_something=false;
		printf ("step %d. going to reduce ", step); print_expr(n); printf ("\n");
		n=reduce_step(n);
		step++;
	};

	return n;
};

enum reg str_to_reg (char *r)
{
	int rt=find_string_in_array_of_strings(r, reg_names, sizeof(reg_names)/sizeof(char*), /* case_insensitive */ true, /* sorted */ false);

	return rt==-1 ? R_UNKNOWN : rt;
};

struct expr *number_to_expr(char *s)
{
	int64_t v;
	if (str_last_char(s)=='h')
	{
		// hexadecimal
		if (sscanf (s, "%" PRIx64, &v)==1)
			goto ok;
		else
			goto error;
	}
	else
	{
		// decimal
		if (sscanf (s, "%" PRIu64, &v)==1)
			goto ok;
		else
			goto error;
	};
ok:
	return create_expr_val(v);

error:
	die ("%s(): can't parse number: %s\n", __FUNCTION__, s);

};

// convert regster's name or number into expression:
struct expr *str_to_expr(char *s)
{
	// is it register?
	enum reg r=str_to_reg(s);
	if (r!=R_UNKNOWN)
		return registers[r];

	// perhaps, it's not a register
	// treat it as number and construct expr with a value in it:
	return number_to_expr(s);
};

void handle_MOV (char *op1, char *op2)
{
	struct expr *op2_expr=str_to_expr(op2);
	oassert(op2_expr);
	enum reg op1_reg=str_to_reg(op1); // op1 is always register, we don't support any memory
	oassert(op1_reg!=R_UNKNOWN);
	registers[op1_reg]=op2_expr;
};

#define RX_REGISTER "(rax|rbx|rcx|rdx|rsi|rdi)"
#define RX_DEC "([0-9]+)"

// examples:
// [reg1+reg2]
// [reg1+1234+reg2]
struct expr* parse_memory(char *s)
{
	struct expr* reg_base=NULL;
	struct expr* reg_idx=NULL;
	struct expr* rt=NULL;
	int64_t disp=0;
	
	regex_t compiled1;
	regex_t compiled2;
	int  rc;

#define PAT_REG_PLUS_REG "\\[" RX_REGISTER "\\+" RX_REGISTER "\\]"
#define PAT_REG_PLUS_VAL_PLUS_REG "\\[" RX_REGISTER "\\+" RX_DEC "\\+" RX_REGISTER "\\]"

	regcomp_or_die(&compiled1, PAT_REG_PLUS_REG, REG_EXTENDED | REG_NEWLINE);
	regcomp_or_die(&compiled2, PAT_REG_PLUS_VAL_PLUS_REG, REG_EXTENDED | REG_NEWLINE);
	
	char **results;

	results=regexec_to_array_of_string(&compiled1, s, 3);
	if (results)
	{
		// lea reg, [reg1+reg2]
		reg_base=str_to_expr(results[1]);
		reg_idx=str_to_expr(results[2]);

		rt=create_binary_expr(OP_ADD, reg_base, reg_idx);
	}
	else
	{
		results=regexec_to_array_of_string(&compiled2, s, 4);
		if (results)
		{
			// lea reg, [reg1+1234+reg2]
			reg_base=str_to_expr(results[1]);
			struct expr* expr_disp=str_to_expr(results[2]);
			reg_idx=str_to_expr(results[3]);

			rt=create_binary_expr(OP_ADD, reg_base, reg_idx);
			rt=create_binary_expr(OP_ADD, rt, expr_disp);
		}
		else
			die("%s() can't parse '%s'\n", __FUNCTION__, s);
	};
	
	dfree_array_of_blocks(results);
	regfree (&compiled1);
	regfree (&compiled2);

	return rt;
};

// works just like handle_MOV(), but parses memory expression and makes expression from it
void handle_LEA (char *op1, char *op2)
{
	// parse op2
	struct expr *op2_expr=parse_memory(op2);
	enum reg op1_reg=str_to_reg(op1); // op1 is always register, we don't support memory
	oassert(op1_reg!=R_UNKNOWN);
	registers[op1_reg]=op2_expr;
};

void handle_unary_op (enum expr_op op, char *op1)
{
	struct expr *op1_expr=str_to_expr(op1);

	enum reg op1_reg=str_to_reg(op1); // op1 is always register, we don't support memory
	oassert(op1_reg!=R_UNKNOWN);

	registers[op1_reg]=create_unary_expr(op, op1_expr);
};

void handle_binary_op (enum expr_op op, char *op1, char *op2)
{
	struct expr *op1_expr=str_to_expr(op1);
	struct expr *op2_expr=str_to_expr(op2);

	enum reg op1_reg=str_to_reg(op1); // op1 is always register, we don't support memory
	oassert(op1_reg!=R_UNKNOWN);

	registers[op1_reg]=create_binary_expr(op, op1_expr, op2_expr);
};

// first op is RAX
void handle_unary_MUL_IMUL(char *op)
{
	struct expr *op_expr=str_to_expr(op);

	struct expr *result=create_binary_expr(OP_MUL, registers[R_RAX], op_expr);

	registers[R_RAX]=result;
	registers[R_RDX]=create_binary_expr(OP_SHIFT_RIGHT, result, create_expr_val(64));
};

// first op is RAX
void handle_unary_DIV_IDIV(char *op)
{
	struct expr *op_expr=str_to_expr(op);
	struct expr *current_RAX=registers[R_RAX];

	struct expr *result=create_binary_expr(OP_DIV, current_RAX, op_expr);

	registers[R_RAX]=result;
	registers[R_RDX]=create_binary_expr(OP_REMAINDER, current_RAX, op_expr);
};

void handle_unary_ins(char *ins, char *op1)
{
	if (strieq (ins, "neg"))
		handle_unary_op (OP_NEG, op1);
	else if (strieq (ins, "not"))
		handle_unary_op (OP_NOT, op1);
	else if (strieq (ins, "shr") || strieq(ins, "sar")) // GCC can produce "shr reg" in assembly listings
		handle_binary_op (OP_SHIFT_RIGHT, op1, "1");
	else if (strieq (ins, "imul") || strieq (ins, "mul"))
		handle_unary_MUL_IMUL(op1);
	else if (strieq (ins, "idiv") || strieq (ins, "div"))
		handle_unary_DIV_IDIV(op1);
	else
		die ("%s() unknown/unhandled instruction %s\n", __FUNCTION__, ins);
};

void handle_binary_ins(char *ins, char *op1, char *op2)
{
	if (strieq (ins, "mov") || strieq (ins, "movabs"))
		handle_MOV (op1, op2);
	else if (strieq (ins, "lea"))
		handle_LEA (op1, op2);
	else if (strieq (ins, "sar") || strieq (ins, "shr"))
		handle_binary_op (OP_SHIFT_RIGHT, op1, op2);
	else if (strieq (ins, "sal") || strieq (ins, "shl"))
		handle_binary_op (OP_SHIFT_LEFT, op1, op2);
	else if (strieq (ins, "and"))
		handle_binary_op (OP_AND, op1, op2);
	else if (strieq (ins, "or"))
		handle_binary_op (OP_OR, op1, op2);
	else if (strieq (ins, "xor"))
		handle_binary_op (OP_XOR, op1, op2);
	else if (strieq (ins, "add"))
		handle_binary_op (OP_ADD, op1, op2);
	else if (strieq (ins, "sub"))
		handle_binary_op (OP_SUB, op1, op2);
	else if (strieq (ins, "imul") || strieq(ins, "mul"))
		handle_binary_op (OP_MUL, op1, op2);
	else
		die ("%s() unknown/unhandled instruction %s\n", __FUNCTION__, ins);
};

void handle_ternary_ins(char *ins, char *op1, char *op2, char* op3)
{
	oassert(strieq(ins,"imul")); // the only ternary instruction we support
	
	// dst
	enum reg op1_reg=str_to_reg(op1); // op1 is always register, we don't support memory
	oassert(op1_reg!=R_UNKNOWN);
	
	// src
	struct expr *op1_expr=str_to_expr(op1);
	struct expr *op2_expr=str_to_expr(op2);
	struct expr *op3_expr=str_to_expr(op3);

	registers[op1_reg]=create_binary_expr(OP_MUL, op2_expr, op3_expr);
};

regex_t compiled1;
regex_t compiled2;
regex_t compiled3;
regex_t compiled_comment;
regex_t compiled_WP;

void parse_asm_line (char *line, void* param)
{
	char **results;

	results=regexec_to_array_of_string(&compiled3, line, 5);
	if (results)
	{
		handle_ternary_ins(results[1], results[2], results[3], results[4]);
		goto handled;
	};

	results=regexec_to_array_of_string(&compiled2, line, 4);
	if (results)
	{
		handle_binary_ins(results[1], results[2], results[3]);
		goto handled;
	};

	results=regexec_to_array_of_string(&compiled1, line, 3);
	if (results)
	{
		handle_unary_ins(results[1], results[2]);
		goto handled;
	};

	results=regexec_to_array_of_string(&compiled_comment, line, 1);
	if (results)
		goto handled;

	results=regexec_to_array_of_string(&compiled_WP, line, 1);
	if (results)
		goto handled;

	die("can't parse line '%s'\n", line);
handled:
	dfree_array_of_blocks(results);
};

int main(int argc, char **argv)
{
	if (argc!=2)
		die ("use: <fname>\n");

	// regular expressions:
#define RX_INS "(mov|movabs|lea|mul|imul|div|idiv|not|neg|sar|sal|shr|shl|sub|add|and|or|xor)"
#define RX_WHITESPACE "[\t ]*"

#define PAT1 "^" RX_WHITESPACE RX_INS RX_WHITESPACE RX_REGISTER RX_WHITESPACE "$"
	regcomp_or_die(&compiled1, PAT1, REG_EXTENDED | REG_NEWLINE);

#define PAT2 "^" RX_WHITESPACE RX_INS RX_WHITESPACE RX_REGISTER "," RX_WHITESPACE "([^ ]+)" "$"
	regcomp_or_die(&compiled2, PAT2, REG_EXTENDED | REG_NEWLINE);

#define PAT3 "^" RX_WHITESPACE RX_INS RX_WHITESPACE RX_REGISTER "," RX_WHITESPACE RX_REGISTER "," RX_WHITESPACE "([^ ]+)" "$"
	regcomp_or_die(&compiled3, PAT3, REG_EXTENDED | REG_NEWLINE);

#define PAT_COMMENT "^" RX_WHITESPACE ";.*$"
	regcomp_or_die(&compiled_comment, PAT_COMMENT, REG_EXTENDED | REG_NEWLINE);

#define PAT_WP "^" RX_WHITESPACE "$"
	regcomp_or_die(&compiled_WP, PAT_WP, REG_EXTENDED | REG_NEWLINE);

	// initial registers states (symbols)
	registers[R_RAX]=create_expr_sym("initial_RAX");
	registers[R_RBX]=create_expr_sym("initial_RBX");
	registers[R_RDI]=create_expr_sym("arg1");
	registers[R_RSI]=create_expr_sym("arg2");
	registers[R_RDX]=create_expr_sym("arg3");
	registers[R_RCX]=create_expr_sym("arg4");

	// process input asm file:
	read_text_file_by_line_or_die (argv[1], parse_asm_line, /* param */ NULL);

	// reduce expression in RAX and print it:
	//registers[R_RAX]=reduce_all(registers[R_RAX]);
	registers[R_RAX]=reduce(registers[R_RAX]);

	printf ("RAX="); print_expr(registers[R_RAX]); printf ("\n");

	// free:
	regfree (&compiled1);
	regfree (&compiled2);
	regfree (&compiled3);
	regfree (&compiled_comment);
	regfree (&compiled_WP);

	dump_unfreed_blocks();
	dmalloc_deinit();

	return 0;
}

