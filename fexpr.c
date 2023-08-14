/* fexpr.c -- floating point expression evaluation. */

/*
 This file is effectively a copy of expr.c, with some tweaks to make
 the arithmetic compatible with floats.

 The bitwise operators are removed, and the floor-division operator
 (`//') is added.

	"id++", "id--"		[post-increment and post-decrement]
	"-", "+"		[(unary operators)]
	"++id", "--id"		[pre-increment and pre-decrement]
	"!"
	"**"			[(exponentiation)]
	"*", "//", "/" "%"
	"+", "-"
	"<=", ">=", "<", ">"
	"==", "!="
	"&&"
	"||"
	"expr ? expr : expr"
	"=", "*=", "//=", "/=" "%=", "+=", "-="
 */

#include "config.h"

#include <stdio.h>
#include "bashansi.h"

#if defined (HAVE_UNISTD_H)
#  ifdef _MINIX
#    include <sys/types.h>
#  endif
#  include <unistd.h>
#endif

#include "chartypes.h"
#include "bashintl.h"

#include "shell.h"
#include "arrayfunc.h"
#include "execute_cmd.h"
#include "flags.h"
#include "subst.h"

#define cr_whitespace(c) (whitespace(c) || ((c) == '\n'))

#define EXPR_STACK_GROW_SIZE 10

#define MAX_EXPR_RECURSION_LEVEL 1024

/* The Tokens.  Singing "The Lion Sleeps Tonight". */

#define EQEQ	1	/* "==" */
#define NEQ	2	/* "!=" */
#define LEQ	3	/* "<=" */
#define GEQ	4	/* ">=" */
#define STR	5	/* string */
#define NUM	6	/* number */
#define LAND	7	/* "&&" Logical AND */
#define LOR	8	/* "||" Logical OR */
#define FLOOR_DIV 9 /* "//" floor division */
#define OP_ASSIGN 10	/* op= expassign as in Posix.2 */
#define COND	11	/* exp1 ? exp2 : exp3 */
#define POWER	12	/* exp1**exp2 */
#define PREINC	13	/* ++var */
#define PREDEC	14	/* --var */
#define POSTINC	15	/* var++ */
#define POSTDEC	16	/* var-- */
#define EQ	'='
#define GT	'>'
#define LT	'<'
#define PLUS	'+'
#define MINUS	'-'
#define MUL	'*'
#define DIV	'/'
#define MOD	'%'
#define NOT	'!'
#define LPAR	'('
#define RPAR	')'
#define QUES	'?'
#define COL	':'
#define COMMA	','

/* Parse-function for expression with the lowest precedence */
#define EXP_LOWEST	expcomma

struct lvalue
{
  char *tokstr;		/* possibly-rewritten lvalue if not NULL */
  double tokval;	/* expression evaluated value */
  SHELL_VAR *tokvar;	/* variable described by array or var reference */
  intmax_t ind;		/* array index if not -1 */
};

/* A structure defining a single expression context. */
typedef struct {
  int curtok, lasttok;
  char *expression, *tp, *lasttp;
  double tokval;
  char *tokstr;
  int noeval;
  struct lvalue lval;
} FEXPR_CONTEXT;

static char	*expression;	/* The current expression */
static char	*tp;		/* token lexical position */
static char	*lasttp;	/* pointer to last token position */
static int	curtok;		/* the current token */
static int	lasttok;	/* the previous token */
static int	assigntok;	/* the OP in OP= */
static char	*tokstr;	/* current token string */
static double	tokval;		/* current token value */
static int	noeval;		/* set to 1 if no assignment to be done */
static procenv_t evalbuf;

/* ... TODO ... */

double
fevalexp(expr, flags, validp)
     char *expr;
     int flags;
     int *validp;
{
  /* TODO placeholder: return pi for now */

  if(validp)
    *validp = 1;

  return 3.141592;
}
