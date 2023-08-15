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
#include <math.h>
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
} EXPR_CONTEXT;

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

/* set to 1 if the expression has already been run through word expansion */
static int	already_expanded;

static struct lvalue curlval = {0, 0, 0, -1};
static struct lvalue lastlval = {0, 0, 0, -1};

static int	_is_arithop PARAMS((int));
static void	readtok PARAMS((void));	/* lexical analyzer */

static void	init_lvalue PARAMS((struct lvalue *));
static struct lvalue *alloc_lvalue PARAMS((void));
static void	free_lvalue PARAMS((struct lvalue *));

static double	expr_streval PARAMS((char *, int, struct lvalue *));
static void	evalerror PARAMS((const char *));

static void	pushexp PARAMS((void));
static void	popexp PARAMS((void));
static void	expr_unwind PARAMS((void));
static void	expr_bind_variable PARAMS((char *, char *));
#if defined (ARRAY_VARS)
static void	expr_bind_array_element PARAMS((char *, arrayind_t, char *));
#endif

static double subexpr PARAMS((char *));

static double	expcomma PARAMS((void));
static double expassign PARAMS((void));
static double	expcond PARAMS((void));
static double explor PARAMS((void));
static double expland PARAMS((void));
static double	expbor PARAMS((void));
static double	expbxor PARAMS((void));
static double	expband PARAMS((void));
static double exp5 PARAMS((void));
static double exp4 PARAMS((void));
static double expshift PARAMS((void));
static double exp3 PARAMS((void));
static double expmuldiv PARAMS((void));
static double	exppower PARAMS((void));
static double exp1 PARAMS((void));
static double exp0 PARAMS((void));

/* Global var which contains the stack of expression contexts. */
static EXPR_CONTEXT **expr_stack;
static int expr_depth;		   /* Location in the stack. */
static int expr_stack_size;	   /* Number of slots already allocated. */

#if defined (ARRAY_VARS)
extern const char * const bash_badsub_errmsg;
#endif

#define SAVETOK(X) \
  do { \
    (X)->curtok = curtok; \
    (X)->lasttok = lasttok; \
    (X)->tp = tp; \
    (X)->lasttp = lasttp; \
    (X)->tokval = tokval; \
    (X)->tokstr = tokstr; \
    (X)->noeval = noeval; \
    (X)->lval = curlval; \
  } while (0)

#define RESTORETOK(X) \
  do { \
    curtok = (X)->curtok; \
    lasttok = (X)->lasttok; \
    tp = (X)->tp; \
    lasttp = (X)->lasttp; \
    tokval = (X)->tokval; \
    tokstr = (X)->tokstr; \
    noeval = (X)->noeval; \
    curlval = (X)->lval; \
  } while (0)

/* Push and save away the contents of the globals describing the
   current expression context. */
static void
pushexp ()
{
  EXPR_CONTEXT *context;

  if (expr_depth >= MAX_EXPR_RECURSION_LEVEL)
    evalerror (_("expression recursion level exceeded"));

  if (expr_depth >= expr_stack_size)
    {
      expr_stack_size += EXPR_STACK_GROW_SIZE;
      expr_stack = (EXPR_CONTEXT **)xrealloc (expr_stack, expr_stack_size * sizeof (EXPR_CONTEXT *));
    }

  context = (EXPR_CONTEXT *)xmalloc (sizeof (EXPR_CONTEXT));

  context->expression = expression;
  SAVETOK(context);

  expr_stack[expr_depth++] = context;
}

/* Pop the the contents of the expression context stack into the
   globals describing the current expression context. */
static void
popexp ()
{
  EXPR_CONTEXT *context;

  if (expr_depth <= 0)
    {
      /* See the comment at the top of evalexp() for an explanation of why
	 this is done. */
      expression = lasttp = 0;
      evalerror (_("recursion stack underflow"));
    }

  context = expr_stack[--expr_depth];

  expression = context->expression;
  RESTORETOK (context);

  free (context);
}

static void
expr_unwind ()
{
  while (--expr_depth > 0)
    {
      if (expr_stack[expr_depth]->tokstr)
	free (expr_stack[expr_depth]->tokstr);

      if (expr_stack[expr_depth]->expression)
	free (expr_stack[expr_depth]->expression);

      free (expr_stack[expr_depth]);
    }
  if (expr_depth == 0)
    free (expr_stack[expr_depth]);	/* free the allocated EXPR_CONTEXT */

  noeval = 0;	/* XXX */
}

static void
expr_bind_variable (lhs, rhs)
     char *lhs, *rhs;
{
  SHELL_VAR *v;
  int aflags;

  if (lhs == 0 || *lhs == 0)
    return;		/* XXX */

#if defined (ARRAY_VARS)
  aflags = (assoc_expand_once && already_expanded) ? ASS_NOEXPAND : 0;
  aflags |= ASS_ALLOWALLSUB;		/* allow assoc[@]=value */
#else
  aflags = 0;
#endif
  v = bind_float_variable (lhs, rhs, aflags);
  if (v && (readonly_p (v) || noassign_p (v)))
    sh_longjmp (evalbuf, 1);	/* variable assignment error */
  stupidly_hack_special_variables (lhs);
}

#if defined (ARRAY_VARS)
/* This is similar to the logic in arrayfunc.c:valid_array_reference when
   you pass VA_NOEXPAND. */
static int
expr_skipsubscript (vp, cp)
     char *vp, *cp;
{
  int flags, isassoc;
  SHELL_VAR *entry;

  isassoc = 0;
  entry = 0;
  if (assoc_expand_once & already_expanded)
    {
      *cp = '\0';
      isassoc = legal_identifier (vp) && (entry = find_variable (vp)) && assoc_p (entry);
      *cp = '[';	/* ] */
    }
  flags = (isassoc && assoc_expand_once && already_expanded) ? VA_NOEXPAND : 0;
  return (skipsubscript (cp, 0, flags));
}

/* Rewrite tok, which is of the form vname[expression], to vname[ind], where
   IND is the already-calculated value of expression. */
static void
expr_bind_array_element (tok, ind, rhs)
     char *tok;
     arrayind_t ind;
     char *rhs;
{
  char *lhs, *vname;
  size_t llen;
  char ibuf[INT_STRLEN_BOUND (arrayind_t) + 1], *istr;

  istr = fmtumax (ind, 10, ibuf, sizeof (ibuf), 0);
  vname = array_variable_name (tok, 0, (char **)NULL, (int *)NULL);

  llen = strlen (vname) + sizeof (ibuf) + 3;
  lhs = xmalloc (llen);

  sprintf (lhs, "%s[%s]", vname, istr);		/* XXX */
  
/*itrace("expr_bind_array_element: %s=%s", lhs, rhs);*/
  expr_bind_variable (lhs, rhs);
  free (vname);
  free (lhs);
}
#endif /* ARRAY_VARS */

/* Evaluate EXPR, and return the arithmetic result.  If VALIDP is
   non-null, a zero is stored into the location to which it points
   if the expression is invalid, non-zero otherwise.  If a non-zero
   value is returned in *VALIDP, the return value of evalexp() may
   be used.
 */
double
fevalexp (expr, validp)
     char *expr;
     int *validp;
{
  double val;
  int c;
  procenv_t oevalbuf;

  val = 0;
  noeval = 0;
  already_expanded = 0;

  FASTCOPY (evalbuf, oevalbuf, sizeof (evalbuf));

  c = setjmp_nosigs (evalbuf);

  if (c) /* encountered an error */
    {
      FREE (tokstr);
      FREE (expression);
      tokstr = expression = (char *)NULL;

      expr_unwind ();
      expr_depth = 0;

      /* We copy in case we've called evalexp recursively */
      FASTCOPY (oevalbuf, evalbuf, sizeof (evalbuf));

      if (validp)
	*validp = 0;
      return (0);
    }

  val = subexpr (expr);

  /* successfully parsed an expression */

  if (validp)
    *validp = 1;

  FASTCOPY (oevalbuf, evalbuf, sizeof (evalbuf));

  return (val);
}

static double
subexpr (expr)
     char *expr;
{
  double val;
  char *p;

  for (p = expr; p && *p && cr_whitespace (*p); p++)
    ;

  if (p == NULL || *p == '\0')
    return (0);

  pushexp ();
  expression = savestring (expr);
  tp = expression;

  curtok = lasttok = 0;
  tokstr = (char *)NULL;
  tokval = 0;
  init_lvalue (&curlval);
  lastlval = curlval;

  readtok ();

  val = EXP_LOWEST ();

  /*TAG:bash-5.3 make it clear that these are arithmetic syntax errors */
  if (curtok != 0)
    evalerror (_("syntax error in expression"));

  FREE (tokstr);
  FREE (expression);

  popexp ();

  return val;
}

static double
expcomma ()
{
  register double value;

  value = expassign ();
  while (curtok == COMMA)
    {
      readtok ();
      value = expassign ();
    }

  return value;
}

static double
expassign ()
{
  register double value;
  char *lhs, *rhs;
  arrayind_t lind;
#if defined (HAVE_IMAXDIV)
  imaxdiv_t idiv;
#endif

  value = expcond ();
  if (curtok == EQ || curtok == OP_ASSIGN)
    {
      int special, op;
      double lvalue;

      special = curtok == OP_ASSIGN;

      if (lasttok != STR)
	evalerror (_("attempted assignment to non-variable"));

      if (special)
	{
	  op = assigntok;		/* a OP= b */
	  lvalue = value;
	}

      if (tokstr == 0)
	evalerror (_("syntax error in variable assignment"));

      /* XXX - watch out for pointer aliasing issues here */
      lhs = savestring (tokstr);
      /* save ind in case rhs is string var and evaluation overwrites it */
      lind = curlval.ind;
      readtok ();
      value = expassign ();

      if (special)
	{
	  switch (op)
	    {
	    case MUL:
	      /* Handle INTMAX_MIN and INTMAX_MAX * -1 specially here? */
	      lvalue *= value;
	      break;
	    case DIV:
	      lvalue /= value;
	      break;
	    case FLOOR_DIV:
	      lvalue = (double)((int)(lvalue / value));
	      break;
	    case PLUS:
	      lvalue += value;
	      break;
	    case MINUS:
	      lvalue -= value;
	    default:
	      free (lhs);
	      evalerror (_("bug: bad expassign token"));
	      break;
	    }
	  value = lvalue;
	}

      FLOAT_TO_STRING (value, rhs);
      if (noeval == 0)
	{
#if defined (ARRAY_VARS)
	  if (lind != -1)
	    expr_bind_array_element (lhs, lind, rhs);
	  else
#endif
	    expr_bind_variable (lhs, rhs);
	}
      if (curlval.tokstr && curlval.tokstr == tokstr)
	init_lvalue (&curlval);

      free (rhs);
      free (lhs);
      FREE (tokstr);
      tokstr = (char *)NULL;		/* For freeing on errors. */
    }

  return (value);
}

/* Conditional expression (expr?expr:expr) */
static double
expcond ()
{
  double cval, val1, val2, rval;
  int set_noeval;

  set_noeval = 0;
  rval = cval = explor ();
  if (curtok == QUES)		/* found conditional expr */
    {
      if (cval == 0)
	{
	  set_noeval = 1;
	  noeval++;
	}

      readtok ();
      if (curtok == 0 || curtok == COL)
	evalerror (_("expression expected"));

      val1 = EXP_LOWEST ();

      if (set_noeval)
	noeval--;
      if (curtok != COL)
	evalerror (_("`:' expected for conditional expression"));

      set_noeval = 0;
      if (cval)
 	{
 	  set_noeval = 1;
	  noeval++;
 	}

      readtok ();
      if (curtok == 0)
	evalerror (_("expression expected"));
      val2 = expcond ();

      if (set_noeval)
	noeval--;
      rval = cval ? val1 : val2;
      lasttok = COND;
    }
  return rval;
}

/* Logical OR. */
static double
explor ()
{
  register double val1, val2;
  int set_noeval;

  val1 = expland ();

  while (curtok == LOR)
    {
      set_noeval = 0;
      if (val1 != 0)
	{
	  noeval++;
	  set_noeval = 1;
	}
      readtok ();
      val2 = expland ();
      if (set_noeval)
	noeval--;
      val1 = val1 || val2;
      lasttok = LOR;
    }

  return (val1);
}

/* Logical AND. */
static double
expland ()
{
  register double val1, val2;
  int set_noeval;

  val1 = exp5 ();

  while (curtok == LAND)
    {
      set_noeval = 0;
      if (val1 == 0)
	{
	  set_noeval = 1;
	  noeval++;
	}
      readtok ();
      val2 = exp5 ();
      if (set_noeval)
	noeval--;
      val1 = val1 && val2;
      lasttok = LAND;
    }

  return (val1);
}

static double
exp5 ()
{
  register double val1, val2;

  val1 = exp4 ();

  while ((curtok == EQEQ) || (curtok == NEQ))
    {
      int op = curtok;

      readtok ();
      val2 = exp4 ();
      if (op == EQEQ)
	val1 = (val1 == val2);
      else if (op == NEQ)
	val1 = (val1 != val2);
      lasttok = NUM;
    }
  return (val1);
}

static double
exp4 ()
{
  register double val1, val2;

  val1 = exp3 ();
  while ((curtok == LEQ) ||
	 (curtok == GEQ) ||
	 (curtok == LT) ||
	 (curtok == GT))
    {
      int op = curtok;

      readtok ();
      val2 = exp3 ();

      if (op == LEQ)
	val1 = val1 <= val2;
      else if (op == GEQ)
	val1 = val1 >= val2;
      else if (op == LT)
	val1 = val1 < val2;
      else			/* (op == GT) */
	val1 = val1 > val2;
      lasttok = NUM;
    }
  return (val1);
}

static double
exp3 ()
{
  register double val1, val2;

  val1 = expmuldiv ();

  while ((curtok == PLUS) || (curtok == MINUS))
    {
      int op = curtok;

      readtok ();
      val2 = expmuldiv ();

      if (op == PLUS)
	val1 += val2;
      else if (op == MINUS)
	val1 -= val2;
      lasttok = NUM;
    }
  return (val1);
}

static double
expmuldiv ()
{
  register double val1, val2;
#if defined (HAVE_IMAXDIV)
  imaxdiv_t idiv;
#endif

  val1 = exppower ();

  while ((curtok == MUL) ||
	 (curtok == DIV) ||
	 (curtok == FLOOR_DIV))
    {
      int op = curtok;
      char *stp, *sltp;

      stp = tp;
      readtok ();

      val2 = exppower ();

      if (op == MUL)
	val1 *= val2;
      else if (op == DIV)
	val1 /= val2;
      else
	val1 = (double)((int)(val1 / val2));

      lasttok = NUM;
    }
  return (val1);
}

static double
exppower ()
{
  register double val1, val2, c;

  val1 = exp1 ();
  while (curtok == POWER)
    {
      readtok ();
      val2 = exppower ();	/* exponentiation is right-associative */
      lasttok = NUM;
      if (val2 == 0)
	return (1);
      if (val2 < 0)
	evalerror (_("exponent less than 0"));
      val1 = pow (val1, val2);
    }
  return (val1);
}

static double
exp1 ()
{
  register double val;

  if (curtok == NOT)
    {
      readtok ();
      val = !exp1 ();
      lasttok = NUM;
    }
  else if (curtok == MINUS)
    {
      readtok ();
      val = - exp1 ();
      lasttok = NUM;
    }
  else if (curtok == PLUS)
    {
      readtok ();
      val = exp1 ();
      lasttok = NUM;
    }
  else
    val = exp0 ();

  return (val);
}

static double
exp0 ()
{
  register double val = 0, v2;
  char *vincdec;
  int stok;
  EXPR_CONTEXT ec;

  if (curtok == PREINC || curtok == PREDEC)
    {
      stok = lasttok = curtok;
      readtok ();
      if (curtok != STR)
	/* readtok() catches this */
	evalerror (_("identifier expected after pre-increment or pre-decrement"));

      v2 = tokval + ((stok == PREINC) ? 1 : -1);
      FLOAT_TO_STRING (v2, vincdec);
      if (noeval == 0)
	{
#if defined (ARRAY_VARS)
	  if (curlval.ind != -1)
	    expr_bind_array_element (curlval.tokstr, curlval.ind, vincdec);
	  else
#endif
	    if (tokstr)
	      expr_bind_variable (tokstr, vincdec);
	}
      free (vincdec);
      val = v2;

      curtok = NUM;	/* make sure --x=7 is flagged as an error */
      readtok ();
    }
  else if (curtok == LPAR)
    {
      /* XXX - save curlval here?  Or entire expression context? */
      readtok ();
      val = EXP_LOWEST ();

      if (curtok != RPAR) /* ( */
	evalerror (_("missing `)'"));

      /* Skip over closing paren. */
      readtok ();
    }
  else if ((curtok == NUM) || (curtok == STR))
    {
      val = tokval;
      if (curtok == STR)
	{
	  SAVETOK (&ec);
	  tokstr = (char *)NULL;	/* keep it from being freed */
          noeval = 1;
          readtok ();
          stok = curtok;

	  /* post-increment or post-decrement */
 	  if (stok == POSTINC || stok == POSTDEC)
 	    {
 	      /* restore certain portions of EC */
 	      tokstr = ec.tokstr;
 	      noeval = ec.noeval;
 	      curlval = ec.lval;
 	      lasttok = STR;	/* ec.curtok */

	      v2 = val + ((stok == POSTINC) ? 1 : -1);
	      FLOAT_TO_STRING (v2, vincdec);
	      if (noeval == 0)
		{
#if defined (ARRAY_VARS)
		  if (curlval.ind != -1)
		    expr_bind_array_element (curlval.tokstr, curlval.ind, vincdec);
		  else
#endif
		    expr_bind_variable (tokstr, vincdec);
		}
	      free (vincdec);
	      curtok = NUM;	/* make sure x++=7 is flagged as an error */
 	    }
 	  else
 	    {
	      /* XXX - watch out for pointer aliasing issues here */
	      if (stok == STR)	/* free new tokstr before old one is restored */
		FREE (tokstr);
	      RESTORETOK (&ec);
 	    }
	}
	  
      readtok ();
    }
  else
    evalerror (_("syntax error: operand expected"));

  return (val);
}

static void
init_lvalue (lv)
     struct lvalue *lv;
{
  lv->tokstr = 0;
  lv->tokvar = 0;
  lv->tokval = lv->ind = -1;
}

static struct lvalue *
alloc_lvalue ()
{
  struct lvalue *lv;

  lv = xmalloc (sizeof (struct lvalue));
  init_lvalue (lv);
  return (lv);
}

static void
free_lvalue (lv)
     struct lvalue *lv;
{
  free (lv);
}

static double
expr_streval (tok, e, lvalue)
     char *tok;
     int e;
     struct lvalue *lvalue;
{
  SHELL_VAR *v;
  char *value;
  double tval;
  int initial_depth;
#if defined (ARRAY_VARS)
  arrayind_t ind;
  int tflag, aflag;
  array_eltstate_t es;
#endif

/*itrace("expr_streval: %s: noeval = %d expanded=%d", tok, noeval, already_expanded);*/
  /* If we are suppressing evaluation, just short-circuit here instead of
     going through the rest of the evaluator. */
  if (noeval)
    return (0);

  initial_depth = expr_depth;

#if defined (ARRAY_VARS)
  tflag = (assoc_expand_once && already_expanded) ? AV_NOEXPAND : 0;	/* for a start */
#endif

  /* [[[[[ */
#if defined (ARRAY_VARS)
  aflag = tflag;	/* use a different variable for now */
  if (shell_compatibility_level > 51)
    aflag |= AV_ATSTARKEYS;
  v = (e == ']') ? array_variable_part (tok, tflag, (char **)0, (int *)0) : find_variable (tok);
#else
  v = find_variable (tok);
#endif
  if (v == 0 && e != ']')
    v = find_variable_last_nameref (tok, 0);  

  if ((v == 0 || invisible_p (v)) && unbound_vars_is_error)
    {
#if defined (ARRAY_VARS)
      value = (e == ']') ? array_variable_name (tok, tflag, (char **)0, (int *)0) : tok;
#else
      value = tok;
#endif

      set_exit_status (EXECUTION_FAILURE);
      err_unboundvar (value);

#if defined (ARRAY_VARS)
      if (e == ']')
	FREE (value);	/* array_variable_name returns new memory */
#endif

      if (no_longjmp_on_fatal_error && interactive_shell)
	sh_longjmp (evalbuf, 1);

      if (interactive_shell)
	{
	  expr_unwind ();
	  top_level_cleanup ();
	  jump_to_top_level (DISCARD);
	}
      else
	jump_to_top_level (FORCE_EOF);
    }

#if defined (ARRAY_VARS)
  init_eltstate (&es);
  es.ind = -1;
  /* If the second argument to get_array_value doesn't include AV_ALLOWALL,
     we don't allow references like array[@].  In this case, get_array_value
     is just like get_variable_value in that it does not return newly-allocated
     memory or quote the results.  AFLAG is set above and is either AV_NOEXPAND
     or 0. */
  value = (e == ']') ? get_array_value (tok, aflag, &es) : get_variable_value (v);
  ind = es.ind;
  flush_eltstate (&es);
#else
  value = get_variable_value (v);
#endif

  if (expr_depth < initial_depth)
    {
      if (no_longjmp_on_fatal_error && interactive_shell)
	sh_longjmp (evalbuf, 1);
      return (0);
    }

  tval = (value && *value) ? subexpr (value) : 0;

  if (lvalue)
    {
      lvalue->tokstr = tok;	/* XXX */
      lvalue->tokval = tval;
      lvalue->tokvar = v;	/* XXX */
#if defined (ARRAY_VARS)
      lvalue->ind = ind;
#else
      lvalue->ind = -1;
#endif
    }
	  
  return (tval);
}

static int
_is_multiop (c)
     int c;
{
  switch (c)
    {
    case EQEQ:
    case NEQ:
    case LEQ:
    case GEQ:
    case LAND:
    case LOR:
    case OP_ASSIGN:
    case COND:
    case POWER:
    case PREINC:
    case PREDEC:
    case POSTINC:
    case POSTDEC:
      return 1;
    default:
      return 0;
    }
}

static int
_is_arithop (c)
     int c;
{
  switch (c)
    {
    case EQ:
    case GT:
    case LT:
    case PLUS:
    case MINUS:
    case MUL:
    case DIV:
    case NOT:
    case LPAR:
    case RPAR:
      return 1;		/* operator tokens */
    case QUES:
    case COL:
    case COMMA:
      return 1;		/* questionable */
    default:
      return 0;		/* anything else is invalid */
    }
}

/* Lexical analyzer/token reader for the expression evaluator.  Reads the
   next token and puts its value into curtok, while advancing past it.
   Updates value of tp.  May also set tokval (for number) or tokstr (for
   string). */
static void
readtok ()
{
  register char *cp, *xp;
  register unsigned char c, c1;
  register int e;
  struct lvalue lval;

  /* Skip leading whitespace. */
  cp = tp;
  c = e = 0;
  while (cp && (c = *cp) && (cr_whitespace (c)))
    cp++;

  if (c)
    cp++;

  if (c == '\0')
    {
      lasttok = curtok;
      curtok = 0;
      tp = cp;
      return;
    }
  lasttp = tp = cp - 1;

  if (legal_variable_starter (c))
    {
      /* variable names not preceded with a dollar sign are shell variables. */
      char *savecp;
      EXPR_CONTEXT ec;
      int peektok;

      while (legal_variable_char (c))
	c = *cp++;

      c = *--cp;

#if defined (ARRAY_VARS)
      if (c == '[')
	{
	  e = expr_skipsubscript (tp, cp);		/* XXX - was skipsubscript */
	  if (cp[e] == ']')
	    {
	      cp += e + 1;
	      c = *cp;
	      e = ']';
	    }
	  else
	    evalerror (bash_badsub_errmsg);
	}
#endif /* ARRAY_VARS */

      *cp = '\0';
      if (curlval.tokstr && curlval.tokstr == tokstr)
	init_lvalue (&curlval);

      FREE (tokstr);
      tokstr = savestring (tp);
      *cp = c;

      SAVETOK (&ec);
      tokstr = (char *)NULL;	/* keep it from being freed */
      tp = savecp = cp;
      noeval = 1;
      curtok = STR;
      readtok ();
      peektok = curtok;
      if (peektok == STR)	/* free new tokstr before old one is restored */
	FREE (tokstr);
      RESTORETOK (&ec);
      cp = savecp;

      /* The tests for PREINC and PREDEC aren't strictly correct, but they
	 preserve old behavior if a construct like --x=9 is given. */
      if (lasttok == PREINC || lasttok == PREDEC || peektok != EQ)
        {
          lastlval = curlval;
	  tokval = expr_streval (tokstr, e, &curlval);
        }
      else
	tokval = 0;

      lasttok = curtok;
      curtok = STR;
    }
  else if (DIGIT(c) || c == '.')
    {
      int seen_digit, seen_point;
      seen_digit = seen_point = 0;

      while (DIGIT(c) || (!seen_point && c == '.'))
	{
	  if (c == '.')
	    seen_point = 1;
	  else
	    seen_digit = 1;

	  c = *cp++;
	}

      c = *--cp;
      *cp = '\0';

      if (*(cp - 1) == '.' || !seen_digit)
	  evalerror (_("invalid floating-point constant"));

      tokval = strtod (tp, NULL);
      *cp = c;
      lasttok = curtok;
      curtok = NUM;
    }
  else
    {
      c1 = *cp++;
      if ((c == EQ) && (c1 == EQ))
	c = EQEQ;
      else if ((c == NOT) && (c1 == EQ))
	c = NEQ;
      else if ((c == GT) && (c1 == EQ))
	c = GEQ;
      else if ((c == LT) && (c1 == EQ))
	c = LEQ;
      else if ((c == '&') && (c1 == '&'))
	c = LAND;
      else if ((c == '|') && (c1 == '|'))
	c = LOR;
      else if ((c == '*') && (c1 == '*'))
	c = POWER;
      else if ((c == '/') && (c1 == '/'))
	{
	  if (*cp == '=')	/* a //= b */
	    {
	      assigntok = FLOOR_DIV;
	      c = OP_ASSIGN;
	      cp++;
	    }
	  else
	    c = FLOOR_DIV;
	}
      else if ((c == '-' || c == '+') && c1 == c && curtok == STR)
	c = (c == '-') ? POSTDEC : POSTINC;
#if STRICT_ARITH_PARSING
      else if ((c == '-' || c == '+') && c1 == c && curtok == NUM)
#else
      else if ((c == '-' || c == '+') && c1 == c && curtok == NUM && (lasttok == PREINC || lasttok == PREDEC))
#endif
	{
	  /* This catches something like --FOO++ */
	  /* TAG:bash-5.3 add gettext calls here or make this a separate function */
	  if (c == '-')
	    evalerror ("--: assignment requires lvalue");
	  else
	    evalerror ("++: assignment requires lvalue");
	}
      else if ((c == '-' || c == '+') && c1 == c)
	{
	  /* Quickly scan forward to see if this is followed by optional
	     whitespace and an identifier. */
	  xp = cp;
	  while (xp && *xp && cr_whitespace (*xp))
	    xp++;
	  if (legal_variable_starter ((unsigned char)*xp))
	    c = (c == '-') ? PREDEC : PREINC;
	  else
	    /* Could force parsing as preinc or predec and throw an error */
#if STRICT_ARITH_PARSING
	    {
	      /* Posix says unary plus and minus have higher priority than
		 preinc and predec. */
	      /* This catches something like --4++ */
	      if (c == '-')
		evalerror ("--: assignment requires lvalue");
	      else
		evalerror ("++: assignment requires lvalue");
	    }
#else
	    cp--;	/* not preinc or predec, so unget the character */
#endif
	}
      else if (c1 == EQ && member (c, "*/+-"))
	{
	  assigntok = c;	/* a OP= b */
	  c = OP_ASSIGN;
	}
      else if (_is_arithop (c) == 0)
	{
	  cp--;
	  /* use curtok, since it hasn't been copied to lasttok yet */
	  if (curtok == 0 || _is_arithop (curtok) || _is_multiop (curtok))
	    evalerror (_("syntax error: operand expected"));
	  else
	    evalerror (_("syntax error: invalid arithmetic operator"));
	}
      else
	cp--;			/* `unget' the character */

      /* Should check here to make sure that the current character is one
	 of the recognized operators and flag an error if not.  Could create
	 a character map the first time through and check it on subsequent
	 calls. */
      lasttok = curtok;
      curtok = c;
    }
  tp = cp;
}

static void
evalerror (msg)
     const char *msg;
{
  char *name, *t;

  name = this_command_name;
  for (t = expression; t && whitespace (*t); t++)
    ;
  internal_error (_("%s%s%s: %s (error token is \"%s\")"),
		   name ? name : "", name ? ": " : "",
		   t ? t : "", msg, (lasttp && *lasttp) ? lasttp : "");
  sh_longjmp (evalbuf, 1);
}
