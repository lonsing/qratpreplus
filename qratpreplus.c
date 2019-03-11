
/*
 This file is part of QRATPre+.

 Copyright 2018 
 Florian Lonsing, Vienna University of Technology, Austria.

 QRATPre+ is free software: you can redistribute it and/or modify
 it under the terms of the GNU General Public License as published by
 the Free Software Foundation, either version 3 of the License, or (at
 your option) any later version.

 QRATPre+ is distributed in the hope that it will be useful, but
 WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 General Public License for more details.

 You should have received a copy of the GNU General Public License
 along with QRATPre+.  If not, see <http://www.gnu.org/licenses/>.
*/

#include <stdio.h>
#include <sys/resource.h>
#include <stdlib.h>
#include <ctype.h>
#include <limits.h>
#include <dirent.h>
#include <assert.h>
#include <string.h>
#include <stdarg.h>
#include <signal.h>
#include <unistd.h>
#include "stack.h"
#include "mem.h"
#include "qratplus.h"
#include "qbce-qrat-plus.h"

/* -------------------- START: Helper macros -------------------- */

#define VERSION                                                  \
  "QRATPre+ 1.0\n"                                               \
  "Copyright 2018 Florian Lonsing, TU Wien, Austria.\n"           \
  "This is free software; see LICENSE for copying conditions.\n" \
  "There is NO WARRANTY, to the extent permitted by law.\n"

#define USAGE \
"usage: ./qratplus [options] input-formula [timeout]\n"\
"\n"\
"  - 'input-formula' is a file in QDIMACS format (default: stdin)\n"\
"  - '[timeout]' is an optional timeout in seconds\n"\
"  - '[options]' is any combination of the following:\n\n"\
"    -h, --help                    print this usage information and exit\n"\
"    -v                            increase verbosity level incrementally (default: 0)\n"\
"    --version                     print version information and exit\n"\
"    --print-formula               print simplified formula to stdout\n"\
"    --no-ble                      disable blocked literal elimination (BLE) \n"\
"    --no-qratu                    disable QRAT-based elimination of universal literals (QRATU)\n"\
"    --no-qbce                     disable blocked clause elimination (QBCE)\n"\
"    --no-at                       disable asymmetric tautology (AT) checks of clauses\n"\
"    --no-qrate                    disable QRAT-based elimination of clauses (QRATE)\n" \
"    --no-eabs                     disable prefix abstraction\n"\
"    --no-eabs-improved-nesting    disable improved prefix abstraction\n"\
"    --soft-time-limit=<n>         enforce soft time limit in <n> seconds\n"\
"    --permute                     randomly permute clause lists between iterations\n" \
"    --seed=<n>                    in combination with '--permute': random seed <n>(default: 0)\n"\
"\n"

/* Macro to print message and abort. */
#define ABORT_APP(cond,msg)                                       \
  do {                                                                  \
    if (cond)                                                           \
      {                                                                 \
        fprintf (stderr, "[QRATPLUS-PRE] %s at line %d: %s\n", __func__,   \
                 __LINE__, msg);                                        \
        fflush (stderr);                                                \
        abort();                                                        \
      }                                                                 \
  } while (0)

/* -------------------- END: Helper macros -------------------- */

/* -------- START: Application helper functions -------- */

/* Print error message. */
static void
print_abort_err (char *msg, ...)
{
  va_list list;
  assert (msg != NULL);
  fprintf (stderr, "qratplus: ");
  va_start (list, msg);
  vfprintf (stderr, msg, list);
  va_end (list);
  fflush (stderr);
  abort ();
}

/* Print array 'lits' of literals of length 'num'. If 'print_info' is
non-zero, then print info about the scope of each literal in the array. */
static void
print_lits (QRATPlusPre * qr, FILE * out, LitID * lits, unsigned int num,
            const int print_info)
{
  Var *vars = qr->pcnf.vars;
  LitID *p, *e;
  for (p = lits, e = p + num; p < e; p++)
    {
      LitID lit = *p;
      Var *var = LIT2VARPTR (vars, lit);
      if (print_info)
        fprintf (out, "%c(%d)%d ",
                 SCOPE_FORALL (var->scope) ? 'A' : 'E',
                 var->scope->nesting, *p);
      else
        fprintf (out, "%d ", *p);
    }
  fprintf (out, "0\n");
}

/* -------- END: Application helper functions -------- */

/* -------------------- START: QDIMACS PARSING -------------------- */

/* Allocate table of variable IDs having fixed size. If the preamble of the
   QDIMACS file specifies a maximum variable ID which is smaller than the ID
   of a variable encountered in the formula, then the program aborts. */
static void
set_up_var_table (QRATPlusPre * qr, int num)
{
  assert (num >= 0);
  assert (!qr->pcnf.size_vars);
  qr->pcnf.size_vars = num + 1;
  assert (!qr->pcnf.vars);
  qr->pcnf.vars =
    (Var *) mm_malloc (qr->mm, qr->pcnf.size_vars * sizeof (Var));
}

/* Allocate a new scope object and append it to the list of scopes. */
static void
open_new_scope (QRATPlusPre * qr, QuantifierType scope_type)
{
  assert (!qr->parsing_prefix_completed);
  Scope *scope = mm_malloc (qr->mm, sizeof (Scope));
  scope->type = scope_type;
  scope->nesting = qr->pcnf.scopes.last ?
    qr->pcnf.scopes.last->nesting + 1 : 0;
  assert (!qr->opened_scope);
  /* Keep pointer to opened scope to add parsed variable IDs afterwards. */
  qr->opened_scope = scope;
  /* Append scope to list of scopes. */
  LINK_LAST (qr->pcnf.scopes, scope, link);
}

/* Comparison function used to sort literals of clauses. */
static int
compare_lits_by_nesting (QRATPlusPre * qr, LitID lit1, LitID lit2)
{
  Var *var1 = LIT2VARPTR (qr->pcnf.vars, lit1);
  Var *var2 = LIT2VARPTR (qr->pcnf.vars, lit2);

  Nesting nesting1 = var1->scope->nesting;
  Nesting nesting2 = var2->scope->nesting;

  if (nesting1 < nesting2)
    return -1;
  else if (nesting1 > nesting2)
    return 1;
  else
    {
      if (var1->id < var2->id)
        return -1;
      else if (var1->id > var2->id)
        return 1;
      else
        return 0;
    }
}


static void
assert_lits_sorted (QRATPlusPre * qr, LitID * lit_start, LitID * lit_end)
{
  Var *vars = qr->pcnf.vars;
  LitID *p, *prev, *e;
  for (prev = p = lit_start, e = lit_end; p < e; p++)
    {
      if (!*p)
        continue;
      Var *pvar = LIT2VARPTR (vars, *p);
      Var *prev_var = LIT2VARPTR (vars, *prev);
      Nesting pvar_nesting, prev_var_nesting;
      pvar_nesting = pvar->scope->nesting;
      prev_var_nesting = prev_var->scope->nesting;
      assert (prev_var_nesting <= pvar_nesting);
      prev = p;
    }
}


//TODO: function appears also in other module, merge
/* Returns number of literals in 'c' with quantifier type 'type'. */
static unsigned int
count_qtype_literals (QRATPlusPre * qr, Clause * c, QuantifierType type)
{
  unsigned int result = 0;
  LitID *p, *e;
  for (p = c->lits, e = p + c->num_lits; p < e; p++)
    {
      LitID lit = *p;
      Var *var = LIT2VARPTR (qr->pcnf.vars, lit);
      if (var->scope->type == type)
        result++;
    }
  return result;
}


/* Discard complementary literals or multiple literals of the same
   variable. Returns nonzero iff clause is tautological and hence should be
   discarded. */
static int
check_and_add_clause (QRATPlusPre * qr, Clause * clause)
{
  int taut = 0;
  /* Add parsed literals to allocated clause object 'clause'. */
  LitID *p, *e, *clause_lits_p = clause->lits;
  for (p = qr->parsed_literals.start, e = qr->parsed_literals.top; p < e; p++)
    {
      LitID lit = *p;
      VarID varid = LIT2VARID (lit);
      ABORT_APP (varid >= qr->pcnf.size_vars,
                       "variable ID in clause exceeds max. ID given in preamble!");
      Var *var = LIT2VARPTR (qr->pcnf.vars, lit);
      ABORT_APP (!var->scope,
                       "variable has not been declared in a scope!");

      /* Check for complementary and multiple occurrences of literals. */
      if (VAR_POS_MARKED (var))
        {
          if (LIT_POS (lit))
            {
              if (qr->options.verbosity >= 2)
                fprintf (stderr, "literal %d appears multiple times in clause!\n", lit);
              /* Ignore multiple occurrences. */
              assert (clause->num_lits > 0);
              clause->num_lits--;
              continue;
            }

          if (LIT_NEG (lit))
            {
              if (qr->options.verbosity >= 2)
                fprintf (stderr, "Clause has complementary literals!\n");
              taut = 1;
              break;
            }
        }
      else if (VAR_NEG_MARKED (var))
        {
          if (LIT_NEG (lit))
            {
              if (qr->options.verbosity >= 2)
                fprintf (stderr, "literal %d appears multiple times in clause!\n", lit);
              /* Ignore multiple occurrences. */
              assert (clause->num_lits > 0);
              clause->num_lits--;
              continue;
            }

          if (LIT_POS (lit))
            {
              if (qr->options.verbosity >= 2)
                fprintf (stderr, "Clause has complementary literals!");
              taut = 1;
              break;
            }
        }
      else
        {
          assert (!VAR_MARKED (var));
          if (LIT_NEG (lit))
            VAR_NEG_MARK (var);
          else
            VAR_POS_MARK (var);
        }

      assert (clause_lits_p < clause->lits + clause->num_lits);
      /* Add literal to clause object. */
      *clause_lits_p++ = *p;
      /* Count universal literals. */
      if (var->scope->type == QTYPE_FORALL)
        clause->cnt_univ_lits++;
    }

  /* Unmark variables. */
  for (p = qr->parsed_literals.start, e = qr->parsed_literals.top; p < e; p++)
    VAR_UNMARK (LIT2VARPTR (qr->pcnf.vars, *p));

  /* Return early if clause is tautological. */
  if (taut)
    return 1;

  /* Sort literals by nesting levels. */
  SORT (qr, LitID, compare_lits_by_nesting, clause->lits,
        clause->num_lits);
#ifndef NDEBUG
  assert_lits_sorted (qr, clause->lits, clause->lits + clause->num_lits);
#endif

  /* Reduction of trailing universal literals. */
  Var *vars = qr->pcnf.vars;
  for (e = clause->lits, p = e + clause->num_lits - 1; p >= e; p--)
    {
      LitID lit = *p;
      Var *v = LIT2VARPTR (vars, lit);
      if (v->scope->type == QTYPE_FORALL)
        {
          clause->num_lits--;
          clause->cnt_univ_lits--;
        }
      else
        break;
    }

  assert (clause->cnt_univ_lits == count_qtype_literals (qr, clause, QTYPE_FORALL));
  qr->total_univ_lits += clause->cnt_univ_lits;

  assert (clause->num_lits == 0 || clause->cnt_univ_lits < clause->num_lits);

  if (clause->num_lits == 0)
    qr->parsed_empty_clause = 1;
  else if (clause->num_lits == 1)
    PUSH_STACK (qr->mm, qr->unit_input_clauses, clause);
  
  for (p = clause->lits, e = p + clause->num_lits; p < e; p++)
    {
      LitID lit = *p;
      Var *var = LIT2VARPTR (qr->pcnf.vars, lit);
      /* Push clause object on stack of occurrences. */
      if (LIT_NEG (lit))
        {
          PUSH_STACK (qr->mm, var->neg_occ_clauses, clause);
          qr->total_occ_cnts++;
          if ((unsigned int) COUNT_STACK (var->neg_occ_clauses) > qr->max_occ_cnt)
            qr->max_occ_cnt = (unsigned int) COUNT_STACK (var->neg_occ_clauses);
        }
      else
        {
          PUSH_STACK (qr->mm, var->pos_occ_clauses, clause);
          qr->total_occ_cnts++;
          if ((unsigned int) COUNT_STACK (var->pos_occ_clauses) > qr->max_occ_cnt)
            qr->max_occ_cnt = (unsigned int) COUNT_STACK (var->pos_occ_clauses);
        }
    }

  qr->total_clause_lengths += clause->num_lits;
  if (clause->num_lits > qr->max_clause_length)
    qr->max_clause_length = clause->num_lits;
  
  /* Append clause to list of clauses. */
  LINK_LAST (qr->pcnf.clauses, clause, link);

  return 0;
}

static void
init_watched_literals (QRATPlusPre * qr, Clause *c)
{
  assert (c->lw_index == WATCHED_LIT_INVALID_INDEX);
  assert (c->rw_index == WATCHED_LIT_INVALID_INDEX);

  /* Do not attempt to set watchers in unit or empty clause. Unit clauses are
     collected on stack 'qr->unit_input_clauses' and assigned each time when
     we apply QBCP. */
  if (c->num_lits <= 1)
    return;

  /* NOTE / TODO: this code is repeated in 'retract_re_init_lit_watchers' in
     file 'qbcp.c'. */
  /* Set right watched literal. */
  c->rw_index = c->num_lits - 1;
  LitID lit = c->lits[c->rw_index];
  Var *var = LIT2VARPTR (qr->pcnf.vars, lit);
  assert (var->assignment == ASSIGNMENT_UNDEF);
  assert (var->scope->type == QTYPE_EXISTS);
  /* Add 'c' to watched occurrences. */
  if (LIT_NEG (lit))
    PUSH_STACK (qr->mm, var->watched_neg_occ_clauses, c);
  else
    PUSH_STACK (qr->mm, var->watched_pos_occ_clauses, c);

  /* Set left watched literal. */
  c->lw_index = c->rw_index - 1;
  lit = c->lits[c->lw_index];
  var = LIT2VARPTR (qr->pcnf.vars, lit);
  assert (var->assignment == ASSIGNMENT_UNDEF);
  /* Add 'c' to watched occurrences. */
  if (LIT_NEG (lit))
    PUSH_STACK (qr->mm, var->watched_neg_occ_clauses, c);
  else
    PUSH_STACK (qr->mm, var->watched_pos_occ_clauses, c);
}

/* Check and add a parsed clause to the PCNF data structures. */
static void
import_parsed_clause (QRATPlusPre * qr)
{
  assert (qr->parsing_prefix_completed);
  assert (!qr->opened_scope);
  /* Allocate new clause object capable of storing 'num_lits' literals. The
     literals on the stack 'parsed_literals' will be copied to the new clause
     object. */
  int num_lits = COUNT_STACK (qr->parsed_literals);
  Clause *clause = mm_malloc (qr->mm, sizeof (Clause) +
                              num_lits * sizeof (LitID));
  clause->id = ++qr->cur_clause_id;
  clause->num_lits = num_lits;
  clause->size_lits = num_lits;
  clause->rw_index = WATCHED_LIT_INVALID_INDEX;
  clause->lw_index = WATCHED_LIT_INVALID_INDEX;

  /* Add the parsed clause to the formula and to the stacks of variable
     occurrences, provided that it does not contain complementary or multiple
     literals of the same variable. */
  if (!check_and_add_clause (qr, clause))
    {
      init_watched_literals (qr, clause);
      
      if (qr->options.verbosity >= 2)
        {
          fprintf (stderr, "Imported clause: ");
          print_lits (qr, stderr, clause->lits, clause->num_lits, 1);
        }
    }
  else
    {
      if (qr->options.verbosity >= 2)
        fprintf (stderr, "Deleting tautological clause.\n");
      mm_free (qr->mm, clause, sizeof (Clause) + clause->size_lits * sizeof (LitID));
    }
}

/* Add parsed scope to data structures. */
static void
import_parsed_scope_variables (QRATPlusPre * qr)
{
  assert (!qr->parsing_prefix_completed);
  assert (qr->opened_scope);
  assert (EMPTY_STACK (qr->opened_scope->vars));
  ABORT_APP (EMPTY_STACK (qr->parsed_literals), "attempted to add empty scope!\n");
  LitID *p, *e;
  for (p = qr->parsed_literals.start, e = qr->parsed_literals.top; p < e; p++)
    {
      LitID varid = *p;
      ABORT_APP (varid <= 0,
                       "variable ID in scope must be positive!\n");
      ABORT_APP ((VarID) varid >= qr->pcnf.size_vars,
                       "variable ID in scope exceeds max. ID given in preamble!");

      /* Add variable ID to list of IDs in the scope. */
      PUSH_STACK (qr->mm, qr->opened_scope->vars, varid);
      Var *var = VARID2VARPTR (qr->pcnf.vars, varid);
      /* Set variable ID and pointer to scope of variable. */
      ABORT_APP (var->id, "variable already quantified!\n");
      var->id = varid;
      assert (!var->scope);
      var->scope = qr->opened_scope;
      qr->actual_num_vars++;
    }
  /* The current scope has been added to the scope list already. */
  assert (qr->opened_scope == qr->pcnf.scopes.first ||
          (qr->opened_scope->link.prev && !qr->opened_scope->link.next));
  assert (qr->opened_scope != qr->pcnf.scopes.first ||
          (!qr->opened_scope->link.prev && !qr->opened_scope->link.next));
}

static void
update_scope_nestings (QRATPlusPre * qr)
{
  /* Update the nesting levels of the scopes. Scope numbering starts
     at nesting level 0. */
  Nesting nesting = 0;
  Scope *s;
  for (s = qr->pcnf.scopes.first; s; s = s->link.next)
    s->nesting = nesting++;
}


/* Merge and remove adjacent scopes of the same quantifier type. */
static void
merge_adjacent_same_type_scopes (QRATPlusPre * qr)
{
  MemMan *mem = qr->mm;
  unsigned int modified = 0;
  Scope *s, *n;
  for (s = qr->pcnf.scopes.first; s; s = n)
    {
      n = s->link.next;
      if (n && s->type == n->type)
        {                       
          /* Adjacent scopes have same type -> merge 'n' into 's'. */
          VarIDStack *scope_vars = &s->vars;
          VarID *p, *e, v;
          for (p = n->vars.start, e = n->vars.top; p < e; p++)
            {
              v = *p;
              PUSH_STACK (mem, *scope_vars, v);
              assert (qr->pcnf.vars[v].scope == n);
              qr->pcnf.vars[v].scope = s;
            }

          UNLINK (qr->pcnf.scopes, n, link);
          DELETE_STACK (qr->mm, n->vars);
          mm_free (qr->mm, n, sizeof (Scope));
          n = s;
          modified = 1;
        }
    }

  assert (!qr->pcnf.scopes.first || qr->pcnf.scopes.first->nesting == 0);

  if (modified)
    update_scope_nestings (qr);
}

/* Collect parsed literals of a scope or a clause on auxiliary stack to be
   imported and added to data structures later. */
static void
collect_parsed_literal (QRATPlusPre * qr, int num)
{
  if (num == 0)
    {
      if (qr->opened_scope)
        {
          assert (!qr->parsing_prefix_completed);
          import_parsed_scope_variables (qr);
          qr->opened_scope = 0;
        }
      else
        {
          if (!qr->parsing_prefix_completed)
            {
              qr->parsing_prefix_completed = 1;
              merge_adjacent_same_type_scopes (qr);
            }
          import_parsed_clause (qr);
        }
      RESET_STACK (qr->parsed_literals);
    }
  else
    PUSH_STACK (qr->mm, qr->parsed_literals, num);
}

#define PARSER_READ_NUM(num, c)                        \
  assert (isdigit (c));                                \
  num = 0;					       \
  do						       \
    {						       \
      num = num * 10 + (c - '0');		       \
    }						       \
  while (isdigit ((c = getc (in))));

#define PARSER_SKIP_SPACE_DO_WHILE(c)		     \
  do						     \
    {                                                \
      c = getc (in);				     \
    }                                                \
  while (isspace (c));

#define PARSER_SKIP_SPACE_WHILE(c)		     \
  while (isspace (c))                                \
    c = getc (in);

#define PARSER_SKIP_COMMENTS_WHILE(c)                \
  while (c == 'c')                                   \
    {                                                \
      while ((c = getc (in)) != '\n' && c != EOF)    \
        ;                                            \
      c = getc (in);                                 \
      PARSER_SKIP_SPACE_WHILE(c);                    \
    }                                                \
  
static void
parse (QRATPlusPre * qr, FILE * in)
{
  int neg = 0, preamble_found = 0;
  LitID num = 0;
  QuantifierType scope_type = QTYPE_UNDEF;

  assert (in);

  int c;
  while ((c = getc (in)) != EOF)
    {
      PARSER_SKIP_SPACE_WHILE (c);

      PARSER_SKIP_COMMENTS_WHILE (c);

      PARSER_SKIP_SPACE_WHILE (c);

      if (c == 'p')
        {
          /* parse preamble */
          PARSER_SKIP_SPACE_DO_WHILE (c);
          if (c != 'c')
            goto MALFORMED_PREAMBLE;
          PARSER_SKIP_SPACE_DO_WHILE (c);
          if (c != 'n')
            goto MALFORMED_PREAMBLE;
          PARSER_SKIP_SPACE_DO_WHILE (c);
          if (c != 'f')
            goto MALFORMED_PREAMBLE;
          PARSER_SKIP_SPACE_DO_WHILE (c);
          if (!isdigit (c))
            goto MALFORMED_PREAMBLE;

          /* Read number of variables */
          PARSER_READ_NUM (num, c);

          /* Allocate array of variable IDs of size 'num + 1', since 0 is an
             invalid variable ID. */
          set_up_var_table (qr, num);

          PARSER_SKIP_SPACE_WHILE (c);
          if (!isdigit (c))
            goto MALFORMED_PREAMBLE;

          /* Read number of clauses */
          PARSER_READ_NUM (num, c);

          qr->declared_num_clauses = num;

          if (qr->options.verbosity >= 1)
            fprintf (stderr, "parsed preamble: p cnf %d %d\n",
                     (qr->pcnf.size_vars - 1), qr->declared_num_clauses);

          preamble_found = 1;
          goto PARSE_SCOPE_OR_CLAUSE;

        MALFORMED_PREAMBLE:
          ABORT_APP (1, "malformed preamble!\n");
          return;
        }
      else
        {
          ABORT_APP (1, "expecting preamble!\n");
          return;
        }

    PARSE_SCOPE_OR_CLAUSE:

      PARSER_SKIP_SPACE_WHILE (c);

      PARSER_SKIP_COMMENTS_WHILE (c);

      PARSER_SKIP_SPACE_WHILE (c);

      if (c == 'a' || c == 'e')
        {
          ABORT_APP (qr->parsing_prefix_completed,
                     "must not interleave addition of clauses and scopes!\n");

          /* Open a new scope */
          if (c == 'a')
            scope_type = QTYPE_FORALL;
          else
            scope_type = QTYPE_EXISTS;

          ABORT_APP (qr->opened_scope,
                           "must close scope by '0' before opening a new scope!\n");

          open_new_scope (qr, scope_type);

          PARSER_SKIP_SPACE_DO_WHILE (c);
        }

      if (!isdigit (c) && c != '-')
        {
          if (c == EOF)
            return;
          ABORT_APP (1, "expecting digit or '-'!\n");
          return;
        }
      else
        {
          if (c == '-')
            {
              neg = 1;
              if (!isdigit ((c = getc (in))))
                {
                  ABORT_APP (1, "expecting digit!\n");
                  return;
                }
            }

          /* parse a literal or variable ID */
          PARSER_READ_NUM (num, c);
          num = neg ? -num : num;

          collect_parsed_literal (qr, num);

          neg = 0;

          goto PARSE_SCOPE_OR_CLAUSE;
        }
    }

  if (!preamble_found)
    ABORT_APP (1, "preamble missing!\n");
}

/* -------------------- END: QDIMACS PARSING -------------------- */

/* -------------------- START: COMMAND LINE PARSING -------------------- */

static int
isnumstr (char *str)
{
  /* Empty string is not considered as number-string. */
  if (!*str)
    return 0;
  char *p;
  for (p = str; *p; p++)
    {
      if (!isdigit (*p))
        return 0;
    }
  return 1;
}

/* Parse command line arguments to set options accordingly. Run the program
   with '-h' or '--help' to print usage information. */
static char *
parse_cmd_line_options (QRATPlusPre * qr, int argc, char **argv)
{
  char *result = 0;
  int opt_cnt;
  for (opt_cnt = 1; opt_cnt < argc; opt_cnt++)
    {
      char *opt_str = argv[opt_cnt];

      if (!strcmp (opt_str, "-h") || !strcmp (opt_str, "--help"))
        {
          qr->options.print_usage = 1;
        }
      else if (!strcmp (opt_str, "--version"))
        {
          qr->options.print_version = 1;
        }
      else if (!strcmp (opt_str, "--no-qbce"))
        {
          qr->options.no_qbce = 1;
        }
      else if (!strcmp (opt_str, "--no-qrate"))
        {
          qr->options.no_qrate = 1;
        }
      else if (!strcmp (opt_str, "--pure-lits-full-reschedule"))
        {
          qr->options.pure_lits_full_reschedule = 1;
        }
      else if (!strcmp (opt_str, "--no-eabs"))
        {
          qr->options.no_eabs = 1;
        }
      else if (!strcmp (opt_str, "--no-eabs-improved-nesting"))
        {
          qr->options.no_eabs_improved_nesting = 1;
        }
      else if (!strcmp (opt_str, "--ignore-inner-lits"))
        {
          qr->options.ignore_inner_lits = 1;
        }
      else if (!strcmp (opt_str, "--no-ble"))
        {
          qr->options.no_ble = 1;
        }
      else if (!strcmp (opt_str, "--no-qratu"))
        {
          qr->options.no_qratu = 1;
        }
      else if (!strcmp (opt_str, "--pure-lits"))
        {
          qr->options.pure_lits = 1;
        }
      else if (!strcmp (opt_str, "--permute"))
        {
          qr->options.permute = 1;
        }
      else if (!strcmp (opt_str, "--qbce-check-taut-by-nesting"))
        {
          qr->options.qbce_check_taut_by_nesting = 1;
        }
      else if (!strncmp (opt_str, "--limit-qbcp-cur-props=", strlen ("--limit-qbcp-cur-props=")))
        {
          opt_str += strlen ("--limit-qbcp-cur-props=");
          if (isnumstr (opt_str))
            qr->limit_qbcp_cur_props = atoi (opt_str);
          else
            result = "Expecting number after '--limit-qbcp-cur-props='";
        }
      else if (!strncmp (opt_str, "--limit-global-iterations=", strlen ("--limit-global-iterations=")))
        {
          opt_str += strlen ("--limit-global-iterations=");
          if (isnumstr (opt_str))
            qr->limit_global_iterations = atoi (opt_str);
          else
            result = "Expecting positive number after '--limit-global-iterations='";
        }
      else if (!strncmp (opt_str, "--soft-time-limit=", strlen ("--soft-time-limit=")))
        {
          opt_str += strlen ("--soft-time-limit=");
          if (isnumstr (opt_str))
            {
              qr->soft_time_limit = atoi (opt_str);
              if (qr->soft_time_limit <= 0)
                {
                  result = "Expecting non-zero value for soft-time-lmit";
                  print_abort_err ("%s!\n\n", result);
                }
              fprintf (stderr, "Setting soft time limit of %d seconds\n",
                       qr->soft_time_limit);
            }
          else
            result = "Expecting number after '--soft-time-limit='";
        }
      else if (!strncmp (opt_str, "--limit-max-occ-cnt=", strlen ("--limit-max-occ-cnt=")))
        {
          opt_str += strlen ("--limit-max-occ-cnt=");
          if (isnumstr (opt_str))
            qr->limit_max_occ_cnt = atoi (opt_str);
          else
            result = "Expecting number after '--limit-max-occ-cnt='";
        }
      else if (!strncmp (opt_str, "--limit-max-clause-len=", strlen ("--limit-max-clause-len=")))
        {
          opt_str += strlen ("--limit-max-clause-len=");
          if (isnumstr (opt_str))
            qr->limit_max_clause_len = atoi (opt_str);
          else
            result = "Expecting number after '--limit-max-clause-len='";
        }
      else if (!strncmp (opt_str, "--limit-min-clause-len=", strlen ("--limit-min-clause-len=")))
        {
          opt_str += strlen ("--limit-min-clause-len=");
          if (isnumstr (opt_str))
            qr->limit_min_clause_len = atoi (opt_str);
          else
            result = "Expecting number after '--limit-min-clause-len='";
        }
      else if (!strncmp (opt_str, "--seed=", strlen ("--seed=")))
        {
          opt_str += strlen ("--seed=");
          if (isnumstr (opt_str))
            qr->options.seed = atoi (opt_str);
          else
            result = "Expecting number after '--seed='";
        }
      else if (!strcmp (opt_str, "--no-at"))
        {
          qr->options.no_asymm_taut_check = 1;
        }
      else
        if (!strncmp (opt_str, "--print-formula", strlen ("--print-formula")))
        {
          qr->options.print_formula = 1;
        }
      else if (!strcmp (opt_str, "-v"))
        {
          qr->options.verbosity++;
        }
      else if (isnumstr (opt_str))
        {
          qr->options.max_time = atoi (opt_str);
          if (qr->options.max_time == 0)
            {
              result = "Expecting non-zero value for max-time";
              print_abort_err ("%s!\n\n", result);
            }
        }
      else if (!qr->options.in_filename)
        {
          qr->options.in_filename = opt_str;
          /* Check input file. */
          DIR *dir;
          if ((dir = opendir (qr->options.in_filename)) != NULL)
            {
              closedir (dir);
              print_abort_err ("input file '%s' is a directory!\n\n",
                               qr->options.in_filename);
            }
          FILE *input_file = fopen (qr->options.in_filename, "r");
          if (!input_file)
            {
              print_abort_err ("could not open input file '%s'!\n\n",
                               qr->options.in_filename);
            }
          else
            qr->options.in = input_file;
        }
      else
        {
          print_abort_err ("unknown option '%s'!\n\n", opt_str);
        }
    }
  
  return result;
}

/* -------------------- END: COMMAND LINE PARSING -------------------- */

/* -------------------- START: HELPER FUNCTIONS -------------------- */

/* Set signal handler. */
static void
sig_handler (int sig)
{
  fprintf (stderr, "\n\n SIG RECEIVED\n\n");
  signal (sig, SIG_DFL);
  raise (sig);
}

/* Set signal handler. */
static void
sigalrm_handler (int sig)
{
  fprintf (stderr, "\n\n SIGALRM RECEIVED\n\n");
  signal (sig, SIG_DFL);
  raise (sig);
}

/* Set signal handler. */
static void
set_signal_handlers (void)
{
  signal (SIGINT, sig_handler);
  signal (SIGTERM, sig_handler);
  signal (SIGALRM, sigalrm_handler);
  signal (SIGXCPU, sigalrm_handler);
}

static void
print_usage ()
{
  fprintf (stdout, USAGE);
}

static void
print_version ()
{
  fprintf (stdout, VERSION);
}

/* Free allocated memory. */
static void
cleanup (QRATPlusPre * qr)
{
  if (qr->options.in_filename)
    fclose (qr->options.in);

  Clause **cp, **ce;
  for (cp = qr->redundant_clauses.start, ce = qr->redundant_clauses.top; cp < ce; cp++)
    {
      Clause *c = *cp;
      assert (c->redundant);
      /* To prevent double free of memory, must unlink redundant clauses from
         PCNF, if not already done so. */
      if (c->link.prev || c->link.next || c == qr->pcnf.clauses.first)
        UNLINK (qr->pcnf.clauses, c, link);
      mm_free (qr->mm, c, sizeof (Clause) + c->size_lits * sizeof (LitID));
    }

  DELETE_STACK (qr->mm, qr->parsed_literals);
  DELETE_STACK (qr->mm, qr->redundant_clauses);
  DELETE_STACK (qr->mm, qr->witness_clauses);
  DELETE_STACK (qr->mm, qr->unit_input_clauses);
  DELETE_STACK (qr->mm, qr->qbcp_queue);
  DELETE_STACK (qr->mm, qr->lw_update_clauses);
  DELETE_STACK (qr->mm, qr->pure_input_lits);

  Var *vp, *ve;
  for (vp = qr->pcnf.vars, ve = vp + qr->pcnf.size_vars; vp < ve; vp++)
    {
      DELETE_STACK (qr->mm, vp->pos_occ_clauses);
      DELETE_STACK (qr->mm, vp->neg_occ_clauses);
      DELETE_STACK (qr->mm, vp->watched_pos_occ_clauses);
      DELETE_STACK (qr->mm, vp->watched_neg_occ_clauses);
    }
  mm_free (qr->mm, qr->pcnf.vars, qr->pcnf.size_vars * sizeof (Var));

  Scope *s, *sn;
  for (s = qr->pcnf.scopes.first; s; s = sn)
    {
      sn = s->link.next;
      DELETE_STACK (qr->mm, s->vars);
      mm_free (qr->mm, s, sizeof (Scope));
    }

  Clause *c, *cn;
  for (c = qr->pcnf.clauses.first; c; c = cn)
    {
      cn = c->link.next;
      mm_free (qr->mm, c, sizeof (Clause) + c->size_lits * sizeof (LitID));
    }
}

/* Print (simplified) formula to file 'out'. */
static void
print_formula (QRATPlusPre * qr, FILE * out)
{
  if (qr->parsed_empty_clause)
    {
      fprintf (out, "p cnf 0 1\n");
      fprintf (out, "0\n");
      return;
    }

  /* Print preamble. */
  assert (qr->pcnf.size_vars > 0);
  assert (qr->actual_num_clauses >= qr->cnt_redundant_clauses);
  fprintf (out, "p cnf %d %d\n", (qr->pcnf.size_vars - 1),
           (qr->actual_num_clauses - qr->cnt_redundant_clauses));

  /* Print prefix. */
  Scope *s;
  for (s = qr->pcnf.scopes.first; s; s = s->link.next)
    {
      fprintf (out, "%c ", SCOPE_FORALL (s) ? 'a' : 'e');
      print_lits (qr, out, (LitID *) s->vars.start,
                  COUNT_STACK (s->vars), 0);
    }

  /* Print clauses. */
  Clause *c;
  for (c = qr->pcnf.clauses.first; c; c = c->link.next)
    if (!c->redundant)
      print_lits (qr, out, c->lits, c->num_lits, 0);
}

/* NOTE / TODO: this function appears also in other module, merge. */
static double
time_stamp ()
{
  double result = 0;
  struct rusage usage;

  if (!getrusage (RUSAGE_SELF, &usage))
    {
      result += usage.ru_utime.tv_sec + 1e-6 * usage.ru_utime.tv_usec;
      result += usage.ru_stime.tv_sec + 1e-6 * usage.ru_stime.tv_usec;
    }

  return result;
}

/* -------------------- END: HELPER FUNCTIONS -------------------- */

/* -------------------- START: SETUP -------------------- */

static void
set_default_options (QRATPlusPre * qr)
{
  qr->options.in_filename = 0;
  qr->options.in = stdin;
  qr->options.print_usage = 0;
  /* Set default limits. */
  qr->limit_qbcp_cur_props = UINT_MAX;
  qr->limit_max_occ_cnt = UINT_MAX;
  qr->limit_max_clause_len = UINT_MAX;
  qr->limit_min_clause_len = 0;
  /* Setting 'qr->eabs_nesting' to UINT_MAX has the effect that ALL
     variables are treating as existentially quantified,. This way, we
     obtain a full propositional abstraction of the given QBF. */
  qr->eabs_nesting = UINT_MAX;
  qr->eabs_nesting_aux = 0;
  qr->limit_global_iterations = UINT_MAX;
}

static void
setup (QRATPlusPre * qr)
{
  /* Initialize simple memory manager. */
  MemMan *mm = mm_create ();
  qr->mm = mm;
  set_default_options (qr);
}

#ifndef NDEBUG
static void
assert_formula_integrity (QRATPlusPre * qr)
{
  Clause *c;
  for (c = qr->pcnf.clauses.first; c; c = c->link.next)
    {
      assert_lits_sorted (qr, c->lits, c->lits + c->num_lits);
      LitID last = c->num_lits ? c->lits[c->num_lits - 1] : 0;
      Var *last_var = last ? LIT2VARPTR (qr->pcnf.vars, last) : 0;
      assert (!last_var || last_var->scope->type == QTYPE_EXISTS);
      if (c->num_lits == 1)
        {
          /* Unit input clauses must appear on stack of collected unit clauses. */
          Clause **uc_p, **uc_e;
          for (uc_p = qr->unit_input_clauses.start, uc_e = qr->unit_input_clauses.top;
               uc_p < uc_e; uc_p++)
            {
              if ((*uc_p) == c)
                break;
            }
          assert (uc_p < uc_e);
        }
      /* Clauses with only universal literals would reduced to empty clause. */
      assert (c->num_lits == 0 || c->cnt_univ_lits < c->num_lits);
      assert (c->cnt_univ_lits == count_qtype_literals (qr, c, QTYPE_FORALL));
    }
  Scope *s;
  for (s = qr->pcnf.scopes.first; s; s = s->link.next)
    {
      if (s->link.next)
        {
          assert (s->nesting + 1 == s->link.next->nesting);
          assert (s->type != s->link.next->type);
        }
    }
}
#endif

/* Collect universal literals that are pure in the input formula. */
static void
init_pure_literals (QRATPlusPre * qr)
{
  assert (qr->options.pure_lits);
  Var *var, *var_e;
  for (var = qr->pcnf.vars, var_e = var + qr->pcnf.size_vars; var < var_e; var++)
    {
      if (var->id && var->scope->type == QTYPE_FORALL)
        {
          assert (var->assignment == ASSIGNMENT_UNDEF);
          if (EMPTY_STACK (var->neg_occ_clauses))
            {
              if (!EMPTY_STACK (var->pos_occ_clauses))
                {
                  /* Variable has only positive occurrences. */
                  assert (!var->input_pure_collected);
                  var->input_pure_collected = 1;
                  PUSH_STACK (qr->mm, qr->pure_input_lits, -var->id);
                }
            }
          else if (EMPTY_STACK (var->pos_occ_clauses))
            {
              /* Variable has only negative occurrences. */
              assert (!var->input_pure_collected);
              var->input_pure_collected = 1;
              PUSH_STACK (qr->mm, qr->pure_input_lits, var->id);
            }
        }
    }
}

/* NOTE / TODO: this function appears also in other module, merge. */
static int
exceeded_soft_time_limit (QRATPlusPre * qr)
{
  if (qr->soft_time_limit &&
      (time_stamp () - qr->start_time) > qr->soft_time_limit)
    return 1;
  else
    return 0;
}

/* -------------------- END: SETUP -------------------- */

int
main (int argc, char **argv)
{  
  double start_time = time_stamp ();
  int result = 0;
  /* Initialize QRATPlusPre object. */
  QRATPlusPre qr;
  memset (&qr, 0, sizeof (QRATPlusPre));
  setup (&qr);
  qr.start_time = start_time;

  char *err_str = parse_cmd_line_options (&qr, argc, argv);
  if (err_str)
    print_abort_err ("error in command line: '%s'\n", err_str);
    
  set_signal_handlers ();
  srand (qr.options.seed);

  ABORT_APP (!(!qr.options.pure_lits || !qr.options.no_eabs), 
             "Must enable abstraction by --eabs when using pure literals!");
  /* Do not allow pure literals with QRATU. */
  ABORT_APP (qr.options.pure_lits && !qr.options.no_qratu, 
             "Temporary restriction: QRATU must not be combined with pure literals!");

  if (qr.options.print_usage || qr.options.print_version)
    {
      if (qr.options.print_usage)
        print_usage ();
      else
        print_version ();
      cleanup (&qr);
      return result;
    }

  if (qr.options.max_time)
    {
      fprintf (stderr, "Setting run time limit of %d seconds\n",
               qr.options.max_time);
      alarm (qr.options.max_time);
    }

  /* Parse QDIMACS formula and simplify, if appropriate command line options
     are given. */

  parse (&qr, qr.options.in);
  qr.actual_num_clauses = qr.pcnf.clauses.cnt;

  int exceeded = 0;
  
  if ((exceeded = exceeded_soft_time_limit (&qr)))
    fprintf (stderr, "Exceeded soft time limit of %u sec\n", qr.soft_time_limit);
  
  if (!exceeded && qr.options.pure_lits)
    init_pure_literals (&qr);

#ifndef NDEBUG
  assert_formula_integrity (&qr);
#endif

  if (!exceeded &&
      (exceeded = exceeded_soft_time_limit (&qr)))
    fprintf (stderr, "Exceeded soft time limit of %u sec\n", qr.soft_time_limit);
  
  if (!qr.parsed_empty_clause)
    {
      int changed = 1;
      while (changed && !exceeded)
        {
          if (qr.cnt_global_iterations >= qr.limit_global_iterations)
            {
              if (qr.options.verbosity >= 1)
                fprintf (stderr, "\nGlobal iteration limit %u reached, "\
                         "exiting simplification loop\n", qr.limit_global_iterations);
              break;
            }

          qr.cnt_global_iterations++;

          if (qr.options.verbosity >= 1)
            fprintf (stderr, "\n*********\nGlobal iteration: %u\n*********\n", 
                     qr.cnt_global_iterations);

          changed = 0;

          if (!qr.options.no_qbce || !qr.options.no_asymm_taut_check || 
              !qr.options.no_qrate)
            find_and_mark_redundant_clauses (&qr);
          
          if ((exceeded = exceeded_soft_time_limit (&qr)))
            fprintf (stderr, "Exceeded soft time limit of %u sec\n", qr.soft_time_limit);

          /* Trigger a new iteration including clause redundancy checks if any
             redundant literals were found. */
          if (!exceeded && (!qr.options.no_ble || !qr.options.no_qratu))
            changed = find_and_delete_redundant_literals (&qr) || changed;

          if (!exceeded &&
              (exceeded = exceeded_soft_time_limit (&qr)))
            fprintf (stderr, "Exceeded soft time limit of %u sec\n", qr.soft_time_limit);
        }
    }

  /* Print formula to stdout. */
  if (qr.options.print_formula)
    print_formula (&qr, stdout);

  if (qr.options.verbosity >= 1)
    {
      /* Print statistics. */
      fprintf (stderr, "\nDONE, printing statistics:\n");
      if (!qr.options.max_time)
        fprintf (stderr, "  time limit: not set\n");
      else
        fprintf (stderr, "  time limit: %d\n", qr.options.max_time);

      if (!qr.soft_time_limit)
        fprintf (stderr, "  soft time limit: not set\n");
      else
        fprintf (stderr, "  soft time limit: %d (exceeded: %s)\n", qr.soft_time_limit, exceeded ? "yes" : "no");
      
      fprintf (stderr, "  printing formula: %s\n",
               qr.options.print_formula ? "yes" : "no");
      fprintf (stderr, "  Global iterations: %d\n", qr.cnt_global_iterations);
      fprintf (stderr, "  CE iterations: %d\n", qr.cnt_qbce_iterations);
      fprintf (stderr, "  CE checks: %llu ( %f %% of initial CNF)\n", 
               qr.cnt_qbce_checks, qr.actual_num_clauses ? 
               ((qr.cnt_qbce_checks / (float)qr.actual_num_clauses) * 100) : 0);
      fprintf (stderr, "  CE: %d redundant clauses of total %d clauses ( %f %% of initial CNF)\n",
               qr.cnt_redundant_clauses, qr.actual_num_clauses, qr.actual_num_clauses ? 
               ((qr.cnt_redundant_clauses / (float)qr.actual_num_clauses) * 100) : 0);
      fprintf (stderr, "  QRAT propagations: total %llu avg. %f per check, total %llu checks of outer res.\n", 
               qr.qbcp_total_props, qr.qrat_qbcp_checks ? (float)qr.qbcp_total_props /  qr.qrat_qbcp_checks : 0, qr.qrat_qbcp_checks);
      fprintf (stderr, "  QRAT success. propagations: total %llu avg. %f per check, total %llu checks of outer res.\n", 
               qr.qbcp_successful_checks_props, qr.qrat_qbcp_successful_checks ? (float)qr.qbcp_successful_checks_props /  
               qr.qrat_qbcp_successful_checks : 0, qr.qrat_qbcp_successful_checks);

      fprintf (stderr, "  QRAT  propagation limit reached: %u times in total %llu checks, with limit set to %u\n", 
               qr.limit_qbcp_cur_props_reached, qr.qrat_qbcp_checks, qr.limit_qbcp_cur_props);
      fprintf (stderr, "  Occ. count: max %u avg %f per used var, total %u used vars\n", qr.max_occ_cnt, 
               qr.actual_num_vars ? qr.total_occ_cnts / (float)qr.actual_num_vars : 0, qr.actual_num_vars);
      fprintf (stderr, "  Clause length: max %u avg %f per clause, total %u clauses\n", qr.max_clause_length, 
               qr.pcnf.clauses.cnt ? qr.total_clause_lengths / (float)qr.pcnf.clauses.cnt : 0, qr.pcnf.clauses.cnt);   
      fprintf (stderr, "  QBCP total calls %llu %s using EABS with avg abs-nesting %f max nesting %u\n", 
               qr.qbcp_total_calls, !qr.options.no_eabs ? "" : "not", !qr.options.no_eabs ? 
               (qr.qbcp_total_calls ? (qr.qbcp_total_eabs_nestings / (float)qr.qbcp_total_calls) : 0) : 
               UINT_MAX, qr.pcnf.scopes.last ? qr.pcnf.scopes.last->nesting : UINT_MAX);
      fprintf (stderr, "  QBCP total assignments %llu ( %f %% pure) avg %f %% per QBCP call\n", qr.total_assignments, 
               qr.total_assignments ? (qr.total_pure_assignments / (float) qr.total_assignments) : 0, 
               qr.qbcp_total_calls ? (qr.total_assignments / (float)qr.qbcp_total_calls) : 0);
      fprintf (stderr, "  QBCP pure lits total occs seen %llu avg %f per counter update, total %llu counter updates\n", 
               qr.pure_lits_occs_seen, qr.pure_lits_cnt_update_calls ? 
               (qr.pure_lits_occs_seen / (float)qr.pure_lits_cnt_update_calls) : 0, qr.pure_lits_cnt_update_calls);

      fprintf (stderr, "  CE total OR checks %llu avg OR checks per CE check %f total lits seen %llu avg lits seen per OR check %f\n", 
               qr.clause_redundancy_or_checks, qr.cnt_qbce_checks ? (qr.clause_redundancy_or_checks / (float)qr.cnt_qbce_checks) : 0, 
               qr.clause_redundancy_or_checks_lits_seen, qr.clause_redundancy_or_checks ? 
               (qr.clause_redundancy_or_checks_lits_seen / (float)qr.clause_redundancy_or_checks) : 0);
      
      fprintf (stderr, "  QRATU iterations: %d\n", qr.cnt_qratu_iterations);
      fprintf (stderr, "  QRATU checks: %llu ( %f %% of initial CNF)\n", 
               qr.cnt_qratu_checks, qr.actual_num_clauses ? 
               ((qr.cnt_qratu_checks / (float)qr.actual_num_clauses) * 100) : 0);
      fprintf (stderr, "  QRATU: %d redundant literals of %llu total univ lits ( %f %% in initial formula)\n", 
               qr.cnt_redundant_literals, qr.total_univ_lits, qr.total_univ_lits ? 
               100 * (qr.cnt_redundant_literals / ((float) qr.total_univ_lits)) : 0);

      
      fprintf (stderr, "  run time: %f\n", time_stamp () - qr.start_time);
    }

  /* Clean up, free memory and exit. */
  cleanup (&qr);
  mm_delete (qr.mm);

  return result;
}
