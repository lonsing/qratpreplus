/*
 This file is part of QRATPre+.

 Copyright 2019
 Florian Lonsing, Stanford University, USA.

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
#include <ctype.h>
#include "qratpreplus_internals.h"
#include "util.h"
#include "parse.h"

/* Comparison function used to sort literals of clauses. */
static int
compare_lits_by_nesting (QRATPrePlus * qr, LitID lit1, LitID lit2)
{
  Var *var1 = LIT2VARPTR (qr->pcnf.vars, lit1);
  Var *var2 = LIT2VARPTR (qr->pcnf.vars, lit2);

  Nesting nesting1 = var1->qblock->nesting;
  Nesting nesting2 = var2->qblock->nesting;

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

/* Discard complementary literals or multiple literals of the same
   variable. Returns nonzero iff clause is tautological and hence should be
   discarded. */
static int
check_and_add_clause (QRATPrePlus * qr, Clause * clause)
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
      ABORT_APP (!var->qblock,
                       "variable has not been declared in a qblock!");

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
      if (v->qblock->type == QTYPE_FORALL)
        clause->num_lits--;
      else
        break;
    }

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

  qr->actual_num_clauses++;
  
  return 0;
}

static void
init_watched_literals (QRATPrePlus * qr, Clause *c)
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
  assert (var->qblock->type == QTYPE_EXISTS);
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
import_parsed_clause (QRATPrePlus * qr)
{
  assert (qr->parsing_prefix_completed);
  assert (!qr->opened_qblock);
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

/* Add parsed qblock to data structures. */
static void
import_parsed_qblock_variables (QRATPrePlus * qr)
{
  assert (!qr->parsing_prefix_completed);
  assert (qr->opened_qblock);
  assert (EMPTY_STACK (qr->opened_qblock->vars));
  ABORT_APP (EMPTY_STACK (qr->parsed_literals), "attempted to add empty qblock!\n");
  LitID *p, *e;
  for (p = qr->parsed_literals.start, e = qr->parsed_literals.top; p < e; p++)
    {
      LitID varid = *p;
      ABORT_APP (varid <= 0,
                       "variable ID in qblock must be positive!\n");
      ABORT_APP ((VarID) varid >= qr->pcnf.size_vars,
                       "variable ID in qblock exceeds specified max. ID (given in preamble or via API)!");

      /* Add variable ID to list of IDs in the qblock. */
      PUSH_STACK (qr->mm, qr->opened_qblock->vars, varid);
      Var *var = VARID2VARPTR (qr->pcnf.vars, varid);
      /* Set variable ID and pointer to qblock of variable. */
      ABORT_APP (var->id, "variable already quantified!\n");
      var->id = varid;
      assert (!var->qblock);
      var->qblock = qr->opened_qblock;
      qr->actual_num_vars++;
    }
  /* The current qblock has been added to the qblock list already. */
  assert (qr->opened_qblock == qr->pcnf.qblocks.first ||
          (qr->opened_qblock->link.prev && !qr->opened_qblock->link.next));
  assert (qr->opened_qblock != qr->pcnf.qblocks.first ||
          (!qr->opened_qblock->link.prev && !qr->opened_qblock->link.next));
}

static void
update_qblock_nestings (QRATPrePlus * qr)
{
  /* Update the nesting levels of the qblocks. QBlock numbering starts
     at nesting level 0. */
  Nesting nesting = 0;
  QBlock *s;
  for (s = qr->pcnf.qblocks.first; s; s = s->link.next)
    s->nesting = nesting++;
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


/* -------------------- START: PUBLIC FUNCTIONS -------------------- */

/* Merge and remove adjacent qblocks of the same quantifier type. */
void
merge_adjacent_same_type_qblocks (QRATPrePlus * qr, int update_nestings)
{
  MemMan *mem = qr->mm;
  unsigned int modified = 0;
  QBlock *s, *n;
  for (s = qr->pcnf.qblocks.first; s; s = n)
    {
      n = s->link.next;
      if (n && s->type == n->type)
        {                       
          /* Adjacent qblocks have same type -> merge 'n' into 's'. */
          VarIDStack *qblock_vars = &s->vars;
          VarID *p, *e, v;
          for (p = n->vars.start, e = n->vars.top; p < e; p++)
            {
              v = *p;
              PUSH_STACK (mem, *qblock_vars, v);
              assert (qr->pcnf.vars[v].qblock == n);
              qr->pcnf.vars[v].qblock = s;
            }

          UNLINK (qr->pcnf.qblocks, n, link);
          DELETE_STACK (qr->mm, n->vars);
          mm_free (qr->mm, n, sizeof (QBlock));
          n = s;
          modified = 1;
        }
    }

  if (modified || update_nestings)
    update_qblock_nestings (qr);
}

/* Collect parsed literals of a qblock or a clause on auxiliary stack to be
   imported and added to data structures later. */
void
parse_literal (QRATPrePlus * qr, int num)
{
  if (num == 0)
    {
      if (qr->opened_qblock)
        {
          assert (!qr->parsing_prefix_completed);
          import_parsed_qblock_variables (qr);
          qr->opened_qblock = 0;
        }
      else
        {
          if (!qr->parsing_prefix_completed)
            {
              qr->parsing_prefix_completed = 1;
              merge_adjacent_same_type_qblocks (qr, 0);
            }
          import_parsed_clause (qr);
        }
      RESET_STACK (qr->parsed_literals);
    }
  else
    PUSH_STACK (qr->mm, qr->parsed_literals, num);
}

void
parse_formula (QRATPrePlus * qr, FILE * in)
{
  int neg = 0, preamble_found = 0;
  LitID num = 0;
  QuantifierType qblock_type = QTYPE_UNDEF;

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
          goto PARSE_QBLOCK_OR_CLAUSE;

        MALFORMED_PREAMBLE:
          ABORT_APP (1, "malformed preamble!\n");
          return;
        }
      else
        {
          ABORT_APP (1, "expecting preamble!\n");
          return;
        }

    PARSE_QBLOCK_OR_CLAUSE:

      PARSER_SKIP_SPACE_WHILE (c);

      PARSER_SKIP_COMMENTS_WHILE (c);

      PARSER_SKIP_SPACE_WHILE (c);

      if (c == 'a' || c == 'e')
        {
          ABORT_APP (qr->parsing_prefix_completed,
                     "must not interleave addition of clauses and qblocks!\n");

          /* Open a new qblock */
          if (c == 'a')
            qblock_type = QTYPE_FORALL;
          else
            qblock_type = QTYPE_EXISTS;

          ABORT_APP (qr->opened_qblock,
                           "must close qblock by '0' before opening a new qblock!\n");

          open_new_qblock (qr, qblock_type);

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

          parse_literal (qr, num);

          neg = 0;

          goto PARSE_QBLOCK_OR_CLAUSE;
        }
    }

  if (!preamble_found)
    ABORT_APP (1, "preamble missing!\n");
}

/* Allocate a new qblock object and append it to the list of
   qblocks. Value '-1' indicates EXISTS, '1' FORALL, everything else
   undefined. */
void
open_new_qblock (QRATPrePlus * qr, QuantifierType qblock_type)
{
  assert (qblock_type != QTYPE_UNDEF);
  assert (!qr->opened_qblock);
  assert (!qr->parsing_prefix_completed);
  QBlock *qblock = mm_malloc (qr->mm, sizeof (QBlock));
  qblock->type = qblock_type;
  qblock->nesting = qr->pcnf.qblocks.last ?
    qr->pcnf.qblocks.last->nesting + 1 : 0;
  /* Keep pointer to opened qblock to add parsed variable IDs afterwards. */
  qr->opened_qblock = qblock;
  /* Append qblock to list of qblocks. */
  LINK_LAST (qr->pcnf.qblocks, qblock, link);
}

/* Allocate table of variable IDs having fixed size. If the preamble of the
   QDIMACS file specifies a maximum variable ID which is smaller than the ID
   of a variable encountered in the formula, then the program aborts. */
void
set_up_var_table (QRATPrePlus * qr, int num)
{
  assert (num >= 0);
  assert (!qr->pcnf.size_vars);
  assert (!qr->pcnf.vars);
  qr->pcnf.size_vars = num + 1;
  qr->pcnf.vars =
    (Var *) mm_malloc (qr->mm, qr->pcnf.size_vars * sizeof (Var));
}

/* -------------------- END: PUBLIC FUNCTIONS -------------------- */
