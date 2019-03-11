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

#include <assert.h>
#include <stdlib.h>
#include "stack.h"
#include "qbcp.h"
#include "util.h"
#include "qbce_qrat_plus.h"
#include "qratpreplus_internals.h"

enum QRATPlusCheckMode
{
  QRATPLUS_CHECK_MODE_UNDEF = 0,
  QRATPLUS_CHECK_MODE_QBCE = 1,
  QRATPLUS_CHECK_MODE_AT = 2,
  QRATPLUS_CHECK_MODE_QRAT = 3
};

typedef enum QRATPlusCheckMode QRATPlusCheckMode;

/* Check if soft time limit is exceeded every
   '2^QRATPLUS_SOFT_TIME_LIMIT_CHECK_PERIOD' clause checks. With small
   values the accuracy of the time limit will be higher but checking
   the limit may be costly. With high values checks are infrequent and
   hence cheap but program may run longer if clause checks are
   expensive. */
#define QRATPLUS_SOFT_TIME_LIMIT_CHECK_PERIOD 10

/* Returns true if and only if 'lit' appears in the literal array
   bounded by 'start' and 'end' (position 'end' is not part of the
   array) AND 'lit' is from a qblock of nesting level equal to
   'nesting' or smaller. Assumes that literal array is sorted by qblock
   ordering. */
static int
find_literal_outer_tautology (QRATPrePlus * qr, LitID taut_lit, Nesting nesting,
                              LitID * start, LitID * end)
{
  LitID *p;
  for (p = start; p < end; p++)
    {
      LitID lit = *p;
      Var *var = LIT2VARPTR (qr->pcnf.vars, lit);
      if (var->qblock->nesting > nesting)
        break;
      if (lit == taut_lit)
        return 1;
    }
  return 0;
}

/* Return nonzero iff resolvent of 'c' and 'occ' on literal 'lit' is
   tautologous with respect to a variable that is smaller than or
   equal to 'lit' in the prefix ordering. */
static int
check_outer_tautology (QRATPrePlus * qr, Clause *c, LitID lit, Clause *occ)
{
  assert (!c->redundant);
  assert (!occ->redundant);
  assert (c->num_lits > 0);
  assert (occ->num_lits > 0);

  qr->clause_redundancy_or_checks++;
  
  Var *var = LIT2VARPTR (qr->pcnf.vars, lit);
  QBlock *qblock = var->qblock;
  Nesting nesting = qblock->nesting;
  /* Literal 'lit' must appear in complementary phases in clauses 'c'
     and 'occ'. */
  assert (find_literal (lit, c->lits, c->lits + c->num_lits));
  assert (find_literal (-lit, occ->lits, occ->lits + occ->num_lits));

  const unsigned int qbce_check_taut_by_nesting =
    qr->options.qbce_check_taut_by_nesting;
  
  LitID *cp, *ce;
  for (cp = c->lits, ce = cp + c->num_lits; cp < ce; cp++)
    {
      qr->clause_redundancy_or_checks_lits_seen++;
      LitID cl = *cp;
      Var *cv = LIT2VARPTR (qr->pcnf.vars, cl);
      /* Can ignore variables from qblocks larger than 'lit'. */
      if (qbce_check_taut_by_nesting && cv->qblock->nesting > nesting)
        break;
      /* Must ignore potential blocking literal 'lit'. */
      if (cl != lit)
        {
          /* Must consider only tautologies due to literals with
             nesting level smaller than or equal to nesting of
             'lit'. Check whether other clause 'occ' contains
             complementary literal '-cl'. */

          if ((!qbce_check_taut_by_nesting && (cv->qblock->nesting <= nesting)
               && find_literal (-cl, occ->lits, occ->lits + occ->num_lits)) ||
              (qbce_check_taut_by_nesting && find_literal_outer_tautology
               (qr, -cl, nesting, occ->lits, occ->lits + occ->num_lits)))
            return 1;
        }
    }
  return 0;
}

/* Return nonzero iff clause 'c' has qrat on literal 'lit'. */
static int
has_qrat_on_literal (QRATPrePlus * qr, Clause *c, LitID lit)
{
  assert (!c->redundant);
  assert (c->num_lits > 0);
  Var *var = LIT2VARPTR (qr->pcnf.vars, lit);
  assert (LIT_NEG (lit) || LIT_POS (lit));
  /* Set pointer to stack of clauses containing literals complementary to 'lit'. */
  ClausePtrStack *comp_occs = LIT_NEG (lit) ? 
    &(var->pos_occ_clauses) : &(var->neg_occ_clauses);

  /* Check all possible resolution candidates on literal 'lit' and
     clauses on 'comp_occs'. Must ignore already redundant
     occurrences. */
  Clause **occ_p, **occ_e;
  for (occ_p = comp_occs->start, occ_e = comp_occs->top; occ_p < occ_e; occ_p++)
    {
      /* Do QRAT test either with or without EABS (controlled by option '--eabs'). */
      Clause *occ = *occ_p;
      
      if (occ->redundant)
        continue;

      qr->clause_redundancy_or_checks++;
      qr->clause_redundancy_or_checks_lits_seen += occ->num_lits;
      
      if (!qrat_qbcp_check (qr, c, lit, occ))
        {
          if (var->qblock->type == QTYPE_EXISTS)
            {
              /* Collect 'occ' as a witness for non-redundancy of 'c' (on
                 'lit'). */
              if (!occ->witness)
                {
                  if (qr->options.verbosity >= 2)
                    {
                      fprintf (stderr, "  clause ");
                      print_lits (qr, stderr, occ->lits, occ->num_lits, 1);
                      fprintf (stderr, "    is witness of: ");
                      print_lits (qr, stderr, c->lits, c->num_lits, 1);
                    }
                  occ->witness = 1;
                  PUSH_STACK (qr->mm, qr->witness_clauses, occ);
                }
            }
          return 0;
        }
    }
  /* All candidates fulfill tautology property of QBCE, hence 'lit' 
     is blocking literal in clause 'c'. */
  return 1;
}

/* Return nonzero iff 'lit' is a blocking literal in clause 'c'. */
static int
is_literal_blocking (QRATPrePlus * qr, Clause *c, LitID lit)
{
  assert (!c->redundant);
  assert (c->num_lits > 0);
  Var *var = LIT2VARPTR (qr->pcnf.vars, lit);
  assert(var->qblock->type == QTYPE_EXISTS);
  assert (LIT_NEG (lit) || LIT_POS (lit));
  /* Set pointer to stack of clauses containing literals complementary to 'lit'. */
  ClausePtrStack *comp_occs = LIT_NEG (lit) ? 
    &(var->pos_occ_clauses) : &(var->neg_occ_clauses);

  /* Check all possible resolution candidates on literal 'lit' and
     clauses on 'comp_occs'. Must ignore already redundant
     occurrences. */
  Clause **occ_p, **occ_e;
  for (occ_p = comp_occs->start, occ_e = comp_occs->top; occ_p < occ_e; occ_p++)
    {
      Clause *occ = *occ_p; 
      if (!occ->redundant &&
          /* Syntactic check for tautology, i.e., QBCE check. */
          !check_outer_tautology (qr, c, lit, occ))
        {
          /* Collect 'occ' as a witness for non-redundancy of 'c' (on
             'lit'). */
          if (!occ->witness)
            {
              if (qr->options.verbosity >= 2)
                {
                  fprintf (stderr, "  clause ");
                  print_lits (qr, stderr, occ->lits, occ->num_lits, 1);
                  fprintf (stderr, "    is witness of: ");
                  print_lits (qr, stderr, c->lits, c->num_lits, 1);
                }
              occ->witness = 1;
              PUSH_STACK (qr->mm, qr->witness_clauses, occ);
            }
          return 0;
        }
    }
  /* All candidates fulfill tautology property of QBCE, hence 'lit' 
     is blocking literal in clause 'c'. */
  return 1;
}

/* Return nonzero iff clause 'c' has QRAT. */
static int
has_clause_qrat (QRATPrePlus * qr, Clause *c)
{
  assert (!c->redundant);
  LitID *p, *e;
  for (p = c->lits, e = p + c->num_lits; p < e; p++)
    {
      qr->clause_redundancy_or_checks_lits_seen++;
      LitID lit = *p;
      Var *var = LIT2VARPTR (qr->pcnf.vars, lit);
      /* Check if existential literal 'lit' is indeed a blocking literal. */
      if (var->qblock->type == QTYPE_EXISTS)
        {
          if (has_qrat_on_literal (qr, c, lit))
            return 1;
        }
    }
  return 0;
}

/* Return nonzero iff 'lit' is blocked in clause 'c'. */
static int
is_literal_blocked (QRATPrePlus * qr, Clause *c, LitID lit)
{
  assert (!c->redundant);
  assert (c->num_lits > 0);
  Var *var = LIT2VARPTR (qr->pcnf.vars, lit);
  assert(var->qblock->type == QTYPE_FORALL);
  assert (LIT_NEG (lit) || LIT_POS (lit));
  /* Set pointer to stack of clauses containing literals complementary to 'lit'. */
  ClausePtrStack *comp_occs = LIT_NEG (lit) ? 
    &(var->pos_occ_clauses) : &(var->neg_occ_clauses);

  /* Check all possible resolution candidates on literal 'lit' and
     clauses on 'comp_occs'. Must ignore already redundant
     occurrences. */
  Clause **occ_p, **occ_e;
  for (occ_p = comp_occs->start, occ_e = comp_occs->top; occ_p < occ_e; occ_p++)
    {
      Clause *occ = *occ_p; 
      if (!occ->redundant &&
          /* Syntactic check for tautology, i.e., QBCE check. */
          !check_outer_tautology (qr, c, lit, occ))
        {
          if (qr->options.verbosity >= 2)
            {
              fprintf (stderr, "  clause ");
              print_lits (qr, stderr, occ->lits, occ->num_lits, 1);
              fprintf (stderr, "    is witness of: ");
              print_lits (qr, stderr, c->lits, c->num_lits, 1);
            }
          return 0;
        }
    }
  /* All candidates fulfill tautology property of QBCE, hence 'lit' 
     is blocked in clause 'c'. */
  return 1;
}

/* Return nonzero iff clause 'c' is blocked. */
static int
is_clause_blocked (QRATPrePlus * qr, Clause *c)
{
  assert (!c->redundant);
  LitID *p, *e;
  for (p = c->lits, e = p + c->num_lits; p < e; p++)
    {
      qr->clause_redundancy_or_checks_lits_seen++;
      LitID lit = *p;
      Var *var = LIT2VARPTR (qr->pcnf.vars, lit);
      /* Check if existential literal 'lit' is indeed a blocking literal. */
      if (var->qblock->type == QTYPE_EXISTS)
        {
          if (is_literal_blocking (qr, c, lit))
            return 1;
        }
    }
  return 0;
}

/* Returns nonzero iff clause 'c' meets the current limits (if not, then 'c'
   is not checked for redundancy). */
static int
reschedule_is_clause_within_limits (QRATPrePlus * qr, Clause *c)
{
  if (c->num_lits < qr->limit_min_clause_len)
    {
      if (qr->options.verbosity >= 2)
        {
          fprintf (stderr, "Clause ID %u not rescheduled, length %u less than min-length %u: ", 
                   c->id, c->num_lits, qr->limit_min_clause_len);
          print_lits (qr, stderr, c->lits, c->num_lits, 1);
        }
      return 0;
    }
  if (qr->limit_max_clause_len < c->num_lits)
    {
      if (qr->options.verbosity >= 2)
        {
          fprintf (stderr, "Clause ID %u not rescheduled, length %u greater than max-length %u: ", 
                   c->id, c->num_lits, qr->limit_max_clause_len);
          print_lits (qr, stderr, c->lits, c->num_lits, 1);
        }
      return 0;
    }

  LitID *p, *e;
  for (p = c->lits, e = p + c->num_lits; p < e; p++)
    {
      LitID lit =  *p;
      Var *var = LIT2VARPTR (qr->pcnf.vars, lit);
      ClausePtrStack *compl_occs = LIT_NEG (lit) ? 
        &var->pos_occ_clauses : &var->neg_occ_clauses;
      if (qr->limit_max_occ_cnt < (unsigned int) COUNT_STACK (*compl_occs))
        {
          if (qr->options.verbosity >= 2)
            {
              fprintf (stderr, "Clause ID %u not rescheduled, compl-occs count %u greater than max occ count %u: ", 
                       c->id, (unsigned int) COUNT_STACK (*compl_occs), qr->limit_max_occ_cnt);
              print_lits (qr, stderr, c->lits, c->num_lits, 1);
            }
          return 0;
        }
    }

  return 1;
}

/* Collect all non-redundant and not already collected clauses 'd' on stack
   'rescheduled' such that 'd' potentially is now redundant due to having
   identified 'c' as redundant before. Clauses 'd' are resolution partners of
   'c'. That is, the now redundant clause 'c' may have prevented 'd' from
   being redundant if the check of the outer resolvent of 'c' and 'd'
   failed. That check may now succeed as 'c' was found redundant. */
static void
reschedule_from_redundant_clause (QRATPrePlus * qr, Clause *c, 
                                  ClausePtrStack *rescheduled)
{
  if (qr->options.verbosity >= 2)
    {
      fprintf (stderr, "    Rescheduling from redundant clause: ");
      print_lits (qr, stderr, c->lits, c->num_lits, 1);
    }
  assert (c->redundant);
  LitID *p, *e;
  for (p = c->lits, e = p + c->num_lits; p < e; p++)
    {
      LitID lit = *p;
      Var *var = LIT2VARPTR (qr->pcnf.vars, lit);
      ClausePtrStack *compl_occs = LIT_NEG (lit) ? 
        &var->pos_occ_clauses : &var->neg_occ_clauses; 
      Clause *oc, **cp, **ce;
      for (cp = compl_occs->start, ce = compl_occs->top; cp < ce; cp++)
        {
          oc = *cp;
          if (!oc->redundant)
            if (!oc->rescheduled && reschedule_is_clause_within_limits (qr, oc))
              {
                oc->rescheduled = 1;
                PUSH_STACK (qr->mm, *rescheduled, oc);
                if (qr->options.verbosity >= 2)
                  {
                    fprintf (stderr, "    rescheduled clause: ");
                    print_lits (qr, stderr, oc->lits, oc->num_lits, 1);
                  }
              }
        }
    }
}

static void
reset_witness_clauses (QRATPrePlus *qr)
{
  Clause **cp, **ce;
  for (cp = qr->witness_clauses.start, ce = qr->witness_clauses.top; 
       cp < ce; cp++)
    {
      Clause *c = *cp;
      assert (c->witness);
      c->witness = 0;
    }
  RESET_STACK (qr->witness_clauses);  
}

static void
reschedule_from_redundant_witness_clauses (QRATPrePlus *qr, 
                                           ClausePtrStack *rescheduled)
{
  if (qr->options.verbosity >= 2)
    fprintf (stderr, "\nRescheduling from %u witness clauses\n", 
             (unsigned int) COUNT_STACK (qr->witness_clauses));

  assert (EMPTY_STACK (*rescheduled));
  Clause **cp, **ce;
  for (cp = qr->witness_clauses.start, ce = qr->witness_clauses.top; 
       cp < ce; cp++)
    {
      Clause *c = *cp;
      assert (c->witness);
      if (c->redundant)
        {
          if (qr->options.verbosity >= 2)
            {
              fprintf (stderr, "  Redundant witness clause: ");
              print_lits (qr, stderr, c->lits, c->num_lits, 1);
            }
          reschedule_from_redundant_clause (qr, c, rescheduled);
          c->witness = 0;
          Clause *last = POP_STACK (qr->witness_clauses);
          *cp = last;
          cp--;
          ce--;
        }
      else
        {
          if (qr->options.verbosity >= 2)
            {
              fprintf (stderr, "  Non-redundant witness clause: ");
              print_lits (qr, stderr, c->lits, c->num_lits, 1);
            }
        }
    }
}

static int
compare_clauses_by_id (const void * cp1, const void * cp2)
{
  Clause *c1 = (Clause *) cp1;
  Clause *c2 = (Clause *) cp2;
  if (c1->id < c2->id)
    return -1;
  else if (c1->id > c2->id)
    return 1;
  else return 0;
}

static void
permute_clauses_to_be_checked (QRATPrePlus * qr, ClausePtrStack *to_be_checked)
{
  if (!EMPTY_STACK (*to_be_checked))
    {
      if (qr->options.verbosity >= 2)
        {
          fprintf (stderr, "Sequence before permuting: ");
          Clause **cp, **ce;
          for (cp = to_be_checked->start, ce = to_be_checked->top; cp < ce; cp++)
            {
              Clause *c = *cp;
              fprintf (stderr, "%u ", c->id);
            }
          fprintf (stderr, "\n");
        }

    /* Permute set of clauses to be checked randomly according to the
       following algorithm:
       https://en.wikipedia.org/wiki/Fisher%E2%80%93Yates_shuffle */
      unsigned int i;
      for (i = ((unsigned int)COUNT_STACK (*to_be_checked)) - 1; i >= 1; i--)
        {
          unsigned int j = rand_r (&qr->options.seed) % (i+1);
          assert (i < COUNT_STACK (*to_be_checked));
          assert (j < COUNT_STACK (*to_be_checked));
          Clause *tmp = to_be_checked->start[i];
          to_be_checked->start[i] = to_be_checked->start[j];
          to_be_checked->start[j] = tmp;
        }

      if (qr->options.verbosity >= 2)
        {
          fprintf (stderr, "Sequence after permuting: ");
          Clause **cp, **ce;
          for (cp = to_be_checked->start, ce = to_be_checked->top; cp < ce; cp++)
            {
              Clause *c = *cp;
              fprintf (stderr, "%u ", c->id);
            }
          fprintf (stderr, "\n");
        }
    }
}

static Clause *
find_non_redundant_occ (QRATPrePlus * qr, ClausePtrStack *occs)
{
  Clause **occ_p, **occ_e;
  for (occ_p = occs->start, occ_e = occs->top; occ_p < occ_e; occ_p++)
    {
      Clause *c = *occ_p;
      if (!c->redundant)
        return c;
    }
  return 0;
}

static void 
reschedule_from_input_clauses (QRATPrePlus * qr, ClausePtrStack *rescheduled)
{
  Clause *c;
  for (c = qr->pcnf.clauses.first; c; c = c->link.next)
    {
      /* Mark 'c->rescheduled' set iff 'c' appears in set of rescheduled
         clauses. */
      if (!c->redundant && !c->rescheduled && 
          reschedule_is_clause_within_limits (qr, c))
        {
          c->rescheduled = 1;
          PUSH_STACK (qr->mm, *rescheduled, c);
        }
    }
}

/* Returns nonzero iff redundant clauses were found. */
static int
find_and_mark_redundant_clauses_aux (QRATPrePlus * qr, 
                                     ClausePtrStack *to_be_checked, 
                                     ClausePtrStack *rescheduled, 
                                     const QRATPlusCheckMode mode)
{
  int result = 0;
  assert (mode == QRATPLUS_CHECK_MODE_QBCE || mode == QRATPLUS_CHECK_MODE_AT || 
          mode == QRATPLUS_CHECK_MODE_QRAT);
  assert (!qr->options.no_qbce || !qr->options.no_qat || 
	  !qr->options.no_qrate);
  assert (mode != QRATPLUS_CHECK_MODE_QRAT || !qr->options.no_qrate);
  assert (mode != QRATPLUS_CHECK_MODE_AT || !qr->options.no_qat);

  assert (EMPTY_STACK (qr->witness_clauses));

  int exceeded = 0;

  if ((exceeded = exceeded_soft_time_limit (qr)))
    fprintf (stderr, "Exceeded soft time limit of %u sec\n", qr->soft_time_limit);
  
#ifndef NDEBUG
  {
    /* Clauses to be tested are expected to be sorted by ID. */
    Clause **cp, **ce, **cpprev;
    for (cp = cpprev = rescheduled->start, ce = rescheduled->top; cp < ce; cp++)
      {
        Clause *c = *cp;
        Clause *cprev = *cpprev;
        assert (cprev->id <= c->id);
        cpprev = cp;     
      }
  }
#endif

  unsigned int cur_redundant_clauses = 0;
  int changed = 1;
  while (!exceeded && changed)
    {
      /* Statistics. */
      qr->cnt_redundant_clauses += cur_redundant_clauses;
      qr->cnt_qbce_iterations++;

      /* Set up new iteration: swap 'rescheduled' and 'to_be_checked', reset. */
      changed = 0;
      Clause **cp, **ce;
      for (cp = rescheduled->start, ce = rescheduled->top; cp < ce; cp++)
        {
          Clause *c = *cp;
          /* NOTE: we may encounter clauses 'c' with 'c->redundant' true. This
             may happen if we first reschedule a non-redundant clause 'c' which
             in the same iteration is found redundant later. */
          assert (c->rescheduled);
          c->rescheduled = 0;
        }
      ClausePtrStack *stack_tmp = to_be_checked;
      to_be_checked = rescheduled;
      rescheduled = stack_tmp;
      RESET_STACK (*rescheduled);

      if (qr->options.verbosity >= 1)
        {
          fprintf (stderr, "\n======\n%s iteration %d: %d new redundant clauses in previous iteration %d\n", 
                   mode == QRATPLUS_CHECK_MODE_QBCE ? "QBCE" : (mode == QRATPLUS_CHECK_MODE_AT ? "AT" : "QRATE"),
                   qr->cnt_qbce_iterations, cur_redundant_clauses, qr->cnt_qbce_iterations - 1);
          fprintf (stderr, "Clauses to be checked (worst case): %u ( %f %% of original CNF)\n======\n", 
                   (unsigned int) COUNT_STACK (*to_be_checked), 100 * (COUNT_STACK (*to_be_checked) / (float) qr->actual_num_clauses));
        }
      cur_redundant_clauses = 0;

      /* Either randomly permute or sort clauses to be tested by ID. Note that
         without sorting we may get different orderings due to the way we
         reschedule clauses. */
      if (mode != QRATPLUS_CHECK_MODE_QBCE && qr->options.permute)
        permute_clauses_to_be_checked (qr, to_be_checked);
      else
        qsort (to_be_checked->start, COUNT_STACK (*to_be_checked), 
               sizeof (Clause *), compare_clauses_by_id);

      for (cp = to_be_checked->start, ce = to_be_checked->top;
           !exceeded && cp < ce; cp++)
        {
          Clause *c = *cp;
          /* NOTE: we may encounter clauses 'c' with 'c->redundant' true
             because such clauses may appear on 'rescheduled' (see comment above)
             and we just swap the sets at the beginning of each iteration. */
          if (!c->redundant)
            {
              if (qr->options.verbosity >= 2)
                {
                  fprintf (stderr, "\nRedundancy check on clause ");
                  print_lits (qr, stderr, c->lits, c->num_lits, 1);
                }

              qr->cnt_qbce_checks++;
              /* Print progress information. */
              if (qr->options.verbosity >= 1 && 
                  (qr->cnt_qbce_checks & ((1 << 15) - 1)) == 0)
                fprintf (stderr, "progress -- clause checks: %llu\n", 
                         qr->cnt_qbce_checks);
              /* Periodically check if soft time limit reached, exit for-loop. */
              if ((qr->cnt_qbce_checks &
                   ((1 << QRATPLUS_SOFT_TIME_LIMIT_CHECK_PERIOD) - 1)) == 0 &&
                  (exceeded = exceeded_soft_time_limit (qr)))
                {
                  fprintf (stderr, "Exceeded soft time limit of %u sec after %llu clause checks\n",
                           qr->soft_time_limit, qr->cnt_qbce_checks);
                  continue;
                }
              if ( (mode == QRATPLUS_CHECK_MODE_QBCE && is_clause_blocked (qr, c)) ||
                   (mode == QRATPLUS_CHECK_MODE_AT && qrat_qat_check (qr, c)) ||
                   (mode == QRATPLUS_CHECK_MODE_QRAT && has_clause_qrat (qr, c)) )
                {
                  if (qr->options.verbosity >= 2)
                    {
                      fprintf (stderr, "  ==> Clause ");
                      print_lits (qr, stderr, c->lits, c->num_lits, 1);
                      fprintf (stderr, " is redundant.\n");
                    }
                  c->redundant = 1;
                  PUSH_STACK (qr->mm, qr->redundant_clauses, c);
                  cur_redundant_clauses++;
                  changed = 1;
                  result = 1;
                }
            }
        }

      /* Do not reschedule from incomplete iterations of above for-loop. */
      if (exceeded)
        continue;
      
      /* Reschedule from redundant witness clauses in QBCE/QRAT mode. */
      if (mode != QRATPLUS_CHECK_MODE_AT)
        reschedule_from_redundant_witness_clauses (qr, rescheduled);
    }

  /* Must update statistics after exiting loop due to exceeding time limit. */
  assert (exceeded || cur_redundant_clauses == 0);
  qr->cnt_redundant_clauses += cur_redundant_clauses;

#ifndef NDEBUG
  Clause *c;
  for (c = qr->pcnf.clauses.first; c; c = c->link.next)
    assert (!c->rescheduled);
#endif

  return result;
}

static void
unlink_redundant_clauses_occs (QRATPrePlus * qr, ClausePtrStack *occs)
{
  Clause **cp, **ce;
  for (cp = occs->start, ce = occs->top; cp < ce; cp++)
    {
      Clause *c = *cp;
      if (c->redundant)
        {
          Clause *last = POP_STACK (*occs);
          *cp = last;
          cp--;
          ce--;
        }
    }
}

static void
remove_clause_from_occs (ClausePtrStack *occs, Clause *c)
{
  Clause **p, **e;
  for (p = occs->start, e = occs->top; p < e; p++)
    {
      if (*p == c)
	{
	  *p = POP_STACK (*occs);
	  break;
	}
    }
  /* Assuming that 'occs' contains 'c'. */
  assert (p < e);
}

/* Clean up redundant universal literal 'red_lit' from clause 'c', update data
   structures and watchers. */
static void
cleanup_redundant_universal_literal (QRATPrePlus * qr, Clause * c, LitID red_lit)
{
  assert (c->num_lits >= 2);
  assert (find_literal (red_lit, c->lits, c->lits + c->num_lits));
  assert (LIT2VARPTR (qr->pcnf.vars, red_lit)->qblock->type == QTYPE_FORALL);
  assert (c->rw_index != WATCHED_LIT_INVALID_INDEX);
  assert (c->lw_index != WATCHED_LIT_INVALID_INDEX);
  assert (c->lw_index != c->rw_index);
  unsigned int update_watcher = 0;
  Var *red_var = LIT2VARPTR (qr->pcnf.vars, red_lit);

  /* Check for update of watched literals. Note: when not using EABS, then
     right watcher may be set to a universal literal and hence we must handle
     this case below. */
  if (c->lits[c->lw_index] == red_lit || c->lits[c->rw_index] == red_lit)
    {
      /* Reset left and right watched literal, remove 'c' from watched occs. */
      update_watcher = 1;
      LitID lw_lit = c->lits[c->lw_index];
      Var *lw_var = LIT2VARPTR (qr->pcnf.vars, lw_lit);
      ClausePtrStack *occs = LIT_NEG (lw_lit) ? 
	&lw_var->watched_neg_occ_clauses : &lw_var->watched_pos_occ_clauses;
      remove_clause_from_occs (occs, c);
      c->lw_index = WATCHED_LIT_INVALID_INDEX;
      LitID rw_lit = c->lits[c->rw_index];
      Var *rw_var = LIT2VARPTR (qr->pcnf.vars, rw_lit);
      occs = LIT_NEG (rw_lit) ? 
	&rw_var->watched_neg_occ_clauses : &rw_var->watched_pos_occ_clauses;
      remove_clause_from_occs (occs, c);
      c->rw_index = WATCHED_LIT_INVALID_INDEX;
    }

  /* Remove clause 'c' from occs of variable of 'red_lit'. */
  ClausePtrStack *occs = LIT_NEG (red_lit) ? 
    &red_var->neg_occ_clauses : &red_var->pos_occ_clauses;
  remove_clause_from_occs (occs, c);

  assert (count_qtype_literals (qr, c, QTYPE_FORALL) + 
          count_qtype_literals (qr, c, QTYPE_EXISTS) == c->num_lits);

  /* Remove 'red_lit' from 'c'  while keeping ordering of literals. */ 
  LitID *p, *e;
  for (p = c->lits, e = p + c->num_lits; p < e; p++)
    {
      LitID lit = *p;
      if (lit == red_lit)
        {
	  /* Must update index of watched literals. */
	  if (!update_watcher)
	    {
	      unsigned int red_lit_index = p - c->lits;
	      assert (c->rw_index != red_lit_index);
	      assert (c->lw_index != red_lit_index);
	      if (c->lw_index > red_lit_index)
		c->lw_index--;
	      if (c->rw_index > red_lit_index)
		c->rw_index--;
	    }
          LitID *to, *from;
          for (to = p, from = p + 1; from < e; to++, from++)
            *to = *from;
	  break;
        }
    }

  c->num_lits--;

  if (c->num_lits == 1)
    PUSH_STACK (qr->mm, qr->unit_input_clauses, c);
  else if (update_watcher)
    {
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
}

/* Return nonzero iff clause 'c' contains universal literals which have QRAT. */
static int
has_clause_qrat_literals (QRATPrePlus * qr, Clause * c)
{
  assert (!c->redundant);
  int result = 0;
  LitID *p, *e;
  for (p = c->lits, e = p + c->num_lits; p < e; p++)
    {
      LitID lit = *p;
      Var *var = LIT2VARPTR (qr->pcnf.vars, lit);
      /* Check if universal literal 'lit' has QRAT. */
      if (var->qblock->type == QTYPE_FORALL)
        {
          if (has_qrat_on_literal (qr, c, lit))
            {
              if (qr->options.verbosity >= 2)
                {
                  fprintf (stderr, "  ==> universal literal %d has QRAT in clause ", lit);
                  print_lits (qr, stderr, c->lits, c->num_lits, 1);
                }
              cleanup_redundant_universal_literal (qr, c, lit);
              result = 1;
              /* Must update pointers since removed redundant 'lit' from 'c'. */
              p--;
              e--;
            }
        }
    }
  return result;
}

/* Return nonzero iff clause 'c' contains blocked universal literals. */
static int
has_clause_blocked_literals (QRATPrePlus * qr, Clause * c)
{
  int result = 0;
  assert (!c->redundant);
  LitID *p, *e;
  for (p = c->lits, e = p + c->num_lits; p < e; p++)
    {
      LitID lit = *p;
      Var *var = LIT2VARPTR (qr->pcnf.vars, lit);
      /* Check if universal literal 'lit' is blocked. */
      if (var->qblock->type == QTYPE_FORALL)
        {
          if (is_literal_blocked (qr, c, lit))
            {
              if (qr->options.verbosity >= 2)
                {
                  fprintf (stderr, "  ==> universal literal %d is blocked in clause ", lit);
                  print_lits (qr, stderr, c->lits, c->num_lits, 1);
                }
              cleanup_redundant_universal_literal (qr, c, lit);
              result = 1;
              /* Must update pointers since removed redundant 'lit' from 'c'. */
              p--;
              e--;
            }
        }
    }
  return result;
}

/* Returns nonzero iff redundant literals were found. */
static int
find_and_delete_redundant_literals_aux (QRATPrePlus * qr, 
                                     ClausePtrStack *to_be_checked, 
                                     ClausePtrStack *rescheduled, 
                                     const QRATPlusCheckMode mode)
{  
  int result = 0;
  assert (!qr->options.no_ble || !qr->options.no_qratu);
  assert (mode == QRATPLUS_CHECK_MODE_QBCE || mode == QRATPLUS_CHECK_MODE_QRAT);
  assert (mode != QRATPLUS_CHECK_MODE_QBCE || !qr->options.no_ble);
  assert (mode != QRATPLUS_CHECK_MODE_QRAT || !qr->options.no_qratu);
  assert (EMPTY_STACK (qr->witness_clauses));

  int exceeded = 0;

  if ((exceeded = exceeded_soft_time_limit (qr)))
    fprintf (stderr, "Exceeded soft time limit of %u sec\n", qr->soft_time_limit);

#ifndef NDEBUG
  {
    /* Clauses to be tested are expected to be sorted by ID. */
    Clause **cp, **ce, **cpprev;
    for (cp = cpprev = rescheduled->start, ce = rescheduled->top; cp < ce; cp++)
      {
        Clause *c = *cp;
        Clause *cprev = *cpprev;
        assert (cprev->id <= c->id);
        cpprev = cp;     
      }
  }
#endif

  unsigned int cur_redundant_literals = 0;
  int changed = 1;
  while (!exceeded && changed)
    {
      /* Statistics. */
      qr->cnt_redundant_literals += cur_redundant_literals;
      qr->cnt_qratu_iterations++;

      /* Set up new iteration: swap 'rescheduled' and 'to_be_checked', reset. */
      changed = 0;
      Clause **cp, **ce;
      for (cp = rescheduled->start, ce = rescheduled->top; cp < ce; cp++)
        {
          Clause *c = *cp;
          /* NOTE: we may encounter clauses 'c' with 'c->redundant' true. This
             may happen if we first reschedule a non-redundant clause 'c' which
             in the same iteration is found redundant later. */
          assert (c->rescheduled);
          c->rescheduled = 0;
        }
      ClausePtrStack *stack_tmp = to_be_checked;
      to_be_checked = rescheduled;
      rescheduled = stack_tmp;
      RESET_STACK (*rescheduled);

      if (qr->options.verbosity >= 1)
        {
          fprintf (stderr, "\n======\n%s iteration %d: %d new redundant literals in previous iteration %d\n", 
                   mode == QRATPLUS_CHECK_MODE_QBCE ? "BLE" : "QRATU",
                   qr->cnt_qratu_iterations, cur_redundant_literals, qr->cnt_qratu_iterations - 1);
          fprintf (stderr, "Clauses to be checked (worst case): %u ( %f %% of original CNF)\n======\n", 
                   (unsigned int) COUNT_STACK (*to_be_checked), 100 * (COUNT_STACK (*to_be_checked) / (float) qr->actual_num_clauses));
        }
      cur_redundant_literals = 0;

      /* Either randomly permute or sort clauses to be tested by ID. Sorting
         makes sure that clauses are always tested in the same ordering, while
         permuting allows to analyze impact of orderings and non-confluence QRAT. 
         Note that without sorting we may get different orderings due to
         the way we reschedule clauses. */
      if (mode != QRATPLUS_CHECK_MODE_QBCE && qr->options.permute)
        permute_clauses_to_be_checked (qr, to_be_checked);
      else
        qsort (to_be_checked->start, COUNT_STACK (*to_be_checked), 
               sizeof (Clause *), compare_clauses_by_id);

      for (cp = to_be_checked->start, ce = to_be_checked->top; 
           !exceeded && cp < ce; cp++)
        {
          Clause *c = *cp;
          /* NOTE: we may encounter clauses 'c' with 'c->redundant' true
             because such clauses may appear on 'rescheduled' (see comment above)
             and we just swap the sets at the beginning of each iteration. */
          if (!c->redundant)
            {
              if (qr->options.verbosity >= 2)
                {
                  fprintf (stderr, "\nLiteral redundancy check on clause ");
                  print_lits (qr, stderr, c->lits, c->num_lits, 1);
                }
              
              qr->cnt_qratu_checks++;
              /* Print progress information. */
              if (qr->options.verbosity >= 1 && 
                  (qr->cnt_qratu_checks & ((1 << 15) - 1)) == 0)
                fprintf (stderr, "progress -- literal redundancy clause checks: %llu\n", 
                         qr->cnt_qratu_checks);
              /* Periodically check if soft time limit reached, exit for-loop. */
              if ((qr->cnt_qratu_checks &
                   ((1 << QRATPLUS_SOFT_TIME_LIMIT_CHECK_PERIOD) - 1)) == 0 &&
                  (exceeded = exceeded_soft_time_limit (qr)))
                {
                  fprintf (stderr, "Exceeded soft time limit of %u sec after %llu literal redundancy clause checks\n",
                           qr->soft_time_limit, qr->cnt_qratu_checks);
                  continue;
                }
              unsigned int num_lits_before = c->num_lits;
              if ( (mode == QRATPLUS_CHECK_MODE_QBCE && has_clause_blocked_literals (qr, c)) ||
                   (mode == QRATPLUS_CHECK_MODE_QRAT && has_clause_qrat_literals (qr, c)) )
                {
                  assert (c->num_lits > 0);
                  assert (num_lits_before > c->num_lits);
                  if (qr->options.verbosity >= 2)
                    {
                      fprintf (stderr, "  ==> Redundant universal literals removed from clause ");
                      print_lits (qr, stderr, c->lits, c->num_lits, 1);
                      fprintf (stderr, "\n");
                    }
                  cur_redundant_literals += (num_lits_before - c->num_lits);
                  changed = 1;
                  result = 1;
                }
            }
        }

      /* Do not reschedule from incomplete iterations of above for-loop. */
      if (exceeded)
        continue;

      /* For simplicity: if redundant literals were found in previous
         iteration, then reschedule ALL non-redundant clauses. */
      if (changed)
        reschedule_from_input_clauses (qr, rescheduled);
    }

#ifndef NDEBUG
  Clause *c;
  for (c = qr->pcnf.clauses.first; c; c = c->link.next)
    assert (!c->rescheduled);
#endif

  return result;
}


/* -------------------- START: PUBLIC FUNCTIONS -------------------- */

void
unlink_redundant_clauses (QRATPrePlus * qr)
{
  qr->max_clause_length = 0;
  qr->total_clause_lengths = 0;

  Clause *c, *n;
  for (c = qr->pcnf.clauses.first; c; c = n)
    {
      n = c->link.next;
      if (c->redundant)
        UNLINK (qr->pcnf.clauses, c, link);
      else
        {
          qr->total_clause_lengths += c->num_lits;
          if (c->num_lits > qr->max_clause_length)
            qr->max_clause_length = c->num_lits;
        }
    }

  qr->max_occ_cnt = 0;
  qr->total_occ_cnts = 0;

  Var *var, *vars_end;
  for (var = qr->pcnf.vars, vars_end = var + qr->pcnf.size_vars; 
       var < vars_end; var++)
    {
      unlink_redundant_clauses_occs (qr, &var->neg_occ_clauses);
      unlink_redundant_clauses_occs (qr, &var->pos_occ_clauses);
      
      unlink_redundant_clauses_occs (qr, &var->watched_neg_occ_clauses);
      unlink_redundant_clauses_occs (qr, &var->watched_pos_occ_clauses);

      /* Update statistics. */
      qr->total_occ_cnts += COUNT_STACK (var->neg_occ_clauses);
      qr->total_occ_cnts += COUNT_STACK (var->pos_occ_clauses);
      if ((unsigned int) COUNT_STACK (var->neg_occ_clauses) > qr->max_occ_cnt)
        qr->max_occ_cnt = (unsigned int) COUNT_STACK (var->neg_occ_clauses);
      if ((unsigned int) COUNT_STACK (var->pos_occ_clauses) > qr->max_occ_cnt)
        qr->max_occ_cnt = (unsigned int) COUNT_STACK (var->pos_occ_clauses);
    }
}

/* Top-level function of literal redundancy detection. Returns nonzero iff
   redundant literals were found. */
int
find_and_delete_redundant_literals (QRATPrePlus * qr)
{
  assert (!qr->options.no_ble || !qr->options.no_qratu);
  int result = 0;
  ClausePtrStack to_be_checked;
  INIT_STACK (to_be_checked);
  ClausePtrStack rescheduled;
  INIT_STACK (rescheduled);

  /* Clear set of witness clauses collected during clause elimination. */
  reset_witness_clauses (qr);
  assert (EMPTY_STACK (qr->witness_clauses));  
  
  /* Initially, schedule all input clauses to be checked. */
  assert (EMPTY_STACK (rescheduled));
  reschedule_from_input_clauses (qr, &rescheduled);

  /* Remove redundant clauses from data structures, which should improve
     QBCP performance. */
  unlink_redundant_clauses (qr);
  
  /* First apply computationally cheap blocked literal check (BLE). */
  if (!qr->options.no_ble)
    {
      result = find_and_delete_redundant_literals_aux 
        (qr, &to_be_checked, &rescheduled, QRATPLUS_CHECK_MODE_QBCE) || result;
    }

  /* Apply QRAT test to universal literals. */
  if (!qr->options.no_qratu)
    {
      if (!qr->options.no_ble)
        {
          RESET_STACK (to_be_checked);
          RESET_STACK (rescheduled);
          /* Schedule all input clauses to be checked. */
          reschedule_from_input_clauses (qr, &rescheduled);
        }
      result = find_and_delete_redundant_literals_aux 
        (qr, &to_be_checked, &rescheduled, QRATPLUS_CHECK_MODE_QRAT) || result;
    }
  
  DELETE_STACK (qr->mm, to_be_checked);
  DELETE_STACK (qr->mm, rescheduled);
  return result;
}

/* Top-level function of clause redundancy detection. Returns nonzero iff
   redundant clauses were found. */
int
find_and_mark_redundant_clauses (QRATPrePlus * qr)
{
  int result = 0;
  /* We call this function only if either QBCE, AT, or QRAT is enabled. */
  assert (!qr->options.no_qbce || !qr->options.no_qat || 
	  !qr->options.no_qrate);

  ClausePtrStack to_be_checked;
  INIT_STACK (to_be_checked);
  ClausePtrStack rescheduled;
  INIT_STACK (rescheduled);

  /* First apply QBCE until saturation. */
  if (!qr->options.no_qbce)
    {
      /* Initially, schedule all input clauses to be checked. */
      assert (EMPTY_STACK (rescheduled));
      reschedule_from_input_clauses (qr, &rescheduled);
      result = find_and_mark_redundant_clauses_aux (qr, &to_be_checked, 
                                                    &rescheduled, 
                                                    QRATPLUS_CHECK_MODE_QBCE) || result;
    }
  
  /* AT checking. */
  if (!qr->options.no_qat)
    {
      RESET_STACK (to_be_checked);
      RESET_STACK (rescheduled);

      /* Clear set of witness clauses collected during QBCE. */
      reset_witness_clauses (qr);

      /* After QBCE, schedule all input clauses that have not been found redundant
         (i.e., blocked) already to be checked for AT. */
      assert (EMPTY_STACK (rescheduled));
      reschedule_from_input_clauses (qr, &rescheduled);

      /* Remove redundant clauses from data structures, which should improve
         QBCP performance. */
      unlink_redundant_clauses (qr);

      /* Check currently non-redundant clauses if they have AT. */
      result = find_and_mark_redundant_clauses_aux (qr, &to_be_checked, 
                                                    &rescheduled, 
                                                    QRATPLUS_CHECK_MODE_AT) || result;
    }

  /* QRAT checking. */
  if (!qr->options.no_qrate)
    {
      RESET_STACK (to_be_checked);
      RESET_STACK (rescheduled);

      /* Clear set of witness clauses collected during QBCE. */
      reset_witness_clauses (qr);

      /* After QBCE, schedule all input clauses that have not been found redundant
         (i.e., blocked) already to be checked for QRAT. */
      assert (EMPTY_STACK (rescheduled));
      reschedule_from_input_clauses (qr, &rescheduled);

      /* Remove redundant clauses from data structures, which should improve
         QBCP performance. */ 
      unlink_redundant_clauses (qr);

      /* Check currently non-redundant clauses if they have QRAT. We did a QBCE
         check above because we observed that on some formulas QBCE alone can
         computationally quite cheaply remove many clauses, which may then speed up
         the following QRAT check as there are fewer clauses to consider than when
         applying QRAT to the original formula. */
      result = find_and_mark_redundant_clauses_aux (qr, &to_be_checked,
                                                    &rescheduled, 
                                                    QRATPLUS_CHECK_MODE_QRAT) || result;
    }

  DELETE_STACK (qr->mm, to_be_checked);
  DELETE_STACK (qr->mm, rescheduled);
  return result;
}

/* -------------------- END: PUBLIC FUNCTIONS -------------------- */
