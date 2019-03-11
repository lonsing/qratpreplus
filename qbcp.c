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

#include <assert.h>
#include <stdlib.h>
#include "qbcp.h"
#include "util.h"

/* Toggle expensive assertions for better control of fuzzing performance. */
#if 1
#define ASSERT_ALL_VAR_ASSIGNMENTS_RESET 1
#define ASSERT_FORMULA_STATE_AFTER_QBCP 1
#define ASSERT_WATCHED_LIT_STATE_BEFORE_ASSIGNING 1
#else
#define ASSERT_ALL_VAR_ASSIGNMENTS_RESET 0
#define ASSERT_FORMULA_STATE_AFTER_QBCP 0
#define ASSERT_WATCHED_LIT_STATE_BEFORE_ASSIGNING 0
#endif

/* ---------- START: QUANTIFIER TYPE ABSTRACTION ---------- */

/* A qblock 's' is existential if it is existential in the prefix of
   the input formula OR if it appears at a nesting level that is equal to
   or smaller than the current abstraction level 'qr->eabs_nesting'. By
   default, '->eabs_nesting' is set to UINT_MAX, thus making all
   variables to be treated as existential ones. */
static QuantifierType
eabs_get_qtype_of_qblock (QRATPrePlus * qr, QBlock *s)
{
  if (s->type == QTYPE_EXISTS || s->nesting <= qr->eabs_nesting)
    return QTYPE_EXISTS;
  else
    {
      assert (s->type == QTYPE_FORALL);
      return s->type;
    }
}

static QuantifierType
eabs_get_qtype_of_var (QRATPrePlus * qr, Var * var)
{
  return eabs_get_qtype_of_qblock (qr, var->qblock);
}

static QuantifierType
eabs_get_qtype_of_lit (QRATPrePlus * qr, LitID lit)
{
  return eabs_get_qtype_of_var (qr, LIT2VARPTR (qr->pcnf.vars, lit));
}

static int
eabs_is_qblock_existential (QRATPrePlus * qr, QBlock *s)
{
  return (eabs_get_qtype_of_qblock (qr, s) == QTYPE_EXISTS);
}

static int
eabs_is_var_existential (QRATPrePlus * qr, Var * var)
{
  return eabs_is_qblock_existential (qr, var->qblock);
}

static int
eabs_is_lit_existential (QRATPrePlus * qr, LitID lit)
{
  return eabs_is_var_existential (qr, LIT2VARPTR (qr->pcnf.vars, lit));
}


/* ---------- END: QUANTIFIER TYPE ABSTRACTION ---------- */

static void
assign_and_enqueue (QRATPrePlus * qr, Var * var, Assignment a)
{
  assert (a != ASSIGNMENT_UNDEF);
  assert (var->assignment == ASSIGNMENT_UNDEF);
  var->assignment = a;
  PUSH_STACK (qr->mm, qr->qbcp_queue, var->id);
  if (qr->options.verbosity >= 2)
    {
      fprintf (stderr, "  enqueued assignment: %d\n",
               var->assignment == ASSIGNMENT_FALSE ? -var->id : var->id);
    }
  qr->total_assignments++;
}

/* Returns index of clause 'c' on stack 'occs' of occurrences or
   'INVALID_OCC_INDEX' if 'c' does not appear in 'occs'. */
static unsigned int
get_index_of_clause_in_occs (QRATPrePlus *qr, Clause *c, ClausePtrStack *occs)
{
  Clause **p, **e;
  for (p = occs->start, e = occs->top; p < e; p++)
    if (*p == c)
      return (p - occs->start);
  return INVALID_OCC_INDEX;
}

/* When using quantifier type abstraction, then it may happen that the right
   watcher is set to a literal that effectively is universal in a forthcoming
   application of QBCP, i.e., when using a differen nesting level in the
   abstraction. To make sure that the right watcher is always at an
   existential literal REGARDLESS of the abstraction level, we initialize the
   literal watcher to the leftmost literals in the clause (in the input
   formula, all leftmost literals in clauses are existential.) */
static void
retract_re_init_lit_watchers (QRATPrePlus * qr)
{
  assert (!qr->options.no_eabs);
  Clause **occ_p, **occ_e;
  for (occ_p = qr->lw_update_clauses.start, occ_e = qr->lw_update_clauses.top;
       occ_p < occ_e; occ_p++)
    {
      Clause *c = *occ_p;
      assert (c->lw_update_collected);
      c->lw_update_collected = 0;
      assert (c->num_lits >= 2);
      if (!c->ignore_in_qbcp && !c->redundant)
        {
          if (qr->options.verbosity >= 2)
            {
              fprintf (stderr, "  retract watchers of clause ID %u: ", c->id);
              print_lits (qr, stderr, c->lits, c->num_lits, 1);
              fprintf (stderr, "    ...with lw-index %u and rw-index %u\n", 
                       c->lw_index, c->rw_index);
            }

          assert (c->lw_index < c->rw_index);

          /* Remove this clause 'c' from list of watched occs. */
          LitID old_rw_lit = c->lits[c->rw_index];
          Var *old_rw_var = LIT2VARPTR (qr->pcnf.vars, old_rw_lit);

          if (old_rw_var->qblock->type == QTYPE_FORALL)
            {
              ClausePtrStack *woccs = LIT_NEG (old_rw_lit) ?
                &old_rw_var->watched_neg_occ_clauses : &old_rw_var->watched_pos_occ_clauses;
              unsigned int old_occ_index = get_index_of_clause_in_occs (qr, c, woccs);
              assert (old_occ_index != INVALID_OCC_INDEX);
              Clause *last_occ = POP_STACK (*woccs);
              woccs->start[old_occ_index] = last_occ;

              /* Set right watched literal. */
              c->rw_index = c->num_lits - 1;
              LitID lit = c->lits[c->rw_index];
              Var *var = LIT2VARPTR (qr->pcnf.vars, lit);
              assert (var->qblock->type == QTYPE_EXISTS);
              /* Add 'c' to watched occurrences. */
              if (LIT_NEG (lit))
                PUSH_STACK (qr->mm, var->watched_neg_occ_clauses, c);
              else
                PUSH_STACK (qr->mm, var->watched_pos_occ_clauses, c);

              assert (c->lw_index < c->rw_index);

              if (qr->options.verbosity >= 2)
                fprintf (stderr, "    ...updated to: lw-index %u and rw-index %u\n", 
                         c->lw_index, c->rw_index);
            }
          else
            {
              if (qr->options.verbosity >= 2)
                fprintf (stderr, "    ...not updated, rw-index %u existential\n", 
                         c->rw_index);
            }
        }
    }

  RESET_STACK (qr->lw_update_clauses);
}

static void
retract_assigned_var (QRATPrePlus * qr, Var * var)
{
  assert (var->assignment != ASSIGNMENT_UNDEF);
  /* NOTE: variable may or may not have been propagated already. */
  if (var->propagated)
    var->propagated = 0;
  var->assignment = ASSIGNMENT_UNDEF;
}

static void
retract (QRATPrePlus * qr)
{
  /* Must retract propagated and unpropagated variables. */
  VarID *qbcp_p, *qbcp_e;
  for (qbcp_p = qr->qbcp_queue.start, qbcp_e = qr->qbcp_queue.top;
       qbcp_p < qbcp_e; qbcp_p++)
    {
      Var *prop_var = VARID2VARPTR (qr->pcnf.vars, *qbcp_p);
      assert (prop_var->assignment != ASSIGNMENT_UNDEF);
      retract_assigned_var (qr, prop_var);
    }
  RESET_STACK (qr->qbcp_queue);

  /* When using abstraction, must make sure that right watcher is always
     at an existential literal. Update watchers in collected clauses. */
  if (!qr->options.no_eabs)
    retract_re_init_lit_watchers (qr);
}

/* Find index of a new unassigned literal in 'c->lits' to watch, starting to
   look from index 'start_index' towards beginning of 'c->lits', that has the
   desired quantifier type. If 'desired_type == QTYPE_UNDEF' then ignore
   quantifier type of literal. Returns 'WATCHED_LIT_INVALID_INDEX' if no such
   literal is found, or 'WATCHED_LIT_CLAUSE_SAT' if clause satisfied, or index
   of new watched literal. */
static unsigned int
get_index_of_new_watched_lit (QRATPrePlus * qr, Clause *c, 
                              unsigned int start_index, 
                              QuantifierType desired_type)
{
  /* We never explicitly look for universal literals to watch. */
  assert (desired_type == QTYPE_UNDEF || desired_type == QTYPE_EXISTS);
  assert (start_index <= c->num_lits - 1);
  LitID *p, *e;
  for (e = c->lits, p = e + start_index; e <= p; p--)
    {
      LitID lit = *p;
      Var *var = LIT2VARPTR (qr->pcnf.vars, lit);
      if (var->assignment == ASSIGNMENT_UNDEF)
        {
          if (desired_type == QTYPE_UNDEF || eabs_is_var_existential (qr, var))
            return (p - e);
        }
      else
        {
          if ((LIT_NEG (lit) && var->assignment == ASSIGNMENT_FALSE) || 
              (LIT_POS (lit) && var->assignment == ASSIGNMENT_TRUE))
            return WATCHED_LIT_CLAUSE_SAT;
        }
    }
  return WATCHED_LIT_INVALID_INDEX;
}

/* For assertion checking only. */
static int
is_clause_empty (QRATPrePlus *qr, Clause *c)
{
  assert (!c->ignore_in_qbcp && !c->redundant);
  LitID *p, *e;
  for (p = c->lits, e = p + c->num_lits; p < e; p++)
    {
      LitID lit = *p;
      Var *var = LIT2VARPTR (qr->pcnf.vars, lit);
      if (var->assignment == ASSIGNMENT_UNDEF && 
	  eabs_is_var_existential (qr, var))
        return 0;
      /* Any satisfying literal makes clause non-empty. */
      else if ((LIT_NEG (lit) && var->assignment == ASSIGNMENT_FALSE) || 
               (LIT_POS (lit) && var->assignment == ASSIGNMENT_TRUE))
        return 0;
    }
  return 1;
}

/* For assertion checking only. */
static int
is_clause_satisfied (QRATPrePlus *qr, Clause *c)
{
  assert (!c->ignore_in_qbcp && !c->redundant);
  LitID *p, *e;
  for (p = c->lits, e = p + c->num_lits; p < e; p++)
    {
      LitID lit = *p;
      Var *var = LIT2VARPTR (qr->pcnf.vars, lit);
      if ((LIT_NEG (lit) && var->assignment == ASSIGNMENT_FALSE) || 
          (LIT_POS (lit) && var->assignment == ASSIGNMENT_TRUE))
        return 1;
    }
  return 0;
}

/* Returns unique unassigned existential literal in clause or 0 if such
   literal does not exist. */
static LitID
find_unique_unassigned_existential_lit (QRATPrePlus *qr, Clause *c)
{
  LitID result = 0;
  LitID *p, *e;
  for (p = c->lits, e = p + c->num_lits; p < e; p++)
    {
      LitID lit = *p;
      assert (lit);
      Var *var = LIT2VARPTR (qr->pcnf.vars, lit);
      if (var->assignment == ASSIGNMENT_UNDEF && 
          eabs_is_var_existential (qr, var))
        {
          if (!result)
            result = lit;
          else
            return 0;
        }
    }
  return result;
}

/* Returns nonzero iff all universal literals smaller than 'check_lit' with
   respect to quantifier ordering in clause 'c' are falsified under current
   assignment. */
static int
check_smaller_universal_lits_falsified (QRATPrePlus *qr, Clause *c, 
                                         LitID check_lit)
{
  assert (!is_clause_satisfied (qr, c));
  assert (find_literal (check_lit, c->lits, c->lits + c->num_lits));
  Var *check_var = LIT2VARPTR (qr->pcnf.vars, check_lit);
  assert (eabs_is_var_existential (qr, check_var));
  LitID *p, *e;
  for (p = c->lits, e = p + c->num_lits; p < e; p++)
    {
      LitID lit = *p;
      Var *var = LIT2VARPTR (qr->pcnf.vars, lit);
      if (var->qblock->nesting > check_var->qblock->nesting)
        return 1;
      assert (var->qblock->nesting <= check_var->qblock->nesting);
      /* Check assignment of universal literals smaller than 'check_lit'. */
      if (eabs_get_qtype_of_var (qr, var) == QTYPE_FORALL)
        {
          /* No need to check for satisfying literals as we assume that this
             function is only called on clauses not satisfied. */
          if (var->assignment == ASSIGNMENT_UNDEF)
            return 0;
        }
    }
  return 1;
}

/* For assertion checking only. */
static int
is_clause_unit (QRATPrePlus *qr, Clause *c)
{
  assert (!c->ignore_in_qbcp && !c->redundant);

  if (is_clause_satisfied (qr, c) || is_clause_empty (qr, c))
    return 0;

  LitID unique_elit = find_unique_unassigned_existential_lit (qr, c);
  if (!unique_elit)
    return 0;

  if (!check_smaller_universal_lits_falsified (qr, c, unique_elit))
    return 0;
  else
    return 1;
}

static void
handle_unit_clause (QRATPrePlus * qr, Clause *c, LitID unit_lit)
{
  assert (is_clause_unit (qr, c));
  LitID unassigned_lit = unit_lit;
  if (qr->options.verbosity >= 2)
    fprintf (stderr, "    clause has unit literal %d\n", unassigned_lit);
  Var *unassigned_var = LIT2VARPTR (qr->pcnf.vars, unassigned_lit);
  assign_and_enqueue (qr, unassigned_var, LIT_NEG (unassigned_lit) ?
                      ASSIGNMENT_FALSE : ASSIGNMENT_TRUE);
}

/* Like 'propagate_clause (...)' but check and updated watched literals to see
   if clause is satisfied, unit, or conflicting under enqueued assignment. */
static QBCPState
propagate_clause_watched_lits (QRATPrePlus * qr, Clause *c)
{
  assert (!c->ignore_in_qbcp);
  assert (!c->redundant);
  assert (c->num_lits >= 2);

  if (qr->options.verbosity >= 2)
    {
      fprintf (stderr, "  propagate clause ID %u and updating watched literals: ", c->id);
      print_lits (qr, stderr, c->lits, c->num_lits, 1);
    }
    
  assert (c->rw_index < c->num_lits);
  LitID rw_lit = c->lits[c->rw_index];
  Var *rw_var = LIT2VARPTR (qr->pcnf.vars, rw_lit);
  assert (eabs_is_var_existential (qr, rw_var));

  /* Return immediately if right watcher satisfies clause already. */
  if ((LIT_NEG (rw_lit) && rw_var->assignment == ASSIGNMENT_FALSE) || 
      (LIT_POS (rw_lit) && rw_var->assignment == ASSIGNMENT_TRUE))
    {
      assert (is_clause_satisfied (qr, c));
      return QBCP_STATE_UNKNOWN;
    }

  assert (c->lw_index < c->rw_index);
  LitID lw_lit = c->lits[c->lw_index];
  Var *lw_var = LIT2VARPTR (qr->pcnf.vars, lw_lit);

  /* Return immediately if left watcher satisfies clause already. */
  if ((LIT_NEG (lw_lit) && lw_var->assignment == ASSIGNMENT_FALSE) || 
      (LIT_POS (lw_lit) && lw_var->assignment == ASSIGNMENT_TRUE))
    {
      assert (is_clause_satisfied (qr, c));
      return QBCP_STATE_UNKNOWN;
    }

  /* At least one watched literal must be assigned. */
  assert (lw_var->assignment != ASSIGNMENT_UNDEF || 
          rw_var->assignment != ASSIGNMENT_UNDEF);

  /* For simplicity, always update both watched literals. */
  unsigned int new_rw_index = 
    get_index_of_new_watched_lit (qr, c, c->num_lits - 1, QTYPE_EXISTS);

  /* Return immediately if clause found satisfied. */
  if (new_rw_index == WATCHED_LIT_CLAUSE_SAT)
    {
      assert (is_clause_satisfied (qr, c));
      return QBCP_STATE_UNKNOWN;
    }
  /* No new right watcher: clause is conflicting. */
  else if (new_rw_index == WATCHED_LIT_INVALID_INDEX)
    {
      assert (is_clause_empty (qr, c));
      return QBCP_STATE_UNSAT;
    }

  /* Found index of new right watched literal. */
  assert (new_rw_index < c->num_lits);

  /* Handle unit clause. */
  if (new_rw_index == 0)
    {
      handle_unit_clause (qr, c, c->lits[new_rw_index]);
      return QBCP_STATE_UNKNOWN;
    }

  /* Search for index of new left watcher starting one position to the left of
     new right watcher. */
  unsigned int new_lw_index = 
    get_index_of_new_watched_lit (qr, c, new_rw_index - 1, QTYPE_UNDEF);

  if (new_lw_index == WATCHED_LIT_CLAUSE_SAT)
    {
      assert (is_clause_satisfied (qr, c));
      return QBCP_STATE_UNKNOWN;
    }
  /* No new left watcher: clause is unit. */
  else if (new_lw_index == WATCHED_LIT_INVALID_INDEX)
    {
      handle_unit_clause (qr, c, c->lits[new_rw_index]);
      return QBCP_STATE_UNKNOWN;
    }

  /* Found index of new left watched literal. */
  assert (new_lw_index < new_rw_index);

  /* Update watched literals and entries on watched occurrences, if needed. */
  //TODO: avoid code repetition in branches below  
  if (new_rw_index != c->rw_index)
    {
      /* Remove this clause 'c' from list of watched occs. */
      LitID old_rw_lit = c->lits[c->rw_index];
      Var *old_rw_var = LIT2VARPTR (qr->pcnf.vars, old_rw_lit);
      ClausePtrStack *occs = LIT_NEG (old_rw_lit) ?
        &old_rw_var->watched_neg_occ_clauses : &old_rw_var->watched_pos_occ_clauses;
      unsigned int old_occ_index = get_index_of_clause_in_occs (qr, c, occs);
      assert (old_occ_index != INVALID_OCC_INDEX);
      Clause *last_occ = POP_STACK (*occs);
      occs->start[old_occ_index] = last_occ;
      /* Set new watched literal and add this clause 'c' to watched occs. */
      c->rw_index = new_rw_index;
      LitID new_rw_lit = c->lits[c->rw_index];
      Var *new_rw_var = LIT2VARPTR (qr->pcnf.vars, new_rw_lit);
      occs = LIT_NEG (new_rw_lit) ?
        &new_rw_var->watched_neg_occ_clauses : &new_rw_var->watched_pos_occ_clauses;
      PUSH_STACK (qr->mm, *occs, c);
      /* New right watcher is at a syntactic universal literal, which is
         currently treated as existential under the abstraction. When retracting
         assignments, must make sure to properly set right watcher to an
         existential literal. */
      if (!qr->options.no_eabs && new_rw_var->qblock->type == QTYPE_FORALL && 
          !c->lw_update_collected)
        {
          c->lw_update_collected = 1;
          PUSH_STACK (qr->mm, qr->lw_update_clauses, c);
          if (qr->options.verbosity >= 2)
            {
              fprintf (stderr, "    collected clause ID %u for eabs right watcher update: ", c->id);
              print_lits (qr, stderr, c->lits, c->num_lits, 1);
            }
        }
    }

  if (new_lw_index != c->lw_index)
    {
      /* Remove this clause 'c' from list of watched occs. */
      LitID old_lw_lit = c->lits[c->lw_index];
      Var *old_lw_var = LIT2VARPTR (qr->pcnf.vars, old_lw_lit);
      ClausePtrStack *occs = LIT_NEG (old_lw_lit) ?
        &old_lw_var->watched_neg_occ_clauses : &old_lw_var->watched_pos_occ_clauses;
      unsigned int old_occ_index = get_index_of_clause_in_occs (qr, c, occs);
      assert (old_occ_index != INVALID_OCC_INDEX);
      Clause *last_occ = POP_STACK (*occs);
      occs->start[old_occ_index] = last_occ;
      /* Set new watched literal and add this clause 'c' to watched occs. */
      c->lw_index = new_lw_index;
      LitID new_lw_lit = c->lits[c->lw_index];
      Var *new_lw_var = LIT2VARPTR (qr->pcnf.vars, new_lw_lit);
      occs = LIT_NEG (new_lw_lit) ?
        &new_lw_var->watched_neg_occ_clauses : &new_lw_var->watched_pos_occ_clauses;
      PUSH_STACK (qr->mm, *occs, c);
    }

  return QBCP_STATE_UNKNOWN;
}

/* Check if clause is satisfied, unit, or conflicting under enqueued assignment. */
static QBCPState
propagate_clause (QRATPrePlus * qr, Clause *c)
{
  assert (!c->ignore_in_qbcp);
  assert (!c->redundant);

  if (qr->options.verbosity >= 2)
    {
      fprintf (stderr, "  propagate clause: ");
      print_lits (qr, stderr, c->lits, c->num_lits, 1);
    }
  
  unsigned int cnt_unassigned = 0;
  LitID unassigned_lit = 0;
  LitID *p, *e;
  for (p = c->lits, e = p + c->num_lits; p < e; p++)
    {
      LitID lit = *p;
      Var *var = LIT2VARPTR (qr->pcnf.vars, lit);
      Assignment var_a = var->assignment;
      if (var_a == ASSIGNMENT_UNDEF && eabs_is_var_existential (qr, var))
        {
          cnt_unassigned++;
          unassigned_lit = lit;
          if (qr->options.verbosity >= 2)
            fprintf (stderr, "    clause has unassigned literal %d\n", lit);
        }
      else
        {
          /* Check for satisfying literals and, if found, return immediately. */
          if ((LIT_NEG (lit) && var_a == ASSIGNMENT_FALSE) ||
              (LIT_POS (lit) && var_a == ASSIGNMENT_TRUE))
            {
               if (qr->options.verbosity >= 2)
                 fprintf (stderr, "    clause satisfied by lit %d and assignment %d\n", lit, var_a);
              return QBCP_STATE_UNKNOWN;
            }
        }
    }

  /* Enqueue assignment resulting from unit clause or report conflict. */
  if (cnt_unassigned == 1)
    {
      assert (unassigned_lit);
      handle_unit_clause (qr, c, unassigned_lit);
    }
  else if (cnt_unassigned == 0)
    {
      if (qr->options.verbosity >= 2)
        fprintf (stderr, "    clause is conflicting\n");      
      return QBCP_STATE_UNSAT;
    }

  if (qr->options.verbosity >= 2)
    fprintf (stderr, "    state unknown after clause propagation\n");
  
  return QBCP_STATE_UNKNOWN;
}

static Clause *
find_unsatisfied_occ (QRATPrePlus * qr, ClausePtrStack *occs)
{
 Clause **occ_p, **occ_e;
  for (occ_p = occs->start, occ_e = occs->top; occ_p < occ_e; occ_p++)
    {
      Clause *c = *occ_p;
      if (!c->ignore_in_qbcp && !c->redundant)
	if (!is_clause_satisfied (qr, c))
	  return c;
    }
  return 0;
}

/* Like 'propagate_assigned_var (...)' but based on watched literals. */
static QBCPState
propagate_assigned_var_watched_lits (QRATPrePlus * qr, Var * var)
{
  assert (var->assignment != ASSIGNMENT_UNDEF);
  assert (!var->propagated);

  if (qr->options.verbosity >= 2)
    {
      fprintf (stderr, "  propagate assignment: %d\n",
               var->assignment == ASSIGNMENT_FALSE ? -var->id : var->id);
    }
  
  QBCPState state = QBCP_STATE_UNKNOWN;

  /* Check clauses shortened by assignment to detect units and conflicts. */
  ClausePtrStack *occs = var->assignment == ASSIGNMENT_FALSE ?
    &var->watched_pos_occ_clauses : &var->watched_neg_occ_clauses; 
  /* Updating watched literals will modify the list of occurrences. Keep track
     of occs-count to make sure we fully traverse the modified list. */
  unsigned int occs_cnt = (unsigned int) COUNT_STACK (*occs);
  Clause **occ_p, **occ_e;
  for (occ_p = occs->start, occ_e = occs->top;
       occ_p < occ_e && state == QBCP_STATE_UNKNOWN; occ_p++)
    {
      Clause *c = *occ_p;
      /* Must ignore tested clause and also redundant clauses. */
      if (!c->ignore_in_qbcp && !c->redundant)
        {
          state = propagate_clause_watched_lits (qr, c);
          if (occs_cnt != COUNT_STACK (*occs))
            {
              /* Last entry of 'occs' has been used to overwrite current
                 one. Update pointers to fully traverse list. */
              assert (occs_cnt == (unsigned int) COUNT_STACK (*occs) + 1);
              occs_cnt--;
              occ_p--;
              occ_e--;
            }
          qr->qbcp_cur_props++;
        }
    }

  if (state == QBCP_STATE_UNKNOWN)
    var->propagated = 1;

  return state;
}

static QBCPState
assign_vars_from_unit_input_clauses (QRATPrePlus *qr)
{
  QBCPState state = QBCP_STATE_UNKNOWN;

  if (qr->options.verbosity >= 2)
    fprintf (stderr, "  Assigning variables from unit input clauses\n");   
  
  Clause **cp, **ce;
  for (cp = qr->unit_input_clauses.start, ce = qr->unit_input_clauses.top;
       cp < ce && state == QBCP_STATE_UNKNOWN; cp++)
    {
      Clause *c = *cp;
      assert (c->num_lits == 1);
      if (!c->redundant && !c->ignore_in_qbcp)
        state = propagate_clause (qr, c);   
    }
  
  return state;
}

/* For asymmetric tautology check, we pass value '0' as parameter
   'lit' to make sure that assignments from all literals in clause are
   enqueued. */
static QBCPState
assign_vars_from_tested_clause (QRATPrePlus *qr, Clause *c, LitID lit)
{
  QBCPState state = QBCP_STATE_UNKNOWN;

  const Nesting pivot_nesting = lit ? 
    LIT2VARPTR (qr->pcnf.vars, lit)->qblock->nesting : UINT_MAX;

  if (qr->options.verbosity >= 2)
    fprintf (stderr, "  Assigning variables from tested clause\n");   
  
  /* Collect assignments from: 'c \ {lit}'. */
  LitID *p, *e;
  for (p = c->lits, e = p + c->num_lits;
       p < e && state == QBCP_STATE_UNKNOWN; p++)
    {
      LitID cl = *p;
      if (cl != lit)
        {
          Var *cl_var = LIT2VARPTR (qr->pcnf.vars, cl);

          /* Ignore literals inner to the pivot. */
          if (qr->options.ignore_inner_lits && 
              cl_var->qblock->nesting > pivot_nesting)
            continue;

	  /* Compute maximum nesting over initially assigned variables. */
	  if (cl_var->qblock->nesting > qr->eabs_nesting_aux)
	    qr->eabs_nesting_aux = cl_var->qblock->nesting;
          if (cl_var->assignment == ASSIGNMENT_UNDEF)
            assign_and_enqueue (qr, cl_var, LIT_NEG (cl) ?
                                ASSIGNMENT_TRUE : ASSIGNMENT_FALSE);
          else
            {
              /* Catch double and conflicting assignments of 'cl_var',
                 which may happen if 'cl_var' appears in unit input, or if
                 outer resolvent is tautological. */
              if ((LIT_NEG (cl) && cl_var->assignment == ASSIGNMENT_FALSE) ||
                  (LIT_POS (cl) && cl_var->assignment == ASSIGNMENT_TRUE))
                state = QBCP_STATE_UNSAT;
            }
        }
    }
  
  return state;
}

static QBCPState
assign_vars_from_other_clause (QRATPrePlus *qr, Clause *occ, LitID lit)
{
  QBCPState state = QBCP_STATE_UNKNOWN;

  if (qr->options.verbosity >= 2)
    fprintf (stderr, "  Assigning variables from other (occ) clauses\n");   
  
  Var *var = LIT2VARPTR (qr->pcnf.vars, lit);
  const Nesting nesting = var->qblock->nesting;
  
  /* Collect assignments from: all lits in 'occ' from qblock smaller or
     equal to qblock of 'lit' except in '\neg lit'. */
  LitID *p, *e;
  for (p = occ->lits, e = p + occ->num_lits; p < e; p++)
    {
      LitID cl = *p;
      Var *cl_var = LIT2VARPTR (qr->pcnf.vars, cl);
      if (cl != -lit)
        {
          /* Literals are sorted, hence abort if literal from qblock
             larger than that of 'lit' is seen. */
          if (cl_var->qblock->nesting <= nesting)
            {
	      /* Compute maximum nesting over initially assigned variables. */
	      if (cl_var->qblock->nesting > qr->eabs_nesting_aux)
		qr->eabs_nesting_aux = cl_var->qblock->nesting;
              if (cl_var->assignment == ASSIGNMENT_UNDEF)
                assign_and_enqueue (qr, cl_var, LIT_NEG (cl) ?
                                    ASSIGNMENT_TRUE : ASSIGNMENT_FALSE);
              else
                {
                  /* Catch double and conflicting assignments of 'cl_var',
                     which may happen if 'cl_var' appears in unit input, or if
                     outer resolvent is tautological. */
                  if ((LIT_NEG (cl) && cl_var->assignment == ASSIGNMENT_FALSE) ||
                      (LIT_POS (cl) && cl_var->assignment == ASSIGNMENT_TRUE))
                    state = QBCP_STATE_UNSAT;
                }
            }
          else
            break;
        }
    }

  return state;
}

/* For assertion checking only. */
static int
has_formula_empty_clause (QRATPrePlus *qr)
{
  Clause *c;
  for (c = qr->pcnf.clauses.first; c; c = c->link.next)
    if (!c->ignore_in_qbcp && !c->redundant && is_clause_empty (qr, c))
      return 1;
  return 0;
}

static int
has_formula_unit_clause (QRATPrePlus *qr)
{
  Clause *c;
  for (c = qr->pcnf.clauses.first; c; c = c->link.next)
    if (!c->ignore_in_qbcp && !c->redundant && is_clause_unit (qr, c))
      return 1;
  return 0;
}

/* For assertion checking only. */
static void
assert_formula_state_after_qbcp (QRATPrePlus * qr, QBCPState state)
{
  if (state == QBCP_STATE_UNSAT)
    assert (has_formula_empty_clause (qr));
  else
    {
      assert (state == QBCP_STATE_UNKNOWN);
      assert (!has_formula_empty_clause (qr));
      assert (!has_formula_unit_clause (qr));
    }
}

/* For assertion checking only. */
static void
assert_check_clause_watched_lits (QRATPrePlus *qr, Clause *c)
{
  /* No watched literals in empty or unit clauses. */
  if (c->num_lits <= 1)
    return;

  assert (c->rw_index < c->num_lits);
  assert (c->lw_index < c->rw_index);

  LitID lit = c->lits[c->rw_index];
  Var *var = LIT2VARPTR (qr->pcnf.vars, lit);
  assert (var->assignment == ASSIGNMENT_UNDEF);
  assert (eabs_is_var_existential (qr, var));
  if (LIT_NEG (lit))
    assert (get_index_of_clause_in_occs (qr, c, &(var->watched_neg_occ_clauses)) 
            != INVALID_OCC_INDEX);
  else
    assert (get_index_of_clause_in_occs (qr, c, &(var->watched_pos_occ_clauses)) 
            != INVALID_OCC_INDEX);

  lit = c->lits[c->lw_index];
  var = LIT2VARPTR (qr->pcnf.vars, lit);
  assert (var->assignment == ASSIGNMENT_UNDEF);
  if (LIT_NEG (lit))
    assert (get_index_of_clause_in_occs (qr, c, &(var->watched_neg_occ_clauses)) 
            != INVALID_OCC_INDEX);
  else
    assert (get_index_of_clause_in_occs (qr, c, &(var->watched_pos_occ_clauses)) 
            != INVALID_OCC_INDEX);
}

/* For assertion checking only. */
static void
assert_watched_lit_state_before_assigning (QRATPrePlus *qr)
{
  Clause *c;
  for (c = qr->pcnf.clauses.first; c; c = c->link.next)
    assert_check_clause_watched_lits (qr, c);
}

static QBCPState
qbcp (QRATPrePlus * qr)
{
  qr->qbcp_total_calls++;
  if (!qr->options.no_eabs)
    qr->qbcp_total_eabs_nestings += qr->eabs_nesting;

  assert (EMPTY_STACK (qr->lw_update_clauses));
  QBCPState state = QBCP_STATE_UNKNOWN;

  if (qr->options.verbosity >= 2)
    fprintf (stderr, "  Starting QBCP with EABS nesting %u\n", qr->eabs_nesting);
  
  /* NOTE: memory region of QBCP queue might be enlarged during
     propagation, hence cannot keep pointer into region. */
  unsigned int qbcp_index = 0;
  VarID *qbcp_p, *qbcp_e;
  for (qbcp_p = qr->qbcp_queue.start, qbcp_e = qr->qbcp_queue.top;
       qbcp_p < qbcp_e && state == QBCP_STATE_UNKNOWN;
       qbcp_p = qr->qbcp_queue.start + ++qbcp_index)
    {
      assert (qbcp_p < qr->qbcp_queue.top);
      assert (qr->qbcp_queue.start <= qbcp_p);

      /* Check if propagation limit reached. */
      if (qr->qbcp_cur_props > qr->limit_qbcp_cur_props)
        {
          qr->limit_qbcp_cur_props_reached++;
          break;
        }

      Var *prop_var = VARID2VARPTR (qr->pcnf.vars, *qbcp_p);

      state = propagate_assigned_var_watched_lits (qr, prop_var);
      
      /* Reassign pointers as queue may have grown and memory enlarged. */
      qbcp_e = qr->qbcp_queue.top;
    }

#if ASSERT_FORMULA_STATE_AFTER_QBCP
#ifndef NDEBUG
  assert_formula_state_after_qbcp (qr, state);
#endif
#endif

  return state;
}

/* -------------------- START: PUBLIC FUNCTIONS -------------------- */

/* Check if 'c' is an asymmetric tautology by negating the clause and
   propagating either by BCP or QBCP, i.e., on full propositional
   abstraction or with respect to nesting level of largest literal in
   clause. */
int 
qrat_qat_check (QRATPrePlus * qr, Clause *c)
{
  assert (qr->eabs_nesting == UINT_MAX);
  assert (qr->eabs_nesting_aux == 0);

  QBCPState state = QBCP_STATE_UNKNOWN;

  qr->qbcp_total_props += qr->qbcp_cur_props;
  qr->qbcp_cur_props = 0;
  
  if (qr->options.verbosity >= 2)
    {
      fprintf (stderr, "Asymm. taut. check with internal QBCP on clause: ");
      print_lits (qr, stderr, c->lits, c->num_lits, 1);
    }
  
  assert (!c->redundant);
  assert (!c->ignore_in_qbcp);
  /* Mark tested clause so that it is ignored in QBCP and cannot
     trigger unit implications or conflicts. */
  c->ignore_in_qbcp = 1;
  
  assert (EMPTY_STACK (qr->qbcp_queue));

#if ASSERT_WATCHED_LIT_STATE_BEFORE_ASSIGNING
#ifndef NDEBUG
  assert_watched_lit_state_before_assigning (qr);
#endif
#endif

  /* Collect assignments from unit input clauses and from entire clause 'c'. */
  if ((state = assign_vars_from_unit_input_clauses (qr)) == QBCP_STATE_UNSAT ||
      (state = assign_vars_from_tested_clause (qr, c, 0)) == QBCP_STATE_UNSAT)
    {
      retract (qr);
      assert (c->ignore_in_qbcp);
      c->ignore_in_qbcp = 0;
      qr->eabs_nesting = UINT_MAX;
      qr->eabs_nesting_aux = 0;
      return 1;
    }

  if (!qr->options.no_eabs)
    {
      if (!qr->options.no_eabs_improved_nesting)
        {
          if (qr->eabs_nesting_aux > 0)
            qr->eabs_nesting_aux--;
        }
      qr->eabs_nesting = qr->eabs_nesting_aux;
    }
  else
    assert (qr->eabs_nesting == UINT_MAX);

  state = qbcp (qr);

  retract (qr);
  assert (c->ignore_in_qbcp);
  c->ignore_in_qbcp = 0;

  if (state == QBCP_STATE_UNSAT)
    {
      qr->qbcp_successful_checks_props += qr->qbcp_cur_props;
    }
    
#if ASSERT_ALL_VAR_ASSIGNMENTS_RESET
#ifndef NDEBUG
    Var *vp, *ve;
    for (vp = qr->pcnf.vars, ve = qr->pcnf.vars + qr->pcnf.size_vars; vp < ve; vp++)
      assert (vp->assignment == ASSIGNMENT_UNDEF);
#endif
#endif

  qr->eabs_nesting = UINT_MAX;
  qr->eabs_nesting_aux = 0;
  
  return (state == QBCP_STATE_UNSAT);
}

int
qrat_qbcp_check (QRATPrePlus * qr, Clause *c, LitID lit, Clause *occ)
{  
  assert (qr->eabs_nesting == UINT_MAX);
  assert (qr->eabs_nesting_aux == 0);

  QBCPState state = QBCP_STATE_UNKNOWN;

  qr->qrat_qbcp_checks++;
  qr->qbcp_total_props += qr->qbcp_cur_props;
  qr->qbcp_cur_props = 0;
  
  if (qr->options.verbosity >= 2)
    {
      fprintf (stderr, "QRAT check with internal QBCP on clause: ");
      print_lits (qr, stderr, c->lits, c->num_lits, 1);
      fprintf (stderr, "  ... and occ: ");
      print_lits (qr, stderr, occ->lits, occ->num_lits, 1);
      fprintf (stderr, "  ... and pivot: %d\n", lit);
    }
  
  assert (!c->redundant);
  assert (!c->ignore_in_qbcp);
  /* Mark tested clause so that it is ignored in QBCP and cannot
     trigger unit implications or conflicts. */
  c->ignore_in_qbcp = 1;
  
  assert (EMPTY_STACK (qr->qbcp_queue));

#if ASSERT_WATCHED_LIT_STATE_BEFORE_ASSIGNING
#ifndef NDEBUG
  assert_watched_lit_state_before_assigning (qr);
#endif
#endif

  /* Enqueue all assignments from unit input clauses. */
  if ((state = assign_vars_from_unit_input_clauses (qr)) == QBCP_STATE_UNSAT ||
      /* Collect assignments from: 'c \ {lit}'. */
      (state = assign_vars_from_tested_clause (qr, c, lit)) == QBCP_STATE_UNSAT ||
      /* Collect assignments from: all lits in 'occ' from qblock smaller or
         equal to qblock of 'lit' except in '\neg lit'. */
      (state = assign_vars_from_other_clause (qr, occ, lit)) == QBCP_STATE_UNSAT)
    {
      retract (qr);
      assert (c->ignore_in_qbcp);
      c->ignore_in_qbcp = 0;
      qr->eabs_nesting = UINT_MAX;
      qr->eabs_nesting_aux = 0;
      return 1;
    }

  if (!qr->options.no_eabs)
    {
      if (!qr->options.no_eabs_improved_nesting)
        {
          if (qr->eabs_nesting_aux > 0)
            qr->eabs_nesting_aux--;
        }
      qr->eabs_nesting = qr->eabs_nesting_aux;
    }
  else
    assert (qr->eabs_nesting == UINT_MAX);

  state = qbcp (qr);

  retract (qr);
  assert (c->ignore_in_qbcp);
  c->ignore_in_qbcp = 0;

  if (state == QBCP_STATE_UNSAT)
    {
      qr->qbcp_successful_checks_props += qr->qbcp_cur_props;
      qr->qrat_qbcp_successful_checks++;
    }
    
#if ASSERT_ALL_VAR_ASSIGNMENTS_RESET
#ifndef NDEBUG
    Var *vp, *ve;
    for (vp = qr->pcnf.vars, ve = qr->pcnf.vars + qr->pcnf.size_vars; vp < ve; vp++)
      assert (vp->assignment == ASSIGNMENT_UNDEF);
#endif
#endif
  
  qr->eabs_nesting = UINT_MAX;
  qr->eabs_nesting_aux = 0;

  return (state == QBCP_STATE_UNSAT);
}

/* -------------------- END: PUBLIC FUNCTIONS -------------------- */
