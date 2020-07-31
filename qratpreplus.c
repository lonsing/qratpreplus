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
#include "qbce_qrat_plus.h"
#include "parse.h"
#include "util.h"
#include "qratpreplus.h"
#include "qratpreplus_internals.h"

/* -------------------- START: COMMAND LINE / CONFIG PARSING -------------------- */

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

/* -------------------- END: COMMAND LINE / CONFIG PARSING -------------------- */

/* -------------------- START: HELPER FUNCTIONS -------------------- */

/* Free allocated memory. */
static void
cleanup (QRATPrePlus * qr)
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

  Var *vp, *ve;
  for (vp = qr->pcnf.vars, ve = vp + qr->pcnf.size_vars; vp < ve; vp++)
    {
      DELETE_STACK (qr->mm, vp->pos_occ_clauses);
      DELETE_STACK (qr->mm, vp->neg_occ_clauses);
      DELETE_STACK (qr->mm, vp->watched_pos_occ_clauses);
      DELETE_STACK (qr->mm, vp->watched_neg_occ_clauses);
    }
  mm_free (qr->mm, qr->pcnf.vars, qr->pcnf.size_vars * sizeof (Var));

  QBlock *s, *sn;
  for (s = qr->pcnf.qblocks.first; s; s = sn)
    {
      sn = s->link.next;
      DELETE_STACK (qr->mm, s->vars);
      mm_free (qr->mm, s, sizeof (QBlock));
    }

  Clause *c, *cn;
  for (c = qr->pcnf.clauses.first; c; c = cn)
    {
      cn = c->link.next;
      mm_free (qr->mm, c, sizeof (Clause) + c->size_lits * sizeof (LitID));
    }
}

/* If we clean up redundant clauses after preprocessing then calling
   this function has constant run time costs since the occurrence lists
   will contain non-redundant clauses only. */
static int
var_has_active_occs (QRATPrePlus *qr, Var *var, ClausePtrStack *occs)
{
  Clause **p, **e;
  for (p = occs->start, e = occs-> top; p < e; p++)
    {
      Clause *c = *p;
      if (!c->redundant)
        return 1;
    }
  return 0;
}

/* Returns non-zero iff the qblock contains at least one variable that
   appears in non-redundant clauses. */
static int
qblock_has_active_vars (QRATPrePlus *qr, QBlock *qb)
{
  VarID *p, *e;
  for (p = qb->vars.start, e = qb->vars.top; p < e; p++)
    {
      Var *var = VARID2VARPTR (qr->pcnf.vars, *p);
      if (var_has_active_occs (qr, var, &var->neg_occ_clauses) ||
          var_has_active_occs (qr, var, &var->pos_occ_clauses))
        return 1;
    }
  return 0;
}

static void
print_qblock_active_vars (QRATPrePlus *qr, QBlock *qb, FILE *out)
{
  VarID *p, *e;
  for (p = qb->vars.start, e = qb->vars.top; p < e; p++)
    {
      Var *var = VARID2VARPTR (qr->pcnf.vars, *p);
      if (var_has_active_occs (qr, var, &var->neg_occ_clauses) ||
          var_has_active_occs (qr, var, &var->pos_occ_clauses))
        fprintf (out, "%d ", var->id);
    }
  fprintf (out, "0\n");
}

static void
print_qblock (QRATPrePlus *qr, QBlock *qb, FILE *out)
{
  if (qblock_has_active_vars (qr, qb))
    {
      fprintf (out, "%c ", QBLOCK_FORALL (qb) ? 'a' : 'e');
      print_qblock_active_vars (qr, qb, out);
    }
}

/* If we clean up redundant clauses after preprocessing then calling
   this function has constant run time costs since the list of
   original clauses will contain non-redundant clauses only. */
static int
formula_has_non_redundant_clauses (QRATPrePlus *qr)
{
  Clause *c;
  for (c = qr->pcnf.clauses.first; c; c = c->link.next)
    if (!c->redundant)
      return 1;
  return 0;
}

static void
clean_up_empty_qblocks (QRATPrePlus *qr)
{
  MemMan *mem = qr->mm;
  QBlock *cur, *next;
  unsigned int modified = 0;
  
  for (cur = qr->pcnf.qblocks.first; cur; cur = next)
    {
      next = cur->link.next;
      if (!qblock_has_active_vars (qr, cur))
        {
          UNLINK (qr->pcnf.qblocks, cur, link);
          DELETE_STACK (qr->mm, cur->vars);
          mm_free (qr->mm, cur, sizeof (QBlock));
          modified = 1;
        }
    }
  
  if (modified)
    merge_adjacent_same_type_qblocks (qr, 1); 
}

static unsigned int
count_qtype_literals_in_formula (QRATPrePlus *qr, QuantifierType type)
{
  unsigned int result = 0;
  Clause *c;
  for (c = qr->pcnf.clauses.first; c; c = c->link.next)
    result += count_qtype_literals (qr, c, type);
  return result;
}

/* -------------------- END: HELPER FUNCTIONS -------------------- */

/* -------------------- START: SETUP -------------------- */

static void
set_default_options (QRATPrePlus * qr)
{
  qr->options.seed = 0;
  qr->options.in_filename = 0;
  qr->options.in = stdin;
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

#ifndef NDEBUG
static void
assert_formula_integrity (QRATPrePlus * qr)
{
  Clause *c;
  for (c = qr->pcnf.clauses.first; c; c = c->link.next)
    {
      assert_lits_sorted (qr, c->lits, c->lits + c->num_lits);
      LitID last = c->num_lits ? c->lits[c->num_lits - 1] : 0;
      Var *last_var = last ? LIT2VARPTR (qr->pcnf.vars, last) : 0;
      assert (!last_var || last_var->qblock->type == QTYPE_EXISTS);
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
    }
  QBlock *s;
  for (s = qr->pcnf.qblocks.first; s; s = s->link.next)
    {
      if (s->link.next)
        {
          assert (s->nesting + 1 == s->link.next->nesting);
          assert (s->type != s->link.next->type);
        }
    }
}
#endif

/* -------------------- END: SETUP -------------------- */

/* -------------------- START: PUBLIC FUNCTIONS -------------------- */

QRATPrePlus *
qratpreplus_create ()
{
  /* Initialize simple memory manager. */
  MemMan *mm = mm_create ();
  QRATPrePlus * qr = mm_malloc (mm, sizeof (QRATPrePlus));
  qr->mm = mm;
  set_default_options (qr);
  qr->start_time = time_stamp ();
  return qr;
}

void
qratpreplus_delete (QRATPrePlus * qr)
{
  /* Clean up, free memory and exit. */
  cleanup (qr);
  MemMan *mm = qr->mm;
  mm_free (mm, qr, sizeof (*qr));
  mm_delete (mm);
}

/* Returns null pointer after success and a pointer to an error string
   otherwise. */
char *
qratpreplus_configure (QRATPrePlus * qr, char *opt_str)
{
  char *result = 0;

  if (!strcmp (opt_str, "--no-qbce"))
    {
      qr->options.no_qbce = 1;
    }
  else if (!strcmp (opt_str, "--ignore-outermost-vars"))
    {
      qr->options.ignore_outermost_vars = 1;
    }
  else if (!strcmp (opt_str, "--no-qrate"))
    {
      qr->options.no_qrate = 1;
    }
  else if (!strcmp (opt_str, "--no-eabs"))
    {
      qr->options.no_eabs = 1;
    }
  else if (!strcmp (opt_str, "--no-eabs-improved-nesting"))
    {
      qr->options.no_eabs_improved_nesting = 1;
    }
  else if (!strcmp (opt_str, "--formula-stats"))
    {
      qr->options.formula_stats = 1;
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
        {
          qr->options.seed = atoi (opt_str);
        }
      else
        result = "Expecting number after '--seed='";
    }
  else if (!strcmp (opt_str, "--no-qat"))
    {
      qr->options.no_qat = 1;
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
    else
      {
        print_abort_err ("unknown option '%s'!\n\n", opt_str);
      }

  return result;  
}

/* Print (simplified) formula to file 'out'. */
void
qratpreplus_print_formula (QRATPrePlus * qr, FILE * out)
{
  ABORT_APP (qr->opened_qblock, "Open qblock -- cannot print formula, must close qblock first");

  /* Must unlink redundant clauses first, as this might not always be
     done in main loop, depending on schedule. */
  unlink_redundant_clauses (qr);
  
  assert (qr->actual_num_clauses >= qr->cnt_redundant_clauses);
  assert (qr->actual_num_clauses - qr->cnt_redundant_clauses == qr->pcnf.clauses.cnt);
  
  if (qr->parsed_empty_clause)
    {
      fprintf (out, "p cnf 0 1\n");
      fprintf (out, "0\n");
      return;
    }
  
  /* Handle cases were no formula was added or all clauses became redundant. */
  if (qr->pcnf.size_vars == 0 || !formula_has_non_redundant_clauses (qr))
    {
      fprintf (out, "p cnf 0 0\n");
      return;
    }
  
  /* Print preamble. */
  fprintf (out, "p cnf %d %d\n", (qr->pcnf.size_vars - 1),
           qr->pcnf.clauses.cnt/*(qr->actual_num_clauses - qr->cnt_redundant_clauses)*/);

  /* Print prefix. */
  QBlock *s;
  for (s = qr->pcnf.qblocks.first; s; s = s->link.next)
    print_qblock (qr, s, out);

  /* Print clauses. */
  Clause *c;
  for (c = qr->pcnf.clauses.first; c; c = c->link.next)
    if (!c->redundant)
      print_lits (qr, out, c->lits, c->num_lits, 0);
}

void
qratpreplus_print_stats (QRATPrePlus *qr, FILE *file)
{
  /* Must unlink redundant clauses first, as this might not always be
     done in main loop, depending on schedule and exceeded time limits. */
  unlink_redundant_clauses (qr);
  /* Cleanup empty qblocks and merge qblocks of the same type. This is
     done to get accurate counts of alternations after preprocessing. */
  clean_up_empty_qblocks (qr);

  /* Compute statistics after cleaning up formula. */
  if (qr->options.formula_stats)
    {
      qr->formula_stats.after_num_qblocks =
        qr->pcnf.qblocks.last ? qr->pcnf.qblocks.last->nesting + 1 : 0;
      qr->formula_stats.after_num_clauses = qr->pcnf.clauses.cnt;
      qr->formula_stats.after_num_univ_lits =
        count_qtype_literals_in_formula (qr, QTYPE_FORALL);
      qr->formula_stats.after_num_exist_lits =
        count_qtype_literals_in_formula (qr, QTYPE_EXISTS);      
    }
  
  /* Print statistics. */
  fprintf (file, "\nDONE, printing statistics:\n");
  if (!qr->options.max_time)
    fprintf (file, "  time limit: not set\n");
  else
    fprintf (file, "  time limit: %d\n", qr->options.max_time);

  if (!qr->soft_time_limit)
    fprintf (file, "  soft time limit: not set\n");
  else
    fprintf (file, "  soft time limit: %d (time exceeded: %s)\n", qr->soft_time_limit, qr->time_exceeded ? "yes" : "no");
      
  fprintf (file, "  Global iterations: %d\n", qr->cnt_global_iterations);
  fprintf (file, "  CE iterations: %d\n", qr->cnt_qbce_iterations);
  fprintf (file, "  CE checks: %llu ( %f %% of initial CNF)\n", 
           qr->cnt_qbce_checks, qr->actual_num_clauses ? 
           ((qr->cnt_qbce_checks / (float)qr->actual_num_clauses) * 100) : 0);
  fprintf (file, "  CE: %d redundant clauses of total %d clauses ( %f %% of initial CNF)\n",
           qr->cnt_redundant_clauses, qr->actual_num_clauses, qr->actual_num_clauses ? 
           ((qr->cnt_redundant_clauses / (float)qr->actual_num_clauses) * 100) : 0);
  fprintf (file, "  QRAT propagations: total %llu avg. %f per check, total %llu checks of outer res.\n", 
           qr->qbcp_total_props, qr->qrat_qbcp_checks ? (float)qr->qbcp_total_props /  qr->qrat_qbcp_checks : 0, qr->qrat_qbcp_checks);
  fprintf (file, "  QRAT success. propagations: total %llu avg. %f per check, total %llu checks of outer res.\n", 
           qr->qbcp_successful_checks_props, qr->qrat_qbcp_successful_checks ? (float)qr->qbcp_successful_checks_props /  
           qr->qrat_qbcp_successful_checks : 0, qr->qrat_qbcp_successful_checks);

  fprintf (file, "  QRAT  propagation limit reached: %u times in total %llu checks, with limit set to %u\n", 
           qr->limit_qbcp_cur_props_reached, qr->qrat_qbcp_checks, qr->limit_qbcp_cur_props);
  fprintf (file, "  Occ. count: max %u avg %f per used var, total %u used vars\n", qr->max_occ_cnt, 
           qr->actual_num_vars ? qr->total_occ_cnts / (float)qr->actual_num_vars : 0, qr->actual_num_vars);
  fprintf (file, "  Clause length: max %u avg %f per clause, total %u clauses\n", qr->max_clause_length, 
           qr->pcnf.clauses.cnt ? qr->total_clause_lengths / (float)qr->pcnf.clauses.cnt : 0, qr->pcnf.clauses.cnt);   
  fprintf (file, "  QBCP total calls %llu %s using EABS with avg abs-nesting %f max nesting %u\n", 
           qr->qbcp_total_calls, !qr->options.no_eabs ? "" : "not", !qr->options.no_eabs ? 
           (qr->qbcp_total_calls ? (qr->qbcp_total_eabs_nestings / (float)qr->qbcp_total_calls) : 0) : 
           UINT_MAX, qr->pcnf.qblocks.last ? qr->pcnf.qblocks.last->nesting : UINT_MAX);
  fprintf (file, "  QBCP total assignments %llu avg %f %% per QBCP call\n", qr->total_assignments,  
           qr->qbcp_total_calls ? (qr->total_assignments / (float)qr->qbcp_total_calls) : 0);

  fprintf (file, "  CE total OR checks %llu avg OR checks per CE check %f total lits seen %llu avg lits seen per OR check %f\n", 
           qr->clause_redundancy_or_checks, qr->cnt_qbce_checks ? (qr->clause_redundancy_or_checks / (float)qr->cnt_qbce_checks) : 0, 
           qr->clause_redundancy_or_checks_lits_seen, qr->clause_redundancy_or_checks ? 
           (qr->clause_redundancy_or_checks_lits_seen / (float)qr->clause_redundancy_or_checks) : 0);
      
  fprintf (file, "  QRATU iterations: %d\n", qr->cnt_qratu_iterations);
  fprintf (file, "  QRATU checks: %llu ( %f %% of initial CNF)\n", 
           qr->cnt_qratu_checks, qr->actual_num_clauses ? 
           ((qr->cnt_qratu_checks / (float)qr->actual_num_clauses) * 100) : 0);
  fprintf (file, "  QRATU: %d redundant literals of %llu total univ lits ( %f %% in initial formula)\n", 
           qr->cnt_redundant_literals, qr->total_univ_lits, qr->total_univ_lits ? 
           100 * (qr->cnt_redundant_literals / ((float) qr->total_univ_lits)) : 0);
      
  fprintf (file, "  run time: %f\n", time_stamp () - qr->start_time);

  if (qr->options.formula_stats)
    {
      fprintf (file, "\n");
      fprintf (file, "formula statistics num clauses after/before: %u %u ratio %f\n",
               qr->formula_stats.after_num_clauses, qr->formula_stats.before_num_clauses,
               qr->formula_stats.before_num_clauses ? (qr->formula_stats.after_num_clauses /
                                                       (float) qr->formula_stats.before_num_clauses) : 0);

      fprintf (file, "formula statistics num qblocks after/before: %u %u ratio %f\n",
               qr->formula_stats.after_num_qblocks, qr->formula_stats.before_num_qblocks,
               qr->formula_stats.before_num_qblocks ? (qr->formula_stats.after_num_qblocks /
                                                       (float) qr->formula_stats.before_num_qblocks) : 0);

      fprintf (file, "formula statistics num exist lits after/before: %u %u ratio %f\n",
               qr->formula_stats.after_num_exist_lits, qr->formula_stats.before_num_exist_lits,
               qr->formula_stats.before_num_exist_lits ? (qr->formula_stats.after_num_exist_lits /
                                                      (float) qr->formula_stats.before_num_exist_lits) : 0);

      fprintf (file, "formula statistics num univ lits after/before: %u %u ratio %f\n",
               qr->formula_stats.after_num_univ_lits, qr->formula_stats.before_num_univ_lits,
               qr->formula_stats.before_num_univ_lits ? (qr->formula_stats.after_num_univ_lits /
                                                         (float) qr->formula_stats.before_num_univ_lits) : 0);
    }
}

void
qratpreplus_declare_max_var_id (QRATPrePlus *qr, int num)
{
  ABORT_APP (qr->preprocessing_called, "Must not declare maximum variable after preprocessing!");
  ABORT_APP (num < 0, "Number of variables must not be negative!");
  ABORT_APP (qr->pcnf.size_vars, "Maximum variable ID must not be declared more than once!");
  ABORT_APP (qr->pcnf.vars, "Maximum variable ID must not be declared more than once!");
  set_up_var_table (qr, num);
}

/* Return maximum ID of a variable in the formula. This value need not
   be accurate, i.e., it might not take into account variables that have
   no occurrences left. */
int
qratpreplus_get_max_var_id (QRATPrePlus *qr)
{
  ABORT_APP (qr->pcnf.size_vars <= 0, "unexpected zero size of variable table");
  return qr->pcnf.size_vars - 1;
}

void
qratpreplus_new_qblock (QRATPrePlus *qr, int qtype)
{
  ABORT_APP (qr->preprocessing_called, "Must not modify formula after preprocessing!");
  ABORT_APP (qtype == 0, "Quantifier type must not be undefined!");
  open_new_qblock (qr, qtype < 0 ? QTYPE_EXISTS : QTYPE_FORALL);
}

void
qratpreplus_add_var_to_qblock (QRATPrePlus *qr, int var_id)
{
  ABORT_APP (qr->preprocessing_called, "Must not modify formula after preprocessing!");
  assert (qr->opened_qblock);
  assert (var_id >= 0);
  parse_literal (qr, var_id);
}

void
qratpreplus_add_literal (QRATPrePlus *qr, int lit)
{
  ABORT_APP (qr->preprocessing_called, "Must not modify formula after preprocessing!");
  /* There must NOT be an open qblock, otherwise the call of
     'parse_literal' will be interpreted as adding a block's literals */
  ABORT_APP (qr->opened_qblock, "Must not add clause's literals while there is still an open qblock");
  parse_literal (qr, lit);
}

void
qratpreplus_add_formula (QRATPrePlus *qr, char *in_filename)
{
  ABORT_APP (qr->preprocessing_called, "Must not modify formula after preprocessing!");
  if (in_filename)
    {
      if (!qr->options.in_filename)
        {
          qr->options.in_filename = in_filename;
          DIR *dir;
          if ((dir = opendir (qr->options.in_filename)) != NULL)
            {
              closedir (dir);
              print_abort_err ("input file '%s' is a directory!\n\n",
                               qr->options.in_filename);
            }
          FILE *input_file = fopen (qr->options.in_filename, "r");
          if (!input_file)
            print_abort_err ("could not open input file '%s'!\n\n",
                             qr->options.in_filename);
          else
            qr->options.in = input_file;
        }
      else
        print_abort_err ("Input file already given at '%s'!\n\n",
                         qr->options.in_filename);
    }
  else
    assert (qr->options.in == stdin);
  /* Parse and import formula in specified file. */
  parse_formula (qr, qr->options.in);
}

void
qratpreplus_preprocess (QRATPrePlus *qr)
{
  ABORT_APP (qr->preprocessing_called,
             "Must not preprocess more than once (library is not incremental)!");
  qr->preprocessing_called = 1;

  if (qr->options.formula_stats)
    {
      qr->formula_stats.before_num_qblocks =
        qr->pcnf.qblocks.last ? qr->pcnf.qblocks.last->nesting + 1 : 0;
      qr->formula_stats.before_num_clauses = qr->pcnf.clauses.cnt;
      qr->formula_stats.before_num_univ_lits =
        count_qtype_literals_in_formula (qr, QTYPE_FORALL);
      qr->formula_stats.before_num_exist_lits =
        count_qtype_literals_in_formula (qr, QTYPE_EXISTS);      
    }

  if (qr->options.max_time)
    {
      fprintf (stderr, "Setting run time limit of %d seconds\n",
               qr->options.max_time);
      alarm (qr->options.max_time);
    }
  
  if ((qr->time_exceeded = exceeded_soft_time_limit (qr)))
    fprintf (stderr, "Exceeded soft time limit of %u sec\n", qr->soft_time_limit);
  
#ifndef NDEBUG
  assert_formula_integrity (qr);
#endif

  if (!qr->time_exceeded &&
      (qr->time_exceeded = exceeded_soft_time_limit (qr)))
    fprintf (stderr, "Exceeded soft time limit of %u sec\n", qr->soft_time_limit);
  
  if (!qr->parsed_empty_clause)
    {
      int changed = 1;
      while (changed && !qr->time_exceeded)
        {
          if (qr->cnt_global_iterations >= qr->limit_global_iterations)
            {
              if (qr->options.verbosity >= 1)
                fprintf (stderr, "\nGlobal iteration limit %u reached, "\
                         "exiting simplification loop\n", qr->limit_global_iterations);
              break;
            }

          qr->cnt_global_iterations++;

          if (qr->options.verbosity >= 1)
            fprintf (stderr, "\n*********\nGlobal iteration: %u\n*********\n", 
                     qr->cnt_global_iterations);

          changed = 0;

          if (!qr->options.no_qbce || !qr->options.no_qat || 
              !qr->options.no_qrate)
            find_and_mark_redundant_clauses (qr);
          
          if ((qr->time_exceeded = exceeded_soft_time_limit (qr)))
            fprintf (stderr, "Exceeded soft time limit of %u sec\n", qr->soft_time_limit);

          /* Trigger a new iteration including clause redundancy checks if any
             redundant literals were found. */
          if (!qr->time_exceeded && (!qr->options.no_ble || !qr->options.no_qratu))
            changed = find_and_delete_redundant_literals (qr) || changed;

          if (!qr->time_exceeded &&
              (qr->time_exceeded = exceeded_soft_time_limit (qr)))
            fprintf (stderr, "Exceeded soft time limit of %u sec\n", qr->soft_time_limit);
        }
    }
}

/* Initialize clause iterator to first non-redundant clause in clause list. */
void
qratpreplus_cl_iter_init (QRATPrePlus *qr)
{
  qr->iter.cl_iter_p = qr->pcnf.clauses.first;
  while (qr->iter.cl_iter_p && qr->iter.cl_iter_p->redundant)
    qr->iter.cl_iter_p = qr->iter.cl_iter_p->link.next;
  assert (!qr->iter.cl_iter_p || !qr->iter.cl_iter_p->redundant);
}

/* Returns non-zero iff a following call of 'qratpreplus_cl_iter_next'
   will return a pointer to an array of literals of the next clause to be
   exported. */
int
qratpreplus_cl_iter_has_next (QRATPrePlus *qr)
{
  assert (!qr->iter.cl_iter_p || !qr->iter.cl_iter_p->redundant);
  return (qr->iter.cl_iter_p != 0);
}

/* Returns the number o literals in a clause that will be exported by
   a following call of 'qratpreplus_cl_iter_next'. If there is no
   clause to be exported next, then a negative value will be
   returned. */
int
qratpreplus_cl_iter_next_len (QRATPrePlus *qr)
{
  assert (!qr->iter.cl_iter_p || !qr->iter.cl_iter_p->redundant);
  if (!qr->iter.cl_iter_p)
    return -1;
  return qr->iter.cl_iter_p->num_lits;
}

/* Copy the literals of the next clause to be exported into array
   "to_lits". A pointer to "to_lits" is returned after success or null
   if there is no clause to be exported. The behavior is undefined if
   the size of "to_lits" is not sufficient to store all literals of
   the exported clause. The number of literals to be exported should
   be determined by "qratpreplus_cl_iter_next_len" first before
   calling this function, and sufficient space should be allocated in
   "to_lits" by the caller. Note that the number of literals returned
   by "qratpreplus_cl_iter_next_len" may be null for the empty clause,
   but still "to_lits" should be allocated by the user. */
int *
qratpreplus_cl_iter_next (QRATPrePlus *qr, int *to_lits)
{
  ABORT_APP (!to_lits, "Expecting a non-null literal array!");
  assert (!qr->iter.cl_iter_p || !qr->iter.cl_iter_p->redundant);

  if (!qr->iter.cl_iter_p)
    return 0;

  LitID *p, *e;
  int *to = to_lits;
  for (p = qr->iter.cl_iter_p->lits,
         e = p + qr->iter.cl_iter_p->num_lits; p < e; p++)
    *to++ = *p;

  do
    qr->iter.cl_iter_p = qr->iter.cl_iter_p->link.next;
  while (qr->iter.cl_iter_p && qr->iter.cl_iter_p->redundant);
  
  return to_lits;
}

void
qratpreplus_qbl_iter_init (QRATPrePlus *qr)
{
  qr->iter.qbl_iter_p = qr->pcnf.qblocks.first;
}

int
qratpreplus_qbl_iter_has_next (QRATPrePlus *qr)
{
  return (qr->iter.qbl_iter_p != 0);
}

int qratpreplus_qbl_iter_next_len (QRATPrePlus *qr)
{
  if (!qr->iter.qbl_iter_p)
    return -1;
  else
    return COUNT_STACK (qr->iter.qbl_iter_p->vars);
}

int *
qratpreplus_qbl_iter_get_vars (QRATPrePlus *qr, int *to_vars)
{
  ABORT_APP (!to_vars, "Expecting a non-null literal array!");

  if (!qr->iter.qbl_iter_p)
    return 0;

  LitID *p, *e;
  int cnt = COUNT_STACK (qr->iter.qbl_iter_p->vars);
  int *to = to_vars;
  for (p = (int *) qr->iter.qbl_iter_p->vars.start,
         e = p + cnt; p < e; p++)
    *to++ = *p;

  return to_vars;
}

int
qratpreplus_qbl_iter_next (QRATPrePlus *qr)
{
  if (qr->iter.qbl_iter_p)
    {
      QBlock *qbl = qr->iter.qbl_iter_p;
      qr->iter.qbl_iter_p = qr->iter.qbl_iter_p->link.next;
      if (qbl->type == QTYPE_EXISTS)
        return -1;
      else if (qbl->type == QTYPE_FORALL)
        return 1;
      else
        ABORT_APP (1, "Undefined quantifier type!");
    }
  else
    return 0;
}

/* -------------------- END: PUBLIC FUNCTIONS -------------------- */
