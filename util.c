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

#include <stdarg.h>
#include <sys/resource.h>
#include "util.h"

/* Print error message. */
void
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
non-zero, then print info about the qblock of each literal in the array. */
void
print_lits (QRATPrePlus * qr, FILE * out, LitID * lits, unsigned int num,
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
                 QBLOCK_FORALL (var->qblock) ? 'A' : 'E',
                 var->qblock->nesting, *p);
      else
        fprintf (out, "%d ", *p);
    }
  fprintf (out, "0\n");
}

/* Get process time. Can be used for performance statistics. */
double
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

int
exceeded_soft_time_limit (QRATPrePlus * qr)
{
  if (qr->soft_time_limit &&
      (time_stamp () - qr->start_time) > qr->soft_time_limit)
    return 1;
  else
    return 0;
}

/* Returns number of literals in 'c' with quantifier type 'type'. */
unsigned int
count_qtype_literals (QRATPrePlus * qr, Clause * c, QuantifierType type)
{
  unsigned int result = 0;
  LitID *p, *e;
  for (p = c->lits, e = p + c->num_lits; p < e; p++)
    {
      LitID lit = *p;
      Var *var = LIT2VARPTR (qr->pcnf.vars, lit);
      if (var->qblock->type == type)
        result++;
    }
  return result;
}

int
find_literal (LitID lit, LitID * start, LitID * end)
{
  LitID *p;
  for (p = start; p < end; p++)
    if (*p == lit)
      return 1;
  return 0;
}

void
assert_lits_sorted (QRATPrePlus * qr, LitID * lit_start, LitID * lit_end)
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
      pvar_nesting = pvar->qblock->nesting;
      prev_var_nesting = prev_var->qblock->nesting;
      assert (prev_var_nesting <= pvar_nesting);
      prev = p;
    }
}
