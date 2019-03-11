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

#ifndef QRATPREPLUS_UTIL_H_INCLUDED
#define QRATPREPLUS_UTIL_H_INCLUDED

#include <stdlib.h>
#include "qratpreplus_internals.h"

/* Macro to print message and abort. */
#define ABORT_APP(cond,msg)						 \
  do {                                                                   \
    if (cond)                                                            \
      {                                                                  \
        fprintf (stderr, "[QRATPREPLUS] %s at line %d: %s\n", __func__, \
                 __LINE__, msg);                                         \
        fflush (stderr);                                                 \
        abort();                                                         \
      }                                                                  \
  } while (0)

/* Print error message. */
void print_abort_err (char *msg, ...);

/* Print array 'lits' of literals of length 'num'. If 'print_info' is
non-zero, then print info about the qblock of each literal in the array. */
void print_lits (QRATPrePlus * qr,
		 FILE * out,
		 LitID * lits,
		 unsigned int num,
		 const int print_info);

/* Get process time. Can be used for performance statistics. */
double time_stamp ();

int exceeded_soft_time_limit (QRATPrePlus * qr);

unsigned int count_qtype_literals (QRATPrePlus * qr,
				   Clause * c,
				   QuantifierType type);

int find_literal (LitID lit, LitID * start, LitID * end);

void assert_lits_sorted (QRATPrePlus *, LitID *, LitID *);


#endif
