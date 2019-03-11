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


#ifndef QRATPREPLUS_H_INCLUDED
#define QRATPREPLUS_H_INCLUDED

#include <stdio.h>

typedef struct QRATPrePlus QRATPrePlus;

QRATPrePlus * qratpreplus_create ();

void qratpreplus_delete (QRATPrePlus *);

char * qratpreplus_configure (QRATPrePlus *, char *);

void qratpreplus_print_formula (QRATPrePlus *, FILE *);

void qratpreplus_print_stats (QRATPrePlus *, FILE *);

void qratpreplus_declare_max_var_id (QRATPrePlus *, int);

int qratpreplus_get_max_var_id (QRATPrePlus *);

void qratpreplus_new_qblock (QRATPrePlus *, int);

void qratpreplus_add_var_to_qblock (QRATPrePlus *, int);

void qratpreplus_add_literal (QRATPrePlus *, int);

void qratpreplus_add_formula (QRATPrePlus *, char *);

void qratpreplus_preprocess (QRATPrePlus *);

/* Iterator to export clauses. */

/* Export clauses: initialize iterator to first element of clause list.  */
void qratpreplus_cl_iter_init (QRATPrePlus *);

/* Export clauses: returns non-zero if there is a next clause to be exported. */
int qratpreplus_cl_iter_has_next (QRATPrePlus *);

int qratpreplus_cl_iter_next_len (QRATPrePlus *qr);

/* Export clauses: returns pointer to lit-array of clauses, terminate
   by zero.  */
int * qratpreplus_cl_iter_next (QRATPrePlus *, int *);

/* Iterator to export quantifier blocks and variables. */

void qratpreplus_qbl_iter_init (QRATPrePlus *);

int qratpreplus_qbl_iter_has_next (QRATPrePlus *);

int qratpreplus_qbl_iter_next_len (QRATPrePlus *qr);

int * qratpreplus_qbl_iter_get_vars (QRATPrePlus *qr, int *to_vars);

int qratpreplus_qbl_iter_next (QRATPrePlus *);

#endif
