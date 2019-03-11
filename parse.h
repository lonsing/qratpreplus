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

#ifndef QRATPREPLUS_PARSE_H_INCLUDED
#define QRATPREPLUS_PARSE_H_INCLUDED

#include <stdio.h>
#include "qratpreplus.h"

/* Merge and remove adjacent qblocks of the same quantifier type. */
void merge_adjacent_same_type_qblocks (QRATPrePlus * qr, int update_nestings);

void parse_formula (QRATPrePlus *, FILE *);

/* Collect parsed literals of a qblock or a clause on auxiliary stack to be
   imported and added to data structures later. */
void parse_literal (QRATPrePlus *, int);

/* Allocate a new qblock object and append it to the list of
   qblocks. Value '-1' indicates EXISTS, '1' FORALL, everything else
   undefined. */
void open_new_qblock (QRATPrePlus *, int);

/* Allocate table of variable IDs having fixed size. If the preamble
   of the QDIMACS file (or the user via the API) specifies a maximum
   variable ID which is smaller than the ID of a variable encountered
   in the formula, then the program aborts. */
void set_up_var_table (QRATPrePlus *, int);

#endif
