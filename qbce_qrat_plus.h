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
 along with qratplus.  If not, see <http://www.gnu.org/licenses/>.
*/

#ifndef QRATPREPLUS_QBCE_H_INCLUDED
#define QRATPREPLUS_QBCE_H_INCLUDED

#include "qratpreplus.h"

/* Returns nonzero iff redundant clauses were found. */
int find_and_mark_redundant_clauses (QRATPrePlus * qr);

/* Returns nonzero iff redundant literals were found. */
int find_and_delete_redundant_literals (QRATPrePlus * qr);

void unlink_redundant_clauses (QRATPrePlus * qr);


#endif
