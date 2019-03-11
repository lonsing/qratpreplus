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

#ifndef QRATPREPLUS_MEM_H_INCLUDED
#define QRATPREPLUS_MEM_H_INCLUDED

#include <stddef.h>

typedef struct MemMan MemMan;

MemMan *mm_create ();

void mm_delete (MemMan * mm);

void *mm_malloc (MemMan * mm, size_t size);

void *mm_realloc (MemMan * mm, void *ptr, size_t old_size,
                     size_t new_size);

void mm_free (MemMan * mm, void *ptr, size_t size);

size_t mm_max_allocated (MemMan * mm);

size_t mm_cur_allocated (MemMan * mm);

void mm_set_mem_limit (MemMan * mm, size_t limit);

size_t mm_get_mem_limit (MemMan * mm);

#endif
