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

#ifndef QRATPREPLUS_STACK_H_INCLUDED
#define QRATPREPLUS_STACK_H_INCLUDED

#include "mem.h"

#define DECLARE_STACK(name, type)					\
  typedef struct name ## Stack name ## Stack;				\
  struct name ## Stack { type * start; type * top; type * end; }

#define INIT_STACK(stack)			   \
  do {						   \
    (stack).start = (stack).top = (stack).end = 0; \
  } while (0)

#define ADJUST_STACK(mm,stack,size)				\
  do {									\
    size_t old_size;							\
    if ((size) > 0 && (old_size = SIZE_STACK(stack)) < (size))	\
      {									\
	size_t elem_bytes = sizeof(*(stack).start);			\
	size_t old_count = COUNT_STACK (stack);			\
	(stack).start = mm_realloc((mm), (stack).start,		\
				      old_size * elem_bytes,		\
				      (size) * elem_bytes);		\
	(stack).top = (stack).start + old_count;			\
	(stack).end = (stack).start + (size);				\
      }									\
  }while(0)								\

#define COUNT_STACK(stack) ((size_t) ((stack).top - (stack).start))
#define EMPTY_STACK(stack) ((stack).top == (stack).start)
#define RESET_STACK(stack) do { (stack).top = (stack).start; } while (0)

#define SIZE_STACK(stack) ((stack).end - (stack).start)
#define FULL_STACK(stack) ((stack).top == (stack).end)

#define DELETE_STACK(mm, stack)					\
  do {									\
    mm_free((mm), (stack).start,					\
	       SIZE_STACK(stack) * sizeof(*(stack).start));	\
    INIT_STACK ((stack));						\
  } while (0)

#define ENLARGE_STACK(mm, stack)					\
  do {									\
    size_t old_size = SIZE_STACK (stack), new_size;		\
    new_size = old_size ? 2 * old_size : 1;				\
    size_t old_count = COUNT_STACK (stack);			\
    size_t elem_bytes = sizeof(*(stack).start);				\
    (stack).start = mm_realloc((mm), (stack).start,			\
				  old_size*elem_bytes,			\
				  new_size*elem_bytes);			\
    (stack).top = (stack).start + old_count;				\
    (stack).end = (stack).start + new_size;				\
  } while (0)

#define PUSH_STACK(mm, stack, elem)	\
  do {						\
    if (FULL_STACK ((stack)))		\
      ENLARGE_STACK ((mm), (stack));	\
    *((stack).top++) = (elem);			\
  } while (0)

#define POP_STACK(stack) (*--(stack).top)

DECLARE_STACK (VoidPtr, void *);

#endif
