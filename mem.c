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

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <assert.h>
#include <stddef.h>
#include "mem.h"

struct MemMan
{
  size_t cur_allocated;
  size_t max_allocated;
  size_t limit;
};

#define ABORT_MEM(cond,msg)					\
  do {									\
    if (cond)								\
      {									\
        fprintf (stderr, "[mem_man] %s at line %d: %s\n", __func__,	\
		 __LINE__,msg);						\
	fflush (stderr);						\
        abort ();							\
      }									\
  } while (0)

/* -------------------- START: PUBLIC FUNCTIONS -------------------- */

MemMan *
mm_create ()
{
  MemMan *mm = (MemMan *) malloc (sizeof (MemMan));
  ABORT_MEM (!mm, "could not allocate memory!");
  memset (mm, 0, sizeof (MemMan));
  return mm;
}


void
mm_delete (MemMan * mm)
{
  ABORT_MEM (!mm, "null pointer encountered!");
  assert (mm->cur_allocated == 0);
  free (mm);
}


void *
mm_malloc (MemMan * mm, size_t size)
{
  /* Mem-limit is given in MB. */
  if (mm->limit && mm->limit < (mm->cur_allocated + size) / 1024 / 1024)
    {
      fprintf (stderr,
               "Attempted to allocate total %f MB (limit = %lu MB)\n",
               ((unsigned long) (mm->cur_allocated +
                                 size)) / 1024 / (float) 1024,
               (unsigned long) mm->limit);
      ABORT_MEM (1, "mem-limit exceeded!");
    }
  void *r = malloc (size);
  ABORT_MEM (!r, "could not allocate memory!");
  memset (r, 0, size);
  mm->cur_allocated += size;
  if (mm->cur_allocated > mm->max_allocated)
    mm->max_allocated = mm->cur_allocated;
  return r;
}


void *
mm_realloc (MemMan * mm, void *ptr, size_t old_size, size_t new_size)
{
  ptr = realloc (ptr, new_size);
  ABORT_MEM (!ptr, "could not allocate memory!");
  if (new_size > old_size)
    memset (((char *) ptr) + old_size, 0, new_size - old_size);
  mm->cur_allocated -= old_size;
  mm->cur_allocated += new_size;
  if (mm->cur_allocated > mm->max_allocated)
    mm->max_allocated = mm->cur_allocated;
  return ptr;
}


void
mm_free (MemMan * mm, void *ptr, size_t size)
{
  ABORT_MEM (!mm, "null pointer encountered!");
  free (ptr);
  mm->cur_allocated -= size;
}


size_t
mm_max_allocated (MemMan * mm)
{
  return mm->max_allocated;
}


size_t
mm_cur_allocated (MemMan * mm)
{
  return mm->cur_allocated;
}


void
mm_set_mem_limit (MemMan * mm, size_t limit)
{
  ABORT_MEM (limit <= 0, "mem-limit must be greater than 0!");
  mm->limit = limit;
}


size_t
mm_get_mem_limit (MemMan * mm)
{
  return mm->limit;
}

/* -------------------- END: PUBLIC FUNCTIONS -------------------- */
