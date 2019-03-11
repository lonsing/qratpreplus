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
 along with qratplus.  If not, see <http://www.gnu.org/licenses/>.
*/

#ifndef QRATPLUS_PRE_H_INCLUDED
#define QRATPLUS_PRE_H_INCLUDED

#include <assert.h>
#include <stdio.h>
#include <limits.h>
#include "stack.h"

/* Generic macros to link and unlink elements from a doubly linked list.  */
#define LINK_LAST(anchor,element,link)		\
  do {						\
    assert (!(element)->link.prev);		\
    assert (!(element)->link.next);		\
    if ((anchor).last)				\
      {						\
        assert (!(anchor).last->link.next);	\
        assert ((anchor).first);                \
        assert (!(anchor).first->link.prev);	\
        (anchor).last->link.next = (element);	\
      }						\
    else                                        \
      {						\
        assert (!(anchor).first);		\
        (anchor).first = (element);		\
      }						\
    (element)->link.prev = (anchor).last;	\
    (anchor).last = (element);			\
    (anchor).cnt++;				\
  } while (0)

#define LINK_FIRST(anchor,element,link)		\
  do {						\
    assert (!(element)->link.prev);		\
    assert (!(element)->link.next);		\
    (element)->link.next = (anchor).first;	\
    if ((anchor).first)				\
      {						\
        assert ((anchor).last);			\
        (anchor).first->link.prev = (element);	\
      }						\
    else					\
      {						\
        assert (!(anchor).last);		\
        (anchor).last = (element);		\
      }						\
    (anchor).first = (element);			\
    (anchor).cnt++;				\
  } while (0)

#define UNLINK(anchor,element,link)				\
  do {								\
    assert ((anchor).cnt);					\
    if ((element)->link.prev)					\
      {								\
        assert ((anchor).first);                                \
        assert ((anchor).last);					\
        assert ((element)->link.prev->link.next == (element));	\
        (element)->link.prev->link.next = (element)->link.next; \
      }								\
    else                                                        \
      {								\
        assert ((anchor).first == (element));			\
        (anchor).first = (element)->link.next;			\
      }								\
    if ((element)->link.next)					\
      {								\
        assert ((anchor).first);                                \
        assert ((anchor).last);					\
        assert ((element)->link.next->link.prev == (element));	\
        (element)->link.next->link.prev = (element)->link.prev; \
      }								\
    else                                                        \
      {								\
        assert ((anchor).last == (element));			\
        (anchor).last = (element)->link.prev;			\
      }								\
    (element)->link.prev = (element)->link.next = 0;		\
    (anchor).cnt--;						\
  } while (0)

/* -------- START: PCNF data structures -------- */

typedef struct PCNF PCNF;
typedef struct Scope Scope;
typedef struct Var Var;
typedef struct Clause Clause;

typedef int LitID;
typedef unsigned int VarID;
typedef unsigned int ClauseID;
typedef unsigned int Nesting;

enum QuantifierType
{
  QTYPE_EXISTS = -1,
  QTYPE_UNDEF = 0,
  QTYPE_FORALL = 1
};

typedef enum QuantifierType QuantifierType;

enum Assignment
{
  ASSIGNMENT_FALSE = -1,
  ASSIGNMENT_UNDEF = 0,
  ASSIGNMENT_TRUE = 1
};

typedef enum Assignment Assignment;

/* Invalid index of watched literal in literal array of a clause. */
#define WATCHED_LIT_INVALID_INDEX UINT_MAX
/* Special value indicates that clause found satisfied during watched literal
   update. */
#define WATCHED_LIT_CLAUSE_SAT (UINT_MAX - 1)
/* Invalid index of occurrence on stack of occurrences. */
#define INVALID_OCC_INDEX UINT_MAX

#define DECLARE_DLIST(name, type)					\
  struct name ## List {type * first; type * last; unsigned int cnt;};	\
  typedef struct name ## List name ## List				\

#define DECLARE_DLINK(name, type)			  \
  struct name ## Link {type * prev; type * next;};        \
  typedef struct name ## Link name ## Link                \

/* Declare lists and stacks of Scopes, Clauses, etc. */
DECLARE_DLINK (Scope, Scope);
DECLARE_DLIST (Scope, Scope);
DECLARE_DLINK (Clause, Clause);
DECLARE_DLIST (Clause, Clause);

DECLARE_STACK (VarID, VarID);
DECLARE_STACK (LitID, LitID);
DECLARE_STACK (ClausePtr, Clause *);
DECLARE_STACK (VarPtr, Var *);

/* PCNF object, defined by list of scopes (quantifier prefix), array of
   variable objects (variable is indexed by its QDIMACS ID), and doubly linked
   list of clauses. */
struct PCNF
{
  ScopeList scopes;
  /* Size of var-table. */
  VarID size_vars;
  /* Table of variable objects indexed by unsigned integer ID. */
  Var *vars;
  ClauseList clauses;
};

/* Scope object (quantifier block in the quantifier prefix). */
struct Scope
{
  QuantifierType type;
  /* Scopes have nesting level, starting at 0, increases by one from left to
     right. */
  unsigned int nesting;
  /* IDs of variables in a scope are kept on a stack. */
  VarIDStack vars;
  /* Scopes appear in a doubly linked list. */
  ScopeLink link;
};

/* Variable object. */
struct Var
{
  /* ID of a variable is used as index to access the array of variable objects. */
  VarID id;
  /* Two multi-purpose marks. */
  unsigned int mark0:1;
  unsigned int mark1:1;
  /* Mark indicates if assigned variable has been propagated in
     QBCP. */
  unsigned int propagated:1;
  /* Mark indicates whether universal variable became pure either due to
     clause/literal elimination or because it was pure already in input
     formula. */
  unsigned int input_pure_collected:1;
  /* Stacks with pointers to clauses containing positive and negative literals
     of the variable. */
  ClausePtrStack neg_occ_clauses;
  ClausePtrStack pos_occ_clauses;
  /* Stacks with pointers to clauses containing WATCHED positive and negative
     literals of the variable. */
  ClausePtrStack watched_neg_occ_clauses;
  ClausePtrStack watched_pos_occ_clauses;

  /* Variable assignment in QBCP. */
  Assignment assignment;

  /* Pointer to scope of variable. */
  Scope *scope;
};

/* Clause object. */
struct Clause
{
  /* Clauses get a unique ID. This is mainly for debugging. */
  ClauseID id;
  /* Number of literals in a clause. */
  unsigned int num_lits;
  /* Initial number of literals in a clause for which space was
     allocated (universal reduction may eliminate literals). */
  unsigned int size_lits;

  /* Index (i.e., position in 'clause->lits') of current left/right watched
     literal. We assume that literals in clauses are sorted by quantifier
     ordering. The right watched literal is always an unassigned existential
     literal, the left one is unassigned and may be existential or
     universal. The value 'UINT_MAX' is used to indicate an invalid index. */
  unsigned int lw_index;
  unsigned int rw_index;

  /* For pure literals: count number of satisfying literals in clause. */
  unsigned int cnt_sat_lits;
  /* For pure literals: count number of universal literals in clause. */
  unsigned int cnt_univ_lits;

  /* Mark indicating that clause is redundant. */
  unsigned int redundant:1;
  /* Mark indicating that clause has been rescheduled for another redundancy
     check in the next iteration. */
  unsigned int rescheduled:1;
  /* Mark used to effectively remove clause from variable during
     QBCP. If mark is set then clause will not trigger unit implications
     or conflicts. */
  unsigned int ignore_in_qbcp:1;
  /* Mark indicating that clause is a witness for non-redundancy of some other
     clause. */
  unsigned int witness:1;
  /* When retracting assignments, must make sure to properly set right watcher
     to an existential literal, if that watcher was at a universal one during
     abstraction. Mark indicates that clause has been collected for update. */
  unsigned int lw_update_collected:1;

  /* Multi-purpose mark. */
  unsigned int mark:1;
  
  /* All  clauses are kept in a doubly linked list. */
  ClauseLink link;

  /* Flexible literal array. DO NOT ADD MEMBERS AFTER 'lits[]'! (violation of
     C99 standard). */
  LitID lits[];
};

/* Some helper macros. */

/* Check if literal is positive or negative. */
#define LIT_NEG(lit) ((lit) < 0)
#define LIT_POS(lit) (!LIT_NEG((lit)))

/* Convert literal to variable ID or to pointer to variable object. */
#define LIT2VARID(lit) ((lit) < 0 ? -(lit) : (lit))
#define LIT2VARPTR(vars, lit) ((vars) + LIT2VARID(lit))
#define LIT2VAR(vars, lit) ((vars)[LIT2VARID(lit)])

/* Convert variable ID to pointer to variable object. */
#define VARID2VARPTR(vars, id) ((vars) + (id))

/* Check if scope is existential or universal. */
#define SCOPE_EXISTS(s) ((s)->type == QTYPE_EXISTS)
#define SCOPE_FORALL(s) ((s)->type == QTYPE_FORALL)

/* Mark/unmark variable by (re-)setting its positive or negative mark. */
#define VAR_POS_MARK(v) ((v)->mark0 = 1)
#define VAR_NEG_MARK(v) ((v)->mark1 = 1)
#define VAR_UNMARK(v) ((v)->mark0 = (v)->mark1 = 0)
#define VAR_POS_MARKED(v) ((v)->mark0)
#define VAR_NEG_MARKED(v) ((v)->mark1)
#define VAR_MARKED(v) ((v)->mark0 || (v)->mark1)

/* -------- END: PCNF data structures -------- */

/* -------- START: Application defintions -------- */

/* QRATPlusPre object. This is used by the main application. */
struct QRATPlusPre
{
  /* PCNF object representing the parsed formula. */
  PCNF pcnf;
  /* Value of 'qr->eabs_nesting' controls the amount of propositional
     abstraction. Every variables from nesting levels <=
     'qr->eabs_nesting' is treating as existentially quantified. */
  Nesting eabs_nesting;
  /* Auxiliary variable for the computation of 'qr->eabs_nesting'. */
  Nesting eabs_nesting_aux;
  /* Simple memory manager. */
  MemMan *mm;
  /* Declared number of clauses in QDIMACS file. */
  unsigned int declared_num_clauses;
  /* Actual number of clauses in input formula (may be different from number
  declared in QDIMACS file due to e.g. removed tautologies). */
  unsigned int actual_num_clauses;
  /* Actual number of variables used in formula (may be different from number
  declared in QDIMACS file). */
  unsigned int actual_num_vars;
  /* Number of redundant clauses. */
  unsigned int cnt_redundant_clauses;
  /* Number of redundant literals. */
  unsigned int cnt_redundant_literals;
  /* Number of global iterations, i.e., iterations in the loop where clause
     and literal elimination is applied. */
  unsigned int cnt_global_iterations;
  /* Number of QBCE iterations. */
  unsigned int cnt_qbce_iterations;
  /* Number of QRATU iterations. */
  unsigned int cnt_qratu_iterations;
  /* Number of QBCE checks. */
  long long unsigned int cnt_qbce_checks;
  /* Number of QRATU checks. */
  long long unsigned int cnt_qratu_checks;
  /* Number of QRAT QBCP checks. */
  long long unsigned int qrat_qbcp_checks;
  /* Maximum propagations allowed in a check. */
  unsigned int limit_qbcp_cur_props;
  /* Number of times the maximum propagations were reached in a check. */
  unsigned int limit_qbcp_cur_props_reached;
  /* Number of clause propagations in QBCP in current clause check. */
  unsigned int qbcp_cur_props;
  /* Number of total clause propagations in QBCP in clause checks. */
  long long unsigned int qbcp_total_props;
  /* Number of propagations in successful QRAT checks. */
  long long unsigned int qbcp_successful_checks_props;
  /* Number of successful QRAT checks. */
  long long unsigned int qrat_qbcp_successful_checks;
  /* Assignment statistics. */
  long long unsigned int total_assignments;
  long long unsigned int total_pure_assignments;

  /* Maximum number of global iterations, initialized to UINT_MAX. */
  unsigned int limit_global_iterations;

  /* QBCP statistics. */
  long long unsigned int qbcp_total_eabs_nestings;
  long long unsigned int qbcp_total_calls;
  long long unsigned int pure_lits_cnt_update_calls;
  long long unsigned int pure_lits_occs_seen;

  /* Occurrence and clause statistics. */
  unsigned int max_occ_cnt;
  long long unsigned int total_occ_cnts;
  unsigned int max_clause_length;
  long long unsigned int total_clause_lengths;
  /* For QRATU statistics: number of universal literals in input formula. */
  long long unsigned int total_univ_lits;

  /* Number of outer resolvents checked for clause redundancy. */
  long long unsigned int clause_redundancy_or_checks;
  /* Number of literals tested in outer resolvents checked for clause red.. */
  long long unsigned int clause_redundancy_or_checks_lits_seen;
  
  /* Do not check redundancy of clauses if number of occurrences to be
     considered exceeds 'check_max_occ_cnt'. This limit restricts the number
     of outer resolvents considered. */
  unsigned int limit_max_occ_cnt;
  /* Do not check redundancy of clauses with MORE THAN 'check_max_clause_len'
     literals. This limit restricts the number of times we check for a QRAT
     literal. */
  unsigned int limit_max_clause_len;
  /* Do not check redundancy of clauses with LESS THAN 'check_min_clause_len'
     literals. E.g., we might want to never check whether a unit clause has
     QRAT. */
  unsigned int limit_min_clause_len;

  /* Soft time imit in seconds: abort preprocessing and print formula,
     ignore redundant clauses and literals found so far. */
  unsigned int soft_time_limit;
  
  /* Stack of literals or variable IDs read during parsing. */
  LitIDStack parsed_literals;
  /* Pointer to most recently opened scope during parsing. */
  Scope *opened_scope;
  /* Flag to indicate whether all scopes have been parsed. Used to
     start merging of adjacent scopes of the same quantifier type. */
  unsigned int parsing_prefix_completed:1;
  /* Every clause gets a unique ID (for debugging purposes). */
  ClauseID cur_clause_id;
  /* Auxiliary stack to store input unit clauses, used for QBCP. */
  ClausePtrStack unit_input_clauses;
  /* Auxiliary stack to store input pure literals, used for QBCP. */
  LitIDStack pure_input_lits;

  /* Auxiliary stack to store clauses which were found to be redundant. */
  ClausePtrStack redundant_clauses;
  /* Auxiliary stack to store clauses which were found to be a witness for the
     non-redundancy of some other clause in a round. */
  ClausePtrStack witness_clauses;

  /* When using abstraction: clauses collected for literal watcher update
     during backtracking. We must maintain the invariant that the right literal
     watcher always is at an existential literal. */
  ClausePtrStack lw_update_clauses;

  /* Start time of program. */
  double start_time;
  unsigned int parsed_empty_clause:1;

  /* Stack of assignments enqueued for propagation. */
  VarIDStack qbcp_queue;
    
  /* Options to be set via command line. */
  struct
  {
    char *in_filename;
    FILE *in;
    unsigned int max_time;
    unsigned int verbosity;
    unsigned int seed;
    unsigned int print_usage:1;
    unsigned int print_version:1;
    unsigned int no_qbce:1;
    unsigned int print_formula:1;
    /* Before QRAT tests, permute clause set randomly based on value of
       'seed'. Permuting can be used to test the impact of non-confluence of
       QRAT. Since QBCE is confluent, permuting is applied to the irredundant
       clause set that remains after QBCE has been applied. */
    unsigned int permute:1;
    /* Exploit scope ordering of literals in clauses to avoid visiting
       literals that only produce inadmissible inner tautologies in QBCE
       checks. */
    unsigned int qbce_check_taut_by_nesting:1;
    /* Check if clause is an asymmetric tautology by negating the
       clause and applying (Q)BCP (i.e., either full propositional or
       abstraction by nesting level of maximal literal in
       clause). This check is applied after QBCE and before QRAT. */
    unsigned int no_asymm_taut_check:1;
    /* Use existential abstraction with respect to currently
       propagated assignments. */
    unsigned int no_eabs:1;
    /* Elimination of clauses which have QRAT on existential literal. */
    unsigned int no_qrate:1;
    /* Elimination of univeral literal which have QRAT. */
    unsigned int no_qratu:1;
    /* Elimination of blocked univeral literals (i.e., checking if outer
       resolvent is tautology). */
    unsigned int no_ble:1;
    /* Detect universal pure literals in QBCP. */
    unsigned int pure_lits:1;
    /* After eliminating a clause containing universal literals, or if a
       universal literal became pure by clause elimination, DO reschedule ALL
       clauses to be checked again by AT and QRAT as this might be
       expensive. HOWEVER, clause elimination may not saturate. */
    unsigned int pure_lits_full_reschedule:1;
    /* For QRAT: when assigning variables from currently tested clause, do not
       assign variables that appear *inner* (i.e. '>' in ordering) to the
       pivot in prefix ordering. These inner literals will make abstraction to
       treat more variables as existential. Instead we abstract only up to the
       pivot, but also assign fewer literals then.
       TODO / CHECK: for QRATU the pivot is universal, and the pivot scope itself may
       also be abstracted as existential if the clause contains a literal from that
       scope. */
    unsigned int ignore_inner_lits:1;
    /* When using EABS, do not abstract the quantifier block B which contains
       the maximum assumption. Instead, abstract up to the block that is left
       of B. This way, we expect to have more universal variables in the
       abstracted formula, if the maximum assumption is universal. This is
       sound: if B is existential, then there is no difference in the
       abstraction compared to the standard approach anyhow. If B is universal
       then the maximum assumption is treated like a decision made after the
       outermost block of existential variables. */
    unsigned int no_eabs_improved_nesting:1;
  } options;
};

typedef struct QRATPlusPre QRATPlusPre;


/* Sorting Macros. */
/* Sorting: taken from Picosat. */
#define INTERNAL_SORTING_SWAP(T,p,q)		      \
  do {                                                \
    T tmp = *(q);				      \
    *(q) = *(p);				       \
    *(p) = tmp;                                        \
  } while (0)

#define INTERNAL_SORTING_CMPSWAP(Q, T,cmp,p,q)                \
  do {                                                        \
    if ((cmp) (Q, *(p), *(q)) > 0)                            \
      INTERNAL_SORTING_SWAP (T, p, q);                        \
  } while(0)

#define INTERNAL_INSERTION_SORT(Q,T,cmp,a,n)                            \
  do {									\
    T pivot;								\
    int l = 0, r = (n) - 1, i, j;					\
    for (i = r; i > l; i--)						\
      INTERNAL_SORTING_CMPSWAP (Q, T, cmp, (a) + i - 1, (a) + i);       \
    for (i = l + 2; i <= r; i++)                                        \
      {									\
        j = i;								\
        pivot = (a)[i];							\
        while ((cmp) (Q, pivot, (a)[j - 1]) < 0)                        \
          {								\
	    (a)[j] = (a)[j - 1];					\
	    j--;							\
          }								\
        (a)[j] = pivot;							\
      }									\
  } while (0)

#ifdef NDEBUG
#define CHECK_SORTED(Q,cmp,a,n) do { } while(0)
#else
#define CHECK_SORTED(Q,cmp,a,n)                                 \
  do {								\
    int i;							\
    for (i = 0; i < (n) - 1; i++)				\
      assert ((cmp) (Q, (a)[i], (a)[i + 1]) <= 0);              \
  } while(0)
#endif

#define SORT(Q,T,cmp,a,n)                                       \
  do {								\
    T * aa = (a);						\
    int nn = (n);						\
    INTERNAL_INSERTION_SORT (Q, T, cmp, aa, nn);                \
    CHECK_SORTED (Q, cmp, aa, nn);                              \
  } while (0)


#endif
