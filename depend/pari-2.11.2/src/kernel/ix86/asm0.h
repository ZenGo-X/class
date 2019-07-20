#line 2 "../src/kernel/ix86/asm0.h"
/* Copyright (C) 2000  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/* This file defines some "level 0" kernel functions for Intel ix86  */
/* It is intended for use with an external "asm" definition          */

/*
ASM addll mulll bfffo divll
*/
#ifdef ASMINLINE
/* Written by Bruno Haible, 1996-1998.
   addllx8/subllx8 by Bill Allombert, 2011.
*/

/* This file can assume the GNU C extensions.
   (It is included only if __GNUC__ is defined.) */

/* Use local variables whenever possible. */
#define LOCAL_HIREMAINDER  register ulong hiremainder
#define LOCAL_OVERFLOW     register ulong overflow

#define addll(a,b) \
__extension__ ({ ulong __value, __arg1 = (a), __arg2 = (b); \
   __asm__ ("addl %3,%0 ; adcl %1,%1" \
        : "=r" (__value), "=r" (overflow) \
        : "0" (__arg1), "g" (__arg2), "1" ((ulong)0) \
        : "cc"); \
  __value; \
})

#define addllx(a,b) \
__extension__ ({ ulong __value, __arg1 = (a), __arg2 = (b), __temp; \
   __asm__ ("subl %5,%2 ; adcl %4,%0 ; adcl %1,%1" \
        : "=r" (__value), "=&r" (overflow), "=&r" (__temp) \
        : "0" (__arg1), "g" (__arg2), "g" (overflow), "1" ((ulong)0), "2" ((ulong)0) \
        : "cc"); \
  __value; \
})

#define addllx8(a,b,c,overflow) \
do { long *__arg1 = a, *__arg2 = b, *__out = c; \
     ulong __temp; \
   __asm__ ("subl %5, %0 \n\t" \
            "movl    (%2), %0 ; adcl    (%3),%0; movl %0,    (%4) \n\t" \
            "movl  -4(%2), %0 ; adcl  -4(%3),%0; movl %0,  -4(%4) \n\t" \
            "movl  -8(%2), %0 ; adcl  -8(%3),%0; movl %0,  -8(%4) \n\t" \
            "movl -12(%2), %0 ; adcl -12(%3),%0; movl %0, -12(%4) \n\t" \
            "movl -16(%2), %0 ; adcl -16(%3),%0; movl %0, -16(%4) \n\t" \
            "movl -20(%2), %0 ; adcl -20(%3),%0; movl %0, -20(%4) \n\t" \
            "movl -24(%2), %0 ; adcl -24(%3),%0; movl %0, -24(%4) \n\t" \
            "movl -28(%2), %0 ; adcl -28(%3),%0; movl %0, -28(%4) \n\t" \
            "adcl  %1, %1" \
        : "=&r" (__temp), "=&r" (overflow) \
        : "r" (__arg1), "r" (__arg2), "r" (__out), "g" (overflow), "0" ((ulong)0), "1" ((ulong)0)        : "cc"); \
} while(0)

#define subll(a,b) \
__extension__ ({ ulong __value, __arg1 = (a), __arg2 = (b); \
   __asm__ ("subl %3,%0 ; adcl %1,%1" \
        : "=r" (__value), "=r" (overflow) \
        : "0" (__arg1), "g" (__arg2), "1" ((ulong)0) \
        : "cc"); \
  __value; \
})

#define subllx(a,b) \
__extension__ ({ ulong __value, __arg1 = (a), __arg2 = (b), __temp; \
   __asm__ ("subl %5,%2 ; sbbl %4,%0 ; adcl %1,%1" \
        : "=r" (__value), "=&r" (overflow), "=&r" (__temp) \
        : "0" (__arg1), "g" (__arg2), "g" (overflow), "1" ((ulong)0), "2" ((ulong)0) \
        : "cc"); \
  __value; \
})

#define subllx8(a,b,c,overflow) \
do { long *__arg1 = a, *__arg2 = b, *__out = c; \
     ulong __temp; \
   __asm__ ("subl %5, %0 \n\t" \
            "movl    (%2), %0 ; sbbl    (%3),%0; movl %0,    (%4) \n\t" \
            "movl  -4(%2), %0 ; sbbl  -4(%3),%0; movl %0,  -4(%4) \n\t" \
            "movl  -8(%2), %0 ; sbbl  -8(%3),%0; movl %0,  -8(%4) \n\t" \
            "movl -12(%2), %0 ; sbbl -12(%3),%0; movl %0, -12(%4) \n\t" \
            "movl -16(%2), %0 ; sbbl -16(%3),%0; movl %0, -16(%4) \n\t" \
            "movl -20(%2), %0 ; sbbl -20(%3),%0; movl %0, -20(%4) \n\t" \
            "movl -24(%2), %0 ; sbbl -24(%3),%0; movl %0, -24(%4) \n\t" \
            "movl -28(%2), %0 ; sbbl -28(%3),%0; movl %0, -28(%4) \n\t" \
            "adcl  %1, %1" \
        : "=&r" (__temp), "=&r" (overflow) \
        : "r" (__arg1), "r" (__arg2), "r" (__out), "g" (overflow), "0" ((ulong)0), "1" ((ulong)0)        : "cc"); \
} while(0)


#define mulll(a,b) \
__extension__ ({ ulong __valuelo, __arg1 = (a), __arg2 = (b); \
   __asm__ ("mull %3" \
        : "=a" /* %eax */ (__valuelo), "=d" /* %edx */ (hiremainder) \
        : "0" (__arg1), "rm" (__arg2)); \
   __valuelo; \
})

#define addmul(a,b) \
__extension__ ({ ulong __valuelo, __arg1 = (a), __arg2 = (b), __temp; \
   __asm__ ("mull %4 ; addl %5,%0 ; adcl %6,%1" \
        : "=a" /* %eax */ (__valuelo), "=&d" /* %edx */ (hiremainder), "=r" (__temp) \
        : "0" (__arg1), "rm" (__arg2), "g" (hiremainder), "2" ((ulong)0)); \
   __valuelo; \
})

#define divll(a,b) \
__extension__ ({ ulong __value, __arg1 = (a), __arg2 = (b); \
   __asm__ ("divl %4" \
        : "=a" /* %eax */ (__value), "=d" /* %edx */ (hiremainder) \
        : "0" /* %eax */ (__arg1), "1" /* %edx */ (hiremainder), "mr" (__arg2)); \
   __value; \
})

#define bfffo(x) \
__extension__ ({ ulong __arg = (x); \
   int leading_one_position; \
  __asm__ ("bsrl %1,%0" : "=r" (leading_one_position) : "rm" (__arg)); \
  31 - leading_one_position; \
})

#endif
