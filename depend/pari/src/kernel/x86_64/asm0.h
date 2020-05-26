#line 2 "../src/kernel/x86-64/asm0.h"
/* Copyright (C) 2004  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/*
ASM addll mulll bfffo divll
*/
/* Written by Bill Allombert from the ix86 version by Bruno Haible. Basically
 * change insl to insq*/
#ifdef ASMINLINE
#define LOCAL_HIREMAINDER  register ulong hiremainder
#define LOCAL_OVERFLOW     register ulong overflow

#define addll(a,b) \
__extension__ ({ ulong __value, __arg1 = (a), __arg2 = (b); \
   __asm__ ("addq %3,%0 ; adcq %1,%1" \
        : "=r" (__value), "=r" (overflow) \
        : "0" (__arg1), "g" (__arg2), "1" ((ulong)0) \
        : "cc"); \
  __value; \
})

#define addllx(a,b) \
__extension__ ({ ulong __value, __arg1 = (a), __arg2 = (b), __temp; \
   __asm__ ("subq %5,%2 ; adcq %4,%0 ; adcq %1,%1" \
        : "=r" (__value), "=&r" (overflow), "=&r" (__temp) \
        : "0" (__arg1), "g" (__arg2), "g" (overflow), "1" ((ulong)0), "2" ((ulong)0) \
        : "cc"); \
  __value; \
})

#define addllx8(a,b,c,overflow) \
do { long *__arg1 = a, *__arg2 = b, *__out = c; \
     ulong __temp; \
   __asm__ ("subq %5, %0 \n\t" \
            "movq    (%2), %0 ; adcq    (%3),%0; movq %0,    (%4) \n\t" \
            "movq  -8(%2), %0 ; adcq  -8(%3),%0; movq %0,  -8(%4) \n\t" \
            "movq -16(%2), %0 ; adcq -16(%3),%0; movq %0, -16(%4) \n\t" \
            "movq -24(%2), %0 ; adcq -24(%3),%0; movq %0, -24(%4) \n\t" \
            "movq -32(%2), %0 ; adcq -32(%3),%0; movq %0, -32(%4) \n\t" \
            "movq -40(%2), %0 ; adcq -40(%3),%0; movq %0, -40(%4) \n\t" \
            "movq -48(%2), %0 ; adcq -48(%3),%0; movq %0, -48(%4) \n\t" \
            "movq -56(%2), %0 ; adcq -56(%3),%0; movq %0, -56(%4) \n\t" \
            "adcq  %1, %1" \
        : "=&r" (__temp), "=&r" (overflow) \
        : "r" (__arg1), "r" (__arg2), "r" (__out), "g" (overflow), "0" ((ulong)0), "1" ((ulong)0) \
        : "cc"); \
} while(0)

#define subll(a,b) \
__extension__ ({ ulong __value, __arg1 = (a), __arg2 = (b); \
   __asm__ ("subq %3,%0 ; adcq %1,%1" \
        : "=r" (__value), "=r" (overflow) \
        : "0" (__arg1), "g" (__arg2), "1" ((ulong)0) \
        : "cc"); \
  __value; \
})

#define subllx(a,b) \
__extension__ ({ ulong __value, __arg1 = (a), __arg2 = (b), __temp; \
   __asm__ ("subq %5,%2 ; sbbq %4,%0 ; adcq %1,%1" \
        : "=r" (__value), "=&r" (overflow), "=&r" (__temp) \
        : "0" (__arg1), "g" (__arg2), "g" (overflow), "1" ((ulong)0), "2" ((ulong)0) \
        : "cc"); \
  __value; \
})

#define subllx8(a,b,c,overflow) \
do { long *__arg1 = a, *__arg2 = b, *__out = c; \
     ulong __temp; \
   __asm__ ("subq %5, %0 \n\t" \
            "movq    (%2), %0 ; sbbq    (%3),%0; movq %0,    (%4) \n\t" \
            "movq  -8(%2), %0 ; sbbq  -8(%3),%0; movq %0,  -8(%4) \n\t" \
            "movq -16(%2), %0 ; sbbq -16(%3),%0; movq %0, -16(%4) \n\t" \
            "movq -24(%2), %0 ; sbbq -24(%3),%0; movq %0, -24(%4) \n\t" \
            "movq -32(%2), %0 ; sbbq -32(%3),%0; movq %0, -32(%4) \n\t" \
            "movq -40(%2), %0 ; sbbq -40(%3),%0; movq %0, -40(%4) \n\t" \
            "movq -48(%2), %0 ; sbbq -48(%3),%0; movq %0, -48(%4) \n\t" \
            "movq -56(%2), %0 ; sbbq -56(%3),%0; movq %0, -56(%4) \n\t" \
            "adcq  %1, %1" \
        : "=&r" (__temp), "=&r" (overflow) \
        : "r" (__arg1), "r" (__arg2), "r" (__out), "g" (overflow), "0" ((ulong)0), "1" ((ulong)0) \
        : "cc"); \
} while(0)

#define mulll(a,b) \
__extension__ ({ ulong __valuelo, __arg1 = (a), __arg2 = (b); \
   __asm__ ("mulq %3" \
        : "=a" /* %eax */ (__valuelo), "=d" /* %edx */ (hiremainder) \
        : "0" (__arg1), "rm" (__arg2)); \
   __valuelo; \
})

#define addmul(a,b) \
__extension__ ({ ulong __valuelo, __arg1 = (a), __arg2 = (b), __temp; \
   __asm__ ("mulq %4 ; addq %5,%0 ; adcq %6,%1" \
        : "=a" /* %eax */ (__valuelo), "=&d" /* %edx */ (hiremainder), "=r" (__temp) \
        : "0" (__arg1), "rm" (__arg2), "g" (hiremainder), "2" ((ulong)0)); \
   __valuelo; \
})

#define divll(a,b) \
__extension__ ({ ulong __value, __arg1 = (a), __arg2 = (b); \
   __asm__ ("divq %4" \
        : "=a" /* %eax */ (__value), "=d" /* %edx */ (hiremainder) \
        : "0" /* %eax */ (__arg1), "1" /* %edx */ (hiremainder), "mr" (__arg2)); \
   __value; \
})

#define bfffo(x) \
__extension__ ({ ulong __arg = (x); \
   long leading_one_position; \
  __asm__ ("bsrq %1,%0" : "=r" (leading_one_position) : "rm" (__arg)); \
  63 - leading_one_position; \
})
#endif
