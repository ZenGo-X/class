#line 2 "../src/kernel/aarch64/asm0.h"
/* Copyright (C) 2015  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/*
ASM addll mulll bfffo
NOASM divll
*/

#ifdef ASMINLINE
#define LOCAL_HIREMAINDER  register ulong hiremainder
#define LOCAL_OVERFLOW     register ulong overflow

#define addll(a, b) \
__extension__ ({ ulong __value, __arg1 = (a), __arg2 = (b); \
 __asm__ ("adds %0,%2,%3\n\tadc %1,xzr,xzr\n\t" \
   : "=&r" (__value), "=&r" (overflow) \
   : "r" (__arg1), "r" (__arg2): "cc"); \
 __value; \
})

#define addllx(a, b) \
__extension__ ({ ulong __value, __arg1 = (a), __arg2 = (b); \
 __asm__ ("subs xzr,%4,#1\n\tadcs %0,%2,%3\n\tadc %1,xzr,xzr\n\t" \
   : "=&r" (__value), "=&r" (overflow) \
   : "r" (__arg1), "r" (__arg2), "r" (overflow): "cc"); \
 __value; \
})

#define addllx8(a,b,c,overflow) \
do { long *__arg1 = a, *__arg2 = b, *__out = c; \
     ulong __temp1, __temp2; \
     __asm__( \
"subs xzr,%6,#1\n\t" \
" ldr %0, [%3]     \n\t ldr %1, [%4]    \n\t adcs %1, %0, %1\n\t str %1, [%5]    \n\t" \
" ldr %0, [%3,-8]  \n\t ldr %1, [%4,-8] \n\t adcs %1, %0, %1\n\t str %1, [%5,-8] \n\t" \
" ldr %0, [%3,-16] \n\t ldr %1, [%4,-16]\n\t adcs %1, %0, %1\n\t str %1, [%5,-16]\n\t" \
" ldr %0, [%3,-24] \n\t ldr %1, [%4,-24]\n\t adcs %1, %0, %1\n\t str %1, [%5,-24]\n\t" \
" ldr %0, [%3,-32] \n\t ldr %1, [%4,-32]\n\t adcs %1, %0, %1\n\t str %1, [%5,-32]\n\t" \
" ldr %0, [%3,-40] \n\t ldr %1, [%4,-40]\n\t adcs %1, %0, %1\n\t str %1, [%5,-40]\n\t" \
" ldr %0, [%3,-48] \n\t ldr %1, [%4,-48]\n\t adcs %1, %0, %1\n\t str %1, [%5,-48]\n\t" \
" ldr %0, [%3,-56] \n\t ldr %1, [%4,-56]\n\t adcs %1, %0, %1\n\t str %1, [%5,-56]\n\t" \
"adc %2,xzr,xzr\n\t" \
        : "=&r" (__temp1), "=&r" (__temp2), "=&r" (overflow) \
        : "r" (__arg1), "r" (__arg2), "r" (__out), "r" (overflow), \
          "0" ((ulong)0), "1" ((ulong)0) \
        : "cc"); \
} while(0)

#define subll(a, b) \
__extension__ ({ ulong __value, __arg1 = (a), __arg2 = (b); \
 __asm__ ("subs %0,%2,%3\n\tngc %1,xzr\n\tsub %1,xzr,%1\n\t" \
   : "=&r" (__value), "=&r" (overflow) \
   : "r" (__arg1), "r" (__arg2): "cc"); \
 __value; \
})

#define subllx(a, b) \
__extension__ ({ ulong __value, __arg1 = (a), __arg2 = (b); \
 __asm__ ("subs xzr,xzr,%4\n\tsbcs %0,%2,%3\n\tngc %1,xzr\n\tsub %1,xzr,%1\n\t" \
   : "=&r" (__value), "=&r" (overflow) \
   : "r" (__arg1), "r" (__arg2), "r" (overflow): "cc"); \
 __value; \
})

#define subllx8(a,b,c,overflow) \
do { long *__arg1 = a, *__arg2 = b, *__out = c; \
     ulong __temp1, __temp2; \
     __asm__( \
"subs xzr,xzr,%6\n\t" \
" ldr %0, [%3]     \n\t ldr %1, [%4]    \n\t sbcs %1, %0, %1\n\t str %1, [%5]    \n\t" \
" ldr %0, [%3,-8]  \n\t ldr %1, [%4,-8] \n\t sbcs %1, %0, %1\n\t str %1, [%5,-8] \n\t" \
" ldr %0, [%3,-16] \n\t ldr %1, [%4,-16]\n\t sbcs %1, %0, %1\n\t str %1, [%5,-16]\n\t" \
" ldr %0, [%3,-24] \n\t ldr %1, [%4,-24]\n\t sbcs %1, %0, %1\n\t str %1, [%5,-24]\n\t" \
" ldr %0, [%3,-32] \n\t ldr %1, [%4,-32]\n\t sbcs %1, %0, %1\n\t str %1, [%5,-32]\n\t" \
" ldr %0, [%3,-40] \n\t ldr %1, [%4,-40]\n\t sbcs %1, %0, %1\n\t str %1, [%5,-40]\n\t" \
" ldr %0, [%3,-48] \n\t ldr %1, [%4,-48]\n\t sbcs %1, %0, %1\n\t str %1, [%5,-48]\n\t" \
" ldr %0, [%3,-56] \n\t ldr %1, [%4,-56]\n\t sbcs %1, %0, %1\n\t str %1, [%5,-56]\n\t" \
"ngc %2,xzr\n\tsub %2,xzr,%2\n\t" \
        : "=&r" (__temp1), "=&r" (__temp2), "=&r" (overflow) \
        : "r" (__arg1), "r" (__arg2), "r" (__out), "r" (overflow), \
          "0" ((ulong)0), "1" ((ulong)0) \
        : "cc"); \
} while(0)

#define mulll(a, b) \
__extension__ ({ ulong __value, __arg1 = (a), __arg2 = (b); \
 __asm__ ("mul %0,%1,%2\n\t" \
   : "=r" (__value) : "r" (__arg1), "r" (__arg2)); \
 __asm__ ("umulh %0,%1,%2\n\t" \
   : "=r" (hiremainder) : "r" (__arg1), "r" (__arg2)); \
 __value; \
})

#define addmul(a, b) \
__extension__ ({ ulong __value, __arg1 = (a), __arg2 = (b), __hi; \
 __asm__ ("madd %0,%1,%2,%3\n\t" \
   : "=r" (__value) : "r" (__arg1), "r" (__arg2), "r" (hiremainder)); \
 __asm__ ("umulh %0,%1,%2\n\t" \
   : "=r" (__hi) : "r" (__arg1), "r" (__arg2)); \
 hiremainder = (__value < hiremainder) ? __hi+1: __hi;\
 __value; \
})

#define bfffo(a) \
__extension__ ({ ulong __a = (a), __value; \
    __asm__ ("clz %0, %1" : "=r" (__value) : "r" (__a)); \
    __value; \
})

#endif
