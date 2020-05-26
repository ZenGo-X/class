#line 2 "../src/kernel/m68k/asm0.h"
/* Copyright (C) 2006  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/* Written by Bill Allombert and dedicated to thoses who wrote the original
 * m68k kernel mp.s */

/*
ASM addll mulll bfffo divll
*/

#ifdef ASMINLINE
#define LOCAL_HIREMAINDER  register ulong hiremainder
#define LOCAL_OVERFLOW     register ulong overflow

#define addll(a,b)                                              \
__extension__ ({ ulong __value, __arg1 = (a), __arg2 = (b);     \
   __asm__ ("add.l %2,%0 ; addx.l %1,%1"                        \
        : "=&d" (__value), "=d" (overflow)                      \
        : "rm" (__arg1), "0" (__arg2), "1" (0UL)                \
        : "cc");                                                \
  __value;                                                      \
})

#define addllx(a,b)                                             \
__extension__ ({ ulong __value, __arg1 = (a), __arg2 = (b), __temp; \
   __asm__ ("neg.l %2 ; addx.l %4,%0 ; addx.l %1,%1"            \
        : "=d" (__value), "=d" (overflow), "=d" (__temp)        \
        : "0" (__arg1), "d" (__arg2), "2" (overflow), "1" (0UL) \
        : "cc");                                                \
  __value;                                                      \
})

#define subll(a,b)                                              \
__extension__ ({ ulong __value, __arg1 = (a), __arg2 = (b);     \
   __asm__ ("sub.l %3,%0 ; addx.l %1,%1"                        \
        : "=&d" (__value), "=d" (overflow)                      \
        : "0" (__arg1), "rm" (__arg2), "1" (0UL)                \
        : "cc");                                                \
  __value;                                                      \
})

#define subllx(a,b)                                             \
__extension__ ({ ulong __value, __arg1 = (a), __arg2 = (b), __temp; \
   __asm__ ("neg.l %2 ; subx.l %4,%0 ; addx.l %1,%1"            \
        : "=d" (__value), "=d" (overflow), "=d" (__temp)        \
        : "0" (__arg1), "d" (__arg2), "2" (overflow), "1" (0UL) \
        : "cc");                                                \
  __value;                                                      \
})

#define mulll(a, b)                                                     \
__extension__ ({                                                        \
  ulong __arg1 = (a), __arg2 = (b), __value;                            \
  __asm__ ("mulu.l %2, %0:%1"                                           \
           : "=d" (hiremainder), "=d" (__value)                         \
           : "md" (__arg1) , "1" (__arg2)                               \
           : "cc");                                                     \
  __value;                                                              \
})

#define addmul(a, b)                                                    \
__extension__ ({                                                        \
  ulong __arg1 = (a), __arg2 = (b), __value;                            \
  __asm__ ("mulu.l %2, %0:%1; add.l %4,%1; addx.l %5,%0"                \
           : "=&d" (hiremainder), "=&d" (__value)                       \
           : "md" (__arg1), "1" (__arg2), "d" (hiremainder), "d" (0UL)  \
           : "cc" );                                                    \
  __value;                                                              \
})

#define bfffo(a)                                                        \
__extension__ ({                                                        \
  ulong __arg1 = (a), __value;                                          \
  __asm__ ("bfffo %1{#0:#0}, %0"                                        \
           : "=d" (__value)                                             \
           : "md" (__arg1)                                              \
           : "cc" );                                                    \
  __value;                                                              \
})

#define divll(a, b)                                                     \
__extension__ ({                                                        \
  ulong __arg2 = (b), __value =(a);                                     \
  __asm__ ("divu.l %2, %0:%1"                                           \
           : "+d" (hiremainder), "+d" (__value)                         \
           : "md" (__arg2)                                              \
           : "cc");                                                     \
  __value;                                                              \
})
#endif
