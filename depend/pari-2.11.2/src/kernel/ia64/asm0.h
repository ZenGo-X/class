#line 2 "../src/kernel/ia64/asm0.h"
/* Copyright (C) 2006  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/*
ASM mulll bfffo
NOASM addll divll
*/

#ifdef ASMINLINE
/* Written by Guillaume Hanrot */
#define LOCAL_HIREMAINDER  register ulong hiremainder

#define bfffo(a)                                                        \
__extension__ ({ ulong __arg1 = (a), __tmp, _a, _c;                     \
    __asm__ ("mux1 %0 = %1, @rev" : "=r" (__tmp) : "r" (__arg1));       \
    __asm__ ("czx1.l %0 = %1" : "=r" (_a) : "r" (-__tmp | __tmp));      \
    _c = (_a - 1) << 3;                                                 \
    __arg1 >>= _c;                                                      \
    if (__arg1 >= 1 << 4)                                               \
      __arg1 >>= 4, _c += 4;                                            \
    if (__arg1 >= 1 << 2)                                               \
      __arg1 >>= 2, _c += 2;                                            \
    _c += __arg1 >> 1;                                                  \
    63 - _c;                                                            \
})

#define mulll(a, b)                                                     \
__extension__ ({                                                        \
  ulong __arg1 = (a), __arg2 = (b), __value;                            \
  __asm__ ("xma.hu %0 = %2, %3, f0\n\t;;\n\txma.l %1 = %2, %3, f0"      \
           : "=&f" (hiremainder), "=f" (__value)                        \
           : "f" (__arg1), "f" (__arg2));                               \
  __value;                                                              \
})

#define addmul(a, b)                                                    \
__extension__ ({                                                        \
  ulong __arg1 = (a), __arg2 = (b), __value;                            \
  __asm__ ("xma.hu %0 = %2, %3, %4\n\txma.l %1 = %2, %3, %4"            \
           : "=&f" (hiremainder), "=f" (__value)                        \
           : "f" (__arg1), "f" (__arg2), "f" (hiremainder));            \
  __value;                                                              \
})
#endif
