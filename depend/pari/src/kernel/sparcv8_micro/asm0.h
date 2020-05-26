/* Copyright (C) 2000  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */
/*
ASM divll
*/
#ifdef ASMINLINE
#define divll(a,b) \
__extension__ ({ ulong __value, __arg1 = (a), __arg2 = (b), __tmp; \
  __asm__( "mov %1, %%y; nop;nop;nop;\n\t\
udivcc  %3,%4,%0;\n\tumul    %0,%4,%2;\n\tsub     %3,%2,%1"\
        : "=&r" (__value), "=&r" (hiremainder), "=&r" (__tmp) \
        : "r" (__arg1), "r" (__arg2), "1" (hiremainder) \
        : "cc");        \
__value;})
#endif
