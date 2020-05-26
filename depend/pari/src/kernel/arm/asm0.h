/* Copyright (C) 2000  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA. */
/*
ASM addll mulll
NOASM bfffo divll
*/
#ifdef ASMINLINE
#define LOCAL_HIREMAINDER  register ulong hiremainder
#define LOCAL_OVERFLOW     register ulong overflow

#define addll(a, b) \
__extension__ ({ ulong __value, __arg1 = (a), __arg2 = (b); \
 __asm__ ("adds %0,%2,%3\n\tadc %1,%4,%4\n\t" \
   : "=&r" (__value), "=&r" (overflow) \
   : "r" (__arg1), "r" (__arg2), "r" ((ulong)0): "cc"); \
 __value; \
})

#define addllx(a, b) \
__extension__ ({ ulong __value, __arg1 = (a), __arg2 = (b); \
 __asm__ ("subs %1,%4,#1\n\tadcs %0,%2,%3\n\tadc %1,%5,%5\n\t" \
   : "=&r" (__value), "=&r" (overflow) \
   : "r" (__arg1), "r" (__arg2), "r" (overflow), "r" ((ulong)0) \
   : "cc"); \
 __value; \
})

#define subll(a, b) \
__extension__ ({ ulong __value, __arg1 = (a), __arg2 = (b); \
 __asm__ ("subs %0,%2,%3\n\tadc %1,%4,%4\n\trsb %1,%1,#1\n\t" \
   : "=&r" (__value), "=&r" (overflow) \
   : "r" (__arg1), "r" (__arg2), "r" ((ulong)0) \
   : "cc"); \
 __value; \
})

#define subllx(a, b) \
__extension__ ({ ulong __value, __arg1 = (a), __arg2 = (b); \
 __asm__ ("rsbs %1,%4,%5\n\tsbcs %0,%2,%3\n\tadc %1,%5,%5\n\trsb %1,%1,#1\n\t" \
   : "=&r" (__value), "=&r" (overflow) \
   : "r" (__arg1), "r" (__arg2), "r" (overflow), "r" ((ulong)0) \
   : "cc"); \
 __value; \
})

#define mulll(a, b) \
__extension__ ({ ulong __value, __arg1 = (a), __arg2 = (b); \
 __asm__ ("umull %0,%1,%2,%3\n\t" \
   : "=&r" (__value), "=&r" (hiremainder) \
   : "r" (__arg1), "r" (__arg2)); \
 __value; \
})

#define addmul(a, b) \
__extension__ ({ ulong __value, __arg1 = (a), __arg2 = (b); \
 __asm__ ("umlal %0,%1,%2,%3\n\t" \
   : "=&r" (__value), "=&r" (hiremainder) \
   : "r" (__arg1), "r" (__arg2), "1" ((ulong) 0), "0" (hiremainder)); \
 __value; \
})

#if 0 /* Not supported by all CPU */
#define bfffo(a) \
__extension__ ({ \
  ulong __arg1 = (a), __value; \
  __asm__ ("clz %0,%1\n\t" \
           : "=&r" (__value) \
           : "r" (__arg1)); \
  __value; \
})
#endif

#endif
