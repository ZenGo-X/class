#line 2 "../src/kernel/none/divll_pre.h"
/* Copyright (C) 2014  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

#undef  LOCAL_HIREMAINDER
extern ulong hiremainder;
#if defined(INLINE) && defined(__GNUC__) && !defined(DISABLE_INLINE)
#define LOCAL_HIREMAINDER register ulong hiremainder
#else
#define LOCAL_HIREMAINDER
#endif

#if defined(INLINE) && defined(__GNUC__) && !defined(DISABLE_INLINE)
INLINE ulong /* precompute inverse of n */
get_Fl_red(ulong n)
{
  LOCAL_HIREMAINDER;
  n <<= bfffo(n);
  hiremainder = ~n;
  return divll(~0UL, n);
}
#else
INLINE ulong /* precompute inverse of n */
get_Fl_red(ulong n)
{
  ulong q, oldhi = hiremainder;
  n <<= bfffo(n);
  hiremainder = ~n;
  q = divll(~0UL, n);
  hiremainder = oldhi;
  return q;
}
#endif

INLINE ulong /* requires u1 <= n, n normalised */
divll_pre_normalized(ulong u1, ulong u0, ulong n, ulong ninv, ulong *pt_r)
{
  ulong q0, q1, r;
  LOCAL_HIREMAINDER;
  LOCAL_OVERFLOW;
  q0 = mulll(ninv, u1); q1 = hiremainder;
  q0 = addll(q0, u0);
  q1 = addllx(q1+1, u1);
  r = u0 - q1 * n;
  if (r > q0)
  {
    r += n; q1--;
  }
  if (r >= n)
  {
    r -= n; q1++;
  }
  *pt_r = r; return q1;
}

INLINE ulong /* requires u1 <= n, n normalised */
remll_pre_normalized(ulong u1, ulong u0, ulong n, ulong ninv)
{
  ulong q0, q1, r;
  LOCAL_HIREMAINDER;
  LOCAL_OVERFLOW;
  q0 = mulll(ninv, u1); q1 = hiremainder;
  q0 = addll(q0, u0);
  q1 = addllx(q1, u1);
  r = u0 - (q1 + 1) * n;
  if (r >= q0)
    r += n;
  return r < n ? r : r - n;
}

INLINE ulong /* reduce <a_hi, a_lo> mod n */
remll_pre(ulong a_hi, ulong a_lo, ulong n, ulong ninv)
{
  int norm = bfffo(n);
  int bits = BITS_IN_LONG - norm;
  ulong sn = n << norm;
  if (a_hi >= n) /* reduce a_hi first */
  {
    const ulong u1 = norm ? a_hi >> bits : 0;
    const ulong u0 = a_hi << norm;
    a_hi = remll_pre_normalized(u1, u0, sn, ninv) >> norm;
  }
  /* now reduce <a_hi, a_lo> */
  {
    const ulong u1 = ((a_hi << norm) | (norm ? a_lo >> bits: 0));
    const ulong u0 =   a_lo << norm;
    return remll_pre_normalized(u1, u0, sn, ninv) >> norm;
  }
}

#if !defined(INLINE)
extern ulong divll_pre(ulong a_lo, ulong n, ulong ninv);
#else

#if defined(__GNUC__) && !defined(DISABLE_INLINE)
#define divll_pre(a, n, ninv)                                           \
__extension__ ({                                                        \
  ulong __a = (a);                                                      \
  ulong __n = (n);                                                      \
  int norm = bfffo(__n);                                                \
  int bits = BITS_IN_LONG - norm;                                       \
  ulong r, sn = __n << norm;                                            \
  const ulong u1 = ((hiremainder << norm) | (norm ? __a >> bits: 0));   \
  const ulong u0 = __a << norm;                                         \
  const ulong q = divll_pre_normalized(u1, u0, sn, ninv, &r);           \
  hiremainder = r>>norm; q;                                             \
              })

#else /* __GNUC__ */
INLINE ulong
divll_pre(ulong a_lo, ulong n, ulong ninv)
{
  int norm = bfffo(n);
  int bits = BITS_IN_LONG - norm;
  ulong r, sn = n << norm;
  const ulong u1 = ((hiremainder << norm) | (norm ? a_lo >> bits: 0));
  const ulong u0 = a_lo << norm;
  const ulong q  = divll_pre_normalized(u1, u0, sn, ninv, &r);
  hiremainder = r>>norm; return q;
}
#endif /* __GNUC__ */

#endif
