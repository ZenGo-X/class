/* Copyright (C) 2016 The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/********************************************************************/
/**                                                                **/
/**             MATRIX PERMANENT, via RYSER'S FORMULA              **/
/**            (initial implementation: C. Greathouse)             **/
/**                                                                **/
/********************************************************************/
#include "pari.h"
#include "paripriv.h"

/* Ryser's formula */
GEN
matpermanent(GEN M)
{
  pari_sp av;
  long n = lg(M)-1, i, x, upper;
  GEN p, in;
  if (typ(M) != t_MAT) pari_err_TYPE("matpermanent", M);
  if (!n) return gen_1;
  if (n != nbrows(M)) pari_err_DIM("matpermanent");
#ifdef LONG_IS_64BIT /* because of vals(long x) => x <= LONG_MAX */
  if (n > 63) pari_err_IMPL("large matrix permanent");
#else
  if (n > 31) pari_err_IMPL("large matrix permanent");
#endif
  if (n == 1) return gcopy(gcoeff(M,1,1));

  av = avma;
  if (RgM_is_QM(M))
  {
    GEN cM;
    M = Q_primitive_part(M, &cM);
    p = ZM_permanent(M);
    if (cM) p = gerepileupto(av, gmul(p, gpowgs(cM,n)));
    return p;
  }

  p = gen_0;
  in = zerovec(n);
  upper = 1L << n;
  for (x = 1; x < upper; x++)
  {
    long gray = x ^ (x>>1), k = vals(x);
    GEN col = gel(M,k+1);
    if (gray & (1L<<k))
    { for (i=1; i <= n; ++i) gel(in, i) = gadd(gel(in, i), gel(col, i)); }
    else
    { for (i=1; i <= n; ++i) gel(in, i) = gsub(gel(in, i), gel(col, i)); }
    if (hammingl(gray)&1)
      p = gsub(p, RgV_prod(in));
    else
      p = gadd(p, RgV_prod(in));
    if (gc_needed(av, 1)) gerepileall(av, 2, &in, &p);
  }
  if (n&1) p = gneg(p);
  return gerepileupto(av, p);
}

/* ||M||_oo = max_i \sum_j | M[i,j] | */
static GEN
ZM_normoo(GEN M)
{
  long i, j, m, l = lg(M);
  GEN N = NULL;
  if (l == 1) return gen_0;
  m = lgcols(M);
  for (i = 1; i < m; i++)
  {
    GEN s = mpabs_shallow(gcoeff(M,i,1));
    for (j = 2; j < l; j++) s = addii(s, mpabs_shallow(gcoeff(M,i,j)));
    if (!N || abscmpii(N, s) < 0) N = s;
  }
  return N;
}

/* Assumes M square; dimensions <= 31x31 (32-bit) or 63x63 (64-bit). */
GEN
ZM_permanent(GEN M)
{
  pari_sp av = avma;
  GEN p, in;
  long i, x, upper, n = lg(M)-1;
  if (!is_bigint(ZM_normoo(M)))
    return gerepileuptoint(av, zm_permanent(ZM_to_zm(M)));
  p = gen_0;
  in = zerocol(n);
  upper = (1L<<n);
  for (x = 1; x < upper; x++)
  {
    long gray = x ^ (x>>1), k = vals(x);
    GEN c, col = gel(M, k+1);
    if (gray & (1L<<k))
    { for (i=1; i <= n; ++i) gel(in, i) = addii(gel(in,i), gel(col,i)); }
    else
    { for (i=1; i <= n; ++i) gel(in, i) = subii(gel(in,i), gel(col,i)); }
    c = ZV_prod(in);
    if (hammingl(gray)&1) togglesign_safe(&c);
    p = addii(p, c);
    if (gc_needed(av, 1)) gerepileall(av, 2, &in, &p);
  }
  if (n&1) togglesign_safe(&p);
  return gerepilecopy(av, p);
}

/* Assumes M square; dimensions <= 31x31 (32-bit) or 63x63 (64-bit). */
GEN
zm_permanent(GEN M)
{
  pari_sp av = avma;
  long n = lg(M)-1;
  ulong x, upper = (1UL<<n);
  GEN p = gen_0, in = const_vecsmall(n, 0);
  pari_sp av2 = avma;
  for (x = 1; x < upper; x++)
  {
    ulong gray = x ^ (x>>1);
    long i, k = vals(x);
    GEN c, col = gel(M, k+1);
    if (gray & (1UL<<k))
    { for (i = 1; i <= n; ++i) in[i] += col[i]; }
    else
    { for (i = 1; i <= n; ++i) in[i] -= col[i]; }
    c = vecsmall_prod(in);
    if (hammingl(gray)&1) togglesign_safe(&c);
    p = addii(p, c);
    if (gc_needed(av2, 1)) p = gerepileuptoint(av2, p);
  }
  if (n&1) togglesign_safe(&p);
  return gerepileuptoint(av, p);
}
