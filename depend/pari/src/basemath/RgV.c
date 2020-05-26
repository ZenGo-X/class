/* Copyright (C) 2000  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

#include "pari.h"
#include "paripriv.h"

int
RgM_is_ZM(GEN x)
{
  long i, j, h, l = lg(x);
  if (l == 1) return 1;
  h = lgcols(x);
  if (h == 1) return 1;
  for (j = l-1; j > 0; j--)
    for (i = h-1; i > 0; i--)
      if (typ(gcoeff(x,i,j)) != t_INT) return 0;
  return 1;
}

int
RgM_is_QM(GEN x)
{
  long i, j, h, l = lg(x);
  if (l == 1) return 1;
  h = lgcols(x);
  if (h == 1) return 1;
  for (j = l-1; j > 0; j--)
    for (i = h-1; i > 0; i--)
      if (!is_rational_t(typ(gcoeff(x,i,j)))) return 0;
  return 1;
}

int
RgV_is_ZMV(GEN V)
{
  long i, l = lg(V);
  for (i=1; i<l; i++)
    if (typ(gel(V,i))!=t_MAT || !RgM_is_ZM(gel(V,i)))
      return 0;
  return 1;
}

/********************************************************************/
/**                                                                **/
/**                   GENERIC LINEAR ALGEBRA                       **/
/**                                                                **/
/********************************************************************/
/*           GENERIC  MULTIPLICATION involving zc/zm                */

/* x[i,] * y */
static GEN
RgMrow_zc_mul_i(GEN x, GEN y, long c, long i)
{
  pari_sp av = avma;
  GEN s = NULL;
  long j;
  for (j=1; j<c; j++)
  {
    long t = y[j];
    if (!t) continue;
    if (!s) { s = gmulgs(gcoeff(x,i,j),t); continue; }
    switch(t)
    {
      case  1: s = gadd(s, gcoeff(x,i,j)); break;
      case -1: s = gsub(s, gcoeff(x,i,j)); break;
      default: s = gadd(s, gmulgs(gcoeff(x,i,j), t)); break;
    }
  }
  if (!s) { avma = av; return gen_0; }
  return gerepileupto(av, s);
}
GEN
RgMrow_zc_mul(GEN x, GEN y, long i) { return RgMrow_zc_mul_i(x,y,lg(y),i); }
/* x non-empty t_MAT, y a compatible zc (dimension > 0). */
static GEN
RgM_zc_mul_i(GEN x, GEN y, long c, long l)
{
  GEN z = cgetg(l,t_COL);
  long i;
  for (i = 1; i < l; i++) gel(z,i) = RgMrow_zc_mul_i(x,y,c,i);
  return z;
}
GEN
RgM_zc_mul(GEN x, GEN y) { return RgM_zc_mul_i(x,y, lg(x), lgcols(x)); }
/* x t_MAT, y a compatible zm (dimension > 0). */
GEN
RgM_zm_mul(GEN x, GEN y)
{
  long j, c, l = lg(x), ly = lg(y);
  GEN z = cgetg(ly, t_MAT);
  if (l == 1) return z;
  c = lgcols(x);
  for (j = 1; j < ly; j++) gel(z,j) = RgM_zc_mul_i(x, gel(y,j), l,c);
  return z;
}

static GEN
RgV_zc_mul_i(GEN x, GEN y, long l)
{
  long i;
  GEN z = gen_0;
  pari_sp av = avma;
  for (i = 1; i < l; i++) z = gadd(z, gmulgs(gel(x,i), y[i]));
  return gerepileupto(av, z);
}
GEN
RgV_zc_mul(GEN x, GEN y) { return RgV_zc_mul_i(x, y, lg(x)); }

GEN
RgV_zm_mul(GEN x, GEN y)
{
  long j, l = lg(x), ly = lg(y);
  GEN z = cgetg(ly, t_VEC);
  for (j = 1; j < ly; j++) gel(z,j) = RgV_zc_mul_i(x, gel(y,j), l);
  return z;
}

/* scalar product x.x */
GEN
RgV_dotsquare(GEN x)
{
  long i, lx = lg(x);
  pari_sp av = avma;
  GEN z;
  if (lx == 1) return gen_0;
  z = gsqr(gel(x,1));
  for (i=2; i<lx; i++)
  {
    z = gadd(z, gsqr(gel(x,i)));
    if (gc_needed(av,3))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"RgV_dotsquare, i = %ld",i);
      z = gerepileupto(av, z);
    }
  }
  return gerepileupto(av,z);
}

/* scalar product x.y, lx = lg(x) = lg(y) */
static GEN
RgV_dotproduct_i(GEN x, GEN y, long lx)
{
  pari_sp av = avma;
  long i;
  GEN z;
  if (lx == 1) return gen_0;
  z = gmul(gel(x,1),gel(y,1));
  for (i=2; i<lx; i++)
  {
    z = gadd(z, gmul(gel(x,i), gel(y,i)));
    if (gc_needed(av,3))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"RgV_dotproduct, i = %ld",i);
      z = gerepileupto(av, z);
    }
  }
  return gerepileupto(av,z);
}
GEN
RgV_dotproduct(GEN x,GEN y)
{
  if (x == y) return RgV_dotsquare(x);
  return RgV_dotproduct_i(x, y, lg(x));
}
/* v[1] + ... + v[lg(v)-1] */
GEN
RgV_sum(GEN v)
{
  GEN p;
  long i, l = lg(v);
  if (l == 1) return gen_0;
  p = gel(v,1); for (i=2; i<l; i++) p = gadd(p, gel(v,i));
  return p;
}
/* v[1] + ... + v[n]. Assume lg(v) > n. */
GEN
RgV_sumpart(GEN v, long n)
{
  GEN p;
  long i;
  if (!n) return gen_0;
  p = gel(v,1); for (i=2; i<=n; i++) p = gadd(p, gel(v,i));
  return p;
}
/* v[m] + ... + v[n]. Assume lg(v) > n, m > 0. */
GEN
RgV_sumpart2(GEN v, long m, long n)
{
  GEN p;
  long i;
  if (n < m) return gen_0;
  p = gel(v,m); for (i=m+1; i<=n; i++) p = gadd(p, gel(v,i));
  return p;
}
GEN
RgM_sumcol(GEN A)
{
  long i,j,m,l = lg(A);
  GEN v;

  if (l == 1) return cgetg(1,t_MAT);
  if (l == 2) return gcopy(gel(A,1));
  m = lgcols(A);
  v = cgetg(m, t_COL);
  for (i = 1; i < m; i++)
  {
    pari_sp av = avma;
    GEN s = gcoeff(A,i,1);
    for (j = 2; j < l; j++) s = gadd(s, gcoeff(A,i,j));
    gel(v, i) = gerepileupto(av, s);
  }
  return v;
}

static GEN
_gmul(void *data, GEN x, GEN y)
{ (void)data; return gmul(x,y); }

GEN
RgV_prod(GEN x)
{
  return gen_product(x, NULL, _gmul);
}

/*                    ADDITION SCALAR + MATRIX                     */
/* x square matrix, y scalar; create the square matrix x + y*Id */
GEN
RgM_Rg_add(GEN x, GEN y)
{
  long l = lg(x), i, j;
  GEN z = cgetg(l,t_MAT);

  if (l==1) return z;
  if (l != lgcols(x)) pari_err_OP( "+", x, y);
  z = cgetg(l,t_MAT);
  for (i=1; i<l; i++)
  {
    GEN zi = cgetg(l,t_COL), xi = gel(x,i);
    gel(z,i) = zi;
    for (j=1; j<l; j++)
      gel(zi,j) = i==j? gadd(y,gel(xi,j)): gcopy(gel(xi,j));
  }
  return z;
}
GEN
RgM_Rg_sub(GEN x, GEN y)
{
  long l = lg(x), i, j;
  GEN z = cgetg(l,t_MAT);

  if (l==1) return z;
  if (l != lgcols(x)) pari_err_OP( "-", x, y);
  z = cgetg(l,t_MAT);
  for (i=1; i<l; i++)
  {
    GEN zi = cgetg(l,t_COL), xi = gel(x,i);
    gel(z,i) = zi;
    for (j=1; j<l; j++)
      gel(zi,j) = i==j? gsub(gel(xi,j), y): gcopy(gel(xi,j));
  }
  return z;
}
GEN
RgM_Rg_add_shallow(GEN x, GEN y)
{
  long l = lg(x), i, j;
  GEN z = cgetg(l,t_MAT);

  if (l==1) return z;
  if (l != lgcols(x)) pari_err_OP( "+", x, y);
  for (i=1; i<l; i++)
  {
    GEN zi = cgetg(l,t_COL), xi = gel(x,i);
    gel(z,i) = zi;
    for (j=1; j<l; j++) gel(zi,j) = gel(xi,j);
    gel(zi,i) = gadd(gel(zi,i), y);
  }
  return z;
}
GEN
RgM_Rg_sub_shallow(GEN x, GEN y)
{
  long l = lg(x), i, j;
  GEN z = cgetg(l,t_MAT);

  if (l==1) return z;
  if (l != lgcols(x)) pari_err_OP( "-", x, y);
  for (i=1; i<l; i++)
  {
    GEN zi = cgetg(l,t_COL), xi = gel(x,i);
    gel(z,i) = zi;
    for (j=1; j<l; j++) gel(zi,j) = gel(xi,j);
    gel(zi,i) = gsub(gel(zi,i), y);
  }
  return z;
}

GEN
RgC_Rg_add(GEN x, GEN y)
{
  long k, lx = lg(x);
  GEN z = cgetg(lx, t_COL);
  if (lx == 1)
  {
    if (isintzero(y)) return z;
    pari_err_TYPE2("+",x,y);
  }
  gel(z,1) = gadd(y,gel(x,1));
  for (k = 2; k < lx; k++) gel(z,k) = gcopy(gel(x,k));
  return z;
}
GEN
RgC_Rg_sub(GEN x, GEN y)
{
  long k, lx = lg(x);
  GEN z = cgetg(lx, t_COL);
  if (lx == 1)
  {
    if (isintzero(y)) return z;
    pari_err_TYPE2("-",x,y);
  }
  gel(z,1) = gsub(gel(x,1), y);
  for (k = 2; k < lx; k++) gel(z,k) = gcopy(gel(x,k));
  return z;
}
/* a - x */
GEN
Rg_RgC_sub(GEN a, GEN x)
{
  long k, lx = lg(x);
  GEN z = cgetg(lx,t_COL);
  if (lx == 1)
  {
    if (isintzero(a)) return z;
    pari_err_TYPE2("-",a,x);
  }
  gel(z,1) = gsub(a, gel(x,1));
  for (k = 2; k < lx; k++) gel(z,k) = gneg(gel(x,k));
  return z;
}


static GEN
RgC_add_i(GEN x, GEN y, long lx)
{
  GEN A = cgetg(lx, t_COL);
  long i;
  for (i=1; i<lx; i++) gel(A,i) = gadd(gel(x,i), gel(y,i));
  return A;
}
GEN
RgC_add(GEN x, GEN y) { return RgC_add_i(x, y, lg(x)); }
GEN
RgV_add(GEN x, GEN y)
{ pari_APPLY_type(t_VEC, gadd(gel(x,i), gel(y,i))) }

static GEN
RgC_sub_i(GEN x, GEN y, long lx)
{
  long i;
  GEN A = cgetg(lx, t_COL);
  for (i=1; i<lx; i++) gel(A,i) = gsub(gel(x,i), gel(y,i));
  return A;
}
GEN
RgC_sub(GEN x, GEN y) { return RgC_sub_i(x, y, lg(x)); }
GEN
RgV_sub(GEN x, GEN y)
{ pari_APPLY_type(t_VEC, gsub(gel(x,i), gel(y,i))) }

GEN
RgM_add(GEN x, GEN y)
{
  long lx = lg(x), l, j;
  GEN z;
  if (lx == 1) return cgetg(1, t_MAT);
  z = cgetg(lx, t_MAT); l = lgcols(x);
  for (j = 1; j < lx; j++) gel(z,j) = RgC_add_i(gel(x,j), gel(y,j), l);
  return z;
}
GEN
RgM_sub(GEN x, GEN y)
{
  long lx = lg(x), l, j;
  GEN z;
  if (lx == 1) return cgetg(1, t_MAT);
  z = cgetg(lx, t_MAT); l = lgcols(x);
  for (j = 1; j < lx; j++) gel(z,j) = RgC_sub_i(gel(x,j), gel(y,j), l);
  return z;
}

static GEN
RgC_neg_i(GEN x, long lx)
{
  long i;
  GEN y = cgetg(lx, t_COL);
  for (i=1; i<lx; i++) gel(y,i) = gneg(gel(x,i));
  return y;
}
GEN
RgC_neg(GEN x) { return RgC_neg_i(x, lg(x)); }
GEN
RgV_neg(GEN x)
{ pari_APPLY_type(t_VEC, gneg(gel(x,i))) }
GEN
RgM_neg(GEN x)
{
  long i, hx, lx = lg(x);
  GEN y = cgetg(lx, t_MAT);
  if (lx == 1) return y;
  hx = lgcols(x);
  for (i=1; i<lx; i++) gel(y,i) = RgC_neg_i(gel(x,i), hx);
  return y;
}

GEN
RgV_RgC_mul(GEN x, GEN y)
{
  long lx = lg(x);
  if (lx != lg(y)) pari_err_OP("operation 'RgV_RgC_mul'", x, y);
  return RgV_dotproduct_i(x, y, lx);
}
GEN
RgC_RgV_mul(GEN x, GEN y)
{
  long i, ly = lg(y);
  GEN z = cgetg(ly,t_MAT);
  for (i=1; i<ly; i++) gel(z,i) = RgC_Rg_mul(x, gel(y,i));
  return z;
}
GEN
RgC_RgM_mul(GEN x, GEN y)
{
  long i, ly = lg(y);
  GEN z = cgetg(ly,t_MAT);
  if (ly != 1 && lgcols(y) != 2) pari_err_OP("operation 'RgC_RgM_mul'",x,y);
  for (i=1; i<ly; i++) gel(z,i) = RgC_Rg_mul(x, gcoeff(y,1,i));
  return z;
}
GEN
RgM_RgV_mul(GEN x, GEN y)
{
  if (lg(x) != 2) pari_err_OP("operation 'RgM_RgV_mul'", x,y);
  return RgC_RgV_mul(gel(x,1), y);
}

/* x[i,]*y, l = lg(y) > 1 */
static GEN
RgMrow_RgC_mul_i(GEN x, GEN y, long i, long l)
{
  pari_sp av = avma;
  GEN t = gmul(gcoeff(x,i,1), gel(y,1)); /* l > 1 ! */
  long j;
  for (j=2; j<l; j++) t = gadd(t, gmul(gcoeff(x,i,j), gel(y,j)));
  return gerepileupto(av,t);
}
GEN
RgMrow_RgC_mul(GEN x, GEN y, long i)
{ return RgMrow_RgC_mul_i(x, y, i, lg(x)); }

/* compatible t_MAT * t_COL, lx = lg(x) = lg(y) > 1, l = lgcols(x) */
static GEN
RgM_RgC_mul_i(GEN x, GEN y, long lx, long l)
{
  GEN z = cgetg(l,t_COL);
  long i;
  for (i=1; i<l; i++) gel(z,i) = RgMrow_RgC_mul_i(x,y,i,lx);
  return z;
}

GEN
RgM_RgC_mul(GEN x, GEN y)
{
  long lx = lg(x);
  GEN ffx = NULL, ffy = NULL;
  if (lx != lg(y)) pari_err_OP("operation 'RgM_RgC_mul'", x,y);
  if (lx == 1) return cgetg(1,t_COL);
  if (RgM_is_FFM(x, &ffx) && RgC_is_FFC(y, &ffy)) {
    if (!FF_samefield(ffx, ffy))
      pari_err_OP("*", ffx, ffy);
    return FFM_FFC_mul(x, y, ffx);
  }
  return RgM_RgC_mul_i(x, y, lx, lgcols(x));
}

GEN
RgV_RgM_mul(GEN x, GEN y)
{
  long i, lx, ly = lg(y);
  GEN z;
  if (ly == 1) return cgetg(1,t_VEC);
  lx = lg(x);
  if (lx != lgcols(y)) pari_err_OP("operation 'RgV_RgM_mul'", x,y);
  z = cgetg(ly, t_VEC);
  for (i=1; i<ly; i++) gel(z,i) = RgV_dotproduct_i(x, gel(y,i), lx);
  return z;
}

static GEN
RgM_mul_FpM(GEN x, GEN y, GEN p)
{
  pari_sp av = avma;
  GEN r;
  if (lgefint(p) == 3)
  {
    ulong pp = uel(p, 2);
    r = Flm_to_ZM_inplace(Flm_mul(RgM_to_Flm(x, pp),
                                  RgM_to_Flm(y, pp), pp));
  }
  else
    r = FpM_mul(RgM_to_FpM(x, p), RgM_to_FpM(y, p), p);
  return gerepileupto(av, FpM_to_mod(r, p));
}

static GEN
RgM_mul_FqM(GEN x, GEN y, GEN pol, GEN p)
{
  pari_sp av = avma;
  GEN b, T = RgX_to_FpX(pol, p);
  if (signe(T) == 0) pari_err_OP("*", x, y);
  b = FqM_mul(RgM_to_FqM(x, T, p), RgM_to_FqM(y, T, p), T, p);
  return gerepileupto(av, FqM_to_mod(b, T, p));
}

static GEN
RgM_liftred(GEN x, GEN T)
{ return RgXQM_red(liftpol_shallow(x), T); }

static GEN
RgM_mul_ZXQM(GEN x, GEN y, GEN T)
{
  pari_sp av = avma;
  GEN b = ZXQM_mul(RgM_liftred(x,T), RgM_liftred(y, T), T);
  return gerepilecopy(av, QXQM_to_mod_shallow(b,T));
}

static GEN
RgM_sqr_ZXQM(GEN x, GEN T)
{
  pari_sp av = avma;
  GEN b = ZXQM_sqr(RgM_liftred(x, T), T);
  return gerepilecopy(av, QXQM_to_mod_shallow(b,T));
}

static GEN
RgM_mul_QXQM(GEN x, GEN y, GEN T)
{
  pari_sp av = avma;
  GEN b = QXQM_mul(RgM_liftred(x, T), RgM_liftred(y, T), T);
  return gerepilecopy(av, QXQM_to_mod_shallow(b,T));
}

static GEN
RgM_sqr_QXQM(GEN x, GEN T)
{
  pari_sp av = avma;
  GEN b = QXQM_sqr(RgM_liftred(x, T), T);
  return gerepilecopy(av, QXQM_to_mod_shallow(b,T));
}

INLINE int
RgX_is_monic_ZX(GEN pol)
{ return RgX_is_ZX(pol) && ZX_is_monic(pol); }

#define code(t1,t2) ((t1 << 6) | t2)
static GEN
RgM_mul_fast(GEN x, GEN y)
{
  GEN p, pol;
  long pa;
  long t = RgM_type2(x,y, &p,&pol,&pa);
  switch(t)
  {
    case t_INT:    return ZM_mul(x,y);
    case t_FRAC:   return QM_mul(x,y);
    case t_FFELT:  return FFM_mul(x, y, pol);
    case t_INTMOD: return RgM_mul_FpM(x, y, p);
    case code(t_POLMOD, t_INT):
                   return ZX_is_monic(pol)? RgM_mul_ZXQM(x, y, pol): NULL;
    case code(t_POLMOD, t_FRAC):
                   return RgX_is_monic_ZX(pol)? RgM_mul_QXQM(x, y, pol): NULL;
    case code(t_POLMOD, t_INTMOD):
                   return RgM_mul_FqM(x, y, pol, p);
    default:       return NULL;
  }
}

static GEN
RgM_sqr_fast(GEN x)
{
  GEN p, pol;
  long pa;
  long t = RgM_type(x, &p,&pol,&pa);
  switch(t)
  {
    case t_INT:    return ZM_sqr(x);
    case t_FRAC:   return QM_mul(x, x);
    case t_FFELT:  return FFM_mul(x, x, pol);
    case t_INTMOD: return RgM_mul_FpM(x, x, p);
    case code(t_POLMOD, t_INT):
                   return ZX_is_monic(pol)? RgM_sqr_ZXQM(x, pol): NULL;
    case code(t_POLMOD, t_FRAC):
                   return RgX_is_monic_ZX(pol)? RgM_sqr_QXQM(x, pol): NULL;
    case code(t_POLMOD, t_INTMOD):
                   return RgM_mul_FqM(x, x, pol, p);
    default:       return NULL;
  }
}

#undef code

GEN
RgM_mul(GEN x, GEN y)
{
  long j, l, lx, ly = lg(y);
  GEN z;
  if (ly == 1) return cgetg(1,t_MAT);
  lx = lg(x);
  if (lx != lgcols(y)) pari_err_OP("operation 'RgM_mul'", x,y);
  if (lx == 1) return zeromat(0,ly-1);
  z = RgM_mul_fast(x, y);
  if (z) return z;
  z = cgetg(ly, t_MAT);
  l = lgcols(x);
  for (j=1; j<ly; j++) gel(z,j) = RgM_RgC_mul_i(x, gel(y,j), lx, l);
  return z;
}

GEN
RgM_sqr(GEN x)
{
  long j, lx = lg(x);
  GEN z;
  if (lx == 1) return cgetg(1, t_MAT);
  if (lx != lgcols(x)) pari_err_OP("operation 'RgM_mul'", x,x);
  z = RgM_sqr_fast(x);
  if (z) return z;
  z = cgetg(lx, t_MAT);
  for (j=1; j<lx; j++) gel(z,j) = RgM_RgC_mul_i(x, gel(x,j), lx, lx);
  return z;
}

/* assume result is symmetric */
GEN
RgM_multosym(GEN x, GEN y)
{
  long j, lx, ly = lg(y);
  GEN M;
  if (ly == 1) return cgetg(1,t_MAT);
  lx = lg(x);
  if (lx != lgcols(y)) pari_err_OP("operation 'RgM_multosym'", x,y);
  if (lx == 1) return cgetg(1,t_MAT);
  if (ly != lgcols(x)) pari_err_OP("operation 'RgM_multosym'", x,y);
  M = cgetg(ly, t_MAT);
  for (j=1; j<ly; j++)
  {
    GEN z = cgetg(ly,t_COL), yj = gel(y,j);
    long i;
    for (i=1; i<j; i++) gel(z,i) = gcoeff(M,j,i);
    for (i=j; i<ly; i++)gel(z,i) = RgMrow_RgC_mul_i(x,yj,i,lx);
    gel(M,j) = z;
  }
  return M;
}
/* x~ * y, assuming result is symmetric */
GEN
RgM_transmultosym(GEN x, GEN y)
{
  long i, j, l, ly = lg(y);
  GEN M;
  if (ly == 1) return cgetg(1,t_MAT);
  if (lg(x) != ly) pari_err_OP("operation 'RgM_transmultosym'", x,y);
  l = lgcols(y);
  if (lgcols(x) != l) pari_err_OP("operation 'RgM_transmultosym'", x,y);
  M = cgetg(ly, t_MAT);
  for (i=1; i<ly; i++)
  {
    GEN xi = gel(x,i), c = cgetg(ly,t_COL);
    gel(M,i) = c;
    for (j=1; j<i; j++)
      gcoeff(M,i,j) = gel(c,j) = RgV_dotproduct_i(xi,gel(y,j),l);
    gel(c,i) = RgV_dotproduct_i(xi,gel(y,i),l);
  }
  return M;
}
/* x~ * y */
GEN
RgM_transmul(GEN x, GEN y)
{
  long i, j, l, lx, ly = lg(y);
  GEN M;
  if (ly == 1) return cgetg(1,t_MAT);
  lx = lg(x);
  l = lgcols(y);
  if (lgcols(x) != l) pari_err_OP("operation 'RgM_transmul'", x,y);
  M = cgetg(ly, t_MAT);
  for (i=1; i<ly; i++)
  {
    GEN yi = gel(y,i), c = cgetg(lx,t_COL);
    gel(M,i) = c;
    for (j=1; j<lx; j++) gel(c,j) = RgV_dotproduct_i(yi,gel(x,j),l);
  }
  return M;
}

GEN
gram_matrix(GEN x)
{
  long i,j, l, lx = lg(x);
  GEN M;
  if (!is_matvec_t(typ(x))) pari_err_TYPE("gram",x);
  if (lx == 1) return cgetg(1,t_MAT);
  l = lgcols(x);
  M = cgetg(lx,t_MAT);
  for (i=1; i<lx; i++)
  {
    GEN xi = gel(x,i), c = cgetg(lx,t_COL);
    gel(M,i) = c;
    for (j=1; j<i; j++)
      gcoeff(M,i,j) = gel(c,j) = RgV_dotproduct_i(xi,gel(x,j),l);
    gel(c,i) = RgV_dotsquare(xi);
  }
  return M;
}

static GEN
_RgM_add(void *E, GEN x, GEN y) { (void)E; return RgM_add(x, y); }

static GEN
_RgM_sub(void *E, GEN x, GEN y) { (void)E; return RgM_sub(x, y); }

static GEN
_RgM_cmul(void *E, GEN P, long a, GEN x) { (void)E; return RgM_Rg_mul(x,gel(P,a+2)); }

static GEN
_RgM_sqr(void *E, GEN x) { (void) E; return RgM_sqr(x); }

static GEN
_RgM_mul(void *E, GEN x, GEN y) { (void) E; return RgM_mul(x, y); }

static GEN
_RgM_one(void *E) { long *n = (long*) E; return matid(*n); }

static GEN
_RgM_zero(void *E) { long *n = (long*) E; return zeromat(*n,*n); }

static GEN
_RgM_red(void *E, GEN x) { (void)E; return x; }

static struct bb_algebra RgM_algebra = { _RgM_red, _RgM_add, _RgM_sub,
       _RgM_mul, _RgM_sqr, _RgM_one, _RgM_zero };

/* generates the list of powers of x of degree 0,1,2,...,l*/
GEN
RgM_powers(GEN x, long l)
{
  long n = lg(x)-1;
  return gen_powers(x,l,1,(void *) &n, &_RgM_sqr, &_RgM_mul, &_RgM_one);
}

GEN
RgX_RgMV_eval(GEN Q, GEN x)
{
  long n = lg(x)>1 ? lg(gel(x,1))-1:0;
  return gen_bkeval_powers(Q,degpol(Q),x,(void*)&n,&RgM_algebra,&_RgM_cmul);
}

GEN
RgX_RgM_eval(GEN Q, GEN x)
{
  long n = lg(x)-1;
  return gen_bkeval(Q,degpol(Q),x,1,(void*)&n,&RgM_algebra,&_RgM_cmul);
}

GEN
RgC_Rg_div(GEN x, GEN y)
{ pari_APPLY_type(t_COL, gdiv(gel(x,i),y)) }

GEN
RgC_Rg_mul(GEN x, GEN y)
{ pari_APPLY_type(t_COL, gmul(gel(x,i),y)) }

GEN
RgV_Rg_mul(GEN x, GEN y)
{ pari_APPLY_type(t_VEC, gmul(gel(x,i),y)) }

GEN
RgM_Rg_div(GEN X, GEN c) {
  long i, j, h, l = lg(X);
  GEN A = cgetg(l, t_MAT);
  if (l == 1) return A;
  h = lgcols(X);
  for (j=1; j<l; j++)
  {
    GEN a = cgetg(h, t_COL), x = gel(X, j);
    for (i = 1; i < h; i++) gel(a,i) = gdiv(gel(x,i), c);
    gel(A,j) = a;
  }
  return A;
}
GEN
RgM_Rg_mul(GEN X, GEN c) {
  long i, j, h, l = lg(X);
  GEN A = cgetg(l, t_MAT);
  if (l == 1) return A;
  h = lgcols(X);
  for (j=1; j<l; j++)
  {
    GEN a = cgetg(h, t_COL), x = gel(X, j);
    for (i = 1; i < h; i++) gel(a,i) = gmul(gel(x,i), c);
    gel(A,j) = a;
  }
  return A;
}

/********************************************************************/
/*                                                                  */
/*                    SCALAR TO MATRIX/VECTOR                       */
/*                                                                  */
/********************************************************************/
/* fill the square nxn matrix equal to t*Id */
static void
fill_scalmat(GEN y, GEN t, long n)
{
  long i;
  for (i = 1; i <= n; i++)
  {
    gel(y,i) = zerocol(n);
    gcoeff(y,i,i) = t;
  }
}

GEN
scalarmat(GEN x, long n) {
  GEN y = cgetg(n+1, t_MAT);
  if (!n) return y;
  fill_scalmat(y, gcopy(x), n); return y;
}
GEN
scalarmat_shallow(GEN x, long n) {
  GEN y = cgetg(n+1, t_MAT);
  fill_scalmat(y, x, n); return y;
}
GEN
scalarmat_s(long x, long n) {
  GEN y = cgetg(n+1, t_MAT);
  if (!n) return y;
  fill_scalmat(y, stoi(x), n); return y;
}
GEN
matid(long n) {
  GEN y;
  if (n < 0) pari_err_DOMAIN("matid", "size", "<", gen_0, stoi(n));
  y = cgetg(n+1, t_MAT);
  fill_scalmat(y, gen_1, n); return y;
}

INLINE GEN
scalarcol_i(GEN x, long n, long c)
{
  long i;
  GEN y = cgetg(n+1,t_COL);
  if (!n) return y;
  gel(y,1) = c? gcopy(x): x;
  for (i=2; i<=n; i++) gel(y,i) = gen_0;
  return y;
}

GEN
scalarcol(GEN x, long n) { return scalarcol_i(x,n,1); }

GEN
scalarcol_shallow(GEN x, long n) { return scalarcol_i(x,n,0); }

int
RgM_isscalar(GEN x, GEN s)
{
  long i, j, lx = lg(x);

  if (lx == 1) return 1;
  if (lx != lgcols(x)) return 0;
  if (!s) s = gcoeff(x,1,1);

  for (j=1; j<lx; j++)
  {
    GEN c = gel(x,j);
    for (i=1; i<j; )
      if (!gequal0(gel(c,i++))) return 0;
    /* i = j */
      if (!gequal(gel(c,i++),s)) return 0;
    for (   ; i<lx; )
      if (!gequal0(gel(c,i++))) return 0;
  }
  return 1;
}

int
RgM_isidentity(GEN x)
{
  long i,j, lx = lg(x);

  if (lx == 1) return 1;
  if (lx != lgcols(x)) return 0;
  for (j=1; j<lx; j++)
  {
    GEN c = gel(x,j);
    for (i=1; i<j; )
      if (!gequal0(gel(c,i++))) return 0;
    /* i = j */
      if (!gequal1(gel(c,i++))) return 0;
    for (   ; i<lx; )
      if (!gequal0(gel(c,i++))) return 0;
  }
  return 1;
}

long
RgC_is_ei(GEN x)
{
  long i, j = 0, l = lg(x);
  for (i = 1; i < l; i++)
  {
    GEN c = gel(x,i);
    if (gequal0(c)) continue;
    if (!gequal1(c) || j) return 0;
    j = i;
  }
  return j;
}

int
RgM_isdiagonal(GEN x)
{
  long i,j, lx = lg(x);
  if (lx == 1) return 1;
  if (lx != lgcols(x)) return 0;

  for (j=1; j<lx; j++)
  {
    GEN c = gel(x,j);
    for (i=1; i<j; i++)
      if (!gequal0(gel(c,i))) return 0;
    for (i++; i<lx; i++)
      if (!gequal0(gel(c,i))) return 0;
  }
  return 1;
}
int
isdiagonal(GEN x)
{
  return (typ(x)==t_MAT) && RgM_isdiagonal(x);
}

/* returns the first index i<=n such that x=v[i] if it exists, 0 otherwise */
long
RgV_isin(GEN v, GEN x)
{
  long i, l = lg(v);
  for (i = 1; i < l; i++)
    if (gequal(gel(v,i), x)) return i;
  return 0;
}

GEN
RgM_det_triangular(GEN mat)
{
  long i,l = lg(mat);
  pari_sp av;
  GEN s;

  if (l<3) return l<2? gen_1: gcopy(gcoeff(mat,1,1));
  av = avma; s = gcoeff(mat,1,1);
  for (i=2; i<l; i++) s = gmul(s,gcoeff(mat,i,i));
  return av==avma? gcopy(s): gerepileupto(av,s);
}

GEN
RgV_kill0(GEN v)
{
  long i, l;
  GEN w = cgetg_copy(v, &l);
  for (i = 1; i < l; i++)
  {
    GEN a = gel(v,i);
    gel(w,i) = gequal0(a) ? NULL: a;
  }
  return w;
}
