/* Copyright (C) 2000, 2012  The PARI group.

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
/**                         LINEAR ALGEBRA                         **/
/**                          (first part)                          **/
/**                                                                **/
/********************************************************************/
#include "pari.h"
#include "paripriv.h"

/*******************************************************************/
/*                                                                 */
/*                         GEREPILE                                */
/*                                                                 */
/*******************************************************************/

static void
gerepile_mat(pari_sp av, pari_sp tetpil, GEN x, long k, long m, long n, long t)
{
  pari_sp A, bot = pari_mainstack->bot;
  long u, i;
  size_t dec;

  (void)gerepile(av,tetpil,NULL); dec = av-tetpil;

  for (u=t+1; u<=m; u++)
  {
    A = (pari_sp)coeff(x,u,k);
    if (A < av && A >= bot) coeff(x,u,k) += dec;
  }
  for (i=k+1; i<=n; i++)
    for (u=1; u<=m; u++)
    {
      A = (pari_sp)coeff(x,u,i);
      if (A < av && A >= bot) coeff(x,u,i) += dec;
    }
}

static void
gen_gerepile_gauss_ker(GEN x, long k, long t, pari_sp av, void *E, GEN (*copy)(void*, GEN))
{
  pari_sp tetpil = avma;
  long u,i, n = lg(x)-1, m = n? nbrows(x): 0;

  if (DEBUGMEM > 1) pari_warn(warnmem,"gauss_pivot_ker. k=%ld, n=%ld",k,n);
  for (u=t+1; u<=m; u++) gcoeff(x,u,k) = copy(E,gcoeff(x,u,k));
  for (i=k+1; i<=n; i++)
    for (u=1; u<=m; u++) gcoeff(x,u,i) = copy(E,gcoeff(x,u,i));
  gerepile_mat(av,tetpil,x,k,m,n,t);
}

/* special gerepile for huge matrices */

#define COPY(x) {\
  GEN _t = (x); if (!is_universal_constant(_t)) x = gcopy(_t); \
}

INLINE GEN
_copy(void *E, GEN x)
{
  (void) E; COPY(x);
  return x;
}

static void
gerepile_gauss_ker(GEN x, long k, long t, pari_sp av)
{
  gen_gerepile_gauss_ker(x, k, t, av, NULL, &_copy);
}

static void
gerepile_gauss(GEN x,long k,long t,pari_sp av, long j, GEN c)
{
  pari_sp tetpil = avma, A, bot;
  long u,i, n = lg(x)-1, m = n? nbrows(x): 0;
  size_t dec;

  if (DEBUGMEM > 1) pari_warn(warnmem,"gauss_pivot. k=%ld, n=%ld",k,n);
  for (u=t+1; u<=m; u++)
    if (u==j || !c[u]) COPY(gcoeff(x,u,k));
  for (u=1; u<=m; u++)
    if (u==j || !c[u])
      for (i=k+1; i<=n; i++) COPY(gcoeff(x,u,i));

  (void)gerepile(av,tetpil,NULL); dec = av-tetpil;
  bot = pari_mainstack->bot;
  for (u=t+1; u<=m; u++)
    if (u==j || !c[u])
    {
      A=(pari_sp)coeff(x,u,k);
      if (A<av && A>=bot) coeff(x,u,k)+=dec;
    }
  for (u=1; u<=m; u++)
    if (u==j || !c[u])
      for (i=k+1; i<=n; i++)
      {
        A=(pari_sp)coeff(x,u,i);
        if (A<av && A>=bot) coeff(x,u,i)+=dec;
      }
}

/*******************************************************************/
/*                                                                 */
/*                         GENERIC                                 */
/*                                                                 */
/*******************************************************************/
GEN
gen_ker(GEN x, long deplin, void *E, const struct bb_field *ff)
{
  pari_sp av0 = avma, av, tetpil;
  GEN y, c, d;
  long i, j, k, r, t, n, m;

  n=lg(x)-1; if (!n) return cgetg(1,t_MAT);
  m=nbrows(x); r=0;
  x = RgM_shallowcopy(x);
  c = zero_zv(m);
  d=new_chunk(n+1);
  av=avma;
  for (k=1; k<=n; k++)
  {
    for (j=1; j<=m; j++)
      if (!c[j])
      {
        gcoeff(x,j,k) = ff->red(E, gcoeff(x,j,k));
        if (!ff->equal0(gcoeff(x,j,k))) break;
      }
    if (j>m)
    {
      if (deplin)
      {
        GEN c = cgetg(n+1, t_COL), g0 = ff->s(E,0), g1=ff->s(E,1);
        for (i=1; i<k; i++) gel(c,i) = ff->red(E, gcoeff(x,d[i],k));
        gel(c,k) = g1; for (i=k+1; i<=n; i++) gel(c,i) = g0;
        return gerepileupto(av0, c);
      }
      r++; d[k]=0;
      for(j=1; j<k; j++)
        if (d[j]) gcoeff(x,d[j],k) = gclone(gcoeff(x,d[j],k));
    }
    else
    {
      GEN piv = ff->neg(E,ff->inv(E,gcoeff(x,j,k)));
      c[j] = k; d[k] = j;
      gcoeff(x,j,k) = ff->s(E,-1);
      for (i=k+1; i<=n; i++) gcoeff(x,j,i) = ff->red(E,ff->mul(E,piv,gcoeff(x,j,i)));
      for (t=1; t<=m; t++)
      {
        if (t==j) continue;

        piv = ff->red(E,gcoeff(x,t,k));
        if (ff->equal0(piv)) continue;

        gcoeff(x,t,k) = ff->s(E,0);
        for (i=k+1; i<=n; i++)
           gcoeff(x,t,i) = ff->red(E, ff->add(E, gcoeff(x,t,i),
                                      ff->mul(E,piv,gcoeff(x,j,i))));
        if (gc_needed(av,1))
          gen_gerepile_gauss_ker(x,k,t,av,E,ff->red);
      }
    }
  }
  if (deplin) { avma = av0; return NULL; }

  tetpil=avma; y=cgetg(r+1,t_MAT);
  for (j=k=1; j<=r; j++,k++)
  {
    GEN C = cgetg(n+1,t_COL);
    GEN g0 = ff->s(E,0), g1 = ff->s(E,1);
    gel(y,j) = C; while (d[k]) k++;
    for (i=1; i<k; i++)
      if (d[i])
      {
        GEN p1=gcoeff(x,d[i],k);
        gel(C,i) = ff->red(E,p1); gunclone(p1);
      }
      else
        gel(C,i) = g0;
    gel(C,k) = g1; for (i=k+1; i<=n; i++) gel(C,i) = g0;
  }
  return gerepile(av0,tetpil,y);
}

GEN
gen_Gauss_pivot(GEN x, long *rr, void *E, const struct bb_field *ff)
{
  pari_sp av;
  GEN c, d;
  long i, j, k, r, t, m, n = lg(x)-1;

  if (!n) { *rr = 0; return NULL; }

  m=nbrows(x); r=0;
  d = cgetg(n+1, t_VECSMALL);
  x = RgM_shallowcopy(x);
  c = zero_zv(m);
  av=avma;
  for (k=1; k<=n; k++)
  {
    for (j=1; j<=m; j++)
      if (!c[j])
      {
        gcoeff(x,j,k) = ff->red(E,gcoeff(x,j,k));
        if (!ff->equal0(gcoeff(x,j,k))) break;
      }
    if (j>m) { r++; d[k]=0; }
    else
    {
      GEN piv = ff->neg(E,ff->inv(E,gcoeff(x,j,k)));
      GEN g0 = ff->s(E,0);
      c[j] = k; d[k] = j;
      for (i=k+1; i<=n; i++) gcoeff(x,j,i) = ff->red(E,ff->mul(E,piv,gcoeff(x,j,i)));
      for (t=1; t<=m; t++)
      {
        if (c[t]) continue; /* already a pivot on that line */

        piv = ff->red(E,gcoeff(x,t,k));
        if (ff->equal0(piv)) continue;
        gcoeff(x,t,k) = g0;
        for (i=k+1; i<=n; i++)
          gcoeff(x,t,i) = ff->red(E, ff->add(E,gcoeff(x,t,i), ff->mul(E,piv,gcoeff(x,j,i))));
        if (gc_needed(av,1))
          gerepile_gauss(x,k,t,av,j,c);
      }
      for (i=k; i<=n; i++) gcoeff(x,j,i) = g0; /* dummy */
    }
  }
  *rr = r; avma = (pari_sp)d; return d;
}

GEN
gen_det(GEN a, void *E, const struct bb_field *ff)
{
  pari_sp av = avma;
  long i,j,k, s = 1, nbco = lg(a)-1;
  GEN q, x = ff->s(E,1);
  if (!nbco) return x;
  a = RgM_shallowcopy(a);
  for (i=1; i<nbco; i++)
  {
    for(k=i; k<=nbco; k++)
    {
      gcoeff(a,k,i) = ff->red(E,gcoeff(a,k,i));
      if (!ff->equal0(gcoeff(a,k,i))) break;
    }
    if (k > nbco) return gerepileupto(av, gcoeff(a,i,i));
    if (k != i)
    { /* exchange the lines s.t. k = i */
      for (j=i; j<=nbco; j++) swap(gcoeff(a,i,j), gcoeff(a,k,j));
      s = -s;
    }
    q = gcoeff(a,i,i);

    x = ff->red(E,ff->mul(E,x,q));
    q = ff->inv(E,q);
    for (k=i+1; k<=nbco; k++)
    {
      GEN m = ff->red(E,gcoeff(a,i,k));
      if (ff->equal0(m)) continue;
      m = ff->neg(E, ff->red(E,ff->mul(E,m, q)));
      for (j=i+1; j<=nbco; j++)
        gcoeff(a,j,k) = ff->red(E,ff->add(E, gcoeff(a,j,k), ff->mul(E,m,gcoeff(a,j,i))));
      if (gc_needed(av,1))
      {
        if(DEBUGMEM>1) pari_warn(warnmem,"det. col = %ld",i);
        gerepileall(av,4, &a,&x,&q,&m);
      }
    }
  }
  if (s < 0) x = ff->neg(E,x);
  return gerepileupto(av, ff->red(E,ff->mul(E, x, gcoeff(a,nbco,nbco))));
}

INLINE void
_gen_addmul(GEN b, long k, long i, GEN m, void *E, const struct bb_field *ff)
{
  gel(b,i) = ff->red(E,gel(b,i));
  gel(b,k) = ff->add(E,gel(b,k), ff->mul(E,m, gel(b,i)));
}

static GEN
_gen_get_col(GEN a, GEN b, long li, void *E, const struct bb_field *ff)
{
  GEN u = cgetg(li+1,t_COL);
  pari_sp av = avma;
  long i, j;

  gel(u,li) = gerepileupto(av, ff->red(E,ff->mul(E,gel(b,li), gcoeff(a,li,li))));
  for (i=li-1; i>0; i--)
  {
    pari_sp av = avma;
    GEN m = gel(b,i);
    for (j=i+1; j<=li; j++) m = ff->add(E,m, ff->neg(E,ff->mul(E,gcoeff(a,i,j), gel(u,j))));
    m = ff->red(E, m);
    gel(u,i) = gerepileupto(av, ff->red(E,ff->mul(E,m, gcoeff(a,i,i))));
  }
  return u;
}

GEN
gen_Gauss(GEN a, GEN b, void *E, const struct bb_field *ff)
{
  long i, j, k, li, bco, aco;
  GEN u, g0 = ff->s(E,0);
  pari_sp av = avma;
  a = RgM_shallowcopy(a);
  b = RgM_shallowcopy(b);
  aco = lg(a)-1; bco = lg(b)-1; li = nbrows(a);
  for (i=1; i<=aco; i++)
  {
    GEN invpiv;
    for (k = i; k <= li; k++)
    {
      GEN piv = ff->red(E,gcoeff(a,k,i));
      if (!ff->equal0(piv)) { gcoeff(a,k,i) = ff->inv(E,piv); break; }
      gcoeff(a,k,i) = g0;
    }
    /* found a pivot on line k */
    if (k > li) return NULL;
    if (k != i)
    { /* swap lines so that k = i */
      for (j=i; j<=aco; j++) swap(gcoeff(a,i,j), gcoeff(a,k,j));
      for (j=1; j<=bco; j++) swap(gcoeff(b,i,j), gcoeff(b,k,j));
    }
    if (i == aco) break;

    invpiv = gcoeff(a,i,i); /* 1/piv mod p */
    for (k=i+1; k<=li; k++)
    {
      GEN m = ff->red(E,gcoeff(a,k,i)); gcoeff(a,k,i) = g0;
      if (ff->equal0(m)) continue;

      m = ff->red(E,ff->neg(E,ff->mul(E,m, invpiv)));
      for (j=i+1; j<=aco; j++) _gen_addmul(gel(a,j),k,i,m,E,ff);
      for (j=1  ; j<=bco; j++) _gen_addmul(gel(b,j),k,i,m,E,ff);
    }
    if (gc_needed(av,1))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"gen_Gauss. i=%ld",i);
      gerepileall(av,2, &a,&b);
    }
  }

  if(DEBUGLEVEL>4) err_printf("Solving the triangular system\n");
  u = cgetg(bco+1,t_MAT);
  for (j=1; j<=bco; j++) gel(u,j) = _gen_get_col(a, gel(b,j), aco, E, ff);
  return u;
}

/* compatible t_MAT * t_COL, lgA = lg(A) = lg(B) > 1, l = lgcols(A) */
static GEN
gen_matcolmul_i(GEN A, GEN B, ulong lgA, ulong l,
                void *E, const struct bb_field *ff)
{
  GEN C = cgetg(l, t_COL);
  ulong i;
  for (i = 1; i < l; i++) {
    pari_sp av = avma;
    GEN e = ff->mul(E, gcoeff(A, i, 1), gel(B, 1));
    ulong k;
    for(k = 2; k < lgA; k++)
      e = ff->add(E, e, ff->mul(E, gcoeff(A, i, k), gel(B, k)));
    gel(C, i) = gerepileupto(av, ff->red(E, e));
  }
  return C;
}

GEN
gen_matcolmul(GEN A, GEN B, void *E, const struct bb_field *ff)
{
  ulong lgA = lg(A);
  if (lgA != (ulong)lg(B))
    pari_err_OP("operation 'gen_matcolmul'", A, B);
  if (lgA == 1)
    return cgetg(1, t_COL);
  return gen_matcolmul_i(A, B, lgA, lgcols(A), E, ff);
}

GEN
gen_matmul(GEN A, GEN B, void *E, const struct bb_field *ff)
{
  ulong j, l, lgA, lgB = lg(B);
  GEN C;
  if (lgB == 1)
    return cgetg(1, t_MAT);
  lgA = lg(A);
  if (lgA != (ulong)lgcols(B))
    pari_err_OP("operation 'gen_matmul'", A, B);
  if (lgA == 1)
    return zeromat(0, lgB - 1);
  l = lgcols(A);
  C = cgetg(lgB, t_MAT);
  for(j = 1; j < lgB; j++)
    gel(C, j) = gen_matcolmul_i(A, gel(B, j), lgA, l, E, ff);
  return C;
}

static GEN
gen_colneg(GEN A, void *E, const struct bb_field *ff)
{
  long i, l;
  GEN B = cgetg_copy(A, &l);
  for (i = 1; i < l; i++)
    gel(B, i) = ff->neg(E, gel(A, i));
  return B;
}

static GEN
gen_matneg(GEN A, void *E, const struct bb_field *ff)
{
  long i, l;
  GEN B = cgetg_copy(A, &l);
  for (i = 1; i < l; i++)
    gel(B, i) = gen_colneg(gel(A, i), E, ff);
  return B;
}

/* assume dim A >= 1, A invertible + upper triangular  */
static GEN
gen_matinv_upper_ind(GEN A, long index, void *E, const struct bb_field *ff)
{
  long n = lg(A) - 1, i, j;
  GEN u = cgetg(n + 1, t_COL);
  for (i = n; i > index; i--)
    gel(u, i) = ff->s(E, 0);
  gel(u, i) = ff->inv(E, gcoeff(A, i, i));
  for (i--; i > 0; i--) {
    pari_sp av = avma;
    GEN m = ff->neg(E, ff->mul(E, gcoeff(A, i, i + 1), gel(u, i + 1)));
    for (j = i + 2; j <= n; j++)
      m = ff->add(E, m, ff->neg(E, ff->mul(E, gcoeff(A, i, j), gel(u, j))));
    gel(u, i) = gerepileupto(av, ff->red(E, ff->mul(E, m, ff->inv(E, gcoeff(A, i, i)))));
  }
  return u;
}

static GEN
gen_matinv_upper(GEN A, void *E, const struct bb_field *ff)
{
  long i, l;
  GEN B = cgetg_copy(A, &l);
  for (i = 1; i < l; i++)
    gel(B,i) = gen_matinv_upper_ind(A, i, E, ff);
  return B;
}

/* find z such that A z = y. Return NULL if no solution */
GEN
gen_matcolinvimage(GEN A, GEN y, void *E, const struct bb_field *ff)
{
  pari_sp av = avma;
  long i, l = lg(A);
  GEN M, x, t;

  M = gen_ker(shallowconcat(A, y), 0, E, ff);
  i = lg(M) - 1;
  if (!i) { avma = av; return NULL; }

  x = gel(M, i);
  t = gel(x, l);
  if (ff->equal0(t)) { avma = av; return NULL; }

  t = ff->neg(E, ff->inv(E, t));
  setlg(x, l);
  for (i = 1; i < l; i++)
    gel(x, i) = ff->red(E, ff->mul(E, t, gel(x, i)));
  return gerepilecopy(av, x);
}

/* find Z such that A Z = B. Return NULL if no solution */
GEN
gen_matinvimage(GEN A, GEN B, void *E, const struct bb_field *ff)
{
  pari_sp av = avma;
  GEN d, x, X, Y;
  long i, j, nY, nA, nB;
  x = gen_ker(shallowconcat(gen_matneg(A, E, ff), B), 0, E, ff);
  /* AX = BY, Y in strict upper echelon form with pivots = 1.
   * We must find T such that Y T = Id_nB then X T = Z. This exists
   * iff Y has at least nB columns and full rank. */
  nY = lg(x) - 1;
  nB = lg(B) - 1;
  if (nY < nB) { avma = av; return NULL; }
  nA = lg(A) - 1;
  Y = rowslice(x, nA + 1, nA + nB); /* nB rows */
  d = cgetg(nB + 1, t_VECSMALL);
  for (i = nB, j = nY; i >= 1; i--, j--) {
    for (; j >= 1; j--)
      if (!ff->equal0(gcoeff(Y, i, j))) { d[i] = j; break; }
    if (!j) { avma = av; return NULL; }
  }
  /* reduce to the case Y square, upper triangular with 1s on diagonal */
  Y = vecpermute(Y, d);
  x = vecpermute(x, d);
  X = rowslice(x, 1, nA);
  return gerepileupto(av, gen_matmul(X, gen_matinv_upper(Y, E, ff), E, ff));
}

static GEN
image_from_pivot(GEN x, GEN d, long r)
{
  GEN y;
  long j, k;

  if (!d) return gcopy(x);
  /* d left on stack for efficiency */
  r = lg(x)-1 - r; /* = dim Im(x) */
  y = cgetg(r+1,t_MAT);
  for (j=k=1; j<=r; k++)
    if (d[k]) gel(y,j++) = gcopy(gel(x,k));
  return y;
}

/*******************************************************************/
/*                                                                 */
/*                Echelon form and CUP decomposition               */
/*                                                                 */
/*******************************************************************/

/* By Peter Bruin, based on
  C.-P. Jeannerod, C. Pernet and A. Storjohann, Rank-profile revealing
  Gaussian elimination and the CUP matrix decomposition.  J. Symbolic
  Comput. 56 (2013), 46-68.

  Decompose an m x n-matrix A of rank r as C*U*P, with
  - C: m x r-matrix in column echelon form (not necessarily reduced)
       with all pivots equal to 1
  - U: upper-triangular r x n-matrix
  - P: permutation matrix
  The pivots of C and the known zeroes in C and U are not necessarily
  filled in; instead, we also return the vector R of pivot rows.
  Instead of the matrix P, we return the permutation p of [1..n]
  (t_VECSMALL) such that P[i,j] = 1 if and only if j = p[i].
*/

/* complement of a strictly increasing subsequence of (1, 2, ..., n) */
static GEN
indexcompl(GEN v, long n)
{
  long i, j, k, m = lg(v) - 1;
  GEN w = cgetg(n - m + 1, t_VECSMALL);
  for (i = j = k = 1; i <= n; i++)
    if (j <= m && v[j] == i) j++; else w[k++] = i;
  return w;
}

static GEN
Flm_rsolve_upper_1(GEN U, GEN B, ulong p)
{ return Flm_Fl_mul(B, Fl_inv(ucoeff(U, 1, 1), p), p); }

static GEN
Flm_rsolve_upper_2(GEN U, GEN B, ulong p)
{
  ulong a = ucoeff(U, 1, 1), b = ucoeff(U, 1, 2), d = ucoeff(U, 2, 2);
  ulong D = Fl_mul(a, d, p), Dinv = Fl_inv(D, p);
  ulong ainv = Fl_mul(d, Dinv, p), dinv = Fl_mul(a, Dinv, p);
  GEN B1 = rowslice(B, 1, 1);
  GEN B2 = rowslice(B, 2, 2);
  GEN X2 = Flm_Fl_mul(B2, dinv, p);
  GEN X1 = Flm_Fl_mul(Flm_sub(B1, Flm_Fl_mul(X2, b, p), p),
                      ainv, p);
  return vconcat(X1, X2);
}

/* solve U*X = B,  U upper triangular and invertible */
static GEN
Flm_rsolve_upper(GEN U, GEN B, ulong p)
{
  long n = lg(U) - 1, n1;
  GEN U2, U11, U12, U22, B1, B2, X1, X2, X;
  pari_sp av = avma;

  if (n == 0) return B;
  if (n == 1) return Flm_rsolve_upper_1(U, B, p);
  if (n == 2) return Flm_rsolve_upper_2(U, B, p);
  n1 = (n + 1)/2;
  U2 = vecslice(U, n1 + 1, n);
  U22 = rowslice(U2, n1 + 1, n);
  B2 = rowslice(B, n1 + 1, n);
  X2 = Flm_rsolve_upper(U22, B2, p);
  U12 = rowslice(U2, 1, n1);
  B1 = rowslice(B, 1, n1);
  B1 = Flm_sub(B1, Flm_mul(U12, X2, p), p);
  if (gc_needed(av, 1)) gerepileall(av, 2, &B1, &X2);
  U11 = matslice(U, 1,n1, 1,n1);
  X1 = Flm_rsolve_upper(U11, B1, p);
  X = vconcat(X1, X2);
  if (gc_needed(av, 1)) X = gerepilecopy(av, X);
  return X;
}

static GEN
Flm_lsolve_upper_1(GEN U, GEN B, ulong p)
{ return Flm_Fl_mul(B, Fl_inv(ucoeff(U, 1, 1), p), p); }

static GEN
Flm_lsolve_upper_2(GEN U, GEN B, ulong p)
{
  ulong a = ucoeff(U, 1, 1), b = ucoeff(U, 1, 2), d = ucoeff(U, 2, 2);
  ulong D = Fl_mul(a, d, p), Dinv = Fl_inv(D, p);
  ulong ainv = Fl_mul(d, Dinv, p), dinv = Fl_mul(a, Dinv, p);
  GEN B1 = vecslice(B, 1, 1);
  GEN B2 = vecslice(B, 2, 2);
  GEN X1 = Flm_Fl_mul(B1, ainv, p);
  GEN X2 = Flm_Fl_mul(Flm_sub(B2, Flm_Fl_mul(X1, b, p), p),
                      dinv, p);
  return shallowconcat(X1, X2);
}

/* solve X*U = B,  U upper triangular and invertible */
static GEN
Flm_lsolve_upper(GEN U, GEN B, ulong p)
{
  long n = lg(U) - 1, n1;
  GEN U2, U11, U12, U22, B1, B2, X1, X2, X;
  pari_sp av = avma;

  if (n == 0) return B;
  if (n == 1) return Flm_lsolve_upper_1(U, B, p);
  if (n == 2) return Flm_lsolve_upper_2(U, B, p);
  n1 = (n + 1)/2;
  U2 = vecslice(U, n1 + 1, n);
  U11 = matslice(U, 1,n1, 1,n1);
  U12 = rowslice(U2, 1, n1);
  U22 = rowslice(U2, n1 + 1, n);
  B1 = vecslice(B, 1, n1);
  B2 = vecslice(B, n1 + 1, n);
  X1 = Flm_lsolve_upper(U11, B1, p);
  B2 = Flm_sub(B2, Flm_mul(X1, U12, p), p);
  if (gc_needed(av, 1)) gerepileall(av, 3, &B2, &U22, &X1);
  X2 = Flm_lsolve_upper(U22, B2, p);
  X = shallowconcat(X1, X2);
  if (gc_needed(av, 1)) X = gerepilecopy(av, X);
  return X;
}

static GEN
Flm_rsolve_lower_unit_2(GEN L, GEN A, ulong p)
{
  GEN X1 = rowslice(A, 1, 1);
  GEN X2 = Flm_sub(rowslice(A, 2, 2),
                   Flm_Fl_mul(X1, ucoeff(L, 2, 1), p), p);
  return vconcat(X1, X2);
}

/* solve L*X = A,  L lower triangular with ones on the diagonal
* (at least as many rows as columns) */
static GEN
Flm_rsolve_lower_unit(GEN L, GEN A, ulong p)
{
  long m = lg(L) - 1, m1, n;
  GEN L1, L11, L21, L22, A1, A2, X1, X2, X;
  pari_sp av = avma;

  if (m == 0) return zero_Flm(0, lg(A) - 1);
  if (m == 1) return rowslice(A, 1, 1);
  if (m == 2) return Flm_rsolve_lower_unit_2(L, A, p);
  m1 = (m + 1)/2;
  n = nbrows(L);
  L1 = vecslice(L, 1, m1);
  L11 = rowslice(L1, 1, m1);
  L21 = rowslice(L1, m1 + 1, n);
  A1 = rowslice(A, 1, m1);
  X1 = Flm_rsolve_lower_unit(L11, A1, p);
  A2 = rowslice(A, m1 + 1, n);
  A2 = Flm_sub(A2, Flm_mul(L21, X1, p), p);
  if (gc_needed(av, 1)) gerepileall(av, 2, &A2, &X1);
  L22 = matslice(L, m1+1,n, m1+1,m);
  X2 = Flm_rsolve_lower_unit(L22, A2, p);
  X = vconcat(X1, X2);
  if (gc_needed(av, 1)) X = gerepilecopy(av, X);
  return X;
}

static GEN
Flm_lsolve_lower_unit_2(GEN L, GEN A, ulong p)
{
  GEN X2 = vecslice(A, 2, 2);
  GEN X1 = Flm_sub(vecslice(A, 1, 1),
                   Flm_Fl_mul(X2, ucoeff(L, 2, 1), p), p);
  return shallowconcat(X1, X2);
}

/* solve L*X = A,  L square lower triangular with ones on the diagonal */
static GEN
Flm_lsolve_lower_unit(GEN L, GEN A, ulong p)
{
  long m = lg(L) - 1, m1;
  GEN L1, L2, L11, L21, L22, A1, A2, X1, X2, X;
  pari_sp av = avma;

  if (m <= 1) return A;
  if (m == 2) return Flm_lsolve_lower_unit_2(L, A, p);
  m1 = (m + 1)/2;
  L2 = vecslice(L, m1 + 1, m);
  L22 = rowslice(L2, m1 + 1, m);
  A2 = vecslice(A, m1 + 1, m);
  X2 = Flm_lsolve_lower_unit(L22, A2, p);
  if (gc_needed(av, 1)) X2 = gerepilecopy(av, X2);
  L1 = vecslice(L, 1, m1);
  L21 = rowslice(L1, m1 + 1, m);
  A1 = vecslice(A, 1, m1);
  A1 = Flm_sub(A1, Flm_mul(X2, L21, p), p);
  L11 = rowslice(L1, 1, m1);
  if (gc_needed(av, 1)) gerepileall(av, 3, &A1, &L11, &X2);
  X1 = Flm_lsolve_lower_unit(L11, A1, p);
  X = shallowconcat(X1, X2);
  if (gc_needed(av, 1)) X = gerepilecopy(av, X);
  return X;
}

/* destroy A */
static long
Flm_CUP_gauss(GEN A, GEN *R, GEN *C, GEN *U, GEN *P, ulong p)
{
  long i, j, k, m = nbrows(A), n = lg(A) - 1, pr, pc, u, v;

  if (P) *P = identity_perm(n);
  *R = cgetg(m + 1, t_VECSMALL);
  for (j = 1, pr = 0; j <= n; j++)
  {
    for (pr++, pc = 0; pr <= m; pr++)
    {
      for (k = j; k <= n; k++) { v = ucoeff(A, pr, k); if (!pc && v) pc = k; }
      if (pc) break;
    }
    if (!pc) break;
    (*R)[j] = pr;
    if (pc != j)
    {
      swap(gel(A, j), gel(A, pc));
      if (P) lswap((*P)[j], (*P)[pc]);
    }
    u = Fl_inv(ucoeff(A, pr, j), p);
    for (i = pr + 1; i <= m; i++)
    {
      v = Fl_mul(ucoeff(A, i, j), u, p);
      ucoeff(A, i, j) = v;
      for (k = j + 1; k <= n; k++)
        ucoeff(A, i, k) = Fl_sub(ucoeff(A, i, k),
                                 Fl_mul(ucoeff(A, pr, k), v, p), p);
    }
  }
  setlg(*R, j);
  *C = vecslice(A, 1, j - 1);
  if (U) *U = rowpermute(A, *R);
  return j - 1;
}

static const long Flm_CUP_LIMIT = 8;

static ulong
Flm_CUP(GEN A, GEN *R, GEN *C, GEN *U, GEN *P, ulong p)
{
  long m = nbrows(A), m1, n = lg(A) - 1, i, r1, r2, r;
  GEN R1, C1, U1, P1, R2, C2, U2, P2;
  GEN A1, A2, B2, C21, U11, U12, T21, T22;
  pari_sp av = avma;

  if (m < Flm_CUP_LIMIT || n < Flm_CUP_LIMIT)
    /* destroy A; not called at the outermost recursion level */
    return Flm_CUP_gauss(A, R, C, U, P, p);
  m1 = (minss(m, n) + 1)/2;
  A1 = rowslice(A, 1, m1);
  A2 = rowslice(A, m1 + 1, m);
  r1 = Flm_CUP(A1, &R1, &C1, &U1, &P1, p);
  if (r1 == 0)
  {
    r2 = Flm_CUP(A2, &R2, &C2, &U2, &P2, p);
    *R = cgetg(r2 + 1, t_VECSMALL);
    for (i = 1; i <= r2; i++) (*R)[i] = R2[i] + m1;
    *C = vconcat(zero_Flm(m1, r2), C2);
    *U = U2;
    *P = P2;
    r = r2;
  }
  else
  {
    U11 = vecslice(U1, 1, r1);
    U12 = vecslice(U1, r1 + 1, n);
    T21 = vecslicepermute(A2, P1, 1, r1);
    T22 = vecslicepermute(A2, P1, r1 + 1, n);
    C21 = Flm_lsolve_upper(U11, T21, p);
    if (gc_needed(av, 1))
      gerepileall(av, 7, &R1, &C1, &P1, &U11, &U12, &T22, &C21);
    B2 = Flm_sub(T22, Flm_mul(C21, U12, p), p);
    r2 = Flm_CUP(B2, &R2, &C2, &U2, &P2, p);
    r = r1 + r2;
    *R = cgetg(r + 1, t_VECSMALL);
    for (i = 1; i <= r1; i++) (*R)[i] = R1[i];
    for (;      i <= r; i++)  (*R)[i] = R2[i - r1] + m1;
    *C = shallowconcat(vconcat(C1, C21),
                       vconcat(zero_Flm(m1, r2), C2));
    *U = shallowconcat(vconcat(U11, zero_Flm(r2, r1)),
                       vconcat(vecpermute(U12, P2), U2));
    *P = cgetg(n + 1, t_VECSMALL);
    for (i = 1; i <= r1; i++) (*P)[i] = P1[i];
    for (; i <= n; i++)       (*P)[i] = P1[P2[i - r1] + r1];
  }
  if (gc_needed(av, 1)) gerepileall(av, 4, R, C, U, P);
  return r;
}

static ulong
Flm_echelon_gauss(GEN A, GEN *R, GEN *C, ulong p)
{ return Flm_CUP_gauss(A, R, C, NULL, NULL, p); }

/* column echelon form */
static ulong
Flm_echelon(GEN A, GEN *R, GEN *C, ulong p)
{
  long j, j1, j2, m = nbrows(A), n = lg(A) - 1, n1, r, r1, r2;
  GEN A1, A2, R1, R1c, C1, R2, C2;
  GEN A12, A22, B2, C11, C21, M12;
  pari_sp av = avma;

  if (m < Flm_CUP_LIMIT || n < Flm_CUP_LIMIT)
    return Flm_echelon_gauss(Flm_copy(A), R, C, p);

  n1 = (n + 1)/2;
  A1 = vecslice(A, 1, n1);
  A2 = vecslice(A, n1 + 1, n);
  r1 = Flm_echelon(A1, &R1, &C1, p);
  if (!r1) return Flm_echelon(A2, R, C, p);
  if (r1 == m) { *R = R1; *C = C1; return r1; }

  R1c = indexcompl(R1, m);
  C11 = rowpermute(C1, R1);
  C21 = rowpermute(C1, R1c);
  A12 = rowpermute(A2, R1);
  A22 = rowpermute(A2, R1c);
  M12 = Flm_rsolve_lower_unit(C11, A12, p);
  B2 = Flm_sub(A22, Flm_mul(C21, M12, p), p);
  r2 = Flm_echelon(B2, &R2, &C2, p);
  if (!r2) { *R = R1; *C = C1; r = r1; }
  else
  {
    R2 = perm_mul(R1c, R2);
    C2 = rowpermute(vconcat(zero_Flm(r1, r2), C2),
                    perm_inv(vecsmall_concat(R1, R1c)));
    r = r1 + r2;
    *R = cgetg(r + 1, t_VECSMALL);
    *C = cgetg(r + 1, t_MAT);
    for (j = j1 = j2 = 1; j <= r; j++)
      if (j2 > r2 || (j1 <= r1 && R1[j1] < R2[j2]))
      {
        gel(*C, j) = gel(C1, j1);
        (*R)[j] = R1[j1++];
      }
      else
      {
        gel(*C, j) = gel(C2, j2);
        (*R)[j] = R2[j2++];
      }
  }
  if (gc_needed(av, 1)) gerepileall(av, 2, R, C);
  return r;
}

static GEN
FlxqM_rsolve_upper_1(GEN U, GEN B, GEN T, ulong p)
{ return FlxqM_Flxq_mul(B, Flxq_inv(gcoeff(U, 1, 1), T, p), T, p);
}

static GEN
FlxqM_rsolve_upper_2(GEN U, GEN B, GEN T, ulong p)
{
  GEN a = gcoeff(U, 1, 1), b = gcoeff(U, 1, 2), d = gcoeff(U, 2, 2);
  GEN D = Flxq_mul(a, d, T, p), Dinv = Flxq_inv(D, T, p);
  GEN ainv = Flxq_mul(d, Dinv, T, p), dinv = Flxq_mul(a, Dinv, T, p);
  GEN B1 = rowslice(B, 1, 1);
  GEN B2 = rowslice(B, 2, 2);
  GEN X2 = FlxqM_Flxq_mul(B2, dinv, T, p);
  GEN X1 = FlxqM_Flxq_mul(FlxM_sub(B1, FlxqM_Flxq_mul(X2, b, T, p), p),
                          ainv, T, p);
  return vconcat(X1, X2);
}

/* solve U*X = B,  U upper triangular and invertible */
static GEN
FlxqM_rsolve_upper(GEN U, GEN B, GEN T, ulong p)
{
  long n = lg(U) - 1, n1;
  GEN U2, U11, U12, U22, B1, B2, X1, X2, X;
  pari_sp av = avma;

  if (n == 0) return B;
  if (n == 1) return FlxqM_rsolve_upper_1(U, B, T, p);
  if (n == 2) return FlxqM_rsolve_upper_2(U, B, T, p);
  n1 = (n + 1)/2;
  U2 = vecslice(U, n1 + 1, n);
  U11 = matslice(U, 1,n1, 1,n1);
  U12 = rowslice(U2, 1, n1);
  U22 = rowslice(U2, n1 + 1, n);
  B1 = rowslice(B, 1, n1);
  B2 = rowslice(B, n1 + 1, n);
  X2 = FlxqM_rsolve_upper(U22, B2, T, p);
  B1 = FlxM_sub(B1, FlxqM_mul(U12, X2, T, p), p);
  if (gc_needed(av, 1)) gerepileall(av, 3, &B1, &U11, &X2);
  X1 = FlxqM_rsolve_upper(U11, B1, T, p);
  X = vconcat(X1, X2);
  if (gc_needed(av, 1)) X = gerepilecopy(av, X);
  return X;
}

static GEN
FlxqM_lsolve_upper_1(GEN U, GEN B, GEN T, ulong p)
{ return FlxqM_Flxq_mul(B, Flxq_inv(gcoeff(U, 1, 1), T, p), T, p); }

static GEN
FlxqM_lsolve_upper_2(GEN U, GEN B, GEN T, ulong p)
{
  GEN a = gcoeff(U, 1, 1), b = gcoeff(U, 1, 2), d = gcoeff(U, 2, 2);
  GEN D = Flxq_mul(a, d, T, p), Dinv = Flxq_inv(D, T, p);
  GEN ainv = Flxq_mul(d, Dinv, T, p), dinv = Flxq_mul(a, Dinv, T, p);
  GEN B1 = vecslice(B, 1, 1);
  GEN B2 = vecslice(B, 2, 2);
  GEN X1 = FlxqM_Flxq_mul(B1, ainv, T, p);
  GEN X2 = FlxqM_Flxq_mul(FlxM_sub(B2, FlxqM_Flxq_mul(X1, b, T, p), p),
                          dinv, T, p);
  return shallowconcat(X1, X2);
}

/* solve X*U = B,  U upper triangular and invertible */
static GEN
FlxqM_lsolve_upper(GEN U, GEN B, GEN T, ulong p)
{
  long n = lg(U) - 1, n1;
  GEN U2, U11, U12, U22, B1, B2, X1, X2, X;
  pari_sp av = avma;

  if (n == 0) return B;
  if (n == 1) return FlxqM_lsolve_upper_1(U, B, T, p);
  if (n == 2) return FlxqM_lsolve_upper_2(U, B, T, p);
  n1 = (n + 1)/2;
  U2 = vecslice(U, n1 + 1, n);
  U11 = matslice(U, 1,n1, 1,n1);
  U12 = rowslice(U2, 1, n1);
  U22 = rowslice(U2, n1 + 1, n);
  B1 = vecslice(B, 1, n1);
  B2 = vecslice(B, n1 + 1, n);
  X1 = FlxqM_lsolve_upper(U11, B1, T, p);
  B2 = FlxM_sub(B2, FlxqM_mul(X1, U12, T, p), p);
  if (gc_needed(av, 1)) gerepileall(av, 3, &B2, &U22, &X1);
  X2 = FlxqM_lsolve_upper(U22, B2, T, p);
  X = shallowconcat(X1, X2);
  if (gc_needed(av, 1)) X = gerepilecopy(av, X);
  return X;
}

static GEN
FlxqM_rsolve_lower_unit_2(GEN L, GEN A, GEN T, ulong p)
{
  GEN X1 = rowslice(A, 1, 1);
  GEN X2 = FlxM_sub(rowslice(A, 2, 2),
                    FlxqM_Flxq_mul(X1, gcoeff(L, 2, 1), T, p), p);
  return vconcat(X1, X2);
}

/* solve L*X = A,  L lower triangular with ones on the diagonal
 * (at least as many rows as columns) */
static GEN
FlxqM_rsolve_lower_unit(GEN L, GEN A, GEN T, ulong p)
{
  long m = lg(L) - 1, m1, n;
  GEN L1, L11, L21, L22, A1, A2, X1, X2, X;
  pari_sp av = avma;

  if (m == 0) return zeromat(0, lg(A) - 1);
  if (m == 1) return rowslice(A, 1, 1);
  if (m == 2) return FlxqM_rsolve_lower_unit_2(L, A, T, p);
  m1 = (m + 1)/2;
  n = nbrows(L);
  L1 = vecslice(L, 1, m1);
  L11 = rowslice(L1, 1, m1);
  L21 = rowslice(L1, m1 + 1, n);
  A1 = rowslice(A, 1, m1);
  A2 = rowslice(A, m1 + 1, n);
  X1 = FlxqM_rsolve_lower_unit(L11, A1, T, p);
  A2 = FlxM_sub(A2, FlxqM_mul(L21, X1, T, p), p);
  if (gc_needed(av, 1)) gerepileall(av, 2, &A2, &X1);
  L22 = matslice(L, m1+1,n, m1+1,m);
  X2 = FlxqM_rsolve_lower_unit(L22, A2, T, p);
  X = vconcat(X1, X2);
  if (gc_needed(av, 1)) X = gerepilecopy(av, X);
  return X;
}

static GEN
FlxqM_lsolve_lower_unit_2(GEN L, GEN A, GEN T, ulong p)
{
  GEN X2 = vecslice(A, 2, 2);
  GEN X1 = FlxM_sub(vecslice(A, 1, 1),
                    FlxqM_Flxq_mul(X2, gcoeff(L, 2, 1), T, p), p);
  return shallowconcat(X1, X2);
}

/* solve L*X = A,  L square lower triangular with ones on the diagonal */
static GEN
FlxqM_lsolve_lower_unit(GEN L, GEN A, GEN T, ulong p)
{
  long m = lg(L) - 1, m1;
  GEN L1, L2, L11, L21, L22, A1, A2, X1, X2, X;
  pari_sp av = avma;

  if (m <= 1) return A;
  if (m == 2) return FlxqM_lsolve_lower_unit_2(L, A, T, p);
  m1 = (m + 1)/2;
  L1 = vecslice(L, 1, m1);
  L2 = vecslice(L, m1 + 1, m);
  L11 = rowslice(L1, 1, m1);
  L21 = rowslice(L1, m1 + 1, m);
  L22 = rowslice(L2, m1 + 1, m);
  A1 = vecslice(A, 1, m1);
  A2 = vecslice(A, m1 + 1, m);
  X2 = FlxqM_lsolve_lower_unit(L22, A2, T, p);
  A1 = FlxM_sub(A1, FlxqM_mul(X2, L21, T, p), p);
  if (gc_needed(av, 1)) gerepileall(av, 3, &A1, &L11, &X2);
  X1 = FlxqM_lsolve_lower_unit(L11, A1, T, p);
  X = shallowconcat(X1, X2);
  if (gc_needed(av, 1)) X = gerepilecopy(av, X);
  return X;
}

/* destroy A */
static long
FlxqM_CUP_gauss(GEN A, GEN *R, GEN *C, GEN *U, GEN *P, GEN T, ulong p)
{
  long i, j, k, m = nbrows(A), n = lg(A) - 1, pr, pc;
  pari_sp av;
  GEN u, v;

  if (P) *P = identity_perm(n);
  *R = cgetg(m + 1, t_VECSMALL);
  av = avma;
  for (j = 1, pr = 0; j <= n; j++)
  {
    for (pr++, pc = 0; pr <= m; pr++)
    {
      for (k = j; k <= n; k++)
      {
        v = Flx_rem(gcoeff(A, pr, k), T, p);
        gcoeff(A, pr, k) = v;
        if (!pc && lgpol(v) > 0) pc = k;
      }
      if (pc) break;
    }
    if (!pc) break;
    (*R)[j] = pr;
    if (pc != j)
    {
      swap(gel(A, j), gel(A, pc));
      if (P) lswap((*P)[j], (*P)[pc]);
    }
    u = Flxq_inv(gcoeff(A, pr, j), T, p);
    for (i = pr + 1; i <= m; i++)
    {
      v = Flxq_mul(gcoeff(A, i, j), u, T, p);
      gcoeff(A, i, j) = v;
      for (k = j + 1; k <= n; k++)
        gcoeff(A, i, k) = Flx_sub(gcoeff(A, i, k),
                                  Flx_mul(gcoeff(A, pr, k), v, p), p);
    }
    if (gc_needed(av, 2)) A = gerepilecopy(av, A);
  }
  setlg(*R, j);
  *C = vecslice(A, 1, j - 1);
  if (U) *U = rowpermute(A, *R);
  return j - 1;
}

static const long FlxqM_CUP_LIMIT = 5;

static ulong
FlxqM_CUP(GEN A, GEN *R, GEN *C, GEN *U, GEN *P, GEN T, ulong p)
{
  long m = nbrows(A), m1, n = lg(A) - 1, i, r1, r2, r, sv;
  GEN R1, C1, U1, P1, R2, C2, U2, P2;
  GEN A1, A2, B2, C21, U11, U12, T21, T22;
  pari_sp av = avma;

  if (m < FlxqM_CUP_LIMIT || n < FlxqM_CUP_LIMIT)
    /* destroy A; not called at the outermost recursion level */
    return FlxqM_CUP_gauss(A, R, C, U, P, T, p);
  sv = get_Flx_var(T);
  m1 = (minss(m, n) + 1)/2;
  A1 = rowslice(A, 1, m1);
  A2 = rowslice(A, m1 + 1, m);
  r1 = FlxqM_CUP(A1, &R1, &C1, &U1, &P1, T, p);
  if (r1 == 0)
  {
    r2 = FlxqM_CUP(A2, &R2, &C2, &U2, &P2, T, p);
    *R = cgetg(r2 + 1, t_VECSMALL);
    for (i = 1; i <= r2; i++) (*R)[i] = R2[i] + m1;
    *C = vconcat(zero_FlxM(m1, r2, sv), C2);
    *U = U2;
    *P = P2;
    r = r2;
  }
  else
  {
    U11 = vecslice(U1, 1, r1);
    U12 = vecslice(U1, r1 + 1, n);
    T21 = vecslicepermute(A2, P1, 1, r1);
    T22 = vecslicepermute(A2, P1, r1 + 1, n);
    C21 = FlxqM_lsolve_upper(U11, T21, T, p);
    if (gc_needed(av, 1))
      gerepileall(av, 7, &R1, &C1, &P1, &U11, &U12, &T22, &C21);
    B2 = FlxM_sub(T22, FlxqM_mul(C21, U12, T, p), p);
    r2 = FlxqM_CUP(B2, &R2, &C2, &U2, &P2, T, p);
    r = r1 + r2;
    *R = cgetg(r + 1, t_VECSMALL);
    for (i = 1; i <= r1; i++) (*R)[i] = R1[i];
    for (     ; i <= r; i++)  (*R)[i] = R2[i - r1] + m1;
    *C = shallowmatconcat(mkmat2(mkcol2(C1, C21),
                                 mkcol2(zero_FlxM(m1, r2, sv), C2)));
    *U = shallowmatconcat(mkmat2(mkcol2(U11, zero_FlxM(r2, r1, sv)),
                                 mkcol2(vecpermute(U12, P2), U2)));
    *P = cgetg(n + 1, t_VECSMALL);
    for (i = 1; i <= r1; i++) (*P)[i] = P1[i];
    for (     ; i <= n; i++)  (*P)[i] = P1[P2[i - r1] + r1];
  }
  if (gc_needed(av, 1)) gerepileall(av, 4, R, C, U, P);
  return r;
}

static ulong
FlxqM_echelon_gauss(GEN A, GEN *R, GEN *C, GEN T, ulong p)
{ return FlxqM_CUP_gauss(A, R, C, NULL, NULL, T, p); }

/* column echelon form */
static ulong
FlxqM_echelon(GEN A, GEN *R, GEN *C, GEN T, ulong p)
{
  long j, j1, j2, m = nbrows(A), n = lg(A) - 1, n1, r, r1, r2;
  GEN A1, A2, R1, R1c, C1, R2, C2;
  GEN A12, A22, B2, C11, C21, M12;
  pari_sp av = avma;

  if (m < FlxqM_CUP_LIMIT || n < FlxqM_CUP_LIMIT)
    return FlxqM_echelon_gauss(shallowcopy(A), R, C, T, p);

  n1 = (n + 1)/2;
  A1 = vecslice(A, 1, n1);
  A2 = vecslice(A, n1 + 1, n);
  r1 = FlxqM_echelon(A1, &R1, &C1, T, p);
  if (!r1) return FlxqM_echelon(A2, R, C, T, p);
  if (r1 == m) { *R = R1; *C = C1; return r1; }
  R1c = indexcompl(R1, m);
  C11 = rowpermute(C1, R1);
  C21 = rowpermute(C1, R1c);
  A12 = rowpermute(A2, R1);
  A22 = rowpermute(A2, R1c);
  M12 = FlxqM_rsolve_lower_unit(C11, A12, T, p);
  B2 = FlxM_sub(A22, FlxqM_mul(C21, M12, T, p), p);
  r2 = FlxqM_echelon(B2, &R2, &C2, T, p);
  if (!r2) { *R = R1; *C = C1; r = r1; }
  else
  {
    R2 = perm_mul(R1c, R2);
    C2 = rowpermute(vconcat(zero_FlxM(r1, r2, get_Flx_var(T)), C2),
                    perm_inv(vecsmall_concat(R1, R1c)));
    r = r1 + r2;
    *R = cgetg(r + 1, t_VECSMALL);
    *C = cgetg(r + 1, t_MAT);
    for (j = j1 = j2 = 1; j <= r; j++)
    {
      if (j2 > r2 || (j1 <= r1 && R1[j1] < R2[j2]))
      {
        gel(*C, j) = gel(C1, j1);
        (*R)[j] = R1[j1++];
      }
      else
      {
        gel(*C, j) = gel(C2, j2);
        (*R)[j] = R2[j2++];
      }
    }
  }
  if (gc_needed(av, 1)) gerepileall(av, 2, R, C);
  return r;
}

/*******************************************************************/
/*                                                                 */
/*                    LINEAR ALGEBRA MODULO P                      */
/*                                                                 */
/*******************************************************************/

static long
F2v_find_nonzero(GEN x0, GEN mask0, long m)
{
  ulong *x = (ulong *)x0+2, *mask = (ulong *)mask0+2, e;
  long i, l = lg(x0)-2;
  for (i = 0; i < l; i++)
  {
    e = *x++ & *mask++;
    if (e) return i*BITS_IN_LONG+vals(e)+1;
  }
  return m+1;
}

/* in place, destroy x */
GEN
F2m_ker_sp(GEN x, long deplin)
{
  GEN y, c, d;
  long i, j, k, r, m, n;

  n = lg(x)-1;
  m = mael(x,1,1); r=0;

  d = cgetg(n+1, t_VECSMALL);
  c = const_F2v(m);
  for (k=1; k<=n; k++)
  {
    GEN xk = gel(x,k);
    j = F2v_find_nonzero(xk, c, m);
    if (j>m)
    {
      if (deplin) {
        GEN c = zero_F2v(n);
        for (i=1; i<k; i++)
          if (F2v_coeff(xk, d[i]))
            F2v_set(c, i);
        F2v_set(c, k);
        return c;
      }
      r++; d[k] = 0;
    }
    else
    {
      F2v_clear(c,j); d[k] = j;
      F2v_clear(xk, j);
      for (i=k+1; i<=n; i++)
      {
        GEN xi = gel(x,i);
        if (F2v_coeff(xi,j)) F2v_add_inplace(xi, xk);
      }
      F2v_set(xk, j);
    }
  }
  if (deplin) return NULL;

  y = zero_F2m_copy(n,r);
  for (j=k=1; j<=r; j++,k++)
  {
    GEN C = gel(y,j); while (d[k]) k++;
    for (i=1; i<k; i++)
      if (d[i] && F2m_coeff(x,d[i],k))
        F2v_set(C,i);
    F2v_set(C, k);
  }
  return y;
}

static void /* assume m < p */
_Fl_addmul(GEN b, long k, long i, ulong m, ulong p, ulong pi)
{
  uel(b,k) = Fl_addmul_pre(uel(b, k), m, uel(b, i), p, pi);
}
static void /* same m = 1 */
_Fl_add(GEN b, long k, long i, ulong p)
{
  uel(b,k) = Fl_add(uel(b,k), uel(b,i), p);
}
static void /* assume m < p && SMALL_ULONG(p) && (! (b[i] & b[k] & HIGHMASK)) */
_Fl_addmul_OK(GEN b, long k, long i, ulong m, ulong p)
{
  uel(b,k) += m * uel(b,i);
  if (uel(b,k) & HIGHMASK) uel(b,k) %= p;
}
static void /* assume SMALL_ULONG(p) && (! (b[i] & b[k] & HIGHMASK)) */
_Fl_add_OK(GEN b, long k, long i, ulong p)
{
  uel(b,k) += uel(b,i);
  if (uel(b,k) & HIGHMASK) uel(b,k) %= p;
}

static GEN
Flm_ker_gauss_OK(GEN x, ulong p, long deplin)
{
  GEN y, c, d;
  long i, j, k, r, t, m, n;
  ulong a;

  n = lg(x)-1;
  m=nbrows(x); r=0;

  c = zero_zv(m);
  d = cgetg(n+1, t_VECSMALL);
  a = 0; /* for gcc -Wall */
  for (k=1; k<=n; k++)
  {
    for (j=1; j<=m; j++)
      if (!c[j])
      {
        a = ucoeff(x,j,k) % p;
        if (a) break;
      }
    if (j > m)
    {
      if (deplin==1) {
        c = cgetg(n+1, t_VECSMALL);
        for (i=1; i<k; i++) c[i] = ucoeff(x,d[i],k) % p;
        c[k] = 1; for (i=k+1; i<=n; i++) c[i] = 0;
        return c;
      }
      r++; d[k] = 0;
    }
    else
    {
      ulong piv = p - Fl_inv(a, p); /* -1/a */
      c[j] = k; d[k] = j;
      ucoeff(x,j,k) = p-1;
      if (piv != 1)
        for (i=k+1; i<=n; i++) ucoeff(x,j,i) = (piv * ucoeff(x,j,i)) % p;
      for (t=1; t<=m; t++)
      {
        if (t == j) continue;

        piv = ( ucoeff(x,t,k) %= p );
        if (!piv) continue;
        if (piv == 1)
          for (i=k+1; i<=n; i++) _Fl_add_OK(gel(x,i),t,j, p);
        else
          for (i=k+1; i<=n; i++) _Fl_addmul_OK(gel(x,i),t,j,piv, p);
      }
    }
  }
  if (deplin==1) return NULL;

  y = cgetg(r+1, t_MAT);
  for (j=k=1; j<=r; j++,k++)
  {
    GEN C = cgetg(n+1, t_VECSMALL);

    gel(y,j) = C; while (d[k]) k++;
    for (i=1; i<k; i++)
      if (d[i])
        uel(C,i) = ucoeff(x,d[i],k) % p;
      else
        uel(C,i) = 0UL;
    uel(C,k) = 1UL; for (i=k+1; i<=n; i++) uel(C,i) = 0UL;
  }
  if (deplin == 2) {
    GEN pc = cgetg(n - r + 1, t_VECSMALL);  /* indices of pivot columns */
    for (i = j = 1; j <= n; j++)
      if (d[j]) pc[i++] = j;
    return mkvec2(y, pc);
  }
  return y;
}

/* in place, destroy x */
static GEN
Flm_ker_gauss(GEN x, ulong p, long deplin)
{
  GEN y, c, d;
  long i, j, k, r, t, m, n;
  ulong a, pi;
  n = lg(x)-1;
  if (!n) return cgetg(1,t_MAT);
  if (SMALL_ULONG(p)) return Flm_ker_gauss_OK(x, p, deplin);
  pi = get_Fl_red(p);

  m=nbrows(x); r=0;

  c = zero_zv(m);
  d = cgetg(n+1, t_VECSMALL);
  a = 0; /* for gcc -Wall */
  for (k=1; k<=n; k++)
  {
    for (j=1; j<=m; j++)
      if (!c[j])
      {
        a = ucoeff(x,j,k);
        if (a) break;
      }
    if (j > m)
    {
      if (deplin==1) {
        c = cgetg(n+1, t_VECSMALL);
        for (i=1; i<k; i++) c[i] = ucoeff(x,d[i],k);
        c[k] = 1; for (i=k+1; i<=n; i++) c[i] = 0;
        return c;
      }
      r++; d[k] = 0;
    }
    else
    {
      ulong piv = p - Fl_inv(a, p); /* -1/a */
      c[j] = k; d[k] = j;
      ucoeff(x,j,k) = p-1;
      if (piv != 1)
        for (i=k+1; i<=n; i++)
          ucoeff(x,j,i) = Fl_mul_pre(piv, ucoeff(x,j,i), p, pi);
      for (t=1; t<=m; t++)
      {
        if (t == j) continue;

        piv = ucoeff(x,t,k);
        if (!piv) continue;
        if (piv == 1)
          for (i=k+1; i<=n; i++) _Fl_add(gel(x,i),t,j,p);
        else
          for (i=k+1; i<=n; i++) _Fl_addmul(gel(x,i),t,j,piv,p, pi);
      }
    }
  }
  if (deplin==1) return NULL;

  y = cgetg(r+1, t_MAT);
  for (j=k=1; j<=r; j++,k++)
  {
    GEN C = cgetg(n+1, t_VECSMALL);

    gel(y,j) = C; while (d[k]) k++;
    for (i=1; i<k; i++)
      if (d[i])
        uel(C,i) = ucoeff(x,d[i],k);
      else
        uel(C,i) = 0UL;
    uel(C,k) = 1UL; for (i=k+1; i<=n; i++) uel(C,i) = 0UL;
  }
  if (deplin == 2) {
    GEN pc = cgetg(n - r + 1, t_VECSMALL);  /* indices of pivot columns */
    for (i = j = 1; j <= n; j++)
      if (d[j]) pc[i++] = j;
    return mkvec2(y, pc);
  }
  return y;
}

GEN
FpM_intersect(GEN x, GEN y, GEN p)
{
  pari_sp av = avma;
  long j, lx = lg(x);
  GEN z;

  if (lx==1 || lg(y)==1) return cgetg(1,t_MAT);
  z = FpM_ker(shallowconcat(x,y), p);
  for (j=lg(z)-1; j; j--) setlg(gel(z,j),lx);
  return gerepileupto(av, FpM_mul(x,z,p));
}
GEN
Flm_intersect(GEN x, GEN y, ulong p)
{
  pari_sp av = avma;
  long j, lx = lg(x);
  GEN z;

  if (lx==1 || lg(y)==1) return cgetg(1,t_MAT);
  z = Flm_ker(shallowconcat(x,y), p);
  for (j=lg(z)-1; j; j--) setlg(gel(z,j),lx);
  return gerepileupto(av, Flm_mul(x,z,p));
}

/* not memory clean */
GEN
F2m_ker(GEN x) { return F2m_ker_sp(F2m_copy(x), 0); }
GEN
F2m_deplin(GEN x) { return F2m_ker_sp(F2m_copy(x), 1); }

static GEN
Flm_ker_echelon(GEN x, ulong p, long pivots) {
  pari_sp av = avma;
  GEN R, Rc, C, C1, C2, S, K;
  long n = lg(x) - 1, r;
  r = Flm_echelon(Flm_transpose(x), &R, &C, p);
  Rc = indexcompl(R, n);
  C1 = rowpermute(C, R);
  C2 = rowpermute(C, Rc);
  S = Flm_lsolve_lower_unit(C1, C2, p);
  K = vecpermute(shallowconcat(Flm_neg(S, p), matid_Flm(n - r)),
                 perm_inv(vecsmall_concat(R, Rc)));
  K = Flm_transpose(K);
  if (pivots)
    return gerepilecopy(av, mkvec2(K, R));
  return gerepileupto(av, K);
}

static GEN
Flm_deplin_echelon(GEN x, ulong p) {
  pari_sp av = avma;
  GEN R, Rc, C, C1, C2, s, v;
  long i, n = lg(x) - 1, r;
  r = Flm_echelon(Flm_transpose(x), &R, &C, p);
  if (r == n) { avma = av; return NULL; }
  Rc = indexcompl(R, n);
  i = Rc[1];
  C1 = rowpermute(C, R);
  C2 = rowslice(C, i, i);
  s = Flm_row(Flm_lsolve_lower_unit(C1, C2, p), 1);
  v = vecsmallpermute(vecsmall_concat(Flv_neg(s, p), vecsmall_ei(n - r, 1)),
                 perm_inv(vecsmall_concat(R, Rc)));
  return gerepileuptoleaf(av, v);
}

static GEN
Flm_ker_i(GEN x, ulong p, long deplin, long inplace) {
  if (lg(x) - 1 >= Flm_CUP_LIMIT && nbrows(x) >= Flm_CUP_LIMIT)
    switch(deplin) {
    case 0: return Flm_ker_echelon(x, p, 0);
    case 1: return Flm_deplin_echelon(x, p);
    case 2: return Flm_ker_echelon(x, p, 1);
    }
  return Flm_ker_gauss(inplace? x: Flm_copy(x), p, deplin);
}

GEN
Flm_ker_sp(GEN x, ulong p, long deplin) {
  return Flm_ker_i(x, p, deplin, 1);
}

GEN
Flm_ker(GEN x, ulong p) {
  return Flm_ker_i(x, p, 0, 0);
}

GEN
Flm_deplin(GEN x, ulong p) {
  return Flm_ker_i(x, p, 1, 0);
}

ulong
F2m_det_sp(GEN x) { return !F2m_ker_sp(x, 1); }

ulong
F2m_det(GEN x)
{
  pari_sp av = avma;
  ulong d = F2m_det_sp(F2m_copy(x));
  avma = av; return d;
}

/* in place, destroy a, SMALL_ULONG(p) is TRUE */
static ulong
Flm_det_gauss_OK(GEN a, long nbco, ulong p)
{
  long i,j,k, s = 1;
  ulong q, x = 1;

  for (i=1; i<nbco; i++)
  {
    for(k=i; k<=nbco; k++)
    {
      ulong c = ucoeff(a,k,i) % p;
      ucoeff(a,k,i) = c;
      if (c) break;
    }
    for(j=k+1; j<=nbco; j++) ucoeff(a,j,i) %= p;
    if (k > nbco) return ucoeff(a,i,i);
    if (k != i)
    { /* exchange the lines s.t. k = i */
      for (j=i; j<=nbco; j++) lswap(ucoeff(a,i,j), ucoeff(a,k,j));
      s = -s;
    }
    q = ucoeff(a,i,i);

    if (x & HIGHMASK) x %= p;
    x *= q;
    q = Fl_inv(q,p);
    for (k=i+1; k<=nbco; k++)
    {
      ulong m = ucoeff(a,i,k) % p;
      if (!m) continue;

      m = p - ((m*q)%p);
      for (j=i+1; j<=nbco; j++)
      {
        ulong c = ucoeff(a,j,k);
        if (c & HIGHMASK) c %= p;
        ucoeff(a,j,k) = c  + m*ucoeff(a,j,i);
      }
    }
  }
  if (x & HIGHMASK) x %= p;
  q = ucoeff(a,nbco,nbco);
  if (q & HIGHMASK) q %= p;
  x = (x*q) % p;
  if (s < 0 && x) x = p - x;
  return x;
}

/* in place, destroy a */
static ulong
Flm_det_gauss(GEN a, ulong p)
{
  long i,j,k, s = 1, nbco = lg(a)-1;
  ulong pi, q, x = 1;

  if (SMALL_ULONG(p)) return Flm_det_gauss_OK(a, nbco, p);
  pi = get_Fl_red(p);
  for (i=1; i<nbco; i++)
  {
    for(k=i; k<=nbco; k++)
      if (ucoeff(a,k,i)) break;
    if (k > nbco) return ucoeff(a,i,i);
    if (k != i)
    { /* exchange the lines s.t. k = i */
      for (j=i; j<=nbco; j++) lswap(ucoeff(a,i,j), ucoeff(a,k,j));
      s = -s;
    }
    q = ucoeff(a,i,i);

    x = Fl_mul_pre(x, q, p, pi);
    q = Fl_inv(q,p);
    for (k=i+1; k<=nbco; k++)
    {
      ulong m = ucoeff(a,i,k);
      if (!m) continue;

      m = Fl_mul_pre(m, q, p, pi);
      for (j=i+1; j<=nbco; j++)
        ucoeff(a,j,k) = Fl_sub(ucoeff(a,j,k), Fl_mul_pre(m,ucoeff(a,j,i), p, pi), p);
    }
  }
  if (s < 0) x = Fl_neg(x, p);
  return Fl_mul(x, ucoeff(a,nbco,nbco), p);
}

static ulong
Flm_det_CUP(GEN a, ulong p) {
  GEN R, C, U, P;
  long d, i, n = lg(a) - 1, r;
  r = Flm_CUP(a, &R, &C, &U, &P, p);
  if (r < n)
    d = 0;
  else {
    d = perm_sign(P) == 1? 1: p-1;
    for (i = 1; i <= n; i++)
      d = Fl_mul(d, ucoeff(U, i, i), p);
  }
  return d;
}

static ulong
Flm_det_i(GEN x, ulong p, long inplace) {
  pari_sp av = avma;
  ulong d;
  if (lg(x) - 1 >= Flm_CUP_LIMIT)
    d = Flm_det_CUP(x, p);
  else
    d = Flm_det_gauss(inplace? x: Flm_copy(x), p);
  avma = av; return d;
}

ulong
Flm_det_sp(GEN x, ulong p) {
  return Flm_det_i(x, p, 1);
}

ulong
Flm_det(GEN x, ulong p) {
  return Flm_det_i(x, p, 0);
}

static GEN
FpM_init(GEN a, GEN p, ulong *pp)
{
  if (lgefint(p) == 3)
  {
    *pp = uel(p,2);
    return (*pp==2)? ZM_to_F2m(a): ZM_to_Flm(a, *pp);
  }
  *pp = 0; return a;
}
GEN
RgM_Fp_init(GEN a, GEN p, ulong *pp)
{
  if (lgefint(p) == 3)
  {
    *pp = uel(p,2);
    return (*pp==2)? RgM_to_F2m(a): RgM_to_Flm(a, *pp);
  }
  *pp = 0; return RgM_to_FpM(a,p);
}

static GEN
FpM_det_gen(GEN a, GEN p)
{
  void *E;
  const struct bb_field *S = get_Fp_field(&E,p);
  return gen_det(a, E, S);
}
GEN
FpM_det(GEN a, GEN p)
{
  pari_sp av = avma;
  ulong pp, d;
  a = FpM_init(a, p, &pp);
  switch(pp)
  {
  case 0: return FpM_det_gen(a, p);
  case 2: d = F2m_det_sp(a); break;
  default:d = Flm_det_sp(a,pp); break;
  }
  avma = av; return utoi(d);
}

/* Destroy x */
static GEN
F2m_gauss_pivot(GEN x, long *rr)
{
  GEN c, d;
  long i, j, k, r, m, n;

  n = lg(x)-1; if (!n) { *rr=0; return NULL; }
  m = mael(x,1,1); r=0;

  d = cgetg(n+1, t_VECSMALL);
  c = const_F2v(m);
  for (k=1; k<=n; k++)
  {
    GEN xk = gel(x,k);
    j = F2v_find_nonzero(xk, c, m);
    if (j>m) { r++; d[k] = 0; }
    else
    {
      F2v_clear(c,j); d[k] = j;
      for (i=k+1; i<=n; i++)
      {
        GEN xi = gel(x,i);
        if (F2v_coeff(xi,j)) F2v_add_inplace(xi, xk);
      }
    }
  }

  *rr = r; avma = (pari_sp)d; return d;
}

/* Destroy x */
static GEN
Flm_gauss_pivot(GEN x, ulong p, long *rr)
{
  GEN c,d;
  long i,j,k,r,t,n,m;

  n=lg(x)-1; if (!n) { *rr=0; return NULL; }

  m=nbrows(x); r=0;
  d=cgetg(n+1,t_VECSMALL);
  c = zero_zv(m);
  for (k=1; k<=n; k++)
  {
    for (j=1; j<=m; j++)
      if (!c[j])
      {
        ucoeff(x,j,k) %= p;
        if (ucoeff(x,j,k)) break;
      }
    if (j>m) { r++; d[k]=0; }
    else
    {
      ulong piv = p - Fl_inv(ucoeff(x,j,k), p);
      c[j]=k; d[k]=j;
      for (i=k+1; i<=n; i++)
        ucoeff(x,j,i) = Fl_mul(piv, ucoeff(x,j,i), p);
      for (t=1; t<=m; t++)
        if (!c[t]) /* no pivot on that line yet */
        {
          piv = ucoeff(x,t,k);
          if (piv)
          {
            ucoeff(x,t,k) = 0;
            for (i=k+1; i<=n; i++)
              ucoeff(x,t,i) = Fl_add(ucoeff(x,t,i),
                                     Fl_mul(piv,ucoeff(x,j,i),p),p);
          }
        }
      for (i=k; i<=n; i++) ucoeff(x,j,i) = 0; /* dummy */
    }
  }
  *rr = r; avma = (pari_sp)d; return d;
}

static GEN
Flm_pivots_CUP(GEN x, ulong p, long *rr) {
  pari_sp av;
  long i, n = lg(x) - 1, r;
  GEN R, C, U, P, d = zero_zv(n);
  av = avma;
  r = Flm_CUP(x, &R, &C, &U, &P, p);
  for(i = 1; i <= r; i++)
    d[P[i]] = R[i];
  avma = av;
  *rr = n - r;
  return d;
}

static GEN
Flm_pivots(GEN x, ulong p, long *rr, long inplace) {
  if (lg(x) - 1 >= Flm_CUP_LIMIT && nbrows(x) >= Flm_CUP_LIMIT)
    return Flm_pivots_CUP(x, p, rr);
  return Flm_gauss_pivot(inplace? x: Flm_copy(x), p, rr);
}

static GEN
FpM_gauss_pivot_gen(GEN x, GEN p, long *rr)
{
  void *E;
  const struct bb_field *S = get_Fp_field(&E,p);
  return gen_Gauss_pivot(x, rr, E, S);
}
static GEN
FpM_gauss_pivot(GEN x, GEN p, long *rr)
{
  ulong pp;
  if (lg(x)==1) { *rr = 0; return NULL; }
  x = FpM_init(x, p, &pp);
  switch(pp)
  {
  case 0: return FpM_gauss_pivot_gen(x, p, rr);
  case 2: return F2m_gauss_pivot(x, rr);
  default:return Flm_pivots(x, pp, rr, 1);
  }
}

GEN
FpM_image(GEN x, GEN p)
{
  long r;
  GEN d = FpM_gauss_pivot(x,p,&r); /* d left on stack for efficiency */
  return image_from_pivot(x,d,r);
}

GEN
Flm_image(GEN x, ulong p)
{
  long r;
  GEN d = Flm_pivots(x, p, &r, 0); /* d left on stack for efficiency */
  return image_from_pivot(x,d,r);
}

GEN
F2m_image(GEN x)
{
  long r;
  GEN d = F2m_gauss_pivot(F2m_copy(x),&r); /* d left on stack for efficiency */
  return image_from_pivot(x,d,r);
}

long
FpM_rank(GEN x, GEN p)
{
  pari_sp av = avma;
  long r;
  (void)FpM_gauss_pivot(x,p,&r);
  avma = av; return lg(x)-1 - r;
}

long
Flm_rank(GEN x, ulong p)
{
  pari_sp av = avma;
  long r;
  if (lg(x) - 1 >= Flm_CUP_LIMIT && nbrows(x) >= Flm_CUP_LIMIT) {
    GEN R, C;
    r = Flm_echelon(x, &R, &C, p);
    avma = av; return r;
  }
  (void) Flm_pivots(x, p, &r, 0);
  avma = av; return lg(x)-1 - r;
}

long
F2m_rank(GEN x)
{
  pari_sp av = avma;
  long r;
  (void)F2m_gauss_pivot(F2m_copy(x),&r);
  avma = av; return lg(x)-1 - r;
}

static GEN
FlxqM_gauss_pivot(GEN x, GEN T, ulong p, long *rr)
{
  void *E;
  const struct bb_field *S = get_Flxq_field(&E, T, p);
  return gen_Gauss_pivot(x, rr, E, S);
}

static GEN
FlxqM_pivots_CUP(GEN x, GEN T, ulong p, long *rr) {
  pari_sp av;
  long i, n = lg(x) - 1, r;
  GEN R, C, U, P, d = zero_zv(n);
  av = avma;
  r = FlxqM_CUP(x, &R, &C, &U, &P, T, p);
  for(i = 1; i <= r; i++)
    d[P[i]] = R[i];
  avma = av;
  *rr = n - r;
  return d;
}

static GEN
FlxqM_pivots(GEN x, GEN T, ulong p, long *rr) {
  if (lg(x) - 1 >= FlxqM_CUP_LIMIT && nbrows(x) >= FlxqM_CUP_LIMIT)
    return FlxqM_pivots_CUP(x, T, p, rr);
  return FlxqM_gauss_pivot(x, T, p, rr);
}

GEN
FlxqM_image(GEN x, GEN T, ulong p)
{
  long r;
  GEN d = FlxqM_pivots(x, T, p, &r); /* d left on stack for efficiency */
  return image_from_pivot(x,d,r);
}

long
FlxqM_rank(GEN x, GEN T, ulong p)
{
  pari_sp av = avma;
  long r;
  if (lg(x) - 1 >= FlxqM_CUP_LIMIT && nbrows(x) >= FlxqM_CUP_LIMIT) {
    GEN R, C;
    r = FlxqM_echelon(x, &R, &C, T, p);
    avma = av; return r;
  }
  (void) FlxqM_pivots(x, T, p, &r);
  avma = av; return lg(x)-1 - r;
}

static GEN
FlxqM_det_gen(GEN a, GEN T, ulong p)
{
  void *E;
  const struct bb_field *S = get_Flxq_field(&E, T, p);
  return gen_det(a, E, S);
}

static GEN
FlxqM_det_CUP(GEN a, GEN T, ulong p) {
  pari_sp av = avma;
  GEN R, C, U, P, d;
  long i, n = lg(a) - 1, r, sv = get_Flx_var(T);
  r = FlxqM_CUP(a, &R, &C, &U, &P, T, p);
  if (r < n)
    d = pol0_Flx(sv);
  else {
    d = mkvecsmall2(sv, perm_sign(P) == 1? 1: p - 1);
    for (i = 1; i <= n; i++)
      d = Flxq_mul(d, gcoeff(U, i, i), T, p);
  }
  return gerepileuptoleaf(av, d);
}

GEN
FlxqM_det(GEN a, GEN T, ulong p) {
  if (lg(a) - 1 >= FlxqM_CUP_LIMIT)
    return FlxqM_det_CUP(a, T, p);
  else
    return FlxqM_det_gen(a, T, p);
}

GEN
FlxqM_FlxqC_invimage(GEN A, GEN B, GEN T, ulong p) {
  void *E;
  const struct bb_field *ff = get_Flxq_field(&E, T, p);
  return gen_matcolinvimage(A, B, E, ff);
}

GEN
FlxqM_FlxqC_mul(GEN A, GEN B, GEN T, ulong p) {
  void *E;
  const struct bb_field *ff = get_Flxq_field(&E, T, p);
  return gen_matcolmul(A, B, E, ff);
}

GEN
FlxqM_mul(GEN A, GEN B, GEN T, ulong p) {
  void *E;
  const struct bb_field *ff;
  long n = lg(A) - 1;

  if (n == 0)
    return cgetg(1, t_MAT);
  if (n > 1)
    return FlxqM_mul_Kronecker(A, B, T, p);
  ff = get_Flxq_field(&E, T, p);
  return gen_matmul(A, B, E, ff);
}

static GEN
FlxqM_invimage_gen(GEN A, GEN B, GEN T, ulong p) {
  void *E;
  const struct bb_field *ff = get_Flxq_field(&E, T, p);
  return gen_matinvimage(A, B, E, ff);
}

static GEN
FlxqM_invimage_CUP(GEN A, GEN B, GEN T, ulong p) {
  pari_sp av = avma;
  GEN R, Rc, C, U, P, B1, B2, C1, C2, X, Y, Z;
  long r, sv = get_Flx_var(T);
  r = FlxqM_CUP(A, &R, &C, &U, &P, T, p);
  Rc = indexcompl(R, nbrows(B));
  C1 = rowpermute(C, R);
  C2 = rowpermute(C, Rc);
  B1 = rowpermute(B, R);
  B2 = rowpermute(B, Rc);
  Z = FlxqM_rsolve_lower_unit(C1, B1, T, p);
  if (!gequal(FlxqM_mul(C2, Z, T, p), B2))
    return NULL;
  Y = vconcat(FlxqM_rsolve_upper(vecslice(U, 1, r), Z, T, p),
              zero_FlxM(lg(A) - 1 - r, lg(B) - 1, sv));
  X = rowpermute(Y, perm_inv(P));
  return gerepilecopy(av, X);
}

GEN
FlxqM_invimage(GEN A, GEN B, GEN T, ulong p) {
  long nA = lg(A)-1, nB = lg(B)-1;

  if (!nB) return cgetg(1, t_MAT);
  if (nA + nB >= FlxqM_CUP_LIMIT && nbrows(B) >= FlxqM_CUP_LIMIT)
    return FlxqM_invimage_CUP(A, B, T, p);
  return FlxqM_invimage_gen(A, B, T, p);
}

GEN
F2xqM_det(GEN a, GEN T)
{
  void *E;
  const struct bb_field *S = get_F2xq_field(&E, T);
  return gen_det(a, E, S);
}

static GEN
F2xqM_gauss_gen(GEN a, GEN b, GEN T)
{
  void *E;
  const struct bb_field *S = get_F2xq_field(&E, T);
  return gen_Gauss(a, b, E, S);
}

GEN
F2xqM_gauss(GEN a, GEN b, GEN T)
{
  pari_sp av = avma;
  long n = lg(a)-1;
  GEN u;
  if (!n || lg(b)==1) { avma = av; return cgetg(1, t_MAT); }
  u = F2xqM_gauss_gen(a, b, T);
  if (!u) { avma = av; return NULL; }
  return gerepilecopy(av, u);
}

GEN
F2xqM_inv(GEN a, GEN T)
{
  pari_sp av = avma;
  GEN u;
  if (lg(a) == 1) { avma = av; return cgetg(1, t_MAT); }
  u = F2xqM_gauss_gen(a, matid_F2xqM(nbrows(a),T), T);
  if (!u) { avma = av; return NULL; }
  return gerepilecopy(av, u);
}

GEN
F2xqM_F2xqC_gauss(GEN a, GEN b, GEN T)
{
  pari_sp av = avma;
  GEN u;
  if (lg(a) == 1) return cgetg(1, t_COL);
  u = F2xqM_gauss_gen(a, mkmat(b), T);
  if (!u) { avma = av; return NULL; }
  return gerepilecopy(av, gel(u,1));
}

GEN
F2xqM_F2xqC_invimage(GEN A, GEN B, GEN T) {
  void *E;
  const struct bb_field *ff = get_F2xq_field(&E, T);
  return gen_matcolinvimage(A, B, E, ff);
}

GEN
F2xqM_F2xqC_mul(GEN A, GEN B, GEN T) {
  void *E;
  const struct bb_field *ff = get_F2xq_field(&E, T);
  return gen_matcolmul(A, B, E, ff);
}

GEN
F2xqM_mul(GEN A, GEN B, GEN T) {
  void *E;
  const struct bb_field *ff = get_F2xq_field(&E, T);
  return gen_matmul(A, B, E, ff);
}

GEN
F2xqM_invimage(GEN A, GEN B, GEN T) {
  void *E;
  const struct bb_field *ff = get_F2xq_field(&E, T);
  return gen_matinvimage(A, B, E, ff);
}

static GEN
FqM_gauss_pivot_gen(GEN x, GEN T, GEN p, long *rr)
{
  void *E;
  const struct bb_field *S = get_Fq_field(&E,T,p);
  return gen_Gauss_pivot(x, rr, E, S);
}
static GEN
FqM_gauss_pivot(GEN x, GEN T, GEN p, long *rr)
{
  if (lg(x)==1) { *rr = 0; return NULL; }
  if (!T) return FpM_gauss_pivot(x, p, rr);
  if (lgefint(p) == 3)
  {
    pari_sp av = avma;
    ulong pp = uel(p,2);
    GEN Tp = ZXT_to_FlxT(T, pp);
    GEN d = FlxqM_gauss_pivot(FqM_to_FlxM(x, T, p), Tp, pp, rr);
    return d ? gerepileuptoleaf(av, d): d;
  }
  return FqM_gauss_pivot_gen(x, T, p, rr);
}

GEN
FqM_image(GEN x, GEN T, GEN p)
{
  long r;
  GEN d = FqM_gauss_pivot(x,T,p,&r); /* d left on stack for efficiency */
  return image_from_pivot(x,d,r);
}

long
FqM_rank(GEN x, GEN T, GEN p)
{
  pari_sp av = avma;
  long r;
  (void)FqM_gauss_pivot(x,T,p,&r);
  avma = av; return lg(x)-1 - r;
}

GEN
FqM_det(GEN x, GEN T, GEN p)
{
  void *E;
  const struct bb_field *S = get_Fq_field(&E,T,p);
  return gen_det(x, E, S);
}

GEN
FqM_FqC_invimage(GEN A, GEN B, GEN T, GEN p) {
  void *E;
  const struct bb_field *ff = get_Fq_field(&E, T, p);
  return gen_matcolinvimage(A, B, E, ff);
}

GEN
FqM_FqC_mul(GEN A, GEN B, GEN T, GEN p) {
  void *E;
  const struct bb_field *ff = get_Fq_field(&E, T, p);
  return gen_matcolmul(A, B, E, ff);
}

GEN
FqM_mul(GEN A, GEN B, GEN T, GEN p) {
  void *E;
  long n = lg(A) - 1;
  const struct bb_field *ff;
  if (n == 0)
    return cgetg(1, t_MAT);
  if (n > 1)
    return FqM_mul_Kronecker(A, B, T, p);
  ff = get_Fq_field(&E, T, p);
  return gen_matmul(A, B, E, ff);
}

GEN
FqM_invimage(GEN A, GEN B, GEN T, GEN p) {
  void *E;
  const struct bb_field *ff = get_Fq_field(&E, T, p);
  return gen_matinvimage(A, B, E, ff);
}

static GEN
FpM_ker_gen(GEN x, GEN p, long deplin)
{
  void *E;
  const struct bb_field *S = get_Fp_field(&E,p);
  return gen_ker(x, deplin, E, S);
}
static GEN
FpM_ker_i(GEN x, GEN p, long deplin)
{
  pari_sp av = avma;
  ulong pp;
  GEN y;

  if (lg(x)==1) return cgetg(1,t_MAT);
  x = FpM_init(x, p, &pp);
  switch(pp)
  {
  case 0: return FpM_ker_gen(x,p,deplin);
  case 2:
    y = F2m_ker_sp(x, deplin);
    if (!y) return y;
    y = deplin? F2c_to_ZC(y): F2m_to_ZM(y);
    return gerepileupto(av, y);
  default:
    y = Flm_ker_sp(x, pp, deplin);
    if (!y) return y;
    y = deplin? Flc_to_ZC(y): Flm_to_ZM(y);
    return gerepileupto(av, y);
  }
}

GEN
FpM_ker(GEN x, GEN p) { return FpM_ker_i(x,p,0); }

GEN
FpM_deplin(GEN x, GEN p) { return FpM_ker_i(x,p,1); }

static GEN
FqM_ker_gen(GEN x, GEN T, GEN p, long deplin)
{
  void *E;
  const struct bb_field *S = get_Fq_field(&E,T,p);
  return gen_ker(x,deplin,E,S);
}
static GEN
FqM_ker_i(GEN x, GEN T, GEN p, long deplin)
{
  if (!T) return FpM_ker_i(x,p,deplin);
  if (lg(x)==1) return cgetg(1,t_MAT);

  if (lgefint(p)==3)
  {
    pari_sp ltop=avma;
    ulong l= p[2];
    GEN Ml = FqM_to_FlxM(x, T, p);
    GEN Tl = ZXT_to_FlxT(T,l);
    GEN p1 = FlxM_to_ZXM(FlxqM_ker(Ml,Tl,l));
    return gerepileupto(ltop,p1);
  }
  return FqM_ker_gen(x, T, p, deplin);
}

GEN
FqM_ker(GEN x, GEN T, GEN p) { return FqM_ker_i(x,T,p,0); }

GEN
FqM_deplin(GEN x, GEN T, GEN p) { return FqM_ker_i(x,T,p,1); }

static GEN
FlxqM_ker_gen(GEN x, GEN T, ulong p, long deplin)
{
  const struct bb_field *ff;
  void *E;

  if (lg(x)==1) return cgetg(1,t_MAT);
  ff=get_Flxq_field(&E,T,p);
  return gen_ker(x,deplin, E, ff);
}

static GEN
FlxqM_ker_echelon(GEN x, GEN T, ulong p) {
  pari_sp av = avma;
  GEN R, Rc, C, C1, C2, S, K;
  long n = lg(x) - 1, r;
  r = FlxqM_echelon(shallowtrans(x), &R, &C, T, p);
  Rc = indexcompl(R, n);
  C1 = rowpermute(C, R);
  C2 = rowpermute(C, Rc);
  S = FlxqM_lsolve_lower_unit(C1, C2, T, p);
  K = vecpermute(shallowconcat(FlxM_neg(S, p), matid_FlxqM(n - r, T, p)),
                 perm_inv(vecsmall_concat(R, Rc)));
  K = shallowtrans(K);
  return gerepilecopy(av, K);
}

static GEN
col_ei_FlxC(long n, long i, long sv) {
  GEN v = zero_FlxC(n, sv);
  gel(v, i) = pol1_Flx(sv);
  return v;
}

static GEN
FlxqM_deplin_echelon(GEN x, GEN T, ulong p) {
  pari_sp av = avma;
  GEN R, Rc, C, C1, C2, s, v;
  long i, n = lg(x) - 1, r, sv = get_Flx_var(T);
  r = FlxqM_echelon(shallowtrans(x), &R, &C, T, p);
  if (r == n) { avma = av; return NULL; }
  Rc = indexcompl(R, n);
  i = Rc[1];
  C1 = rowpermute(C, R);
  C2 = rowslice(C, i, i);
  s = row(FlxqM_lsolve_lower_unit(C1, C2, T, p), 1);
  settyp(s, t_COL);
  v = vecpermute(shallowconcat(FlxC_neg(s, p), col_ei_FlxC(n - r, 1, sv)),
                 perm_inv(vecsmall_concat(R, Rc)));
  return gerepilecopy(av, v);
}

static GEN
FlxqM_ker_i(GEN x, GEN T, ulong p, long deplin) {
  if (lg(x) - 1 >= FlxqM_CUP_LIMIT && nbrows(x) >= FlxqM_CUP_LIMIT)
    return deplin? FlxqM_deplin_echelon(x, T, p): FlxqM_ker_echelon(x, T, p);
  return FlxqM_ker_gen(x, T, p, deplin);
}

GEN
FlxqM_ker(GEN x, GEN T, ulong p)
{
  return FlxqM_ker_i(x, T, p, 0);
}

GEN
FlxqM_deplin(GEN x, GEN T, ulong p)
{
  return FlxqM_ker_i(x, T, p, 1);
}

static GEN
F2xqM_ker_i(GEN x, GEN T, long deplin)
{
  const struct bb_field *ff;
  void *E;

  if (lg(x)==1) return cgetg(1,t_MAT);
  ff = get_F2xq_field(&E,T);
  return gen_ker(x,deplin, E, ff);
}

GEN
F2xqM_ker(GEN x, GEN T)
{
  return F2xqM_ker_i(x, T, 0);
}

GEN
F2xqM_deplin(GEN x, GEN T)
{
  return F2xqM_ker_i(x, T, 1);
}

static GEN
F2xqM_gauss_pivot(GEN x, GEN T, long *rr)
{
  void *E;
  const struct bb_field *S = get_F2xq_field(&E,T);
  return gen_Gauss_pivot(x, rr, E, S);
}
GEN
F2xqM_image(GEN x, GEN T)
{
  long r;
  GEN d = F2xqM_gauss_pivot(x,T,&r); /* d left on stack for efficiency */
  return image_from_pivot(x,d,r);
}
long
F2xqM_rank(GEN x, GEN T)
{
  pari_sp av = avma;
  long r;
  (void)F2xqM_gauss_pivot(x,T,&r);
  avma = av; return lg(x)-1 - r;
}
/*******************************************************************/
/*                                                                 */
/*                       Solve A*X=B (Gauss pivot)                 */
/*                                                                 */
/*******************************************************************/
/* x ~ 0 compared to reference y */
int
approx_0(GEN x, GEN y)
{
  long tx = typ(x);
  if (tx == t_COMPLEX)
    return approx_0(gel(x,1), y) && approx_0(gel(x,2), y);
  return gequal0(x) ||
         (tx == t_REAL && gexpo(y) - gexpo(x) > bit_prec(x));
}
/* x a column, x0 same column in the original input matrix (for reference),
 * c list of pivots so far */
static long
gauss_get_pivot_max(GEN X, GEN X0, long ix, GEN c)
{
  GEN p, r, x = gel(X,ix), x0 = gel(X0,ix);
  long i, k = 0, ex = - (long)HIGHEXPOBIT, lx = lg(x);
  if (c)
  {
    for (i=1; i<lx; i++)
      if (!c[i])
      {
        long e = gexpo(gel(x,i));
        if (e > ex) { ex = e; k = i; }
      }
  }
  else
  {
    for (i=ix; i<lx; i++)
    {
      long e = gexpo(gel(x,i));
      if (e > ex) { ex = e; k = i; }
    }
  }
  if (!k) return lx;
  p = gel(x,k);
  r = gel(x0,k); if (isrationalzero(r)) r = x0;
  return approx_0(p, r)? lx: k;
}
static long
gauss_get_pivot_padic(GEN X, GEN p, long ix, GEN c)
{
  GEN x = gel(X, ix);
  long i, k = 0, ex = (long)HIGHVALPBIT, lx = lg(x);
  if (c)
  {
    for (i=1; i<lx; i++)
      if (!c[i] && !gequal0(gel(x,i)))
      {
        long e = gvaluation(gel(x,i), p);
        if (e < ex) { ex = e; k = i; }
      }
  }
  else
  {
    for (i=ix; i<lx; i++)
      if (!gequal0(gel(x,i)))
      {
        long e = gvaluation(gel(x,i), p);
        if (e < ex) { ex = e; k = i; }
      }
  }
  return k? k: lx;
}
static long
gauss_get_pivot_NZ(GEN X, GEN x0/*unused*/, long ix, GEN c)
{
  GEN x = gel(X, ix);
  long i, lx = lg(x);
  (void)x0;
  if (c)
  {
    for (i=1; i<lx; i++)
      if (!c[i] && !gequal0(gel(x,i))) return i;
  }
  else
  {
    for (i=ix; i<lx; i++)
      if (!gequal0(gel(x,i))) return i;
  }
  return lx;
}

/* Return pivot seeking function appropriate for the domain of the RgM x
 * (first non zero pivot, maximal pivot...)
 * x0 is a reference point used when guessing whether x[i,j] ~ 0
 * (iff x[i,j] << x0[i,j]); typical case: mateigen, Gauss pivot on x - vp.Id,
 * but use original x when deciding whether a prospective pivot is non-0 */
static pivot_fun
get_pivot_fun(GEN x, GEN x0, GEN *data)
{
  long i, j, hx, lx = lg(x);
  int res = t_INT;
  GEN p = NULL;

  *data = NULL;
  if (lx == 1) return &gauss_get_pivot_NZ;
  hx = lgcols(x);
  for (j=1; j<lx; j++)
  {
    GEN xj = gel(x,j);
    for (i=1; i<hx; i++)
    {
      GEN c = gel(xj,i);
      switch(typ(c))
      {
        case t_REAL:
          res = t_REAL;
          break;
        case t_COMPLEX:
          if (typ(gel(c,1)) == t_REAL || typ(gel(c,2)) == t_REAL) res = t_REAL;
          break;
        case t_INT: case t_INTMOD: case t_FRAC: case t_FFELT: case t_QUAD:
        case t_POLMOD: /* exact types */
          break;
        case t_PADIC:
          p = gel(c,2);
          res = t_PADIC;
          break;
        default: return &gauss_get_pivot_NZ;
      }
    }
  }
  switch(res)
  {
    case t_REAL: *data = x0; return &gauss_get_pivot_max;
    case t_PADIC: *data = p; return &gauss_get_pivot_padic;
    default: return &gauss_get_pivot_NZ;
  }
}

static GEN
get_col(GEN a, GEN b, GEN p, long li)
{
  GEN u = cgetg(li+1,t_COL);
  long i, j;

  gel(u,li) = gdiv(gel(b,li), p);
  for (i=li-1; i>0; i--)
  {
    pari_sp av = avma;
    GEN m = gel(b,i);
    for (j=i+1; j<=li; j++) m = gsub(m, gmul(gcoeff(a,i,j), gel(u,j)));
    gel(u,i) = gerepileupto(av, gdiv(m, gcoeff(a,i,i)));
  }
  return u;
}
/* assume 0 <= a[i,j] < p */
static GEN
Fl_get_col_OK(GEN a, GEN b, long li, ulong p)
{
  GEN u = cgetg(li+1,t_VECSMALL);
  ulong m = uel(b,li) % p;
  long i,j;

  uel(u,li) = (m * ucoeff(a,li,li)) % p;
  for (i = li-1; i > 0; i--)
  {
    m = p - uel(b,i)%p;
    for (j = i+1; j <= li; j++) {
      if (m & HIGHBIT) m %= p;
      m += ucoeff(a,i,j) * uel(u,j); /* 0 <= u[j] < p */
    }
    m %= p;
    if (m) m = ((p-m) * ucoeff(a,i,i)) % p;
    uel(u,i) = m;
  }
  return u;
}
static GEN
Fl_get_col(GEN a, GEN b, long li, ulong p)
{
  GEN u = cgetg(li+1,t_VECSMALL);
  ulong m = uel(b,li) % p;
  long i,j;

  uel(u,li) = Fl_mul(m, ucoeff(a,li,li), p);
  for (i=li-1; i>0; i--)
  {
    m = b[i]%p;
    for (j = i+1; j <= li; j++)
      m = Fl_sub(m, Fl_mul(ucoeff(a,i,j), uel(u,j), p), p);
    if (m) m = Fl_mul(m, ucoeff(a,i,i), p);
    uel(u,i) = m;
  }
  return u;
}

/* bk -= m * bi */
static void
_submul(GEN b, long k, long i, GEN m)
{
  gel(b,k) = gsub(gel(b,k), gmul(m, gel(b,i)));
}
static int
init_gauss(GEN a, GEN *b, long *aco, long *li, int *iscol)
{
  *iscol = *b ? (typ(*b) == t_COL): 0;
  *aco = lg(a) - 1;
  if (!*aco) /* a empty */
  {
    if (*b && lg(*b) != 1) pari_err_DIM("gauss");
    *li = 0; return 0;
  }
  *li = nbrows(a);
  if (*li < *aco) pari_err_INV("gauss [no left inverse]", a);
  if (*b)
  {
    switch(typ(*b))
    {
      case t_MAT:
        if (lg(*b) == 1) return 0;
        *b = RgM_shallowcopy(*b);
        break;
      case t_COL:
        *b = mkmat( leafcopy(*b) );
        break;
      default: pari_err_TYPE("gauss",*b);
    }
    if (nbrows(*b) != *li) pari_err_DIM("gauss");
  }
  else
    *b = matid(*li);
  return 1;
}

static GEN Flm_inv_sp(GEN a, ulong *detp, ulong p);
static GEN
RgM_inv_QM(GEN M)
{
  pari_sp av = avma;
  GEN den, cM, pM = Q_primitive_part(M, &cM);
  GEN b = ZM_inv(pM, &den);
  if (!b) { avma = av; return NULL; }
  if (cM) den = gmul(den, cM);
  if (!gequal1(den)) b = ZM_Q_mul(b, ginv(den));
  return gerepileupto(av, b);
}

static GEN
RgM_inv_FpM(GEN a, GEN p)
{
  ulong pp;
  a = RgM_Fp_init(a, p, &pp);
  switch(pp)
  {
  case 0:
    a = FpM_inv(a,p);
    if (a) a = FpM_to_mod(a, p);
    break;
  case 2:
    a = F2m_inv(a);
    if (a) a = F2m_to_mod(a);
    break;
  default:
    a = Flm_inv_sp(a, NULL, pp);
    if (a) a = Flm_to_mod(a, pp);
  }
  return a;
}

static GEN
RgM_inv_FqM(GEN x, GEN pol, GEN p)
{
  pari_sp av = avma;
  GEN b, T = RgX_to_FpX(pol, p);
  if (signe(T) == 0) pari_err_OP("^",x,gen_m1);
  b = FqM_inv(RgM_to_FqM(x, T, p), T, p);
  if (!b) { avma = av; return NULL; }
  return gerepileupto(av, FqM_to_mod(b, T, p));
}

#define code(t1,t2) ((t1 << 6) | t2)
static GEN
RgM_inv_fast(GEN x)
{
  GEN p, pol;
  long pa;
  long t = RgM_type(x, &p,&pol,&pa);
  switch(t)
  {
    case t_INT:    /* Fall back */
    case t_FRAC:   return RgM_inv_QM(x);
    case t_FFELT:  return FFM_inv(x, pol);
    case t_INTMOD: return RgM_inv_FpM(x, p);
    case code(t_POLMOD, t_INTMOD):
                   return RgM_inv_FqM(x, pol, p);
    default:       return gen_0;
  }
}
#undef code

static GEN
RgM_RgC_solve_FpC(GEN a, GEN b, GEN p)
{
  pari_sp av = avma;
  ulong pp;
  a = RgM_Fp_init(a, p, &pp);
  switch(pp)
  {
  case 0:
    b = RgC_to_FpC(b, p);
    a = FpM_FpC_gauss(a,b,p);
    return a ? gerepileupto(av, FpC_to_mod(a, p)): NULL;
  case 2:
    b = RgV_to_F2v(b);
    a = F2m_F2c_gauss(a,b);
    return a ? gerepileupto(av, F2c_to_mod(a)): NULL;
  default:
    b = RgV_to_Flv(b, pp);
    a = Flm_Flc_gauss(a, b, pp);
    return a ? gerepileupto(av, Flc_to_mod(a, pp)): NULL;
  }
}

static GEN
RgM_solve_FpM(GEN a, GEN b, GEN p)
{
  pari_sp av = avma;
  ulong pp;
  a = RgM_Fp_init(a, p, &pp);
  switch(pp)
  {
  case 0:
    b = RgM_to_FpM(b, p);
    a = FpM_gauss(a,b,p);
    return a ? gerepileupto(av, FpM_to_mod(a, p)): NULL;
  case 2:
    b = RgM_to_F2m(b);
    a = F2m_gauss(a,b);
    return a ? gerepileupto(av, F2m_to_mod(a)): NULL;
  default:
    b = RgM_to_Flm(b, pp);
    a = Flm_gauss(a,b,pp);
    return a ? gerepileupto(av, Flm_to_mod(a, pp)): NULL;
  }
}

/* Gaussan Elimination. If a is square, return a^(-1)*b;
 * if a has more rows than columns and b is NULL, return c such that c a = Id.
 * a is a (not necessarily square) matrix
 * b is a matrix or column vector, NULL meaning: take the identity matrix,
 *   effectively returning the inverse of a
 * If a and b are empty, the result is the empty matrix.
 *
 * li: number of rows of a and b
 * aco: number of columns of a
 * bco: number of columns of b (if matrix)
 */
static GEN
RgM_solve_basecase(GEN a, GEN b)
{
  pari_sp av = avma;
  long i, j, k, li, bco, aco;
  int iscol;
  pivot_fun pivot;
  GEN p, u, data;

  avma = av;

  if (lg(a)-1 == 2 && nbrows(a) == 2) {
    /* 2x2 matrix, start by inverting a */
    GEN u = gcoeff(a,1,1), v = gcoeff(a,1,2);
    GEN w = gcoeff(a,2,1), x = gcoeff(a,2,2);
    GEN D = gsub(gmul(u,x), gmul(v,w)), ainv;
    if (gequal0(D)) return NULL;
    ainv = mkmat2(mkcol2(x, gneg(w)), mkcol2(gneg(v), u));
    ainv = gmul(ainv, ginv(D));
    if (b) ainv = gmul(ainv, b);
    return gerepileupto(av, ainv);
  }

  if (!init_gauss(a, &b, &aco, &li, &iscol)) return cgetg(1, iscol?t_COL:t_MAT);
  pivot = get_pivot_fun(a, a, &data);
  a = RgM_shallowcopy(a);
  bco = lg(b)-1;
  if(DEBUGLEVEL>4) err_printf("Entering gauss\n");

  p = NULL; /* gcc -Wall */
  for (i=1; i<=aco; i++)
  {
    /* k is the line where we find the pivot */
    k = pivot(a, data, i, NULL);
    if (k > li) return NULL;
    if (k != i)
    { /* exchange the lines s.t. k = i */
      for (j=i; j<=aco; j++) swap(gcoeff(a,i,j), gcoeff(a,k,j));
      for (j=1; j<=bco; j++) swap(gcoeff(b,i,j), gcoeff(b,k,j));
    }
    p = gcoeff(a,i,i);
    if (i == aco) break;

    for (k=i+1; k<=li; k++)
    {
      GEN m = gcoeff(a,k,i);
      if (!gequal0(m))
      {
        m = gdiv(m,p);
        for (j=i+1; j<=aco; j++) _submul(gel(a,j),k,i,m);
        for (j=1;   j<=bco; j++) _submul(gel(b,j),k,i,m);
      }
    }
    if (gc_needed(av,1))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"gauss. i=%ld",i);
      gerepileall(av,2, &a,&b);
    }
  }

  if(DEBUGLEVEL>4) err_printf("Solving the triangular system\n");
  u = cgetg(bco+1,t_MAT);
  for (j=1; j<=bco; j++) gel(u,j) = get_col(a,gel(b,j),p,aco);
  return gerepilecopy(av, iscol? gel(u,1): u);
}

static GEN
RgM_RgC_solve_fast(GEN x, GEN y)
{
  GEN p, pol;
  long pa;
  long t = RgM_RgC_type(x, y, &p,&pol,&pa);
  switch(t)
  {
    case t_INT:    return ZM_gauss(x, y);
    case t_FRAC:   return QM_gauss(x, y);
    case t_INTMOD: return RgM_RgC_solve_FpC(x, y, p);
    case t_FFELT:  return FFM_FFC_gauss(x, y, pol);
    default:       return gen_0;
  }
}

static GEN
RgM_solve_fast(GEN x, GEN y)
{
  GEN p, pol;
  long pa;
  long t = RgM_type2(x, y, &p,&pol,&pa);
  switch(t)
  {
    case t_INT:    return ZM_gauss(x, y);
    case t_FRAC:   return QM_gauss(x, y);
    case t_INTMOD: return RgM_solve_FpM(x, y, p);
    case t_FFELT:  return FFM_gauss(x, y, pol);
    default:       return gen_0;
  }
}

GEN
RgM_solve(GEN a, GEN b)
{
  pari_sp av = avma;
  GEN u;
  if (!b) return RgM_inv(a);
  u = typ(b)==t_MAT ? RgM_solve_fast(a, b): RgM_RgC_solve_fast(a, b);
  if (!u) { avma = av; return u; }
  if (u != gen_0) return u;
  return RgM_solve_basecase(a, b);
}

GEN
RgM_inv(GEN a)
{
  GEN b = RgM_inv_fast(a);
  return b==gen_0? RgM_solve_basecase(a, NULL): b;
}

/* assume dim A >= 1, A invertible + upper triangular  */
static GEN
RgM_inv_upper_ind(GEN A, long index)
{
  long n = lg(A)-1, i = index, j;
  GEN u = zerocol(n);
  gel(u,i) = ginv(gcoeff(A,i,i));
  for (i--; i>0; i--)
  {
    pari_sp av = avma;
    GEN m = gneg(gmul(gcoeff(A,i,i+1),gel(u,i+1))); /* j = i+1 */
    for (j=i+2; j<=n; j++) m = gsub(m, gmul(gcoeff(A,i,j),gel(u,j)));
    gel(u,i) = gerepileupto(av, gdiv(m, gcoeff(A,i,i)));
  }
  return u;
}
GEN
RgM_inv_upper(GEN A)
{
  long i, l;
  GEN B = cgetg_copy(A, &l);
  for (i = 1; i < l; i++) gel(B,i) = RgM_inv_upper_ind(A, i);
  return B;
}

/* assume dim A >= 1, A invertible + upper triangular, 1s on diagonal  */
static GEN
FpM_inv_upper_1_ind(GEN A, long index, GEN p)
{
  long n = lg(A)-1, i = index, j;
  GEN u = zerocol(n);
  gel(u,i) = gen_1;
  for (i--; i>0; i--)
  {
    pari_sp av = avma;
    GEN m = negi(mulii(gcoeff(A,i,i+1),gel(u,i+1))); /* j = i+1 */
    for (j=i+2; j<=n; j++) m = subii(m, mulii(gcoeff(A,i,j),gel(u,j)));
    gel(u,i) = gerepileuptoint(av, modii(m,p));
  }
  return u;
}
static GEN
FpM_inv_upper_1(GEN A, GEN p)
{
  long i, l;
  GEN B = cgetg_copy(A, &l);
  for (i = 1; i < l; i++) gel(B,i) = FpM_inv_upper_1_ind(A, i, p);
  return B;
}
/* assume dim A >= 1, A invertible + upper triangular, 1s on diagonal,
 * reduced mod p */
static GEN
Flm_inv_upper_1_ind(GEN A, long index, ulong p)
{
  long n = lg(A)-1, i = index, j;
  GEN u = const_vecsmall(n, 0);
  u[i] = 1;
  if (SMALL_ULONG(p))
    for (i--; i>0; i--)
    {
      ulong m = ucoeff(A,i,i+1) * uel(u,i+1); /* j = i+1 */
      for (j=i+2; j<=n; j++)
      {
        if (m & HIGHMASK) m %= p;
        m += ucoeff(A,i,j) * uel(u,j);
      }
      u[i] = Fl_neg(m % p, p);
    }
  else
    for (i--; i>0; i--)
    {
      ulong m = Fl_mul(ucoeff(A,i,i+1),uel(u,i+1), p); /* j = i+1 */
      for (j=i+2; j<=n; j++) m = Fl_add(m, Fl_mul(ucoeff(A,i,j),uel(u,j),p), p);
      u[i] = Fl_neg(m, p);
    }
  return u;
}
static GEN
F2m_inv_upper_1_ind(GEN A, long index)
{
  pari_sp av = avma;
  long n = lg(A)-1, i = index, j;
  GEN u = const_vecsmall(n, 0);
  u[i] = 1;
  for (i--; i>0; i--)
  {
    ulong m = F2m_coeff(A,i,i+1) & uel(u,i+1); /* j = i+1 */
    for (j=i+2; j<=n; j++) m ^= F2m_coeff(A,i,j) & uel(u,j);
    u[i] = m & 1;
  }
  return gerepileuptoleaf(av, Flv_to_F2v(u));
}
static GEN
Flm_inv_upper_1(GEN A, ulong p)
{
  long i, l;
  GEN B = cgetg_copy(A, &l);
  for (i = 1; i < l; i++) gel(B,i) = Flm_inv_upper_1_ind(A, i, p);
  return B;
}
static GEN
F2m_inv_upper_1(GEN A)
{
  long i, l;
  GEN B = cgetg_copy(A, &l);
  for (i = 1; i < l; i++) gel(B,i) = F2m_inv_upper_1_ind(A, i);
  return B;
}

static GEN
split_realimag_col(GEN z, long r1, long r2)
{
  long i, ru = r1+r2;
  GEN x = cgetg(ru+r2+1,t_COL), y = x + r2;
  for (i=1; i<=r1; i++) {
    GEN a = gel(z,i);
    if (typ(a) == t_COMPLEX) a = gel(a,1); /* paranoia: a should be real */
    gel(x,i) = a;
  }
  for (   ; i<=ru; i++) {
    GEN b, a = gel(z,i);
    if (typ(a) == t_COMPLEX) { b = gel(a,2); a = gel(a,1); } else b = gen_0;
    gel(x,i) = a;
    gel(y,i) = b;
  }
  return x;
}
GEN
split_realimag(GEN x, long r1, long r2)
{
  long i,l; GEN y;
  if (typ(x) == t_COL) return split_realimag_col(x,r1,r2);
  y = cgetg_copy(x, &l);
  for (i=1; i<l; i++) gel(y,i) = split_realimag_col(gel(x,i), r1, r2);
  return y;
}

/* assume M = (r1+r2) x (r1+2r2) matrix and y compatible vector or matrix
 * r1 first lines of M,y are real. Solve the system obtained by splitting
 * real and imaginary parts. */
GEN
RgM_solve_realimag(GEN M, GEN y)
{
  long l = lg(M), r2 = l - lgcols(M), r1 = l-1 - 2*r2;
  return RgM_solve(split_realimag(M, r1,r2),
                   split_realimag(y, r1,r2));
}

GEN
gauss(GEN a, GEN b)
{
  GEN z;
  long t = typ(b);
  if (typ(a)!=t_MAT) pari_err_TYPE("gauss",a);
  if (t!=t_COL && t!=t_MAT) pari_err_TYPE("gauss",b);
  z = RgM_solve(a,b);
  if (!z) pari_err_INV("gauss",a);
  return z;
}

static GEN
F2_get_col(GEN b, GEN d, long li, long aco)
{
  long i, l = nbits2lg(aco);
  GEN u = cgetg(l, t_VECSMALL);
  u[1] = aco;
  for (i = 1; i <= li; i++)
    if (d[i]) /* d[i] can still be 0 if li > aco */
    {
      if (F2v_coeff(b, i))
        F2v_set(u, d[i]);
      else
        F2v_clear(u, d[i]);
    }
  return u;
}

/* destroy a, b */
static GEN
F2m_gauss_sp(GEN a, GEN b)
{
  long i, j, k, l, li, bco, aco = lg(a)-1;
  GEN u, d;

  if (!aco) return cgetg(1,t_MAT);
  li = gel(a,1)[1];
  d = zero_Flv(li);
  bco = lg(b)-1;
  for (i=1; i<=aco; i++)
  {
    GEN ai = vecsmall_copy(gel(a,i));
    if (!d[i] && F2v_coeff(ai, i))
      k = i;
    else
      for (k = 1; k <= li; k++) if (!d[k] && F2v_coeff(ai,k)) break;
    /* found a pivot on row k */
    if (k > li) return NULL;
    d[k] = i;

    /* Clear k-th row but column-wise instead of line-wise */
    /*  a_ij -= a_i1*a1j/a_11
       line-wise grouping:  L_j -= a_1j/a_11*L_1
       column-wise:         C_i -= a_i1/a_11*C_1
    */
    F2v_clear(ai,k);
    for (l=1; l<=aco; l++)
    {
      GEN al = gel(a,l);
      if (F2v_coeff(al,k)) F2v_add_inplace(al,ai);
    }
    for (l=1; l<=bco; l++)
    {
      GEN bl = gel(b,l);
      if (F2v_coeff(bl,k)) F2v_add_inplace(bl,ai);
    }
  }
  u = cgetg(bco+1,t_MAT);
  for (j = 1; j <= bco; j++) gel(u,j) = F2_get_col(gel(b,j), d, li, aco);
  return u;
}

GEN
F2m_gauss(GEN a, GEN b)
{
  pari_sp av = avma;
  if (lg(a) == 1) return cgetg(1,t_MAT);
  return gerepileupto(av, F2m_gauss_sp(F2m_copy(a), F2m_copy(b)));
}
GEN
F2m_F2c_gauss(GEN a, GEN b)
{
  pari_sp av = avma;
  GEN z = F2m_gauss(a, mkmat(b));
  if (!z) { avma = av; return NULL; }
  if (lg(z) == 1) { avma = av; return cgetg(1,t_VECSMALL); }
  return gerepileuptoleaf(av, gel(z,1));
}

GEN
F2m_inv(GEN a)
{
  pari_sp av = avma;
  if (lg(a) == 1) return cgetg(1,t_MAT);
  return gerepileupto(av, F2m_gauss_sp(F2m_copy(a), matid_F2m(gel(a,1)[1])));
}

/* destroy a, b */
static GEN
Flm_gauss_sp_OK(GEN a, GEN b, ulong *detp, ulong p)
{
  long i, j, k, li, bco, aco = lg(a)-1, s = 1;
  ulong det = 1;
  GEN u;

  li = nbrows(a);
  bco = lg(b)-1;
  for (i=1; i<=aco; i++)
  {
    ulong invpiv;
    /* Fl_get_col wants 0 <= a[i,j] < p for all i,j */
    for (k = 1; k < i; k++) ucoeff(a,k,i) %= p;
    for (k = i; k <= li; k++)
    {
      ulong piv = ( ucoeff(a,k,i) %= p );
      if (piv)
      {
        ucoeff(a,k,i) = Fl_inv(piv, p);
        if (detp)
        {
          if (det & HIGHMASK) det %= p;
          det *= piv;
        }
        break;
      }
    }
    /* found a pivot on line k */
    if (k > li) return NULL;
    if (k != i)
    { /* swap lines so that k = i */
      s = -s;
      for (j=i; j<=aco; j++) swap(gcoeff(a,i,j), gcoeff(a,k,j));
      for (j=1; j<=bco; j++) swap(gcoeff(b,i,j), gcoeff(b,k,j));
    }
    if (i == aco) break;

    invpiv = p - ucoeff(a,i,i); /* -1/piv mod p */
    for (k=i+1; k<=li; k++)
    {
      ulong m = ( ucoeff(a,k,i) %= p );
      if (!m) continue;

      m = Fl_mul(m, invpiv, p);
      if (m == 1) {
        for (j=i+1; j<=aco; j++) _Fl_add_OK(gel(a,j),k,i, p);
        for (j=1;   j<=bco; j++) _Fl_add_OK(gel(b,j),k,i, p);
      } else {
        for (j=i+1; j<=aco; j++) _Fl_addmul_OK(gel(a,j),k,i,m, p);
        for (j=1;   j<=bco; j++) _Fl_addmul_OK(gel(b,j),k,i,m, p);
      }
    }
  }
  if (detp)
  {
    det %=  p;
    if (s < 0 && det) det = p - det;
    *detp = det;
  }
  u = cgetg(bco+1,t_MAT);
  for (j=1; j<=bco; j++) gel(u,j) = Fl_get_col_OK(a,gel(b,j), aco,p);
  return u;
}

/* destroy a, b */
static GEN
Flm_gauss_sp(GEN a, GEN b, ulong *detp, ulong p)
{
  long i, j, k, li, bco, aco = lg(a)-1, s = 1;
  ulong det = 1;
  GEN u;
  ulong pi;
  if (!aco) { if (detp) *detp = 1; return cgetg(1,t_MAT); }
  if (SMALL_ULONG(p)) return Flm_gauss_sp_OK(a, b, detp, p);
  pi = get_Fl_red(p);
  li = nbrows(a);
  bco = lg(b)-1;
  for (i=1; i<=aco; i++)
  {
    ulong invpiv;
    /* Fl_get_col wants 0 <= a[i,j] < p for all i,j */
    for (k = i; k <= li; k++)
    {
      ulong piv = ucoeff(a,k,i);
      if (piv)
      {
        ucoeff(a,k,i) = Fl_inv(piv, p);
        if (detp) det = Fl_mul_pre(det, piv, p, pi);
        break;
      }
    }
    /* found a pivot on line k */
    if (k > li) return NULL;
    if (k != i)
    { /* swap lines so that k = i */
      s = -s;
      for (j=i; j<=aco; j++) swap(gcoeff(a,i,j), gcoeff(a,k,j));
      for (j=1; j<=bco; j++) swap(gcoeff(b,i,j), gcoeff(b,k,j));
    }
    if (i == aco) break;

    invpiv = p - ucoeff(a,i,i); /* -1/piv mod p */
    for (k=i+1; k<=li; k++)
    {
      ulong m = ucoeff(a,k,i);
      if (!m) continue;

      m = Fl_mul_pre(m, invpiv, p, pi);
      if (m == 1) {
        for (j=i+1; j<=aco; j++) _Fl_add(gel(a,j),k,i, p);
        for (j=1;   j<=bco; j++) _Fl_add(gel(b,j),k,i, p);
      } else {
        for (j=i+1; j<=aco; j++) _Fl_addmul(gel(a,j),k,i,m, p, pi);
        for (j=1;   j<=bco; j++) _Fl_addmul(gel(b,j),k,i,m, p, pi);
      }
    }
  }
  if (detp)
  {
    if (s < 0 && det) det = p - det;
    *detp = det;
  }
  u = cgetg(bco+1,t_MAT);
  for (j=1; j<=bco; j++) gel(u,j) = Fl_get_col(a,gel(b,j), aco,p);
  return u;
}

static GEN
Flm_gauss_from_CUP(GEN b, GEN R, GEN C, GEN U, GEN P, ulong p, ulong *detp)
{
  GEN Y = Flm_rsolve_lower_unit(rowpermute(C, R), rowpermute(b, R), p);
  GEN X = rowpermute(Flm_rsolve_upper(U, Y, p), perm_inv(P));
  if (detp)
  {
    ulong d = perm_sign(P) == 1? 1: p-1;
    long i, r = lg(R);
    for (i = 1; i < r; i++)
      d = Fl_mul(d, ucoeff(U, i, i), p);
    *detp = d;
  }
  return X;
}

static GEN
Flm_gauss_CUP(GEN a, GEN b, ulong *detp, ulong p) {
  GEN R, C, U, P;
  long n = lg(a) - 1, r;
  if (nbrows(a) < n || (r = Flm_CUP(a, &R, &C, &U, &P, p)) < n)
    return NULL;
  return Flm_gauss_from_CUP(b, R, C, U, P, p, detp);
}

GEN
Flm_gauss(GEN a, GEN b, ulong p) {
  pari_sp av = avma;
  GEN x;
  if (lg(a) - 1 >= Flm_CUP_LIMIT)
    x = Flm_gauss_CUP(a, b, NULL, p);
  else {
    a = RgM_shallowcopy(a);
    b = RgM_shallowcopy(b);
    x = Flm_gauss_sp(a, b, NULL, p);
  }
  if (!x) { avma = av; return NULL; }
  return gerepileupto(av, x);
}

static GEN
Flm_inv_i(GEN a, ulong *detp, ulong p, long inplace) {
  pari_sp av = avma;
  long n = lg(a) - 1;
  GEN b, x;
  if (n == 0) return cgetg(1, t_MAT);
  b = matid_Flm(nbrows(a));
  if (n >= Flm_CUP_LIMIT)
    x = Flm_gauss_CUP(a, b, detp, p);
  else {
    if (!inplace)
      a = RgM_shallowcopy(a);
    x = Flm_gauss_sp(a, b, detp, p);
  }
  if (!x) { avma = av; return NULL; }
  return gerepileupto(av, x);
}

static GEN
Flm_inv_sp(GEN a, ulong *detp, ulong p) {
  return Flm_inv_i(a, detp, p, 1);
}

GEN
Flm_inv(GEN a, ulong p) {
  return Flm_inv_i(a, NULL, p, 0);
}

GEN
Flm_Flc_gauss(GEN a, GEN b, ulong p) {
  pari_sp av = avma;
  GEN z = Flm_gauss(a, mkmat(b), p);
  if (!z) { avma = av; return NULL; }
  if (lg(z) == 1) { avma = av; return cgetg(1,t_VECSMALL); }
  return gerepileuptoleaf(av, gel(z,1));
}

GEN
Flm_adjoint(GEN A, ulong p)
{
  pari_sp av = avma;
  GEN R, C, U, P, C1, U1, v, c, d;
  long r, i, q, n = lg(A)-1, m;
  ulong D;
  if (n == 0) return cgetg(1, t_MAT);
  r = Flm_CUP(A, &R, &C, &U, &P, p);
  m = nbrows(A);
  if (r == n)
  {
    GEN X = Flm_gauss_from_CUP(matid_Flm(m), R, C, U, P, p, &D);
    return gerepileupto(av, Flm_Fl_mul(X, D, p));
  }
  if (r < n-1) return zero_Flm(n, m);
  for (q = n, i = 1; i < n; i++)
    if (R[i] != i) { q = i; break; }
  C1 = matslice(C, 1, q-1, 1, q-1);
  c = vecslice(Flm_row(C, q), 1, q-1);
  c = Flm_lsolve_lower_unit(C1, Flm_transpose(mkmat(c)), p);
  d = cgetg(m+1, t_VECSMALL);
  for (i=1; i<q; i++)    uel(d,i) = ucoeff(c,1,i);
  uel(d,q) = p-1;
  for (i=q+1; i<=m; i++) uel(d,i) = 0;
  U1 = vecslice(U, 1, n-1);
  v = gel(Flm_rsolve_upper(U1, mkmat(gel(U,n)), p),1);
  v = vecsmall_append(v, p-1);
  D = perm_sign(P) != (odd(q+n)?-1:1) ? p-1 : 1;
  for (i = 1; i <= n-1; i++)
    D = Fl_mul(D, ucoeff(U1, i, i), p);
  d = Flv_Fl_mul(d, D, p);
  return rowpermute(Flc_Flv_mul(v, d, p),perm_inv(P));
}

static GEN
FpM_gauss_gen(GEN a, GEN b, GEN p)
{
  void *E;
  const struct bb_field *S = get_Fp_field(&E,p);
  return gen_Gauss(a,b, E, S);
}
/* a an FpM, lg(a)>1; b an FpM or NULL (replace by identity) */
static GEN
FpM_gauss_i(GEN a, GEN b, GEN p, ulong *pp)
{
  long n = nbrows(a);
  a = FpM_init(a,p,pp);
  switch(*pp)
  {
  case 0:
    if (!b) b = matid(n);
    return FpM_gauss_gen(a,b,p);
  case 2:
    if (b) b = ZM_to_F2m(b); else b = matid_F2m(n);
    return F2m_gauss_sp(a,b);
  default:
    if (b) b = ZM_to_Flm(b, *pp); else b = matid_Flm(n);
    return Flm_gauss_sp(a,b, NULL, *pp);
  }
}
GEN
FpM_gauss(GEN a, GEN b, GEN p)
{
  pari_sp av = avma;
  ulong pp;
  GEN u;
  if (lg(a) == 1 || lg(b)==1) return cgetg(1, t_MAT);
  u = FpM_gauss_i(a, b, p, &pp);
  if (!u) { avma = av; return NULL; }
  switch(pp)
  {
  case 0: return gerepilecopy(av, u);
  case 2:  u = F2m_to_ZM(u); break;
  default: u = Flm_to_ZM(u); break;
  }
  return gerepileupto(av, u);
}
GEN
FpM_inv(GEN a, GEN p)
{
  pari_sp av = avma;
  ulong pp;
  GEN u;
  if (lg(a) == 1) return cgetg(1, t_MAT);
  u = FpM_gauss_i(a, NULL, p, &pp);
  if (!u) { avma = av; return NULL; }
  switch(pp)
  {
  case 0: return gerepilecopy(av, u);
  case 2:  u = F2m_to_ZM(u); break;
  default: u = Flm_to_ZM(u); break;
  }
  return gerepileupto(av, u);
}

GEN
FpM_FpC_gauss(GEN a, GEN b, GEN p)
{
  pari_sp av = avma;
  ulong pp;
  GEN u;
  if (lg(a) == 1) return cgetg(1, t_COL);
  u = FpM_gauss_i(a, mkmat(b), p, &pp);
  if (!u) { avma = av; return NULL; }
  switch(pp)
  {
  case 0: return gerepilecopy(av, gel(u,1));
  case 2:  u = F2c_to_ZC(gel(u,1)); break;
  default: u = Flc_to_ZC(gel(u,1)); break;
  }
  return gerepileupto(av, u);
}

static GEN
FlxqM_gauss_gen(GEN a, GEN b, GEN T, ulong p)
{
  void *E;
  const struct bb_field *S = get_Flxq_field(&E, T, p);
  return gen_Gauss(a, b, E, S);
}

static GEN
FlxqM_gauss_CUP(GEN a, GEN b, GEN T, ulong p) {
  GEN R, C, U, P, Y;
  long n = lg(a) - 1, r;
  if (nbrows(a) < n || (r = FlxqM_CUP(a, &R, &C, &U, &P, T, p)) < n)
    return NULL;
  Y = FlxqM_rsolve_lower_unit(rowpermute(C, R),
                              rowpermute(b, R), T, p);
  return rowpermute(FlxqM_rsolve_upper(U, Y, T, p),
                    perm_inv(P));
}

static GEN
FlxqM_gauss_i(GEN a, GEN b, GEN T, ulong p) {
  if (lg(a) - 1 >= FlxqM_CUP_LIMIT)
    return FlxqM_gauss_CUP(a, b, T, p);
  return FlxqM_gauss_gen(a, b, T, p);
}

GEN
FlxqM_gauss(GEN a, GEN b, GEN T, ulong p)
{
  pari_sp av = avma;
  long n = lg(a)-1;
  GEN u;
  if (!n || lg(b)==1) { avma = av; return cgetg(1, t_MAT); }
  u = FlxqM_gauss_i(a, b, T, p);
  if (!u) { avma = av; return NULL; }
  return gerepilecopy(av, u);
}
GEN
FlxqM_inv(GEN a, GEN T, ulong p)
{
  pari_sp av = avma;
  GEN u;
  if (lg(a) == 1) { avma = av; return cgetg(1, t_MAT); }
  u = FlxqM_gauss_i(a, matid_FlxqM(nbrows(a),T,p), T,p);
  if (!u) { avma = av; return NULL; }
  return gerepilecopy(av, u);
}
GEN
FlxqM_FlxqC_gauss(GEN a, GEN b, GEN T, ulong p)
{
  pari_sp av = avma;
  GEN u;
  if (lg(a) == 1) return cgetg(1, t_COL);
  u = FlxqM_gauss_i(a, mkmat(b), T, p);
  if (!u) { avma = av; return NULL; }
  return gerepilecopy(av, gel(u,1));
}

static GEN
FqM_gauss_gen(GEN a, GEN b, GEN T, GEN p)
{
  void *E;
  const struct bb_field *S = get_Fq_field(&E,T,p);
  return gen_Gauss(a,b,E,S);
}
GEN
FqM_gauss(GEN a, GEN b, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN u;
  long n;
  if (!T) return FpM_gauss(a,b,p);
  n = lg(a)-1; if (!n || lg(b)==1) return cgetg(1, t_MAT);
  u = FqM_gauss_gen(a,b,T,p);
  if (!u) { avma = av; return NULL; }
  return gerepilecopy(av, u);
}
GEN
FqM_inv(GEN a, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN u;
  if (!T) return FpM_inv(a,p);
  if (lg(a) == 1) return cgetg(1, t_MAT);
  u = FqM_gauss_gen(a,matid(nbrows(a)),T,p);
  if (!u) { avma = av; return NULL; }
  return gerepilecopy(av, u);
}
GEN
FqM_FqC_gauss(GEN a, GEN b, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN u;
  if (!T) return FpM_FpC_gauss(a,b,p);
  if (lg(a) == 1) return cgetg(1, t_COL);
  u = FqM_gauss_gen(a,mkmat(b),T,p);
  if (!u) { avma = av; return NULL; }
  return gerepilecopy(av, gel(u,1));
}

static GEN
ZlM_gauss_ratlift(GEN a, GEN b, ulong p, long e, GEN C)
{
  pari_sp av = avma, av2;
  GEN bb, xi, xb, pi, P, B, r;
  long i, k = 2;
  if (!C) {
    C = Flm_inv(ZM_to_Flm(a, p), p);
    if (!C) pari_err_INV("ZlM_gauss", a);
  }
  pi = P = utoipos(p);
  av2 = avma;
  xi = Flm_mul(C, ZM_to_Flm(b, p), p);
  xb = Flm_to_ZM(xi);
  bb = b;
  for (i = 2; i <= e; i++)
  {
    bb = ZM_Z_divexact(ZM_sub(bb, ZM_nm_mul(a, xi)), P);
    if (gc_needed(av,2))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"ZlM_gauss. i=%ld/%ld",i,e);
      gerepileall(av2,3, &pi,&bb,&xb);
    }
    xi = Flm_mul(C, ZM_to_Flm(bb, p), p);
    xb = ZM_add(xb, nm_Z_mul(xi, pi));
    pi = muliu(pi, p); /* = p^(i-1) */
    if (i==k && i < e)
    {
      k *= 2;
      B = sqrti(shifti(pi,-1));
      r = FpM_ratlift(xb, pi, B, B, NULL);
      if (r)
      {
        GEN dr, nr = Q_remove_denom(r,&dr);
        if (ZM_equal(ZM_mul(a,nr), dr? ZM_Z_mul(b,dr): b))
        {
          if (DEBUGLEVEL>=4)
            err_printf("ZlM_gauss: early solution: %ld/%ld\n",i,e);
          return gerepilecopy(av, r);
        }
      }
    }
  }
  B = sqrti(shifti(pi,-1));
  return gerepileupto(av, FpM_ratlift(xb, pi, B, B, NULL));
}

/* Dixon p-adic lifting algorithm.
 * Numer. Math. 40, 137-141 (1982), DOI: 10.1007/BF01459082 */
GEN
ZM_gauss(GEN a, GEN b0)
{
  pari_sp av = avma, av2;
  int iscol;
  long n, ncol, i, m, elim;
  ulong p;
  GEN C, delta, nb, nmin, res, b = b0;
  forprime_t S;

  if (!init_gauss(a, &b, &n, &ncol, &iscol)) return cgetg(1, iscol?t_COL:t_MAT);
  nb = gen_0; ncol = lg(b);
  for (i = 1; i < ncol; i++)
  {
    GEN ni = gnorml2(gel(b, i));
    if (cmpii(nb, ni) < 0) nb = ni;
  }
  if (!signe(nb)) { avma = av; return gcopy(b0); }
  delta = gen_1; nmin = nb;
  for (i = 1; i <= n; i++)
  {
    GEN ni = gnorml2(gel(a, i));
    if (cmpii(ni, nmin) < 0)
    {
      delta = mulii(delta, nmin); nmin = ni;
    }
    else
      delta = mulii(delta, ni);
  }
  if (!signe(nmin)) return NULL;
  elim = expi(delta)+1;
  av2 = avma;
  init_modular_big(&S);
  for(;;)
  {
    p = u_forprime_next(&S);
    C = Flm_inv_sp(ZM_to_Flm(a, p), NULL, p);
    if (C) break;
    elim -= expu(p);
    if (elim < 0) return NULL;
    avma = av2;
  }
  /* N.B. Our delta/lambda are SQUARES of those in the paper
   * log(delta lambda) / log p, where lambda is 3+sqrt(5) / 2,
   * whose log is < 1, hence + 1 (to cater for rounding errors) */
  m = (long)ceil((rtodbl(logr_abs(itor(delta,LOWDEFAULTPREC))) + 1)
                 / log((double)p));
  res = ZlM_gauss_ratlift(a, b, p, m, C);
  if (iscol) return gerepilecopy(av, gel(res, 1));
  return gerepileupto(av, res);
}

/* same as above, M rational */
GEN
QM_gauss(GEN M, GEN B)
{
  pari_sp av = avma;
  GEN K, MB;
  MB = Q_primitive_part(mkvec2(M,B), NULL);
  K = ZM_gauss(gel(MB,1), gel(MB,2));
  return gerepileupto(av, K);
}

static GEN
ZM_inv_slice(GEN A, GEN P, GEN *mod)
{
  pari_sp av = avma;
  long i, n = lg(P)-1;
  GEN H, T;
  if (n == 1)
  {
    ulong p = uel(P,1);
    GEN Hp, a = ZM_to_Flm(A, p);
    Hp = Flm_adjoint(a, p);
    Hp = gerepileupto(av, Flm_to_ZM(Hp));
    *mod = utoi(p); return Hp;
  }
  T = ZV_producttree(P);
  A = ZM_nv_mod_tree(A, P, T);
  H = cgetg(n+1, t_VEC);
  for(i=1; i <= n; i++)
    gel(H,i) = Flm_adjoint(gel(A, i), uel(P,i));
  H = nmV_chinese_center_tree_seq(H, P, T, ZV_chinesetree(P,T));
  *mod = gmael(T, lg(T)-1, 1);
  gerepileall(av, 2, &H, mod);
  return H;
}

static GEN
RgM_true_Hadamard(GEN a)
{
  pari_sp av = avma;
  long n = lg(a)-1, i;
  GEN B;
  if (n == 0) return gen_1;
  a = RgM_gtofp(a, LOWDEFAULTPREC);
  B = gnorml2(gel(a,1));
  for (i = 2; i <= n; i++) B = gmul(B, gnorml2(gel(a,i)));
  return gerepileuptoint(av, ceil_safe(sqrtr(B)));
}

GEN
ZM_inv_worker(GEN P, GEN A)
{
  GEN V = cgetg(3, t_VEC);
  gel(V,1) = ZM_inv_slice(A, P, &gel(V,2));
  return V;
}

static GEN
ZM_inv0(GEN A, GEN *pden)
{
  if (pden) *pden = gen_1;
  (void)A; return cgetg(1, t_MAT);
}
static GEN
ZM_inv1(GEN A, GEN *pden)
{
  GEN a = gcoeff(A,1,1);
  long s = signe(a);
  if (!s) return NULL;
  if (pden) *pden = absi(a);
  retmkmat(mkcol(s == 1? gen_1: gen_m1));
}
static GEN
ZM_inv2(GEN A, GEN *pden)
{
  GEN a, b, c, d, D, cA;
  long s;
  A = Q_primitive_part(A, &cA);
  a = gcoeff(A,1,1); b = gcoeff(A,1,2);
  c = gcoeff(A,2,1); d = gcoeff(A,2,2);
  D = subii(mulii(a,d), mulii(b,c)); /* left on stack */
  s = signe(D);
  if (!s) return NULL;
  if (s < 0) D = negi(D);
  if (pden) *pden = mul_denom(D, cA);
  if (s > 0)
    retmkmat2(mkcol2(icopy(d), negi(c)), mkcol2(negi(b), icopy(a)));
  else
    retmkmat2(mkcol2(negi(d), icopy(c)), mkcol2(icopy(b), negi(a)));
}

/* to be used when denom(M^(-1)) << det(M) and a sharp multiple is
 * not available. Return H primitive such that M*H = den*Id */
GEN
ZM_inv_ratlift(GEN M, GEN *pden)
{
  pari_sp av2, av = avma;
  GEN Hp, q, H;
  ulong p;
  long m = lg(M)-1;
  forprime_t S;
  pari_timer ti;

  if (m == 0) return ZM_inv0(M,pden);
  if (m == 1 && nbrows(M)==1) return ZM_inv1(M,pden);
  if (m == 2 && nbrows(M)==2) return ZM_inv2(M,pden);

  if (DEBUGLEVEL>5) timer_start(&ti);
  init_modular_big(&S);
  av2 = avma;
  H = NULL;
  while ((p = u_forprime_next(&S)))
  {
    GEN Mp, B, Hr;
    Mp = ZM_to_Flm(M,p);
    Hp = Flm_inv_sp(Mp, NULL, p);
    if (!Hp) continue;
    if (!H)
    {
      H = ZM_init_CRT(Hp, p);
      q = utoipos(p);
    }
    else
      ZM_incremental_CRT(&H, Hp, &q, p);
    B = sqrti(shifti(q,-1));
    Hr = FpM_ratlift(H,q,B,B,NULL);
    if (DEBUGLEVEL>5)
      timer_printf(&ti,"ZM_inv mod %lu (ratlift=%ld)", p,!!Hr);
    if (Hr) {/* DONE ? */
      GEN Hl = Q_remove_denom(Hr, pden);
      if (ZM_isscalar(ZM_mul(Hl, M), *pden)) { H = Hl; break; }
    }

    if (gc_needed(av,2))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"ZM_inv_ratlift");
      gerepileall(av2, 2, &H, &q);
    }
  }
  if (!*pden) *pden = gen_1;
  gerepileall(av, 2, &H, pden);
  return H;
}

static GEN
ZM_adj_ratlift(GEN A, GEN H, GEN mod)
{
  GEN B;
  GEN D = ZMrow_ZC_mul(H, gel(A,1), 1);
  GEN g = gcdii(D, mod);
  if (!equali1(g))
  {
    mod = diviiexact(mod, g);
    H = FpM_red(H, mod);
  }
  D = Fp_inv(Fp_red(D, mod), mod);
  H = FpM_Fp_mul(H, D, mod);
  B = sqrti(shifti(mod,-1));
  return FpM_ratlift(H, mod, B, B, NULL);
}

GEN
ZM_inv(GEN A, GEN *pden)
{
  pari_sp av = avma;
  long m = lg(A)-1, n, k1 = 1, k2;
  GEN H = NULL, D, H1 = NULL, mod1 = NULL, worker;
  ulong bnd, mask, p = 0;
  pari_timer ti;

  if (m == 0) return ZM_inv0(A,pden);
  if (pden) *pden = gen_1;
  if (nbrows(A) < m) return NULL;
  if (m == 1 && nbrows(A)==1) return ZM_inv1(A,pden);
  if (m == 2 && nbrows(A)==2) return ZM_inv2(A,pden);

  if (DEBUGLEVEL>=5) timer_start(&ti);
  bnd = expi(RgM_true_Hadamard(A));
  worker = strtoclosure("_ZM_inv_worker", 1, A);
  gen_inccrt("ZM_inv_r", worker, NULL, k1, m, &p, &H1, &mod1, nmV_chinese_center, FpM_center);
  n = (bnd+1)/expu(p)+1;
  if (DEBUGLEVEL>=5) timer_printf(&ti,"inv (%ld/%ld primes)", k1, n);
  mask = quadratic_prec_mask(n);
  for (k2 = 0;;)
  {
    GEN Hr;
    if (k2 > 0)
    {
      gen_inccrt("ZM_inv_r", worker, NULL, k2, m, &p, &H1, &mod1,nmV_chinese_center,FpM_center);
      k1 += k2;
      if (DEBUGLEVEL>=5) timer_printf(&ti,"CRT (%ld/%ld primes)", k1, n);
    }
    if (mask == 1) break;
    k2 = (mask&1UL) ? k1-1: k1;
    mask >>= 1;

    Hr = ZM_adj_ratlift(A, H1, mod1);
    if (DEBUGLEVEL>=5) timer_printf(&ti,"ratlift (%ld/%ld primes)", k1, n);
    if (Hr) {/* DONE ? */
      GEN den;
      GEN Hl = Q_remove_denom(Hr, &den);
      GEN R = ZM_mul(Hl, A);
      if (DEBUGLEVEL>=5) timer_printf(&ti,"mult (%ld/%ld primes)", k1, n);
      den = den ? den: gen_1;
      if (den)
      {
        if (ZM_isscalar(R, den))
        {
          H = Hl;
          if (pden) *pden = den;
          break;
        }
      }
      else
        if (ZM_isidentity(R)) { H=Hl; break; }
    }
  }
  if (!H)
  {
    GEN d;
    H = H1;
    D = ZMrow_ZC_mul(H, gel(A,1), 1);
    if (signe(D)==0) pari_err_INV("ZM_inv", A);
    d = gcdii(Q_content_safe(H), D);
    if (signe(D) < 0) d = negi(d);
    if (!equali1(d))
    {
      H = ZM_Z_divexact(H, d);
      D = diviiexact(D, d);
    }
    if (pden) *pden = D;
  }
  gerepileall(av, pden? 2: 1, &H, pden);
  return H;
}

/* same as above, M rational */
GEN
QM_inv(GEN M)
{
  pari_sp av = avma;
  GEN den, cM, K;
  M = Q_primitive_part(M, &cM);
  K = ZM_inv(M, &den);
  if (!K) { avma = av; return NULL; }
  cM = inv_content(mul_content(cM, den));
  if (cM) K = RgM_Rg_div(K, cM);
  return gerepileupto(av, K);
}

static GEN
ZM_ker_i(GEN M, long fl)
{
  pari_sp av2, av = avma;
  GEN q, H, D;
  forprime_t S;
  av2 = avma;
  H = NULL; D = NULL;
  if (lg(M)==1) return cgetg(1, t_MAT);
  init_modular_big(&S);
  for(;;)
  {
    GEN Kp, Hp, Dp, Mp, Hr, B;
    ulong p = u_forprime_next(&S);
    Mp = ZM_to_Flm(M, p);
    Kp = Flm_ker_sp(Mp, p, 2);
    Hp = gel(Kp,1); Dp = gel(Kp,2);
    if (H && (lg(Hp)>lg(H) || (lg(Hp)==lg(H) && vecsmall_lexcmp(Dp,D)>0))) continue;
    if (!H || (lg(Hp)<lg(H) || vecsmall_lexcmp(Dp,D)<0))
    {
      H = ZM_init_CRT(Hp, p); D = Dp;
      q = utoipos(p);
    }
    else
      ZM_incremental_CRT(&H, Hp, &q, p);
    B = sqrti(shifti(q,-1));
    Hr = FpM_ratlift(H, q, B, B, NULL);
    if (DEBUGLEVEL>5) err_printf("ZM_ker mod %lu (ratlift=%ld)\n", p,!!Hr);
    if (Hr) {/* DONE ? */
      GEN MH = QM_mul(M, Hr);
      if (gequal0(MH)) { H = fl ? vec_Q_primpart(Hr): Hr;  break; }
    }
    if (gc_needed(av,2))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"ZM_ker");
      gerepileall(av2, 3, &H, &D, &q);
    }
  }
  return gerepilecopy(av, H);
}

GEN
ZM_ker(GEN M)
{ return ZM_ker_i(M, 1); }

GEN
QM_ker(GEN M)
{
  pari_sp av = avma;
  long l = lg(M)-1;
  if (l==0) return cgetg(1, t_MAT);
  if (lgcols(M)==1) return matid(l);
  M = shallowtrans(vec_Q_primpart(shallowtrans(M)));
  return gerepileupto(av, ZM_ker_i(M, 0));
}

/* x a ZM. Return a multiple of the determinant of the lattice generated by
 * the columns of x. From Algorithm 2.2.6 in GTM138 */
GEN
detint(GEN A)
{
  if (typ(A) != t_MAT) pari_err_TYPE("detint",A);
  RgM_check_ZM(A, "detint");
  return ZM_detmult(A);
}
GEN
ZM_detmult(GEN A)
{
  pari_sp av1, av = avma;
  GEN B, c, v, piv;
  long rg, i, j, k, m, n = lg(A) - 1;

  if (!n) return gen_1;
  m = nbrows(A);
  if (n < m) return gen_0;
  c = zero_zv(m);
  av1 = avma;
  B = zeromatcopy(m,m);
  v = cgetg(m+1, t_COL);
  piv = gen_1; rg = 0;
  for (k=1; k<=n; k++)
  {
    GEN pivprec = piv;
    long t = 0;
    for (i=1; i<=m; i++)
    {
      pari_sp av2 = avma;
      GEN vi;
      if (c[i]) continue;

      vi = mulii(piv, gcoeff(A,i,k));
      for (j=1; j<=m; j++)
        if (c[j]) vi = addii(vi, mulii(gcoeff(B,j,i),gcoeff(A,j,k)));
      if (!t && signe(vi)) t = i;
      gel(v,i) = gerepileuptoint(av2, vi);
    }
    if (!t) continue;
    /* at this point c[t] = 0 */

    if (++rg >= m) { /* full rank; mostly done */
      GEN det = gel(v,t); /* last on stack */
      if (++k > n)
        det = absi(det);
      else
      {
        /* improve further; at this point c[i] is set for all i != t */
        gcoeff(B,t,t) = piv; v = centermod(gel(B,t), det);
        for ( ; k<=n; k++)
          det = gcdii(det, ZV_dotproduct(v, gel(A,k)));
      }
      return gerepileuptoint(av, det);
    }

    piv = gel(v,t);
    for (i=1; i<=m; i++)
    {
      GEN mvi;
      if (c[i] || i == t) continue;

      gcoeff(B,t,i) = mvi = negi(gel(v,i));
      for (j=1; j<=m; j++)
        if (c[j]) /* implies j != t */
        {
          pari_sp av2 = avma;
          GEN z = addii(mulii(gcoeff(B,j,i), piv), mulii(gcoeff(B,j,t), mvi));
          if (rg > 1) z = diviiexact(z, pivprec);
          gcoeff(B,j,i) = gerepileuptoint(av2, z);
        }
    }
    c[t] = k;
    if (gc_needed(av,1))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"detint. k=%ld",k);
      gerepileall(av1, 2, &piv,&B); v = zerovec(m);
    }
  }
  avma = av; return gen_0;
}

/* Reduce x modulo (invertible) y */
GEN
closemodinvertible(GEN x, GEN y)
{
  return gmul(y, ground(RgM_solve(y,x)));
}
GEN
reducemodinvertible(GEN x, GEN y)
{
  return gsub(x, closemodinvertible(x,y));
}
GEN
reducemodlll(GEN x,GEN y)
{
  return reducemodinvertible(x, ZM_lll(y, 0.75, LLL_INPLACE));
}

/*******************************************************************/
/*                                                                 */
/*                    KERNEL of an m x n matrix                    */
/*          return n - rk(x) linearly independent vectors          */
/*                                                                 */
/*******************************************************************/
static GEN
RgM_deplin_i(GEN x0)
{
  pari_sp av = avma, av2;
  long i, j, k, nl, nc = lg(x0)-1;
  GEN D, x, y, c, l, d, ck;

  if (!nc) { avma=av; return NULL; }
  nl = nbrows(x0);
  c = zero_zv(nl);
  l = cgetg(nc+1, t_VECSMALL); /* not initialized */
  av2 = avma;
  x = RgM_shallowcopy(x0);
  d = const_vec(nl, gen_1); /* pivot list */
  ck = NULL; /* gcc -Wall */
  for (k=1; k<=nc; k++)
  {
    ck = gel(x,k);
    for (j=1; j<k; j++)
    {
      GEN cj = gel(x,j), piv = gel(d,j), q = gel(ck,l[j]);
      for (i=1; i<=nl; i++)
        if (i!=l[j]) gel(ck,i) = gsub(gmul(piv, gel(ck,i)), gmul(q, gel(cj,i)));
    }

    i = gauss_get_pivot_NZ(x, NULL, k, c);
    if (i > nl) break;
    if (gc_needed(av,1))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"deplin k = %ld/%ld",k,nc);
      gerepileall(av2, 2, &x, &d);
      ck = gel(x,k);
    }
    gel(d,k) = gel(ck,i);
    c[i] = k; l[k] = i; /* pivot d[k] in x[i,k] */
  }
  if (k > nc) { avma = av; return NULL; }
  if (k == 1) { avma = av; return scalarcol_shallow(gen_1,nc); }
  y = cgetg(nc+1,t_COL);
  gel(y,1) = gcopy(gel(ck, l[1]));
  for (D=gel(d,1),j=2; j<k; j++)
  {
    gel(y,j) = gmul(gel(ck, l[j]), D);
    D = gmul(D, gel(d,j));
  }
  gel(y,j) = gneg(D);
  for (j++; j<=nc; j++) gel(y,j) = gen_0;
  y = primitive_part(y, &c);
  return c? gerepileupto(av, y): gerepilecopy(av, y);
}
static GEN
RgV_deplin(GEN v)
{
  pari_sp av = avma;
  long n = lg(v)-1;
  GEN y, p = NULL;
  if (n <= 1)
  {
    if (n == 1 && gequal0(gel(v,1))) return mkcol(gen_1);
    return cgetg(1, t_COL);
  }
  if (gequal0(gel(v,1))) return scalarcol_shallow(gen_1, n);
  v = primpart(mkvec2(gel(v,1),gel(v,2)));
  if (RgV_is_FpV(v, &p) && p) v = centerlift(v);
  y = zerocol(n);
  gel(y,1) = gneg(gel(v,2));
  gel(y,2) = gcopy(gel(v,1));
  return gerepileupto(av, y);

}

static GEN
RgM_deplin_FpM(GEN x, GEN p)
{
  pari_sp av = avma;
  ulong pp;
  x = RgM_Fp_init(x, p, &pp);
  switch(pp)
  {
  case 0:
    x = FpM_ker_gen(x,p,1);
    if (!x) { avma = av; return NULL; }
    x = FpC_center(x,p,shifti(p,-1));
    break;
  case 2:
    x = F2m_ker_sp(x,1);
    if (!x) { avma = av; return NULL; }
    x = F2c_to_ZC(x); break;
  default:
    x = Flm_ker_sp(x,pp,1);
    if (!x) { avma = av; return NULL; }
    x = Flv_center(x, pp, pp>>1);
    x = zc_to_ZC(x);
    break;
  }
  return gerepileupto(av, x);
}

/* FIXME: implement direct modular ZM_deplin ? */
static GEN
QM_deplin(GEN M)
{
  pari_sp av = avma;
  long l = lg(M)-1;
  GEN k;
  if (l==0) return NULL;
  if (lgcols(M)==1) return col_ei(l, 1);
  M = shallowtrans(vec_Q_primpart(shallowtrans(M)));
  k = ZM_ker_i(M, 1);
  if (lg(k)== 1) { avma = av; return NULL; }
  return gerepilecopy(av, gel(k,1));
}

static GEN
RgM_deplin_FqM(GEN x, GEN pol, GEN p)
{
  pari_sp av = avma;
  GEN b, T = RgX_to_FpX(pol, p);
  if (signe(T) == 0) pari_err_OP("deplin",x,pol);
  b = FqM_deplin(RgM_to_FqM(x, T, p), T, p);
  return gerepileupto(av, b);
}

#define code(t1,t2) ((t1 << 6) | t2)
static GEN
RgM_deplin_fast(GEN x)
{
  GEN p, pol;
  long pa;
  long t = RgM_type(x, &p,&pol,&pa);
  switch(t)
  {
    case t_INT:    /* fall through */
    case t_FRAC:   return QM_deplin(x);
    case t_FFELT:  return FFM_deplin(x, pol);
    case t_INTMOD: return RgM_deplin_FpM(x, p);
    case code(t_POLMOD, t_INTMOD):
                   return RgM_deplin_FqM(x, pol, p);
    default:       return gen_0;
  }
}
#undef code

static GEN
RgM_deplin(GEN x)
{
  GEN z = RgM_deplin_fast(x);
  if (z!= gen_0) return z;
  return RgM_deplin_i(x);
}

GEN
deplin(GEN x)
{
  switch(typ(x))
  {
    case t_MAT:
    {
      GEN z = RgM_deplin(x);
      if (z) return z;
      return cgetg(1, t_COL);
    }
    case t_VEC: return RgV_deplin(x);
    default: pari_err_TYPE("deplin",x);
  }
  return NULL;/*LCOV_EXCL_LINE*/
}

/*******************************************************************/
/*                                                                 */
/*         GAUSS REDUCTION OF MATRICES  (m lines x n cols)         */
/*           (kernel, image, complementary image, rank)            */
/*                                                                 */
/*******************************************************************/
/* return the transform of x under a standard Gauss pivot.
 * x0 is a reference point when guessing whether x[i,j] ~ 0
 * (iff x[i,j] << x0[i,j])
 * Set r = dim ker(x). d[k] contains the index of the first non-zero pivot
 * in column k */
static GEN
gauss_pivot_ker(GEN x, GEN x0, GEN *dd, long *rr)
{
  GEN c, d, p, data;
  pari_sp av;
  long i, j, k, r, t, n, m;
  pivot_fun pivot;

  n=lg(x)-1; if (!n) { *dd=NULL; *rr=0; return cgetg(1,t_MAT); }
  m=nbrows(x); r=0;
  pivot = get_pivot_fun(x, x0, &data);
  x = RgM_shallowcopy(x);
  c = zero_zv(m);
  d = cgetg(n+1,t_VECSMALL);
  av=avma;
  for (k=1; k<=n; k++)
  {
    j = pivot(x, data, k, c);
    if (j > m)
    {
      r++; d[k]=0;
      for(j=1; j<k; j++)
        if (d[j]) gcoeff(x,d[j],k) = gclone(gcoeff(x,d[j],k));
    }
    else
    { /* pivot for column k on row j */
      c[j]=k; d[k]=j; p = gdiv(gen_m1,gcoeff(x,j,k));
      gcoeff(x,j,k) = gen_m1;
      /* x[j,] /= - x[j,k] */
      for (i=k+1; i<=n; i++) gcoeff(x,j,i) = gmul(p,gcoeff(x,j,i));
      for (t=1; t<=m; t++)
        if (t!=j)
        { /* x[t,] -= 1 / x[j,k] x[j,] */
          p = gcoeff(x,t,k); gcoeff(x,t,k) = gen_0;
          for (i=k+1; i<=n; i++)
            gcoeff(x,t,i) = gadd(gcoeff(x,t,i),gmul(p,gcoeff(x,j,i)));
          if (gc_needed(av,1)) gerepile_gauss_ker(x,k,t,av);
        }
    }
  }
  *dd=d; *rr=r; return x;
}

static GEN FpM_gauss_pivot(GEN x, GEN p, long *rr);
static GEN FqM_gauss_pivot(GEN x, GEN T, GEN p, long *rr);
static GEN F2m_gauss_pivot(GEN x, long *rr);

/* r = dim ker(x).
 * Returns d:
 *   d[k] != 0 contains the index of a non-zero pivot in column k
 *   d[k] == 0 if column k is a linear combination of the (k-1) first ones */
GEN
RgM_pivots(GEN x0, GEN data, long *rr, pivot_fun pivot)
{
  GEN x, c, d, p;
  long i, j, k, r, t, m, n = lg(x0)-1;
  pari_sp av;

  if (RgM_is_ZM(x0)) return ZM_pivots(x0, rr);
  if (!n) { *rr = 0; return NULL; }

  d = cgetg(n+1, t_VECSMALL);
  x = RgM_shallowcopy(x0);
  m = nbrows(x); r = 0;
  c = zero_zv(m);
  av = avma;
  for (k=1; k<=n; k++)
  {
    j = pivot(x, data, k, c);
    if (j > m) { r++; d[k] = 0; }
    else
    {
      c[j] = k; d[k] = j; p = gdiv(gen_m1, gcoeff(x,j,k));
      for (i=k+1; i<=n; i++) gcoeff(x,j,i) = gmul(p,gcoeff(x,j,i));

      for (t=1; t<=m; t++)
        if (!c[t]) /* no pivot on that line yet */
        {
          p = gcoeff(x,t,k); gcoeff(x,t,k) = gen_0;
          for (i=k+1; i<=n; i++)
            gcoeff(x,t,i) = gadd(gcoeff(x,t,i), gmul(p, gcoeff(x,j,i)));
          if (gc_needed(av,1)) gerepile_gauss(x,k,t,av,j,c);
        }
      for (i=k; i<=n; i++) gcoeff(x,j,i) = gen_0; /* dummy */
    }
  }
  *rr = r; avma = (pari_sp)d; return d;
}

static long
ZM_count_0_cols(GEN M)
{
  long i, l = lg(M), n = 0;
  for (i = 1; i < l; i++)
    if (ZV_equal0(gel(M,i))) n++;
  return n;
}

static void indexrank_all(long m, long n, long r, GEN d, GEN *prow, GEN *pcol);
/* As RgM_pivots, integer entries. Set *rr = dim Ker M0 */
GEN
ZM_pivots(GEN M0, long *rr)
{
  GEN d, dbest = NULL;
  long m, n, i, imax, rmin, rbest, zc;
  int beenthere = 0;
  pari_sp av, av0 = avma;
  forprime_t S;

  rbest = n = lg(M0)-1;
  if (n == 0) { *rr = 0; return NULL; }
  zc = ZM_count_0_cols(M0);
  if (n == zc) { *rr = zc; return zero_zv(n); }

  m = nbrows(M0);
  rmin = maxss(zc, n-m);
  init_modular_small(&S);
  imax = (n < (1<<4))? 1: (n>>3); /* heuristic */

  for(;;)
  {
    GEN row, col, M, KM, IM, RHS, X, cX;
    long rk;
    for (av = avma, i = 0;; avma = av, i++)
    {
      ulong p = u_forprime_next(&S);
      long rp;
      if (!p) pari_err_OVERFLOW("ZM_pivots [ran out of primes]");
      d = Flm_pivots(ZM_to_Flm(M0, p), p, &rp, 1);
      if (rp == rmin) { rbest = rp; goto END; } /* maximal rank, return */
      if (rp < rbest) { /* save best r so far */
        rbest = rp;
        if (dbest) gunclone(dbest);
        dbest = gclone(d);
        if (beenthere) break;
      }
      if (!beenthere && i >= imax) break;
    }
    beenthere = 1;
    /* Dubious case: there is (probably) a non trivial kernel */
    indexrank_all(m,n, rbest, dbest, &row, &col);
    M = rowpermute(vecpermute(M0, col), row);
    rk = n - rbest; /* (probable) dimension of image */
    IM = vecslice(M,1,rk);
    KM = vecslice(M,rk+1, n);
    M = rowslice(IM, 1,rk); /* square maximal rank */
    X = ZM_gauss(M, rowslice(KM, 1,rk));
    X = Q_remove_denom(X, &cX);
    RHS = rowslice(KM,rk+1,m);
    if (cX) RHS = ZM_Z_mul(RHS, cX);
    if (ZM_equal(ZM_mul(rowslice(IM,rk+1,m), X), RHS))
    {
      d = vecsmall_copy(dbest);
      goto END;
    }
    avma = av;
  }
END:
  *rr = rbest; if (dbest) gunclone(dbest);
  return gerepileuptoleaf(av0, d);
}

/* set *pr = dim Ker x */
static GEN
gauss_pivot(GEN x, long *pr) {
  GEN data;
  pivot_fun pivot = get_pivot_fun(x, x, &data);
  return RgM_pivots(x, data, pr, pivot);
}

/* compute ker(x), x0 is a reference point when guessing whether x[i,j] ~ 0
 * (iff x[i,j] << x0[i,j]) */
static GEN
ker_aux(GEN x, GEN x0)
{
  pari_sp av = avma;
  GEN d,y;
  long i,j,k,r,n;

  x = gauss_pivot_ker(x,x0,&d,&r);
  if (!r) { avma=av; return cgetg(1,t_MAT); }
  n = lg(x)-1; y=cgetg(r+1,t_MAT);
  for (j=k=1; j<=r; j++,k++)
  {
    GEN p = cgetg(n+1,t_COL);

    gel(y,j) = p; while (d[k]) k++;
    for (i=1; i<k; i++)
      if (d[i])
      {
        GEN p1=gcoeff(x,d[i],k);
        gel(p,i) = gcopy(p1); gunclone(p1);
      }
      else
        gel(p,i) = gen_0;
    gel(p,k) = gen_1; for (i=k+1; i<=n; i++) gel(p,i) = gen_0;
  }
  return gerepileupto(av,y);
}

static GEN
RgM_ker_FpM(GEN x, GEN p)
{
  pari_sp av = avma;
  ulong pp;
  x = RgM_Fp_init(x, p, &pp);
  switch(pp)
  {
    case 0: x = FpM_to_mod(FpM_ker_gen(x,p,0),p); break;
    case 2: x = F2m_to_mod(F2m_ker_sp(x,0)); break;
    default:x = Flm_to_mod(Flm_ker_sp(x,pp,0), pp); break;
  }
  return gerepileupto(av, x);
}

static GEN
RgM_ker_FqM(GEN x, GEN pol, GEN p)
{
  pari_sp av = avma;
  GEN b, T = RgX_to_FpX(pol, p);
  if (signe(T) == 0) pari_err_OP("ker",x,pol);
  b = FqM_ker(RgM_to_FqM(x, T, p), T, p);
  return gerepileupto(av, FqM_to_mod(b, T, p));
}

#define code(t1,t2) ((t1 << 6) | t2)
static GEN
RgM_ker_fast(GEN x)
{
  GEN p, pol;
  long pa;
  long t = RgM_type(x, &p,&pol,&pa);
  switch(t)
  {
    case t_INT:    /* fall through */
    case t_FRAC:   return QM_ker(x);
    case t_FFELT:  return FFM_ker(x, pol);
    case t_INTMOD: return RgM_ker_FpM(x, p);
    case code(t_POLMOD, t_INTMOD):
                   return RgM_ker_FqM(x, pol, p);
    default:       return NULL;
  }
}
#undef code

GEN
ker(GEN x)
{
  GEN b = RgM_ker_fast(x);
  if (b) return b;
  return ker_aux(x,x);
}

GEN
matker0(GEN x,long flag)
{
  if (typ(x)!=t_MAT) pari_err_TYPE("matker",x);
  if (!flag) return ker(x);
  RgM_check_ZM(x, "matker");
  return ZM_ker(x);
}

static GEN
RgM_image_FpM(GEN x, GEN p)
{
  pari_sp av = avma;
  ulong pp;
  x = RgM_Fp_init(x, p, &pp);
  switch(pp)
  {
    case 0: x = FpM_to_mod(FpM_image(x,p),p); break;
    case 2: x = F2m_to_mod(F2m_image(x)); break;
    default:x = Flm_to_mod(Flm_image(x,pp), pp); break;
  }
  return gerepileupto(av, x);
}

static GEN
RgM_image_FqM(GEN x, GEN pol, GEN p)
{
  pari_sp av = avma;
  GEN b, T = RgX_to_FpX(pol, p);
  if (signe(T) == 0) pari_err_OP("image",x,pol);
  b = FqM_image(RgM_to_FqM(x, T, p), T, p);
  return gerepileupto(av, FqM_to_mod(b, T, p));
}

static GEN
QM_image(GEN A)
{
  pari_sp av = avma;
  GEN M = vecpermute(A, ZM_indeximage(vec_Q_primpart(A)));
  return gerepilecopy(av, M);
}

#define code(t1,t2) ((t1 << 6) | t2)
static GEN
RgM_image_fast(GEN x)
{
  GEN p, pol;
  long pa;
  long t = RgM_type(x, &p,&pol,&pa);
  switch(t)
  {
    case t_INT:    /* fall through */
    case t_FRAC:   return QM_image(x);
    case t_FFELT:  return FFM_image(x, pol);
    case t_INTMOD: return RgM_image_FpM(x, p);
    case code(t_POLMOD, t_INTMOD):
                   return RgM_image_FqM(x, pol, p);
    default:       return NULL;
  }
}
#undef code

GEN
image(GEN x)
{
  GEN d, M;
  long r;

  if (typ(x)!=t_MAT) pari_err_TYPE("matimage",x);
  M = RgM_image_fast(x);
  if (M) return M;
  d = gauss_pivot(x,&r); /* d left on stack for efficiency */
  return image_from_pivot(x,d,r);
}

static GEN
imagecompl_aux(GEN x, GEN(*PIVOT)(GEN,long*))
{
  pari_sp av = avma;
  GEN d,y;
  long j,i,r;

  if (typ(x)!=t_MAT) pari_err_TYPE("imagecompl",x);
  (void)new_chunk(lg(x) * 4 + 1); /* HACK */
  d = PIVOT(x,&r); /* if (!d) then r = 0 */
  avma = av; y = cgetg(r+1,t_VECSMALL);
  for (i=j=1; j<=r; i++)
    if (!d[i]) y[j++] = i;
  return y;
}
GEN
imagecompl(GEN x) { return imagecompl_aux(x, &gauss_pivot); }
GEN
ZM_imagecompl(GEN x) { return imagecompl_aux(x, &ZM_pivots); }

GEN
FpM_FpC_invimage(GEN A, GEN y, GEN p)
{
  pari_sp av = avma;
  long i, l = lg(A);
  GEN M, x, t;

  if (lgefint(p) == 3)
  {
    ulong pp = p[2];
    A = ZM_to_Flm(A, pp);
    y = ZV_to_Flv(y, pp);
    x = Flm_Flc_invimage(A,y,pp);
    if (!x) { avma = av; return NULL; }
    return gerepileupto(av, Flc_to_ZC(x));
  }
  if (l==1) return NULL;
  if (lg(y) != lgcols(A)) pari_err_DIM("FpM_FpC_invimage");
  M = FpM_ker(shallowconcat(A,y),p);
  i = lg(M)-1; if (!i) { avma = av; return NULL; }

  x = gel(M,i); t = gel(x,l);
  if (!signe(t)) { avma = av; return NULL; }

  setlg(x,l); t = Fp_inv(negi(t),p);
  if (is_pm1(t)) return gerepilecopy(av, x);
  return gerepileupto(av, FpC_Fp_mul(x, t, p));
}
GEN
Flm_Flc_invimage(GEN A, GEN y, ulong p)
{
  pari_sp av = avma;
  long i, l = lg(A);
  GEN M, x;
  ulong t;

  if (l==1) return NULL;
  if (lg(y) != lgcols(A)) pari_err_DIM("Flm_Flc_invimage");
  M = cgetg(l+1,t_MAT);
  for (i=1; i<l; i++) gel(M,i) = gel(A,i);
  gel(M,l) = y; M = Flm_ker(M,p);
  i = lg(M)-1; if (!i) { avma = av; return NULL; }

  x = gel(M,i); t = x[l];
  if (!t) { avma = av; return NULL; }

  setlg(x,l); t = Fl_inv(Fl_neg(t,p),p);
  if (t!=1) x = Flv_Fl_mul(x, t, p);
  return gerepileuptoleaf(av, x);
}
GEN
F2m_F2c_invimage(GEN A, GEN y)
{
  pari_sp av = avma;
  long i, l = lg(A);
  GEN M, x;

  if (l==1) return NULL;
  if (lg(y) != lgcols(A)) pari_err_DIM("F2m_F2c_invimage");
  M = cgetg(l+1,t_MAT);
  for (i=1; i<l; i++) gel(M,i) = gel(A,i);
  gel(M,l) = y; M = F2m_ker(M);
  i = lg(M)-1; if (!i) { avma = av; return NULL; }

  x = gel(M,i);
  if (!F2v_coeff(x,l)) { avma = av; return NULL; }
  F2v_clear(x, x[1]); x[1]--; /* remove last coord */
  return gerepileuptoleaf(av, x);
}

static GEN
RgM_RgC_invimage_FpC(GEN A, GEN y, GEN p)
{
  pari_sp av = avma;
  ulong pp;
  GEN x;
  A = RgM_Fp_init(A,p,&pp);
  switch(pp)
  {
  case 0:
    y = RgC_to_FpC(y,p);
    x = FpM_FpC_invimage(A, y, p);
    return x ? gerepileupto(av, FpC_to_mod(x,p)): NULL;
  case 2:
    y = RgV_to_F2v(y);
    x = F2m_F2c_invimage(A, y);
    return x ? gerepileupto(av, F2c_to_mod(x)): NULL;
  default:
    y = RgV_to_Flv(y,pp);
    x = Flm_Flc_invimage(A, y, pp);
    return x ? gerepileupto(av, Flc_to_mod(x,pp)): NULL;
  }
}

static GEN
RgM_RgC_invimage_fast(GEN x, GEN y)
{
  GEN p, pol;
  long pa;
  long t = RgM_RgC_type(x, y, &p,&pol,&pa);
  switch(t)
  {
    case t_INTMOD: return RgM_RgC_invimage_FpC(x, y, p);
    case t_FFELT:  return FFM_FFC_invimage(x, y, pol);
    default:       return gen_0;
  }
}

GEN
RgM_RgC_invimage(GEN A, GEN y)
{
  pari_sp av = avma;
  long i, l = lg(A);
  GEN M, x, t;
  if (l==1) return NULL;
  if (lg(y) != lgcols(A)) pari_err_DIM("inverseimage");
  M = RgM_RgC_invimage_fast(A, y);
  if (!M) {avma = av; return NULL; }
  if (M != gen_0) return M;
  M = ker(shallowconcat(A, y));
  i = lg(M)-1;
  if (!i) { avma = av; return NULL; }

  x = gel(M,i); t = gel(x,l);
  if (gequal0(t)) { avma = av; return NULL; }

  t = gneg_i(t); setlg(x,l);
  return gerepileupto(av, RgC_Rg_div(x, t));
}

/* Return X such that m X = v (t_COL or t_MAT), resp. an empty t_COL / t_MAT
 * if no solution exist */
GEN
inverseimage(GEN m, GEN v)
{
  GEN y;
  if (typ(m)!=t_MAT) pari_err_TYPE("inverseimage",m);
  switch(typ(v))
  {
    case t_COL:
      y = RgM_RgC_invimage(m,v);
      return y? y: cgetg(1,t_COL);
    case t_MAT:
      y = RgM_invimage(m, v);
      return y? y: cgetg(1,t_MAT);
  }
  pari_err_TYPE("inverseimage",v);
  return NULL;/*LCOV_EXCL_LINE*/
}

static GEN
Flm_invimage_CUP(GEN A, GEN B, ulong p) {
  pari_sp av = avma;
  GEN R, Rc, C, U, P, B1, B2, C1, C2, X, Y, Z;
  long r;
  r = Flm_CUP(A, &R, &C, &U, &P, p);
  Rc = indexcompl(R, nbrows(B));
  C1 = rowpermute(C, R);
  C2 = rowpermute(C, Rc);
  B1 = rowpermute(B, R);
  B2 = rowpermute(B, Rc);
  Z = Flm_rsolve_lower_unit(C1, B1, p);
  if (!gequal(Flm_mul(C2, Z, p), B2))
    return NULL;
  Y = vconcat(Flm_rsolve_upper(vecslice(U, 1, r), Z, p),
              zero_Flm(lg(A) - 1 - r, lg(B) - 1));
  X = rowpermute(Y, perm_inv(P));
  return gerepileupto(av, X);
}

static GEN
Flm_invimage_i(GEN A, GEN B, ulong p)
{
  GEN d, x, X, Y;
  long i, j, nY, nA = lg(A)-1, nB = lg(B)-1;

  if (!nB) return cgetg(1, t_MAT);
  if (nA + nB >= Flm_CUP_LIMIT && nbrows(B) >= Flm_CUP_LIMIT)
    return Flm_invimage_CUP(A, B, p);

  x = Flm_ker_sp(shallowconcat(Flm_neg(A,p), B), p, 0);
  /* AX = BY, Y in strict upper echelon form with pivots = 1.
   * We must find T such that Y T = Id_nB then X T = Z. This exists iff
   * Y has at least nB columns and full rank */
  nY = lg(x)-1;
  if (nY < nB) return NULL;
  Y = rowslice(x, nA+1, nA+nB); /* nB rows */
  d = cgetg(nB+1, t_VECSMALL);
  for (i = nB, j = nY; i >= 1; i--, j--)
  {
    for (; j>=1; j--)
      if (coeff(Y,i,j)) { d[i] = j; break; }
    if (!j) return NULL;
  }
  /* reduce to the case Y square, upper triangular with 1s on diagonal */
  Y = vecpermute(Y, d);
  x = vecpermute(x, d);
  X = rowslice(x, 1, nA);
  return Flm_mul(X, Flm_inv_upper_1(Y,p), p);
}

static GEN
F2m_invimage_i(GEN A, GEN B)
{
  GEN d, x, X, Y;
  long i, j, nY, nA = lg(A)-1, nB = lg(B)-1;
  x = F2m_ker_sp(shallowconcat(A, B), 0);
  /* AX = BY, Y in strict upper echelon form with pivots = 1.
   * We must find T such that Y T = Id_nB then X T = Z. This exists iff
   * Y has at least nB columns and full rank */
  nY = lg(x)-1;
  if (nY < nB) return NULL;

  /* implicitly: Y = rowslice(x, nA+1, nA+nB), nB rows */
  d = cgetg(nB+1, t_VECSMALL);
  for (i = nB, j = nY; i >= 1; i--, j--)
  {
    for (; j>=1; j--)
      if (F2m_coeff(x,nA+i,j)) { d[i] = j; break; } /* Y[i,j] */
    if (!j) return NULL;
  }
  x = vecpermute(x, d);

  X = F2m_rowslice(x, 1, nA);
  Y = F2m_rowslice(x, nA+1, nA+nB);
  return F2m_mul(X, F2m_inv_upper_1(Y));
}
GEN
Flm_invimage(GEN A, GEN B, ulong p)
{
  pari_sp av = avma;
  GEN X = Flm_invimage_i(A,B,p);
  if (!X) { avma = av; return NULL; }
  return gerepileupto(av, X);
}
GEN
F2m_invimage(GEN A, GEN B)
{
  pari_sp av = avma;
  GEN X = F2m_invimage_i(A,B);
  if (!X) { avma = av; return NULL; }
  return gerepileupto(av, X);
}
static GEN
FpM_invimage_i(GEN A, GEN B, GEN p)
{
  GEN d, x, X, Y;
  long i, j, nY, nA = lg(A)-1, nB = lg(B)-1;
  if (lgefint(p) == 3)
  {
    ulong pp = p[2];
    A = ZM_to_Flm(A, pp);
    B = ZM_to_Flm(B, pp);
    x = Flm_invimage_i(A, B, pp);
    return x? Flm_to_ZM(x): NULL;
  }
  x = FpM_ker(shallowconcat(ZM_neg(A), B), p);
  /* AX = BY, Y in strict upper echelon form with pivots = 1.
   * We must find T such that Y T = Id_nB then X T = Z. This exists iff
   * Y has at least nB columns and full rank */
  nY = lg(x)-1;
  if (nY < nB) return NULL;
  Y = rowslice(x, nA+1, nA+nB); /* nB rows */
  d = cgetg(nB+1, t_VECSMALL);
  for (i = nB, j = nY; i >= 1; i--, j--)
  {
    for (; j>=1; j--)
      if (signe(gcoeff(Y,i,j))) { d[i] = j; break; }
    if (!j) return NULL;
  }
  /* reduce to the case Y square, upper triangular with 1s on diagonal */
  Y = vecpermute(Y, d);
  x = vecpermute(x, d);
  X = rowslice(x, 1, nA);
  return FpM_mul(X, FpM_inv_upper_1(Y,p), p);
}
GEN
FpM_invimage(GEN A, GEN B, GEN p)
{
  pari_sp av = avma;
  GEN X = FpM_invimage_i(A,B,p);
  if (!X) { avma = av; return NULL; }
  return gerepileupto(av, X);
}

static GEN
RgM_invimage_FpM(GEN A, GEN B, GEN p)
{
  pari_sp av = avma;
  ulong pp;
  GEN x;
  A = RgM_Fp_init(A,p,&pp);
  switch(pp)
  {
  case 0:
    B = RgM_to_FpM(B,p);
    x = FpM_invimage_i(A, B, p);
    return x ? gerepileupto(av, FpM_to_mod(x, p)): x;
  case 2:
    B = RgM_to_F2m(B);
    x = F2m_invimage_i(A, B);
    return x ? gerepileupto(av, F2m_to_mod(x)): x;
  default:
    B = RgM_to_Flm(B,pp);
    x = Flm_invimage_i(A, B, pp);
    return x ? gerepileupto(av, Flm_to_mod(x, pp)): x;
  }
}

static GEN
RgM_invimage_fast(GEN x, GEN y)
{
  GEN p, pol;
  long pa;
  long t = RgM_type2(x, y, &p,&pol,&pa);
  switch(t)
  {
    case t_INTMOD: return RgM_invimage_FpM(x, y, p);
    case t_FFELT:  return FFM_invimage(x, y, pol);
    default:       return gen_0;
  }
}

/* find Z such that A Z = B. Return NULL if no solution */
GEN
RgM_invimage(GEN A, GEN B)
{
  pari_sp av = avma;
  GEN d, x, X, Y;
  long i, j, nY, nA = lg(A)-1, nB = lg(B)-1;
  X = RgM_invimage_fast(A, B);
  if (!X) {avma = av; return NULL; }
  if (X != gen_0) return X;
  x = ker(shallowconcat(RgM_neg(A), B));
  /* AX = BY, Y in strict upper echelon form with pivots = 1.
   * We must find T such that Y T = Id_nB then X T = Z. This exists iff
   * Y has at least nB columns and full rank */
  nY = lg(x)-1;
  if (nY < nB) { avma = av; return NULL; }
  Y = rowslice(x, nA+1, nA+nB); /* nB rows */
  d = cgetg(nB+1, t_VECSMALL);
  for (i = nB, j = nY; i >= 1; i--, j--)
  {
    for (; j>=1; j--)
      if (!gequal0(gcoeff(Y,i,j))) { d[i] = j; break; }
    if (!j) { avma = av; return NULL; }
  }
  /* reduce to the case Y square, upper triangular with 1s on diagonal */
  Y = vecpermute(Y, d);
  x = vecpermute(x, d);
  X = rowslice(x, 1, nA);
  return gerepileupto(av, RgM_mul(X, RgM_inv_upper(Y)));
}

/* r = dim Ker x, n = nbrows(x) */
static GEN
get_suppl(GEN x, GEN d, long n, long r, GEN(*ei)(long,long))
{
  pari_sp av;
  GEN y, c;
  long j, k, rx = lg(x)-1; /* != 0 due to init_suppl() */

  if (rx == n && r == 0) return gcopy(x);
  y = cgetg(n+1, t_MAT);
  av = avma; c = zero_zv(n);
  /* c = lines containing pivots (could get it from gauss_pivot, but cheap)
   * In theory r = 0 and d[j] > 0 for all j, but why take chances? */
  for (k = j = 1; j<=rx; j++)
    if (d[j]) { c[ d[j] ] = 1; gel(y,k++) = gel(x,j); }
  for (j=1; j<=n; j++)
    if (!c[j]) gel(y,k++) = (GEN)j; /* HACK */
  avma = av;

  rx -= r;
  for (j=1; j<=rx; j++) gel(y,j) = gcopy(gel(y,j));
  for (   ; j<=n; j++)  gel(y,j) = ei(n, y[j]);
  return y;
}

static void
init_suppl(GEN x)
{
  if (lg(x) == 1) pari_err_IMPL("suppl [empty matrix]");
  /* HACK: avoid overwriting d from gauss_pivot() after avma=av */
  (void)new_chunk(lgcols(x) * 2);
}

GEN
FpM_suppl(GEN x, GEN p)
{
  GEN d;
  long r;
  init_suppl(x); d = FpM_gauss_pivot(x,p, &r);
  return get_suppl(x,d,nbrows(x),r,&col_ei);
}

GEN
Flm_suppl(GEN x, ulong p)
{
  GEN d;
  long r;
  init_suppl(x); d = Flm_pivots(x, p, &r, 0);
  return get_suppl(x,d,nbrows(x),r,&vecsmall_ei);
}

GEN
F2m_suppl(GEN x)
{
  GEN d;
  long r;
  init_suppl(x); d = F2m_gauss_pivot(F2m_copy(x), &r);
  return get_suppl(x,d,mael(x,1,1),r,&F2v_ei);
}

static GEN
RgM_suppl_FpM(GEN x, GEN p)
{
  pari_sp av = avma;
  ulong pp;
  x = RgM_Fp_init(x, p, &pp);
  switch(pp)
  {
  case 0: x = FpM_to_mod(FpM_suppl(x,p), p); break;
  case 2: x = F2m_to_mod(F2m_suppl(x)); break;
  default:x = Flm_to_mod(Flm_suppl(x,pp), pp); break;
  }
  return gerepileupto(av, x);
}

static GEN
RgM_suppl_fast(GEN x)
{
  GEN p, pol;
  long pa;
  long t = RgM_type(x,&p,&pol,&pa);
  switch(t)
  {
    case t_INTMOD: return RgM_suppl_FpM(x, p);
    case t_FFELT:  return FFM_suppl(x, pol);
    default:       return NULL;
  }
}

/* x is an n x k matrix, rank(x) = k <= n. Return an invertible n x n matrix
 * whose first k columns are given by x. If rank(x) < k, undefined result. */
GEN
suppl(GEN x)
{
  pari_sp av = avma;
  GEN d, M;
  long r;
  if (typ(x)!=t_MAT) pari_err_TYPE("suppl",x);
  M = RgM_suppl_fast(x);
  if (M) return M;
  init_suppl(x);
  d = gauss_pivot(x,&r);
  avma = av; return get_suppl(x,d,nbrows(x),r,&col_ei);
}
/* variable number to be filled in later */
static GEN
_FlxC_ei(long n, long i)
{
  GEN x = cgetg(n + 1, t_COL);
  long j;
  for (j = 1; j <= n; j++)
    gel(x, j) = (j == i)? pol1_Flx(0): pol0_Flx(0);
  return x;
}

GEN
F2xqM_suppl(GEN x, GEN T)
{
  pari_sp av = avma;
  GEN d, y;
  long n = nbrows(x), r, sv = get_Flx_var(T);

  init_suppl(x);
  d = F2xqM_gauss_pivot(x, T, &r);
  avma = av;
  y = get_suppl(x, d, n, r, &_FlxC_ei);
  if (sv) {
    long i, j;
    for (j = r + 1; j <= n; j++) {
      for (i = 1; i <= n; i++)
        gcoeff(y, i, j)[1] = sv;
    }
  }
  return y;
}

GEN
FlxqM_suppl(GEN x, GEN T, ulong p)
{
  pari_sp av = avma;
  GEN d, y;
  long n = nbrows(x), r, sv = get_Flx_var(T);

  init_suppl(x);
  d = FlxqM_gauss_pivot(x, T, p, &r);
  avma = av;
  y = get_suppl(x, d, n, r, &_FlxC_ei);
  if (sv) {
    long i, j;
    for (j = r + 1; j <= n; j++) {
      for (i = 1; i <= n; i++)
        gcoeff(y, i, j)[1] = sv;
    }
  }
  return y;
}

GEN
FqM_suppl(GEN x, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN d;
  long r;

  if (!T) return FpM_suppl(x,p);
  init_suppl(x);
  d = FqM_gauss_pivot(x,T,p,&r);
  avma = av; return get_suppl(x,d,nbrows(x),r,&col_ei);
}

GEN
image2(GEN x)
{
  pari_sp av = avma;
  long k, n, i;
  GEN A, B;

  if (typ(x)!=t_MAT) pari_err_TYPE("image2",x);
  if (lg(x) == 1) return cgetg(1,t_MAT);
  A = ker(x); k = lg(A)-1;
  if (!k) { avma = av; return gcopy(x); }
  A = suppl(A); n = lg(A)-1;
  B = cgetg(n-k+1, t_MAT);
  for (i = k+1; i <= n; i++) gel(B,i-k) = RgM_RgC_mul(x, gel(A,i));
  return gerepileupto(av, B);
}

GEN
matimage0(GEN x,long flag)
{
  switch(flag)
  {
    case 0: return image(x);
    case 1: return image2(x);
    default: pari_err_FLAG("matimage");
  }
  return NULL; /* LCOV_EXCL_LINE */
}

static long
RgM_rank_FpM(GEN x, GEN p)
{
  pari_sp av = avma;
  ulong pp;
  long r;
  x = RgM_Fp_init(x,p,&pp);
  switch(pp)
  {
  case 0: r = FpM_rank(x,p); break;
  case 2: r = F2m_rank(x); break;
  default:r = Flm_rank(x,pp); break;
  }
  avma = av; return r;
}

static long
RgM_rank_FqM(GEN x, GEN pol, GEN p)
{
  pari_sp av = avma;
  long r;
  GEN T = RgX_to_FpX(pol, p);
  if (signe(T) == 0) pari_err_OP("rank",x,pol);
  r = FqM_rank(RgM_to_FqM(x, T, p), T, p);
  avma = av;
  return r;
}

#define code(t1,t2) ((t1 << 6) | t2)
static long
RgM_rank_fast(GEN x)
{
  GEN p, pol;
  long pa;
  long t = RgM_type(x,&p,&pol,&pa);
  switch(t)
  {
    case t_INT:    return ZM_rank(x);
    case t_FRAC:   return QM_rank(x);
    case t_INTMOD: return RgM_rank_FpM(x, p);
    case t_FFELT:  return FFM_rank(x, pol);
    case code(t_POLMOD, t_INTMOD):
                   return RgM_rank_FqM(x, pol, p);
    default:       return -1;
  }
}
#undef code

long
rank(GEN x)
{
  pari_sp av = avma;
  long r;

  if (typ(x)!=t_MAT) pari_err_TYPE("rank",x);
  r = RgM_rank_fast(x);
  if (r >= 0) return r;
  (void)gauss_pivot(x, &r);
  avma = av; return lg(x)-1 - r;
}

/* d a t_VECSMALL of integers in 1..n. Return the vector of the d[i]
 * followed by the missing indices */
static GEN
perm_complete(GEN d, long n)
{
  GEN y = cgetg(n+1, t_VECSMALL);
  long i, j = 1, k = n, l = lg(d);
  pari_sp av = avma;
  char *T = stack_calloc(n+1);
  for (i = 1; i < l; i++) T[d[i]] = 1;
  for (i = 1; i <= n; i++)
    if (T[i]) y[j++] = i; else y[k--] = i;
  avma = av; return y;
}

/* n = dim x, r = dim Ker(x), d from gauss_pivot */
static GEN
indexrank0(long n, long r, GEN d)
{
  GEN p1, p2, res = cgetg(3,t_VEC);
  long i, j;

  r = n - r; /* now r = dim Im(x) */
  p1 = cgetg(r+1,t_VECSMALL); gel(res,1) = p1;
  p2 = cgetg(r+1,t_VECSMALL); gel(res,2) = p2;
  if (d)
  {
    for (i=0,j=1; j<=n; j++)
      if (d[j]) { i++; p1[i] = d[j]; p2[i] = j; }
    vecsmall_sort(p1);
  }
  return res;
}
/* n = dim x, r = dim Ker(x), d from gauss_pivot */
static GEN
indeximage0(long n, long r, GEN d)
{
  long i, j;
  GEN v;

  r = n - r; /* now r = dim Im(x) */
  v = cgetg(r+1,t_VECSMALL);
  if (d) for (i=j=1; j<=n; j++)
    if (d[j]) v[i++] = j;
  return v;
}
/* x an m x n t_MAT, n > 0, r = dim Ker(x), d from gauss_pivot */
static void
indexrank_all(long m, long n, long r, GEN d, GEN *prow, GEN *pcol)
{
  GEN IR = indexrank0(n, r, d);
  *prow = perm_complete(gel(IR,1), m);
  *pcol = perm_complete(gel(IR,2), n);
}
static void
init_indexrank(GEN x) {
  (void)new_chunk(3 + 2*lg(x)); /* HACK */
}

static GEN
RgM_indexrank_FpM(GEN x, GEN p)
{
  pari_sp av = avma;
  ulong pp;
  GEN r;
  x = RgM_Fp_init(x,p,&pp);
  switch(pp)
  {
  case 0:  r = FpM_indexrank(x,p); break;
  case 2:  r = F2m_indexrank(x); break;
  default: r = Flm_indexrank(x,pp); break;
  }
  return gerepileupto(av, r);
}

static GEN
RgM_indexrank_FqM(GEN x, GEN pol, GEN p)
{
  pari_sp av = avma;
  GEN r, T = RgX_to_FpX(pol, p);
  if (signe(T) == 0) pari_err_OP("indexrank",x,pol);
  r = FqM_indexrank(RgM_to_FqM(x, T, p), T, p);
  return gerepileupto(av, r);
}

#define code(t1,t2) ((t1 << 6) | t2)
static GEN
RgM_indexrank_fast(GEN x)
{
  GEN p, pol;
  long pa;
  long t = RgM_type(x,&p,&pol,&pa);
  switch(t)
  {
    case t_INT:    return ZM_indexrank(x);
    case t_FRAC:   return QM_indexrank(x);
    case t_INTMOD: return RgM_indexrank_FpM(x, p);
    case t_FFELT:  return FFM_indexrank(x, pol);
    case code(t_POLMOD, t_INTMOD):
                   return RgM_indexrank_FqM(x, pol, p);
    default:       return NULL;
  }
}
#undef code

GEN
indexrank(GEN x)
{
  pari_sp av;
  long r;
  GEN d;
  if (typ(x)!=t_MAT) pari_err_TYPE("indexrank",x);
  d = RgM_indexrank_fast(x);
  if (d) return d;
  av = avma;
  init_indexrank(x);
  d = gauss_pivot(x, &r);
  avma = av; return indexrank0(lg(x)-1, r, d);
}

GEN
FpM_indexrank(GEN x, GEN p) {
  pari_sp av = avma;
  long r;
  GEN d;
  init_indexrank(x);
  d = FpM_gauss_pivot(x,p,&r);
  avma = av; return indexrank0(lg(x)-1, r, d);
}

GEN
Flm_indexrank(GEN x, ulong p) {
  pari_sp av = avma;
  long r;
  GEN d;
  init_indexrank(x);
  d = Flm_pivots(x, p, &r, 0);
  avma = av; return indexrank0(lg(x)-1, r, d);
}

GEN
F2m_indexrank(GEN x) {
  pari_sp av = avma;
  long r;
  GEN d;
  init_indexrank(x);
  d = F2m_gauss_pivot(F2m_copy(x),&r);
  avma = av; return indexrank0(lg(x)-1, r, d);
}

GEN
F2xqM_indexrank(GEN x, GEN T) {
  pari_sp av = avma;
  long r;
  GEN d;
  init_indexrank(x);
  d = F2xqM_gauss_pivot(x, T, &r);
  avma = av; return indexrank0(lg(x) - 1, r, d);
}

GEN
FlxqM_indexrank(GEN x, GEN T, ulong p) {
  pari_sp av = avma;
  long r;
  GEN d;
  init_indexrank(x);
  d = FlxqM_gauss_pivot(x, T, p, &r);
  avma = av; return indexrank0(lg(x) - 1, r, d);
}

GEN
FqM_indexrank(GEN x, GEN T, GEN p) {
  pari_sp av = avma;
  long r;
  GEN d;
  init_indexrank(x);
  d = FqM_gauss_pivot(x, T, p, &r);
  avma = av; return indexrank0(lg(x) - 1, r, d);
}

GEN
ZM_indeximage(GEN x) {
  pari_sp av = avma;
  long r;
  GEN d;
  init_indexrank(x);
  d = ZM_pivots(x,&r);
  avma = av; return indeximage0(lg(x)-1, r, d);
}
long
ZM_rank(GEN x) {
  pari_sp av = avma;
  long r;
  (void)ZM_pivots(x,&r);
  avma = av; return lg(x)-1-r;
}
GEN
ZM_indexrank(GEN x) {
  pari_sp av = avma;
  long r;
  GEN d;
  init_indexrank(x);
  d = ZM_pivots(x,&r);
  avma = av; return indexrank0(lg(x)-1, r, d);
}

long
QM_rank(GEN x)
{
  pari_sp av = avma;
  long r = ZM_rank(Q_primpart(x));
  avma = av;
  return r;
}

GEN
QM_indexrank(GEN x)
{
  pari_sp av = avma;
  GEN r = ZM_indexrank(Q_primpart(x));
  return gerepileupto(av, r);
}

/*******************************************************************/
/*                                                                 */
/*                             ZabM                                */
/*                                                                 */
/*******************************************************************/

static GEN
FpXM_ratlift(GEN a, GEN q)
{
  GEN B, y;
  long i, j, l = lg(a), n;
  B = sqrti(shifti(q,-1));
  y = cgetg(l, t_MAT);
  if (l==1) return y;
  n = lgcols(a);
  for (i=1; i<l; i++)
  {
    GEN yi = cgetg(n, t_COL);
    for (j=1; j<n; j++)
    {
      GEN v = FpX_ratlift(gmael(a,i,j), q, B, B, NULL);
      if (!v) return NULL;
      gel(yi, j) = RgX_renormalize(v);
    }
    gel(y,i) = yi;
  }
  return y;
}

static GEN
FlmV_recover_pre(GEN a, GEN M, ulong p, ulong pi, long sv)
{
  GEN a1 = gel(a,1);
  long i, j, k, l = lg(a1), n, lM = lg(M);
  GEN v = cgetg(lM, t_VECSMALL);
  GEN y = cgetg(l, t_MAT);
  if (l==1) return y;
  n = lgcols(a1);
  for (i=1; i<l; i++)
  {
    GEN yi = cgetg(n, t_COL);
    for (j=1; j<n; j++)
    {
      for (k=1; k<lM; k++) uel(v,k) = umael(gel(a,k),i,j);
      gel(yi, j) = Flm_Flc_mul_pre_Flx(M, v, p, pi, sv);
    }
    gel(y,i) = yi;
  }
  return y;
}

static GEN
FlkM_inv(GEN M, GEN P, ulong p)
{
  ulong pi = get_Fl_red(p);
  GEN R = Flx_roots(P, p);
  long l = lg(R), i;
  GEN W = Flv_invVandermonde(R, 1UL, p);
  GEN V = cgetg(l, t_VEC);
  for(i=1; i<l; i++)
  {
    GEN pows = Fl_powers_pre(uel(R,i), degpol(P), p, pi);
    GEN H = Flm_inv_sp(FlxM_eval_powers_pre(M, pows, p, pi), NULL, p);
    if (!H) return NULL;
    gel(V, i) = H;
  }
  return FlmV_recover_pre(V, W, p, pi, P[1]);
}

static GEN
FlkM_adjoint(GEN M, GEN P, ulong p)
{
  ulong pi = get_Fl_red(p);
  GEN R = Flx_roots(P, p);
  long l = lg(R), i;
  GEN W = Flv_invVandermonde(R, 1UL, p);
  GEN V = cgetg(l, t_VEC);
  for(i=1; i<l; i++)
  {
    GEN pows = Fl_powers_pre(uel(R,i), degpol(P), p, pi);
    gel(V, i) = Flm_adjoint(FlxM_eval_powers_pre(M, pows, p, pi), p);
  }
  return FlmV_recover_pre(V, W, p, pi, P[1]);
}


static GEN
ZabM_inv_slice(GEN A, GEN Q, GEN P, GEN *mod)
{
  pari_sp av = avma;
  long i, n = lg(P)-1, w = varn(Q);
  GEN H, T;
  if (n == 1)
  {
    ulong p = uel(P,1);
    GEN Ap = FqM_to_FlxM(A, Q, utoi(p));
    GEN Qp = ZX_to_Flx(Q, p);
    GEN Hp = FlkM_adjoint(Ap, Qp, p);
    Hp = gerepileupto(av, FlxM_to_ZXM(Hp));
    *mod = utoi(p); return Hp;
  }
  T = ZV_producttree(P);
  A = ZXM_nv_mod_tree(A, P, T, w);
  Q = ZX_nv_mod_tree(Q, P, T);
  H = cgetg(n+1, t_VEC);
  for(i=1; i <= n; i++)
  {
    ulong p = P[i];
    GEN a = gel(A,i), q = gel(Q, i);
    gel(H,i) = FlkM_adjoint(a, q, p);
  }
  H = nxMV_chinese_center_tree_seq(H, P, T, ZV_chinesetree(P,T));
  *mod = gmael(T, lg(T)-1, 1);
  gerepileall(av, 2, &H, mod);
  return H;
}

GEN
ZabM_inv_worker(GEN P, GEN A, GEN Q)
{
  GEN V = cgetg(3, t_VEC);
  gel(V,1) = ZabM_inv_slice(A, Q, P, &gel(V,2));
  return V;
}

static GEN
vecnorml1(GEN a)
{
  long i, l;
  GEN g = cgetg_copy(a, &l);
  for (i=1; i<l; i++)
    gel(g, i) = gnorml1_fake(gel(a,i));
  return g;
}

static GEN
ZabM_true_Hadamard(GEN a)
{
  pari_sp av = avma;
  long n = lg(a)-1, i;
  GEN B;
  if (n == 0) return gen_1;
  if (n == 1) return gnorml1_fake(gcoeff(a,1,1));
  B = gen_1;
  for (i = 1; i <= n; i++) B = gmul(B, gnorml2(RgC_gtofp(vecnorml1(gel(a,i)),DEFAULTPREC)));
  return gerepileuptoint(av, ceil_safe(sqrtr_abs(B)));
}

GEN
ZabM_inv(GEN A, GEN Q, long n, GEN *pt_den)
{
  pari_sp av = avma;
  long m = lg(A)-1;
  GEN bnd, H, D, d, mod, worker;
  if (m == 0)
  {
    if (pt_den) *pt_den = gen_1;
    return cgetg(1, t_MAT);
  }
  bnd = ZabM_true_Hadamard(A);
  worker = strtoclosure("_ZabM_inv_worker", 2, A, Q);
  H = gen_crt("ZabM_inv", worker, mkvecsmall(n), expi(bnd), m, &mod,
              nxMV_chinese_center, FpXM_center);
  D = RgMrow_RgC_mul(H, gel(A,1), 1);
  D = ZX_rem(D, Q);
  d = Z_content(mkvec2(H, D));
  if (d)
  {
    D = ZX_Z_divexact(D, d);
    H = Q_div_to_int(H, d);
  }
  if (pt_den)
  {
    gerepileall(av, 2, &H, &D);
    *pt_den = D; return H;
  }
  return gerepileupto(av, H);
}

GEN
ZabM_inv_ratlift(GEN M, GEN P, long n, GEN *pden)
{
  pari_sp av2, av = avma;
  GEN q, H;
  ulong m = LONG_MAX>>1;
  ulong p= 1 + m - (m % n);
  long lM = lg(M);
  if (lM == 1) { *pden = gen_1; return cgetg(1,t_MAT); }

  av2 = avma;
  H = NULL;
  for(;;)
  {
    GEN Hp, Pp, Mp, Hr;
    do p += n; while(!uisprime(p));
    Pp = ZX_to_Flx(P, p);
    Mp = FqM_to_FlxM(M, P, utoi(p));
    Hp = FlkM_inv(Mp, Pp, p);
    if (!Hp) continue;
    if (!H)
    {
      H = ZXM_init_CRT(Hp, degpol(P)-1, p);
      q = utoipos(p);
    }
    else
      ZXM_incremental_CRT(&H, Hp, &q, p);
    Hr = FpXM_ratlift(H, q);
    if (DEBUGLEVEL>5) err_printf("ZabM_inv mod %ld (ratlift=%ld)\n", p,!!Hr);
    if (Hr) {/* DONE ? */
      GEN Hl = Q_remove_denom(Hr, pden);
      GEN MH = ZXQM_mul(Hl, M, P);
      if (*pden)
      { if (RgM_isscalar(MH, *pden)) { H = Hl; break; }}
      else
      { if (RgM_isidentity(MH)) { H = Hl; *pden = gen_1; break; } }
    }

    if (gc_needed(av,2))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"ZabM_inv");
      gerepileall(av2, 2, &H, &q);
    }
  }
  gerepileall(av, 2, &H, pden);
  return H;
}

static GEN
FlkM_ker(GEN M, GEN P, ulong p)
{
  ulong pi = get_Fl_red(p);
  GEN R = Flx_roots(P, p);
  long l = lg(R), i, dP = degpol(P), r;
  GEN M1, K, D;
  GEN W = Flv_invVandermonde(R, 1UL, p);
  GEN V = cgetg(l, t_VEC);
  M1 = FlxM_eval_powers_pre(M, Fl_powers_pre(uel(R,1), dP, p, pi), p, pi);
  K = Flm_ker_sp(M1, p, 2);
  r = lg(gel(K,1)); D = gel(K,2);
  gel(V, 1) = gel(K,1);
  for(i=2; i<l; i++)
  {
    GEN Mi = FlxM_eval_powers_pre(M, Fl_powers_pre(uel(R,i), dP, p, pi), p, pi);
    GEN K = Flm_ker_sp(Mi, p, 2);
    if (lg(gel(K,1)) != r || !zv_equal(D, gel(K,2))) return NULL;
    gel(V, i) = gel(K,1);
  }
  return mkvec2(FlmV_recover_pre(V, W, p, pi, P[1]), D);
}

GEN
ZabM_ker(GEN M, GEN P, long n)
{
  pari_sp av2, av = avma;
  GEN q, H, D;
  ulong m = LONG_MAX>>1;
  ulong p= 1 + m - (m % n);
  av2 = avma;
  H = NULL; D = NULL;
  for(;;)
  {
    GEN Kp, Hp, Dp, Pp, Mp, Hr;
    do p += n; while(!uisprime(p));
    Pp = ZX_to_Flx(P, p);
    Mp = FqM_to_FlxM(M, P, utoi(p));
    Kp = FlkM_ker(Mp, Pp, p);
    if (!Kp) continue;
    Hp = gel(Kp,1); Dp = gel(Kp,2);
    if (H && (lg(Hp)>lg(H) || (lg(Hp)==lg(H) && vecsmall_lexcmp(Dp,D)>0))) continue;
    if (!H || (lg(Hp)<lg(H) || vecsmall_lexcmp(Dp,D)<0))
    {
      H = ZXM_init_CRT(Hp, degpol(P)-1, p); D = Dp;
      q = utoipos(p);
    }
    else
      ZXM_incremental_CRT(&H, Hp, &q, p);
    Hr = FpXM_ratlift(H, q);
    if (DEBUGLEVEL>5) err_printf("ZabM_ker mod %ld (ratlift=%ld)\n", p,!!Hr);
    if (Hr) {/* DONE ? */
      GEN Hl = vec_Q_primpart(Hr);
      GEN MH = ZXQM_mul(M, Hl,P);
      if (gequal0(MH)) { H = Hl;  break; }
    }

    if (gc_needed(av,2))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"ZabM_ker");
      gerepileall(av2, 3, &H, &D, &q);
    }
  }
  return gerepilecopy(av, H);
}

GEN
ZabM_indexrank(GEN M, GEN P, long n)
{
  pari_sp av = avma;
  ulong m = LONG_MAX>>1;
  ulong p = 1+m-(m%n), D = degpol(P);
  long lM = lg(M), lmax = 0, c = 0;
  GEN v;
  for(;;)
  {
    GEN R, Mp, K;
    ulong pi;
    long l;
    do p += n; while (!uisprime(p));
    pi = get_Fl_red(p);
    R = Flx_roots(ZX_to_Flx(P, p), p);
    Mp = FqM_to_FlxM(M, P, utoipos(p));
    K = FlxM_eval_powers_pre(Mp, Fl_powers_pre(uel(R,1), D,p,pi), p,pi);
    v = Flm_indexrank(K, p);
    l = lg(gel(v,2));
    if (l == lM) break;
    if (lmax >= 0 && l > lmax) { lmax = l; c = 0; } else c++;
    if (c > 2)
    { /* probably not maximal rank, expensive check */
      lM -= lg(ZabM_ker(M, P, n))-1; /* actual rank (+1) */
      if (lmax == lM) break;
      lmax = -1; /* disable check */
    }
  }
  return gerepileupto(av, v);
}

#if 0
GEN
ZabM_gauss(GEN M, GEN P, long n, GEN *den)
{
  pari_sp av = avma;
  GEN v, S, W;
  v = ZabM_indexrank(M, P, n);
  S = shallowmatextract(M,gel(v,1),gel(v,2));
  W = ZabM_inv(S, P, n, den);
  gerepileall(av,2,&W,den);
  return W;
}
#endif

GEN
ZabM_pseudoinv(GEN M, GEN P, long n, GEN *pv, GEN *den)
{
  GEN v = ZabM_indexrank(M, P, n);
  if (pv) *pv = v;
  M = shallowmatextract(M,gel(v,1),gel(v,2));
  return ZabM_inv(M, P, n, den);
}
GEN
ZM_pseudoinv(GEN M, GEN *pv, GEN *den)
{
  GEN v = ZM_indexrank(M);
  if (pv) *pv = v;
  M = shallowmatextract(M,gel(v,1),gel(v,2));
  return ZM_inv(M, den);
}

/*******************************************************************/
/*                                                                 */
/*                   Structured Elimination                        */
/*                                                                 */
/*******************************************************************/

static void
rem_col(GEN c, long i, GEN iscol, GEN Wrow, long *rcol, long *rrow)
{
  long lc = lg(c), k;
  iscol[i] = 0; (*rcol)--;
  for (k = 1; k < lc; ++k)
  {
    Wrow[c[k]]--;
    if (Wrow[c[k]]==0) (*rrow)--;
  }
}

static void
rem_singleton(GEN M, GEN iscol, GEN Wrow, long *rcol, long *rrow)
{
  long i, j;
  long nbcol = lg(iscol)-1, last;
  do
  {
    last = 0;
    for (i = 1; i <= nbcol; ++i)
      if (iscol[i])
      {
        GEN c = gmael(M, i, 1);
        long lc = lg(c);
        for (j = 1; j < lc; ++j)
          if (Wrow[c[j]] == 1)
          {
            rem_col(c, i, iscol, Wrow, rcol, rrow);
            last=1; break;
          }
      }
  } while (last);
}

static GEN
fill_wcol(GEN M, GEN iscol, GEN Wrow, long *w, GEN wcol)
{
  long nbcol = lg(iscol)-1;
  long i, j, m, last;
  GEN per;
  for (m = 2, last=0; !last ; m++)
  {
    for (i = 1; i <= nbcol; ++i)
    {
      wcol[i] = 0;
      if (iscol[i])
      {
        GEN c = gmael(M, i, 1);
        long lc = lg(c);
        for (j = 1; j < lc; ++j)
          if (Wrow[c[j]] == m) {  wcol[i]++; last = 1; }
      }
    }
  }
  per = vecsmall_indexsort(wcol);
  *w = wcol[per[nbcol]];
  return per;
}

/* M is a RgMs with nbrow rows, A a list of row indices.
   Eliminate rows of M with a single entry that do not belong to A,
   and the corresponding columns. Also eliminate columns until #colums=#rows.
   Return pcol and prow:
   pcol is a map from the new columns indices to the old one.
   prow is a map from the old rows indices to the new one (0 if removed).
*/

void
RgMs_structelim_col(GEN M, long nbcol, long nbrow, GEN A, GEN *p_col, GEN *p_row)
{
  long i,j,k;
  long lA = lg(A);
  GEN prow = cgetg(nbrow+1, t_VECSMALL);
  GEN pcol = zero_zv(nbcol);
  pari_sp av = avma;
  long rcol = nbcol, rrow = 0, imin = nbcol - usqrt(nbcol);
  GEN iscol = const_vecsmall(nbcol, 1);
  GEN Wrow  = zero_zv(nbrow);
  GEN wcol = cgetg(nbcol+1, t_VECSMALL);
  pari_sp av2=avma;
  for (i = 1; i <= nbcol; ++i)
  {
    GEN F = gmael(M, i, 1);
    long l = lg(F)-1;
    for (j = 1; j <= l; ++j)
      Wrow[F[j]]++;
  }
  for (j = 1; j < lA; ++j)
  {
    if (Wrow[A[j]] == 0) { *p_col=NULL; return; }
    Wrow[A[j]] = -1;
  }
  for (i = 1; i <= nbrow; ++i)
    if (Wrow[i])
      rrow++;
  rem_singleton(M, iscol, Wrow, &rcol, &rrow);
  if (rcol<rrow) pari_err_BUG("RgMs_structelim, rcol<rrow");
  for (; rcol>rrow;)
  {
    long w;
    GEN per = fill_wcol(M, iscol, Wrow, &w, wcol);
    for (i = nbcol; i>=imin && wcol[per[i]]>=w && rcol>rrow; i--)
      rem_col(gmael(M, per[i], 1), per[i], iscol, Wrow, &rcol, &rrow);
    rem_singleton(M, iscol, Wrow, &rcol, &rrow);
    avma = av2;
  }
  for (j = 1, i = 1; i <= nbcol; ++i)
    if (iscol[i])
      pcol[j++] = i;
  setlg(pcol,j);
  for (k = 1, i = 1; i <= nbrow; ++i)
    prow[i] = Wrow[i] ? k++: 0;
  avma = av;
  *p_col = pcol; *p_row = prow;
}

void
RgMs_structelim(GEN M, long nbrow, GEN A, GEN *p_col, GEN *p_row)
{
  RgMs_structelim_col(M, lg(M)-1, nbrow, A, p_col, p_row);
}

/*******************************************************************/
/*                                                                 */
/*                        EIGENVECTORS                             */
/*   (independent eigenvectors, sorted by increasing eigenvalue)   */
/*                                                                 */
/*******************************************************************/
/* assume x is square of dimension > 0 */
static int
RgM_is_symmetric_cx(GEN x, long bit)
{
  pari_sp av = avma;
  long i, j, l = lg(x);
  for (i = 1; i < l; i++)
    for (j = 1; j < i; j++)
    {
      GEN a = gcoeff(x,i,j), b = gcoeff(x,j,i), c = gsub(a,b);
      if (!gequal0(c) && gexpo(c) - gexpo(a) > -bit) { avma = av; return 0; }
    }
  avma = av; return 1;
}
static GEN
eigen_err(int exact, GEN x, long flag, long prec)
{
  pari_sp av = avma;
  if (RgM_is_symmetric_cx(x, prec2nbits(prec) - 10))
  { /* approximately symmetric: recover */
    x = jacobi(x, prec); if (flag) return x;
    return gerepilecopy(av, gel(x,1));
  }
  if (exact)
  {
    GEN y = mateigen(x, flag, precdbl(prec));
    return gerepilecopy(av, gprec_wtrunc(y, prec));
  }
  pari_err_PREC("mateigen");
  return NULL; /* LCOV_EXCL_LINE */
}
GEN
mateigen(GEN x, long flag, long prec)
{
  GEN y, R, T;
  long k, l, ex, n = lg(x);
  int exact;
  pari_sp av = avma;

  if (typ(x)!=t_MAT) pari_err_TYPE("eigen",x);
  if (n != 1 && n != lgcols(x)) pari_err_DIM("eigen");
  if (flag < 0 || flag > 1) pari_err_FLAG("mateigen");
  if (n == 1)
  {
    if (flag) retmkvec2(cgetg(1,t_VEC), cgetg(1,t_MAT));
    return cgetg(1,t_VEC);
  }
  if (n == 2)
  {
    if (flag) retmkvec2(mkveccopy(gcoeff(x,1,1)), matid(1));
    return matid(1);
  }

  ex = 16 - prec2nbits(prec);
  T = charpoly(x,0);
  exact = RgX_is_QX(T);
  if (exact)
  {
    T = ZX_radical( Q_primpart(T) );
    R = nfrootsQ(T);
    if (lg(R)-1 < degpol(T))
    { /* add missing complex roots */
      GEN r = cleanroots(RgX_div(T, roots_to_pol(R, 0)), prec);
      settyp(r, t_VEC);
      R = shallowconcat(R, r);
    }
  }
  else
  {
    GEN r1, v = vectrunc_init(lg(T));
    long e;
    R = cleanroots(T,prec);
    r1 = NULL;
    for (k = 1; k < lg(R); k++)
    {
      GEN r2 = gel(R,k), r = grndtoi(r2, &e);
      if (e < ex) r2 = r;
      if (r1)
      {
        r = gsub(r1,r2);
        if (gequal0(r) || gexpo(r) < ex) continue;
      }
      vectrunc_append(v, r2);
      r1 = r2;
    }
    R = v;
  }
  /* R = distinct complex roots of charpoly(x) */
  l = lg(R); y = cgetg(l, t_VEC);
  for (k = 1; k < l; k++)
  {
    GEN F = ker_aux(RgM_Rg_sub_shallow(x, gel(R,k)), x);
    long d = lg(F)-1;
    if (!d) { avma = av; return eigen_err(exact, x, flag, prec); }
    gel(y,k) = F;
    if (flag) gel(R,k) = const_vec(d, gel(R,k));
  }
  y = shallowconcat1(y);
  if (lg(y) > n) { avma = av; return eigen_err(exact, x, flag, prec); }
  /* lg(y) < n if x is not diagonalizable */
  if (flag) y = mkvec2(shallowconcat1(R), y);
  return gerepilecopy(av,y);
}
GEN
eigen(GEN x, long prec) { return mateigen(x, 0, prec); }

/*******************************************************************/
/*                                                                 */
/*                           DETERMINANT                           */
/*                                                                 */
/*******************************************************************/

GEN
det0(GEN a,long flag)
{
  switch(flag)
  {
    case 0: return det(a);
    case 1: return det2(a);
    default: pari_err_FLAG("matdet");
  }
  return NULL; /* LCOV_EXCL_LINE */
}

/* M a 2x2 matrix, returns det(M) */
static GEN
RgM_det2(GEN M)
{
  pari_sp av = avma;
  GEN a = gcoeff(M,1,1), b = gcoeff(M,1,2);
  GEN c = gcoeff(M,2,1), d = gcoeff(M,2,2);
  return gerepileupto(av, gsub(gmul(a,d), gmul(b,c)));
}
/* M a 2x2 ZM, returns det(M) */
static GEN
ZM_det2(GEN M)
{
  pari_sp av = avma;
  GEN a = gcoeff(M,1,1), b = gcoeff(M,1,2);
  GEN c = gcoeff(M,2,1), d = gcoeff(M,2,2);
  return gerepileuptoint(av, subii(mulii(a,d), mulii(b, c)));
}
/* M a 3x3 ZM, return det(M) */
static GEN
ZM_det3(GEN M)
{
  pari_sp av = avma;
  GEN a = gcoeff(M,1,1), b = gcoeff(M,1,2), c = gcoeff(M,1,3);
  GEN d = gcoeff(M,2,1), e = gcoeff(M,2,2), f = gcoeff(M,2,3);
  GEN g = gcoeff(M,3,1), h = gcoeff(M,3,2), i = gcoeff(M,3,3);
  GEN t, D = signe(i)? mulii(subii(mulii(a,e), mulii(b,d)), i): gen_0;
  if (signe(g))
  {
    t = mulii(subii(mulii(b,f), mulii(c,e)), g);
    D = addii(D, t);
  }
  if (signe(h))
  {
    t = mulii(subii(mulii(c,d), mulii(a,f)), h);
    D = addii(D, t);
  }
  return gerepileuptoint(av, D);
}

static GEN
det_simple_gauss(GEN a, GEN data, pivot_fun pivot)
{
  pari_sp av = avma;
  long i,j,k, s = 1, nbco = lg(a)-1;
  GEN p, x = gen_1;

  a = RgM_shallowcopy(a);
  for (i=1; i<nbco; i++)
  {
    k = pivot(a, data, i, NULL);
    if (k > nbco) return gerepilecopy(av, gcoeff(a,i,i));
    if (k != i)
    { /* exchange the lines s.t. k = i */
      for (j=i; j<=nbco; j++) swap(gcoeff(a,i,j), gcoeff(a,k,j));
      s = -s;
    }
    p = gcoeff(a,i,i);

    x = gmul(x,p);
    for (k=i+1; k<=nbco; k++)
    {
      GEN m = gcoeff(a,i,k);
      if (gequal0(m)) continue;

      m = gdiv(m,p);
      for (j=i+1; j<=nbco; j++)
        gcoeff(a,j,k) = gsub(gcoeff(a,j,k), gmul(m,gcoeff(a,j,i)));
    }
    if (gc_needed(av,2))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"det. col = %ld",i);
      gerepileall(av,2, &a,&x);
    }
  }
  if (s < 0) x = gneg_i(x);
  return gerepileupto(av, gmul(x, gcoeff(a,nbco,nbco)));
}

GEN
det2(GEN a)
{
  GEN data;
  pivot_fun pivot;
  long n = lg(a)-1;
  if (typ(a)!=t_MAT) pari_err_TYPE("det2",a);
  if (!n) return gen_1;
  if (n != nbrows(a)) pari_err_DIM("det2");
  if (n == 1) return gcopy(gcoeff(a,1,1));
  if (n == 2) return RgM_det2(a);
  pivot = get_pivot_fun(a, a, &data);
  return det_simple_gauss(a, data, pivot);
}

/* Assumes a a square t_MAT of dimension n > 0. Returns det(a) using
 * Gauss-Bareiss. */
static GEN
det_bareiss(GEN a)
{
  pari_sp av = avma;
  long nbco = lg(a)-1,i,j,k,s = 1;
  GEN p, pprec;

  a = RgM_shallowcopy(a);
  for (pprec=gen_1,i=1; i<nbco; i++,pprec=p)
  {
    int diveuc = (gequal1(pprec)==0);
    GEN ci;

    p = gcoeff(a,i,i);
    if (gequal0(p))
    {
      k=i+1; while (k<=nbco && gequal0(gcoeff(a,i,k))) k++;
      if (k>nbco) return gerepilecopy(av, p);
      swap(gel(a,k), gel(a,i)); s = -s;
      p = gcoeff(a,i,i);
    }
    ci = gel(a,i);
    for (k=i+1; k<=nbco; k++)
    {
      GEN ck = gel(a,k), m = gel(ck,i);
      if (gequal0(m))
      {
        if (gequal1(p))
        {
          if (diveuc)
            gel(a,k) = gdiv(gel(a,k), pprec);
        }
        else
          for (j=i+1; j<=nbco; j++)
          {
            GEN p1 = gmul(p, gel(ck,j));
            if (diveuc) p1 = gdiv(p1,pprec);
            gel(ck,j) = p1;
          }
      }
      else
        for (j=i+1; j<=nbco; j++)
        {
          pari_sp av2 = avma;
          GEN p1 = gsub(gmul(p,gel(ck,j)), gmul(m,gel(ci,j)));
          if (diveuc) p1 = gdiv(p1,pprec);
          gel(ck,j) = gerepileupto(av2, p1);
        }
      if (gc_needed(av,2))
      {
        if(DEBUGMEM>1) pari_warn(warnmem,"det. col = %ld",i);
        gerepileall(av,2, &a,&pprec);
        ci = gel(a,i);
        p = gcoeff(a,i,i);
      }
    }
  }
  p = gcoeff(a,nbco,nbco);
  p = (s < 0)? gneg(p): gcopy(p);
  return gerepileupto(av, p);
}

/* count non-zero entries in col j, at most 'max' of them.
 * Return their indices */
static GEN
col_count_non_zero(GEN a, long j, long max)
{
  GEN v = cgetg(max+1, t_VECSMALL);
  GEN c = gel(a,j);
  long i, l = lg(a), k = 1;
  for (i = 1; i < l; i++)
    if (!gequal0(gel(c,i)))
    {
      if (k > max) return NULL; /* fail */
      v[k++] = i;
    }
  setlg(v, k); return v;
}
/* count non-zero entries in row i, at most 'max' of them.
 * Return their indices */
static GEN
row_count_non_zero(GEN a, long i, long max)
{
  GEN v = cgetg(max+1, t_VECSMALL);
  long j, l = lg(a), k = 1;
  for (j = 1; j < l; j++)
    if (!gequal0(gcoeff(a,i,j)))
    {
      if (k > max) return NULL; /* fail */
      v[k++] = j;
    }
  setlg(v, k); return v;
}

static GEN det_develop(GEN a, long max, double bound);
/* (-1)^(i+j) a[i,j] * det RgM_minor(a,i,j) */
static GEN
coeff_det(GEN a, long i, long j, long max, double bound)
{
  GEN c = gcoeff(a, i, j);
  c = gmul(c, det_develop(RgM_minor(a, i,j), max, bound));
  if (odd(i+j)) c = gneg(c);
  return c;
}
/* a square t_MAT, 'bound' a rough upper bound for the number of
 * multiplications we are willing to pay while developing rows/columns before
 * switching to Gaussian elimination */
static GEN
det_develop(GEN M, long max, double bound)
{
  pari_sp av = avma;
  long i,j, n = lg(M)-1, lbest = max+2, best_col = 0, best_row = 0;
  GEN best = NULL;

  if (bound < 1.) return det_bareiss(M); /* too costly now */

  switch(n)
  {
    case 0: return gen_1;
    case 1: return gcopy(gcoeff(M,1,1));
    case 2: return RgM_det2(M);
  }
  if (max > ((n+2)>>1)) max = (n+2)>>1;
  for (j = 1; j <= n; j++)
  {
    pari_sp av2 = avma;
    GEN v = col_count_non_zero(M, j, max);
    long lv;
    if (!v || (lv = lg(v)) >= lbest) { avma = av2; continue; }
    if (lv == 1) { avma = av; return gen_0; }
    if (lv == 2) {
      avma = av;
      return gerepileupto(av, coeff_det(M,v[1],j,max,bound));
    }
    best = v; lbest = lv; best_col = j;
  }
  for (i = 1; i <= n; i++)
  {
    pari_sp av2 = avma;
    GEN v = row_count_non_zero(M, i, max);
    long lv;
    if (!v || (lv = lg(v)) >= lbest) { avma = av2; continue; }
    if (lv == 1) { avma = av; return gen_0; }
    if (lv == 2) {
      avma = av;
      return gerepileupto(av, coeff_det(M,i,v[1],max,bound));
    }
    best = v; lbest = lv; best_row = i;
  }
  if (best_row)
  {
    double d = lbest-1;
    GEN s = NULL;
    long k;
    bound /= d*d*d;
    for (k = 1; k < lbest; k++)
    {
      GEN c = coeff_det(M, best_row, best[k], max, bound);
      s = s? gadd(s, c): c;
    }
    return gerepileupto(av, s);
  }
  if (best_col)
  {
    double d = lbest-1;
    GEN s = NULL;
    long k;
    bound /= d*d*d;
    for (k = 1; k < lbest; k++)
    {
      GEN c = coeff_det(M, best[k], best_col, max, bound);
      s = s? gadd(s, c): c;
    }
    return gerepileupto(av, s);
  }
  return det_bareiss(M);
}

/* area of parallelogram bounded by (v1,v2) */
static GEN
parallelogramarea(GEN v1, GEN v2)
{ return gsub(gmul(gnorml2(v1), gnorml2(v2)), gsqr(RgV_dotproduct(v1, v2))); }

/* Square of Hadamard bound for det(a), a square matrix.
 * Slightly improvement: instead of using the column norms, use the area of
 * the parallelogram formed by pairs of consecutive vectors */
GEN
RgM_Hadamard(GEN a)
{
  pari_sp av = avma;
  long n = lg(a)-1, i;
  GEN B;
  if (n == 0) return gen_1;
  if (n == 1) return gsqr(gcoeff(a,1,1));
  a = RgM_gtofp(a, LOWDEFAULTPREC);
  B = gen_1;
  for (i = 1; i <= n/2; i++)
    B = gmul(B, parallelogramarea(gel(a,2*i-1), gel(a,2*i)));
  if (odd(n)) B = gmul(B, gnorml2(gel(a, n)));
  return gerepileuptoint(av, ceil_safe(B));
}

/* If B=NULL, assume B=A' */
static GEN
ZM_det_slice(GEN A, GEN P, GEN *mod)
{
  pari_sp av = avma;
  long i, n = lg(P)-1;
  GEN H, T;
  if (n == 1)
  {
    ulong Hp, p = uel(P,1);
    GEN a = ZM_to_Flm(A, p);
    Hp = Flm_det_sp(a, p);
    avma = av;
    *mod = utoi(p); return utoi(Hp);
  }
  T = ZV_producttree(P);
  A = ZM_nv_mod_tree(A, P, T);
  H = cgetg(n+1, t_VECSMALL);
  for(i=1; i <= n; i++)
  {
    ulong p = P[i];
    GEN a = gel(A,i);
    H[i] = Flm_det_sp(a, p);
  }
  H = ZV_chinese_tree(H, P, T, ZV_chinesetree(P,T));
  *mod = gmael(T, lg(T)-1, 1);
  gerepileall(av, 2, &H, mod);
  return H;
}

GEN
ZM_det_worker(GEN P, GEN A)
{
  GEN V = cgetg(3, t_VEC);
  gel(V,1) = ZM_det_slice(A, P, &gel(V,2));
  return V;
}

/* assume dim(a) = n > 0 */
static GEN
ZM_det_i(GEN M, long n)
{
  const long DIXON_THRESHOLD = 40;
  pari_sp av = avma, av2;
  long i;
  ulong p, Dp = 1;
  forprime_t S;
  pari_timer ti;
  GEN H, D, mod, h, q, v, worker;
  if (n == 1) return icopy(gcoeff(M,1,1));
  if (n == 2) return ZM_det2(M);
  if (n == 3) return ZM_det3(M);
  if (DEBUGLEVEL >=4) timer_start(&ti);
  h = RgM_Hadamard(M);
  if (!signe(h)) { avma = av; return gen_0; }
  h = sqrti(h); q = gen_1;
  init_modular_big(&S);
  p = 0; /* -Wall */
  while( cmpii(q, h) <= 0 && (p = u_forprime_next(&S)) )
  {
    av2 = avma; Dp = Flm_det_sp(ZM_to_Flm(M, p), p);
    avma = av2;
    if (Dp) break;
    q = muliu(q, p);
  }
  if (!p) pari_err_OVERFLOW("ZM_det [ran out of primes]");
  if (!Dp) { avma = av; return gen_0; }
  if (n <= DIXON_THRESHOLD)
    D = q;
  else
  {
    av2 = avma;
    v = cgetg(n+1, t_COL);
    gel(v, 1) = gen_1; /* ensure content(v) = 1 */
    for (i = 2; i <= n; i++) gel(v, i) = stoi(random_Fl(15) - 7);
    D = Q_denom(ZM_gauss(M, v));
    if (expi(D) < expi(h) >> 1)
    { /* First try unlucky, try once more */
      for (i = 2; i <= n; i++) gel(v, i) = stoi(random_Fl(15) - 7);
      D = lcmii(D, Q_denom(ZM_gauss(M, v)));
    }
    D = gerepileuptoint(av2, D);
    if (q != gen_1) D = lcmii(D, q);
  }
  /* determinant is a multiple of D */
  if (DEBUGLEVEL >=4)
    timer_printf(&ti,"ZM_det: Dixon %ld/%ld bits",expi(D),expi(h));
  h = divii(h, D);
  worker = strtoclosure("_ZM_det_worker", 1, M);
  H = gen_crt("ZM_det", worker, D, expi(h)+1, lg(M)-1, &mod, ZV_chinese, NULL);
  if (D) H = Fp_div(H, D, mod);
  H = Fp_center(H, mod, shifti(mod,-1));
  if (D) H = mulii(H, D);
  return gerepileuptoint(av, H);
}

static GEN
RgM_det_FpM(GEN a, GEN p)
{
  pari_sp av = avma;
  ulong pp, d;
  a = RgM_Fp_init(a,p,&pp);
  switch(pp)
  {
  case 0: return gerepileupto(av, Fp_to_mod(FpM_det(a,p),p)); break;
  case 2: d = F2m_det(a); break;
  default:d = Flm_det_sp(a, pp); break;
  }
  avma = av; return mkintmodu(d, pp);
}

static GEN
RgM_det_FqM(GEN x, GEN pol, GEN p)
{
  pari_sp av = avma;
  GEN b, T = RgX_to_FpX(pol, p);
  if (signe(T) == 0) pari_err_OP("%",x,pol);
  b = FqM_det(RgM_to_FqM(x, T, p), T, p);
  if (!b) { avma = av; return NULL; }
  return gerepilecopy(av, mkpolmod(FpX_to_mod(b, p), FpX_to_mod(T, p)));
}

#define code(t1,t2) ((t1 << 6) | t2)
static GEN
RgM_det_fast(GEN x)
{
  GEN p, pol;
  long pa;
  long t = RgM_type(x, &p,&pol,&pa);
  switch(t)
  {
    case t_INT:    return ZM_det(x);
    case t_FRAC:   return QM_det(x);
    case t_FFELT:  return FFM_det(x, pol);
    case t_INTMOD: return RgM_det_FpM(x, p);
    case code(t_POLMOD, t_INTMOD):
                   return RgM_det_FqM(x, pol, p);
    default:       return NULL;
  }
}
#undef code

static long
det_init_max(long n)
{
  if (n > 100) return 0;
  if (n > 50) return 1;
  if (n > 30) return 4;
  return 7;
}

GEN
det(GEN a)
{
  long n = lg(a)-1;
  double B;
  GEN data, b;
  pivot_fun pivot;

  if (typ(a)!=t_MAT) pari_err_TYPE("det",a);
  if (!n) return gen_1;
  if (n != nbrows(a)) pari_err_DIM("det");
  if (n == 1) return gcopy(gcoeff(a,1,1));
  if (n == 2) return RgM_det2(a);
  b = RgM_det_fast(a);
  if (b) return b;
  pivot = get_pivot_fun(a, a, &data);
  if (pivot != gauss_get_pivot_NZ) return det_simple_gauss(a, data, pivot);
  B = (double)n;
  return det_develop(a, det_init_max(n), B*B*B);
}

GEN
ZM_det(GEN a)
{
  long n = lg(a)-1;
  if (!n) return gen_1;
  return ZM_det_i(a, n);
}

GEN
QM_det(GEN M)
{
  pari_sp av = avma;
  GEN cM, pM = Q_primitive_part(M, &cM);
  GEN b = ZM_det(pM);
  if (cM) b = gmul(b, gpowgs(cM, lg(M)-1));
  return gerepileupto(av, b);
}
