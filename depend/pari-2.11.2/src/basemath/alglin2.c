/* Copyright (C) 2000  The PARI group.

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
/**                         (second part)                          **/
/**                                                                **/
/********************************************************************/
#include "pari.h"
#include "paripriv.h"
/*******************************************************************/
/*                                                                 */
/*                   CHARACTERISTIC POLYNOMIAL                     */
/*                                                                 */
/*******************************************************************/

static GEN
Flm_charpoly_i(GEN x, ulong p)
{
  long lx = lg(x), r, i;
  GEN H, y = cgetg(lx+1, t_VEC);
  gel(y,1) = pol1_Flx(0); H = Flm_hess(x, p);
  for (r = 1; r < lx; r++)
  {
    pari_sp av2 = avma;
    ulong a = 1;
    GEN z, b = zero_Flx(0);
    for (i = r-1; i; i--)
    {
      a = Fl_mul(a, ucoeff(H,i+1,i), p);
      if (!a) break;
      b = Flx_add(b, Flx_Fl_mul(gel(y,i), Fl_mul(a,ucoeff(H,i,r),p), p), p);
    }
    z = Flx_sub(Flx_shift(gel(y,r), 1),
                Flx_Fl_mul(gel(y,r), ucoeff(H,r,r), p), p);
    /* (X - H[r,r])y[r] - b */
    gel(y,r+1) = gerepileuptoleaf(av2, Flx_sub(z, b, p));
  }
  return gel(y,lx);
}

GEN
Flm_charpoly(GEN x, ulong p)
{
  pari_sp av = avma;
  return gerepileuptoleaf(av, Flm_charpoly_i(x,p));
}

GEN
FpM_charpoly(GEN x, GEN p)
{
  pari_sp av = avma;
  long lx, r, i;
  GEN y, H;

  if (lgefint(p) == 3)
  {
    ulong pp = p[2];
    y = Flx_to_ZX(Flm_charpoly_i(ZM_to_Flm(x,pp), pp));
    return gerepileupto(av, y);
  }
  lx = lg(x); y = cgetg(lx+1, t_VEC);
  gel(y,1) = pol_1(0); H = FpM_hess(x, p);
  for (r = 1; r < lx; r++)
  {
    pari_sp av2 = avma;
    GEN z, a = gen_1, b = pol_0(0);
    for (i = r-1; i; i--)
    {
      a = Fp_mul(a, gcoeff(H,i+1,i), p);
      if (!signe(a)) break;
      b = ZX_add(b, ZX_Z_mul(gel(y,i), Fp_mul(a,gcoeff(H,i,r),p)));
    }
    b = FpX_red(b, p);
    z = FpX_sub(RgX_shift_shallow(gel(y,r), 1),
                FpX_Fp_mul(gel(y,r), gcoeff(H,r,r), p), p);
    z = FpX_sub(z,b,p);
    if (r+1 == lx) { gel(y,lx) = z; break; }
    gel(y,r+1) = gerepileupto(av2, z); /* (X - H[r,r])y[r] - b */
  }
  return gerepileupto(av, gel(y,lx));
}

GEN
charpoly0(GEN x, long v, long flag)
{
  if (v<0) v = 0;
  switch(flag)
  {
    case 0: return caradj(x,v,NULL);
    case 1: return caract(x,v);
    case 2: return carhess(x,v);
    case 3: return carberkowitz(x,v);
    case 4:
      if (typ(x) != t_MAT) pari_err_TYPE("charpoly",x);
      RgM_check_ZM(x, "charpoly");
      x = ZM_charpoly(x); setvarn(x, v); return x;
    case 5:
      return charpoly(x, v);
  }
  pari_err_FLAG("charpoly");
  return NULL; /* LCOV_EXCL_LINE */
}

/* characteristic pol. Easy cases. Return NULL in case it's not so easy. */
static GEN
easychar(GEN x, long v)
{
  pari_sp av;
  long lx;
  GEN p1;

  switch(typ(x))
  {
    case t_INT: case t_REAL: case t_INTMOD:
    case t_FRAC: case t_PADIC:
      p1=cgetg(4,t_POL);
      p1[1]=evalsigne(1) | evalvarn(v);
      gel(p1,2) = gneg(x); gel(p1,3) = gen_1;
      return p1;

    case t_COMPLEX: case t_QUAD:
      p1 = cgetg(5,t_POL);
      p1[1] = evalsigne(1) | evalvarn(v);
      gel(p1,2) = gnorm(x); av = avma;
      gel(p1,3) = gerepileupto(av, gneg(gtrace(x)));
      gel(p1,4) = gen_1; return p1;

    case t_FFELT: {
      pari_sp ltop=avma;
      p1 = FpX_to_mod(FF_charpoly(x), FF_p_i(x));
      setvarn(p1,v); return gerepileupto(ltop,p1);
    }

    case t_POLMOD:
    {
      GEN A = gel(x,2), T = gel(x,1);
      if (typ(A)==t_POL && RgX_is_QX(A) && RgX_is_ZX(T))
        return QXQ_charpoly(A, T, v);
      else
        return RgXQ_charpoly(A, T, v);
    }
    case t_MAT:
      lx=lg(x);
      if (lx==1) return pol_1(v);
      if (lgcols(x) != lx) break;
      return NULL;
  }
  pari_err_TYPE("easychar",x);
  return NULL; /* LCOV_EXCL_LINE */
}
/* compute charpoly by mapping to Fp first, return lift to Z */
static GEN
RgM_Fp_charpoly(GEN x, GEN p, long v)
{
  GEN T;
  if (lgefint(p) == 3)
  {
    ulong pp = itou(p);
    T = Flm_charpoly_i(RgM_to_Flm(x, pp), pp);
    T = Flx_to_ZX(T);
  }
  else
    T = FpM_charpoly(RgM_to_FpM(x, p), p);
  setvarn(T, v); return T;
}
GEN
charpoly(GEN x, long v)
{
  GEN T, p = NULL;
  long prec;
  if ((T = easychar(x,v))) return T;
  switch(RgM_type(x, &p,&T,&prec))
  {
    case t_INT:
      T = ZM_charpoly(x); setvarn(T, v); break;
    case t_INTMOD:
      if (!BPSW_psp(p)) T = carberkowitz(x, v);
      else
      {
        pari_sp av = avma;
        T = RgM_Fp_charpoly(x,p,v);
        T = gerepileupto(av, FpX_to_mod(T,p));
      }
      break;
    case t_REAL:
    case t_COMPLEX:
    case t_PADIC:
      T = carhess(x, v);
      break;
    default:
      T = carberkowitz(x, v);
  }
  return T;
}

/* We possibly worked with an "invalid" polynomial p, satisfying
 * varn(p) > gvar2(p). Fix this. */
static GEN
fix_pol(pari_sp av, GEN p)
{
  long w = gvar2(p), v = varn(p);
  if (w == v) pari_err_PRIORITY("charpoly", p, "=", w);
  if (varncmp(w,v) < 0) p = gerepileupto(av, poleval(p, pol_x(v)));
  return p;
}
GEN
caract(GEN x, long v)
{
  pari_sp av = avma;
  GEN  T, C, x_k, Q;
  long k, n;

  if ((T = easychar(x,v))) return T;

  n = lg(x)-1;
  if (n == 1) return fix_pol(av, deg1pol(gen_1, gneg(gcoeff(x,1,1)), v));

  x_k = pol_x(v); /* to be modified in place */
  T = scalarpol(det(x), v); C = utoineg(n); Q = pol_x(v);
  for (k=1; k<=n; k++)
  {
    GEN mk = utoineg(k), d;
    gel(x_k,2) = mk;
    d = det(RgM_Rg_add_shallow(x, mk));
    T = RgX_add(RgX_mul(T, x_k), RgX_Rg_mul(Q, gmul(C, d)));
    if (k == n) break;

    Q = RgX_mul(Q, x_k);
    C = diviuexact(mulsi(k-n,C), k+1); /* (-1)^k binomial(n,k) */
  }
  return fix_pol(av, RgX_Rg_div(T, mpfact(n)));
}

/* C = charpoly(x, v) */
static GEN
RgM_adj_from_char(GEN x, long v, GEN C)
{
  if (varn(C) != v) /* problem with variable priorities */
  {
    C = gdiv(gsub(C, gsubst(C, v, gen_0)), pol_x(v));
    if (odd(lg(x))) C = RgX_neg(C); /* even dimension */
    return gsubst(C, v, x);
  }
  else
  {
    C = RgX_shift_shallow(C, -1);
    if (odd(lg(x))) C = RgX_neg(C); /* even dimension */
    return RgX_RgM_eval(C, x);
  }
}
/* assume x square matrice */
static GEN
mattrace(GEN x)
{
  long i, lx = lg(x);
  GEN t;
  if (lx < 3) return lx == 1? gen_0: gcopy(gcoeff(x,1,1));
  t = gcoeff(x,1,1);
  for (i = 2; i < lx; i++) t = gadd(t, gcoeff(x,i,i));
  return t;
}
static int
bad_char(GEN q, long n)
{
  forprime_t S;
  ulong p;
  if (!signe(q)) return 0;
  (void)u_forprime_init(&S, 2, n);
  while ((p = u_forprime_next(&S)))
    if (!umodiu(q, p)) return 1;
  return 0;
}
/* Using traces: return the characteristic polynomial of x (in variable v).
 * If py != NULL, the adjoint matrix is put there. */
GEN
caradj(GEN x, long v, GEN *py)
{
  pari_sp av, av0;
  long i, k, n;
  GEN T, y, t;

  if ((T = easychar(x, v)))
  {
    if (py)
    {
      if (typ(x) != t_MAT) pari_err_TYPE("matadjoint",x);
      *py = cgetg(1,t_MAT);
    }
    return T;
  }

  n = lg(x)-1; av0 = avma;
  T = cgetg(n+3,t_POL); T[1] = evalsigne(1) | evalvarn(v);
  gel(T,n+2) = gen_1;
  if (!n) { if (py) *py = cgetg(1,t_MAT); return T; }
  av = avma; t = gerepileupto(av, gneg(mattrace(x)));
  gel(T,n+1) = t;
  if (n == 1) {
    T = fix_pol(av0, T);
    if (py) *py = matid(1); return T;
  }
  if (n == 2) {
    GEN a = gcoeff(x,1,1), b = gcoeff(x,1,2);
    GEN c = gcoeff(x,2,1), d = gcoeff(x,2,2);
    av = avma;
    gel(T,2) = gerepileupto(av, gsub(gmul(a,d), gmul(b,c)));
    T = fix_pol(av0, T);
    if (py) {
      y = cgetg(3, t_MAT);
      gel(y,1) = mkcol2(gcopy(d), gneg(c));
      gel(y,2) = mkcol2(gneg(b), gcopy(a));
      *py = y;
    }
    return T;
  }
  /* l > 3 */
  if (bad_char(residual_characteristic(x), n))
  { /* n! not invertible in base ring */
    T = charpoly(x, v);
    if (!py) return gerepileupto(av, T);
    *py = RgM_adj_from_char(x, v, T);
    gerepileall(av, 2, &T,py);
    return T;
  }
  av = avma; y = RgM_shallowcopy(x);
  for (i = 1; i <= n; i++) gcoeff(y,i,i) = gadd(gcoeff(y,i,i), t);
  for (k = 2; k < n; k++)
  {
    GEN y0 = y;
    y = RgM_mul(y, x);
    t = gdivgs(mattrace(y), -k);
    for (i = 1; i <= n; i++) gcoeff(y,i,i) = gadd(gcoeff(y,i,i), t);
    y = gclone(y);
    gel(T,n-k+2) = gerepilecopy(av, t); av = avma;
    if (k > 2) gunclone(y0);
  }
  t = gmul(gcoeff(x,1,1),gcoeff(y,1,1));
  for (i=2; i<=n; i++) t = gadd(t, gmul(gcoeff(x,1,i),gcoeff(y,i,1)));
  gel(T,2) = gerepileupto(av, gneg(t));
  T = fix_pol(av0, T);
  if (py) *py = odd(n)? gcopy(y): RgM_neg(y);
  gunclone(y); return T;
}

GEN
adj(GEN x)
{
  GEN y;
  (void)caradj(x, fetch_var(), &y);
  (void)delete_var(); return y;
}

GEN
adjsafe(GEN x)
{
  const long v = fetch_var();
  pari_sp av = avma;
  GEN C, A;
  if (typ(x) != t_MAT) pari_err_TYPE("matadjoint",x);
  if (lg(x) < 3) return gcopy(x);
  C = charpoly(x,v);
  A = RgM_adj_from_char(x, v, C);
  (void)delete_var(); return gerepileupto(av, A);
}

GEN
matadjoint0(GEN x, long flag)
{
  switch(flag)
  {
    case 0: return adj(x);
    case 1: return adjsafe(x);
  }
  pari_err_FLAG("matadjoint");
  return NULL; /* LCOV_EXCL_LINE */
}

/*******************************************************************/
/*                                                                 */
/*                       Frobenius form                            */
/*                                                                 */
/*******************************************************************/

/* The following section implement a mix of Ozello and Storjohann algorithms

P. Ozello, doctoral thesis (in French):
Calcul exact des formes de Jordan et de Frobenius d'une matrice, Chapitre 2
http://tel.archives-ouvertes.fr/tel-00323705

A. Storjohann,  Diss. ETH No. 13922
Algorithms for Matrix Canonical Forms, Chapter 9
https://cs.uwaterloo.ca/~astorjoh/diss2up.pdf

We use Storjohann Lemma 9.14 (step1, step2, step3) Ozello theorem 4,
and Storjohann Lemma 9.18
*/

/* Elementary transforms */

/* M <- U^(-1) M U, U = E_{i,j}(k) => U^(-1) = E{i,j}(-k)
 * P = U * P */
static void
transL(GEN M, GEN P, GEN k, long i, long j)
{
  long l, n = lg(M)-1;
  for(l=1; l<=n; l++) /* M[,j]-=k*M[,i] */
    gcoeff(M,l,j) = gsub(gcoeff(M,l,j), gmul(gcoeff(M,l,i), k));
  for(l=1; l<=n; l++) /* M[i,]+=k*M[j,] */
    gcoeff(M,i,l) = gadd(gcoeff(M,i,l), gmul(gcoeff(M,j,l), k));
  if (P)
    for(l=1; l<=n; l++)
      gcoeff(P,i,l) = gadd(gcoeff(P,i,l), gmul(gcoeff(P,j,l), k));
}

/* j = a or b */
static void
transD(GEN M, GEN P, long a, long b, long j)
{
  long l, n;
  GEN k = gcoeff(M,a,b), ki;

  if (gequal1(k)) return;
  ki = ginv(k); n = lg(M)-1;
  for(l=1; l<=n; l++)
    if (l!=j)
    {
      gcoeff(M,l,j) = gmul(gcoeff(M,l,j), k);
      gcoeff(M,j,l) = (j==a && l==b)? gen_1: gmul(gcoeff(M,j,l), ki);
    }
  if (P)
    for(l=1; l<=n; l++)
      gcoeff(P,j,l) = gmul(gcoeff(P,j,l), ki);
}

static void
transS(GEN M, GEN P, long i, long j)
{
  long l, n = lg(M)-1;
  swap(gel(M,i), gel(M,j));
  for (l=1; l<=n; l++)
    swap(gcoeff(M,i,l), gcoeff(M,j,l));
  if (P)
    for (l=1; l<=n; l++)
      swap(gcoeff(P,i,l), gcoeff(P,j,l));
}

/* Convert companion matrix to polynomial*/
static GEN
minpoly_polslice(GEN M, long i, long j, long v)
{
  long k, d = j+1-i;
  GEN P = cgetg(d+3,t_POL);
  P[1] = evalsigne(1)|evalvarn(v);
  for (k=0; k<d; k++)
    gel(P,k+2) = gneg(gcoeff(M,i+k, j));
  gel(P,d+2) = gen_1;
  return P;
}

static GEN
minpoly_listpolslice(GEN M, GEN V, long v)
{
  long i, n = lg(M)-1, nb = lg(V)-1;
  GEN W = cgetg(nb+1, t_VEC);
  for (i=1; i<=nb; i++)
    gel(W,i) = minpoly_polslice(M, V[i], i < nb? V[i+1]-1: n, v);
  return W;
}

static int
minpoly_dvdslice(GEN M, long i, long j, long k)
{
  pari_sp av = avma;
  long r = signe(RgX_rem(minpoly_polslice(M, i, j-1, 0),
                        minpoly_polslice(M, j, k, 0)));
  avma = av; return r==0;
}

static void
RgM_replace(GEN M, GEN M2)
{
  long n = lg(M)-1, m = nbrows(M), i, j;
  for(i=1; i<=n; i++)
    for(j=1; j<=m; j++)
      gcoeff(M, i, j) = gcoeff(M2, i, j);
}

static void
gerepilemat2_inplace(pari_sp av, GEN M, GEN P)
{
  GEN M2 = M, P2 = P;
  gerepileall(av, P ? 2: 1, &M2, &P2);
  RgM_replace(M, M2);
  if (P) RgM_replace(P, P2);
}

/* Lemma 9.14 */
static long
weakfrobenius_step1(GEN M, GEN P, long j0)
{
  pari_sp av = avma;
  long n = lg(M)-1, k, j;
  for (j = j0; j < n; ++j)
  {
    if (gequal0(gcoeff(M, j+1, j)))
    {
      for (k = j+2; k <= n; ++k)
        if (!gequal0(gcoeff(M,k,j))) break;
      if (k > n) return j;
      transS(M, P, k, j+1);
    }
    transD(M, P, j+1, j, j+1);
    /* Now M[j+1,j] = 1 */
    for (k = 1; k <= n; ++k)
      if (k != j+1 && !gequal0(gcoeff(M,k,j))) /* zero M[k,j] */
      {
        transL(M, P, gneg(gcoeff(M,k,j)), k, j+1);
        gcoeff(M,k,j) = gen_0; /* avoid approximate 0 */
      }
    if (gc_needed(av,1))
    {
      if (DEBUGMEM > 1)
        pari_warn(warnmem,"RgM_minpoly stage 1: j0=%ld, j=%ld", j0, j);
      gerepilemat2_inplace(av, M, P);
    }
  }
  return n;
}

static void
weakfrobenius_step2(GEN M, GEN P, long j)
{
  pari_sp av = avma;
  long i, k, n = lg(M)-1;
  for(i=j; i>=2; i--)
  {
    for(k=j+1; k<=n; k++)
      if (!gequal0(gcoeff(M,i,k)))
        transL(M, P, gcoeff(M,i,k), i-1, k);
    if (gc_needed(av,1))
    {
      if (DEBUGMEM > 1)
        pari_warn(warnmem,"RgM_minpoly stage 2: j=%ld, i=%ld", j, i);
      gerepilemat2_inplace(av, M, P);
    }
  }
}

static long
weakfrobenius_step3(GEN M, GEN P, long j0, long j)
{
  long i, k, n = lg(M)-1;
  if (j == n) return 0;
  if (gequal0(gcoeff(M, j0, j+1)))
  {
    for (k=j+2; k<=n; k++)
      if (!gequal0(gcoeff(M, j0, k))) break;
    if (k > n) return 0;
    transS(M, P, k, j+1);
  }
  transD(M, P, j0, j+1, j+1);
  for (i=j+2; i<=n; i++)
    if (!gequal0(gcoeff(M, j0, i)))
      transL(M, P, gcoeff(M, j0, i),j+1, i);
  return 1;
}

/* flag: 0 -> full Frobenius from , 1 -> weak Frobenius form */
static GEN
RgM_Frobenius(GEN M, long flag, GEN *pt_P, GEN *pt_v)
{
  pari_sp av = avma, av2, ltop;
  long n = lg(M)-1, eps, j0 = 1, nb = 0;
  GEN v, P;
  v = cgetg(n+1, t_VECSMALL);
  ltop = avma;
  P = pt_P ? matid(n): NULL;
  M = RgM_shallowcopy(M);
  av2 = avma;
  while (j0 <= n)
  {
    long j = weakfrobenius_step1(M, P, j0);
    weakfrobenius_step2(M, P, j);
    eps = weakfrobenius_step3(M, P, j0, j);
    if (eps == 0)
    {
      v[++nb] = j0;
      if (flag == 0 && nb > 1 && !minpoly_dvdslice(M, v[nb-1], j0, j))
      {
        j = j0; j0 = v[nb-1]; nb -= 2;
        transL(M, P, gen_1, j, j0); /*lemma 9.18*/
      } else
        j0 = j+1;
    }
    else
      transS(M, P, j0, j+1); /*theorem 4*/
    if (gc_needed(av,1))
    {
      if (DEBUGMEM > 1)
        pari_warn(warnmem,"weakfrobenius j0=%ld",j0);
      gerepilemat2_inplace(av2, M, P);
    }
  }
  fixlg(v, nb+1);
  if (pt_v) *pt_v = v;
  gerepileall(pt_v ? ltop: av, P? 2: 1, &M, &P);
  if (pt_P) *pt_P = P;
  return M;
}

static GEN
RgM_minpoly(GEN M, long v)
{
  pari_sp av = avma;
  GEN V, W;
  if (lg(M) == 1) return pol_1(v);
  M = RgM_Frobenius(M, 1, NULL, &V);
  W = minpoly_listpolslice(M, V, v);
  if (varncmp(v,gvar2(W)) >= 0)
    pari_err_PRIORITY("matfrobenius", M, "<=", v);
  return gerepileupto(av, RgX_normalize(glcm0(W, NULL)));
}

GEN
Frobeniusform(GEN V, long n)
{
  long i, j, k;
  GEN M = zeromatcopy(n,n);
  for (k=1,i=1;i<lg(V);i++,k++)
  {
    GEN  P = gel(V,i);
    long d = degpol(P);
    if (k+d-1 > n) pari_err_PREC("matfrobenius");
    for (j=0; j<d-1; j++, k++) gcoeff(M,k+1,k) = gen_1;
    for (j=0; j<d; j++) gcoeff(M,k-j,k) = gneg(gel(P, 1+d-j));
  }
  return M;
}

GEN
matfrobenius(GEN M, long flag, long v)
{
  long n;
  if (typ(M)!=t_MAT) pari_err_TYPE("matfrobenius",M);
  if (v < 0) v = 0;
  n = lg(M)-1;
  if (n && lgcols(M)!=n+1) pari_err_DIM("matfrobenius");
  if (flag > 2) pari_err_FLAG("matfrobenius");
  switch (flag)
  {
  case 0:
    return RgM_Frobenius(M, 0, NULL, NULL);
  case 1:
    {
      pari_sp av = avma;
      GEN V, W, F;
      F = RgM_Frobenius(M, 0, NULL, &V);
      W = minpoly_listpolslice(F, V, v);
      if (varncmp(v, gvar2(W)) >= 0)
        pari_err_PRIORITY("matfrobenius", M, "<=", v);
      return gerepileupto(av, W);
    }
  case 2:
    {
      GEN P, F, R = cgetg(3, t_VEC);
      F = RgM_Frobenius(M, 0, &P, NULL);
      gel(R,1) = F; gel(R,2) = P;
      return R;
    }
  default:
    pari_err_FLAG("matfrobenius");
  }
  return NULL; /*LCOV_EXCL_LINE*/
}

/*******************************************************************/
/*                                                                 */
/*                       MINIMAL POLYNOMIAL                        */
/*                                                                 */
/*******************************************************************/

static GEN
RgXQ_minpoly_naive(GEN y, GEN P)
{
  long n = lgpol(P);
  GEN M = ker(RgXQ_matrix_pow(y,n,n,P));
  return content(RgM_to_RgXV(M,varn(P)));
}
static GEN
easymin(GEN x, long v)
{
  GEN G, R, dR;
  long tx = typ(x);
  if (tx == t_FFELT)
  {
    R = FpX_to_mod(FF_minpoly(x), FF_p_i(x));
    setvarn(R,v); return R;
  }
  if (tx == t_POLMOD)
  {
    GEN a = gel(x,2), b = gel(x,1);
    if (typ(a) != t_POL || varn(a) != varn(b))
    {
      if (varncmp(gvar(a), v) <= 0) pari_err_PRIORITY("minpoly", x, "<", v);
      return deg1pol(gen_1, gneg_i(a), v);
    }
    if (!issquarefree(b))
    {
      R = RgXQ_minpoly_naive(a, b);
      setvarn(R,v); return R;
    }
  }
  R = easychar(x, v); if (!R) return NULL;
  dR = RgX_deriv(R);  if (!lgpol(dR)) return NULL;
  G = RgX_normalize(RgX_gcd(R,dR));
  return RgX_div(R,G);
}
GEN
minpoly(GEN x, long v)
{
  pari_sp av = avma;
  GEN P;
  if (v < 0) v = 0;
  P = easymin(x,v);
  if (P) return gerepileupto(av,P);
  avma = av;
  if (typ(x) == t_POLMOD)
  {
    P = RgXQ_minpoly_naive(gel(x,2), gel(x,1));
    setvarn(P,v); return gerepileupto(av,P);
  }
  if (typ(x) != t_MAT) pari_err_TYPE("minpoly",x);
  if (lg(x) == 1) return pol_1(v);
  return RgM_minpoly(x,v);
}

/*******************************************************************/
/*                                                                 */
/*                       HESSENBERG FORM                           */
/*                                                                 */
/*******************************************************************/
static int
relative0(GEN a, GEN a0, long bit)
{ return gequal0(a) || (bit && gexpo(a)-gexpo(a0) < bit); }
/* assume x a non-empty square t_MAT */
static GEN
RgM_hess(GEN x0, long prec)
{
  pari_sp av;
  long lx = lg(x0), bit = prec? 8 - bit_accuracy(prec): 0, m, i, j;
  GEN x;

  if (bit) x0 = RgM_shallowcopy(x0);
  av = avma; x = RgM_shallowcopy(x0);
  for (m=2; m<lx-1; m++)
  {
    GEN t = NULL;
    for (i=m+1; i<lx; i++)
    {
      t = gcoeff(x,i,m-1);
      if (!relative0(t, gcoeff(x0,i,m-1), bit)) break;
    }
    if (i == lx) continue;
    for (j=m-1; j<lx; j++) swap(gcoeff(x,i,j), gcoeff(x,m,j));
    swap(gel(x,i), gel(x,m));
    if (bit)
    {
      for (j=m-1; j<lx; j++) swap(gcoeff(x0,i,j), gcoeff(x0,m,j));
      swap(gel(x0,i), gel(x0,m));
    }
    t = ginv(t);

    for (i=m+1; i<lx; i++)
    {
      GEN c = gcoeff(x,i,m-1);
      if (gequal0(c)) continue;

      c = gmul(c,t); gcoeff(x,i,m-1) = gen_0;
      for (j=m; j<lx; j++)
        gcoeff(x,i,j) = gsub(gcoeff(x,i,j), gmul(c,gcoeff(x,m,j)));
      for (j=1; j<lx; j++)
        gcoeff(x,j,m) = gadd(gcoeff(x,j,m), gmul(c,gcoeff(x,j,i)));
      if (gc_needed(av,2))
      {
        if (DEBUGMEM>1) pari_warn(warnmem,"hess, m = %ld", m);
        gerepileall(av,2, &x, &t);
      }
    }
  }
  return x;
}

GEN
hess(GEN x)
{
  pari_sp av = avma;
  GEN p = NULL, T = NULL;
  long prec, lx = lg(x);
  if (typ(x) != t_MAT) pari_err_TYPE("hess",x);
  if (lx == 1) return cgetg(1,t_MAT);
  if (lgcols(x) != lx) pari_err_DIM("hess");
  switch(RgM_type(x, &p, &T, &prec))
  {
    case t_REAL:
    case t_COMPLEX: break;
    default: prec = 0;
  }
  return gerepilecopy(av, RgM_hess(x,prec));
}

GEN
Flm_hess(GEN x, ulong p)
{
  long lx = lg(x), m, i, j;
  if (lx == 1) return cgetg(1,t_MAT);
  if (lgcols(x) != lx) pari_err_DIM("hess");

  x = Flm_copy(x);
  for (m=2; m<lx-1; m++)
  {
    ulong t = 0;
    for (i=m+1; i<lx; i++) { t = ucoeff(x,i,m-1); if (t) break; }
    if (i == lx) continue;
    for (j=m-1; j<lx; j++) lswap(ucoeff(x,i,j), ucoeff(x,m,j));
    swap(gel(x,i), gel(x,m)); t = Fl_inv(t, p);

    for (i=m+1; i<lx; i++)
    {
      ulong c = ucoeff(x,i,m-1);
      if (!c) continue;

      c = Fl_mul(c,t,p); ucoeff(x,i,m-1) = 0;
      for (j=m; j<lx; j++)
        ucoeff(x,i,j) = Fl_sub(ucoeff(x,i,j), Fl_mul(c,ucoeff(x,m,j), p), p);
      for (j=1; j<lx; j++)
        ucoeff(x,j,m) = Fl_add(ucoeff(x,j,m), Fl_mul(c,ucoeff(x,j,i), p), p);
    }
  }
  return x;
}
GEN
FpM_hess(GEN x, GEN p)
{
  pari_sp av = avma;
  long lx = lg(x), m, i, j;
  if (lx == 1) return cgetg(1,t_MAT);
  if (lgcols(x) != lx) pari_err_DIM("hess");
  if (lgefint(p) == 3)
  {
    ulong pp = p[2];
    x = Flm_hess(ZM_to_Flm(x, pp), pp);
    return gerepileupto(av, Flm_to_ZM(x));
  }
  x = RgM_shallowcopy(x);
  for (m=2; m<lx-1; m++)
  {
    GEN t = NULL;
    for (i=m+1; i<lx; i++) { t = gcoeff(x,i,m-1); if (signe(t)) break; }
    if (i == lx) continue;
    for (j=m-1; j<lx; j++) swap(gcoeff(x,i,j), gcoeff(x,m,j));
    swap(gel(x,i), gel(x,m)); t = Fp_inv(t, p);

    for (i=m+1; i<lx; i++)
    {
      GEN c = gcoeff(x,i,m-1);
      if (!signe(c)) continue;

      c = Fp_mul(c,t, p); gcoeff(x,i,m-1) = gen_0;
      for (j=m; j<lx; j++)
        gcoeff(x,i,j) = Fp_sub(gcoeff(x,i,j), Fp_mul(c,gcoeff(x,m,j),p), p);
      for (j=1; j<lx; j++)
        gcoeff(x,j,m) = Fp_add(gcoeff(x,j,m), Fp_mul(c,gcoeff(x,j,i),p), p);
      if (gc_needed(av,2))
      {
        if (DEBUGMEM>1) pari_warn(warnmem,"hess, m = %ld", m);
        gerepileall(av,2, &x, &t);
      }
    }
  }
  return gerepilecopy(av,x);
}
/* H in Hessenberg form */
static GEN
RgM_hess_charpoly(GEN H, long v)
{
  long n = lg(H), r, i;
  GEN y = cgetg(n+1, t_VEC);
  gel(y,1) = pol_1(v);
  for (r = 1; r < n; r++)
  {
    pari_sp av2 = avma;
    GEN z, a = gen_1, b = pol_0(v);
    for (i = r-1; i; i--)
    {
      a = gmul(a, gcoeff(H,i+1,i));
      if (gequal0(a)) break;
      b = RgX_add(b, RgX_Rg_mul(gel(y,i), gmul(a,gcoeff(H,i,r))));
    }
    z = RgX_sub(RgX_shift_shallow(gel(y,r), 1),
                RgX_Rg_mul(gel(y,r), gcoeff(H,r,r)));
    gel(y,r+1) = gerepileupto(av2, RgX_sub(z, b)); /* (X - H[r,r])y[r] - b */
  }
  return gel(y,n);
}
GEN
carhess(GEN x, long v)
{
  pari_sp av;
  GEN y;
  if ((y = easychar(x,v))) return y;
  av = avma; y = RgM_hess_charpoly(hess(x), v);
  return fix_pol(av, y);
}

/* Bound for sup norm of charpoly(M/dM), M integral: let B = |M|oo / |dM|,
 *   s = max_k binomial(n,k) (kB^2)^(k/2),
 * return ceil(log2(s)) */
static double
charpoly_bound(GEN M, GEN dM)
{
  pari_sp av = avma;
  GEN B = itor(ZM_supnorm(M), LOWDEFAULTPREC);
  GEN s = real_0(LOWDEFAULTPREC), bin, B2;
  long n = lg(M)-1, k;
  double d;
  bin = gen_1;
  if (dM) B = divri(B, dM);
  B2 = sqrr(B);
  for (k = n; k >= (n+1)>>1; k--)
  {
    GEN t = mulri(powruhalf(mulur(k, B2), k), bin);
    if (abscmprr(t, s) > 0) s = t;
    bin = diviuexact(muliu(bin, k), n-k+1);
  }
  d = dbllog2(s); avma = av; return ceil(d);
}

/* Return char_{M/d}(X) = d^(-n) char_M(dX) modulo p. Assume dp = d mod p. */
static GEN
QM_charpoly_Flx(GEN M, ulong dp, ulong p)
{
  pari_sp av = avma;
  GEN H = Flm_charpoly_i(ZM_to_Flm(M,p), p);
  if (dp) H = Flx_rescale(H, Fl_inv(dp,p), p);
  return gerepileuptoleaf(av, H);
}

static int
ZX_CRT(GEN *H, GEN Hp, GEN *q, ulong p, long bit)
{
  if (!*H)
  {
    *H = ZX_init_CRT(Hp, p, 0);
    if (DEBUGLEVEL>5)
      err_printf("charpoly mod %lu, bound = 2^%ld\n", p, expu(p));
    if (expu(p) > bit) return 1;
    *q = utoipos(p);
  }
  else
  {
    int stable = ZX_incremental_CRT(H, Hp, q,p);
    if (DEBUGLEVEL>5)
      err_printf("charpoly mod %lu (stable=%ld), bound = 2^%ld\n",
                 p, stable, expi(*q));
    if (stable && expi(*q) > bit) return 1;
  }
  return 0;
}

/* Assume M a square ZM, dM integer. Return charpoly(M / dM) in Z[X] */
static GEN
QM_charpoly_ZX_i(GEN M, GEN dM, long bit)
{
  long n = lg(M)-1;
  GEN q = NULL, H = NULL;
  forprime_t S;
  ulong p;
  if (!n) return pol_1(0);

  if (bit < 0) bit = (long)charpoly_bound(M, dM) + 1;
  if (DEBUGLEVEL>5) err_printf("ZM_charpoly: bit-bound 2^%ld\n", bit);
  init_modular_big(&S);
  while ((p = u_forprime_next(&S)))
  {
    ulong dMp = 0;
    GEN Hp;
    if (dM && !(dMp = umodiu(dM, p))) continue;
    Hp = QM_charpoly_Flx(M, dMp, p);
    if (ZX_CRT(&H, Hp, &q,p, bit)) break;
  }
  if (!p) pari_err_OVERFLOW("charpoly [ran out of primes]");
  return H;
}
GEN
QM_charpoly_ZX_bound(GEN M, long bit)
{
  pari_sp av = avma;
  GEN dM; M = Q_remove_denom(M, &dM);
  return gerepilecopy(av, QM_charpoly_ZX_i(M, dM, bit));
}
GEN
QM_charpoly_ZX(GEN M)
{
  pari_sp av = avma;
  GEN dM; M = Q_remove_denom(M, &dM);
  return gerepilecopy(av, QM_charpoly_ZX_i(M, dM, -1));
}
GEN
ZM_charpoly(GEN M)
{
  pari_sp av = avma;
  return gerepilecopy(av, QM_charpoly_ZX_i(M, NULL, -1));
}

/*******************************************************************/
/*                                                                 */
/*        CHARACTERISTIC POLYNOMIAL (BERKOWITZ'S ALGORITHM)        */
/*                                                                 */
/*******************************************************************/
GEN
carberkowitz(GEN x, long v)
{
  long lx, i, j, k, r;
  GEN V, S, C, Q;
  pari_sp av0, av;
  if ((V = easychar(x,v))) return V;
  lx = lg(x); av0 = avma;
  V = cgetg(lx+1, t_VEC);
  S = cgetg(lx+1, t_VEC);
  C = cgetg(lx+1, t_VEC);
  Q = cgetg(lx+1, t_VEC);
  av = avma;
  gel(C,1) = gen_m1;
  gel(V,1) = gen_m1;
  for (i=2;i<=lx; i++) gel(C,i) = gel(Q,i) = gel(S,i) = gel(V,i) = gen_0;
  gel(V,2) = gcoeff(x,1,1);
  for (r = 2; r < lx; r++)
  {
    pari_sp av2;
    GEN t;

    for (i = 1; i < r; i++) gel(S,i) = gcoeff(x,i,r);
    gel(C,2) = gcoeff(x,r,r);
    for (i = 1; i < r-1; i++)
    {
      av2 = avma; t = gmul(gcoeff(x,r,1), gel(S,1));
      for (j = 2; j < r; j++) t = gadd(t, gmul(gcoeff(x,r,j), gel(S,j)));
      gel(C,i+2) = gerepileupto(av2, t);
      for (j = 1; j < r; j++)
      {
        av2 = avma; t = gmul(gcoeff(x,j,1), gel(S,1));
        for (k = 2; k < r; k++) t = gadd(t, gmul(gcoeff(x,j,k), gel(S,k)));
        gel(Q,j) = gerepileupto(av2, t);
      }
      for (j = 1; j < r; j++) gel(S,j) = gel(Q,j);
    }
    av2 = avma; t = gmul(gcoeff(x,r,1), gel(S,1));
    for (j = 2; j < r; j++) t = gadd(t, gmul(gcoeff(x,r,j), gel(S,j)));
    gel(C,r+1) = gerepileupto(av2, t);
    if (gc_needed(av0,1))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"carberkowitz");
      gerepileall(av, 2, &C, &V);
    }
    for (i = 1; i <= r+1; i++)
    {
      av2 = avma; t = gmul(gel(C,i), gel(V,1));
      for (j = 2; j <= minss(r,i); j++)
        t = gadd(t, gmul(gel(C,i+1-j), gel(V,j)));
      gel(Q,i) = gerepileupto(av2, t);
    }
    for (i = 1; i <= r+1; i++) gel(V,i) = gel(Q,i);
  }
  V = RgV_to_RgX(vecreverse(V), v); /* not gtopoly: fail if v > gvar(V) */
  V = odd(lx)? gcopy(V): RgX_neg(V);
  return fix_pol(av0, V);
}

/*******************************************************************/
/*                                                                 */
/*                            NORMS                                */
/*                                                                 */
/*******************************************************************/
GEN
gnorm(GEN x)
{
  pari_sp av;
  long lx, i;
  GEN y;

  switch(typ(x))
  {
    case t_INT:  return sqri(x);
    case t_REAL: return sqrr(x);
    case t_FRAC: return sqrfrac(x);
    case t_COMPLEX: av = avma; return gerepileupto(av, cxnorm(x));
    case t_QUAD:    av = avma; return gerepileupto(av, quadnorm(x));

    case t_POL: case t_SER: case t_RFRAC: av = avma;
      return gerepileupto(av, greal(gmul(conj_i(x),x)));

    case t_FFELT:
      y = cgetg(3, t_INTMOD);
      gel(y,1) = FF_p(x);
      gel(y,2) = FF_norm(x); return y;

    case t_POLMOD:
    {
      GEN T = gel(x,1), a = gel(x,2);
      if (typ(a) != t_POL || varn(a) != varn(T)) return gpowgs(a, degpol(T));
      return RgXQ_norm(a, T);
    }
    case t_VEC: case t_COL: case t_MAT:
      y = cgetg_copy(x, &lx);
      for (i=1; i<lx; i++) gel(y,i) = gnorm(gel(x,i));
      return y;
  }
  pari_err_TYPE("gnorm",x);
  return NULL; /* LCOV_EXCL_LINE */
}

/* return |q|^2, complex modulus */
static GEN
cxquadnorm(GEN q, long prec)
{
  GEN X = gel(q,1), c = gel(X,2); /* (1-D)/4, -D/4 */
  if (signe(c) > 0) return quadnorm(q); /* imaginary */
  if (!prec) pari_err_TYPE("gnorml2", q);
  return sqrr(quadtofp(q, prec));
}

static GEN
gnorml2_i(GEN x, long prec)
{
  pari_sp av;
  long i, lx;
  GEN s;

  switch(typ(x))
  {
    case t_INT:  return sqri(x);
    case t_REAL: return sqrr(x);
    case t_FRAC: return sqrfrac(x);
    case t_COMPLEX: av = avma; return gerepileupto(av, cxnorm(x));
    case t_QUAD:    av = avma; return gerepileupto(av, cxquadnorm(x,prec));

    case t_POL: lx = lg(x)-1; x++; break;

    case t_VEC:
    case t_COL:
    case t_MAT: lx = lg(x); break;

    default: pari_err_TYPE("gnorml2",x);
      return NULL; /* LCOV_EXCL_LINE */
  }
  if (lx == 1) return gen_0;
  av = avma;
  s = gnorml2(gel(x,1));
  for (i=2; i<lx; i++)
  {
    s = gadd(s, gnorml2(gel(x,i)));
    if (gc_needed(av,1))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"gnorml2");
      s = gerepileupto(av, s);
    }
  }
  return gerepileupto(av,s);
}
GEN
gnorml2(GEN x) { return gnorml2_i(x, 0); }

static GEN pnormlp(GEN,GEN,long);
static GEN
pnormlpvec(long i0, GEN x, GEN p, long prec)
{
  pari_sp av = avma;
  long i, lx = lg(x);
  GEN s = gen_0;
  for (i=i0; i<lx; i++)
  {
    s = gadd(s, pnormlp(gel(x,i),p,prec));
    if (gc_needed(av,1))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"gnormlp, i = %ld", i);
      s = gerepileupto(av, s);
    }
  }
  return s;
}
/* (||x||_p)^p */
static GEN
pnormlp(GEN x, GEN p, long prec)
{
  switch(typ(x))
  {
    case t_INT: case t_REAL: x = mpabs(x); break;
    case t_FRAC: x = absfrac(x); break;
    case t_COMPLEX: case t_QUAD: x = gabs(x,prec); break;
    case t_POL: return pnormlpvec(2, x, p, prec);
    case t_VEC: case t_COL: case t_MAT: return pnormlpvec(1, x, p, prec);
    default: pari_err_TYPE("gnormlp",x);
  }
  return gpow(x, p, prec);
}

GEN
gnormlp(GEN x, GEN p, long prec)
{
  pari_sp av = avma;
  if (!p || (typ(p) == t_INFINITY && inf_get_sign(p) > 0))
    return gsupnorm(x, prec);
  if (gsigne(p) <= 0) pari_err_DOMAIN("normlp", "p", "<=", gen_0, p);
  if (is_scalar_t(typ(x))) return gabs(x, prec);
  if (typ(p) == t_INT)
  {
    ulong pp = itou_or_0(p);
    switch(pp)
    {
      case 1: return gnorml1(x, prec);
      case 2: x = gnorml2_i(x, prec); break;
      default: x = pnormlp(x, p, prec); break;
    }
    if (pp && typ(x) == t_INT && Z_ispowerall(x, pp, &x))
      return gerepileuptoleaf(av, x);
    if (pp == 2) return gerepileupto(av, gsqrt(x, prec));
  }
  else
    x = pnormlp(x, p, prec);
  x = gpow(x, ginv(p), prec);
  return gerepileupto(av, x);
}

GEN
gnorml1(GEN x,long prec)
{
  pari_sp av = avma;
  long lx,i;
  GEN s;
  switch(typ(x))
  {
    case t_INT: case t_REAL: return mpabs(x);
    case t_FRAC: return absfrac(x);

    case t_COMPLEX: case t_QUAD:
      return gabs(x,prec);

    case t_POL:
      lx = lg(x); s = gen_0;
      for (i=2; i<lx; i++) s = gadd(s, gnorml1(gel(x,i),prec));
      break;

    case t_VEC: case t_COL: case t_MAT:
      lx = lg(x); s = gen_0;
      for (i=1; i<lx; i++) s = gadd(s, gnorml1(gel(x,i),prec));
      break;

    default: pari_err_TYPE("gnorml1",x);
      return NULL; /* LCOV_EXCL_LINE */
  }
  return gerepileupto(av, s);
}
/* As gnorml1, except for t_QUAD and t_COMPLEX: |x + wy| := |x| + |y|
 * Still a norm of R-vector spaces, and can be cheaply computed without
 * square roots */
GEN
gnorml1_fake(GEN x)
{
  pari_sp av = avma;
  long lx, i;
  GEN s;
  switch(typ(x))
  {
    case t_INT: case t_REAL: return mpabs(x);
    case t_FRAC: return absfrac(x);

    case t_COMPLEX:
      s = gadd(gnorml1_fake(gel(x,1)), gnorml1_fake(gel(x,2)));
      break;
    case t_QUAD:
      s = gadd(gnorml1_fake(gel(x,2)), gnorml1_fake(gel(x,3)));
      break;

    case t_POL:
      lx = lg(x); s = gen_0;
      for (i=2; i<lx; i++) s = gadd(s, gnorml1_fake(gel(x,i)));
      break;

    case t_VEC: case t_COL: case t_MAT:
      lx = lg(x); s = gen_0;
      for (i=1; i<lx; i++) s = gadd(s, gnorml1_fake(gel(x,i)));
      break;

    default: pari_err_TYPE("gnorml1_fake",x);
      return NULL; /* LCOV_EXCL_LINE */
  }
  return gerepileupto(av, s);
}

static void
store(GEN z, GEN *m) { if (!*m || gcmp(z, *m) > 0) *m = z; }
/* compare |x| to *m or |x|^2 to *msq, whichever is easiest, and update
 * the pointed value if x is larger */
void
gsupnorm_aux(GEN x, GEN *m, GEN *msq, long prec)
{
  long i, lx;
  GEN z;
  switch(typ(x))
  {
    case t_COMPLEX: z = cxnorm(x); store(z, msq); return;
    case t_QUAD:  z = cxquadnorm(x,prec); store(z, msq); return;
    case t_INT: case t_REAL: z = mpabs(x); store(z,m); return;
    case t_FRAC: z = absfrac(x); store(z,m); return;

    case t_POL: lx = lg(x)-1; x++; break;

    case t_VEC:
    case t_COL:
    case t_MAT: lx = lg(x); break;

    default: pari_err_TYPE("gsupnorm",x);
      return; /* LCOV_EXCL_LINE */
  }
  for (i=1; i<lx; i++) gsupnorm_aux(gel(x,i), m, msq, prec);
}
GEN
gsupnorm(GEN x, long prec)
{
  GEN m = NULL, msq = NULL;
  pari_sp av = avma;
  gsupnorm_aux(x, &m, &msq, prec);
  /* now set m = max (m, sqrt(msq)) */
  if (msq) {
    msq = gsqrt(msq, prec);
    if (!m || gcmp(m, msq) < 0) m = msq;
  } else if (!m) m = gen_0;
  return gerepilecopy(av, m);
}

/*******************************************************************/
/*                                                                 */
/*                            TRACES                               */
/*                                                                 */
/*******************************************************************/
GEN
matcompanion(GEN x)
{
  long n = degpol(x), j;
  GEN y, c;

  if (typ(x)!=t_POL) pari_err_TYPE("matcompanion",x);
  if (!signe(x)) pari_err_DOMAIN("matcompanion","polynomial","=",gen_0,x);
  if (n == 0) return cgetg(1, t_MAT);

  y = cgetg(n+1,t_MAT);
  for (j=1; j < n; j++) gel(y,j) = col_ei(n, j+1);
  c = cgetg(n+1,t_COL); gel(y,n) = c;
  if (gequal1(gel(x, n+2)))
    for (j=1; j<=n; j++) gel(c,j) = gneg(gel(x,j+1));
  else
  { /* not monic. Hardly ever used */
    pari_sp av = avma;
    GEN d = gclone(gneg(gel(x,n+2)));
    avma = av;
    for (j=1; j<=n; j++) gel(c,j) = gdiv(gel(x,j+1), d);
    gunclone(d);
  }
  return y;
}

GEN
gtrace(GEN x)
{
  pari_sp av;
  long i, lx, tx = typ(x);
  GEN y, z;

  switch(tx)
  {
    case t_INT: case t_REAL: case t_FRAC:
      return gmul2n(x,1);

    case t_COMPLEX:
      return gmul2n(gel(x,1),1);

    case t_QUAD:
      y = gel(x,1);
      if (!gequal0(gel(y,3)))
      { /* assume quad. polynomial is either x^2 + d or x^2 - x + d */
        av = avma;
        return gerepileupto(av, gadd(gel(x,3), gmul2n(gel(x,2),1)));
      }
      return gmul2n(gel(x,2),1);

    case t_POL:
      y = cgetg_copy(x, &lx); y[1] = x[1];
      for (i=2; i<lx; i++) gel(y,i) = gtrace(gel(x,i));
      return normalizepol_lg(y, lx);

    case t_SER:
      if (ser_isexactzero(x)) return gcopy(x);
      y = cgetg_copy(x, &lx); y[1] = x[1];
      for (i=2; i<lx; i++) gel(y,i) = gtrace(gel(x,i));
      return normalize(y);

    case t_POLMOD:
      y = gel(x,1); z = gel(x,2);
      if (typ(z) != t_POL || varn(y) != varn(z)) return gmulsg(degpol(y), z);
      av = avma;
      return gerepileupto(av, quicktrace(z, polsym(y, degpol(y)-1)));

    case t_FFELT:
      y=cgetg(3, t_INTMOD);
      gel(y,1) = FF_p(x);
      gel(y,2) = FF_trace(x);
      return y;


    case t_RFRAC:
      av = avma; return gerepileupto(av, gadd(x, conj_i(x)));

    case t_VEC: case t_COL:
      y = cgetg_copy(x, &lx);
      for (i=1; i<lx; i++) gel(y,i) = gtrace(gel(x,i));
      return y;

    case t_MAT:
      lx = lg(x); if (lx == 1) return gen_0;
      /*now lx >= 2*/
      if (lx != lgcols(x)) pari_err_DIM("gtrace");
      av = avma; return gerepileupto(av, mattrace(x));
  }
  pari_err_TYPE("gtrace",x);
  return NULL; /* LCOV_EXCL_LINE */
}

/* Cholesky decomposition for positive definite matrix a
 * [GTM138, Algo 2.7.6, matrix Q]
 * If a is not positive definite return NULL. */
GEN
qfgaussred_positive(GEN a)
{
  pari_sp av = avma;
  GEN b;
  long i,j,k, n = lg(a);

  if (typ(a)!=t_MAT) pari_err_TYPE("qfgaussred_positive",a);
  if (n == 1) return cgetg(1, t_MAT);
  if (lgcols(a)!=n) pari_err_DIM("qfgaussred_positive");
  b = cgetg(n,t_MAT);
  for (j=1; j<n; j++)
  {
    GEN p1=cgetg(n,t_COL), p2=gel(a,j);

    gel(b,j) = p1;
    for (i=1; i<=j; i++) gel(p1,i) = gel(p2,i);
    for (   ; i<n ; i++) gel(p1,i) = gen_0;
  }
  for (k=1; k<n; k++)
  {
    GEN bk, p = gcoeff(b,k,k), invp;
    if (gsigne(p)<=0) { avma = av; return NULL; } /* not positive definite */
    invp = ginv(p);
    bk = row(b, k);
    for (i=k+1; i<n; i++) gcoeff(b,k,i) = gmul(gel(bk,i), invp);
    for (i=k+1; i<n; i++)
    {
      GEN c = gel(bk, i);
      for (j=i; j<n; j++)
        gcoeff(b,i,j) = gsub(gcoeff(b,i,j), gmul(c,gcoeff(b,k,j)));
    }
    if (gc_needed(av,1))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"qfgaussred_positive");
      b=gerepilecopy(av,b);
    }
  }
  return gerepilecopy(av,b);
}

/* Maximal pivot strategy: x is a suitable pivot if it is non zero and either
 * - an exact type, or
 * - it is maximal among remaining non-zero (t_REAL) pivots */
static int
suitable(GEN x, long k, GEN *pp, long *pi)
{
  long t = typ(x);
  switch(t)
  {
    case t_INT: return signe(x) != 0;
    case t_FRAC: return 1;
    case t_REAL: {
      GEN p = *pp;
      if (signe(x) && (!p || abscmprr(p, x) < 0)) { *pp = x; *pi = k; }
      return 0;
    }
    default: return !gequal0(x);
  }
}

/* Gauss reduction (arbitrary symetric matrix, only the part above the
 * diagonal is considered). If signature is non-zero, return only the
 * signature, in which case gsigne() should be defined for elements of a. */
static GEN
gaussred(GEN a, long signature)
{
  GEN r, ak, al;
  pari_sp av, av1;
  long n = lg(a), i, j, k, l, sp, sn, t;

  if (typ(a) != t_MAT) pari_err_TYPE("gaussred",a);
  if (n == 1) return signature? mkvec2(gen_0, gen_0): cgetg(1, t_MAT);
  if (lgcols(a) != n) pari_err_DIM("gaussred");
  n--;

  av = avma;
  r = const_vecsmall(n, 1);
  av1= avma;
  a = RgM_shallowcopy(a);
  t = n; sp = sn = 0;
  while (t)
  {
    long pind = 0;
    GEN invp, p = NULL;
    k=1; while (k<=n && (!r[k] || !suitable(gcoeff(a,k,k), k, &p, &pind))) k++;
    if (k > n && p) k = pind;
    if (k <= n)
    {
      p = gcoeff(a,k,k); invp = ginv(p); /* != 0 */
      if (signature) { /* skip if (!signature): gsigne may fail ! */
        if (gsigne(p) > 0) sp++; else sn++;
      }
      r[k] = 0; t--;
      ak = row(a, k);
      for (i=1; i<=n; i++)
        gcoeff(a,k,i) = r[i]? gmul(gcoeff(a,k,i), invp): gen_0;

      for (i=1; i<=n; i++) if (r[i])
      {
        GEN c = gel(ak,i); /* - p * a[k,i] */
        if (gequal0(c)) continue;
        for (j=1; j<=n; j++) if (r[j])
          gcoeff(a,i,j) = gsub(gcoeff(a,i,j), gmul(c,gcoeff(a,k,j)));
      }
      gcoeff(a,k,k) = p;
      if (gc_needed(av1,1))
      {
        if(DEBUGMEM>1) pari_warn(warnmem,"gaussred (t = %ld)", t);
        a = gerepilecopy(av1, a);
      }
    }
    else
    { /* all remaining diagonal coeffs are currently 0 */
      for (k=1; k<=n; k++) if (r[k])
      {
        l=k+1; while (l<=n && (!r[l] || !suitable(gcoeff(a,k,l), l, &p, &pind))) l++;
        if (l > n && p) l = pind;
        if (l > n) continue;

        p = gcoeff(a,k,l); invp = ginv(p);
        sp++; sn++;
        r[k] = r[l] = 0; t -= 2;
        ak = row(a, k);
        al = row(a, l);
        for (i=1; i<=n; i++) if (r[i])
        {
          gcoeff(a,k,i) = gmul(gcoeff(a,k,i), invp);
          gcoeff(a,l,i) = gmul(gcoeff(a,l,i), invp);
        } else {
          gcoeff(a,k,i) = gen_0;
          gcoeff(a,l,i) = gen_0;
        }

        for (i=1; i<=n; i++) if (r[i])
        { /* c = a[k,i] * p, d = a[l,i] * p; */
          GEN c = gel(ak,i), d = gel(al,i);
          for (j=1; j<=n; j++) if (r[j])
            gcoeff(a,i,j) = gsub(gcoeff(a,i,j),
                                 gadd(gmul(gcoeff(a,l,j), c),
                                      gmul(gcoeff(a,k,j), d)));
        }
        for (i=1; i<=n; i++) if (r[i])
        {
          GEN c = gcoeff(a,k,i), d = gcoeff(a,l,i);
          gcoeff(a,k,i) = gadd(c, d);
          gcoeff(a,l,i) = gsub(c, d);
        }
        gcoeff(a,k,l) = gen_1;
        gcoeff(a,l,k) = gen_m1;
        gcoeff(a,k,k) = gmul2n(p,-1);
        gcoeff(a,l,l) = gneg(gcoeff(a,k,k));
        if (gc_needed(av1,1))
        {
          if(DEBUGMEM>1) pari_warn(warnmem,"gaussred");
          a = gerepilecopy(av1, a);
        }
        break;
      }
      if (k > n) break;
    }
  }
  if (!signature) return gerepilecopy(av, a);
  avma = av; return mkvec2s(sp, sn);
}

GEN
qfgaussred(GEN a) { return gaussred(a,0); }

GEN
qfsign(GEN a) { return gaussred(a,1); }

/* x -= s(y+u*x) */
/* y += s(x-u*y), simultaneously */
static void
rot(GEN x, GEN y, GEN s, GEN u) {
  GEN x1 = subrr(x, mulrr(s,addrr(y,mulrr(u,x))));
  GEN y1 = addrr(y, mulrr(s,subrr(x,mulrr(u,y))));
  affrr(x1,x);
  affrr(y1,y);
}

/* Diagonalization of a REAL symetric matrix. Return a vector [L, r]:
 * L = vector of eigenvalues
 * r = matrix of eigenvectors */
GEN
jacobi(GEN a, long prec)
{
  pari_sp av1;
  long de, e, e1, e2, i, j, p, q, l = lg(a);
  GEN c, ja, L, r, L2, r2, unr;

  if (typ(a) != t_MAT) pari_err_TYPE("jacobi",a);
  ja = cgetg(3,t_VEC);
  L = cgetg(l,t_COL); gel(ja,1) = L;
  r = cgetg(l,t_MAT); gel(ja,2) = r;
  if (l == 1) return ja;
  if (lgcols(a) != l) pari_err_DIM("jacobi");

  e1 = HIGHEXPOBIT-1;
  for (j=1; j<l; j++)
  {
    GEN z = gtofp(gcoeff(a,j,j), prec);
    gel(L,j) = z;
    e = expo(z); if (e < e1) e1 = e;
  }
  for (j=1; j<l; j++)
  {
    gel(r,j) = cgetg(l,t_COL);
    for (i=1; i<l; i++) gcoeff(r,i,j) = utor(i==j? 1: 0, prec);
  }
  av1 = avma;

  e2 = -(long)HIGHEXPOBIT; p = q = 1;
  c = cgetg(l,t_MAT);
  for (j=1; j<l; j++)
  {
    gel(c,j) = cgetg(j,t_COL);
    for (i=1; i<j; i++)
    {
      GEN z = gtofp(gcoeff(a,i,j), prec);
      gcoeff(c,i,j) = z;
      if (!signe(z)) continue;
      e = expo(z); if (e > e2) { e2 = e; p = i; q = j; }
    }
  }
  a = c; unr = real_1(prec);
  de = prec2nbits(prec);

 /* e1 = min expo(a[i,i])
  * e2 = max expo(a[i,j]), i != j */
  while (e1-e2 < de)
  {
    pari_sp av2 = avma;
    GEN x, y, t, c, s, u;
    /* compute attached rotation in the plane formed by basis vectors number
     * p and q */
    x = subrr(gel(L,q),gel(L,p));
    if (signe(x))
    {
      x = divrr(x, shiftr(gcoeff(a,p,q),1));
      y = sqrtr(addrr(unr, sqrr(x)));
      t = invr((signe(x)>0)? addrr(x,y): subrr(x,y));
    }
    else
      y = t = unr;
    c = sqrtr(addrr(unr,sqrr(t)));
    s = divrr(t,c);
    u = divrr(t,addrr(unr,c));

    /* compute successive transforms of a and the matrix of accumulated
     * rotations (r) */
    for (i=1;   i<p; i++) rot(gcoeff(a,i,p), gcoeff(a,i,q), s,u);
    for (i=p+1; i<q; i++) rot(gcoeff(a,p,i), gcoeff(a,i,q), s,u);
    for (i=q+1; i<l; i++) rot(gcoeff(a,p,i), gcoeff(a,q,i), s,u);
    y = gcoeff(a,p,q);
    t = mulrr(t, y); shiftr_inplace(y, -de - 1);
    x = gel(L,p); subrrz(x,t, x);
    y = gel(L,q); addrrz(y,t, y);
    for (i=1; i<l; i++) rot(gcoeff(r,i,p), gcoeff(r,i,q), s,u);

    e2 = -(long)HIGHEXPOBIT; p = q = 1;
    for (j=1; j<l; j++)
    {
      for (i=1; i<j; i++)
      {
        GEN z = gcoeff(a,i,j);
        if (!signe(z)) continue;
        e = expo(z); if (e > e2) { e2=e; p=i; q=j; }
      }
      for (i=j+1; i<l; i++)
      {
        GEN z = gcoeff(a,j,i);
        if (!signe(z)) continue;
        e = expo(z); if (e > e2) { e2=e; p=j; q=i; }
      }
    }
    avma = av2;
  }
  /* sort eigenvalues from smallest to largest */
  c = indexsort(L);
  r2 = vecpermute(r, c); for (i=1; i<l; i++) gel(r,i) = gel(r2,i);
  L2 = vecpermute(L, c); for (i=1; i<l; i++) gel(L,i) = gel(L2,i);
  avma = av1; return ja;
}

/*************************************************************************/
/**                                                                     **/
/**                   Q-vector space -> Z-modules                       **/
/**                                                                     **/
/*************************************************************************/

GEN
matrixqz0(GEN x,GEN p)
{
  if (typ(x) != t_MAT) pari_err_TYPE("matrixqz",x);
  if (!p) return QM_minors_coprime(x,NULL);
  if (typ(p) != t_INT) pari_err_TYPE("matrixqz",p);
  if (signe(p)>=0) return QM_minors_coprime(x,p);
  if (!RgM_is_QM(x)) pari_err_TYPE("matrixqz", x);
  if (absequaliu(p,1)) return QM_ImZ_hnf(x); /* p = -1 */
  if (absequaliu(p,2)) return QM_ImQ_hnf(x); /* p = -2 */
  pari_err_FLAG("QM_minors_coprime");
  return NULL; /* LCOV_EXCL_LINE */
}

GEN
QM_minors_coprime(GEN x, GEN D)
{
  pari_sp av = avma, av1;
  long i, j, m, n, lP;
  GEN P, y;

  n = lg(x)-1; if (!n) return gcopy(x);
  m = nbrows(x);
  if (n > m) pari_err_DOMAIN("QM_minors_coprime","n",">",strtoGENstr("m"),x);
  y = x; x = cgetg(n+1,t_MAT);
  for (j=1; j<=n; j++)
  {
    gel(x,j) = Q_primpart(gel(y,j));
    RgV_check_ZV(gel(x,j), "QM_minors_coprime");
  }
  /* x now a ZM */
  if (n==m)
  {
    if (gequal0(ZM_det(x)))
      pari_err_DOMAIN("QM_minors_coprime", "rank(A)", "<",stoi(n),x);
    avma = av; return matid(n);
  }
  /* m > n */
  if (!D || gequal0(D))
  {
    pari_sp av2 = avma;
    D = ZM_detmult(shallowtrans(x));
    if (is_pm1(D)) { avma = av2; return ZM_copy(x); }
  }
  P = gel(Z_factor(D), 1); lP = lg(P);
  av1 = avma;
  for (i=1; i < lP; i++)
  {
    GEN p = gel(P,i), pov2 = shifti(p, -1);
    for(;;)
    {
      GEN N, M = FpM_ker(x, p);
      long lM = lg(M);
      if (lM==1) break;

      FpM_center_inplace(M, p, pov2);
      N = ZM_Z_divexact(ZM_mul(x,M), p);
      for (j=1; j<lM; j++)
      {
        long k = n; while (!signe(gcoeff(M,k,j))) k--;
        gel(x,k) = gel(N,j);
      }
      if (gc_needed(av1,1))
      {
        if (DEBUGMEM>1) pari_warn(warnmem,"QM_minors_coprime, p = %Ps", p);
        x = gerepilecopy(av1, x); pov2 = shifti(p, -1);
      }
    }
  }
  return gerepilecopy(av, x);
}

static GEN
QM_ImZ_hnfall_i(GEN A, GEN *U, long remove)
{
  GEN V = NULL, D;
  A = Q_remove_denom(A,&D);
  if (D)
  {
    long l, lA;
    V = matkermod(A,D,NULL);
    l = lg(V); lA = lg(A);
    if (l == 1) V = scalarmat_shallow(D, lA-1);
    else
    {
      if (l < lA) V = hnfmodid(V,D);
      A = ZM_Z_divexact(ZM_mul(A, V), D);
    }
  }
  A = ZM_hnflll(A, U, remove);
  if (U && V) *U = ZM_mul(V,*U);
  return A;
}
GEN
QM_ImZ_hnfall(GEN x, GEN *U, long remove)
{
  pari_sp av = avma;
  x = QM_ImZ_hnfall_i(x, U, remove);
  if (U) gerepileall(av, 2, &x, &U); else x = gerepileupto(av, x);
  return x;
}
GEN
QM_ImZ_hnf(GEN x) { return QM_ImZ_hnfall(x, NULL, 1); }

GEN
QM_ImQ_hnfall(GEN x, GEN *U, long remove)
{
  pari_sp av = avma, av1;
  long k, r, m, n = lg(x);
  GEN c, V;

  if (U) *U = matid(n-1);
  if (n==1) return gcopy(x);
  m = lgcols(x); x = RgM_shallowcopy(x);
  c = zero_zv(n-1); r = 1;
  av1 = avma;
  for (k = 1; k < m; k++)
  {
    long j = 1, a;
    GEN p;
    while (j<n && (c[j] || isintzero(gcoeff(x,k,j)))) j++;
    if (j==n) continue;

    c[j]=k; p = gcoeff(x,k,j);
    gel(x,j) = RgC_Rg_div(gel(x,j), p);
    if (U) gel(*U,j) = RgC_Rg_div(gel(*U,j), p);
    for (a = 1; a < n; a++)
      if (a != j)
      {
        GEN t = gcoeff(x,k,a);
        if (gequal0(t)) continue;
        if (U) gel(*U,a) = RgC_sub(gel(*U,a), RgC_Rg_mul(gel(*U,j),t));
        gel(x,a) = RgC_sub(gel(x,a), RgC_Rg_mul(gel(x,j),t));
      }
    if (++r == n) break;
    if (gc_needed(av1,1))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"QM_ImQ_hnf");
      gerepileall(av1, U? 2: 1, &x, U);
    }
  }
  x = QM_ImZ_hnfall_i(x, U? &V: NULL, remove);
  if (U) { *U = RgM_mul(*U,V); gerepileall(av,2,&x,U); }
  else x = gerepileupto(av,x);
  return x;
}
GEN
QM_ImQ_hnf(GEN x) { return QM_ImQ_hnfall(x, NULL, 1); }

GEN
intersect(GEN x, GEN y)
{
  long j, lx = lg(x);
  pari_sp av;
  GEN z;

  if (typ(x)!=t_MAT) pari_err_TYPE("intersect",x);
  if (typ(y)!=t_MAT) pari_err_TYPE("intersect",y);
  if (lx==1 || lg(y)==1) return cgetg(1,t_MAT);

  av = avma; z = ker(shallowconcat(x,y));
  for (j=lg(z)-1; j; j--) setlg(z[j], lx);
  return gerepileupto(av, image(RgM_mul(x,z)));
}
