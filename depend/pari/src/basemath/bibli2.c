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

/*******************************************************************/
/**                                                               **/
/**                      SPECIAL POLYNOMIALS                      **/
/**                                                               **/
/*******************************************************************/
/* Tchebichev polynomial: T0=1; T1=X; T(n)=2*X*T(n-1)-T(n-2)
 * T(n) = (n/2) sum_{k=0}^{n/2} a_k x^(n-2k)
 *   where a_k = (-1)^k 2^(n-2k) (n-k-1)! / k!(n-2k)! is an integer
 *   and a_0 = 2^(n-1), a_k / a_{k-1} = - (n-2k+2)(n-2k+1) / 4k(n-k) */
GEN
polchebyshev1(long n, long v) /* Assume 4*n < LONG_MAX */
{
  long k, l;
  pari_sp av;
  GEN q,a,r;

  if (v<0) v = 0;
  /* polchebyshev(-n,1) = polchebyshev(n,1) */
  if (n < 0) n = -n;
  if (n==0) return pol_1(v);
  if (n==1) return pol_x(v);

  q = cgetg(n+3, t_POL); r = q + n+2;
  a = int2n(n-1);
  gel(r--,0) = a;
  gel(r--,0) = gen_0;
  for (k=1,l=n; l>1; k++,l-=2)
  {
    av = avma;
    a = diviuuexact(muluui(l, l-1, a), 4*k, n-k);
    togglesign(a); a = gerepileuptoint(av, a);
    gel(r--,0) = a;
    gel(r--,0) = gen_0;
  }
  q[1] = evalsigne(1) | evalvarn(v);
  return q;
}
static void
polchebyshev1_eval_aux(long n, GEN x, GEN *pt1, GEN *pt2)
{
  GEN t1, t2, b;
  if (n == 1) { *pt1 = gen_1; *pt2 = x; return; }
  if (n == 0) { *pt1 = x; *pt2 = gen_1; return; }
  polchebyshev1_eval_aux((n+1) >> 1, x, &t1, &t2);
  b = gsub(gmul(gmul2n(t1,1), t2), x);
  if (odd(n)) { *pt1 = gadd(gmul2n(gsqr(t1), 1), gen_m1); *pt2 = b; }
  else        { *pt1 = b; *pt2 = gadd(gmul2n(gsqr(t2), 1), gen_m1); }
}
static GEN
polchebyshev1_eval(long n, GEN x)
{
  GEN t1, t2;
  long i, v;
  pari_sp av;

  if (n < 0) n = -n;
  if (n==0) return gen_1;
  if (n==1) return gcopy(x);
  av = avma;
  v = u_lvalrem(n, 2, (ulong*)&n);
  polchebyshev1_eval_aux((n+1)>>1, x, &t1, &t2);
  if (n != 1) t2 = gsub(gmul(gmul2n(t1,1), t2), x);
  for (i = 1; i <= v; i++) t2 = gadd(gmul2n(gsqr(t2), 1), gen_m1);
  return gerepileupto(av, t2);
}

/* Chebychev  polynomial of the second kind U(n,x): the coefficient in front of
 * x^(n-2*m) is (-1)^m * 2^(n-2m)*(n-m)!/m!/(n-2m)!  for m=0,1,...,n/2 */
GEN
polchebyshev2(long n, long v)
{
  pari_sp av;
  GEN q, a, r;
  long m;
  int neg = 0;

  if (v<0) v = 0;
  /* polchebyshev(-n,2) = -polchebyshev(n-2,2) */
  if (n < 0) {
    if (n == -1) return zeropol(v);
    neg = 1; n = -n-2;
  }
  if (n==0) return neg ? scalar_ZX_shallow(gen_m1, v): pol_1(v);

  q = cgetg(n+3, t_POL); r = q + n+2;
  a = int2n(n);
  if (neg) togglesign(a);
  gel(r--,0) = a;
  gel(r--,0) = gen_0;
  for (m=1; 2*m<= n; m++)
  {
    av = avma;
    a = diviuuexact(muluui(n-2*m+2, n-2*m+1, a), 4*m, n-m+1);
    togglesign(a); a = gerepileuptoint(av, a);
    gel(r--,0) = a;
    gel(r--,0) = gen_0;
  }
  q[1] = evalsigne(1) | evalvarn(v);
  return q;
}
static void
polchebyshev2_eval_aux(long n, GEN x, GEN *pu1, GEN *pu2)
{
  GEN u1, u2, u, mu1;
  if (n == 1) { *pu1 = gen_1; *pu2 = gmul2n(x,1); return; }
  if (n == 0) { *pu1 = gen_0; *pu2 = gen_1; return; }
  polchebyshev2_eval_aux(n >> 1, x, &u1, &u2);
  mu1 = gneg(u1);
  u = gmul(gadd(u2,u1), gadd(u2,mu1));
  if (odd(n)) { *pu1 = u; *pu2 = gmul(gmul2n(u2,1), gadd(gmul(x,u2), mu1)); }
  else        { *pu2 = u; *pu1 = gmul(gmul2n(u1,1), gadd(u2, gmul(x,mu1))); }
}
static GEN
polchebyshev2_eval(long n, GEN x)
{
  GEN u1, u2, mu1;
  long neg = 0;
  pari_sp av;

  if (n < 0) {
    if (n == -1) return gen_0;
    neg = 1; n = -n-2;
  }
  if (n==0) return neg ? gen_m1: gen_1;
  av = avma;
  polchebyshev2_eval_aux(n>>1, x, &u1, &u2);
  mu1 = gneg(u1);
  if (odd(n)) u2 = gmul(gmul2n(u2,1), gadd(gmul(x,u2), mu1));
  else        u2 = gmul(gadd(u2,u1), gadd(u2,mu1));
  if (neg) u2 = gneg(u2);
  return gerepileupto(av, u2);
}

GEN
polchebyshev(long n, long kind, long v)
{
  switch (kind)
  {
    case 1: return polchebyshev1(n, v);
    case 2: return polchebyshev2(n, v);
    default: pari_err_FLAG("polchebyshev");
  }
  return NULL; /* LCOV_EXCL_LINE */
}
GEN
polchebyshev_eval(long n, long kind, GEN x)
{
  if (!x) return polchebyshev(n, kind, 0);
  if (gequalX(x)) return polchebyshev(n, kind, varn(x));
  switch (kind)
  {
    case 1: return polchebyshev1_eval(n, x);
    case 2: return polchebyshev2_eval(n, x);
    default: pari_err_FLAG("polchebyshev");
  }
  return NULL; /* LCOV_EXCL_LINE */
}

/* Hermite polynomial H(n,x):  H(n+1) = 2x H(n) - 2n H(n-1)
 * The coefficient in front of x^(n-2*m) is
 * (-1)^m * n! * 2^(n-2m)/m!/(n-2m)!  for m=0,1,...,n/2.. */
GEN
polhermite(long n, long v)
{
  long m;
  pari_sp av;
  GEN q,a,r;

  if (v<0) v = 0;
  if (n < 0) pari_err_DOMAIN("polhermite", "degree", "<", gen_0, stoi(n));
  if (n==0) return pol_1(v);

  q = cgetg(n+3, t_POL); r = q + n+2;
  a = int2n(n);
  gel(r--,0) = a;
  gel(r--,0) = gen_0;
  for (m=1; 2*m<= n; m++)
  {
    av = avma;
    a = diviuexact(muluui(n-2*m+2, n-2*m+1, a), 4*m);
    togglesign(a);
    gel(r--,0) = a = gerepileuptoint(av, a);
    gel(r--,0) = gen_0;
  }
  q[1] = evalsigne(1) | evalvarn(v);
  return q;
}
GEN
polhermite_eval(long n, GEN x)
{
  long i;
  pari_sp av, av2;
  GEN x2, u, v;

  if (!x) return polhermite(n, 0);
  if (gequalX(x)) return polhermite(n, varn(x));
  if (n==0) return gen_1;
  if (n==1) return gmul2n(x,1);
  av = avma; x2 = gmul2n(x,1); v = gen_1; u = x2;
  av2= avma;
  for (i=1; i<n; i++)
  { /* u = H_i(x), v = H_{i-1}(x), compute t = H_{i+1}(x) */
    GEN t;
    if ((i & 0xff) == 0) gerepileall(av2,2,&u, &v);
    t = gsub(gmul(x2, u), gmulsg(2*i,v));
    v = u; u = t;
  }
  return gerepileupto(av, u);
}

/* Legendre polynomial
 * L0=1; L1=X; (n+1)*L(n+1)=(2*n+1)*X*L(n)-n*L(n-1)
 * L(n) = 2^-n sum_{k=0}^{n/2} a_k x^(n-2k)
 *   where a_k = (-1)^k (2n-2k)! / k! (n-k)! (n-2k)! is an integer
 *   and a_0 = binom(2n,n), a_k / a_{k-1} = - (n-2k+1)(n-2k+2) / 2k (2n-2k+1) */
GEN
pollegendre(long n, long v)
{
  long k, l;
  pari_sp av;
  GEN a, r, q;

  if (v<0) v = 0;
  /* pollegendre(-n) = pollegendre(n-1) */
  if (n < 0) n = -n-1;
  if (n==0) return pol_1(v);
  if (n==1) return pol_x(v);

  av = avma;
  q = cgetg(n+3, t_POL); r = q + n+2;
  gel(r--,0) = a = binomialuu(n<<1,n);
  gel(r--,0) = gen_0;
  for (k=1,l=n; l>1; k++,l-=2)
  { /* l = n-2*k+2 */
    av = avma;
    a = diviuuexact(muluui(l, l-1, a), 2*k, n+l-1);
    togglesign(a); a = gerepileuptoint(av, a);
    gel(r--,0) = a;
    gel(r--,0) = gen_0;
  }
  q[1] = evalsigne(1) | evalvarn(v);
  return gerepileupto(av, gmul2n(q,-n));
}

GEN
pollegendre_eval(long n, GEN x)
{
  long i;
  pari_sp av;
  GEN u, v;

  if (!x) return pollegendre(n, 0);
  if (gequalX(x)) return pollegendre(n, varn(x));
  /* pollegendre(-n) = pollegendre(n-1) */
  if (n < 0) n = -n-1;
  if (n==0) return gen_1;
  if (n==1) return gcopy(x);
  av = avma; v = gen_1; u = x;
  for (i=1; i<n; i++)
  { /* u = P_i(x), v = P_{i-1}(x), compute t = P_{i+1}(x) */
    GEN t;
    if ((i & 0xff) == 0) gerepileall(av,2,&u, &v);
    t = gdivgs(gsub(gmul(gmulsg(2*i+1,x), u), gmulsg(i,v)), i+1);
    v = u; u = t;
  }
  return gerepileupto(av, u);
}

/* polcyclo(p) = X^(p-1) + ... + 1 */
static GEN
polcyclo_prime(long p, long v)
{
  GEN T = cgetg(p+2, t_POL);
  long i;
  T[1] = evalsigne(1) | evalvarn(v);
  for (i = 2; i < p+2; i++) gel(T,i) = gen_1;
  return T;
}

/* cyclotomic polynomial */
GEN
polcyclo(long n, long v)
{
  long s, q, i, l;
  pari_sp av=avma;
  GEN T, P;

  if (v<0) v = 0;
  if (n < 3)
    switch(n)
    {
      case 1: return deg1pol_shallow(gen_1, gen_m1, v);
      case 2: return deg1pol_shallow(gen_1, gen_1, v);
      default: pari_err_DOMAIN("polcyclo", "index", "<=", gen_0, stoi(n));
    }
  P = gel(factoru(n), 1); l = lg(P);
  s = P[1]; T = polcyclo_prime(s, v);
  for (i = 2; i < l; i++)
  { /* Phi_{np}(X) = Phi_n(X^p) / Phi_n(X) */
    s *= P[i];
    T = RgX_div(RgX_inflate(T, P[i]), T);
  }
  /* s = squarefree part of n */
  q = n / s;
  if (q == 1) return gerepileupto(av, T);
  return gerepilecopy(av, RgX_inflate(T,q));
}

/* cyclotomic polynomial */
GEN
polcyclo_eval(long n, GEN x)
{
  pari_sp av= avma;
  GEN P, md, xd, yneg, ypos;
  long l, s, i, j, q, tx;
  long root_of_1 = 0;

  if (!x) return polcyclo(n, 0);
  tx = typ(x);
  if (gequalX(x)) return polcyclo(n, varn(x));
  if (n <= 0) pari_err_DOMAIN("polcyclo", "index", "<=", gen_0, stoi(n));
  if (n == 1) return gsubgs(x, 1);
  if (tx == t_INT && !signe(x)) return gen_1;
  while ((n & 3) == 0) { n >>= 1; x = gsqr(x); } /* Phi_4n(x) = Phi_2n(x^2) */
  /* n not divisible by 4 */
  if (n == 2) return gerepileupto(av, gaddgs(x,1));
  if (!odd(n)) { n >>= 1; x = gneg(x); } /* Phi_2n(x) = Phi_n(-x) for n>1 odd */
  /* n odd > 2.  s largest squarefree divisor of n */
  P = gel(factoru(n), 1); s = zv_prod(P);
  /* replace n by largest squarefree divisor */
  q = n/s; if (q != 1) { x = gpowgs(x, q); n = s; }
  l = lg(P)-1;
  /* n squarefree odd > 2, l distinct prime divisors. Now handle x = 1 or -1 */
  if (tx == t_INT) { /* shortcut */
    if (is_pm1(x))
    {
      avma = av;
      if (signe(x) > 0 && l == 1) return utoipos(P[1]);
      return gen_1;
    }
  } else {
    if (gequal1(x))
    { /* n is prime, return n; multiply by x to keep the type */
      if (l == 1) return gerepileupto(av, gmulgs(x,n));
      return gerepilecopy(av, x); /* else 1 */
    }
    if (gequalm1(x)) return gerepileupto(av, gneg(x)); /* -1 */
  }
  /* Heuristic: evaluation will probably not improve things */
  if (tx == t_POL || tx == t_MAT || lg(x) > n)
    return gerepileupto(av, poleval(polcyclo(n,0), x));

  xd = cgetg((1L<<l) + 1, t_VEC); /* the x^d, where d | n */
  md = cgetg((1L<<l) + 1, t_VECSMALL); /* the mu(d), where d | n */
  gel(xd, 1) = x;
  md[1] = 1;
  /* Use Phi_n(x) = Prod_{d|n} (x^d-1)^mu(n/d).
   * If x has exact order D, n = Dq, then the result is 0 if q = 1. Otherwise
   * the factors with x^d-1, D|d are omitted and we multiply at the end by
   *   prod_{d | q} d^mu(q/d) = q if prime, 1 otherwise */
  /* We store the factors with mu(d)= 1 (resp.-1) in ypos (resp yneg).
   * At the end we return ypos/yneg if mu(n)=1 and yneg/ypos if mu(n)=-1 */
  ypos = gsubgs(x,1);
  yneg = gen_1;
  for (i = 1; i <= l; i++)
  {
    long ti = 1L<<(i-1), p = P[i];
    for (j = 1; j <= ti; j++) {
      GEN X = gpowgs(gel(xd,j), p), t = gsubgs(X,1);
      gel(xd,ti+j) = X;
      md[ti+j] = -md[j];
      if (gequal0(t))
      { /* x^d = 1; root_of_1 := the smallest index ti+j such that X == 1
        * (whose bits code d: bit i-1 is set iff P[i] | d). If no such index
        * exists, then root_of_1 remains 0. Do not multiply with X-1 if X = 1,
        * we handle these factors at the end */
        if (!root_of_1) root_of_1 = ti+j;
      }
      else
      {
        if (md[ti+j] == 1) ypos = gmul(ypos, t);
        else               yneg = gmul(yneg, t);
      }
    }
  }
  ypos = odd(l)? gdiv(yneg,ypos): gdiv(ypos,yneg);
  if (root_of_1)
  {
    GEN X = gel(xd,(1<<l)); /* = x^n = 1 */
    long bitmask_q = (1<<l) - root_of_1;
    /* bitmask_q encodes q = n/d: bit (i-1) is 1 iff P[i] | q */

    /* x is a root of unity.  If bitmask_q = 0, then x was a primitive n-th
     * root of 1 and the result is zero. Return X - 1 to preserve type. */
    if (!bitmask_q) return gerepileupto(av, gsubgs(X, 1));
    /* x is a primitive d-th root of unity, where d|n and d<n: we
     * must multiply ypos by if(isprime(n/d), n/d, 1) */
    ypos = gmul(ypos, X); /* multiply by X = 1 to preserve type */
    /* If bitmask_q = 1<<(i-1) for some i <= l, then q == P[i] and we multiply
     * by P[i]; otherwise q is composite and nothing more needs to be done */
    if (!(bitmask_q & (bitmask_q-1))) /* detects power of 2, since bitmask!=0 */
    {
      i = vals(bitmask_q)+1; /* q = P[i] */
      ypos = gmulgs(ypos, P[i]);
    }
  }
  return gerepileupto(av, ypos);
}
/********************************************************************/
/**                                                                **/
/**                  HILBERT & PASCAL MATRICES                     **/
/**                                                                **/
/********************************************************************/
GEN
mathilbert(long n) /* Hilbert matrix of order n */
{
  long i,j;
  GEN p;

  if (n < 0) pari_err_DOMAIN("mathilbert", "dimension", "<", gen_0, stoi(n));
  p = cgetg(n+1,t_MAT);
  for (j=1; j<=n; j++)
  {
    gel(p,j) = cgetg(n+1,t_COL);
    for (i=1+(j==1); i<=n; i++)
      gcoeff(p,i,j) = mkfrac(gen_1, utoipos(i+j-1));
  }
  if (n) gcoeff(p,1,1) = gen_1;
  return p;
}

/* q-Pascal triangle = (choose(i,j)_q) (ordinary binomial if q = NULL) */
GEN
matqpascal(long n, GEN q)
{
  long i, j, I;
  pari_sp av = avma;
  GEN m, qpow = NULL; /* gcc -Wall */

  if (n < -1)  pari_err_DOMAIN("matpascal", "n", "<", gen_m1, stoi(n));
  n++; m = cgetg(n+1,t_MAT);
  for (j=1; j<=n; j++) gel(m,j) = cgetg(n+1,t_COL);
  if (q)
  {
    I = (n+1)/2;
    if (I > 1) { qpow = new_chunk(I+1); gel(qpow,2)=q; }
    for (j=3; j<=I; j++) gel(qpow,j) = gmul(q, gel(qpow,j-1));
  }
  for (i=1; i<=n; i++)
  {
    I = (i+1)/2; gcoeff(m,i,1)= gen_1;
    if (q)
    {
      for (j=2; j<=I; j++)
        gcoeff(m,i,j) = gadd(gmul(gel(qpow,j),gcoeff(m,i-1,j)),
                             gcoeff(m,i-1,j-1));
    }
    else
    {
      for (j=2; j<=I; j++)
        gcoeff(m,i,j) = addii(gcoeff(m,i-1,j), gcoeff(m,i-1,j-1));
    }
    for (   ; j<=i; j++) gcoeff(m,i,j) = gcoeff(m,i,i+1-j);
    for (   ; j<=n; j++) gcoeff(m,i,j) = gen_0;
  }
  return gerepilecopy(av, m);
}

/******************************************************************/
/**                                                              **/
/**                       PRECISION CHANGES                      **/
/**                                                              **/
/******************************************************************/

GEN
gprec(GEN x, long d)
{
  pari_sp av = avma;
  if (d <= 0) pari_err_DOMAIN("gprec", "precision", "<=", gen_0, stoi(d));
  return gerepilecopy(av, gprec_w(x, ndec2prec(d)));
}

/* not GC-safe; precision given in word length (including codewords) */
GEN
gprec_w(GEN x, long pr)
{
  long lx, i;
  GEN y;

  switch(typ(x))
  {
    case t_REAL:
      if (signe(x)) return realprec(x) != pr? rtor(x,pr): x;
      i = -prec2nbits(pr);
      if (i < expo(x)) return real_0_bit(i);
      y = cgetr(2); y[1] = x[1]; return y;
    case t_COMPLEX:
      y = cgetg(3, t_COMPLEX);
      gel(y,1) = gprec_w(gel(x,1),pr);
      gel(y,2) = gprec_w(gel(x,2),pr);
      break;
   case t_POL: case t_SER:
      y = cgetg_copy(x, &lx); y[1] = x[1];
      for (i=2; i<lx; i++) gel(y,i) = gprec_w(gel(x,i),pr);
      break;
    case t_POLMOD: case t_RFRAC: case t_VEC: case t_COL: case t_MAT:
      y = cgetg_copy(x, &lx);
      for (i=1; i<lx; i++) gel(y,i) = gprec_w(gel(x,i),pr);
      break;
    default: return x;
  }
  return y;
}
/* not GC-safe; precision given in word length (including codewords) */
GEN
gprec_wensure(GEN x, long pr)
{
  long lx, i;
  GEN y;

  switch(typ(x))
  {
    case t_REAL:
      if (signe(x)) return realprec(x) < pr? rtor(x,pr): x;
      i = -prec2nbits(pr);
      if (i < expo(x)) return real_0_bit(i);
      y = cgetr(2); y[1] = x[1]; return y;
    case t_COMPLEX:
      y = cgetg(3, t_COMPLEX);
      gel(y,1) = gprec_wensure(gel(x,1),pr);
      gel(y,2) = gprec_wensure(gel(x,2),pr);
      break;
   case t_POL: case t_SER:
      y = cgetg_copy(x, &lx); y[1] = x[1];
      for (i=2; i<lx; i++) gel(y,i) = gprec_wensure(gel(x,i),pr);
      break;
    case t_POLMOD: case t_RFRAC: case t_VEC: case t_COL: case t_MAT:
      y = cgetg_copy(x, &lx);
      for (i=1; i<lx; i++) gel(y,i) = gprec_wensure(gel(x,i),pr);
      break;
    default: return x;
  }
  return y;
}

/* not GC-safe; precision given in word length (including codewords),
 * truncate mantissa to precision 'pr' but never increase it */
GEN
gprec_wtrunc(GEN x, long pr)
{
  long lx, i;
  GEN y;

  switch(typ(x))
  {
    case t_REAL:
      return (signe(x) && realprec(x) > pr)? rtor(x,pr): x;
    case t_COMPLEX:
      y = cgetg(3, t_COMPLEX);
      gel(y,1) = gprec_wtrunc(gel(x,1),pr);
      gel(y,2) = gprec_wtrunc(gel(x,2),pr);
      break;
    case t_POL:
    case t_SER:
      y = cgetg_copy(x, &lx); y[1] = x[1];
      for (i=2; i<lx; i++) gel(y,i) = gprec_wtrunc(gel(x,i),pr);
      break;
    case t_POLMOD: case t_RFRAC: case t_VEC: case t_COL: case t_MAT:
      y = cgetg_copy(x, &lx);
      for (i=1; i<lx; i++) gel(y,i) = gprec_wtrunc(gel(x,i),pr);
      break;
    default: return x;
  }
  return y;
}

/********************************************************************/
/**                                                                **/
/**                      SERIES TRANSFORMS                         **/
/**                                                                **/
/********************************************************************/
/**                  LAPLACE TRANSFORM (OF A SERIES)               **/
/********************************************************************/
static GEN
serlaplace(GEN x)
{
  long i, l = lg(x), e = valp(x);
  GEN t, y = cgetg(l,t_SER);
  if (e < 0) pari_err_DOMAIN("laplace","valuation","<",gen_0,stoi(e));
  t = mpfact(e); y[1] = x[1];
  for (i=2; i<l; i++)
  {
    gel(y,i) = gmul(t, gel(x,i));
    e++; t = mului(e,t);
  }
  return y;
}
static GEN
pollaplace(GEN x)
{
  long i, e = 0, l = lg(x);
  GEN t = gen_1, y = cgetg(l,t_POL);
  y[1] = x[1];
  for (i=2; i<l; i++)
  {
    gel(y,i) = gmul(t, gel(x,i));
    e++; t = mului(e,t);
  }
  return y;
}
GEN
laplace(GEN x)
{
  pari_sp av = avma;
  switch(typ(x))
  {
    case t_POL: x = pollaplace(x); break;
    case t_SER: x = serlaplace(x); break;
    default: pari_err_TYPE("laplace",x);
  }
  return gerepilecopy(av, x);
}

/********************************************************************/
/**              CONVOLUTION PRODUCT (OF TWO SERIES)               **/
/********************************************************************/
GEN
convol(GEN x, GEN y)
{
  long j, lx, ly, ex, ey, vx = varn(x);
  GEN z;

  if (typ(x) != t_SER) pari_err_TYPE("convol",x);
  if (typ(y) != t_SER) pari_err_TYPE("convol",y);
  if (varn(y) != vx) pari_err_VAR("convol", x,y);
  ex = valp(x);
  ey = valp(y);
  if (ser_isexactzero(x))
    return scalarser(gadd(Rg_get_0(x), Rg_get_0(y)), varn(x), maxss(ex,ey));
  lx = lg(x) + ex; x -= ex;
  ly = lg(y) + ey; y -= ey;
  /* inputs shifted: x[i] and y[i] now correspond to monomials of same degree */
  if (ly < lx) lx = ly; /* min length */
  if (ex < ey) ex = ey; /* max valuation */
  if (lx - ex < 3) return zeroser(vx, lx-2);

  z = cgetg(lx - ex, t_SER);
  z[1] = evalvalp(ex) | evalvarn(vx);
  for (j = ex+2; j<lx; j++) gel(z,j-ex) = gmul(gel(x,j),gel(y,j));
  return normalize(z);
}

/***********************************************************************/
/*               OPERATIONS ON DIRICHLET SERIES: *, /                  */
/* (+, -, scalar multiplication are done on the corresponding vectors) */
/***********************************************************************/
static long
dirval(GEN x)
{
  long i = 1, lx = lg(x);
  while (i < lx && gequal0(gel(x,i))) i++;
  return i;
}

GEN
dirmul(GEN x, GEN y)
{
  pari_sp av = avma, av2;
  long nx, ny, nz, dx, dy, i, j, k;
  GEN z;

  if (typ(x)!=t_VEC) pari_err_TYPE("dirmul",x);
  if (typ(y)!=t_VEC) pari_err_TYPE("dirmul",y);
  dx = dirval(x); nx = lg(x)-1;
  dy = dirval(y); ny = lg(y)-1;
  if (ny-dy < nx-dx) { swap(x,y); lswap(nx,ny); lswap(dx,dy); }
  nz = minss(nx*dy,ny*dx);
  y = RgV_kill0(y);
  av2 = avma;
  z = zerovec(nz);
  for (j=dx; j<=nx; j++)
  {
    GEN c = gel(x,j);
    if (gequal0(c)) continue;
    if (gequal1(c))
    {
      for (k=dy,i=j*dy; i<=nz; i+=j,k++)
        if (gel(y,k)) gel(z,i) = gadd(gel(z,i),gel(y,k));
    }
    else if (gequalm1(c))
    {
      for (k=dy,i=j*dy; i<=nz; i+=j,k++)
        if (gel(y,k)) gel(z,i) = gsub(gel(z,i),gel(y,k));
    }
    else
    {
      for (k=dy,i=j*dy; i<=nz; i+=j,k++)
        if (gel(y,k)) gel(z,i) = gadd(gel(z,i),gmul(c,gel(y,k)));
    }
    if (gc_needed(av2,3))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"dirmul, %ld/%ld",j,nx);
      z = gerepilecopy(av2,z);
    }
  }
  return gerepilecopy(av,z);
}

GEN
dirdiv(GEN x, GEN y)
{
  pari_sp av = avma, av2;
  long nx,ny,nz, dx,dy, i,j,k;
  GEN p1;

  if (typ(x)!=t_VEC) pari_err_TYPE("dirdiv",x);
  if (typ(y)!=t_VEC) pari_err_TYPE("dirdiv",y);
  dx = dirval(x); nx = lg(x)-1;
  dy = dirval(y); ny = lg(y)-1;
  if (dy != 1 || !ny) pari_err_INV("dirdiv",y);
  nz = minss(nx,ny*dx);
  p1 = gel(y,1);
  if (gequal1(p1)) p1 = NULL; else y = gdiv(y,p1);
  y = RgV_kill0(y);
  av2 = avma;
  x = p1 ? gdiv(x,p1): leafcopy(x);
  for (j=1; j<dx; j++) gel(x,j) = gen_0;
  setlg(x,nz+1);
  for (j=dx; j<=nz; j++)
  {
    GEN c = gel(x,j);
    if (gequal0(c)) continue;
    if (gequal1(c))
    {
      for (i=j+j,k=2; i<=nz; i+=j,k++)
        if (gel(y,k)) gel(x,i) = gsub(gel(x,i),gel(y,k));
    }
    else if (gequalm1(c))
    {
      for (i=j+j,k=2; i<=nz; i+=j,k++)
        if (gel(y,k)) gel(x,i) = gadd(gel(x,i),gel(y,k));
    }
    else
    {
      for (i=j+j,k=2; i<=nz; i+=j,k++)
        if (gel(y,k)) gel(x,i) = gsub(gel(x,i),gmul(c,gel(y,k)));
    }
    if (gc_needed(av2,3))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"dirdiv, %ld/%ld",j,nz);
      x = gerepilecopy(av2,x);
    }
  }
  return gerepilecopy(av,x);
}

/*******************************************************************/
/**                                                               **/
/**                       COMBINATORICS                           **/
/**                                                               **/
/*******************************************************************/
/**                      BINOMIAL COEFFICIENTS                    **/
/*******************************************************************/
GEN
binomialuu(ulong n, ulong k)
{
  pari_sp ltop = avma;
  GEN z;
  if (k > n) return gen_0;
  k = minuu(k,n-k);
  if (!k) return gen_1;
  if (k == 1) return utoipos(n);
  z = diviiexact(mulu_interval(n-k+1, n), mulu_interval(2UL, k));
  return gerepileuptoint(ltop,z);
}

GEN
binomial(GEN n, long k)
{
  long i, prec;
  pari_sp av;
  GEN y;

  if (k <= 1)
  {
    if (is_noncalc_t(typ(n))) pari_err_TYPE("binomial",n);
    if (k < 0) return gen_0;
    if (k == 0) return gen_1;
    return gcopy(n);
  }
  av = avma;
  if (typ(n) == t_INT)
  {
    if (signe(n) > 0)
    {
      GEN z = subiu(n,k);
      if (cmpis(z,k) < 0)
      {
        k = itos(z); avma = av;
        if (k <= 1)
        {
          if (k < 0) return gen_0;
          if (k == 0) return gen_1;
          return icopy(n);
        }
      }
    }
    /* k > 1 */
    if (lgefint(n) == 3 && signe(n) > 0)
    {
      y = binomialuu(itou(n),(ulong)k);
      return gerepileupto(av, y);
    }
    else
    {
      y = cgetg(k+1,t_VEC);
      for (i=1; i<=k; i++) gel(y,i) = subiu(n,i-1);
      y = ZV_prod(y);
    }
    y = diviiexact(y, mpfact(k));
    return gerepileuptoint(av, y);
  }

  prec = precision(n);
  if (prec && k > 200 + 0.8*prec2nbits(prec)) {
    GEN A = mpfactr(k, prec), B = ggamma(gsubgs(n,k-1), prec);
    return gerepileupto(av, gdiv(ggamma(gaddgs(n,1), prec), gmul(A,B)));
  }

  y = cgetg(k+1,t_VEC);
  for (i=1; i<=k; i++) gel(y,i) = gsubgs(n,i-1);
  return gerepileupto(av, gdiv(RgV_prod(y), mpfact(k)));
}

GEN
binomial0(GEN x, GEN k)
{
  if (!k)
  {
    if (typ(x) != t_INT || signe(x) < 0) pari_err_TYPE("binomial", x);
    return vecbinomial(itos(x));
  }
  if (typ(k) != t_INT) pari_err_TYPE("binomial", k);
  return binomial(x, itos(k));
}

/* Assume n >= 0, return bin, bin[k+1] = binomial(n, k) */
GEN
vecbinomial(long n)
{
  long d, k;
  GEN C;
  if (!n) return mkvec(gen_1);
  C = cgetg(n+2, t_VEC) + 1; /* C[k] = binomial(n, k) */
  gel(C,0) = gen_1;
  gel(C,1) = utoipos(n); d = (n + 1) >> 1;
  for (k=2; k <= d; k++)
  {
    pari_sp av = avma;
    gel(C,k) = gerepileuptoint(av, diviuexact(mului(n-k+1, gel(C,k-1)), k));
  }
  for (   ; k <= n; k++) gel(C,k) = gel(C,n-k);
  return C - 1;
}

/********************************************************************/
/**                  STIRLING NUMBERS                              **/
/********************************************************************/
/* Stirling number of the 2nd kind. The number of ways of partitioning
   a set of n elements into m non-empty subsets. */
GEN
stirling2(ulong n, ulong m)
{
  pari_sp av = avma;
  GEN s, bmk;
  ulong k;
  if (n==0) return (m == 0)? gen_1: gen_0;
  if (m > n || m == 0) return gen_0;
  if (m==n) return gen_1;
  /* k = 0 */
  bmk = gen_1; s  = powuu(m, n);
  for (k = 1; k <= ((m-1)>>1); ++k)
  { /* bmk = binomial(m, k) */
    GEN c, kn, mkn;
    bmk = diviuexact(mului(m-k+1, bmk), k);
    kn  = powuu(k, n); mkn = powuu(m-k, n);
    c = odd(m)? subii(mkn,kn): addii(mkn,kn);
    c = mulii(bmk, c);
    s = odd(k)? subii(s, c): addii(s, c);
    if (gc_needed(av,2))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"stirling2");
      gerepileall(av, 2, &s, &bmk);
    }
  }
  /* k = m/2 */
  if (!odd(m))
  {
    GEN c;
    bmk = diviuexact(mului(k+1, bmk), k);
    c = mulii(bmk, powuu(k,n));
    s = odd(k)? subii(s, c): addii(s, c);
  }
  return gerepileuptoint(av, diviiexact(s, mpfact(m)));
}

/* Stirling number of the first kind. Up to the sign, the number of
   permutations of n symbols which have exactly m cycles. */
GEN
stirling1(ulong n, ulong m)
{
  pari_sp ltop=avma;
  ulong k;
  GEN s, t;
  if (n < m) return gen_0;
  else if (n==m) return gen_1;
  /* t = binomial(n-1+k, m-1) * binomial(2n-m, n-m-k) */
  /* k = n-m > 0 */
  t = binomialuu(2*n-m-1, m-1);
  s = mulii(t, stirling2(2*(n-m), n-m));
  if (odd(n-m)) togglesign(s);
  for (k = n-m-1; k > 0; --k)
  {
    GEN c;
    t = diviuuexact(muluui(n-m+k+1, n+k+1, t), n+k, n-m-k);
    c = mulii(t, stirling2(n-m+k, k));
    s = odd(k)? subii(s, c): addii(s, c);
    if ((k & 0x1f) == 0) {
      t = gerepileuptoint(ltop, t);
      s = gerepileuptoint(avma, s);
    }
  }
  return gerepileuptoint(ltop, s);
}

GEN
stirling(long n, long m, long flag)
{
  if (n < 0) pari_err_DOMAIN("stirling", "n", "<", gen_0, stoi(n));
  if (m < 0) pari_err_DOMAIN("stirling", "m", "<", gen_0, stoi(m));
  switch (flag)
  {
    case 1: return stirling1((ulong)n,(ulong)m);
    case 2: return stirling2((ulong)n,(ulong)m);
    default: pari_err_FLAG("stirling");
  }
  return NULL; /*LCOV_EXCL_LINE*/
}

/*******************************************************************/
/**                                                               **/
/**                     RECIPROCAL POLYNOMIAL                     **/
/**                                                               **/
/*******************************************************************/
/* return coefficients s.t x = x_0 X^n + ... + x_n */
GEN
polrecip(GEN x)
{
  long tx = typ(x);
  if (is_scalar_t(tx)) return gcopy(x);
  if (tx != t_POL) pari_err_TYPE("polrecip",x);
  return RgX_recip(x);
}

/********************************************************************/
/**                                                                **/
/**                  POLYNOMIAL INTERPOLATION                      **/
/**                                                                **/
/********************************************************************/
/* allow X = NULL for [1,...,n] */
GEN
RgV_polint(GEN X, GEN Y, long v)
{
  pari_sp av0 = avma, av;
  GEN Q, P = NULL;
  long i, l = lg(Y);
  if (!X)
  {
    X = cgetg(l, t_VEC);
    for (i=1; i<l; i++) gel(X,i) = utoipos(i);
  }
  Q = roots_to_pol(X, v); av = avma;
  for (i=1; i<l; i++)
  {
    GEN inv, T, dP;
    if (gequal0(gel(Y,i))) continue;
    T = RgX_div_by_X_x(Q, gel(X,i), NULL);
    inv = ginv(poleval(T,gel(X,i)));
    dP = RgX_Rg_mul(T, gmul(gel(Y,i),inv));
    P = P? RgX_add(P, dP): dP;
    if (gc_needed(av,2))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"FpV_polint");
      P = gerepileupto(av, P);
    }
  }
  if (!P) { avma = av; return zeropol(v); }
  return gerepileupto(av0, P);
}
/* X,Y are "spec" GEN vectors with n > 0 components ( at X[0], ... X[n-1] ) */
GEN
polint_i(GEN X, GEN Y, GEN x, long n, GEN *ptdy)
{
  long i, m, ns = 0;
  pari_sp av = avma;
  GEN y, c, d, dy = NULL; /* gcc -Wall */

  if (n == 1)
  {
    if (ptdy) *ptdy = gen_0;
    return gmul(gel(Y,0), Rg_get_1(x));
  }
  if (!X)
  {
    X = cgetg(n+1, t_VEC);
    for (i=1; i<=n; i++) gel(X,i) = utoipos(i);
    X++;
  }
  switch(typ(x)) {
    case t_INT: case t_REAL: case t_FRAC: case t_COMPLEX: case t_QUAD:
    {
      GEN D = NULL;
      for (i=0; i<n; i++)
      {
        GEN t = gsub(x,gel(X,i));
        switch(typ(t))
        {
          case t_INT: case t_REAL: case t_FRAC: case t_COMPLEX: case t_QUAD:
            t = gabs(t, DEFAULTPREC);
            if (!D || gcmp(t,D) < 0) { ns = i; D = t; }
            break;
          default:
            goto NODY;
        }
      }
      break;
      /* X[ns] is closest to x */
    }
NODY:
    default:
      if (ptdy) { *ptdy = gen_0; ptdy = NULL; }
  }
  c = new_chunk(n);
  d = new_chunk(n); for (i=0; i<n; i++) gel(c,i) = gel(d,i) = gel(Y,i);
  y = gel(d,ns--);
  /* divided differences */
  for (m=1; m<n; m++)
  {
    for (i=0; i<n-m; i++)
    {
      GEN ho = gsub(gel(X,i),x), hp = gsub(gel(X,i+m),x), den = gsub(ho,hp);
      if (gequal0(den))
      {
        char *x1 = stack_sprintf("X[%ld]", i+1);
        char *x2 = stack_sprintf("X[%ld]", i+m+1);
        pari_err_DOMAIN("polinterpolate",x1,"=",strtoGENstr(x2), X);
      }
      den = gdiv(gsub(gel(c,i+1),gel(d,i)), den);
      gel(c,i) = gmul(ho,den);
      gel(d,i) = gmul(hp,den);
    }
    dy = (2*(ns+1) < n-m)? gel(c,ns+1): gel(d,ns--);
    y = gadd(y,dy);
  }
  if (!ptdy) return gerepileupto(av, y);
  *ptdy = dy;
  gerepileall(av, 2, &y, ptdy);
  return y;
}

GEN
polint(GEN X, GEN Y, GEN t, GEN *ptdy)
{
  long lx = lg(X), vt;

  if (! is_vec_t(typ(X))) pari_err_TYPE("polinterpolate",X);
  if (Y)
  {
    if (! is_vec_t(typ(Y))) pari_err_TYPE("polinterpolate",Y);
    if (lx != lg(Y)) pari_err_DIM("polinterpolate");
  }
  else
  {
    Y = X;
    X = NULL;
  }
  if (ptdy) *ptdy = gen_0;
  vt = t? gvar(t): 0;
  if (vt != NO_VARIABLE)
  { /* formal interpolation */
    pari_sp av;
    long v0, vY = gvar(Y);
    GEN P;
    if (X) vY = varnmax(vY, gvar(X));
    /* shortcut */
    if (varncmp(vY, vt) > 0 && (!t || gequalX(t))) return RgV_polint(X, Y, vt);
    av = avma;
    /* first interpolate in high priority variable, then substitute t */
    v0 = fetch_var_higher();
    P = RgV_polint(X, Y, v0);
    P = gsubst(P, v0, t? t: pol_x(0));
    (void)delete_var();
    return gerepileupto(av, P);
  }
  /* numerical interpolation */
  if (lx == 1) return Rg_get_0(t);
  return polint_i(X? X+1: NULL,Y+1,t,lx-1,ptdy);
}

/********************************************************************/
/**                                                                **/
/**                       MODREVERSE                               **/
/**                                                                **/
/********************************************************************/
static void
err_reverse(GEN x, GEN T)
{
  pari_err_DOMAIN("modreverse","deg(minpoly(z))", "<", stoi(degpol(T)),
                  mkpolmod(x,T));
}

/* return y such that Mod(y, charpoly(Mod(a,T)) = Mod(a,T) */
GEN
RgXQ_reverse(GEN a, GEN T)
{
  pari_sp av = avma;
  long n = degpol(T);
  GEN y;

  if (n <= 1) {
    if (n <= 0) return gcopy(a);
    return gerepileupto(av, gneg(gdiv(gel(T,2), gel(T,3))));
  }
  if (typ(a) != t_POL || !signe(a)) err_reverse(a,T);
  y = RgXV_to_RgM(RgXQ_powers(a,n-1,T), n);
  y = RgM_solve(y, col_ei(n, 2));
  if (!y) err_reverse(a,T);
  return gerepilecopy(av, RgV_to_RgX(y, varn(T)));
}
GEN
QXQ_reverse(GEN a, GEN T)
{
  pari_sp av = avma;
  long n = degpol(T);
  GEN y;

  if (n <= 1) {
    if (n <= 0) return gcopy(a);
    return gerepileupto(av, gneg(gdiv(gel(T,2), gel(T,3))));
  }
  if (typ(a) != t_POL || !signe(a)) err_reverse(a,T);
  if (gequalX(a)) return gcopy(a);
  y = RgXV_to_RgM(QXQ_powers(a,n-1,T), n);
  y = QM_gauss(y, col_ei(n, 2));
  if (!y) err_reverse(a,T);
  return gerepilecopy(av, RgV_to_RgX(y, varn(T)));
}

GEN
modreverse(GEN x)
{
  long v, n;
  GEN T, a;

  if (typ(x)!=t_POLMOD) pari_err_TYPE("modreverse",x);
  T = gel(x,1); n = degpol(T); if (n <= 0) return gcopy(x);
  a = gel(x,2);
  v = varn(T);
  retmkpolmod(RgXQ_reverse(a, T),
              (n==1)? gsub(pol_x(v), a): RgXQ_charpoly(a, T, v));
}

/********************************************************************/
/**                                                                **/
/**                          MERGESORT                             **/
/**                                                                **/
/********************************************************************/
static int
cmp_small(GEN x, GEN y) {
  long a = (long)x, b = (long)y;
  return a>b? 1: (a<b? -1: 0);
}

static int
veccmp(void *data, GEN x, GEN y)
{
  GEN k = (GEN)data;
  long i, s, lk = lg(k), lx = minss(lg(x), lg(y));

  if (!is_vec_t(typ(x))) pari_err_TYPE("lexicographic vecsort",x);
  if (!is_vec_t(typ(y))) pari_err_TYPE("lexicographic vecsort",y);
  for (i=1; i<lk; i++)
  {
    long c = k[i];
    if (c >= lx)
      pari_err_TYPE("lexicographic vecsort, index too large", stoi(c));
    s = lexcmp(gel(x,c), gel(y,c));
    if (s) return s;
  }
  return 0;
}

/* return permutation sorting v[1..n], removing duplicates. Assume n > 0 */
static GEN
gen_sortspec_uniq(GEN v, long n, void *E, int (*cmp)(void*,GEN,GEN))
{
  pari_sp av;
  long NX, nx, ny, m, ix, iy, i;
  GEN x, y, w, W;
  int s;
  switch(n)
  {
    case 1: return mkvecsmall(1);
    case 2:
      s = cmp(E,gel(v,1),gel(v,2));
      if      (s < 0) return mkvecsmall2(1,2);
      else if (s > 0) return mkvecsmall2(2,1);
      return mkvecsmall(1);
    case 3:
      s = cmp(E,gel(v,1),gel(v,2));
      if (s < 0) {
        s = cmp(E,gel(v,2),gel(v,3));
        if (s < 0) return mkvecsmall3(1,2,3);
        else if (s == 0) return mkvecsmall2(1,2);
        s = cmp(E,gel(v,1),gel(v,3));
        if      (s < 0) return mkvecsmall3(1,3,2);
        else if (s > 0) return mkvecsmall3(3,1,2);
        return mkvecsmall2(1,2);
      } else if (s > 0) {
        s = cmp(E,gel(v,1),gel(v,3));
        if (s < 0) return mkvecsmall3(2,1,3);
        else if (s == 0) return mkvecsmall2(2,1);
        s = cmp(E,gel(v,2),gel(v,3));
        if (s < 0) return mkvecsmall3(2,3,1);
        else if (s > 0) return mkvecsmall3(3,2,1);
        return mkvecsmall2(2,1);
      } else {
        s = cmp(E,gel(v,1),gel(v,3));
        if (s < 0) return mkvecsmall2(1,3);
        else if (s == 0) return mkvecsmall(1);
        return mkvecsmall2(3,1);
      }
  }
  NX = nx = n>>1; ny = n-nx;
  av = avma;
  x = gen_sortspec_uniq(v,   nx,E,cmp); nx = lg(x)-1;
  y = gen_sortspec_uniq(v+NX,ny,E,cmp); ny = lg(y)-1;
  w = cgetg(n+1, t_VECSMALL);
  m = ix = iy = 1;
  while (ix<=nx && iy<=ny)
  {
    s = cmp(E, gel(v,x[ix]), gel(v,y[iy]+NX));
    if (s < 0)
      w[m++] = x[ix++];
    else if (s > 0)
      w[m++] = y[iy++]+NX;
    else {
      w[m++] = x[ix++];
      iy++;
    }
  }
  while (ix<=nx) w[m++] = x[ix++];
  while (iy<=ny) w[m++] = y[iy++]+NX;
  avma = av;
  W = cgetg(m, t_VECSMALL);
  for (i = 1; i < m; i++) W[i] = w[i];
  return W;
}

/* return permutation sorting v[1..n]. Assume n > 0 */
static GEN
gen_sortspec(GEN v, long n, void *E, int (*cmp)(void*,GEN,GEN))
{
  long nx, ny, m, ix, iy;
  GEN x, y, w;
  switch(n)
  {
    case 1:
      (void)cmp(E,gel(v,1),gel(v,1)); /* check for type error */
      return mkvecsmall(1);
    case 2:
      return cmp(E,gel(v,1),gel(v,2)) <= 0? mkvecsmall2(1,2)
                                          : mkvecsmall2(2,1);
    case 3:
      if (cmp(E,gel(v,1),gel(v,2)) <= 0) {
        if (cmp(E,gel(v,2),gel(v,3)) <= 0) return mkvecsmall3(1,2,3);
        return (cmp(E,gel(v,1),gel(v,3)) <= 0)? mkvecsmall3(1,3,2)
                                              : mkvecsmall3(3,1,2);
      } else {
        if (cmp(E,gel(v,1),gel(v,3)) <= 0) return mkvecsmall3(2,1,3);
        return (cmp(E,gel(v,2),gel(v,3)) <= 0)? mkvecsmall3(2,3,1)
                                              : mkvecsmall3(3,2,1);
      }
  }
  nx = n>>1; ny = n-nx;
  w = cgetg(n+1,t_VECSMALL);
  x = gen_sortspec(v,   nx,E,cmp);
  y = gen_sortspec(v+nx,ny,E,cmp);
  m = ix = iy = 1;
  while (ix<=nx && iy<=ny)
    if (cmp(E, gel(v,x[ix]), gel(v,y[iy]+nx))<=0)
      w[m++] = x[ix++];
    else
      w[m++] = y[iy++]+nx;
  while (ix<=nx) w[m++] = x[ix++];
  while (iy<=ny) w[m++] = y[iy++]+nx;
  avma = (pari_sp)w; return w;
}

static void
init_sort(GEN *x, long *tx, long *lx)
{
  *tx = typ(*x);
  if (*tx == t_LIST)
  {
    if (list_typ(*x)!=t_LIST_RAW) pari_err_TYPE("sort",*x);
    *x = list_data(*x);
    *lx = *x? lg(*x): 1;
  } else {
    if (!is_matvec_t(*tx) && *tx != t_VECSMALL) pari_err_TYPE("gen_sort",*x);
    *lx = lg(*x);
  }
}

/* (x o y)[1..lx-1], destroy y */
INLINE GEN
sort_extract(GEN x, GEN y, long tx, long lx)
{
  long i;
  switch(tx)
  {
    case t_VECSMALL:
      for (i=1; i<lx; i++) y[i] = x[y[i]];
      break;
    case t_LIST:
      settyp(y,t_VEC);
      for (i=1; i<lx; i++) gel(y,i) = gel(x,y[i]);
      return gtolist(y);
    default:
      settyp(y,tx);
      for (i=1; i<lx; i++) gel(y,i) = gcopy(gel(x,y[i]));
  }
  return y;
}

static GEN
triv_sort(long tx) { return tx == t_LIST? mklist(): cgetg(1, tx); }
/* Sort the vector x, using cmp to compare entries. */
GEN
gen_sort_uniq(GEN x, void *E, int (*cmp)(void*,GEN,GEN))
{
  long tx, lx;
  GEN y;

  init_sort(&x, &tx, &lx);
  if (lx==1) return triv_sort(tx);
  y = gen_sortspec_uniq(x,lx-1,E,cmp);
  return sort_extract(x, y, tx, lg(y)); /* lg(y) <= lx */
}
/* Sort the vector x, using cmp to compare entries. */
GEN
gen_sort(GEN x, void *E, int (*cmp)(void*,GEN,GEN))
{
  long tx, lx;
  GEN y;

  init_sort(&x, &tx, &lx);
  if (lx==1) return triv_sort(tx);
  y = gen_sortspec(x,lx-1,E,cmp);
  return sort_extract(x, y, tx, lx);
}
/* indirect sort: return the permutation that would sort x */
GEN
gen_indexsort_uniq(GEN x, void *E, int (*cmp)(void*,GEN,GEN))
{
  long tx, lx;
  init_sort(&x, &tx, &lx);
  if (lx==1) return cgetg(1, t_VECSMALL);
  return gen_sortspec_uniq(x,lx-1,E,cmp);
}
/* indirect sort: return the permutation that would sort x */
GEN
gen_indexsort(GEN x, void *E, int (*cmp)(void*,GEN,GEN))
{
  long tx, lx;
  init_sort(&x, &tx, &lx);
  if (lx==1) return cgetg(1, t_VECSMALL);
  return gen_sortspec(x,lx-1,E,cmp);
}

/* Sort the vector x in place, using cmp to compare entries */
void
gen_sort_inplace(GEN x, void *E, int (*cmp)(void*,GEN,GEN), GEN *perm)
{
  long tx, lx, i;
  pari_sp av = avma;
  GEN y;

  init_sort(&x, &tx, &lx);
  if (lx<=2)
  {
    if (perm) *perm = lx == 1? cgetg(1, t_VECSMALL): mkvecsmall(1);
    return;
  }
  y = gen_sortspec(x,lx-1, E, cmp);
  if (perm)
  {
    GEN z = new_chunk(lx);
    for (i=1; i<lx; i++) gel(z,i) = gel(x,y[i]);
    for (i=1; i<lx; i++) gel(x,i) = gel(z,i);
    *perm = y;
    avma = (pari_sp)y;
  } else {
    for (i=1; i<lx; i++) gel(y,i) = gel(x,y[i]);
    for (i=1; i<lx; i++) gel(x,i) = gel(y,i);
    avma = av;
  }
}

static int
closurecmp(void *data, GEN x, GEN y)
{
  pari_sp av = avma;
  long s = gsigne(closure_callgen2((GEN)data, x,y));
  avma = av; return s;
}
static void
check_positive_entries(GEN k)
{
  long i, l = lg(k);
  for (i=1; i<l; i++)
    if (k[i] <= 0) pari_err_DOMAIN("sort_function", "index", "<", gen_0, stoi(k[i]));
}

typedef int (*CMP_FUN)(void*,GEN,GEN);
/* return NULL if t_CLOSURE k is a "key" (arity 1) and not a sorting func */
static CMP_FUN
sort_function(void **E, GEN x, GEN k)
{
  int (*cmp)(GEN,GEN) = &lexcmp;
  long tx = typ(x);
  if (!k)
  {
    *E = (void*)((typ(x) == t_VECSMALL)? cmp_small: cmp);
    return &cmp_nodata;
  }
  if (tx == t_VECSMALL) pari_err_TYPE("sort_function", x);
  switch(typ(k))
  {
    case t_INT: k = mkvecsmall(itos(k));  break;
    case t_VEC: case t_COL: k = ZV_to_zv(k); break;
    case t_VECSMALL: break;
    case t_CLOSURE:
     if (closure_is_variadic(k))
       pari_err_TYPE("sort_function, variadic cmpf",k);
     *E = (void*)k;
     switch(closure_arity(k))
     {
       case 1: return NULL; /* wrt key */
       case 2: return &closurecmp;
       default: pari_err_TYPE("sort_function, cmpf arity != 1, 2",k);
     }
    default: pari_err_TYPE("sort_function",k);
  }
  check_positive_entries(k);
  *E = (void*)k; return &veccmp;
}

#define cmp_IND 1
#define cmp_LEX 2 /* FIXME: backward compatibility, ignored */
#define cmp_REV 4
#define cmp_UNIQ 8
GEN
vecsort0(GEN x, GEN k, long flag)
{
  void *E;
  int (*CMP)(void*,GEN,GEN) = sort_function(&E, x, k);

  if (flag < 0 || flag > (cmp_REV|cmp_LEX|cmp_IND|cmp_UNIQ))
    pari_err_FLAG("vecsort");
  if (!CMP)
  { /* wrt key: precompute all values, O(n) calls instead of O(n log n) */
    pari_sp av = avma;
    GEN v, y;
    long i, tx, lx;
    init_sort(&x, &tx, &lx);
    if (lx == 1) return flag&cmp_IND? cgetg(1,t_VECSMALL): triv_sort(tx);
    v = cgetg(lx, t_VEC);
    for (i = 1; i < lx; i++) gel(v,i) = closure_callgen1(k, gel(x,i));
    y = vecsort0(v, NULL, flag | cmp_IND);
    y = flag&cmp_IND? y: sort_extract(x, y, tx, lg(y));
    return gerepileupto(av, y);
  }
  if (flag&cmp_UNIQ)
    x = flag&cmp_IND? gen_indexsort_uniq(x, E, CMP): gen_sort_uniq(x, E, CMP);
  else
    x = flag&cmp_IND? gen_indexsort(x, E, CMP): gen_sort(x, E, CMP);
  if (flag & cmp_REV)
  { /* reverse order */
    GEN y = x;
    if (typ(x)==t_LIST) { y = list_data(x); if (!y) return x; }
    vecreverse_inplace(y);
  }
  return x;
}

GEN
indexsort(GEN x) { return gen_indexsort(x, (void*)&gcmp, cmp_nodata); }
GEN
indexlexsort(GEN x) { return gen_indexsort(x, (void*)&lexcmp, cmp_nodata); }
GEN
indexvecsort(GEN x, GEN k)
{
  if (typ(k) != t_VECSMALL) pari_err_TYPE("vecsort",k);
  return gen_indexsort(x, (void*)k, &veccmp);
}

GEN
sort(GEN x) { return gen_sort(x, (void*)gcmp, cmp_nodata); }
GEN
lexsort(GEN x) { return gen_sort(x, (void*)lexcmp, cmp_nodata); }
GEN
vecsort(GEN x, GEN k)
{
  if (typ(k) != t_VECSMALL) pari_err_TYPE("vecsort",k);
  return gen_sort(x, (void*)k, &veccmp);
}
/* adapted from gen_search; don't export: keys of T[i] should be precomputed */
static long
key_search(GEN T, GEN x, GEN code)
{
  long u = lg(T)-1, i, l, s;

  if (!u) return 0;
  l = 1; x = closure_callgen1(code, x);
  do
  {
    i = (l+u)>>1; s = lexcmp(x, closure_callgen1(code, gel(T,i)));
    if (!s) return i;
    if (s<0) u=i-1; else l=i+1;
  } while (u>=l);
  return 0;
}
long
vecsearch(GEN v, GEN x, GEN k)
{
  pari_sp av = avma;
  void *E;
  int (*CMP)(void*,GEN,GEN) = sort_function(&E, v, k);
  long r, tv = typ(v);
  if (tv == t_VECSMALL)
    x = (GEN)itos(x);
  else if (!is_matvec_t(tv)) pari_err_TYPE("vecsearch", v);
  r = CMP? gen_search(v, x, 0, E, CMP): key_search(v, x, k);
  avma = av; return r;
}

GEN
ZV_indexsort(GEN L) { return gen_indexsort(L, (void*)&cmpii, &cmp_nodata); }
GEN
ZV_sort(GEN L) { return gen_sort(L, (void*)&cmpii, &cmp_nodata); }
GEN
ZV_sort_uniq(GEN L) { return gen_sort_uniq(L, (void*)&cmpii, &cmp_nodata); }
void
ZV_sort_inplace(GEN L) { gen_sort_inplace(L, (void*)&cmpii, &cmp_nodata,NULL); }

/********************************************************************/
/**                      SEARCH IN SORTED VECTOR                   **/
/********************************************************************/
/* index of x in table T, 0 otherwise */
long
tablesearch(GEN T, GEN x, int (*cmp)(GEN,GEN))
{
  long l = 1, u = lg(T)-1, i, s;

  while (u>=l)
  {
    i = (l+u)>>1; s = cmp(x, gel(T,i));
    if (!s) return i;
    if (s<0) u=i-1; else l=i+1;
  }
  return 0;
}

/* looks if x belongs to the set T and returns the index if yes, 0 if no */
long
gen_search(GEN T, GEN x, long flag, void *data, int (*cmp)(void*,GEN,GEN))
{
  long u = lg(T)-1, i, l, s;

  if (!u) return flag? 1: 0;
  l = 1;
  do
  {
    i = (l+u)>>1; s = cmp(data, x, gel(T,i));
    if (!s) return flag? 0: i;
    if (s<0) u=i-1; else l=i+1;
  } while (u>=l);
  if (!flag) return 0;
  return (s<0)? i: i+1;
}

long
ZV_search(GEN x, GEN y) { return tablesearch(x, y, cmpii); }

long
zv_search(GEN x, long y) { return tablesearch(x, (GEN)y, cmp_small); }

/********************************************************************/
/**                   COMPARISON FUNCTIONS                         **/
/********************************************************************/
int
cmp_nodata(void *data, GEN x, GEN y)
{
  int (*cmp)(GEN,GEN)=(int (*)(GEN,GEN)) data;
  return cmp(x,y);
}

/* assume x and y come from the same idealprimedec call (uniformizer unique) */
int
cmp_prime_over_p(GEN x, GEN y)
{
  long k = pr_get_f(x) - pr_get_f(y); /* diff. between residue degree */
  return k? ((k > 0)? 1: -1)
          : ZV_cmp(pr_get_gen(x), pr_get_gen(y));
}

int
cmp_prime_ideal(GEN x, GEN y)
{
  int k = cmpii(pr_get_p(x), pr_get_p(y));
  return k? k: cmp_prime_over_p(x,y);
}

/* assume x and y are t_POL in the same variable whose coeffs can be
 * compared (used to sort polynomial factorizations) */
int
gen_cmp_RgX(void *data, GEN x, GEN y)
{
  int (*coeff_cmp)(GEN,GEN)=(int(*)(GEN,GEN))data;
  long i, lx = lg(x), ly = lg(y);
  int fl;
  if (lx > ly) return  1;
  if (lx < ly) return -1;
  for (i=lx-1; i>1; i--)
    if ((fl = coeff_cmp(gel(x,i), gel(y,i)))) return fl;
  return 0;
}

static int
cmp_RgX_Rg(GEN x, GEN y)
{
  long lx = lgpol(x), ly;
  if (lx > 1) return  1;
  ly = gequal0(y) ? 0:1;
  if (lx > ly) return  1;
  if (lx < ly) return -1;
  if (lx==0) return 0;
  return gcmp(gel(x,2), y);
}
int
cmp_RgX(GEN x, GEN y)
{
  if (typ(x) == t_POLMOD) x = gel(x,2);
  if (typ(y) == t_POLMOD) y = gel(y,2);
  if (typ(x) == t_POL) {
    if (typ(y) != t_POL) return cmp_RgX_Rg(x, y);
  } else {
    if (typ(y) != t_POL) return gcmp(x,y);
    return - cmp_RgX_Rg(y,x);
  }
  return gen_cmp_RgX((void*)&gcmp,x,y);
}

int
cmp_Flx(GEN x, GEN y)
{
  long i, lx = lg(x), ly = lg(y);
  if (lx > ly) return  1;
  if (lx < ly) return -1;
  for (i=lx-1; i>1; i--)
    if (uel(x,i) != uel(y,i)) return uel(x,i)<uel(y,i)? -1: 1;
  return 0;
}
/********************************************************************/
/**                   MERGE & SORT FACTORIZATIONS                  **/
/********************************************************************/
/* merge fx, fy two factorizations, whose 1st column is sorted in strictly
 * increasing order wrt cmp */
GEN
merge_factor(GEN fx, GEN fy, void *data, int (*cmp)(void *,GEN,GEN))
{
  GEN x = gel(fx,1), e = gel(fx,2), M, E;
  GEN y = gel(fy,1), f = gel(fy,2);
  long ix, iy, m, lx = lg(x), ly = lg(y), l = lx+ly-1;

  M = cgetg(l, t_COL);
  E = cgetg(l, t_COL);

  m = ix = iy = 1;
  while (ix<lx && iy<ly)
  {
    int s = cmp(data, gel(x,ix), gel(y,iy));
    if (s < 0)
    { gel(M,m) = gel(x,ix); gel(E,m) = gel(e,ix); ix++; }
    else if (s == 0)
    {
      GEN z = gel(x,ix), g = addii(gel(e,ix), gel(f,iy));
      iy++; ix++; if (!signe(g)) continue;
      gel(M,m) = z; gel(E,m) = g;
    }
    else
    { gel(M,m) = gel(y,iy); gel(E,m) = gel(f,iy); iy++; }
    m++;
  }
  while (ix<lx) { gel(M,m) = gel(x,ix); gel(E,m) = gel(e,ix); ix++; m++; }
  while (iy<ly) { gel(M,m) = gel(y,iy); gel(E,m) = gel(f,iy); iy++; m++; }
  setlg(M, m);
  setlg(E, m); return mkmat2(M, E);
}
/* merge two sorted vectors, removing duplicates. Shallow */
GEN
merge_sort_uniq(GEN x, GEN y, void *data, int (*cmp)(void *,GEN,GEN))
{
  long ix, iy, m, lx = lg(x), ly = lg(y), l = lx+ly-1;
  GEN M;

  M = cgetg(l, t_COL);
  m = ix = iy = 1;
  while (ix<lx && iy<ly)
  {
    int s = cmp(data, gel(x,ix), gel(y,iy));
    if (s < 0)
    { gel(M,m) = gel(x,ix); ix++; }
    else if (s == 0)
    { gel(M,m) = gel(x,ix); iy++; ix++; }
    else
    { gel(M,m) = gel(y,iy); iy++; }
    m++;
  }
  while (ix<lx) { gel(M,m) = gel(x,ix); ix++; m++; }
  while (iy<ly) { gel(M,m) = gel(y,iy); iy++; m++; }
  setlg(M, m); return M;
}

/* sort generic factorization, in place */
GEN
sort_factor(GEN y, void *data, int (*cmp)(void *,GEN,GEN))
{
  GEN a, b, A, B, w;
  pari_sp av;
  long n, i;

  a = gel(y,1); n = lg(a); if (n == 1) return y;
  b = gel(y,2); av = avma;
  A = new_chunk(n);
  B = new_chunk(n);
  w = gen_sortspec(a, n-1, data, cmp);
  for (i=1; i<n; i++) { long k=w[i]; gel(A,i) = gel(a,k); gel(B,i) = gel(b,k); }
  for (i=1; i<n; i++) { gel(a,i) = gel(A,i); gel(b,i) = gel(B,i); }
  avma = av; return y;
}
/* sort polynomial factorization, in place */
GEN
sort_factor_pol(GEN y,int (*cmp)(GEN,GEN))
{
  (void)sort_factor(y,(void*)cmp, &gen_cmp_RgX);
  return y;
}

/***********************************************************************/
/*                                                                     */
/*                          SET OPERATIONS                             */
/*                                                                     */
/***********************************************************************/
GEN
gtoset(GEN x)
{
  long lx;
  if (!x) return cgetg(1, t_VEC);
  switch(typ(x))
  {
    case t_VEC:
    case t_COL: lx = lg(x); break;
    case t_LIST:
      if (list_typ(x)==t_LIST_MAP) return mapdomain(x);
      x = list_data(x); lx = x? lg(x): 1; break;
    case t_VECSMALL: lx = lg(x); x = zv_to_ZV(x); break;
    default: return mkveccopy(x);
  }
  if (lx==1) return cgetg(1,t_VEC);
  x = gen_sort_uniq(x, (void*)&cmp_universal, cmp_nodata);
  settyp(x, t_VEC); /* it may be t_COL */
  return x;
}

long
setisset(GEN x)
{
  long i, lx = lg(x);

  if (typ(x) != t_VEC) return 0;
  if (lx == 1) return 1;
  for (i=1; i<lx-1; i++)
    if (cmp_universal(gel(x,i+1), gel(x,i)) <= 0) return 0;
  return 1;
}

long
setsearch(GEN T, GEN y, long flag)
{
  long lx;
  switch(typ(T))
  {
    case t_VEC: lx = lg(T); break;
    case t_LIST:
    if (list_typ(T) != t_LIST_RAW) pari_err_TYPE("setsearch",T);
    T = list_data(T); lx = T? lg(T): 1; break;
    default: pari_err_TYPE("setsearch",T);
      return 0; /*LCOV_EXCL_LINE*/
  }
  if (lx==1) return flag? 1: 0;
  return gen_search(T,y,flag,(void*)cmp_universal,cmp_nodata);
}

GEN
setunion(GEN x, GEN y)
{
  pari_sp av = avma;
  long i, j, k, lx = lg(x), ly = lg(y);
  GEN z = cgetg(lx + ly - 1, t_VEC);
  if (typ(x) != t_VEC) pari_err_TYPE("setunion",x);
  if (typ(y) != t_VEC) pari_err_TYPE("setunion",y);
  i = j = k = 1;
  while (i<lx && j<ly)
  {
    int s = cmp_universal(gel(x,i), gel(y,j));
    if (s < 0)
      z[k++] = x[i++];
    else if (s > 0)
      z[k++] = y[j++];
    else {
      z[k++] = x[i++];
      j++;
    }
  }
  while (i<lx) z[k++] = x[i++];
  while (j<ly) z[k++] = y[j++];
  setlg(z, k);
  return gerepilecopy(av, z);
}
/* in case of equal keys in x,y, take the key from x */
static GEN
ZV_union_shallow_t(GEN x, GEN y, long t)
{
  long i, j, k, lx = lg(x), ly = lg(y);
  GEN z = cgetg(lx + ly - 1, t);
  i = j = k = 1;
  while (i<lx && j<ly)
  {
    int s = cmpii(gel(x,i), gel(y,j));
    if (s < 0)
      z[k++] = x[i++];
    else if (s > 0)
      z[k++] = y[j++];
    else {
      z[k++] = x[i++];
      j++;
    }
  }
  while (i<lx) z[k++] = x[i++];
  while (j<ly) z[k++] = y[j++];
  setlg(z, k); return z;
}

GEN
ZV_union_shallow(GEN x, GEN y)
{ return ZV_union_shallow_t(x, y, t_VEC); }

GEN
ZC_union_shallow(GEN x, GEN y)
{ return ZV_union_shallow_t(x, y, t_COL); }

GEN
setintersect(GEN x, GEN y)
{
  long ix = 1, iy = 1, iz = 1, lx = lg(x), ly = lg(y);
  pari_sp av = avma;
  GEN z = cgetg(lx,t_VEC);
  if (typ(x) != t_VEC) pari_err_TYPE("setintersect",x);
  if (typ(y) != t_VEC) pari_err_TYPE("setintersect",y);
  while (ix < lx && iy < ly)
  {
    int c = cmp_universal(gel(x,ix), gel(y,iy));
    if      (c < 0) ix++;
    else if (c > 0) iy++;
    else { gel(z, iz++) = gel(x,ix); ix++; iy++; }
  }
  setlg(z,iz); return gerepilecopy(av,z);
}

GEN
gen_setminus(GEN A, GEN B, int (*cmp)(GEN,GEN))
{
  pari_sp ltop = avma;
  long i = 1, j = 1, k = 1, lx = lg(A), ly = lg(B);
  GEN  diff = cgetg(lx,t_VEC);
  while (i < lx && j < ly)
    switch ( cmp(gel(A,i),gel(B,j)) )
    {
      case -1: gel(diff,k++) = gel(A,i++); break;
      case 1: j++; break;
      case 0: i++; break;
    }
  while (i < lx) gel(diff,k++) = gel(A,i++);
  setlg(diff,k);
  return gerepilecopy(ltop,diff);
}

GEN
setminus(GEN x, GEN y)
{
  if (typ(x) != t_VEC) pari_err_TYPE("setminus",x);
  if (typ(y) != t_VEC) pari_err_TYPE("setminus",y);
  return gen_setminus(x,y,cmp_universal);
}

GEN
setbinop(GEN f, GEN x, GEN y)
{
  pari_sp av = avma;
  long i, j, lx, ly, k = 1;
  GEN z;
  if (typ(f) != t_CLOSURE || closure_arity(f) != 2 || closure_is_variadic(f))
    pari_err_TYPE("setbinop [function needs exactly 2 arguments]",f);
  lx = lg(x);
  if (typ(x) != t_VEC) pari_err_TYPE("setbinop", x);
  if (y == NULL) { /* assume x = y and f symmetric */
    z = cgetg((((lx-1)*lx) >> 1) + 1, t_VEC);
    for (i = 1; i < lx; i++)
      for (j = i; j < lx; j++)
        gel(z, k++) = closure_callgen2(f, gel(x,i),gel(x,j));
  } else {
    ly = lg(y);
    if (typ(y) != t_VEC) pari_err_TYPE("setbinop", y);
    z = cgetg((lx-1)*(ly-1) + 1, t_VEC);
    for (i = 1; i < lx; i++)
      for (j = 1; j < ly; j++)
        gel(z, k++) = closure_callgen2(f, gel(x,i),gel(y,j));
  }
  return gerepileupto(av, gtoset(z));
}
