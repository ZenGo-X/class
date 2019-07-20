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
/**                   TRANSCENDENTAL FUNCTIONS                     **/
/**                                                                **/
/********************************************************************/
#include "pari.h"
#include "paripriv.h"

#ifdef LONG_IS_64BIT
static const long SQRTVERYBIGINT = 3037000500L; /* ceil(sqrt(LONG_MAX)) */
#else
static const long SQRTVERYBIGINT = 46341L;
#endif

static THREAD GEN gcatalan, geuler, glog2, gpi;
void
pari_init_floats(void)
{
  gcatalan = geuler = gpi = bernzone = glog2 = NULL;
}

void
pari_close_floats(void)
{
  if (gcatalan) gunclone(gcatalan);
  if (geuler) gunclone(geuler);
  if (gpi) gunclone(gpi);
  if (bernzone) gunclone(bernzone);
  if (glog2) gunclone(glog2);
}

/********************************************************************/
/**                   GENERIC BINARY SPLITTING                     **/
/**                    (Haible, Papanikolaou)                      **/
/********************************************************************/
void
abpq_init(struct abpq *A, long n)
{
  A->a = (GEN*)new_chunk(n+1);
  A->b = (GEN*)new_chunk(n+1);
  A->p = (GEN*)new_chunk(n+1);
  A->q = (GEN*)new_chunk(n+1);
}
static GEN
mulii3(GEN a, GEN b, GEN c) { return mulii(mulii(a,b),c); }
static GEN
mulii4(GEN a, GEN b, GEN c, GEN d) { return mulii(mulii(a,b),mulii(c,d)); }

/* T_{n1,n1+1}, given P = p[n1]p[n1+1] */
static GEN
T2(struct abpq *A, long n1, GEN P)
{
  GEN u1 = mulii4(A->a[n1], A->p[n1], A->b[n1+1], A->q[n1+1]);
  GEN u2 = mulii3(A->b[n1],A->a[n1+1], P);
  return addii(u1, u2);
}

/* assume n2 > n1. Compute sum_{n1 <= n < n2} a/b(n) p/q(n1)... p/q(n) */
void
abpq_sum(struct abpq_res *r, long n1, long n2, struct abpq *A)
{
  struct abpq_res L, R;
  GEN u1, u2;
  pari_sp av;
  long n;
  switch(n2 - n1)
  {
    GEN b, p, q;
    case 1:
      r->P = A->p[n1];
      r->Q = A->q[n1];
      r->B = A->b[n1];
      r->T = mulii(A->a[n1], A->p[n1]);
      return;
    case 2:
      r->P = mulii(A->p[n1], A->p[n1+1]);
      r->Q = mulii(A->q[n1], A->q[n1+1]);
      r->B = mulii(A->b[n1], A->b[n1+1]);
      av = avma;
      r->T = gerepileuptoint(av, T2(A, n1, r->P));
      return;

    case 3:
      p = mulii(A->p[n1+1], A->p[n1+2]);
      q = mulii(A->q[n1+1], A->q[n1+2]);
      b = mulii(A->b[n1+1], A->b[n1+2]);
      r->P = mulii(A->p[n1], p);
      r->Q = mulii(A->q[n1], q);
      r->B = mulii(A->b[n1], b);
      av = avma;
      u1 = mulii3(b, q, A->a[n1]);
      u2 = mulii(A->b[n1], T2(A, n1+1, p));
      r->T = gerepileuptoint(av, mulii(A->p[n1], addii(u1, u2)));
      return;
  }

  av = avma;
  n = (n1 + n2) >> 1;
  abpq_sum(&L, n1, n, A);
  abpq_sum(&R, n, n2, A);

  r->P = mulii(L.P, R.P);
  r->Q = mulii(L.Q, R.Q);
  r->B = mulii(L.B, R.B);
  u1 = mulii3(R.B,R.Q,L.T);
  u2 = mulii3(L.B,L.P,R.T);
  r->T = addii(u1,u2);
  avma = av;
  r->P = icopy(r->P);
  r->Q = icopy(r->Q);
  r->B = icopy(r->B);
  r->T = icopy(r->T);
}

/********************************************************************/
/**                                                                **/
/**                               PI                               **/
/**                                                                **/
/********************************************************************/
/* replace *old clone by c. Protect against SIGINT */
static void
swap_clone(GEN *old, GEN c)
{
  GEN tmp = *old;
  *old = c;
  if (tmp) gunclone(tmp);
}

/*                         ----
 *  53360 (640320)^(1/2)   \    (6n)! (545140134 n + 13591409)
 *  -------------------- = /    ------------------------------
 *        Pi               ----   (n!)^3 (3n)! (-640320)^(3n)
 *                         n>=0
 *
 * Ramanujan's formula + binary splitting */
static GEN
pi_ramanujan(long prec)
{
  const ulong B = 545140134, A = 13591409, C = 640320;
  const double alpha2 = 47.11041314; /* 3log(C/12) / log(2) */
  long n, nmax, prec2;
  struct abpq_res R;
  struct abpq S;
  GEN D, u;

  nmax = (long)(1 + prec2nbits(prec)/alpha2);
#ifdef LONG_IS_64BIT
  D = utoipos(10939058860032000UL); /* C^3/24 */
#else
  D = uutoi(2546948UL,495419392UL);
#endif
  abpq_init(&S, nmax);
  S.a[0] = utoipos(A);
  S.b[0] = S.p[0] = S.q[0] = gen_1;
  for (n = 1; n <= nmax; n++)
  {
    S.a[n] = addiu(muluu(B, n), A);
    S.b[n] = gen_1;
    S.p[n] = mulis(muluu(6*n-5, 2*n-1), 1-6*n);
    S.q[n] = mulii(sqru(n), muliu(D,n));
  }
  abpq_sum(&R, 0, nmax, &S); prec2 = prec+EXTRAPRECWORD;
  u = itor(muliu(R.Q,C/12), prec2);
  return rtor(mulrr(divri(u, R.T), sqrtr_abs(utor(C,prec2))), prec);
}

#if 0 /* Much slower than binary splitting at least up to prec = 10^8 */
/* Gauss - Brent-Salamin AGM iteration */
static GEN
pi_brent_salamin(long prec)
{
  GEN A, B, C;
  pari_sp av2;
  long i, G;

  G = - prec2nbits(prec);
  incrprec(prec);

  A = real2n(-1, prec);
  B = sqrtr_abs(A); /* = 1/sqrt(2) */
  setexpo(A, 0);
  C = real2n(-2, prec); av2 = avma;
  for (i = 0;; i++)
  {
    GEN y, a, b, B_A = subrr(B, A);
    pari_sp av3 = avma;
    if (expo(B_A) < G) break;
    a = addrr(A,B); shiftr_inplace(a, -1);
    b = mulrr(A,B);
    affrr(a, A);
    affrr(sqrtr_abs(b), B); avma = av3;
    y = sqrr(B_A); shiftr_inplace(y, i - 2);
    affrr(subrr(C, y), C); avma = av2;
  }
  shiftr_inplace(C, 2);
  return divrr(sqrr(addrr(A,B)), C);
}
GEN
constpi(long prec)
{
  pari_sp av;
  GEN tmp;
  if (gpi && realprec(gpi) >= prec) return gpi;

  tmp = cgetr_block(prec);
  av = avma;
  affrr(pi_brent_salamin(prec), tmp);
  swap_clone(&gpi, tmp);
  avma = av;  return gpi;
}
#endif

GEN
constpi(long prec)
{
  pari_sp av;
  GEN tmp;
  if (gpi && realprec(gpi) >= prec) return gpi;

  av = avma;
  tmp = gclone(pi_ramanujan(prec));
  swap_clone(&gpi,tmp);
  avma = av; return gpi;
}

GEN
mppi(long prec) { return rtor(constpi(prec), prec); }

/* Pi * 2^n */
GEN
Pi2n(long n, long prec)
{
  GEN x = mppi(prec); shiftr_inplace(x, n);
  return x;
}

/* I * Pi * 2^n */
GEN
PiI2n(long n, long prec) { retmkcomplex(gen_0, Pi2n(n, prec)); }

/* 2I * Pi */
GEN
PiI2(long prec) { return PiI2n(1, prec); }

/********************************************************************/
/**                                                                **/
/**                       EULER CONSTANT                           **/
/**                                                                **/
/********************************************************************/

GEN
consteuler(long prec)
{
  GEN u,v,a,b,tmpeuler;
  long l, n1, n, k, x;
  pari_sp av1, av2;

  if (geuler && realprec(geuler) >= prec) return geuler;

  av1 = avma; tmpeuler = cgetr_block(prec);

  incrprec(prec);

  l = prec+EXTRAPRECWORD; x = (long) (1 + prec2nbits_mul(l, M_LN2/4));
  a = utor(x,l); u=logr_abs(a); setsigne(u,-1); affrr(u,a);
  b = real_1(l);
  v = real_1(l);
  n = (long)(1+3.591*x); /* z=3.591: z*[ ln(z)-1 ]=1 */
  n1 = minss(n, SQRTVERYBIGINT);
  if (x < SQRTVERYBIGINT)
  {
    ulong xx = x*x;
    av2 = avma;
    for (k=1; k<n1; k++)
    {
      affrr(divru(mulur(xx,b),k*k), b);
      affrr(divru(addrr(divru(mulur(xx,a),k),b),k), a);
      affrr(addrr(u,a), u);
      affrr(addrr(v,b), v); avma = av2;
    }
    for (   ; k<=n; k++)
    {
      affrr(divru(divru(mulur(xx,b),k),k), b);
      affrr(divru(addrr(divru(mulur(xx,a),k),b),k), a);
      affrr(addrr(u,a), u);
      affrr(addrr(v,b), v); avma = av2;
    }
  }
  else
  {
    GEN xx = sqru(x);
    av2 = avma;
    for (k=1; k<n1; k++)
    {
      affrr(divru(mulir(xx,b),k*k), b);
      affrr(divru(addrr(divru(mulir(xx,a),k),b),k), a);
      affrr(addrr(u,a), u);
      affrr(addrr(v,b), v); avma = av2;
    }
    for (   ; k<=n; k++)
    {
      affrr(divru(divru(mulir(xx,b),k),k), b);
      affrr(divru(addrr(divru(mulir(xx,a),k),b),k), a);
      affrr(addrr(u,a), u);
      affrr(addrr(v,b), v); avma = av2;
    }
  }
  divrrz(u,v,tmpeuler);
  swap_clone(&geuler,tmpeuler);
  avma = av1; return geuler;
}

GEN
mpeuler(long prec) { return rtor(consteuler(prec), prec); }

/********************************************************************/
/**                                                                **/
/**                       CATALAN CONSTANT                         **/
/**                                                                **/
/********************************************************************/
/* 8G = 3\sum_{n>=0} 1/(binomial(2n,n)(2n+1)^2) + Pi log(2+sqrt(3)) */
static GEN
catalan(long prec)
{
  long i, nmax = prec2nbits(prec) >> 1;
  struct abpq_res R;
  struct abpq A;
  GEN u, v;
  abpq_init(&A, nmax);
  A.a[0] = A.b[0] = A.p[0] = A.q[0] = gen_1;
  for (i = 1; i <= nmax; i++)
  {
    A.a[i] = gen_1;
    A.b[i] = utoipos((i<<1)+1);
    A.p[i] = utoipos(i);
    A.q[i] = utoipos((i<<2)+2);
  }
  abpq_sum(&R, 0, nmax, &A);
  u = mulur(3, rdivii(R.T, mulii(R.B,R.Q),prec));
  v = mulrr(mppi(prec), logr_abs(addrs(sqrtr_abs(utor(3,prec)), 2)));
  u = addrr(u, v); shiftr_inplace(u, -3);
  return u;
}

GEN
constcatalan(long prec)
{
  pari_sp av = avma;
  GEN tmp;
  if (gcatalan && realprec(gcatalan) >= prec) return gcatalan;
  tmp = gclone(catalan(prec));
  swap_clone(&gcatalan,tmp);
  avma = av; return gcatalan;
}

GEN
mpcatalan(long prec) { return rtor(constcatalan(prec), prec); }

/********************************************************************/
/**                                                                **/
/**          TYPE CONVERSION FOR TRANSCENDENTAL FUNCTIONS          **/
/**                                                                **/
/********************************************************************/
static GEN
transvec(GEN (*f)(GEN,long), GEN x, long prec)
{
  long i, l;
  GEN y = cgetg_copy(x, &l);
  for (i=1; i<l; i++) gel(y,i) = f(gel(x,i),prec);
  return y;
}

GEN
trans_eval(const char *fun, GEN (*f)(GEN,long), GEN x, long prec)
{
  pari_sp av = avma;
  if (prec < 3) pari_err_BUG("trans_eval [prec < 3]");
  switch(typ(x))
  {
    case t_INT:    x = f(itor(x,prec),prec); break;
    case t_FRAC:   x = f(fractor(x, prec),prec); break;
    case t_QUAD:   x = f(quadtofp(x,prec),prec); break;
    case t_POLMOD: x = transvec(f, polmod_to_embed(x,prec), prec); break;
    case t_VEC:
    case t_COL:
    case t_MAT: return transvec(f, x, prec);
    default: pari_err_TYPE(fun,x); return NULL;
  }
  return gerepileupto(av, x);
}

/*******************************************************************/
/*                                                                 */
/*                            POWERING                             */
/*                                                                 */
/*******************************************************************/
/* x a t_REAL 0, return exp(x) */
static GEN
mpexp0(GEN x)
{
  long e = expo(x);
  return e >= 0? real_0_bit(e): real_1_bit(-e);
}
static GEN
powr0(GEN x)
{ return signe(x)? real_1(realprec(x)): mpexp0(x); }

/* x t_POL or t_SER, return scalarpol(Rg_get_1(x)) */
static GEN
scalarpol_get_1(GEN x)
{
  GEN y = cgetg(3,t_POL);
  y[1] = evalvarn(varn(x)) | evalsigne(1);
  gel(y,2) = Rg_get_1(x); return y;
}
/* to be called by the generic function gpowgs(x,s) when s = 0 */
static GEN
gpowg0(GEN x)
{
  long lx, i;
  GEN y;

  switch(typ(x))
  {
    case t_INT: case t_REAL: case t_FRAC: case t_PADIC:
      return gen_1;

    case t_QUAD: x++; /*fall through*/
    case t_COMPLEX: {
      pari_sp av = avma;
      GEN a = gpowg0(gel(x,1));
      GEN b = gpowg0(gel(x,2));
      if (a == gen_1) return b;
      if (b == gen_1) return a;
      return gerepileupto(av, gmul(a,b));
    }
    case t_INTMOD:
      y = cgetg(3,t_INTMOD);
      gel(y,1) = icopy(gel(x,1));
      gel(y,2) = is_pm1(gel(x,1))? gen_0: gen_1;
      return y;

    case t_FFELT: return FF_1(x);

    case t_POLMOD:
      retmkpolmod(scalarpol_get_1(gel(x,1)), gcopy(gel(x,1)));

    case t_RFRAC:
      return scalarpol_get_1(gel(x,2));
    case t_POL: case t_SER:
      return scalarpol_get_1(x);

    case t_MAT:
      lx=lg(x); if (lx==1) return cgetg(1,t_MAT);
      if (lx != lgcols(x)) pari_err_DIM("gpow");
      y = matid(lx-1);
      for (i=1; i<lx; i++) gcoeff(y,i,i) = gpowg0(gcoeff(x,i,i));
      return y;
    case t_QFR: return qfr_1(x);
    case t_QFI: return qfi_1(x);
    case t_VECSMALL: return identity_perm(lg(x) - 1);
  }
  pari_err_TYPE("gpow",x);
  return NULL; /* LCOV_EXCL_LINE */
}

static GEN
_sqr(void *data /* ignored */, GEN x) { (void)data; return gsqr(x); }
static GEN
_mul(void *data /* ignored */, GEN x, GEN y) { (void)data; return gmul(x,y); }
static GEN
_one(void *x) { return gpowg0((GEN) x); }
static GEN
_sqri(void *data /* ignored */, GEN x) { (void)data; return sqri(x); }
static GEN
_muli(void *data /* ignored */, GEN x, GEN y) { (void)data; return mulii(x,y); }
static GEN
_sqrr(void *data /* ignored */, GEN x) { (void)data; return sqrr(x); }
static GEN
_mulr(void *data /* ignored */, GEN x, GEN y) { (void)data; return mulrr(x,y); }
static GEN
_oner(void *data /* prec */) { return real_1( *(long*) data); }

/* INTEGER POWERING (a^n for integer a != 0 and integer n > 0)
 *
 * Use left shift binary algorithm (RS is wasteful: multiplies big numbers,
 * with LS one of them is the base, hence small). Sign of result is set
 * to s (= 1,-1). Makes life easier for caller, which otherwise might do a
 * setsigne(gen_1 / gen_m1) */
static GEN
powiu_sign(GEN a, ulong N, long s)
{
  pari_sp av;
  GEN y;

  if (lgefint(a) == 3)
  { /* easy if |a| < 3 */
    ulong q = a[2];
    if (q == 1) return (s>0)? gen_1: gen_m1;
    if (q == 2) { a = int2u(N); setsigne(a,s); return a; }
    q = upowuu(q, N);
    if (q) return s>0? utoipos(q): utoineg(q);
  }
  if (N <= 2) {
    if (N == 2) return sqri(a);
    a = icopy(a); setsigne(a,s); return a;
  }
  av = avma;
  y = gen_powu_i(a, N, NULL, &_sqri, &_muli);
  setsigne(y,s); return gerepileuptoint(av, y);
}
/* a^n */
GEN
powiu(GEN a, ulong n)
{
  long s;
  if (!n) return gen_1;
  s = signe(a);
  if (!s) return gen_0;
  return powiu_sign(a, n, (s < 0 && odd(n))? -1: 1);
}
GEN
powis(GEN a, long n)
{
  long s;
  GEN t, y;
  if (n >= 0) return powiu(a, n);
  s = signe(a);
  if (!s) pari_err_INV("powis",gen_0);
  t = (s < 0 && odd(n))? gen_m1: gen_1;
  if (is_pm1(a)) return t;
  /* n < 0, |a| > 1 */
  y = cgetg(3,t_FRAC);
  gel(y,1) = t;
  gel(y,2) = powiu_sign(a, -n, 1); /* force denominator > 0 */
  return y;
}
GEN
powuu(ulong p, ulong N)
{
  pari_sp av = avma;
  long P[] = {evaltyp(t_INT)|_evallg(3), evalsigne(1)|evallgefint(3),0};
  ulong pN;
  GEN y;
  if (N <= 2)
  {
    if (N == 2) return sqru(p);
    if (N == 1) return utoi(p);
    return gen_1;
  }
  if (!p) return gen_0;
  pN = upowuu(p, N);
  if (pN) return utoipos(pN);
  if (p == 2) return int2u(N);
  P[2] = p; av = avma;
  y = gen_powu_i(P, N, NULL, &_sqri, &_muli);
  return gerepileuptoint(av, y);
}

/* return 0 if overflow */
static ulong
usqru(ulong p) { return p & HIGHMASK? 0: p*p; }
ulong
upowuu(ulong p, ulong k)
{
#ifdef LONG_IS_64BIT
  const ulong CUTOFF3 = 2642245;
  const ulong CUTOFF4 = 65535;
  const ulong CUTOFF5 = 7131;
  const ulong CUTOFF6 = 1625;
  const ulong CUTOFF7 = 565;
  const ulong CUTOFF8 = 255;
  const ulong CUTOFF9 = 138;
  const ulong CUTOFF10 = 84;
  const ulong CUTOFF11 = 56;
  const ulong CUTOFF12 = 40;
  const ulong CUTOFF13 = 30;
  const ulong CUTOFF14 = 23;
  const ulong CUTOFF15 = 19;
  const ulong CUTOFF16 = 15;
  const ulong CUTOFF17 = 13;
  const ulong CUTOFF18 = 11;
  const ulong CUTOFF19 = 10;
  const ulong CUTOFF20 =  9;
#else
  const ulong CUTOFF3 = 1625;
  const ulong CUTOFF4 =  255;
  const ulong CUTOFF5 =   84;
  const ulong CUTOFF6 =   40;
  const ulong CUTOFF7 =   23;
  const ulong CUTOFF8 =   15;
  const ulong CUTOFF9 =   11;
  const ulong CUTOFF10 =   9;
  const ulong CUTOFF11 =   7;
  const ulong CUTOFF12 =   6;
  const ulong CUTOFF13 =   5;
  const ulong CUTOFF14 =   4;
  const ulong CUTOFF15 =   4;
  const ulong CUTOFF16 =   3;
  const ulong CUTOFF17 =   3;
  const ulong CUTOFF18 =   3;
  const ulong CUTOFF19 =   3;
  const ulong CUTOFF20 =   3;
#endif

  if (p <= 2)
  {
    if (p < 2) return p;
    return k < BITS_IN_LONG? 1UL<<k: 0;
  }
  switch(k)
  {
    ulong p2, p3, p4, p5, p8;
    case 0:  return 1;
    case 1:  return p;
    case 2:  return usqru(p);
    case 3:  if (p > CUTOFF3) return 0; return p*p*p;
    case 4:  if (p > CUTOFF4) return 0; p2=p*p; return p2*p2;
    case 5:  if (p > CUTOFF5) return 0; p2=p*p; return p2*p2*p;
    case 6:  if (p > CUTOFF6) return 0; p2=p*p; return p2*p2*p2;
    case 7:  if (p > CUTOFF7) return 0; p2=p*p; return p2*p2*p2*p;
    case 8:  if (p > CUTOFF8) return 0; p2=p*p; p4=p2*p2; return p4*p4;
    case 9:  if (p > CUTOFF9) return 0; p2=p*p; p4=p2*p2; return p4*p4*p;
    case 10: if (p > CUTOFF10)return 0; p2=p*p; p4=p2*p2; return p4*p4*p2;
    case 11: if (p > CUTOFF11)return 0; p2=p*p; p4=p2*p2; return p4*p4*p2*p;
    case 12: if (p > CUTOFF12)return 0; p2=p*p; p4=p2*p2; return p4*p4*p4;
    case 13: if (p > CUTOFF13)return 0; p2=p*p; p4=p2*p2; return p4*p4*p4*p;
    case 14: if (p > CUTOFF14)return 0; p2=p*p; p4=p2*p2; return p4*p4*p4*p2;
    case 15: if (p > CUTOFF15)return 0;
      p2=p*p; p3=p2*p; p5=p3*p2; return p5*p5*p5;
    case 16: if (p > CUTOFF16)return 0;
      p2=p*p; p4=p2*p2; p8=p4*p4; return p8*p8;
    case 17: if (p > CUTOFF17)return 0;
      p2=p*p; p4=p2*p2; p8=p4*p4; return p*p8*p8;
    case 18: if (p > CUTOFF18)return 0;
      p2=p*p; p4=p2*p2; p8=p4*p4; return p2*p8*p8;
    case 19: if (p > CUTOFF19)return 0;
      p2=p*p; p4=p2*p2; p8=p4*p4; return p*p2*p8*p8;
    case 20: if (p > CUTOFF20)return 0;
      p2=p*p; p4=p2*p2; p8=p4*p4; return p4*p8*p8;
  }
#ifdef LONG_IS_64BIT
  switch(p)
  {
    case 3: if (k > 40) return 0;
      break;
    case 4: if (k > 31) return 0;
      return 1UL<<(2*k);
    case 5: if (k > 27) return 0;
      break;
    case 6: if (k > 24) return 0;
      break;
    case 7: if (k > 22) return 0;
      break;
    default: return 0;
  }
  /* no overflow */
  {
    ulong q = upowuu(p, k >> 1);
    q *= q ;
    return odd(k)? q*p: q;
  }
#else
  return 0;
#endif
}

typedef struct {
  long prec, a;
  GEN (*sqr)(GEN);
  GEN (*mulug)(ulong,GEN);
} sr_muldata;

static GEN
_rpowuu_sqr(void *data, GEN x)
{
  sr_muldata *D = (sr_muldata *)data;
  if (typ(x) == t_INT && lgefint(x) >= D->prec)
  { /* switch to t_REAL */
    D->sqr   = &sqrr;
    D->mulug = &mulur; x = itor(x, D->prec);
  }
  return D->sqr(x);
}

static GEN
_rpowuu_msqr(void *data, GEN x)
{
  GEN x2 = _rpowuu_sqr(data, x);
  sr_muldata *D = (sr_muldata *)data;
  return D->mulug(D->a, x2);
}

/* return a^n as a t_REAL of precision prec. Assume a > 0, n > 0 */
GEN
rpowuu(ulong a, ulong n, long prec)
{
  pari_sp av;
  GEN y, z;
  sr_muldata D;

  if (a == 1) return real_1(prec);
  if (a == 2) return real2n(n, prec);
  if (n == 1) return utor(a, prec);
  z = cgetr(prec);
  av = avma;
  D.sqr   = &sqri;
  D.mulug = &mului;
  D.prec = prec;
  D.a = (long)a;
  y = gen_powu_fold_i(utoipos(a), n, (void*)&D, &_rpowuu_sqr, &_rpowuu_msqr);
  mpaff(y, z); avma = av; return z;
}

GEN
powrs(GEN x, long n)
{
  pari_sp av = avma;
  GEN y;
  if (!n) return powr0(x);
  y = gen_powu_i(x, (ulong)labs(n), NULL, &_sqrr, &_mulr);
  if (n < 0) y = invr(y);
  return gerepileuptoleaf(av,y);
}
GEN
powru(GEN x, ulong n)
{
  pari_sp av = avma;
  GEN y;
  if (!n) return powr0(x);
  y = gen_powu_i(x, n, NULL, &_sqrr, &_mulr);
  return gerepileuptoleaf(av,y);
}

GEN
powersr(GEN x, long n)
{
  long prec = realprec(x);
  return gen_powers(x, n, 1, &prec, &_sqrr, &_mulr, &_oner);
}

/* x^(s/2), assume x t_REAL */
GEN
powrshalf(GEN x, long s)
{
  if (s & 1) return sqrtr(powrs(x, s));
  return powrs(x, s>>1);
}
/* x^(s/2), assume x t_REAL */
GEN
powruhalf(GEN x, ulong s)
{
  if (s & 1) return sqrtr(powru(x, s));
  return powru(x, s>>1);
}
/* x^(n/d), assume x t_REAL, return t_REAL */
GEN
powrfrac(GEN x, long n, long d)
{
  long z;
  if (!n) return powr0(x);
  z = cgcd(n, d); if (z > 1) { n /= z; d /= z; }
  if (d == 1) return powrs(x, n);
  x = powrs(x, n);
  if (d == 2) return sqrtr(x);
  return sqrtnr(x, d);
}

/* assume x != 0 */
static GEN
pow_monome(GEN x, long n)
{
  long i, d, dx = degpol(x);
  GEN A, b, y;

  if (n < 0) { n = -n; y = cgetg(3, t_RFRAC); } else y = NULL;

  if (HIGHWORD(dx) || HIGHWORD(n))
  {
    LOCAL_HIREMAINDER;
    d = (long)mulll((ulong)dx, (ulong)n);
    if (hiremainder || (d &~ LGBITS)) d = LGBITS; /* overflow */
    d += 2;
  }
  else
    d = dx*n + 2;
  if ((d + 1) & ~LGBITS) pari_err(e_OVERFLOW,"pow_monome [degree]");
  A = cgetg(d+1, t_POL); A[1] = x[1];
  for (i=2; i < d; i++) gel(A,i) = gen_0;
  b = gpowgs(gel(x,dx+2), n); /* not memory clean if (n < 0) */
  if (!y) y = A;
  else {
    GEN c = denom_i(b);
    gel(y,1) = c; if (c != gen_1) b = gmul(b,c);
    gel(y,2) = A;
  }
  gel(A,d) = b; return y;
}

/* x t_PADIC */
static GEN
powps(GEN x, long n)
{
  long e = n*valp(x), v;
  GEN t, y, mod, p = gel(x,2);
  pari_sp av;

  if (!signe(gel(x,4))) {
    if (n < 0) pari_err_INV("powps",x);
    return zeropadic(p, e);
  }
  v = z_pval(n, p);

  y = cgetg(5,t_PADIC);
  mod = gel(x,3);
  if (v == 0) mod = icopy(mod);
  else
  {
    if (precp(x) == 1 && absequaliu(p, 2)) v++;
    mod = mulii(mod, powiu(p,v));
    mod = gerepileuptoint((pari_sp)y, mod);
  }
  y[1] = evalprecp(precp(x) + v) | evalvalp(e);
  gel(y,2) = icopy(p);
  gel(y,3) = mod;

  av = avma; t = gel(x,4);
  if (n < 0) { t = Fp_inv(t, mod); n = -n; }
  t = Fp_powu(t, n, mod);
  gel(y,4) = gerepileuptoint(av, t);
  return y;
}
/* x t_PADIC */
static GEN
powp(GEN x, GEN n)
{
  long v;
  GEN y, mod, p = gel(x,2);

  if (valp(x)) pari_err_OVERFLOW("valp()");

  if (!signe(gel(x,4))) {
    if (signe(n) < 0) pari_err_INV("powp",x);
    return zeropadic(p, 0);
  }
  v = Z_pval(n, p);

  y = cgetg(5,t_PADIC);
  mod = gel(x,3);
  if (v == 0) mod = icopy(mod);
  else
  {
    mod = mulii(mod, powiu(p,v));
    mod = gerepileuptoint((pari_sp)y, mod);
  }
  y[1] = evalprecp(precp(x) + v) | _evalvalp(0);
  gel(y,2) = icopy(p);
  gel(y,3) = mod;
  gel(y,4) = Fp_pow(gel(x,4), n, mod);
  return y;
}
static GEN
pow_polmod(GEN x, GEN n)
{
  GEN z = cgetg(3, t_POLMOD), a = gel(x,2), T = gel(x,1);
  gel(z,1) = gcopy(T);
  if (typ(a) != t_POL || varn(a) != varn(T) || lg(a) <= 3)
    a = powgi(a, n);
  else {
    pari_sp av = avma;
    GEN p = NULL;
    if (RgX_is_FpX(T, &p) && RgX_is_FpX(a, &p) && p)
    {
      T = RgX_to_FpX(T, p); a = RgX_to_FpX(a, p);
      if (lgefint(p) == 3)
      {
        ulong pp = p[2];
        a = Flxq_pow(ZX_to_Flx(a, pp), n, ZX_to_Flx(T, pp), pp);
        a = Flx_to_ZX(a);
      }
      else
        a = FpXQ_pow(a, n, T, p);
      a = FpX_to_mod(a, p);
      a = gerepileupto(av, a);
    }
    else
    {
      avma = av;
      a = RgXQ_pow(a, n, gel(z,1));
    }
  }
  gel(z,2) = a; return z;
}

GEN
gpowgs(GEN x, long n)
{
  long m;
  pari_sp av;
  GEN y;

  if (n == 0) return gpowg0(x);
  if (n == 1)
    switch (typ(x)) {
      case t_QFI: return redimag(x);
      case t_QFR: return redreal(x);
      default: return gcopy(x);
    }
  if (n ==-1) return ginv(x);
  switch(typ(x))
  {
    case t_INT: return powis(x,n);
    case t_REAL: return powrs(x,n);
    case t_INTMOD:
      y = cgetg(3,t_INTMOD); gel(y,1) = icopy(gel(x,1));
      gel(y,2) = Fp_pows(gel(x,2), n, gel(x,1));
      return y;
    case t_FRAC:
    {
      GEN a = gel(x,1), b = gel(x,2);
      long s = (signe(a) < 0 && odd(n))? -1: 1;
      if (n < 0) {
        n = -n;
        if (is_pm1(a)) return powiu_sign(b, n, s); /* +-1/x[2] inverts to t_INT */
        swap(a, b);
      }
      y = cgetg(3, t_FRAC);
      gel(y,1) = powiu_sign(a, n, s);
      gel(y,2) = powiu_sign(b, n, 1);
      return y;
    }
    case t_PADIC: return powps(x, n);
    case t_RFRAC:
    {
      av = avma; y = cgetg(3, t_RFRAC); m = labs(n);
      gel(y,1) = gpowgs(gel(x,1),m);
      gel(y,2) = gpowgs(gel(x,2),m);
      if (n < 0) y = ginv(y);
      return gerepileupto(av,y);
    }
    case t_POLMOD: {
      long N[] = {evaltyp(t_INT) | _evallg(3),0,0};
      affsi(n,N); return pow_polmod(x, N);
    }
    case t_POL:
      if (RgX_is_monomial(x)) return pow_monome(x, n);
    default: {
      pari_sp av = avma;
      y = gen_powu_i(x, (ulong)labs(n), NULL, &_sqr, &_mul);
      if (n < 0) y = ginv(y);
      return gerepileupto(av,y);
    }
  }
}

/* n a t_INT */
GEN
powgi(GEN x, GEN n)
{
  GEN y;

  if (!is_bigint(n)) return gpowgs(x, itos(n));
  /* probable overflow for non-modular types (typical exception: (X^0)^N) */
  switch(typ(x))
  {
    case t_INTMOD:
      y = cgetg(3,t_INTMOD); gel(y,1) = icopy(gel(x,1));
      gel(y,2) = Fp_pow(gel(x,2), n, gel(x,1));
      return y;
    case t_FFELT: return FF_pow(x,n);
    case t_PADIC: return powp(x, n);

    case t_INT:
      if (is_pm1(x)) return (signe(x) < 0 && mpodd(n))? gen_m1: gen_1;
      if (signe(x)) pari_err_OVERFLOW("lg()");
      if (signe(n) < 0) pari_err_INV("powgi",gen_0);
      return gen_0;
    case t_FRAC:
      pari_err_OVERFLOW("lg()");

    case t_QFR: return qfrpow(x, n);
    case t_POLMOD: return pow_polmod(x, n);
    default: {
      pari_sp av = avma;
      y = gen_pow(x, n, NULL, &_sqr, &_mul);
      if (signe(n) < 0) y = ginv(y);
      return gerepileupto(av,y);
    }
  }
}

/* Assume x = 1 + O(t), n a scalar. Return x^n */
static GEN
ser_pow_1(GEN x, GEN n)
{
  long lx, mi, i, j, d;
  GEN y = cgetg_copy(x, &lx), X = x+2, Y = y + 2;
  y[1] = evalsigne(1) | _evalvalp(0) | evalvarn(varn(x));
  d = mi = lx-3; while (mi>=1 && isrationalzero(gel(X,mi))) mi--;
  gel(Y,0) = gen_1;
  for (i=1; i<=d; i++)
  {
    pari_sp av = avma;
    GEN s = gen_0;
    for (j=1; j<=minss(i,mi); j++)
    {
      GEN t = gsubgs(gmulgs(n,j),i-j);
      s = gadd(s, gmul(gmul(t, gel(X,j)), gel(Y,i-j)));
    }
    gel(Y,i) = gerepileupto(av, gdivgs(s,i));
  }
  return y;
}

/* we suppose n != 0, valp(x) = 0 and leading-term(x) != 0. Not stack clean */
static GEN
ser_pow(GEN x, GEN n, long prec)
{
  GEN y, c, lead;
  if (varncmp(gvar(n), varn(x)) <= 0) return gexp(gmul(n, glog(x,prec)), prec);
  lead = gel(x,2);
  if (gequal1(lead)) return ser_pow_1(x, n);
  x = ser_normalize(x);
  if (typ(n) == t_FRAC && !isinexact(lead) && ispower(lead, gel(n,2), &c))
    c = powgi(c, gel(n,1));
  else
    c = gpow(lead,n, prec);
  y = gmul(c, ser_pow_1(x, n));
  /* gpow(t_POLMOD,n) can be a t_COL [conjvec] */
  if (typ(y) != t_SER) pari_err_TYPE("gpow", y);
  return y;
}

static long
val_from_i(GEN E)
{
  if (is_bigint(E)) pari_err_OVERFLOW("sqrtn [valuation]");
  return itos(E);
}

/* return x^q, assume typ(x) = t_SER, typ(q) = t_INT/t_FRAC and q != 0 */
static GEN
ser_powfrac(GEN x, GEN q, long prec)
{
  GEN y, E = gmulsg(valp(x), q);
  long e;

  if (!signe(x))
  {
    if (gsigne(q) < 0) pari_err_INV("gpow", x);
    return zeroser(varn(x), val_from_i(gfloor(E)));
  }
  if (typ(E) != t_INT)
    pari_err_DOMAIN("sqrtn", "valuation", "!=", mkintmod(gen_0, gel(q,2)), x);
  e = val_from_i(E);
  y = leafcopy(x); setvalp(y, 0);
  y = ser_pow(y, q, prec);
  setvalp(y, e); return y;
}

static GEN
gpow0(GEN x, GEN n, long prec)
{
  pari_sp av = avma;
  long i, lx;
  GEN y;
  switch(typ(n))
  {
    case t_INT: case t_REAL: case t_FRAC: case t_COMPLEX: case t_QUAD:
      break;
    case t_VEC: case t_COL: case t_MAT:
      y = cgetg_copy(n, &lx);
      for (i=1; i<lx; i++) gel(y,i) = gpow0(x,gel(n,i),prec);
      return y;
    default: pari_err_TYPE("gpow(0,n)", n);
  }
  n = real_i(n);
  if (gsigne(n) <= 0) pari_err_DOMAIN("gpow(0,n)", "n", "<=", gen_0, n);
  if (!precision(x)) return gcopy(x);

  x = ground(gmulsg(gexpo(x),n));
  if (is_bigint(x) || uel(x,2) >= HIGHEXPOBIT)
    pari_err_OVERFLOW("gpow");
  avma = av; return real_0_bit(itos(x));
}

GEN
gpow(GEN x, GEN n, long prec)
{
  long prec0, i, lx, tx, tn = typ(n);
  pari_sp av;
  GEN y;

  if (tn == t_INT) return powgi(x,n);
  tx = typ(x);
  if (is_matvec_t(tx))
  {
    y = cgetg_copy(x, &lx);
    for (i=1; i<lx; i++) gel(y,i) = gpow(gel(x,i),n,prec);
    return y;
  }
  av = avma;
  switch (tx)
  {
    case t_POL: case t_RFRAC: x = toser_i(x); /* fall through */
    case t_SER:
      if (tn == t_FRAC) return gerepileupto(av, ser_powfrac(x, n, prec));
      if (valp(x))
        pari_err_DOMAIN("gpow [irrational exponent]",
                        "valuation", "!=", gen_0, x);
      if (lg(x) == 2) return gerepilecopy(av, x); /* O(1) */
      return gerepileupto(av, ser_pow(x, n, prec));
  }
  if (gequal0(x)) return gpow0(x, n, prec);
  if (tn == t_FRAC)
  {
    GEN z, d = gel(n,2), a = gel(n,1);
    long D;
    switch (tx)
    {
    case t_INTMOD:
      {
        GEN p = gel(x,1);
        if (!BPSW_psp(p)) pari_err_PRIME("gpow",p);
        y = cgetg(3,t_INTMOD); gel(y,1) = icopy(p);
        av = avma;
        z = Fp_sqrtn(gel(x,2), d, p, NULL);
        if (!z) pari_err_SQRTN("gpow",x);
        gel(y,2) = gerepileuptoint(av, Fp_pow(z, a, p));
        return y;
      }

    case t_PADIC:
      z = Qp_sqrtn(x, d, NULL); if (!z) pari_err_SQRTN("gpow",x);
      return gerepileupto(av, powgi(z, a));

    case t_FFELT:
      return gerepileupto(av,FF_pow(FF_sqrtn(x,d,NULL),a));
    default:
      D = itos_or_0(d);
      if (!D) break;
      if (D == 2)
      {
        GEN y = gsqrt(x,prec), t = shifti(subiu(a,1), -1);
        if (signe(t)) y = gmul(y, powgi(x,t));
        return gerepileupto(av, y);
      }
      if (is_real_t(tx) && gsigne(x) > 0)
      {
        prec += nbits2extraprec(expi(a));
        if (tx != t_REAL) x = gtofp(x, prec);
        z = sqrtnr(x, D);
        if (!equali1(a)) z = powgi(z, a);
        return gerepileuptoleaf(av, z);
      }
    }
  }
  i = precision(n);
  if (i) prec = i;
  prec0 = prec;
  if (!gprecision(x))
  {
    long e = gexpo_safe(n); /* avoided if n = 0 or gexpo not defined */
    if (e > 2) prec += nbits2extraprec(e);
  }
  y = gmul(n, glog(x,prec));
  y = gexp(y,prec);
  if (prec0 == prec) return gerepileupto(av, y);
  return gerepilecopy(av, gprec_wtrunc(y,prec0));
}

GEN
gpowers0(GEN x, long n, GEN x0)
{
  long i, l;
  GEN V;
  if (!x0) return gpowers(x,n);
  if (n < 0) return cgetg(1,t_VEC);
  l = n+2; V = cgetg(l, t_VEC); gel(V,1) = gcopy(x0);
  for (i = 2; i < l; i++) gel(V,i) = gmul(gel(V,i-1),x);
  return V;
}

GEN
gpowers(GEN x, long n)
{
  if (n < 0) return cgetg(1,t_VEC);
  return gen_powers(x, n, 1, (void*)x, &_sqr, &_mul, &_one);
}

/* return [q^1,q^4,...,q^{n^2}] */
GEN
gsqrpowers(GEN q, long n)
{
  pari_sp av = avma;
  GEN L = gpowers0(gsqr(q), n, q); /* L[i] = q^(2i - 1), i <= n+1 */
  GEN v = cgetg(n+1, t_VEC);
  long i;
  gel(v, 1) = gcopy(q);
  for (i = 2; i <= n ; ++i) gel(v, i) = q = gmul(q, gel(L,i)); /* q^(i^2) */
  return gerepileupto(av, v);
}

/* 4 | N. returns a vector RU which contains exp(2*i*k*Pi/N), k=0..N-1 */
static GEN
grootsof1_4(long N, long prec)
{
  GEN z, RU = cgetg(N+1,t_VEC), *v  = ((GEN*)RU) + 1;
  long i, N2 = (N>>1), N4 = (N>>2), N8 = (N>>3);
  /* z^N2 = -1, z^N4 = I; if z^k = a+I*b, then z^(N4-k) = I*conj(z) = b+a*I */

  v[0] = gen_1; v[1] = z = rootsof1u_cx(N, prec);
  if (odd(N4)) N8++;
  for (i=1; i<N8; i++)
  {
    GEN t = v[i];
    v[i+1] = gmul(z, t);
    v[N4-i] = mkcomplex(gel(t,2), gel(t,1));
  }
  for (i=0; i<N4; i++) v[i+N4] = mulcxI(v[i]);
  for (i=0; i<N2; i++) v[i+N2] = gneg(v[i]);
  return RU;
}

/* as above, N arbitrary */
GEN
grootsof1(long N, long prec)
{
  GEN z, RU, *v;
  long i, k;

  if ((N & 3) == 0) return grootsof1_4(N, prec);
  if (N <= 2) return N == 1? mkvec(gen_1): mkvec2(gen_1, gen_m1);
  k = (N+3)>>1;
  RU = cgetg(N+1,t_VEC);
  v  = ((GEN*)RU) + 1;
  v[0] = gen_1; v[1] = z = rootsof1u_cx(N, prec);
  if (odd(N))
    for (i=2; i<k; i++) v[i] = gmul(z, v[i-1]);
  else
  {
    for (i=2; i<k-1; i++) v[i] = gmul(z, v[i-1]);
    v[i++] = gen_m1; /*avoid loss of accuracy*/
  }
  for (   ; i<N; i++) v[i] = gconj(v[N-i]);
  return RU;
}

/********************************************************************/
/**                                                                **/
/**                        RACINE CARREE                           **/
/**                                                                **/
/********************************************************************/
/* assume x unit, e = precp(x) */
GEN
Z2_sqrt(GEN x, long e)
{
  ulong r = signe(x)>=0?mod16(x):16-mod16(x);
  GEN z;
  long ez;
  pari_sp av;

  switch(e)
  {
    case 1: return gen_1;
    case 2: return (r & 3UL) == 1? gen_1: NULL;
    case 3: return (r & 7UL) == 1? gen_1: NULL;
    case 4: if (r == 1) return gen_1;
            else return (r == 9)? utoipos(3): NULL;
    default: if ((r&7UL) != 1) return NULL;
  }
  av = avma; z = (r==1)? gen_1: utoipos(3);
  ez = 3; /* number of correct bits in z (compared to sqrt(x)) */
  for(;;)
  {
    GEN mod;
    ez = (ez<<1) - 1;
    if (ez > e) ez = e;
    mod = int2n(ez);
    z = addii(z, remi2n(mulii(x, Fp_inv(z,mod)), ez));
    z = shifti(z, -1); /* (z + x/z) / 2 */
    if (e == ez) return gerepileuptoint(av, z);
    if (ez < e) ez--;
    if (gc_needed(av,2))
    {
      if (DEBUGMEM > 1) pari_warn(warnmem,"Qp_sqrt");
      z = gerepileuptoint(av,z);
    }
  }
}

/* x unit defined modulo p^e, e > 0 */
GEN
Qp_sqrt(GEN x)
{
  long pp, e = valp(x);
  GEN z,y,mod, p = gel(x,2);

  if (gequal0(x)) return zeropadic(p, (e+1) >> 1);
  if (e & 1) return NULL;

  y = cgetg(5,t_PADIC);
  pp = precp(x);
  mod = gel(x,3);
  z   = gel(x,4); /* lift to t_INT */
  e >>= 1;
  z = Zp_sqrt(z, p, pp);
  if (!z) return NULL;
  if (absequaliu(p,2))
  {
    pp  = (pp <= 3) ? 1 : pp-1;
    mod = int2n(pp);
  }
  else mod = icopy(mod);
  y[1] = evalprecp(pp) | evalvalp(e);
  gel(y,2) = icopy(p);
  gel(y,3) = mod;
  gel(y,4) = z; return y;
}

GEN
Zn_sqrt(GEN d, GEN fn)
{
  pari_sp ltop = avma, btop;
  GEN b = gen_0, m = gen_1;
  long j, np;
  if (typ(d) != t_INT) pari_err_TYPE("Zn_sqrt",d);
  if (typ(fn) == t_INT)
    fn = absZ_factor(fn);
  else if (!is_Z_factorpos(fn))
    pari_err_TYPE("Zn_sqrt",fn);
  np = nbrows(fn);
  btop = avma;
  for (j = 1; j <= np; ++j)
  {
    GEN  bp, mp, pr, r;
    GEN  p = gcoeff(fn, j, 1);
    long e = itos(gcoeff(fn, j, 2));
    long v = Z_pvalrem(d,p,&r);
    if (v >= e) bp =gen_0;
    else
    {
      if (odd(v)) return NULL;
      bp = Zp_sqrt(r, p, e-v);
      if (!bp)    return NULL;
      if (v) bp = mulii(bp, powiu(p, v>>1L));
    }
    mp = powiu(p, e);
    pr = mulii(m, mp);
    b = Z_chinese_coprime(b, bp, m, mp, pr);
    m = pr;
    if (gc_needed(btop, 1))
      gerepileall(btop, 2, &b, &m);
  }
  return gerepileupto(ltop, b);
}

static GEN
sqrt_ser(GEN b, long prec)
{
  long e = valp(b), vx = varn(b), lx, lold, j;
  ulong mask;
  GEN a, x, lta, ltx;

  if (!signe(b)) return zeroser(vx, e>>1);
  a = leafcopy(b);
  x = cgetg_copy(b, &lx);
  if (e & 1)
    pari_err_DOMAIN("sqrtn", "valuation", "!=", mkintmod(gen_0, gen_2), b);
  a[1] = x[1] = evalsigne(1) | evalvarn(0) | _evalvalp(0);
  lta = gel(a,2);
  if (gequal1(lta)) ltx = lta;
  else if (!issquareall(lta,&ltx)) ltx = gsqrt(lta,prec);
  gel(x,2) = ltx;
  for (j = 3; j < lx; j++) gel(x,j) = gen_0;
  setlg(x,3);
  mask = quadratic_prec_mask(lx - 2);
  lold = 1;
  while (mask > 1)
  {
    GEN y, x2 = gmul2n(x,1);
    long l = lold << 1, lx;

    if (mask & 1) l--;
    mask >>= 1;
    setlg(a, l + 2);
    setlg(x, l + 2);
    y = sqr_ser_part(x, lold, l-1) - lold;
    for (j = lold+2; j < l+2; j++) gel(y,j) = gsub(gel(y,j), gel(a,j));
    y += lold; setvalp(y, lold);
    y = normalize(y);
    y = gsub(x, gdiv(y, x2)); /* = gmul2n(gsub(x, gdiv(a,x)), -1); */
    lx = minss(l+2, lg(y));
    for (j = lold+2; j < lx; j++) gel(x,j) = gel(y,j);
    lold = l;
  }
  x[1] = evalsigne(1) | evalvarn(vx) | _evalvalp(e >> 1);
  return x;
}

GEN
gsqrt(GEN x, long prec)
{
  pari_sp av;
  GEN y;

  switch(typ(x))
  {
    case t_INT:
      if (!signe(x)) return real_0(prec); /* no loss of accuracy */
      x = itor(x,prec); /* fall through */
    case t_REAL: return sqrtr(x);

    case t_INTMOD:
    {
      GEN p = gel(x,1), a;
      y = cgetg(3,t_INTMOD); gel(y,1) = icopy(p);
      a = Fp_sqrt(gel(x,2),p);
      if (!a)
      {
        if (!BPSW_psp(p)) pari_err_PRIME("sqrt [modulus]",p);
        pari_err_SQRTN("gsqrt",x);
      }
      gel(y,2) = a; return y;
    }

    case t_COMPLEX:
    { /* (u+iv)^2 = a+ib <=> u^2+v^2 = sqrt(a^2+b^2), u^2-v^2=a, 2uv=b */
      GEN a = gel(x,1), b = gel(x,2), r, u, v;
      if (isrationalzero(b)) return gsqrt(a, prec);
      y = cgetg(3,t_COMPLEX); av = avma;

      r = cxnorm(x);
      if (typ(r) == t_INTMOD || typ(r) == t_PADIC)
        pari_err_IMPL("sqrt(complex of t_INTMODs)");
      r = gsqrt(r, prec); /* t_REAL, |a+Ib| */
      if (!signe(r))
        u = v = gerepileuptoleaf(av, sqrtr(r));
      else if (gsigne(a) < 0)
      {
        /* v > 0 since r > 0, a < 0, rounding errors can't make the sum of two
         * positive numbers = 0 */
        v = sqrtr( gmul2n(gsub(r,a), -1) );
        if (gsigne(b) < 0) togglesign(v);
        v = gerepileuptoleaf(av, v); av = avma;
        /* v = 0 is impossible */
        u = gerepileuptoleaf(av, gdiv(b, shiftr(v,1)));
      } else {
        u = sqrtr( gmul2n(gadd(r,a), -1) );
        u = gerepileuptoleaf(av, u); av = avma;
        if (!signe(u)) /* possible if a = 0.0, e.g. sqrt(0.e-10+1e-10*I) */
          v = u;
        else
          v = gerepileuptoleaf(av, gdiv(b, shiftr(u,1)));
      }
      gel(y,1) = u;
      gel(y,2) = v; return y;
    }

    case t_PADIC:
      y = Qp_sqrt(x);
      if (!y) pari_err_SQRTN("Qp_sqrt",x);
      return y;

    case t_FFELT: return FF_sqrt(x);

    default:
      av = avma; if (!(y = toser_i(x))) break;
      return gerepilecopy(av, sqrt_ser(y, prec));
  }
  return trans_eval("sqrt",gsqrt,x,prec);
}
/********************************************************************/
/**                                                                **/
/**                          N-th ROOT                             **/
/**                                                                **/
/********************************************************************/
static void
bug_logp(GEN p)
{
  if (!BPSW_psp(p)) pari_err_PRIME("p-adic log",p);
  pari_err_BUG("log_p");
}
/* Let x = 1 mod p and y := (x-1)/(x+1) = 0 (p). Then
 * log(x) = log(1+y) - log(1-y) = 2 \sum_{k odd} y^k / k.
 * palogaux(x) returns the last sum (not multiplied by 2) */
static GEN
palogaux(GEN x)
{
  long i, k, e, pp, t;
  GEN y,s,y2, p = gel(x,2);
  int is2 = absequaliu(p,2);

  y = subiu(gel(x,4), 1);
  if (!signe(y))
  {
    long v = valp(x)+precp(x);
    if (is2) v--;
    return zeropadic(p, v);
  }
  /* optimize t: log(x) = log(x^(p^t)) / p^t */
  e = Z_pval(y, p); /* valp(y) = e >= 1; precp(y) = precp(x)-e */
  if (!e) bug_logp(p);
  if (is2)
    t = sqrt( (double)(precp(x)-e) / e ); /* instead of (2*e) */
  else
    t = sqrt( (double)(precp(x)-e) / (e * (expi(p) + hammingweight(p))) );
  for (i = 0; i < t; i++) x = gpow(x, p, 0);

  y = gdiv(gaddgs(x,-1), gaddgs(x,1));
  e = valp(y); /* > 0 */
  if (e <= 0) bug_logp(p);
  pp = precp(y) + e;
  if (is2) pp--;
  else
  {
    GEN p1;
    for (p1=utoipos(e); abscmpui(pp,p1) > 0; pp++) p1 = mulii(p1, p);
    pp -= 2;
  }
  k = pp/e; if (!odd(k)) k--;
  if (DEBUGLEVEL>5)
    err_printf("logp: [pp,k,e,t] = [%ld,%ld,%ld,%ld]\n",pp,k,e,t);
  if (k > 1)
  {
    y2 = gsqr(y); s = gdivgs(gen_1,k);
    while (k > 2)
    {
      k -= 2;
      s = gadd(gmul(y2,s), gdivgs(gen_1,k));
    }
    y = gmul(s,y);
  }
  if (t) setvalp(y, valp(y) - t);
  return y;
}

GEN
Qp_log(GEN x)
{
  pari_sp av = avma;
  GEN y, p = gel(x,2), a = gel(x,4);

  if (!signe(a)) pari_err_DOMAIN("Qp_log", "argument", "=", gen_0, x);
  y = leafcopy(x); setvalp(y,0);
  if (absequaliu(p,2))
    y = palogaux(gsqr(y));
  else if (gequal1(modii(a, p)))
    y = gmul2n(palogaux(y), 1);
  else
  { /* compute log(x^(p-1)) / (p-1) */
    GEN mod = gel(y,3), p1 = subiu(p,1);
    gel(y,4) = Fp_pow(a, p1, mod);
    p1 = diviiexact(subsi(1,mod), p1); /* 1/(p-1) */
    y = gmul(palogaux(y), shifti(p1,1));
  }
  return gerepileupto(av,y);
}

static GEN Qp_exp_safe(GEN x);

/*compute the p^e th root of x p-adic, assume x != 0 */
static GEN
Qp_sqrtn_ram(GEN x, long e)
{
  pari_sp ltop=avma;
  GEN a, p = gel(x,2), n = powiu(p,e);
  long v = valp(x), va;
  if (v)
  {
    long z;
    v = sdivsi_rem(v, n, &z);
    if (z) return NULL;
    x = leafcopy(x);
    setvalp(x,0);
  }
  /*If p = 2, -1 is a root of 1 in U1: need extra check*/
  if (absequaliu(p, 2) && mod8(gel(x,4)) != 1) return NULL;
  a = Qp_log(x);
  va = valp(a) - e;
  if (va <= 0)
  {
    if (signe(gel(a,4))) return NULL;
    /* all accuracy lost */
    a = cvtop(remii(gel(x,4),p), p, 1);
  }
  else
  {
    setvalp(a, va); /* divide by p^e */
    a = Qp_exp_safe(a);
    if (!a) return NULL;
    /* n=p^e and a^n=z*x where z is a (p-1)th-root of 1.
     * Since z^n=z, we have (a/z)^n = x. */
    a = gdiv(x, powgi(a,subiu(n,1))); /* = a/z = x/a^(n-1)*/
    if (v) setvalp(a,v);
  }
  return gerepileupto(ltop,a);
}

/*compute the nth root of x p-adic p prime with n*/
static GEN
Qp_sqrtn_unram(GEN x, GEN n, GEN *zetan)
{
  pari_sp av;
  GEN Z, a, r, p = gel(x,2);
  long v = valp(x);
  if (v)
  {
    long z;
    v = sdivsi_rem(v,n,&z);
    if (z) return NULL;
  }
  r = cgetp(x); setvalp(r,v);
  Z = NULL; /* -Wall */
  if (zetan) Z = cgetp(x);
  av = avma; a = Fp_sqrtn(gel(x,4), n, p, zetan);
  if (!a) return NULL;
  affii(Zp_sqrtnlift(gel(x,4), n, a, p, precp(x)), gel(r,4));
  if (zetan)
  {
    affii(Zp_sqrtnlift(gen_1, n, *zetan, p, precp(x)), gel(Z,4));
    *zetan = Z;
  }
  avma = av; return r;
}

GEN
Qp_sqrtn(GEN x, GEN n, GEN *zetan)
{
  pari_sp av, tetpil;
  GEN q, p;
  long e;
  if (absequaliu(n, 2))
  {
    if (zetan) *zetan = gen_m1;
    if (signe(n) < 0) x = ginv(x);
    return Qp_sqrt(x);
  }
  av = avma; p = gel(x,2);
  if (!signe(gel(x,4)))
  {
    if (signe(n) < 0) pari_err_INV("Qp_sqrtn", x);
    q = divii(addis(n, valp(x)-1), n);
    if (zetan) *zetan = gen_1;
    avma = av; return zeropadic(p, itos(q));
  }
  /* treat the ramified part using logarithms */
  e = Z_pvalrem(n, p, &q);
  if (e) { x = Qp_sqrtn_ram(x,e); if (!x) return NULL; }
  if (is_pm1(q))
  { /* finished */
    if (signe(q) < 0) x = ginv(x);
    x = gerepileupto(av, x);
    if (zetan)
      *zetan = (e && absequaliu(p, 2))? gen_m1 /*-1 in Q_2*/
                                   : gen_1;
    return x;
  }
  tetpil = avma;
  /* use hensel lift for unramified case */
  x = Qp_sqrtn_unram(x, q, zetan);
  if (!x) return NULL;
  if (zetan)
  {
    GEN *gptr[2];
    if (e && absequaliu(p, 2))/*-1 in Q_2*/
    {
      tetpil = avma; x = gcopy(x); *zetan = gneg(*zetan);
    }
    gptr[0] = &x; gptr[1] = zetan;
    gerepilemanysp(av,tetpil,gptr,2);
    return x;
  }
  return gerepile(av,tetpil,x);
}

GEN
sqrtnint(GEN a, long n)
{
  pari_sp ltop = avma;
  GEN x, b, q;
  long s, k, e;
  const ulong nm1 = n - 1;
  if (typ(a) != t_INT) pari_err_TYPE("sqrtnint",a);
  if (n <= 0) pari_err_DOMAIN("sqrtnint", "n", "<=", gen_0, stoi(n));
  if (n == 1) return icopy(a);
  s = signe(a);
  if (s < 0) pari_err_DOMAIN("sqrtnint", "x", "<", gen_0, a);
  if (!s) return gen_0;
  if (lgefint(a) == 3) return utoi(usqrtn(itou(a), n));
  e = expi(a); k = e/(2*n);
  if (k == 0)
  {
    long flag;
    if (n > e) {avma = ltop; return gen_1;}
    flag = cmpii(a, powuu(3, n)); avma = ltop;
    return (flag < 0) ? gen_2: stoi(3);
  }
  if (e < n*BITS_IN_LONG - 1)
  {
    ulong xs, qs;
    b = itor(a, (2*e < n*BITS_IN_LONG)? DEFAULTPREC: MEDDEFAULTPREC);
    x = mpexp(divru(logr_abs(b), n));
    xs = itou(floorr(x)) + 1; /* >= a^(1/n) */
    for(;;) {
      q = divii(a, powuu(xs, nm1));
      if (lgefint(q) > 3) break;
      qs = itou(q); if (qs >= xs) break;
      xs -= (xs - qs + nm1)/n;
    }
    return utoi(xs);
  }
  b = addui(1, shifti(a, -n*k));
  x = shifti(addui(1, sqrtnint(b, n)), k);
  q = divii(a, powiu(x, nm1));
  while (cmpii(q, x) < 0) /* a priori one iteration, no GC necessary */
  {
    x = subii(x, divis(addui(nm1, subii(x, q)), n));
    q = divii(a, powiu(x, nm1));
  }
  return gerepileuptoleaf(ltop, x);
}

ulong
usqrtn(ulong a, ulong n)
{
  ulong x, s, q;
  const ulong nm1 = n - 1;
  if (!n) pari_err_DOMAIN("sqrtnint", "n", "=", gen_0, utoi(n));
  if (n == 1 || a == 0) return a;
  s = 1 + expu(a)/n; x = 1UL << s;
  q = (nm1*s >= BITS_IN_LONG)? 0: a >> (nm1*s);
  while (q < x) {
    ulong X;
    x -= (x - q + nm1)/n;
    X = upowuu(x, nm1);
    q = X? a/X: 0;
  }
  return x;
}

static ulong
cubic_prec_mask(long n)
{
  long a = n, i;
  ulong mask = 0;
  for(i = 1;; i++, mask *= 3)
  {
    long c = a%3;
    if (c) mask += 3 - c;
    a = (a+2)/3;
    if (a==1) return mask + upowuu(3, i);
  }
}

/* cubic Newton iteration, |a|^(1/n), assuming a != 0 */
GEN
sqrtnr_abs(GEN a, long n)
{
  pari_sp av;
  GEN x, b;
  long eextra, eold, n1, n2, prec, B, v;
  ulong mask;

  if (n == 1) return mpabs(a);
  if (n == 2) return sqrtr_abs(a);

  prec = realprec(a);
  B = prec2nbits(prec);
  eextra = expu(n)-1;
  n1 = n+1;
  n2 = 2*n; av = avma;
  v = expo(a) / n;
  if (v) a = shiftr(a, -n*v);

  b = rtor(a, DEFAULTPREC);
  x = mpexp(divru(logr_abs(b), n));
  if (prec == DEFAULTPREC)
  {
    if (v) shiftr_inplace(x, v);
    return gerepileuptoleaf(av, x);
  }
  mask = cubic_prec_mask(B + 63);
  eold = 1;
  for(;;)
  { /* reach 64 */
    long enew = eold * 3;
    enew -= mask % 3;
    if (enew > 64) break; /* back up one step */
    mask /= 3;
    eold = enew;
  }
  for(;;)
  {
    long pr, enew = eold * 3;
    GEN y, z;
    enew -= mask % 3;
    mask /= 3;
    pr = nbits2prec(enew + eextra);
    b = rtor(a, pr); setsigne(b,1);
    x = rtor(x, pr);
    y = subrr(powru(x, n), b);
    z = divrr(y, addrr(mulur(n1, y), mulur(n2, b)));
    shiftr_inplace(z,1);
    x = mulrr(x, subsr(1,z));
    if (mask == 1)
    {
      if (v) shiftr_inplace(x, v);
      return gerepileuptoleaf(av, gprec_wtrunc(x,prec));
    }
    eold = enew;
  }
}

static void
shiftc_inplace(GEN z, long d)
{
  shiftr_inplace(gel(z,1), d);
  shiftr_inplace(gel(z,2), d);
}

/* exp(2*Pi*I/n), same iteration as sqrtnr_abs, different initial point */
static GEN
sqrtnof1(ulong n, long prec)
{
  pari_sp av;
  GEN x;
  long eold, n1, n2, B;
  ulong mask;

  B = prec2nbits(prec);
  n1 = n+1;
  n2 = 2*n; av = avma;

  x = expIr(divru(Pi2n(1, LOWDEFAULTPREC), n));
  if (prec == LOWDEFAULTPREC) return gerepileupto(av, x);
  mask = cubic_prec_mask(B + BITS_IN_LONG-1);
  eold = 1;
  for(;;)
  { /* reach BITS_IN_LONG */
    long enew = eold * 3;
    enew -= mask % 3;
    if (enew > BITS_IN_LONG) break; /* back up one step */
    mask /= 3;
    eold = enew;
  }
  for(;;)
  {
    long pr, enew = eold * 3;
    GEN y, z;
    enew -= mask % 3;
    mask /= 3;
    pr = nbits2prec(enew);
    x = cxtofp(x, pr);
    y = gsub(gpowgs(x, n), gen_1);
    z = gdiv(y, gaddgs(gmulsg(n1, y), n2));
    shiftc_inplace(z,1);
    x = gmul(x, gsubsg(1, z));
    if (mask == 1) return gerepilecopy(av, gprec_w(x,prec));
    eold = enew;
  }
}

/* exp(2iPi/d) */
GEN
rootsof1u_cx(ulong n, long prec)
{
  switch(n)
  {
    case 1: return gen_1;
    case 2: return gen_m1;
    case 4: return gen_I();
    case 3: case 6: case 12:
    {
      pari_sp av = avma;
      GEN a = (n == 3)? mkfrac(gen_m1,gen_2): ghalf;
      GEN sq3 = sqrtr_abs(utor(3, prec));
      shiftr_inplace(sq3, -1);
      a = (n == 12)? mkcomplex(sq3, a): mkcomplex(a, sq3);
      return gerepilecopy(av, a);
    }
    case 8:
    {
      pari_sp av = avma;
      GEN sq2 = sqrtr_abs(utor(2, prec));
      shiftr_inplace(sq2,-1);
      return gerepilecopy(av, mkcomplex(sq2, sq2));
    }
  }
  return sqrtnof1(n, prec);
}
/* e(a/b) */
GEN
rootsof1q_cx(long a, long b, long prec)
{
  long g = cgcd(a,b);
  GEN z;
  if (g != 1) { a /= g; b /= g; }
  if (b < 0) { b = -b; a = -a; }
  z = rootsof1u_cx(b, prec);
  if (a < 0) { z = conj_i(z); a = -a; }
  return gpowgs(z, a);
}

/* initializes powers of e(a/b) */
GEN
rootsof1powinit(long a, long b, long prec)
{
  long g = cgcd(a,b);
  if (g != 1) { a /= g; b /= g; }
  if (b < 0) { b = -b; a = -a; }
  a %= b; if (a < 0) a += b;
  return mkvec2(grootsof1(b,prec), mkvecsmall2(a,b));
}
/* T = rootsof1powinit(a,b); return  e(a/b)^c */
GEN
rootsof1pow(GEN T, long c)
{
  GEN vz = gel(T,1), ab = gel(T,2);
  long a = ab[1], b = ab[2]; /* a >= 0, b > 0 */
  c %= b; if (c < 0) c += b;
  a = Fl_mul(a, c, b);
  return gel(vz, a + 1);
}

/* exp(2iPi/d), assume d a t_INT */
GEN
rootsof1_cx(GEN d, long prec)
{
  if (lgefint(d) == 3) return rootsof1u_cx((ulong)d[2], prec);
  return expIr(divri(Pi2n(1,prec), d));
}

GEN
gsqrtn(GEN x, GEN n, GEN *zetan, long prec)
{
  long i, lx, tx;
  pari_sp av;
  GEN y, z;
  if (typ(n)!=t_INT) pari_err_TYPE("sqrtn",n);
  if (!signe(n)) pari_err_DOMAIN("sqrtn", "n", "=", gen_0, n);
  if (is_pm1(n))
  {
    if (zetan) *zetan = gen_1;
    return (signe(n) > 0)? gcopy(x): ginv(x);
  }
  if (zetan) *zetan = gen_0;
  tx = typ(x);
  if (is_matvec_t(tx))
  {
    y = cgetg_copy(x, &lx);
    for (i=1; i<lx; i++) gel(y,i) = gsqrtn(gel(x,i),n,NULL,prec);
    return y;
  }
  av = avma;
  switch(tx)
  {
  case t_INTMOD:
    {
      GEN p = gel(x,1), s;
      z = gen_0;
      y = cgetg(3,t_INTMOD);  gel(y,1) = icopy(p);
      if (zetan) { z = cgetg(3,t_INTMOD); gel(z,1) = gel(y,1); }
      s = Fp_sqrtn(gel(x,2),n,p,zetan);
      if (!s) {
        if (zetan) {avma=av; return gen_0;}
        if (!BPSW_psp(p)) pari_err_PRIME("sqrtn [modulus]",p);
        pari_err_SQRTN("gsqrtn",x);
      }
      gel(y,2) = s;
      if (zetan) { gel(z,2) = *zetan; *zetan = z; }
      return y;
    }

  case t_PADIC:
    y = Qp_sqrtn(x,n,zetan);
    if (!y) {
      if (zetan) return gen_0;
      pari_err_SQRTN("gsqrtn",x);
    }
    return y;

  case t_FFELT: return FF_sqrtn(x,n,zetan);

  case t_INT: case t_FRAC: case t_REAL: case t_COMPLEX:
    i = precision(x); if (i) prec = i;
    if (isint1(x))
      y = real_1(prec);
    else if (gequal0(x))
    {
      long b;
      if (signe(n) < 0) pari_err_INV("gsqrtn",x);
      if (isinexactreal(x))
        b = sdivsi(gexpo(x), n);
      else
        b = -prec2nbits(prec);
      if (typ(x) == t_COMPLEX)
      {
        y = cgetg(3,t_COMPLEX);
        gel(y,1) = gel(y,2) = real_0_bit(b);
      }
      else
        y = real_0_bit(b);
    }
    else
    {
      long nn = itos_or_0(n);
      if (tx == t_INT) { x = itor(x,prec); tx = t_REAL; }
      if (nn > 0 && tx == t_REAL && signe(x) > 0)
        y = sqrtnr(x, nn);
      else
        y = gexp(gdiv(glog(x,prec), n), prec);
      y = gerepileupto(av, y);
    }
    if (zetan) *zetan = rootsof1_cx(n, prec);
    return y;

  case t_QUAD:
    return gsqrtn(quadtofp(x, prec), n, zetan, prec);

  default:
    av = avma; if (!(y = toser_i(x))) break;
    return gerepileupto(av, ser_powfrac(y, ginv(n), prec));
  }
  pari_err_TYPE("sqrtn",x);
  return NULL;/* LCOV_EXCL_LINE */
}

/********************************************************************/
/**                                                                **/
/**                             EXP(X) - 1                         **/
/**                                                                **/
/********************************************************************/
/* exp(|x|) - 1, assume x != 0.
 * For efficiency, x should be reduced mod log(2): if so, we have a < 0 */
GEN
exp1r_abs(GEN x)
{
  long l = realprec(x), a = expo(x), b = prec2nbits(l), L, i, n, m, B;
  GEN y, p2, X;
  pari_sp av;
  double d;

  if (b + a <= 0) return mpabs(x);

  y = cgetr(l); av = avma;
  B = b/3 + BITS_IN_LONG + (BITS_IN_LONG*BITS_IN_LONG)/ b;
  d = a/2.; m = (long)(d + sqrt(d*d + B)); /* >= 0 */
  if (m < (-a) * 0.1) m = 0; /* not worth it */
  L = l + nbits2extraprec(m);
 /* Multiplication is quadratic in this range (l is small, otherwise we
  * use logAGM + Newton). Set Y = 2^(-e-a) x, compute truncated series
  * sum x^k/k!: this costs roughly
  *    m b^2 + sum_{k <= n} (k e + BITS_IN_LONG)^2
  * bit operations with |x| <  2^(1+a), |Y| < 2^(1-e) , m = e+a and b bits of
  * accuracy needed, so
  *    B := (b / 3 + BITS_IN_LONG + BITS_IN_LONG^2 / b) ~ m(m-a)
  * we want b ~ 3 m (m-a) or m~b+a hence
  *     m = min( a/2 + sqrt(a^2/4 + B),  b + a )
  * NB: e ~ (b/3)^(1/2) as b -> oo
  *
  * Truncate the sum at k = n (>= 1), the remainder is
  *   sum_{k >= n+1} Y^k / k! < Y^(n+1) / (n+1)! (1-Y) < Y^(n+1) / n!
  * We want Y^(n+1) / n! <= Y 2^-b, hence -n log_2 |Y| + log_2 n! >= b
  *   log n! ~ (n + 1/2) log(n+1) - (n+1) + log(2Pi)/2,
  * error bounded by 1/6(n+1) <= 1/12. Finally, we want
  * n (-1/log(2) -log_2 |Y| + log_2(n+1)) >= b  */
  b += m;
  d = m-dbllog2(x)-1/M_LN2; /* ~ -log_2 Y - 1/log(2) */
  n = (long)(b / d);
  if (n > 1)
    n = (long)(b / (d + log2((double)n+1))); /* log~constant in small ranges */
  while (n*(d+log2((double)n+1)) < b) n++; /* expect few corrections */

  X = rtor(x,L); shiftr_inplace(X, -m); setsigne(X, 1);
  if (n == 1) p2 = X;
  else
  {
    long s = 0, l1 = nbits2prec((long)(d + n + 16));
    GEN unr = real_1(L);
    pari_sp av2;

    p2 = cgetr(L); av2 = avma;
    for (i=n; i>=2; i--, avma = av2)
    { /* compute X^(n-1)/n! + ... + X/2 + 1 */
      GEN p1, p3;
      setprec(X,l1); p3 = divru(X,i);
      l1 += dvmdsBIL(s - expo(p3), &s); if (l1>L) l1=L;
      setprec(unr,l1); p1 = addrr_sign(unr,1, i == n? p3: mulrr(p3,p2),1);
      setprec(p2,l1); affrr(p1,p2); /* p2 <- 1 + (X/i)*p2 */
    }
    setprec(X,L); p2 = mulrr(X,p2);
  }

  for (i=1; i<=m; i++)
  {
    if (realprec(p2) > L) setprec(p2,L);
    p2 = mulrr(p2, addsr(2,p2));
  }
  affrr_fixlg(p2,y); avma = av; return y;
}

GEN
mpexpm1(GEN x)
{
  const long s = 6;
  long l, sx = signe(x);
  GEN y, z;
  pari_sp av;
  if (!sx) return real_0_bit(expo(x));
  l = realprec(x);
  if (l > maxss(EXPNEWTON_LIMIT, (1L<<s) + 2))
  {
    long e = expo(x);
    if (e < 0) x = rtor(x, l + nbits2extraprec(-e));
    return subrs(mpexp(x), 1);
  }
  if (sx > 0) return exp1r_abs(x);
  /* compute exp(x) * (1 - exp(-x)) */
  av = avma; y = exp1r_abs(x);
  z = addsr(1, y); setsigne(z, -1);
  return gerepileupto(av, divrr(y, z));
}

static GEN serexp(GEN x, long prec);
GEN
gexpm1(GEN x, long prec)
{
  switch(typ(x))
  {
    case t_REAL: return mpexpm1(x);
    case t_COMPLEX: return cxexpm1(x,prec);
    case t_PADIC: return gsubgs(Qp_exp(x), 1);
    default:
    {
      pari_sp av = avma;
      long ey;
      GEN y;
      if (!(y = toser_i(x))) break;
      ey = valp(y);
      if (ey < 0) pari_err_DOMAIN("expm1","valuation", "<", gen_0, x);
      if (gequal0(y)) return gcopy(y);
      if (ey)
        return gerepileupto(av, gsubgs(serexp(y,prec), 1));
      else
      {
        GEN e1 = gexpm1(gel(y,2), prec), e = gaddgs(e1,1);
        y = gmul(e, serexp(serchop0(y),prec));
        gel(y,2) = e1;
        return gerepilecopy(av, y);
      }
    }
  }
  return trans_eval("expm1",gexpm1,x,prec);
}
/********************************************************************/
/**                                                                **/
/**                             EXP(X)                             **/
/**                                                                **/
/********************************************************************/

/* centermod(x, log(2)), set *sh to the quotient */
static GEN
modlog2(GEN x, long *sh)
{
  double d = rtodbl(x), da = fabs(d);
  long q = (long) ((da + (M_LN2/2))/M_LN2);
  if (da > M_LN2 * LONG_MAX)
    pari_err_OVERFLOW("expo()"); /* avoid overflow in  q */
  if (d < 0) q = -q;
  *sh = q;
  if (q) {
    long l = realprec(x) + 1;
    x = subrr(rtor(x,l), mulsr(q, mplog2(l)));
    if (!signe(x)) return NULL;
  }
  return x;
}

static GEN
mpexp_basecase(GEN x)
{
  pari_sp av = avma;
  long sh, l = realprec(x);
  GEN y, z;

  y = modlog2(x, &sh);
  if (!y) { avma = av; return real2n(sh, l); }
  z = addsr(1, exp1r_abs(y));
  if (signe(y) < 0) z = invr(z);
  if (sh) {
    shiftr_inplace(z, sh);
    if (realprec(z) > l) z = rtor(z, l); /* spurious precision increase */
  }
#ifdef DEBUG
{
  GEN t = mplog(z), u = divrr(subrr(x, t),x);
  if (signe(u) && expo(u) > 5-prec2nbits(minss(l,realprec(t))))
    pari_err_BUG("exp");
}
#endif
  return gerepileuptoleaf(av, z); /* NOT affrr, precision often increases */
}

GEN
mpexp(GEN x)
{
  const long s = 6; /*Initial steps using basecase*/
  long i, p, l = realprec(x), sh;
  GEN a, t, z;
  ulong mask;

  if (l <= maxss(EXPNEWTON_LIMIT, (1L<<s) + 2))
  {
    if (!signe(x)) return mpexp0(x);
    return mpexp_basecase(x);
  }
  z = cgetr(l); /* room for result */
  x = modlog2(x, &sh);
  if (!x) { avma = (pari_sp)(z+lg(z)); return real2n(sh, l); }
  constpi(l); /* precompute for later logr_abs() */
  mask = quadratic_prec_mask(prec2nbits(l)+BITS_IN_LONG);
  for(i=0, p=1; i<s+TWOPOTBITS_IN_LONG; i++) { p <<= 1; if (mask & 1) p-=1; mask >>= 1; }
  a = mpexp_basecase(rtor(x, nbits2prec(p)));
  x = addrs(x,1);
  if (realprec(x) < l+EXTRAPRECWORD) x = rtor(x, l+EXTRAPRECWORD);
  a = rtor(a, l+EXTRAPRECWORD); /*append 0s */
  t = NULL;
  for(;;)
  {
    p <<= 1; if (mask & 1) p--;
    mask >>= 1;
    setprec(x, nbits2prec(p));
    setprec(a, nbits2prec(p));
    t = mulrr(a, subrr(x, logr_abs(a))); /* a (x - log(a)) */
    if (mask == 1) break;
    affrr(t, a); avma = (pari_sp)a;
  }
  affrr(t,z);
  if (sh) shiftr_inplace(z, sh);
  avma = (pari_sp)z; return z;
}

static long
Qp_exp_prec(GEN x)
{
  long k, e = valp(x), n = e + precp(x);
  GEN p = gel(x,2);
  int is2 = absequaliu(p,2);
  if (e < 1 || (e == 1 && is2)) return -1;
  if (is2)
  {
    n--; e--; k = n/e;
    if (n%e == 0) k--;
  }
  else
  { /* e > 0, n > 0 */
    GEN r, t = subiu(p, 1);
    k = itos(dvmdii(subiu(muliu(t,n), 1), subiu(muliu(t,e), 1), &r));
    if (!signe(r)) k--;
  }
  return k;
}

static GEN
Qp_exp_safe(GEN x)
{
  long k;
  pari_sp av;
  GEN y;

  if (gequal0(x)) return gaddgs(x,1);
  k = Qp_exp_prec(x);
  if (k < 0) return NULL;
  av = avma;
  for (y=gen_1; k; k--) y = gaddsg(1, gdivgs(gmul(y,x), k));
  return gerepileupto(av, y);
}

GEN
Qp_exp(GEN x)
{
  GEN y = Qp_exp_safe(x);
  if (!y) pari_err_DOMAIN("gexp(t_PADIC)","argument","",gen_0,x);
  return y;
}

static GEN
cos_p(GEN x)
{
  long k;
  pari_sp av;
  GEN x2, y;

  if (gequal0(x)) return gaddgs(x,1);
  k = Qp_exp_prec(x);
  if (k < 0) return NULL;
  av = avma; x2 = gsqr(x);
  if (k & 1) k--;
  for (y=gen_1; k; k-=2)
  {
    GEN t = gdiv(gmul(y,x2), muluu(k, k-1));
    y = gsubsg(1, t);
  }
  return gerepileupto(av, y);
}
static GEN
sin_p(GEN x)
{
  long k;
  pari_sp av;
  GEN x2, y;

  if (gequal0(x)) return gcopy(x);
  k = Qp_exp_prec(x);
  if (k < 0) return NULL;
  av = avma; x2 = gsqr(x);
  if (k & 1) k--;
  for (y=gen_1; k; k-=2)
  {
    GEN t = gdiv(gmul(y,x2), muluu(k, k+1));
    y = gsubsg(1, t);
  }
  return gerepileupto(av, gmul(y, x));
}

static GEN
cxexp(GEN x, long prec)
{
  GEN r, p1, p2, y = cgetg(3,t_COMPLEX);
  pari_sp av = avma, tetpil;
  long l;
  l = precision(x); if (l > prec) prec = l;
  r = gexp(gel(x,1),prec);
  if (gequal0(r)) { gel(y,1) = r; gel(y,2) = r; return y; }
  gsincos(gel(x,2),&p2,&p1,prec);
  tetpil = avma;
  gel(y,1) = gmul(r,p1);
  gel(y,2) = gmul(r,p2);
  gerepilecoeffssp(av,tetpil,y+1,2);
  return y;
}

/* given a t_SER x^v s(x), with s(0) != 0, return x^v(s - s(0)), shallow */
GEN
serchop0(GEN s)
{
  long i, l = lg(s);
  GEN y;
  if (l == 2) return s;
  if (l == 3 && isexactzero(gel(s,2))) return s;
  y = cgetg(l, t_SER); y[1] = s[1];
  gel(y,2) = gen_0; for (i=3; i <l; i++) gel(y,i) = gel(s,i);
  return normalize(y);
}

GEN
serchop_i(GEN s, long n)
{
  long i, m, l = lg(s);
  GEN y;
  if (l == 2 || (l == 3 && isexactzero(gel(s,2))))
  {
    if (valp(s) < n) { s = shallowcopy(s); setvalp(s,n); }
    return s;
  }
  m = n - valp(s); if (m < 0) return s;
  if (l-m <= 2) return zeroser(varn(s), n);
  y = cgetg(l-m, t_SER); y[1] = s[1]; setvalp(y, valp(y)+m);
  for (i=m+2; i < l; i++) gel(y,i-m) = gel(s,i);
  return normalize(y);
}
GEN
serchop(GEN s, long n)
{
  pari_sp av = avma;
  if (typ(s) != t_SER) pari_err_TYPE("serchop",s);
  return gerepilecopy(av, serchop_i(s,n));
}

static GEN
serexp(GEN x, long prec)
{
  pari_sp av;
  long i,j,lx,ly,ex,mi;
  GEN p1,y,xd,yd;

  ex = valp(x);
  if (ex < 0) pari_err_DOMAIN("exp","valuation", "<", gen_0, x);
  if (gequal0(x)) return gaddsg(1,x);
  lx = lg(x);
  if (ex)
  {
    ly = lx+ex; y = cgetg(ly,t_SER);
    mi = lx-1; while (mi>=3 && isrationalzero(gel(x,mi))) mi--;
    mi += ex-2;
    y[1] = evalsigne(1) | _evalvalp(0) | evalvarn(varn(x));
    /* zd[i] = coefficient of X^i in z */
    xd = x+2-ex; yd = y+2; ly -= 2;
    gel(yd,0) = gen_1;
    for (i=1; i<ex; i++) gel(yd,i) = gen_0;
    for (   ; i<ly; i++)
    {
      av = avma; p1 = gen_0;
      for (j=ex; j<=minss(i,mi); j++)
        p1 = gadd(p1, gmulgs(gmul(gel(xd,j),gel(yd,i-j)),j));
      gel(yd,i) = gerepileupto(av, gdivgs(p1,i));
    }
    return y;
  }
  av = avma;
  return gerepileupto(av, gmul(gexp(gel(x,2),prec), serexp(serchop0(x),prec)));
}

GEN
gexp(GEN x, long prec)
{
  switch(typ(x))
  {
    case t_REAL: return mpexp(x);
    case t_COMPLEX: return cxexp(x,prec);
    case t_PADIC: return Qp_exp(x);
    default:
    {
      pari_sp av = avma;
      GEN y;
      if (!(y = toser_i(x))) break;
      return gerepileupto(av, serexp(y,prec));
    }
  }
  return trans_eval("exp",gexp,x,prec);
}

/********************************************************************/
/**                                                                **/
/**                           AGM(X, Y)                            **/
/**                                                                **/
/********************************************************************/
static int
agmr_gap(GEN a, GEN b, long L)
{
  GEN d = subrr(b, a);
  return (signe(d) && expo(d) - expo(b) >= L);
}
/* assume x > 0 */
static GEN
agm1r_abs(GEN x)
{
  long l = realprec(x), L = 5-prec2nbits(l);
  GEN a1, b1, y = cgetr(l);
  pari_sp av = avma;

  a1 = addrr(real_1(l), x); shiftr_inplace(a1, -1);
  b1 = sqrtr_abs(x);
  while (agmr_gap(a1,b1,L))
  {
    GEN a = a1;
    a1 = addrr(a,b1); shiftr_inplace(a1, -1);
    b1 = sqrtr_abs(mulrr(a,b1));
  }
  affrr_fixlg(a1,y); avma = av; return y;
}

struct agmcx_gap_t { long L, ex, cnt; };

static void
agmcx_init(GEN x, long *prec, struct agmcx_gap_t *S)
{
  long l = precision(x);
  if (l) *prec = l;
  S->L = 1-prec2nbits(*prec);
  S->cnt = 0;
  S->ex = LONG_MAX;
}

static long
agmcx_a_b(GEN x, GEN *a1, GEN *b1, long prec)
{
  long rotate = 0;
  if (gsigne(real_i(x))<0)
  { /* Rotate by +/-Pi/2, so that the choice of the principal square
     * root gives the optimal AGM. So a1 = +/-I*a1, b1=sqrt(-x). */
    if (gsigne(imag_i(x))<0) { *a1=mulcxI(*a1);  rotate=-1; }
    else                     { *a1=mulcxmI(*a1); rotate=1; }
    x = gneg(x);
  }
  *b1 = gsqrt(x, prec);
  return rotate;
}
/* return 0 if we must stop the AGM loop (a=b or a ~ b), 1 otherwise */
static int
agmcx_gap(GEN a, GEN b, struct agmcx_gap_t *S)
{
  GEN d = gsub(b, a);
  long ex = S->ex;
  S->ex = gexpo(d);
  if (gequal0(d) || S->ex - gexpo(b) < S->L) return 0;
  /* if (S->ex >= ex) we're no longer making progress; twice in a row */
  if (S->ex < ex) S->cnt = 0;
  else
    if (S->cnt++) return 0;
  return 1;
}
static GEN
agm1cx(GEN x, long prec)
{
  struct agmcx_gap_t S;
  GEN a1, b1;
  pari_sp av = avma;
  long rotate;
  agmcx_init(x, &prec, &S);
  a1 = gtofp(gmul2n(gadd(real_1(prec), x), -1), prec);
  rotate = agmcx_a_b(x, &a1, &b1, prec);
  while (agmcx_gap(a1,b1,&S))
  {
    GEN a = a1;
    a1 = gmul2n(gadd(a,b1),-1);
    b1 = gsqrt(gmul(a,b1), prec);
  }
  if (rotate) a1 = rotate>0 ? mulcxI(a1):mulcxmI(a1);
  return gerepilecopy(av,a1);
}

GEN
zellagmcx(GEN a0, GEN b0, GEN r, GEN t, long prec)
{
  struct agmcx_gap_t S;
  pari_sp av = avma;
  GEN x = gdiv(a0, b0), a1, b1;
  long rotate;
  agmcx_init(x, &prec, &S);
  a1 = gtofp(gmul2n(gadd(real_1(prec), x), -1), prec);
  r = gsqrt(gdiv(gmul(a1,gaddgs(r, 1)),gadd(r, x)), prec);
  t = gmul(r, t);
  rotate = agmcx_a_b(x, &a1, &b1, prec);
  while (agmcx_gap(a1,b1,&S))
  {
    GEN a = a1, b = b1;
    a1 = gmul2n(gadd(a,b),-1);
    b1 = gsqrt(gmul(a,b), prec);
    r = gsqrt(gdiv(gmul(a1,gaddgs(r, 1)),gadd(gmul(b, r), a )), prec);
    t = gmul(r, t);
  }
  if (rotate) a1 = rotate>0 ? mulcxI(a1):mulcxmI(a1);
  a1 = gmul(a1, b0);
  t = gatan(gdiv(a1,t), prec);
  /* send t to the fundamental domain if necessary */
  if (gsigne(real_i(t))<0) t = gadd(t, mppi(prec));
  return gerepileupto(av,gdiv(t,a1));
}

static long
ser_cmp_expo(GEN A, GEN B)
{
  long e = -(long)HIGHEXPOBIT, d = valp(B) - valp(A);
  long i, la = lg(A), v = varn(B);
  for (i = 2; i < la; i++)
  {
    GEN a = gel(A,i), b;
    long ei;
    if (isexactzero(a)) continue;
    b = polcoef_i(B, i-2 + d, v);
    ei = gexpo(a);
    if (!isexactzero(b)) ei -= gexpo(b);
    e = maxss(e, ei);
  }
  return e;
}

static GEN
ser_agm1(GEN y, long prec)
{
  GEN a1 = y, b1 = gen_1;
  long l = lg(y)-2, l2 = 6-prec2nbits(prec), eold = LONG_MAX;
  for(;;)
  {
    GEN a = a1, p1;
    a1 = gmul2n(gadd(a,b1),-1);
    b1 = gsqrt(gmul(a,b1), prec);
    p1 = gsub(b1,a1);
    if (isinexactreal(p1))
    {
      long e = ser_cmp_expo(p1, b1);
      if (e < l2 || e >= eold) break;
      eold = e;
    }
    else
    {
      long ep = valp(p1)-valp(b1);
      if (ep >= l && gequal0(p1)) break;
    }
  }
  return a1;
}

/* agm(1,x) */
static GEN
agm1(GEN x, long prec)
{
  GEN y;
  pari_sp av;

  if (gequal0(x)) return gcopy(x);
  switch(typ(x))
  {
    case t_INT:
      if (!is_pm1(x)) break;
      return (signe(x) > 0)? real_1(prec): real_0(prec);

    case t_REAL: return signe(x) > 0? agm1r_abs(x): agm1cx(x, prec);

    case t_COMPLEX:
      if (gequal0(gel(x,2))) return agm1(gel(x,1), prec);
      return agm1cx(x, prec);

    case t_PADIC:
    {
      GEN a1 = x, b1 = gen_1;
      long l = precp(x);
      av = avma;
      for(;;)
      {
        GEN a = a1, p1;
        long ep;
        a1 = gmul2n(gadd(a,b1),-1);
        a = gmul(a,b1);
        b1 = Qp_sqrt(a); if (!b1) pari_err_SQRTN("Qp_sqrt",a);
        p1 = gsub(b1,a1); ep = valp(p1)-valp(b1);
        if (ep<=0) { b1 = gneg_i(b1); p1 = gsub(b1,a1); ep=valp(p1)-valp(b1); }
        if (ep >= l || gequal0(p1)) return gerepilecopy(av,a1);
      }
    }

    default:
      av = avma; if (!(y = toser_i(x))) break;
      return gerepilecopy(av, ser_agm1(y, prec));
  }
  return trans_eval("agm",agm1,x,prec);
}

GEN
agm(GEN x, GEN y, long prec)
{
  pari_sp av;
  if (is_matvec_t(typ(y)))
  {
    if (is_matvec_t(typ(x))) pari_err_TYPE2("agm",x,y);
    swap(x, y);
  }
  if (gequal0(y)) return gcopy(y);
  av = avma;
  return gerepileupto(av, gmul(y, agm1(gdiv(x,y), prec)));
}

/********************************************************************/
/**                                                                **/
/**                             LOG(X)                             **/
/**                                                                **/
/********************************************************************/
/* atanh(u/v) using binary splitting */
static GEN
atanhQ_split(ulong u, ulong v, long prec)
{
  long i, nmax;
  GEN u2 = sqru(u), v2 = sqru(v);
  double d = ((double)v) / u;
  struct abpq_res R;
  struct abpq A;
  /* satisfies (2n+1) (v/u)^2n > 2^bitprec */
  nmax = (long)(prec2nbits(prec) / (2*log2(d)));
  abpq_init(&A, nmax);
  A.a[0] = A.b[0] = gen_1;
  A.p[0] = utoipos(u);
  A.q[0] = utoipos(v);
  for (i = 1; i <= nmax; i++)
  {
    A.a[i] = gen_1;
    A.b[i] = utoipos((i<<1)+1);
    A.p[i] = u2;
    A.q[i] = v2;
  }
  abpq_sum(&R, 0, nmax, &A);
  return rdivii(R.T, mulii(R.B,R.Q),prec);
}
/* log(2) = 10*atanh(1/17)+4*atanh(13/499); faster than logagmr_abs()
 * and Pi/2M(1,4/2^n) ~ n log(2) */
static GEN
log2_split(long prec)
{
  GEN u = atanhQ_split(1, 17, prec);
  GEN v = atanhQ_split(13, 499, prec);
  shiftr_inplace(v, 2);
  return addrr(mulur(10, u), v);
}
GEN
constlog2(long prec)
{
  pari_sp av;
  GEN tmp;
  if (glog2 && realprec(glog2) >= prec) return glog2;

  tmp = cgetr_block(prec);
  av = avma;
  affrr(log2_split(prec+EXTRAPRECWORD), tmp);
  swap_clone(&glog2,tmp);
  avma = av; return glog2;
}

GEN
mplog2(long prec) { return rtor(constlog2(prec), prec); }

/* dont check that q != 2^expo(q), done in logr_abs */
static GEN
logagmr_abs(GEN q)
{
  long prec = realprec(q), e = expo(q), lim;
  GEN z = cgetr(prec), y, Q, _4ovQ;
  pari_sp av = avma;

  incrprec(prec);
  lim = prec2nbits(prec) >> 1;
  Q = rtor(q,prec);
  shiftr_inplace(Q,lim-e); setsigne(Q,1);

  _4ovQ = invr(Q); shiftr_inplace(_4ovQ, 2); /* 4/Q */
  /* Pi / 2agm(1, 4/Q) ~ log(Q), q = Q * 2^(e-lim) */
  y = divrr(Pi2n(-1, prec), agm1r_abs(_4ovQ));
  y = addrr(y, mulsr(e - lim, mplog2(prec)));
  affrr_fixlg(y, z); avma = av; return z;
}

/* sum_{k >= 0} y^(2k+1) / (2k+1), y close to 0 */
static GEN
logr_aux(GEN y)
{
  long k, L = realprec(y); /* should be ~ l+1 - (k-2) */
  /* log(x) = log(1+y) - log(1-y) = 2 sum_{k odd} y^k / k
   * Truncate the sum at k = 2n+1, the remainder is
   *   2 sum_{k >= 2n+3} y^k / k < 2y^(2n+3) / (2n+3)(1-y) < y^(2n+3)
   * We want y^(2n+3) < y 2^(-prec2nbits(L)), hence
   *   n+1 > -prec2nbits(L) /-log_2(y^2) */
  double d = -2*dbllog2r(y); /* ~ -log_2(y^2) */
  k = (long)(2*(prec2nbits(L) / d));
  k |= 1;
  if (k >= 3)
  {
    GEN T, S = cgetr(L), y2 = sqrr(y), unr = real_1(L);
    pari_sp av = avma;
    long s = 0, incs = (long)d, l1 = nbits2prec((long)d);
    setprec(S,  l1);
    setprec(unr,l1); affrr(divru(unr,k), S);
    for (k -= 2;; k -= 2) /* k = 2n+1, ..., 1 */
    { /* S = y^(2n+1-k)/(2n+1) + ... + 1 / k */
      setprec(y2, l1); T = mulrr(S,y2);
      if (k == 1) break;

      l1 += dvmdsBIL(s + incs, &s); if (l1>L) l1=L;
      setprec(S, l1);
      setprec(unr,l1);
      affrr(addrr(divru(unr, k), T), S); avma = av;
    }
    /* k = 1 special-cased for eficiency */
    y = mulrr(y, addsr(1,T)); /* = log(X)/2 */
  }
  return y;
}
/*return log(|x|), assuming x != 0 */
GEN
logr_abs(GEN X)
{
  long EX, L, m, k, a, b, l = realprec(X);
  GEN z, x, y;
  ulong u;
  double d;

 /* Assuming 1 < x < 2, we want delta = x-1, 1-x/2, 1-1/x, or 2/x-1 small.
  * We have 2/x-1 > 1-x/2, 1-1/x < x-1. So one should be choosing between
  * 1-1/x and 1-x/2 ( crossover sqrt(2), worse ~ 0.29 ). To avoid an inverse,
  * we choose between x-1 and 1-x/2 ( crossover 4/3, worse ~ 0.33 ) */
  EX = expo(X);
  u = uel(X,2);
  k = 2;
  if (u > (~0UL / 3) * 2) { /* choose 1-x/2 */
    EX++; u = ~u;
    while (!u && ++k < l) { u = uel(X,k); u = ~u; }
  } else { /* choose x - 1 */
    u &= ~HIGHBIT; /* u - HIGHBIT, assuming HIGHBIT set */
    while (!u && ++k < l) u = uel(X,k);
  }
  if (k == l) return EX? mulsr(EX, mplog2(l)): real_0(l);
  a = prec2nbits(k) + bfffo(u); /* ~ -log2 |1-x| */
  L = l+1;
  b = prec2nbits(L - (k-2)); /* take loss of accuracy into account */
  if (b > 24*a*log2(L) &&
      prec2nbits(l) > prec2nbits(LOGAGM_LIMIT)) return logagmr_abs(X);

  z = cgetr(EX? l: l - (k-2));

 /* Multiplication is quadratic in this range (l is small, otherwise we
  * use AGM). Set Y = x^(1/2^m), y = (Y - 1) / (Y + 1) and compute truncated
  * series sum y^(2k+1)/(2k+1): the costs is less than
  *    m b^2 + sum_{k <= n} ((2k+1) e + BITS_IN_LONG)^2
  * bit operations with |x-1| <  2^(1-a), |Y| < 2^(1-e) , m = e-a and b bits of
  * accuracy needed (+ BITS_IN_LONG since bit accuracies increase by
  * increments of BITS_IN_LONG), so
  * 4n^3/3 e^2 + n^2 2e BITS_IN_LONG+ n BITS_IN_LONG ~ m b^2, with n ~ b/2e
  * or b/6e + BITS_IN_LONG/2e + BITS_IN_LONG/2be ~ m
  *    B := (b / 6 + BITS_IN_LONG/2 + BITS_IN_LONG^2 / 2b) ~ m(m+a)
  *     m = min( -a/2 + sqrt(a^2/4 + B),  b - a )
  * NB: e ~ (b/6)^(1/2) as b -> oo
  * Instead of the above pessimistic estimate for the cost of the sum, use
  * optimistic estimate (BITS_IN_LONG -> 0) */
  d = -a/2.; m = (long)(d + sqrt(d*d + b/6)); /* >= 0 */

  if (m > b-a) m = b-a;
  if (m < 0.2*a) m = 0; else L += nbits2extraprec(m);
  x = rtor(X,L);
  setsigne(x,1); shiftr_inplace(x,-EX);
  /* 2/3 < x < 4/3 */
  for (k=1; k<=m; k++) x = sqrtr_abs(x);

  y = divrr(subrs(x,1), addrs(x,1)); /* = (x-1) / (x+1), close to 0 */
  y = logr_aux(y); /* log(1+y) - log(1-y) = log(x) */
  shiftr_inplace(y, m + 1);
  if (EX) y = addrr(y, mulsr(EX, mplog2(l+1)));
  affrr_fixlg(y, z); avma = (pari_sp)z; return z;
}

/* assume Im(q) != 0 and precision(q) >= prec. Compute log(q) with accuracy
 * prec [disregard input accuracy] */
GEN
logagmcx(GEN q, long prec)
{
  GEN z = cgetc(prec), y, Q, a, b;
  long lim, e, ea, eb;
  pari_sp av = avma;
  int neg = 0;

  incrprec(prec);
  if (gsigne(gel(q,1)) < 0) { q = gneg(q); neg = 1; }
  lim = prec2nbits(prec) >> 1;
  Q = gtofp(q, prec);
  a = gel(Q,1);
  b = gel(Q,2);
  if (gequal0(a)) {
    affrr_fixlg(logr_abs(b), gel(z,1));
    y = Pi2n(-1, prec);
    if (signe(b) < 0) setsigne(y, -1);
    affrr_fixlg(y, gel(z,2)); avma = av; return z;
  }
  ea = expo(a);
  eb = expo(b);
  e = ea <= eb ? lim - eb : lim - ea;
  shiftr_inplace(a, e);
  shiftr_inplace(b, e);

  /* Pi / 2agm(1, 4/Q) ~ log(Q), q = Q * 2^e */
  y = gdiv(Pi2n(-1, prec), agm1cx( gdivsg(4, Q), prec ));
  a = gel(y,1);
  b = gel(y,2);
  a = addrr(a, mulsr(-e, mplog2(prec)));
  if (realprec(a) <= LOWDEFAULTPREC) a = real_0_bit(expo(a));
  if (neg) b = gsigne(b) <= 0? gadd(b, mppi(prec))
                             : gsub(b, mppi(prec));
  affrr_fixlg(a, gel(z,1));
  affrr_fixlg(b, gel(z,2)); avma = av; return z;
}

GEN
mplog(GEN x)
{
  if (signe(x)<=0) pari_err_DOMAIN("mplog", "argument", "<=", gen_0, x);
  return logr_abs(x);
}

/* pe = p^e, p prime, 0 < x < pe a t_INT coprime to p. Return the (p-1)-th
 * root of 1 in (Z/pe)^* congruent to x mod p, resp x mod 4 if p = 2.
 * Simplified form of Zp_sqrtnlift: 1/(p-1) is trivial to compute */
GEN
Zp_teichmuller(GEN x, GEN p, long e, GEN pe)
{
  GEN q, z, p1;
  pari_sp av;
  ulong mask;
  if (absequaliu(p,2)) return (mod4(x) & 2)? subiu(pe,1): gen_1;
  if (e == 1) return icopy(x);
  av = avma;
  p1 = subiu(p, 1);
  mask = quadratic_prec_mask(e);
  q = p; z = remii(x, p);
  while (mask > 1)
  { /* Newton iteration solving z^{1 - p} = 1, z = x (mod p) */
    GEN w, t, qold = q;
    if (mask <= 3) /* last iteration */
      q = pe;
    else
    {
      q = sqri(q);
      if (mask & 1) q = diviiexact(q, p);
    }
    mask >>= 1;
    /* q <= qold^2 */
    if (lgefint(q) == 3)
    {
      ulong Z = uel(z,2), Q = uel(q,2), P1 = uel(p1,2);
      ulong W = (Q-1) / P1; /* -1/(p-1) + O(qold) */
      ulong T = Fl_mul(W, Fl_powu(Z,P1,Q) - 1, Q);
      Z = Fl_mul(Z, 1 + T, Q);
      z = utoi(Z);
    }
    else
    {
      w = diviiexact(subiu(qold,1),p1); /* -1/(p-1) + O(qold) */
      t = Fp_mul(w, subiu(Fp_pow(z,p1,q), 1), q);
      z = Fp_mul(z, addui(1,t), q);
    }
  }
  return gerepileuptoint(av, z);
}

GEN
teichmullerinit(long p, long n)
{
  GEN t, pn, g, v;
  ulong gp, tp;
  long a, m;

  if (p == 2) return mkvec(gen_1);
  if (!uisprime(p)) pari_err_PRIME("teichmullerinit",utoipos(p));

  m = p >> 1; /* (p-1)/2 */
  tp= gp= pgener_Fl(p); /* order (p-1), gp^m = -1 */
  pn = powuu(p, n);
  v = cgetg(p, t_VEC);
  t = g = Zp_teichmuller(utoipos(gp), utoipos(p), n, pn);
  gel(v, 1) = gen_1;
  gel(v, p-1) = subiu(pn,1);
  for (a = 1; a < m; a++)
  {
    gel(v, tp) = t;
    gel(v, p - tp) = Fp_neg(t, pn); /* g^(m+a) = -g^a */
    if (a < m-1)
    {
      t = Fp_mul(t, g, pn); /* g^(a+1) */
      tp = Fl_mul(tp, gp, p); /* t mod p  */
    }
  }
  return v;
}

/* tab from teichmullerinit or NULL */
GEN
teichmuller(GEN x, GEN tab)
{
  GEN p, q, y, z;
  long n, tx = typ(x);

  if (!tab)
  {
    if (tx == t_VEC && lg(x) == 3)
    {
      p = gel(x,1);
      q = gel(x,2);
      if (typ(p) == t_INT && typ(q) == t_INT)
        return teichmullerinit(itos(p), itos(q));
    }
  }
  else if (typ(tab) != t_VEC) pari_err_TYPE("teichmuller",tab);
  if (tx!=t_PADIC) pari_err_TYPE("teichmuller",x);
  z = gel(x,4);
  if (!signe(z)) return gcopy(x);
  p = gel(x,2);
  q = gel(x,3);
  n = precp(x);
  y = cgetg(5,t_PADIC);
  y[1] = evalprecp(n) | _evalvalp(0);
  gel(y,2) = icopy(p);
  gel(y,3) = icopy(q);
  if (tab)
  {
    ulong pp = itou_or_0(p);
    if (lg(tab) != (long)pp) pari_err_TYPE("teichmuller",tab);
    z = gel(tab, umodiu(z, pp));
    if (typ(z) != t_INT) pari_err_TYPE("teichmuller",tab);
    z = remii(z, q);
  }
  else
    z = Zp_teichmuller(z, p, n, q);
  gel(y,4) = z;
  return y;
}
GEN
teich(GEN x) { return teichmuller(x, NULL); }

GEN
glog(GEN x, long prec)
{
  pari_sp av, tetpil;
  GEN y, p1;
  long l;

  switch(typ(x))
  {
    case t_REAL:
      if (signe(x) >= 0)
      {
        if (!signe(x)) pari_err_DOMAIN("log", "argument", "=", gen_0, x);
        return logr_abs(x);
      }
      retmkcomplex(logr_abs(x), mppi(realprec(x)));

    case t_FRAC:
    {
      GEN a, b;
      long e1, e2;
      av = avma;
      a = gel(x,1);
      b = gel(x,2);
      e1 = expi(subii(a,b)); e2 = expi(b);
      if (e2 > e1) prec += nbits2nlong(e2 - e1);
      x = fractor(x, prec);
      return gerepileupto(av, glog(x, prec));
    }
    case t_COMPLEX:
      if (ismpzero(gel(x,2))) return glog(gel(x,1), prec);
      l = precision(x); if (l > prec) prec = l;
      if (ismpzero(gel(x,1)))
      {
        GEN a = gel(x,2), b;
        av = avma; b = Pi2n(-1,prec);
        if (gsigne(a) < 0) { setsigne(b, -1); a = gabs(a,prec); }
        a = isint1(a) ? gen_0: glog(a,prec);
        return gerepilecopy(av, mkcomplex(a, b));
      }
      if (prec >= LOGAGMCX_LIMIT) return logagmcx(x, prec);
      y = cgetg(3,t_COMPLEX);
      gel(y,2) = garg(x,prec);
      av = avma; p1 = glog(cxnorm(x),prec); tetpil = avma;
      gel(y,1) = gerepile(av,tetpil,gmul2n(p1,-1)); return y;

    case t_PADIC: return Qp_log(x);
    default:
      av = avma; if (!(y = toser_i(x))) break;
      if (!signe(y)) pari_err_DOMAIN("log", "argument", "=", gen_0, x);
      if (valp(y)) pari_err_DOMAIN("log", "series valuation", "!=", gen_0, x);
      p1 = integser(gdiv(derivser(y), y)); /* log(y)' = y'/y */
      if (!gequal1(gel(y,2))) p1 = gadd(p1, glog(gel(y,2),prec));
      return gerepileupto(av, p1);
  }
  return trans_eval("log",glog,x,prec);
}

static GEN
mplog1p(GEN x)
{
  long ex, a, b, l, L;
  if (!signe(x)) return rcopy(x);
  ex = expo(x); if (ex >= 0) return glog(addrs(x,1), 0);
  a = -ex;
  b = realprec(x); L = b+1;
  if (b > a*log2(L) && prec2nbits(b) > prec2nbits(LOGAGM_LIMIT))
  {
    x = addrs(x,1); l = b + nbits2extraprec(a);
    if (realprec(x) < l) x = rtor(x,l);
    return logagmr_abs(x);
  }
  x = rtor(x, L);
  x = logr_aux(divrr(x, addrs(x,2)));
  if (realprec(x) > b) fixlg(x, b);
  shiftr_inplace(x,1); return x;
}

static GEN log1p_i(GEN x, long prec);
static GEN
cxlog1p(GEN x, long prec)
{
  pari_sp av;
  GEN z, a, b = gel(x,2);
  long l;
  if (ismpzero(b)) return log1p_i(gel(x,1), prec);
  l = precision(x); if (l > prec) prec = l;
  if (prec >= LOGAGMCX_LIMIT) return logagmcx(gaddgs(x,1), prec);
  a = gel(x,1);
  z = cgetg(3,t_COMPLEX); av = avma;
  a = gadd(gadd(gmul2n(a,1), gsqr(a)), gsqr(b));
  a = log1p_i(a, prec); shiftr_inplace(a,-1);
  gel(z,1) = gerepileupto(av, a);
  gel(z,2) = garg(gaddgs(x,1),prec); return z;
}
static GEN
log1p_i(GEN x, long prec)
{
  switch(typ(x))
  {
    case t_REAL: return mplog1p(x);
    case t_COMPLEX: return cxlog1p(x, prec);
    case t_PADIC: return Qp_log(gaddgs(x,1));
    default:
    {
      long ey;
      GEN y;
      if (!(y = toser_i(x))) break;
      ey = valp(y);
      if (ey < 0) pari_err_DOMAIN("log1p","valuation", "<", gen_0, x);
      if (gequal0(y)) return gcopy(y);
      if (ey)
        return glog(gaddgs(y,1),prec);
      else
      {
        GEN a = gel(y,2), a1 = gaddgs(a,1);
        y = gdiv(y, a1); gel(y,2) = gen_1;
        return gadd(glog1p(a,prec), glog(y, prec));
      }
    }
  }
  return trans_eval("log1p",glog1p,x,prec);
}
GEN
glog1p(GEN x, long prec)
{
  pari_sp av = avma;
  return gerepileupto(av, log1p_i(x, prec));
}
/********************************************************************/
/**                                                                **/
/**                        SINE, COSINE                            **/
/**                                                                **/
/********************************************************************/

/* Reduce x0 mod Pi/2 to x in [-Pi/4, Pi/4]. Return cos(x)-1 */
static GEN
mpcosm1(GEN x, long *ptmod8)
{
  long a = expo(x), l = realprec(x), b, L, i, n, m, B;
  GEN y, p2, x2;
  double d;

  n = 0;
  if (a >= 0)
  {
    long p;
    GEN q;
    if (a > 30)
    {
      GEN z, pitemp = Pi2n(-2, nbits2prec(a + 32));
      z = addrr(x,pitemp); /* = x + Pi/4 */
      if (expo(z) >= bit_prec(z) + 3) pari_err_PREC("mpcosm1");
      shiftr_inplace(pitemp, 1);
      q = floorr( divrr(z,pitemp) ); /* round ( x / (Pi/2) ) */
      p = l+EXTRAPRECWORD; x = rtor(x,p);
    } else {
      q = stoi((long)floor(rtodbl(x) / (M_PI/2) + 0.5));
      p = l;
    }
    if (signe(q))
    {
      x = subrr(x, mulir(q, Pi2n(-1,p))); /* x mod Pi/2  */
      a = expo(x);
      if (!signe(x) && a >= 0) pari_err_PREC("mpcosm1");
      n = mod4(q); if (n && signe(q) < 0) n = 4 - n;
    }
  }
  /* a < 0 */
  b = signe(x); *ptmod8 = (b < 0)? 4 + n: n;
  if (!b) return real_0_bit(expo(x)*2 - 1);

  b = prec2nbits(l);
  if (b + 2*a <= 0) {
    y = sqrr(x); shiftr_inplace(y, -1); setsigne(y, -1);
    return y;
  }

  y = cgetr(l);
  B = b/6 + BITS_IN_LONG + (BITS_IN_LONG*BITS_IN_LONG/2)/ b;
  d = a/2.; m = (long)(d + sqrt(d*d + B)); /* >= 0 ,*/
  if (m < (-a) * 0.1) m = 0; /* not worth it */
  L = l + nbits2extraprec(m);

  b += m;
  d = 2.0 * (m-dbllog2r(x)-1/M_LN2); /* ~ 2( - log_2 Y - 1/log(2) ) */
  n = (long)(b / d);
  if (n > 1)
    n = (long)(b / (d + log2((double)n+1))); /* log~constant in small ranges */
  while (n*(d+log2((double)n+1)) < b) n++; /* expect few corrections */

 /* Multiplication is quadratic in this range (l is small, otherwise we
  * use logAGM + Newton). Set Y = 2^(-e-a) x, compute truncated series
  * sum Y^2k/(2k)!: this costs roughly
  *   m b^2 + sum_{k <= n} (2k e + BITS_IN_LONG)^2
  *   ~ floor(b/2e) b^2 / 3  + m b^2
  * bit operations with |x| <  2^(1+a), |Y| < 2^(1-e) , m = e+a and b bits of
  * accuracy needed, so
  *    B := ( b / 6 + BITS_IN_LONG + BITS_IN_LONG^2 / 2b) ~ m(m-a)
  * we want b ~ 6 m (m-a) or m~b+a hence
  *     m = min( a/2 + sqrt(a^2/4 + b/6),  b/2 + a )
  * NB1: e ~ (b/6)^(1/2) or b/2.
  * NB2: We use b/4 instead of b/6 in the formula above: hand-optimized...
  *
  * Truncate the sum at k = n (>= 1), the remainder is
  * < sum_{k >= n+1} Y^2k / 2k! < Y^(2n+2) / (2n+2)!(1-Y^2) < Y^(2n+2)/(2n+1)!
  * We want ... <= Y^2 2^-b, hence -2n log_2 |Y| + log_2 (2n+1)! >= b
  *   log n! ~ (n + 1/2) log(n+1) - (n+1) + log(2Pi)/2,
  * error bounded by 1/6(n+1) <= 1/12. Finally, we want
  * 2n (-1/log(2) - log_2 |Y| + log_2(2n+2)) >= b  */
  x = rtor(x, L); shiftr_inplace(x, -m); setsigne(x, 1);
  x2 = sqrr(x);
  if (n == 1) { p2 = x2; shiftr_inplace(p2, -1); setsigne(p2, -1); } /*-Y^2/2*/
  else
  {
    GEN unr = real_1(L);
    pari_sp av;
    long s = 0, l1 = nbits2prec((long)(d + n + 16));

    p2 = cgetr(L); av = avma;
    for (i=n; i>=2; i--)
    {
      GEN p1;
      setprec(x2,l1); p1 = divrunu(x2, 2*i-1);
      l1 += dvmdsBIL(s - expo(p1), &s); if (l1>L) l1=L;
      if (i != n) p1 = mulrr(p1,p2);
      setprec(unr,l1); p1 = addrr_sign(unr,1, p1,-signe(p1));
      setprec(p2,l1); affrr(p1,p2); avma = av;
    }
    shiftr_inplace(p2, -1); togglesign(p2); /* p2 := -p2/2 */
    setprec(x2,L); p2 = mulrr(x2,p2);
  }
  /* Now p2 = sum {1<= i <=n} (-1)^i x^(2i) / (2i)! ~ cos(x) - 1 */
  for (i=1; i<=m; i++)
  { /* p2 = cos(x)-1 --> cos(2x)-1 */
    p2 = mulrr(p2, addsr(2,p2));
    shiftr_inplace(p2, 1);
    if ((i & 31) == 0) p2 = gerepileuptoleaf((pari_sp)y, p2);
  }
  affrr_fixlg(p2,y); return y;
}

/* sqrt (|1 - (1+x)^2|) = sqrt(|x*(x+2)|). Sends cos(x)-1 to |sin(x)| */
static GEN
mpaut(GEN x)
{
  pari_sp av = avma;
  GEN t = mulrr(x, addsr(2,x)); /* != 0 */
  if (!signe(t)) return real_0_bit(expo(t) >> 1);
  return gerepileuptoleaf(av, sqrtr_abs(t));
}

/********************************************************************/
/**                            COSINE                              **/
/********************************************************************/

GEN
mpcos(GEN x)
{
  long mod8;
  pari_sp av;
  GEN y,p1;

  if (!signe(x)) {
    long l = nbits2prec(-expo(x));
    if (l < LOWDEFAULTPREC) l = LOWDEFAULTPREC;
    return real_1(l);
  }

  av = avma; p1 = mpcosm1(x,&mod8);
  switch(mod8)
  {
    case 0: case 4: y = addsr(1,p1); break;
    case 1: case 7: y = mpaut(p1); togglesign(y); break;
    case 2: case 6: y = subsr(-1,p1); break;
    default:        y = mpaut(p1); break; /* case 3: case 5: */
  }
  return gerepileuptoleaf(av, y);
}

/* convert INT or FRAC to REAL, which is later reduced mod 2Pi : avoid
 * cancellation */
static GEN
tofp_safe(GEN x, long prec)
{
  return (typ(x) == t_INT || gexpo(x) > 0)? gadd(x, real_0(prec))
                                          : fractor(x, prec);
}

GEN
gcos(GEN x, long prec)
{
  pari_sp av;
  GEN r, u, v, y, u1, v1;
  long i;

  switch(typ(x))
  {
    case t_REAL: return mpcos(x);
    case t_COMPLEX:
      if (isintzero(gel(x,1))) return gcosh(gel(x,2), prec);
      i = precision(x); if (i) prec = i;
      y = cgetc(prec); av = avma;
      r = gexp(gel(x,2),prec);
      v1 = gmul2n(addrr(invr(r),r), -1); /* = cos(I*Im(x)) */
      u1 = subrr(v1, r); /* = - I*sin(I*Im(x)) */
      gsincos(gel(x,1),&u,&v,prec);
      affrr_fixlg(gmul(v1,v), gel(y,1));
      affrr_fixlg(gmul(u1,u), gel(y,2)); avma = av; return y;

    case t_INT: case t_FRAC:
      y = cgetr(prec); av = avma;
      affrr_fixlg(mpcos(tofp_safe(x,prec)), y); avma = av; return y;

    case t_PADIC: y = cos_p(x);
      if (!y) pari_err_DOMAIN("gcos(t_PADIC)","argument","",gen_0,x);
      return y;

    default:
      av = avma; if (!(y = toser_i(x))) break;
      if (gequal0(y)) return gerepileupto(av, gaddsg(1,y));
      if (valp(y) < 0)
        pari_err_DOMAIN("cos","valuation", "<", gen_0, x);
      gsincos(y,&u,&v,prec);
      return gerepilecopy(av,v);
  }
  return trans_eval("cos",gcos,x,prec);
}
/********************************************************************/
/**                             SINE                               **/
/********************************************************************/

GEN
mpsin(GEN x)
{
  long mod8;
  pari_sp av;
  GEN y,p1;

  if (!signe(x)) return real_0_bit(expo(x));

  av = avma; p1 = mpcosm1(x,&mod8);
  switch(mod8)
  {
    case 0: case 6: y=mpaut(p1); break;
    case 1: case 5: y=addsr(1,p1); break;
    case 2: case 4: y=mpaut(p1); togglesign(y); break;
    default:        y=subsr(-1,p1); break; /* case 3: case 7: */
  }
  return gerepileuptoleaf(av, y);
}

GEN
gsin(GEN x, long prec)
{
  pari_sp av;
  GEN r, u, v, y, v1, u1;
  long i;

  switch(typ(x))
  {
    case t_REAL: return mpsin(x);
    case t_COMPLEX:
      if (isintzero(gel(x,1))) retmkcomplex(gen_0,gsinh(gel(x,2),prec));
      i = precision(x); if (i) prec = i;
      y = cgetc(prec); av = avma;
      r = gexp(gel(x,2),prec);
      v1 = gmul2n(addrr(invr(r),r), -1); /* = cos(I*Im(x)) */
      u1 = subrr(r, v1); /* = I*sin(I*Im(x)) */
      gsincos(gel(x,1),&u,&v,prec);
      affrr_fixlg(gmul(v1,u), gel(y,1));
      affrr_fixlg(gmul(u1,v), gel(y,2)); avma = av; return y;

    case t_INT: case t_FRAC:
      y = cgetr(prec); av = avma;
      affrr_fixlg(mpsin(tofp_safe(x,prec)), y); avma = av; return y;

    case t_PADIC: y = sin_p(x);
      if (!y) pari_err_DOMAIN("gsin(t_PADIC)","argument","",gen_0,x);
      return y;

    default:
      av = avma; if (!(y = toser_i(x))) break;
      if (gequal0(y)) return gerepilecopy(av, y);
      if (valp(y) < 0)
        pari_err_DOMAIN("sin","valuation", "<", gen_0, x);
      gsincos(y,&u,&v,prec);
      return gerepilecopy(av,u);
  }
  return trans_eval("sin",gsin,x,prec);
}
/********************************************************************/
/**                       SINE, COSINE together                    **/
/********************************************************************/

void
mpsincos(GEN x, GEN *s, GEN *c)
{
  long mod8;
  pari_sp av, tetpil;
  GEN p1, *gptr[2];

  if (!signe(x))
  {
    long e = expo(x);
    *s = real_0_bit(e);
    *c = e >= 0? real_0_bit(e): real_1_bit(-e);
    return;
  }

  av=avma; p1=mpcosm1(x,&mod8); tetpil=avma;
  switch(mod8)
  {
    case 0: *c=addsr( 1,p1); *s=mpaut(p1); break;
    case 1: *s=addsr( 1,p1); *c=mpaut(p1); togglesign(*c); break;
    case 2: *c=subsr(-1,p1); *s=mpaut(p1); togglesign(*s); break;
    case 3: *s=subsr(-1,p1); *c=mpaut(p1); break;
    case 4: *c=addsr( 1,p1); *s=mpaut(p1); togglesign(*s); break;
    case 5: *s=addsr( 1,p1); *c=mpaut(p1); break;
    case 6: *c=subsr(-1,p1); *s=mpaut(p1); break;
    case 7: *s=subsr(-1,p1); *c=mpaut(p1); togglesign(*c); break;
  }
  gptr[0]=s; gptr[1]=c;
  gerepilemanysp(av,tetpil,gptr,2);
}

/* SINE and COSINE - 1 */
void
mpsincosm1(GEN x, GEN *s, GEN *c)
{
  long mod8;
  pari_sp av, tetpil;
  GEN p1, *gptr[2];

  if (!signe(x))
  {
    long e = expo(x);
    *s = real_0_bit(e);
    *c = real_0_bit(2*e-1);
    return;
  }
  av=avma; p1=mpcosm1(x,&mod8); tetpil=avma;
  switch(mod8)
  {
    case 0: *c=rcopy(p1); *s=mpaut(p1); break;
    case 1: *s=addsr(1,p1); *c=addrs(mpaut(p1),1); togglesign(*c); break;
    case 2: *c=subsr(-2,p1); *s=mpaut(p1); togglesign(*s); break;
    case 3: *s=subsr(-1,p1); *c=subrs(mpaut(p1),1); break;
    case 4: *c=rcopy(p1); *s=mpaut(p1); togglesign(*s); break;
    case 5: *s=addsr( 1,p1); *c=subrs(mpaut(p1),1); break;
    case 6: *c=subsr(-2,p1); *s=mpaut(p1); break;
    case 7: *s=subsr(-1,p1); *c=subsr(-1,mpaut(p1)); break;
  }
  gptr[0]=s; gptr[1]=c;
  gerepilemanysp(av,tetpil,gptr,2);
}

/* return exp(ix), x a t_REAL */
GEN
expIr(GEN x)
{
  pari_sp av = avma;
  GEN v = cgetg(3,t_COMPLEX);
  mpsincos(x, (GEN*)(v+2), (GEN*)(v+1));
  if (!signe(gel(v,2))) return gerepilecopy(av, gel(v,1));
  return v;
}

/* return exp(ix)-1, x a t_REAL */
static GEN
expm1_Ir(GEN x)
{
  pari_sp av = avma;
  GEN v = cgetg(3,t_COMPLEX);
  mpsincosm1(x, (GEN*)(v+2), (GEN*)(v+1));
  if (!signe(gel(v,2))) return gerepilecopy(av, gel(v,1));
  return v;
}

/* return exp(z)-1, z complex */
GEN
cxexpm1(GEN z, long prec)
{
  pari_sp av = avma;
  GEN X, Y, x = real_i(z), y = imag_i(z);
  long l = precision(z);
  if (l) prec = l;
  if (typ(x) != t_REAL) x = gtofp(x, prec);
  if (typ(y) != t_REAL) y = gtofp(y, prec);
  if (gequal0(y)) return mpexpm1(x);
  if (gequal0(x)) return expm1_Ir(y);
  X = mpexpm1(x); /* t_REAL */
  Y = expm1_Ir(y);
  /* exp(x+iy) - 1 = (exp(x)-1)(exp(iy)-1) + exp(x)-1 + exp(iy)-1 */
  return gerepileupto(av, gadd(gadd(X,Y), gmul(X,Y)));
}

void
gsincos(GEN x, GEN *s, GEN *c, long prec)
{
  long i, j, ex, ex2, lx, ly, mi;
  pari_sp av, tetpil;
  GEN y, r, u, v, u1, v1, p1, p2, p3, p4, ps, pc;
  GEN *gptr[4];

  switch(typ(x))
  {
    case t_INT: case t_FRAC:
      *s = cgetr(prec);
      *c = cgetr(prec); av = avma;
      mpsincos(tofp_safe(x, prec), &ps, &pc);
      affrr_fixlg(ps,*s);
      affrr_fixlg(pc,*c); avma = av; return;

    case t_REAL:
      mpsincos(x,s,c); return;

    case t_COMPLEX:
      i = precision(x); if (i) prec = i;
      ps = cgetc(prec); *s = ps;
      pc = cgetc(prec); *c = pc; av = avma;
      r = gexp(gel(x,2),prec);
      v1 = gmul2n(addrr(invr(r),r), -1); /* = cos(I*Im(x)) */
      u1 = subrr(r, v1); /* = I*sin(I*Im(x)) */
      gsincos(gel(x,1), &u,&v, prec);
      affrr_fixlg(mulrr(v1,u), gel(ps,1));
      affrr_fixlg(mulrr(u1,v), gel(ps,2));
      affrr_fixlg(mulrr(v1,v), gel(pc,1));
      affrr_fixlg(mulrr(u1,u), gel(pc,2)); togglesign(gel(pc,2));
      avma = av; return;

    case t_QUAD:
      av = avma; gsincos(quadtofp(x, prec), s, c, prec);
      gerepileall(av, 2, s, c); return;

    default:
      av = avma; if (!(y = toser_i(x))) break;
      if (gequal0(y)) { *s = gerepilecopy(av,y); *c = gaddsg(1,*s); return; }

      ex = valp(y); lx = lg(y); ex2 = 2*ex+2;
      if (ex < 0) pari_err_DOMAIN("gsincos","valuation", "<", gen_0, x);
      if (ex2 > lx)
      {
        *s = x == y? gcopy(y): gerepilecopy(av, y); av = avma;
        *c = gerepileupto(av, gsubsg(1, gdivgs(gsqr(y),2)));
        return;
      }
      if (!ex)
      {
        gsincos(serchop0(y),&u,&v,prec);
        gsincos(gel(y,2),&u1,&v1,prec);
        p1 = gmul(v1,v);
        p2 = gmul(u1,u);
        p3 = gmul(v1,u);
        p4 = gmul(u1,v); tetpil = avma;
        *c = gsub(p1,p2);
        *s = gadd(p3,p4);
        gptr[0]=s; gptr[1]=c;
        gerepilemanysp(av,tetpil,gptr,2);
        return;
      }

      ly = lx+2*ex;
      mi = lx-1; while (mi>=3 && isrationalzero(gel(y,mi))) mi--;
      mi += ex-2;
      pc = cgetg(ly,t_SER); *c = pc;
      ps = cgetg(lx,t_SER); *s = ps;
      pc[1] = evalsigne(1) | _evalvalp(0) | evalvarn(varn(y));
      gel(pc,2) = gen_1; ps[1] = y[1];
      for (i=2; i<ex+2; i++) gel(ps,i) = gcopy(gel(y,i));
      for (i=3; i< ex2; i++) gel(pc,i) = gen_0;
      for (i=ex2; i<ly; i++)
      {
        long ii = i-ex;
        av = avma; p1 = gen_0;
        for (j=ex; j<=minss(ii-2,mi); j++)
          p1 = gadd(p1, gmulgs(gmul(gel(y,j-ex+2),gel(ps,ii-j)),j));
        gel(pc,i) = gerepileupto(av, gdivgs(p1,2-i));
        if (ii < lx)
        {
          av = avma; p1 = gen_0;
          for (j=ex; j<=minss(i-ex2,mi); j++)
            p1 = gadd(p1,gmulgs(gmul(gel(y,j-ex+2),gel(pc,i-j)),j));
          p1 = gdivgs(p1,i-2);
          gel(ps,ii) = gerepileupto(av, gadd(p1,gel(y,ii)));
        }
      }
      return;
  }
  pari_err_TYPE("gsincos",x);
}

/********************************************************************/
/**                                                                **/
/**                              SINC                              **/
/**                                                                **/
/********************************************************************/
static GEN
mpsinc(GEN x)
{
  pari_sp av = avma;
  GEN s, c;

  if (!signe(x)) {
    long l = nbits2prec(-expo(x));
    if (l < LOWDEFAULTPREC) l = LOWDEFAULTPREC;
    return real_1(l);
  }

  mpsincos(x,&s,&c);
  return gerepileuptoleaf(av, divrr(s,x));
}

GEN
gsinc(GEN x, long prec)
{
  pari_sp av;
  GEN r, u, v, y, u1, v1;
  long i;

  switch(typ(x))
  {
    case t_REAL: return mpsinc(x);
    case t_COMPLEX:
      if (isintzero(gel(x,1)))
      {
        av = avma; x = gel(x,2);
        if (gequal0(x)) return gcosh(x,prec);
        return gerepileuptoleaf(av,gdiv(gsinh(x,prec),x));
      }
      i = precision(x); if (i) prec = i;
      y = cgetc(prec); av = avma;
      r = gexp(gel(x,2),prec);
      v1 = gmul2n(addrr(invr(r),r), -1); /* = cos(I*Im(x)) */
      u1 = subrr(r, v1); /* = I*sin(I*Im(x)) */
      gsincos(gel(x,1),&u,&v,prec);
      affc_fixlg(gdiv(mkcomplex(gmul(v1,u), gmul(u1,v)), x), y);
      avma = av; return y;

    case t_INT:
      if (!signe(x)) return real_1(prec); /*fall through*/
    case t_FRAC:
      y = cgetr(prec); av = avma;
      affrr_fixlg(mpsinc(tofp_safe(x,prec)), y); avma = av; return y;

    case t_PADIC:
      if (gequal0(x)) return cvtop(gen_1, gel(x,2), valp(x));
      av = avma; y = sin_p(x);
      if (!y) pari_err_DOMAIN("gsinc(t_PADIC)","argument","",gen_0,x);
      return gerepileupto(av,gdiv(y,x));

    default:
    {
      long ex;
      av = avma; if (!(y = toser_i(x))) break;
      if (gequal0(y)) return gerepileupto(av, gaddsg(1,y));
      ex = valp(y);
      if (ex < 0) pari_err_DOMAIN("sinc","valuation", "<", gen_0, x);
      if (ex)
      {
        gsincos(y,&u,&v,prec);
        y = gerepileupto(av, gdiv(u,y));
        if (lg(y) > 2) gel(y,2) = gen_1;
        return y;
      }
      else
      {
        GEN z0, y0 = gel(y,2), y1 = serchop0(y), y10 = y1;
        if (!gequal1(y0)) y10 = gdiv(y10, y0);
        gsincos(y1,&u,&v,prec);
        z0 = gdiv(gcos(y0,prec), y0);
        y = gaddsg(1, y10);
        u = gadd(gmul(gsinc(y0, prec),v), gmul(z0, u));
        return gerepileupto(av,gdiv(u,y));
      }
    }
  }
  return trans_eval("sinc",gsinc,x,prec);
}

/********************************************************************/
/**                                                                **/
/**                     TANGENT and COTANGENT                      **/
/**                                                                **/
/********************************************************************/
static GEN
mptan(GEN x)
{
  pari_sp av = avma;
  GEN s, c;

  mpsincos(x,&s,&c);
  if (!signe(c))
    pari_err_DOMAIN("tan", "argument", "=", strtoGENstr("Pi/2 + kPi"),x);
  return gerepileuptoleaf(av, divrr(s,c));
}

GEN
gtan(GEN x, long prec)
{
  pari_sp av;
  GEN y, s, c;

  switch(typ(x))
  {
    case t_REAL: return mptan(x);

    case t_COMPLEX: {
      if (isintzero(gel(x,1))) retmkcomplex(gen_0,gtanh(gel(x,2),prec));
      av = avma; y = mulcxmI(gtanh(mulcxI(x), prec)); /* tan x = -I th(I x) */
      gel(y,1) = gcopy(gel(y,1));
      return gerepileupto(av, y);
    }
    case t_INT: case t_FRAC:
      y = cgetr(prec); av = avma;
      affrr_fixlg(mptan(tofp_safe(x,prec)), y); avma = av; return y;

    case t_PADIC:
      av = avma;
      return gerepileupto(av, gdiv(gsin(x,prec), gcos(x,prec)));

    default:
      av = avma; if (!(y = toser_i(x))) break;
      if (gequal0(y)) return gerepilecopy(av, y);
      if (valp(y) < 0)
        pari_err_DOMAIN("tan","valuation", "<", gen_0, x);
      gsincos(y,&s,&c,prec);
      return gerepileupto(av, gdiv(s,c));
  }
  return trans_eval("tan",gtan,x,prec);
}

static GEN
mpcotan(GEN x)
{
  pari_sp av=avma, tetpil;
  GEN s,c;

  mpsincos(x,&s,&c); tetpil=avma;
  return gerepile(av,tetpil,divrr(c,s));
}

GEN
gcotan(GEN x, long prec)
{
  pari_sp av;
  GEN y, s, c;

  switch(typ(x))
  {
    case t_REAL:
      return mpcotan(x);

    case t_COMPLEX:
      if (isintzero(gel(x,1))) {
        GEN z = cgetg(3, t_COMPLEX);
        gel(z,1) = gen_0;
        av = avma;
        gel(z,2) = gerepileupto(av, gneg(ginv(gtanh(gel(x,2),prec))));
        return z;
      }
      av = avma;
      gsincos(x,&s,&c,prec);
      return gerepileupto(av, gdiv(c,s));

    case t_INT: case t_FRAC:
      y = cgetr(prec); av = avma;
      affrr_fixlg(mpcotan(tofp_safe(x,prec)), y); avma = av; return y;

    case t_PADIC:
      av = avma;
      return gerepileupto(av, gdiv(gcos(x,prec), gsin(x,prec)));

    default:
      av = avma; if (!(y = toser_i(x))) break;
      if (gequal0(y)) pari_err_DOMAIN("cotan", "argument", "=", gen_0, y);
      if (valp(y) < 0) pari_err_DOMAIN("cotan","valuation", "<", gen_0, x);
      gsincos(y,&s,&c,prec);
      return gerepileupto(av, gdiv(c,s));
  }
  return trans_eval("cotan",gcotan,x,prec);
}
