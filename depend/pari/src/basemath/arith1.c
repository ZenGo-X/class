/* Copyright (C) 2000  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/*********************************************************************/
/**                                                                 **/
/**                     ARITHMETIC FUNCTIONS                        **/
/**                         (first part)                            **/
/**                                                                 **/
/*********************************************************************/
#include "pari.h"
#include "paripriv.h"

/******************************************************************/
/*                                                                */
/*                 GENERATOR of (Z/mZ)*                           */
/*                                                                */
/******************************************************************/
static GEN
remove2(GEN q) { long v = vali(q); return v? shifti(q, -v): q; }
static ulong
u_remove2(ulong q) { return q >> vals(q); }
GEN
odd_prime_divisors(GEN q) { return gel(Z_factor(remove2(q)), 1); }
static GEN
u_odd_prime_divisors(ulong q) { return gel(factoru(u_remove2(q)), 1); }
/* p odd prime, q=(p-1)/2; L0 list of (some) divisors of q = (p-1)/2 or NULL
 * (all prime divisors of q); return the q/l, l in L0 */
static GEN
is_gener_expo(GEN p, GEN L0)
{
  GEN L, q = shifti(p,-1);
  long i, l;
  if (L0) {
    l = lg(L0);
    L = cgetg(l, t_VEC);
  } else {
    L0 = L = odd_prime_divisors(q);
    l = lg(L);
  }
  for (i=1; i<l; i++) gel(L,i) = diviiexact(q, gel(L0,i));
  return L;
}
static GEN
u_is_gener_expo(ulong p, GEN L0)
{
  const ulong q = p >> 1;
  long i, l;
  GEN L;
  if (L0) {
    l = lg(L0);
    L = cgetg(l, t_VECSMALL);
  } else {
    L0 = L = u_odd_prime_divisors(q);
    l = lg(L);
  }
  for (i=1; i<l; i++) L[i] = q / uel(L0,i);
  return L;
}

int
is_gener_Fl(ulong x, ulong p, ulong p_1, GEN L)
{
  long i;
  if (krouu(x, p) >= 0) return 0;
  for (i=lg(L)-1; i; i--)
  {
    ulong t = Fl_powu(x, uel(L,i), p);
    if (t == p_1 || t == 1) return 0;
  }
  return 1;
}
/* assume p prime */
ulong
pgener_Fl_local(ulong p, GEN L0)
{
  const pari_sp av = avma;
  const ulong p_1 = p-1;
  long x;
  GEN L;
  if (p <= 19) switch(p)
  { /* quick trivial cases */
    case 2:  return 1;
    case 7:
    case 17: return 3;
    default: return 2;
  }
  L = u_is_gener_expo(p,L0);
  for (x=2;;x++) { if (is_gener_Fl(x,p,p_1,L)) break; }
  avma = av; return x;
}
ulong
pgener_Fl(ulong p) { return pgener_Fl_local(p, NULL); }

/* L[i] = set of (p-1)/2l, l ODD prime divisor of p-1 (l=2 can be included,
 * but wasteful) */
int
is_gener_Fp(GEN x, GEN p, GEN p_1, GEN L)
{
  long i, t = lgefint(x)==3? kroui(x[2], p): kronecker(x, p);
  if (t >= 0) return 0;
  for (i = lg(L)-1; i; i--)
  {
    GEN t = Fp_pow(x, gel(L,i), p);
    if (equalii(t, p_1) || equali1(t)) return 0;
  }
  return 1;
}

/* assume p prime, return a generator of all L[i]-Sylows in F_p^*. */
GEN
pgener_Fp_local(GEN p, GEN L0)
{
  pari_sp av0 = avma;
  GEN x, p_1, L;
  if (lgefint(p) == 3)
  {
    ulong z;
    if (p[2] == 2) return gen_1;
    if (L0) L0 = ZV_to_nv(L0);
    z = pgener_Fl_local(uel(p,2), L0);
    avma = av0; return utoipos(z);
  }
  p_1 = subiu(p,1); L = is_gener_expo(p, L0);
  x = utoipos(2);
  for (;; x[2]++) { if (is_gener_Fp(x, p, p_1, L)) break; }
  avma = av0; return utoipos(uel(x,2));
}

GEN
pgener_Fp(GEN p) { return pgener_Fp_local(p, NULL); }

ulong
pgener_Zl(ulong p)
{
  if (p == 2) pari_err_DOMAIN("pgener_Zl","p","=",gen_2,gen_2);
  /* only p < 2^32 such that znprimroot(p) != znprimroot(p^2) */
  if (p == 40487) return 10;
#ifndef LONG_IS_64BIT
  return pgener_Fl(p);
#else
  if (p < (1UL<<32)) return pgener_Fl(p);
  else
  {
    const pari_sp av = avma;
    const ulong p_1 = p-1;
    long x ;
    GEN p2 = sqru(p), L = u_is_gener_expo(p, NULL);
    for (x=2;;x++)
      if (is_gener_Fl(x,p,p_1,L) && !is_pm1(Fp_powu(utoipos(x),p_1,p2))) break;
    avma = av; return x;
  }
#endif
}

/* p prime. Return a primitive root modulo p^e, e > 1 */
GEN
pgener_Zp(GEN p)
{
  if (lgefint(p) == 3) return utoipos(pgener_Zl(p[2]));
  else
  {
    const pari_sp av = avma;
    GEN p_1 = subiu(p,1), p2 = sqri(p), L = is_gener_expo(p,NULL);
    GEN x = utoipos(2);
    for (;; x[2]++)
      if (is_gener_Fp(x,p,p_1,L) && !equali1(Fp_pow(x,p_1,p2))) break;
    avma = av; return utoipos(uel(x,2));
  }
}

static GEN
gener_Zp(GEN q, GEN F)
{
  GEN p = NULL;
  long e = 0;
  if (F)
  {
    GEN P = gel(F,1), E = gel(F,2);
    long i, l = lg(P);
    for (i = 1; i < l; i++)
    {
      p = gel(P,i);
      if (absequaliu(p, 2)) continue;
      if (i < l-1) pari_err_DOMAIN("znprimroot", "argument","=",F,F);
      e = itos(gel(E,i));
    }
    if (!p) pari_err_DOMAIN("znprimroot", "argument","=",F,F);
  }
  else
    e = Z_isanypower(q, &p);
  return e > 1? pgener_Zp(p): pgener_Fp(q);
}

GEN
znprimroot(GEN N)
{
  pari_sp av = avma;
  GEN x, n, F;

  if ((F = check_arith_non0(N,"znprimroot")))
  {
    F = clean_Z_factor(F);
    N = typ(N) == t_VEC? gel(N,1): factorback(F);
  }
  N = absi_shallow(N);
  if (abscmpiu(N, 4) <= 0) { avma = av; return mkintmodu(N[2]-1,N[2]); }
  switch(mod4(N))
  {
    case 0: /* N = 0 mod 4 */
      pari_err_DOMAIN("znprimroot", "argument","=",N,N);
      x = NULL; break;
    case 2: /* N = 2 mod 4 */
      n = shifti(N,-1); /* becomes odd */
      x = gener_Zp(n,F); if (!mod2(x)) x = addii(x,n);
      break;
    default: /* N odd */
      x = gener_Zp(N,F);
      break;
  }
  return gerepilecopy(av, mkintmod(x, N));
}

/* n | (p-1), returns a primitive n-th root of 1 in F_p^* */
GEN
rootsof1_Fp(GEN n, GEN p)
{
  pari_sp av = avma;
  GEN L = odd_prime_divisors(n); /* 2 implicit in pgener_Fp_local */
  GEN z = pgener_Fp_local(p, L);
  z = Fp_pow(z, diviiexact(subiu(p,1), n), p); /* prim. n-th root of 1 */
  return gerepileuptoint(av, z);
}

GEN
rootsof1u_Fp(ulong n, GEN p)
{
  pari_sp av = avma;
  GEN z, L = u_odd_prime_divisors(n); /* 2 implicit in pgener_Fp_local */
  z = pgener_Fp_local(p, Flv_to_ZV(L));
  z = Fp_pow(z, diviuexact(subiu(p,1), n), p); /* prim. n-th root of 1 */
  return gerepileuptoint(av, z);
}

ulong
rootsof1_Fl(ulong n, ulong p)
{
  pari_sp av = avma;
  GEN L = u_odd_prime_divisors(n); /* 2 implicit in pgener_Fl_local */
  ulong z = pgener_Fl_local(p, L);
  z = Fl_powu(z, (p-1) / n, p); /* prim. n-th root of 1 */
  avma = av; return z;
}

/*********************************************************************/
/**                                                                 **/
/**                     INVERSE TOTIENT FUNCTION                    **/
/**                                                                 **/
/*********************************************************************/
/* N t_INT, L a ZV containing all prime divisors of N, and possibly other
 * primes. Return factor(N) */
GEN
Z_factor_listP(GEN N, GEN L)
{
  long i, k, l = lg(L);
  GEN P = cgetg(l, t_COL), E = cgetg(l, t_COL);
  for (i = k = 1; i < l; i++)
  {
    GEN p = gel(L,i);
    long v = Z_pvalrem(N, p, &N);
    if (v)
    {
      gel(P,k) = p;
      gel(E,k) = utoipos(v);
      k++;
    }
  }
  setlg(P, k);
  setlg(E, k); return mkmat2(P,E);
}

/* look for x such that phi(x) = n, p | x => p > m (if m = NULL: no condition).
 * L is a list of primes containing all prime divisors of n. */
static long
istotient_i(GEN n, GEN m, GEN L, GEN *px)
{
  pari_sp av = avma, av2;
  GEN k, D;
  long i, v;
  if (m && mod2(n))
  {
    if (!equali1(n)) return 0;
    if (px) *px = gen_1;
    return 1;
  }
  D = divisors(Z_factor_listP(shifti(n, -1), L));
  /* loop through primes p > m, d = p-1 | n */
  av2 = avma;
  if (!m)
  { /* special case p = 2, d = 1 */
    k = n;
    for (v = 1;; v++) {
      if (istotient_i(k, gen_2, L, px)) {
        if (px) *px = shifti(*px, v);
        return 1;
      }
      if (mod2(k)) break;
      k = shifti(k,-1);
    }
    avma = av2;
  }
  for (i = 1; i < lg(D); ++i)
  {
    GEN p, d = shifti(gel(D, i), 1); /* even divisors of n */
    if (m && cmpii(d, m) < 0) continue;
    p = addiu(d, 1);
    if (!isprime(p)) continue;
    k = diviiexact(n, d);
    for (v = 1;; v++) {
      GEN r;
      if (istotient_i(k, p, L, px)) {
        if (px) *px = mulii(*px, powiu(p, v));
        return 1;
      }
      k = dvmdii(k, p, &r);
      if (r != gen_0) break;
    }
    avma = av2;
  }
  avma = av; return 0;
}

/* find x such that phi(x) = n */
long
istotient(GEN n, GEN *px)
{
  pari_sp av = avma;
  if (typ(n) != t_INT) pari_err_TYPE("istotient", n);
  if (signe(n) < 1) return 0;
  if (mod2(n))
  {
    if (!equali1(n)) return 0;
    if (px) *px = gen_1;
    return 1;
  }
  if (istotient_i(n, NULL, gel(Z_factor(n), 1), px))
  {
    if (!px) avma = av;
    else
      *px = gerepileuptoint(av, *px);
    return 1;
  }
  avma = av; return 0;
}

/*********************************************************************/
/**                                                                 **/
/**                     INTEGRAL LOGARITHM                          **/
/**                                                                 **/
/*********************************************************************/

/* y > 1 and B > 0 integers. Return e such that y^e <= B < y^(e+1), i.e
 * e = floor(log_y B). Set *ptq = y^e if non-NULL */
long
ulogintall(ulong B, ulong y, ulong *ptq)
{
  ulong r, r2;
  long e;

  if (y == 2)
  {
    long eB = expu(B); /* 2^eB <= B < 2^(eB + 1) */
    if (ptq) *ptq = 1UL << eB;
    return eB;
  }
  r = y, r2 = 1UL;
  for (e=1;; e++)
  { /* here, r = y^e, r2 = y^(e-1) */
    if (r >= B)
    {
      if (r != B) { e--; r = r2; }
      if (ptq) *ptq = r;
      return e;
    }
    r2 = r;
    r = umuluu_or_0(y, r);
    if (!r)
    {
      if (ptq) *ptq = r2;
      return e;
    }
  }
}

/* y > 1 and B > 0 integers. Return e such that y^e <= B < y^(e+1), i.e
 * e = floor(log_y B). Set *ptq = y^e if non-NULL */
long
logintall(GEN B, GEN y, GEN *ptq)
{
  pari_sp av;
  long ey, e, emax, i, eB = expi(B); /* 2^eB <= B < 2^(eB + 1) */
  GEN q, pow2;

  if (lgefint(B) == 3)
  {
    ulong q;
    if (lgefint(y) > 3)
    {
      if (ptq) *ptq = gen_1;
      return 0;
    }
    if (!ptq) return ulogintall(B[2], y[2], NULL);
    e = ulogintall(B[2], y[2], &q);
    *ptq = utoi(q); return e;
  }
  if (equaliu(y,2))
  {
    if (ptq) *ptq = int2n(eB);
    return eB;
  }
  av = avma;
  ey = expi(y);
  /* eB/(ey+1) - 1 < e <= eB/ey */
  emax = eB/ey;
  if (emax <= 13) /* e small, be naive */
  {
    GEN r = y, r2 = gen_1;
    for (e=1;; e++)
    { /* here, r = y^e, r2 = y^(e-1) */
      long fl = cmpii(r, B);
      if (fl >= 0)
      {
        if (fl) { e--; cgiv(r); r = r2; }
        if (ptq) *ptq = gerepileuptoint(av, r); else avma = av;
        return e;
      }
      r2 = r; r = mulii(r,y);
    }
  }
  /* e >= 13 ey / (ey+1) >= 6.5 */

  /* binary splitting: compute bits of e one by one */
  /* compute pow2[i] = y^(2^i) [i < crude upper bound for log_2 log_y(B)] */
  pow2 = new_chunk((long)log2(eB)+2);
  gel(pow2,0) = y;
  for (i=0, q=y;; )
  {
    GEN r = gel(pow2,i); /* r = y^2^i */
    long fl = cmpii(r,B);
    if (!fl)
    {
      e = 1L<<i;
      if (ptq) *ptq = gerepileuptoint(av, r); else avma = av;
      return e;
    }
    if (fl > 0) { i--; break; }
    q = r;
    if (1L<<(i+1) > emax) break;
    gel(pow2,++i) = sqri(q);
  }

  for (e = 1L<<i;;)
  { /* y^e = q < B < r = q * y^(2^i) */
    pari_sp av2 = avma;
    long fl;
    GEN r;
    if (--i < 0) break;
    r = mulii(q, gel(pow2,i));
    fl = cmpii(r, B);
    if (fl > 0) avma = av2;
    else
    {
      e += (1L<<i);
      q = r;
      if (!fl) break; /* B = r */
    }
  }
  if (ptq) *ptq = gerepileuptoint(av, q); else avma = av;
  return e;
}

long
logint0(GEN B, GEN y, GEN *ptq)
{
  if (typ(B) != t_INT) pari_err_TYPE("logint",B);
  if (signe(B) <= 0) pari_err_DOMAIN("logint", "x" ,"<=", gen_0, B);
  if (typ(y) != t_INT) pari_err_TYPE("logint",y);
  if (cmpis(y, 2) < 0) pari_err_DOMAIN("logint", "b" ,"<=", gen_1, y);
  return logintall(B,y,ptq);
}

/*********************************************************************/
/**                                                                 **/
/**                     INTEGRAL SQUARE ROOT                        **/
/**                                                                 **/
/*********************************************************************/
GEN
sqrtint(GEN a)
{
  if (typ(a) != t_INT) pari_err_TYPE("sqrtint",a);
  switch (signe(a))
  {
    case 1: return sqrti(a);
    case 0: return gen_0;
    default: pari_err_DOMAIN("sqrtint", "argument", "<", gen_0,a);
  }
  return NULL; /* LCOV_EXCL_LINE */
}

/*********************************************************************/
/**                                                                 **/
/**                      PERFECT SQUARE                             **/
/**                                                                 **/
/*********************************************************************/
static int
carremod(ulong A)
{
  const int carresmod64[]={
    1,1,0,0,1,0,0,0,0,1, 0,0,0,0,0,0,1,1,0,0, 0,0,0,0,0,1,0,0,0,0,
    0,0,0,1,0,0,1,0,0,0, 0,1,0,0,0,0,0,0,0,1, 0,0,0,0,0,0,0,1,0,0, 0,0,0,0};
  const int carresmod63[]={
    1,1,0,0,1,0,0,1,0,1, 0,0,0,0,0,0,1,0,1,0, 0,0,1,0,0,1,0,0,1,0,
    0,0,0,0,0,0,1,1,0,0, 0,0,0,1,0,0,1,0,0,1, 0,0,0,0,0,0,0,0,1,0, 0,0,0};
  const int carresmod65[]={
    1,1,0,0,1,0,0,0,0,1, 1,0,0,0,1,0,1,0,0,0, 0,0,0,0,0,1,1,0,0,1,
    1,0,0,0,0,1,1,0,0,1, 1,0,0,0,0,0,0,0,0,1, 0,1,0,0,0,1,1,0,0,0, 0,1,0,0,1};
  const int carresmod11[]={1,1,0,1,1,1,0,0,0,1, 0};
  return (carresmod64[A & 0x3fUL]
    && carresmod63[A % 63UL]
    && carresmod65[A % 65UL]
    && carresmod11[A % 11UL]);
}

/* emulate Z_issquareall on single-word integers */
long
uissquareall(ulong A, ulong *sqrtA)
{
  if (!A) { *sqrtA = 0; return 1; }
  if (carremod(A))
  {
    ulong a = usqrt(A);
    if (a * a == A) { *sqrtA = a; return 1; }
  }
  return 0;
}
long
uissquare(ulong A)
{
  if (!A) return 1;
  if (carremod(A))
  {
    ulong a = usqrt(A);
    if (a * a == A) return 1;
  }
  return 0;
}

long
Z_issquareall(GEN x, GEN *pt)
{
  pari_sp av;
  GEN y, r;

  switch(signe(x))
  {
    case -1: return 0;
    case 0: if (pt) *pt=gen_0; return 1;
  }
  if (lgefint(x) == 3)
  {
    ulong u = uel(x,2), a;
    if (!pt) return uissquare(u);
    if (!uissquareall(u, &a)) return 0;
    *pt = utoipos(a); return 1;
  }
  if (!carremod(umodiu(x, 64*63*65*11))) return 0;
  av = avma; y = sqrtremi(x, &r);
  if (r != gen_0) { avma = av; return 0; }
  if (pt) { *pt = y; avma = (pari_sp)y; } else avma = av;
  return 1;
}

/* a t_INT, p prime */
long
Zp_issquare(GEN a, GEN p)
{
  long v;
  GEN ap;

  if (!signe(a) || gequal1(a)) return 1;
  v = Z_pvalrem(a, p, &ap);
  if (v&1) return 0;
  return absequaliu(p, 2)? umodiu(ap, 8) == 1
                      : kronecker(ap,p) == 1;
}

static long
polissquareall(GEN x, GEN *pt)
{
  pari_sp av;
  long v;
  GEN y, a, b, p;

  if (!signe(x))
  {
    if (pt) *pt = gcopy(x);
    return 1;
  }
  if (odd(degpol(x))) return 0; /* odd degree */
  av = avma;
  v = RgX_valrem(x, &x);
  if (v & 1) { avma = av; return 0; }
  a = gel(x,2); /* test constant coeff */
  if (!pt)
  { if (!issquare(a)) { avma = av; return 0; } }
  else
  { if (!issquareall(a,&b)) { avma = av; return 0; } }
  if (!degpol(x)) { /* constant polynomial */
    if (!pt) { avma = av; return 1; }
    y = scalarpol(b, varn(x)); goto END;
  }
  p = characteristic(x);
  if (signe(p) && !mod2(p))
  {
    long i, lx;
    if (!absequaliu(p,2)) pari_err_IMPL("issquare for even characteristic != 2");
    x = gmul(x, mkintmod(gen_1, gen_2));
    lx = lg(x);
    if ((lx-3) & 1) { avma = av; return 0; }
    for (i = 3; i < lx; i+=2)
      if (!gequal0(gel(x,i))) { avma = av; return 0; }
    if (pt) {
      y = cgetg((lx+3) / 2, t_POL);
      for (i = 2; i < lx; i+=2)
        if (!issquareall(gel(x,i), &gel(y, (i+2)>>1))) { avma = av; return 0; }
      y[1] = evalsigne(1) | evalvarn(varn(x));
      goto END;
    } else {
      for (i = 2; i < lx; i+=2)
        if (!issquare(gel(x,i))) { avma = av; return 0; }
      avma = av; return 1;
    }
  }
  else
  {
    long m = 1;
    x = RgX_Rg_div(x,a);
    /* a(x^m) = B^2 => B = b(x^m) provided a(0) != 0 */
    if (!signe(p)) x = RgX_deflate_max(x,&m);
    y = ser2rfrac_i(gsqrt(RgX_to_ser(x,lg(x)-1),0));
    if (!RgX_equal(RgX_sqr(y), x)) { avma = av; return 0; }
    if (!pt) { avma = av; return 1; }
    if (!gequal1(a)) y = gmul(b, y);
    if (m != 1) y = RgX_inflate(y,m);
  }
END:
  if (v) y = RgX_shift_shallow(y, v>>1);
  *pt = gerepilecopy(av, y); return 1;
}

/* b unit mod p */
static int
Up_ispower(GEN b, GEN K, GEN p, long d, GEN *pt)
{
  if (d == 1)
  { /* mod p: faster */
    if (!Fp_ispower(b, K, p)) return 0;
    if (pt) *pt = Fp_sqrtn(b, K, p, NULL);
  }
  else
  { /* mod p^{2 +} */
    if (!ispower(cvtop(b, p, d), K, pt)) return 0;
    if (pt) *pt = gtrunc(*pt);
  }
  return 1;
}

/* We're studying whether a mod (q*p^e) is a K-th power, (q,p) = 1.
 * Decide mod p^e, then reduce a mod q unless q = NULL. */
static int
handle_pe(GEN *pa, GEN q, GEN L, GEN K, GEN p, long e)
{
  GEN t, A;
  long v = Z_pvalrem(*pa, p, &A), d = e - v;
  if (d <= 0) t = gen_0;
  else
  {
    ulong r;
    v = uabsdivui_rem(v, K, &r);
    if (r || !Up_ispower(A, K, p, d, L? &t: NULL)) return 0;
    if (L && v) t = mulii(t, powiu(p, v));
  }
  if (q) *pa = modii(*pa, q);
  if (L) vectrunc_append(L, mkintmod(t, powiu(p, e)));
  return 1;
}
long
Zn_ispower(GEN a, GEN q, GEN K, GEN *pt)
{
  GEN L, N;
  pari_sp av;
  long e, i, l;
  ulong pp;
  forprime_t S;

  if (!signe(a))
  {
    if (pt) {
      GEN t = cgetg(3, t_INTMOD);
      gel(t,1) = icopy(q); gel(t,2) = gen_0; *pt = t;
    }
    return 1;
  }
  /* a != 0 */
  av = avma;

  if (typ(q) != t_INT) /* integer factorization */
  {
    GEN P = gel(q,1), E = gel(q,2);
    l = lg(P);
    L = pt? vectrunc_init(l): NULL;
    for (i = 1; i < l; i++)
    {
      GEN p = gel(P,i);
      long e = itos(gel(E,i));
      if (!handle_pe(&a, NULL, L, K, p, e)) { avma = av; return 0; }
    }
    goto END;
  }
  if (!mod2(K)
      && kronecker(a, shifti(q,-vali(q))) == -1) { avma = av; return 0; }
  L = pt? vectrunc_init(expi(q)+1): NULL;
  u_forprime_init(&S, 2, tridiv_bound(q));
  while ((pp = u_forprime_next(&S)))
  {
    int stop;
    e = Z_lvalrem_stop(&q, pp, &stop);
    if (!e) continue;
    if (!handle_pe(&a, q, L, K, utoipos(pp), e)) { avma = av; return 0; }
    if (stop)
    {
      if (!is_pm1(q) && !handle_pe(&a, q, L, K, q, 1)) { avma = av; return 0; }
      goto END;
    }
  }
  l = lg(primetab);
  for (i = 1; i < l; i++)
  {
    GEN p = gel(primetab,i);
    e = Z_pvalrem(q, p, &q);
    if (!e) continue;
    if (!handle_pe(&a, q, L, K, p, e)) { avma = av; return 0; }
    if (is_pm1(q)) goto END;
  }
  N = gcdii(a,q);
  if (!is_pm1(N))
  {
    if (ifac_isprime(N))
    {
      e = Z_pvalrem(q, N, &q);
      if (!handle_pe(&a, q, L, K, N, e)) { avma = av; return 0; }
    }
    else
    {
      GEN part = ifac_start(N, 0);
      for(;;)
      {
        long e;
        GEN p;
        if (!ifac_next(&part, &p, &e)) break;
        e = Z_pvalrem(q, p, &q);
        if (!handle_pe(&a, q, L, K, p, e)) { avma = av; return 0; }
      }
    }
  }
  if (!is_pm1(q))
  {
    if (ifac_isprime(q))
    {
      if (!handle_pe(&a, q, L, K, q, 1)) { avma = av; return 0; }
    }
    else
    {
      GEN part = ifac_start(q, 0);
      for(;;)
      {
        long e;
        GEN p;
        if (!ifac_next(&part, &p, &e)) break;
        if (!handle_pe(&a, q, L, K, p, e)) { avma = av; return 0; }
      }
    }
  }
END:
  if (pt) *pt = gerepileupto(av, chinese1_coprime_Z(L));
  return 1;
}

static long
polmodispower(GEN x, GEN K, GEN *pt)
{
  pari_sp av = avma;
  GEN p = NULL, T = NULL;
  if (Rg_is_FpXQ(x, &T,&p) && p)
  {
    x = liftall_shallow(x);
    if (T) T = liftall_shallow(T);
    if (!Fq_ispower(x, K, T, p)) { avma = av; return 0; }
    if (!pt) { avma = av; return 1; }
    x = Fq_sqrtn(x, K, T,p, NULL);
    if (typ(x) == t_INT)
      x = Fp_to_mod(x,p);
    else
      x = mkpolmod(FpX_to_mod(x,p), FpX_to_mod(T,p));
    *pt = gerepilecopy(av, x); return 1;
  }
  pari_err_IMPL("ispower for general t_POLMOD");
  return 0;
}

long
issquareall(GEN x, GEN *pt)
{
  long tx = typ(x);
  GEN F;
  pari_sp av;

  if (!pt) return issquare(x);
  switch(tx)
  {
    case t_INT: return Z_issquareall(x, pt);
    case t_FRAC: av = avma;
      F = cgetg(3, t_FRAC);
      if (   !Z_issquareall(gel(x,1), &gel(F,1))
          || !Z_issquareall(gel(x,2), &gel(F,2))) { avma = av; return 0; }
      *pt = F; return 1;

    case t_POLMOD:
      return polmodispower(x, gen_2, pt);
    case t_POL: return polissquareall(x,pt);
    case t_RFRAC: av = avma;
      F = cgetg(3, t_RFRAC);
      if (   !issquareall(gel(x,1), &gel(F,1))
          || !polissquareall(gel(x,2), &gel(F,2))) { avma = av; return 0; }
      *pt = F; return 1;

    case t_REAL: case t_COMPLEX: case t_PADIC: case t_SER:
      if (!issquare(x)) return 0;
      *pt = gsqrt(x, DEFAULTPREC); return 1;

    case t_INTMOD:
      return Zn_ispower(gel(x,2), gel(x,1), gen_2, pt);

    case t_FFELT: return FF_issquareall(x, pt);

  }
  pari_err_TYPE("issquareall",x);
  return 0; /* LCOV_EXCL_LINE */
}

long
issquare(GEN x)
{
  pari_sp av;
  GEN a, p;
  long i, v;

  switch(typ(x))
  {
    case t_INT:
      return Z_issquare(x);

    case t_REAL:
      return (signe(x)>=0);

    case t_INTMOD:
      return Zn_ispower(gel(x,2), gel(x,1), gen_2, NULL);

    case t_FRAC:
      return Z_issquare(gel(x,1)) && Z_issquare(gel(x,2));

    case t_FFELT: return FF_issquareall(x, NULL);

    case t_COMPLEX:
      return 1;

    case t_PADIC:
      a = gel(x,4); if (!signe(a)) return 1;
      if (valp(x)&1) return 0;
      p = gel(x,2);
      if (!absequaliu(p, 2)) return (kronecker(a,p) != -1);

      v = precp(x); /* here p=2, a is odd */
      if ((v>=3 && mod8(a) != 1 ) ||
          (v==2 && mod4(a) != 1)) return 0;
      return 1;

    case t_POLMOD:
      return polmodispower(x, gen_2, NULL);

    case t_POL:
      return polissquareall(x,NULL);

    case t_SER:
      if (!signe(x)) return 1;
      if (valp(x)&1) return 0;
      return issquare(gel(x,2));

    case t_RFRAC:
      av = avma; i = issquare(gmul(gel(x,1),gel(x,2)));
      avma = av; return i;
  }
  pari_err_TYPE("issquare",x);
  return 0; /* LCOV_EXCL_LINE */
}
GEN gissquare(GEN x) { return issquare(x)? gen_1: gen_0; }
GEN gissquareall(GEN x, GEN *pt) { return issquareall(x,pt)? gen_1: gen_0; }

long
ispolygonal(GEN x, GEN S, GEN *N)
{
  pari_sp av = avma;
  GEN D, d, n;
  if (typ(x) != t_INT) pari_err_TYPE("ispolygonal", x);
  if (typ(S) != t_INT) pari_err_TYPE("ispolygonal", S);
  if (abscmpiu(S,3) < 0) pari_err_DOMAIN("ispolygonal","s","<", utoipos(3),S);
  if (signe(x) < 0) return 0;
  if (signe(x) == 0) { if (N) *N = gen_0; return 1; }
  if (is_pm1(x)) { if (N) *N = gen_1; return 1; }
  /* n = (sqrt( (8s - 16) x + (s-4)^2 ) + s - 4) / 2(s - 2) */
  if (abscmpiu(S, 1<<16) < 0) /* common case ! */
  {
    ulong s = S[2], r;
    if (s == 4) return Z_issquareall(x, N);
    if (s == 3)
      D = addiu(shifti(x, 3), 1);
    else
      D = addiu(mului(8*s - 16, x), (s-4)*(s-4));
    if (!Z_issquareall(D, &d)) { avma = av; return 0; }
    if (s == 3)
      d = subiu(d, 1);
    else
      d = addiu(d, s - 4);
    n = absdiviu_rem(d, 2*s - 4, &r);
    if (r) { avma = av; return 0; }
  }
  else
  {
    GEN r, S_2 = subiu(S,2), S_4 = subiu(S,4);
    D = addii(mulii(shifti(S_2,3), x), sqri(S_4));
    if (!Z_issquareall(D, &d)) { avma = av; return 0; }
    d = addii(d, S_4);
    n = dvmdii(shifti(d,-1), S_2, &r);
    if (r != gen_0) { avma = av; return 0; }
  }
  if (N) *N = gerepileuptoint(av, n); else avma = av;
  return 1;
}

/*********************************************************************/
/**                                                                 **/
/**                        PERFECT POWER                            **/
/**                                                                 **/
/*********************************************************************/
static long
polispower(GEN x, GEN K, GEN *pt)
{
  pari_sp av;
  long v, d, k = itos(K);
  GEN y, a, b;
  GEN T = NULL, p = NULL;

  if (!signe(x))
  {
    if (pt) *pt = gcopy(x);
    return 1;
  }
  d = degpol(x);
  if (d % k) return 0; /* degree not multiple of k */
  av = avma;
  if (RgX_is_FpXQX(x, &T, &p) && p)
  { /* over Fq */
    if (T && typ(T) == t_FFELT)
    {
      if (!FFX_ispower(x, k, T, pt)) { avma = av; return 0; }
      return 1;
    }
    x = RgX_to_FqX(x,T,p);
    if (!FqX_ispower(x, k, T,p, pt)) { avma = av; return 0; }
    if (pt)
      *pt = gerepileupto(av, FqX_to_mod(*pt, T, p));
    return 1;
  }
  v = RgX_valrem(x, &x);
  if (v % k) return 0;
  v /= k;
  a = gel(x,2); b = NULL;
  if (!ispower(a, K, &b)) { avma = av; return 0; }
  if (d)
  {
    GEN p = characteristic(x);
    a = leading_coeff(x);
    if (!ispower(a, K, &b)) { avma = av; return 0; }
    x = RgX_normalize(x);
    if (signe(p) && cmpii(p,K) <= 0)
      pari_err_IMPL("ispower(general t_POL) in small characteristic");
    y = gtrunc(gsqrtn(RgX_to_ser(x,lg(x)), K, NULL, 0));
    if (!RgX_equal(powgi(y, K), x)) { avma = av; return 0; }
  }
  else
    y = pol_1(varn(x));
  if (pt)
  {
    if (!gequal1(a))
    {
      if (!b) b = gsqrtn(a, K, NULL, DEFAULTPREC);
      y = gmul(b,y);
    }
    if (v) y = RgX_shift_shallow(y, v);
    *pt = gerepilecopy(av, y);
  }
  else avma = av;
  return 1;
}

long
Z_ispowerall(GEN x, ulong k, GEN *pt)
{
  long s = signe(x);
  ulong mask;
  if (!s) { if (pt) *pt = gen_0; return 1; }
  if (s > 0) {
    if (k == 2) return Z_issquareall(x, pt);
    if (k == 3) { mask = 1; return !!is_357_power(x, pt, &mask); }
    if (k == 5) { mask = 2; return !!is_357_power(x, pt, &mask); }
    if (k == 7) { mask = 4; return !!is_357_power(x, pt, &mask); }
    return is_kth_power(x, k, pt);
  }
  if (!odd(k)) return 0;
  if (Z_ispowerall(absi_shallow(x), k, pt))
  {
    if (pt) *pt = negi(*pt);
    return 1;
  };
  return 0;
}

/* is x a K-th power mod p ? Assume p prime. */
int
Fp_ispower(GEN x, GEN K, GEN p)
{
  pari_sp av = avma;
  GEN p_1;
  long r;
  x = modii(x, p);
  if (!signe(x) || equali1(x)) { avma = av; return 1; }
  /* implies p > 2 */
  p_1 = subiu(p,1);
  K = gcdii(K, p_1);
  if (absequaliu(K, 2)) { r = kronecker(x,p); avma = av; return (r > 0); }
  x = Fp_pow(x, diviiexact(p_1,K), p);
  avma = av; return equali1(x);
}

/* x unit defined modulo 2^e, e > 0, p prime */
static int
U2_issquare(GEN x, long e)
{
  long r = signe(x)>=0?mod8(x):8-mod8(x);
  if (e==1) return 1;
  if (e==2) return (r&3L) == 1;
  return r == 1;
}
/* x unit defined modulo p^e, e > 0, p prime */
static int
Up_issquare(GEN x, GEN p, long e)
{ return (absequaliu(p,2))? U2_issquare(x, e): kronecker(x,p)==1; }

long
Zn_issquare(GEN d, GEN fn)
{
  long j, np;
  if (typ(d) != t_INT) pari_err_TYPE("Zn_issquare",d);
  if (typ(fn) == t_INT) return Zn_ispower(d, fn, gen_2, NULL);
  /* integer factorization */
  np = nbrows(fn);
  for (j = 1; j <= np; ++j)
  {
    GEN  r, p = gcoeff(fn, j, 1);
    long e = itos(gcoeff(fn, j, 2));
    long v = Z_pvalrem(d,p,&r);
    if (v < e && (odd(v) || !Up_issquare(r, p, e-v))) return 0;
  }
  return 1;
}

static long
Qp_ispower(GEN x, GEN K, GEN *pt)
{
  pari_sp av = avma;
  GEN z = Qp_sqrtn(x, K, NULL);
  if (!z) { avma = av; return 0; }
  if (pt) *pt = z;
  return 1;
}

long
ispower(GEN x, GEN K, GEN *pt)
{
  GEN z;

  if (!K) return gisanypower(x, pt);
  if (typ(K) != t_INT) pari_err_TYPE("ispower",K);
  if (signe(K) <= 0) pari_err_DOMAIN("ispower","exponent","<=",gen_0,K);
  if (equali1(K)) { if (pt) *pt = gcopy(x); return 1; }
  switch(typ(x)) {
    case t_INT:
      if (lgefint(K) != 3) return 0;
      return Z_ispowerall(x, itou(K), pt);
    case t_FRAC:
    {
      GEN a = gel(x,1), b = gel(x,2);
      ulong k;
      if (lgefint(K) != 3) return 0;
      k = itou(K);
      if (pt) {
        z = cgetg(3, t_FRAC);
        if (Z_ispowerall(a, k, &a) && Z_ispowerall(b, k, &b)) {
          *pt = z; gel(z,1) = a; gel(z,2) = b; return 1;
        }
        avma = (pari_sp)(z + 3); return 0;
      }
      return Z_ispower(a, k) && Z_ispower(b, k);
    }
    case t_INTMOD:
      return Zn_ispower(gel(x,2), gel(x,1), K, pt);
    case t_FFELT:
      return FF_ispower(x, K, pt);

    case t_PADIC:
      return Qp_ispower(x, K, pt);
    case t_POLMOD:
      return polmodispower(x, K, pt);
    case t_POL:
      return polispower(x, K, pt);
    case t_RFRAC: {
      GEN a = gel(x,1), b = gel(x,2);
      if (pt) {
        z = cgetg(3, t_RFRAC);
        if (ispower(a, K, &a) && polispower(b, K, &b)) {
          *pt = z; gel(z,1) = a; gel(z,2) = b; return 1;
        }
        avma = (pari_sp)(z + 3); return 0;
      }
      return (ispower(a, K, NULL) && polispower(b, K, NULL));
    }
    case t_REAL:
      if (signe(x) < 0 && !mpodd(K)) return 0;
    case t_COMPLEX:
      if (pt) *pt = gsqrtn(x, K, NULL, DEFAULTPREC);
      return 1;

    case t_SER:
      if (signe(x) && (!dvdsi(valp(x), K) || !ispower(gel(x,2), K, NULL)))
        return 0;
      if (pt) *pt = gsqrtn(x, K, NULL, DEFAULTPREC);
      return 1;
  }
  pari_err_TYPE("ispower",x);
  return 0; /* LCOV_EXCL_LINE */
}

long
gisanypower(GEN x, GEN *pty)
{
  long tx = typ(x);
  ulong k, h;
  if (tx == t_INT) return Z_isanypower(x, pty);
  if (tx == t_FRAC)
  {
    pari_sp av = avma;
    GEN fa, P, E, a = gel(x,1), b = gel(x,2);
    long i, j, p, e;
    int sw = (abscmpii(a, b) > 0);

    if (sw) swap(a, b);
    k = Z_isanypower(a, pty? &a: NULL);
    if (!k)
    { /* a = -1,1 or not a pure power */
      if (!is_pm1(a)) { avma = av; return 0; }
      if (signe(a) < 0) b = negi(b);
      k = Z_isanypower(b, pty? &b: NULL);
      if (!k || !pty) { avma = av; return k; }
      *pty = gerepileupto(av, ginv(b));
      return k;
    }
    fa = factoru(k);
    P = gel(fa,1);
    E = gel(fa,2); h = k;
    for (i = lg(P) - 1; i > 0; i--)
    {
      p = P[i];
      e = E[i];
      for (j = 0; j < e; j++)
        if (!is_kth_power(b, p, &b)) break;
      if (j < e) k /= upowuu(p, e - j);
    }
    if (k == 1) { avma = av; return 0; }
    if (!pty) { avma = av; return k; }
    if (k != h) a = powiu(a, h/k);
    *pty = gerepilecopy(av, mkfrac(a, b));
    return k;
  }
  pari_err_TYPE("gisanypower", x);
  return 0; /* LCOV_EXCL_LINE */
}

/* v_p(x) = e != 0 for some p; return ispower(x,,&x), updating x.
 * No need to optimize for 2,3,5,7 powers (done before) */
static long
split_exponent(ulong e, GEN *x)
{
  GEN fa, P, E;
  long i, j, l, k = 1;
  if (e == 1) return 1;
  fa = factoru(e);
  P = gel(fa,1);
  E = gel(fa,2); l = lg(P);
  for (i = 1; i < l; i++)
  {
    ulong p = P[i];
    for (j = 0; j < E[i]; j++)
    {
      GEN y;
      if (!is_kth_power(*x, p, &y)) break;
      k *= p; *x = y;
    }
  }
  return k;
}

static long
Z_isanypower_nosmalldiv(GEN *px)
{ /* any prime divisor of x is > 102 */
  const double LOG2_103 = 6.6865; /* lower bound for log_2(103) */
  const double LOG103 = 4.6347; /* lower bound for log(103) */
  forprime_t T;
  ulong mask = 7, e2;
  long k, ex;
  GEN y, x = *px;

  k = 1;
  while (Z_issquareall(x, &y)) { k <<= 1; x = y; }
  while ( (ex = is_357_power(x, &y, &mask)) ) { k *= ex; x = y; }
  e2 = (ulong)((expi(x) + 1) / LOG2_103); /* >= log_103 (x) */
  if (u_forprime_init(&T, 11, e2))
  {
    GEN logx = NULL;
    const ulong Q = 30011; /* prime */
    ulong p, xmodQ;
    double dlogx = 0;
    /* cut off at x^(1/p) ~ 2^30 bits which seems to be about optimum;
     * for large p the modular checks are no longer competitively fast */
    while ( (ex = is_pth_power(x, &y, &T, 30)) )
    {
      k *= ex; x = y;
      e2 = (ulong)((expi(x) + 1) / LOG2_103);
      u_forprime_restrict(&T, e2);
    }
    if (DEBUGLEVEL>4) err_printf("Z_isanypower: now k=%ld, x=%ld-bit\n", k, expi(x));
    xmodQ = umodiu(x, Q);
    /* test Q | x, just in case */
    if (!xmodQ) { *px = x; return k * split_exponent(Z_lval(x,Q), px); }
    /* x^(1/p) < 2^31 */
    p = T.p;
    if (p <= e2)
    {
      logx = logr_abs( itor(x, DEFAULTPREC) );
      dlogx = rtodbl(logx);
      e2 = (ulong)(dlogx / LOG103); /* >= log_103(x) */
    }
    while (p && p <= e2)
    { /* is x a p-th power ? By computing y = round(x^(1/p)).
       * Check whether y^p = x, first mod Q, then exactly. */
      pari_sp av = avma;
      long e;
      GEN logy = divru(logx, p), y = grndtoi(mpexp(logy), &e);
      ulong ymodQ = umodiu(y,Q);
      if (e >= -10 || Fl_powu(ymodQ, p % (Q-1), Q) != xmodQ
                   || !equalii(powiu(y, p), x)) avma = av;
      else
      {
        k *= p; x = y; xmodQ = ymodQ; logx = logy; dlogx /= p;
        e2 = (ulong)(dlogx / LOG103); /* >= log_103(x) */
        u_forprime_restrict(&T, e2);
        continue; /* if success, retry same p */
      }
      p = u_forprime_next(&T);
    }
  }
  *px = x; return k;
}

static ulong tinyprimes[] = {
  2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71,
  73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151,
  157, 163, 167, 173, 179, 181, 191, 193, 197, 199
};

/* disregard the sign of x, caller will take care of x < 0 */
static long
Z_isanypower_aux(GEN x, GEN *pty)
{
  long ex, v, i, l, k;
  GEN y, P, E;
  ulong mask, e = 0;

  if (abscmpii(x, gen_2) < 0) return 0; /* -1,0,1 */

  if (signe(x) < 0) x = negi(x);
  k = l = 1;
  P = cgetg(26 + 1, t_VECSMALL);
  E = cgetg(26 + 1, t_VECSMALL);
  /* trial division */
  for(i = 0; i < 26; i++)
  {
    ulong p = tinyprimes[i];
    int stop;
    v = Z_lvalrem_stop(&x, p, &stop);
    if (v)
    {
      P[l] = p;
      E[l] = v; l++;
      e = ugcd(e, v); if (e == 1) goto END;
    }
    if (stop) {
      if (is_pm1(x)) k = e;
      goto END;
    }
  }

  if (e)
  { /* Bingo. Result divides e */
    long v3, v5, v7;
    ulong e2 = e;
    v = u_lvalrem(e2, 2, &e2);
    if (v)
    {
      for (i = 0; i < v; i++)
      {
        if (!Z_issquareall(x, &y)) break;
        k <<= 1; x = y;
      }
    }
    mask = 0;
    v3 = u_lvalrem(e2, 3, &e2); if (v3) mask = 1;
    v5 = u_lvalrem(e2, 5, &e2); if (v5) mask |= 2;
    v7 = u_lvalrem(e2, 7, &e2); if (v7) mask |= 4;
    while ( (ex = is_357_power(x, &y, &mask)) ) {
      x = y;
      switch(ex)
      {
        case 3: k *= 3; if (--v3 == 0) mask &= ~1; break;
        case 5: k *= 5; if (--v5 == 0) mask &= ~2; break;
        case 7: k *= 7; if (--v7 == 0) mask &= ~4; break;
      }
    }
    k *= split_exponent(e2, &x);
  }
  else
    k = Z_isanypower_nosmalldiv(&x);
END:
  if (pty && k != 1)
  {
    if (e)
    { /* add missing small factors */
      y = powuu(P[1], E[1] / k);
      for (i = 2; i < l; i++) y = mulii(y, powuu(P[i], E[i] / k));
      x = equali1(x)? y: mulii(x,y);
    }
    *pty = x;
  }
  return k == 1? 0: k;
}

long
Z_isanypower(GEN x, GEN *pty)
{
  pari_sp av = avma;
  long k = Z_isanypower_aux(x, pty);
  if (!k) { avma = av; return 0; }
  if (signe(x) < 0)
  {
    long v = vals(k);
    if (v)
    {
      GEN y;
      k >>= v;
      if (k == 1) { avma = av; return 0; }
      if (!pty) { avma = av; return k; }
      y = *pty;
      y = powiu(y, 1<<v);
      togglesign(y);
      *pty = gerepileuptoint(av, y);
      return k;
    }
    if (pty) togglesign_safe(pty);
  }
  if (pty) *pty = gerepilecopy(av, *pty); else avma = av;
  return k;
}

/* Faster than */
/*   !cmpii(n, int2n(vali(n))) */
/*   !cmpis(shifti(n, -vali(n)), 1) */
/*   expi(n) == vali(n) */
/*   hamming(n) == 1 */
/* even for single-word values, and much faster for multiword values. */
/* If all you have is a word, you can just use n & !(n & (n-1)). */
long
Z_ispow2(GEN n)
{
  GEN xp;
  long i, lx;
  ulong u;
  if (signe(n) != 1) return 0;
  xp = int_LSW(n);
  lx = lgefint(n);
  u = *xp;
  for (i = 3; i < lx; ++i)
  {
    if (u) return 0;
    xp = int_nextW(xp);
    u = *xp;
  }
  return !(u & (u-1));
}

static long
isprimepower_i(GEN n, GEN *pt, long flag)
{
  pari_sp av = avma;
  long i, v;

  if (typ(n) != t_INT) pari_err_TYPE("isprimepower", n);
  if (signe(n) <= 0) return 0;

  if (lgefint(n) == 3)
  {
    ulong p;
    v = uisprimepower(n[2], &p);
    if (v)
    {
      if (pt) *pt = utoipos(p);
      return v;
    }
    return 0;
  }
  for (i = 0; i < 26; i++)
  {
    ulong p = tinyprimes[i];
    v = Z_lvalrem(n, p, &n);
    if (v)
    {
      avma = av;
      if (!is_pm1(n)) return 0;
      if (pt) *pt = utoipos(p);
      return v;
    }
  }
  /* p | n => p >= 103 */
  v = Z_isanypower_nosmalldiv(&n); /* expensive */
  if (!(flag? isprime(n): BPSW_psp(n))) { avma = av; return 0; }
  if (pt) *pt = gerepilecopy(av, n); else avma = av;
  return v;
}
long
isprimepower(GEN n, GEN *pt) { return isprimepower_i(n,pt,1); }
long
ispseudoprimepower(GEN n, GEN *pt) { return isprimepower_i(n,pt,0); }

long
uisprimepower(ulong n, ulong *pp)
{ /* We must have CUTOFF^11 >= ULONG_MAX and CUTOFF^3 < ULONG_MAX.
   * Tests suggest that 200-300 is the best range for 64-bit platforms. */
  const ulong CUTOFF = 200UL;
  const long TINYCUTOFF = 46;  /* tinyprimes[45] = 199 */
  const ulong CUTOFF3 = CUTOFF*CUTOFF*CUTOFF;
#ifdef LONG_IS_64BIT
  /* primes preceeding the appropriate root of ULONG_MAX. */
  const ulong ROOT9 = 137;
  const ulong ROOT8 = 251;
  const ulong ROOT7 = 563;
  const ulong ROOT5 = 7129;
  const ulong ROOT4 = 65521;
#else
  const ulong ROOT9 = 11;
  const ulong ROOT8 = 13;
  const ulong ROOT7 = 23;
  const ulong ROOT5 = 83;
  const ulong ROOT4 = 251;
#endif
  ulong mask;
  long v, i;
  int e;
  if (n < 2) return 0;
  if (!odd(n)) {
    if (n & (n-1)) return 0;
    *pp = 2; return vals(n);
  }
  if (n < 8) { *pp = n; return 1; } /* 3,5,7 */
  for (i = 1/*skip p=2*/; i < TINYCUTOFF; i++)
  {
    ulong p = tinyprimes[i];
    if (n % p == 0)
    {
      v = u_lvalrem(n, p, &n);
      if (n == 1) { *pp = p; return v; }
      return 0;
    }
  }
  /* p | n => p >= CUTOFF */

  if (n < CUTOFF3)
  {
    if (n < CUTOFF*CUTOFF || uisprime_101(n)) { *pp = n; return 1; }
    if (uissquareall(n, &n)) { *pp = n; return 2; }
    return 0;
  }

  /* Check for squares, fourth powers, and eighth powers as appropriate. */
  v = 1;
  if (uissquareall(n, &n)) {
    v <<= 1;
    if (CUTOFF <= ROOT4 && uissquareall(n, &n)) {
      v <<= 1;
      if (CUTOFF <= ROOT8 && uissquareall(n, &n)) v <<= 1;
    }
  }

  if (CUTOFF > ROOT5) mask = 1;
  else
  {
    const ulong CUTOFF5 = CUTOFF3*CUTOFF*CUTOFF;
    if (n < CUTOFF5) mask = 1; else mask = 3;
    if (CUTOFF <= ROOT7)
    {
      const ulong CUTOFF7 = CUTOFF5*CUTOFF*CUTOFF;
      if (n >= CUTOFF7) mask = 7;
    }
  }

  if (CUTOFF <= ROOT9 && (e = uis_357_power(n, &n, &mask))) { v *= e; mask=1; }
  if ((e = uis_357_power(n, &n, &mask))) v *= e;

  if (uisprime_101(n)) { *pp = n; return v; }
  return 0;
}

/*********************************************************************/
/**                                                                 **/
/**                        KRONECKER SYMBOL                         **/
/**                                                                 **/
/*********************************************************************/
/* t = 3,5 mod 8 ?  (= 2 not a square mod t) */
static int
ome(long t)
{
  switch(t & 7)
  {
    case 3:
    case 5: return 1;
    default: return 0;
  }
}
/* t a t_INT, is t = 3,5 mod 8 ? */
static int
gome(GEN t)
{ return signe(t)? ome( mod2BIL(t) ): 0; }

/* assume y odd, return kronecker(x,y) * s */
static long
krouu_s(ulong x, ulong y, long s)
{
  ulong x1 = x, y1 = y, z;
  while (x1)
  {
    long r = vals(x1);
    if (r)
    {
      if (odd(r) && ome(y1)) s = -s;
      x1 >>= r;
    }
    if (x1 & y1 & 2) s = -s;
    z = y1 % x1; y1 = x1; x1 = z;
  }
  return (y1 == 1)? s: 0;
}

long
kronecker(GEN x, GEN y)
{
  pari_sp av = avma;
  long s = 1, r;
  ulong xu, yu;

  if (typ(x) != t_INT) pari_err_TYPE("kronecker",x);
  if (typ(y) != t_INT) pari_err_TYPE("kronecker",y);
  switch (signe(y))
  {
    case -1: y = negi(y); if (signe(x) < 0) s = -1; break;
    case 0: return is_pm1(x);
  }
  r = vali(y);
  if (r)
  {
    if (!mpodd(x)) { avma = av; return 0; }
    if (odd(r) && gome(x)) s = -s;
    y = shifti(y,-r);
  }
  x = modii(x,y);
  while (lgefint(x) > 3) /* x < y */
  {
    GEN z;
    r = vali(x);
    if (r)
    {
      if (odd(r) && gome(y)) s = -s;
      x = shifti(x,-r);
    }
    /* x=3 mod 4 && y=3 mod 4 ? (both are odd here) */
    if (mod2BIL(x) & mod2BIL(y) & 2) s = -s;
    z = remii(y,x); y = x; x = z;
    if (gc_needed(av,2))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"kronecker");
      gerepileall(av, 2, &x, &y);
    }
  }
  xu = itou(x);
  if (!xu) return is_pm1(y)? s: 0;
  r = vals(xu);
  if (r)
  {
    if (odd(r) && gome(y)) s = -s;
    xu >>= r;
  }
  /* x=3 mod 4 && y=3 mod 4 ? (both are odd here) */
  if (xu & mod2BIL(y) & 2) s = -s;
  yu = umodiu(y, xu);
  avma = av; return krouu_s(yu, xu, s);
}

long
krois(GEN x, long y)
{
  ulong yu;
  long s = 1;

  if (y <= 0)
  {
    if (y == 0) return is_pm1(x);
    yu = (ulong)-y; if (signe(x) < 0) s = -1;
  }
  else
    yu = (ulong)y;
  if (!odd(yu))
  {
    long r;
    if (!mpodd(x)) return 0;
    r = vals(yu); yu >>= r;
    if (odd(r) && gome(x)) s = -s;
  }
  return krouu_s(umodiu(x, yu), yu, s);
}
/* assume y != 0 */
long
kroiu(GEN x, ulong y)
{
  long r;
  if (odd(y)) return krouu_s(umodiu(x,y), y, 1);
  if (!mpodd(x)) return 0;
  r = vals(y); y >>= r;
  return krouu_s(umodiu(x,y), y, (odd(r) && gome(x))? -1: 1);
}

/* assume y > 0, odd, return s * kronecker(x,y) */
static long
krouodd(ulong x, GEN y, long s)
{
  long r;
  if (lgefint(y) == 3) return krouu_s(x, y[2], s);
  if (!x) return 0; /* y != 1 */
  r = vals(x);
  if (r)
  {
    if (odd(r) && gome(y)) s = -s;
    x >>= r;
  }
  /* x=3 mod 4 && y=3 mod 4 ? (both are odd here) */
  if (x & mod2BIL(y) & 2) s = -s;
  return krouu_s(umodiu(y,x), x, s);
}

long
krosi(long x, GEN y)
{
  const pari_sp av = avma;
  long s = 1, r;
  switch (signe(y))
  {
    case -1: y = negi(y); if (x < 0) s = -1; break;
    case 0: return (x==1 || x==-1);
  }
  r = vali(y);
  if (r)
  {
    if (!odd(x)) { avma = av; return 0; }
    if (odd(r) && ome(x)) s = -s;
    y = shifti(y,-r);
  }
  if (x < 0) { x = -x; if (mod4(y) == 3) s = -s; }
  s = krouodd((ulong)x, y, s);
  avma = av; return s;
}

long
kroui(ulong x, GEN y)
{
  const pari_sp av = avma;
  long s = 1, r;
  switch (signe(y))
  {
    case -1: y = negi(y); break;
    case 0: return x==1UL;
  }
  r = vali(y);
  if (r)
  {
    if (!odd(x)) { avma = av; return 0; }
    if (odd(r) && ome(x)) s = -s;
    y = shifti(y,-r);
  }
  s = krouodd(x, y, s);
  avma = av; return s;
}

long
kross(long x, long y)
{
  ulong yu;
  long s = 1;

  if (y <= 0)
  {
    if (y == 0) return (labs(x)==1);
    yu = (ulong)-y; if (x < 0) s = -1;
  }
  else
    yu = (ulong)y;
  if (!odd(yu))
  {
    long r;
    if (!odd(x)) return 0;
    r = vals(yu); yu >>= r;
    if (odd(r) && ome(x)) s = -s;
  }
  x %= (long)yu; if (x < 0) x += yu;
  return krouu_s((ulong)x, yu, s);
}

long
krouu(ulong x, ulong y)
{
  long r;
  if (odd(y)) return krouu_s(x, y, 1);
  if (!odd(x)) return 0;
  r = vals(y); y >>= r;
  return krouu_s(x, y, (odd(r) && ome(x))? -1: 1);
}

/*********************************************************************/
/**                                                                 **/
/**                          HILBERT SYMBOL                         **/
/**                                                                 **/
/*********************************************************************/
/* x,y are t_INT or t_REAL */
static long
mphilbertoo(GEN x, GEN y)
{
  long sx = signe(x), sy = signe(y);
  if (!sx || !sy) return 0;
  return (sx < 0 && sy < 0)? -1: 1;
}

long
hilbertii(GEN x, GEN y, GEN p)
{
  pari_sp av;
  long oddvx, oddvy, z;

  if (!p) return mphilbertoo(x,y);
  if (is_pm1(p) || signe(p) < 0) pari_err_PRIME("hilbertii",p);
  if (!signe(x) || !signe(y)) return 0;
  av = avma;
  oddvx = odd(Z_pvalrem(x,p,&x));
  oddvy = odd(Z_pvalrem(y,p,&y));
  /* x, y are p-units, compute hilbert(x * p^oddvx, y * p^oddvy, p) */
  if (absequaliu(p, 2))
  {
    z = (Mod4(x) == 3 && Mod4(y) == 3)? -1: 1;
    if (oddvx && gome(y)) z = -z;
    if (oddvy && gome(x)) z = -z;
  }
  else
  {
    z = (oddvx && oddvy && mod4(p) == 3)? -1: 1;
    if (oddvx && kronecker(y,p) < 0) z = -z;
    if (oddvy && kronecker(x,p) < 0) z = -z;
  }
  avma = av; return z;
}

static void
err_prec(void) { pari_err_PREC("hilbert"); }
static void
err_p(GEN p, GEN q) { pari_err_MODULUS("hilbert", p,q); }
static void
err_oo(GEN p) { pari_err_MODULUS("hilbert", p, strtoGENstr("oo")); }

/* x t_INTMOD, *pp = prime or NULL [ unset, set it to x.mod ].
 * Return lift(x) provided it's p-adic accuracy is large enough to decide
 * hilbert()'s value [ problem at p = 2 ] */
static GEN
lift_intmod(GEN x, GEN *pp)
{
  GEN p = *pp, N = gel(x,1);
  x = gel(x,2);
  if (!p)
  {
    *pp = p = N;
    switch(itos_or_0(p))
    {
      case 2:
      case 4: err_prec();
    }
    return x;
  }
  if (!signe(p)) err_oo(N);
  if (absequaliu(p,2))
  { if (vali(N) <= 2) err_prec(); }
  else
  { if (!dvdii(N,p)) err_p(N,p); }
  if (!signe(x)) err_prec();
  return x;
}
/* x t_PADIC, *pp = prime or NULL [ unset, set it to x.p ].
 * Return lift(x)*p^(v(x) mod 2) provided it's p-adic accuracy is large enough
 * to decide hilbert()'s value [ problem at p = 2 ]*/
static GEN
lift_padic(GEN x, GEN *pp)
{
  GEN p = *pp, q = gel(x,2), y = gel(x,4);
  if (!p) *pp = p = q;
  else if (!equalii(p,q)) err_p(p, q);
  if (absequaliu(p,2) && precp(x) <= 2) err_prec();
  if (!signe(y)) err_prec();
  return odd(valp(x))? mulii(p,y): y;
}

long
hilbert(GEN x, GEN y, GEN p)
{
  pari_sp av = avma;
  long tx = typ(x), ty = typ(y), z;

  if (p && typ(p) != t_INT) pari_err_TYPE("hilbert",p);
  if (tx == t_REAL)
  {
    if (p && signe(p)) err_oo(p);
    switch (ty)
    {
      case t_INT:
      case t_REAL: return mphilbertoo(x,y);
      case t_FRAC: return mphilbertoo(x,gel(y,1));
      default: pari_err_TYPE2("hilbert",x,y);
    }
  }
  if (ty == t_REAL)
  {
    if (p && signe(p)) err_oo(p);
    switch (tx)
    {
      case t_INT:
      case t_REAL: return mphilbertoo(x,y);
      case t_FRAC: return mphilbertoo(gel(x,1),y);
      default: pari_err_TYPE2("hilbert",x,y);
    }
  }
  if (tx == t_INTMOD) { x = lift_intmod(x, &p); tx = t_INT; }
  if (ty == t_INTMOD) { y = lift_intmod(y, &p); ty = t_INT; }

  if (tx == t_PADIC) { x = lift_padic(x, &p); tx = t_INT; }
  if (ty == t_PADIC) { y = lift_padic(y, &p); ty = t_INT; }

  if (tx == t_FRAC) { tx = t_INT; x = p? mulii(gel(x,1),gel(x,2)): gel(x,1); }
  if (ty == t_FRAC) { ty = t_INT; y = p? mulii(gel(y,1),gel(y,2)): gel(y,1); }

  if (tx != t_INT || ty != t_INT) pari_err_TYPE2("hilbert",x,y);
  if (p && !signe(p)) p = NULL;
  z = hilbertii(x,y,p); avma = av; return z;
}

/*******************************************************************/
/*                                                                 */
/*                       SQUARE ROOT MODULO p                      */
/*                                                                 */
/*******************************************************************/

static ulong
Fl_2gener_pre_all(long e, ulong p, ulong pi)
{
  ulong y, m;
  long k, i;
  ulong q = (p-1) >> e; /* q = (p-1)/2^oo is odd */
  for (k=2; ; k++)
  { /* loop terminates for k < p (even if p composite) */
    i = krouu(k, p);
    if (i >= 0)
    {
      if (i) continue;
      pari_err_PRIME("Fl_sqrt [modulus]",utoi(p));
    }
    y = m = Fl_powu_pre(k, q, p, pi);
    for (i=1; i<e; i++)
      if ((m = Fl_sqr_pre(m, p, pi)) == 1) break;
    if (i == e) break; /* success */
  }
  return y;
}

ulong
Fl_2gener_pre(ulong p, ulong pi)
{ return Fl_2gener_pre_all(vals(p-1), p, pi); }

/* Tonelli-Shanks. Assume p is prime and (a,p) != -1. */
ulong
Fl_sqrt_pre_i(ulong a, ulong y, ulong p, ulong pi)
{
  long i, e, k;
  ulong p1, q, v, w;

  if (!a) return 0;
  p1 = p - 1; e = vals(p1);
  if (e == 0) /* p = 2 */
  {
    if (p != 2) pari_err_PRIME("Fl_sqrt [modulus]",utoi(p));
    return ((a & 1) == 0)? 0: 1;
  }
  q = p1 >> e; /* q = (p-1)/2^oo is odd */
  if (e == 1)    y = p1;
  else if (y==0) y = Fl_2gener_pre_all(e, p, pi);
  p1 = Fl_powu_pre(a, q >> 1, p, pi); /* a ^ [(q-1)/2] */
  if (!p1) return 0;
  v = Fl_mul_pre(a, p1, p, pi);
  w = Fl_mul_pre(v, p1, p, pi);
  while (w != 1)
  { /* a*w = v^2, y primitive 2^e-th root of 1
       a square --> w even power of y, hence w^(2^(e-1)) = 1 */
    p1 = Fl_sqr_pre(w,p,pi);
    for (k=1; p1 != 1 && k < e; k++) p1 = Fl_sqr_pre(p1,p,pi);
    if (k == e) return ~0UL;
    /* w ^ (2^k) = 1 --> w = y ^ (u * 2^(e-k)), u odd */
    p1 = y;
    for (i=1; i < e-k; i++) p1 = Fl_sqr_pre(p1, p, pi);
    y = Fl_sqr_pre(p1, p, pi); e = k;
    w = Fl_mul_pre(y, w, p, pi);
    v = Fl_mul_pre(v, p1, p, pi);
  }
  p1 = p - v; if (v > p1) v = p1;
  return v;
}

ulong
Fl_sqrt(ulong a, ulong p)
{
  ulong pi = get_Fl_red(p);
  return Fl_sqrt_pre_i(a, 0, p, pi);
}

ulong
Fl_sqrt_pre(ulong a, ulong p, ulong pi)
{
  return Fl_sqrt_pre_i(a, 0, p, pi);
}

static ulong
Fl_lgener_pre_all(ulong l, long e, ulong r, ulong p, ulong pi, ulong *pt_m)
{
  ulong x, y, m;
  ulong le1 = upowuu(l, e-1);
  for (x = 2; ; x++)
  {
    y = Fl_powu_pre(x, r, p, pi);
    if (y==1) continue;
    m = Fl_powu_pre(y, le1, p, pi);
    if (m != 1) break;
  }
  *pt_m = m;
  return y;
}

/* solve x^l = a , l prime in G of order q.
 *
 * q =  (l^e)*r, e >= 1, (r,l) = 1
 * y generates the l-Sylow of G
 * m = y^(l^(e-1)) != 1 */
static ulong
Fl_sqrtl_raw(ulong a, ulong l, ulong e, ulong r, ulong p, ulong pi, ulong y, ulong m)
{
  ulong p1, v, w, z, dl;
  ulong u2;
  if (a==0) return a;
  u2 = Fl_inv(l%r, r);
  v = Fl_powu_pre(a, u2, p, pi);
  w = Fl_powu_pre(v, l, p, pi);
  w = Fl_mul_pre(w, Fl_inv(a, p), p, pi);
  if (w==1) return v;
  if (y==0) y = Fl_lgener_pre_all(l, e, r, p, pi, &m);
  while (w!=1)
  {
    ulong k = 0;
    p1 = w;
    do
    {
      z = p1; p1 = Fl_powu_pre(p1, l, p, pi);
      k++;
    } while (p1!=1);
    if (k==e) return ULONG_MAX;
    dl = Fl_log_pre(z, m, l, p, pi);
    dl = Fl_neg(dl, l);
    p1 = Fl_powu_pre(y,dl*upowuu(l,e-k-1),p,pi);
    m = Fl_powu_pre(m, dl, p, pi);
    e = k;
    v = Fl_mul_pre(p1,v,p,pi);
    y = Fl_powu_pre(p1,l,p,pi);
    w = Fl_mul_pre(y,w,p,pi);
  }
  return v;
}

static ulong
Fl_sqrtl_i(ulong a, ulong l, ulong p, ulong pi, ulong y, ulong m)
{
  ulong r, e = u_lvalrem(p-1, l, &r);
  return Fl_sqrtl_raw(a, l, e, r, p, pi, y, m);
}

ulong
Fl_sqrtl_pre(ulong a, ulong l, ulong p, ulong pi)
{
  return Fl_sqrtl_i(a, l, p, pi, 0, 0);
}

ulong
Fl_sqrtl(ulong a, ulong l, ulong p)
{
  ulong pi = get_Fl_red(p);
  return Fl_sqrtl_i(a, l, p, pi, 0, 0);
}

ulong
Fl_sqrtn_pre(ulong a, long n, ulong p, ulong pi, ulong *zetan)
{
  ulong m, q = p-1, z;
  ulong nn = n >= 0 ? (ulong)n: -(ulong)n;
  if (a==0)
  {
    if (n < 0) pari_err_INV("Fl_sqrtn", mkintmod(gen_0,utoi(p)));
    if (zetan) *zetan = 1UL;
    return 0;
  }
  if (n==1)
  {
    if (zetan) *zetan = 1;
    return n < 0? Fl_inv(a,p): a;
  }
  if (n==2)
  {
    if (zetan) *zetan = p-1;
    return Fl_sqrt_pre_i(a, 0, p, pi);
  }
  if (a == 1 && !zetan) return a;
  m = ugcd(nn, q);
  z = 1;
  if (m!=1)
  {
    GEN F = factoru(m);
    long i, j, e;
    ulong r, zeta, y, l;
    for (i = nbrows(F); i; i--)
    {
      l = ucoeff(F,i,1);
      j = ucoeff(F,i,2);
      e = u_lvalrem(q,l, &r);
      y = Fl_lgener_pre_all(l, e, r, p, pi, &zeta);
      if (zetan)
        z = Fl_mul_pre(z, Fl_powu_pre(y, upowuu(l,e-j), p, pi), p, pi);
      if (a!=1)
        do
        {
          a = Fl_sqrtl_raw(a, l, e, r, p, pi, y, zeta);
          if (a==ULONG_MAX) return ULONG_MAX;
        } while (--j);
    }
  }
  if (m != nn)
  {
    ulong qm = q/m, nm = nn/m;
    a = Fl_powu_pre(a, Fl_inv(nm%qm, qm), p, pi);
  }
  if (n < 0) a = Fl_inv(a, p);
  if (zetan) *zetan = z;
  return a;
}

ulong
Fl_sqrtn(ulong a, long n, ulong p, ulong *zetan)
{
  ulong pi = get_Fl_red(p);
  return Fl_sqrtn_pre(a, n, p, pi, zetan);
}

/* Cipolla is better than Tonelli-Shanks when e = v_2(p-1) is "too big".
 * Otherwise, is a constant times worse; for p = 3 (mod 4), is about 3 times worse,
 * and in average is about 2 or 2.5 times worse. But try both algorithms for
 * S(n) = (2^n+3)^2-8 with n = 750, 771, 779, 790, 874, 1176, 1728, 2604, etc.
 *
 * If X^2 := t^2 - a  is not a square in F_p (so X is in F_p^2), then
 *   (t+X)^(p+1) = (t-X)(t+X) = a,   hence  sqrt(a) = (t+X)^((p+1)/2)  in F_p^2.
 * If (a|p)=1, then sqrt(a) is in F_p.
 * cf: LNCS 2286, pp 430-434 (2002)  [Gonzalo Tornaria] */

/* compute y^2, y = y[1] + y[2] X */
static GEN
sqrt_Cipolla_sqr(void *data, GEN y)
{
  GEN u = gel(y,1), v = gel(y,2), p = gel(data,2), n = gel(data,3);
  GEN u2 = sqri(u), v2 = sqri(v);
  v = subii(sqri(addii(v,u)), addii(u2,v2));
  u = addii(u2, mulii(v2,n));
  /* NOT mkvec2: must be gerepileupto-able */
  retmkvec2(modii(u,p), modii(v,p));
}
/* compute (t+X) y^2 */
static GEN
sqrt_Cipolla_msqr(void *data, GEN y)
{
  GEN u = gel(y,1), v = gel(y,2), a = gel(data,1), p = gel(data,2), gt = gel(data,4);
  ulong t = gt[2];
  GEN d = addii(u, mului(t,v)), d2= sqri(d);
  GEN b = remii(mulii(a,v), p);
  u = subii(mului(t,d2), mulii(b,addii(u,d)));
  v = subii(d2, mulii(b,v));
  /* NOT mkvec2: must be gerepileupto-able */
  retmkvec2(modii(u,p), modii(v,p));
}
/* assume a reduced mod p [ otherwise correct but inefficient ] */
static GEN
sqrt_Cipolla(GEN a, GEN p)
{
  pari_sp av1;
  GEN u, v, n, y, pov2;
  ulong t;

  if (kronecker(a, p) < 0) return NULL;
  pov2 = shifti(p,-1);
  if (cmpii(a,pov2) > 0) a = subii(a,p); /* center: avoid multiplying by huge base*/

  av1 = avma;
  for(t=1; ; t++)
  {
    n = subsi((long)(t*t), a);
    if (kronecker(n, p) < 0) break;
    avma = av1;
  }

  /* compute (t+X)^((p-1)/2) =: u+vX */
  u = utoipos(t);
  y = gen_pow_fold(mkvec2(u, gen_1), pov2, mkvec4(a,p,n,u),
                         sqrt_Cipolla_sqr, sqrt_Cipolla_msqr);
  /* Now u+vX = (t+X)^((p-1)/2); thus
   *   (u+vX)(t+X) = sqrt(a) + 0 X
   * Whence,
   *   sqrt(a) = (u+vt)t - v*a
   *   0       = (u+vt)
   * Thus a square root is v*a */

  v = Fp_mul(gel(y, 2), a, p);
  if (cmpii(v,pov2) > 0) v = subii(p,v);
  return v;
}

/* Return NULL if p is found to be composite */
static GEN
Fp_2gener_all(long e, GEN p)
{
  GEN y, m;
  long k;
  GEN q = shifti(subiu(p,1), -e); /* q = (p-1)/2^oo is odd */
  if (e==0 && !equaliu(p,2)) return NULL;
  for (k=2; ; k++)
  {
    long i = krosi(k, p);
    if (i >= 0)
    {
      if (i) continue;
      return NULL;
    }
    y = m = Fp_pow(utoi(k), q, p);
    for (i=1; i<e; i++)
      if (equali1(m = Fp_sqr(m, p))) break;
    if (i == e) break; /* success */
  }
  return y;
}

/* Return NULL if p is found to be composite */
GEN
Fp_2gener(GEN p)
{ return Fp_2gener_all(vali(subis(p,1)),p); }

/* smallest square root */
static GEN
choose_sqrt(GEN v, GEN p)
{
  pari_sp av = avma;
  GEN q = subii(p,v);
  if (cmpii(v,q) > 0) v = q; else avma = av;
  return v;
}
/* Tonelli-Shanks. Assume p is prime and return NULL if (a,p) = -1. */
GEN
Fp_sqrt_i(GEN a, GEN y, GEN p)
{
  pari_sp av = avma;
  long i, k, e;
  GEN p1, q, v, w;

  if (typ(a) != t_INT) pari_err_TYPE("Fp_sqrt",a);
  if (typ(p) != t_INT) pari_err_TYPE("Fp_sqrt",p);
  if (signe(p) <= 0 || equali1(p)) pari_err_PRIME("Fp_sqrt",p);
  if (lgefint(p) == 3)
  {
    ulong pp = uel(p,2), u = Fl_sqrt(umodiu(a, pp), pp);
    if (u == ~0UL) return NULL;
    return utoi(u);
  }

  a = modii(a, p); if (!signe(a)) { avma = av; return gen_0; }
  p1 = subiu(p,1); e = vali(p1);
  if (e <= 2)
  { /* direct formulas more efficient */
    pari_sp av2;
    if (e == 0) pari_err_PRIME("Fp_sqrt [modulus]",p); /* p != 2 */
    if (e == 1)
    {
      q = addiu(shifti(p1,-2),1); /* (p+1) / 4 */
      v = Fp_pow(a, q, p);
    }
    else
    { /* Atkin's formula */
      GEN i, a2 = shifti(a,1);
      if (cmpii(a2,p) >= 0) a2 = subii(a2,p);
      q = shifti(p1, -3); /* (p-5)/8 */
      v = Fp_pow(a2, q, p);
      i = Fp_mul(a2, Fp_sqr(v,p), p); /* i^2 = -1 */
      v = Fp_mul(a, Fp_mul(v, subiu(i,1), p), p);
    }
    av2 = avma;
    /* must check equality in case (a/p) = -1 or p not prime */
    e = equalii(Fp_sqr(v,p), a); avma = av2;
    return e? gerepileuptoint(av,choose_sqrt(v,p)): NULL;
  }
  /* On average, Cipolla is better than Tonelli/Shanks if and only if
   * e(e-1) > 8*log2(n)+20, see LNCS 2286 pp 430 [GTL] */
  if (e*(e-1) > 20 + 8 * expi(p))
  {
    v = sqrt_Cipolla(a,p); if (!v) { avma = av; return NULL; }
    return gerepileuptoint(av,v);
  }
  if (!y)
  {
    y = Fp_2gener_all(e, p);
    if (!y) pari_err_PRIME("Fp_sqrt [modulus]",p);
  }
  q = shifti(p1,-e); /* q = (p-1)/2^oo is odd */
  p1 = Fp_pow(a, shifti(q,-1), p); /* a ^ (q-1)/2 */
  v = Fp_mul(a, p1, p);
  w = Fp_mul(v, p1, p);
  while (!equali1(w))
  { /* a*w = v^2, y primitive 2^e-th root of 1
       a square --> w even power of y, hence w^(2^(e-1)) = 1 */
    p1 = Fp_sqr(w,p);
    for (k=1; !equali1(p1) && k < e; k++) p1 = Fp_sqr(p1,p);
    if (k == e) { avma=av; return NULL; } /* p composite or (a/p) != 1 */
    /* w ^ (2^k) = 1 --> w = y ^ (u * 2^(e-k)), u odd */
    p1 = y;
    for (i=1; i < e-k; i++) p1 = Fp_sqr(p1,p);
    y = Fp_sqr(p1, p); e = k;
    w = Fp_mul(y, w, p);
    v = Fp_mul(v, p1, p);
    if (gc_needed(av,1))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"Fp_sqrt");
      gerepileall(av,3, &y,&w,&v);
    }
  }
  return gerepileuptoint(av, choose_sqrt(v,p));
}

GEN
Fp_sqrt(GEN a, GEN p)
{
  return Fp_sqrt_i(a, NULL, p);
}

/*********************************************************************/
/**                                                                 **/
/**                        GCD & BEZOUT                             **/
/**                                                                 **/
/*********************************************************************/

GEN
lcmii(GEN x, GEN y)
{
  pari_sp av;
  GEN a, b;
  if (!signe(x) || !signe(y)) return gen_0;
  av = avma;
  a = gcdii(x,y); if (!equali1(a)) y = diviiexact(y,a);
  b = mulii(x,y); setabssign(b); return gerepileuptoint(av, b);
}

/* given x in assume 0 < x < N; return u in (Z/NZ)^* such that u x = gcd(x,N) (mod N);
 * set *pd = gcd(x,N) */
GEN
Fp_invgen(GEN x, GEN N, GEN *pd)
{
  GEN d, d0, e, v;
  if (lgefint(N) == 3)
  {
    ulong dd, NN = N[2], xx = umodiu(x,NN);
    if (!xx) { *pd = N; return gen_0; }
    xx = Fl_invgen(xx, NN, &dd);
    *pd = utoi(dd); return utoi(xx);
  }
  *pd = d = bezout(x, N, &v, NULL);
  if (equali1(d)) return v;
  /* vx = gcd(x,N) (mod N), v coprime to N/d but need not be coprime to N */
  e = diviiexact(N,d);
  d0 = Z_ppo(d, e); /* d = d0 d1, d0 coprime to N/d, rad(d1) | N/d */
  if (equali1(d0)) return v;
  if (!equalii(d,d0)) e = lcmii(e, diviiexact(d,d0));
  return Z_chinese_coprime(v, gen_1, e, d0, mulii(e,d0));
}

/*********************************************************************/
/**                                                                 **/
/**                      CHINESE REMAINDERS                         **/
/**                                                                 **/
/*********************************************************************/

/* Chinese Remainder Theorem.  x and y must have the same type (integermod,
 * polymod, or polynomial/vector/matrix recursively constructed with these
 * as coefficients). Creates (with the same type) a z in the same residue
 * class as x and the same residue class as y, if it is possible.
 *
 * We also allow (during recursion) two identical objects even if they are
 * not integermod or polymod. For example:
 *
 * ? x = [1, Mod(5, 11), Mod(X + Mod(2, 7), X^2 + 1)];
 * ? y = [1, Mod(7, 17), Mod(X + Mod(0, 3), X^2 + 1)];
 * ? chinese(x, y)
 * %3 = [1, Mod(16, 187), Mod(X + mod(9, 21), X^2 + 1)] */

static GEN
gen_chinese(GEN x, GEN(*f)(GEN,GEN))
{
  GEN z = gassoc_proto(f,x,NULL);
  if (z == gen_1) retmkintmod(gen_0,gen_1);
  return z;
}

/* x t_INTMOD, y t_POLMOD; promote x to t_POLMOD mod Pol(x.mod) then
 * call chinese: makes Mod(0,1) a better "neutral" element */
static GEN
chinese_intpol(GEN x,GEN y)
{
  pari_sp av = avma;
  GEN z = mkpolmod(gel(x,2), scalarpol_shallow(gel(x,1), varn(gel(y,1))));
  return gerepileupto(av, chinese(z, y));
}

GEN
chinese1(GEN x) { return gen_chinese(x,chinese); }

GEN
chinese(GEN x, GEN y)
{
  pari_sp av;
  long tx = typ(x), ty;
  GEN z,p1,p2,d,u,v;

  if (!y) return chinese1(x);
  if (gidentical(x,y)) return gcopy(x);
  ty = typ(y);
  if (tx == ty) switch(tx)
  {
    case t_POLMOD:
    {
      GEN A = gel(x,1), B = gel(y,1);
      GEN a = gel(x,2), b = gel(y,2);
      if (varn(A)!=varn(B)) pari_err_VAR("chinese",A,B);
      if (RgX_equal(A,B)) retmkpolmod(chinese(a,b), gcopy(A)); /*same modulus*/
      av = avma;
      d = RgX_extgcd(A,B,&u,&v);
      p2 = gsub(b, a);
      if (!gequal0(gmod(p2, d))) break;
      p1 = gdiv(A,d);
      p2 = gadd(a, gmul(gmul(u,p1), p2));

      z = cgetg(3, t_POLMOD);
      gel(z,1) = gmul(p1,B);
      gel(z,2) = gmod(p2,gel(z,1));
      return gerepileupto(av, z);
    }
    case t_INTMOD:
    {
      GEN A = gel(x,1), B = gel(y,1);
      GEN a = gel(x,2), b = gel(y,2), c, d, C, U;
      z = cgetg(3,t_INTMOD);
      Z_chinese_pre(A, B, &C, &U, &d);
      c = Z_chinese_post(a, b, C, U, d);
      if (!c) pari_err_OP("chinese", x,y);
      avma = (pari_sp)z;
      gel(z,1) = icopy(C);
      gel(z,2) = icopy(c); return z;
    }
    case t_POL:
    {
      long i, lx = lg(x), ly = lg(y);
      if (varn(x) != varn(y)) break;
      if (lx < ly) { swap(x,y); lswap(lx,ly); }
      z = cgetg(lx, t_POL); z[1] = x[1];
      for (i=2; i<ly; i++) gel(z,i) = chinese(gel(x,i),gel(y,i));
      for (   ; i<lx; i++) gel(z,i) = gcopy(gel(x,i));
      return z;
    }

    case t_VEC: case t_COL: case t_MAT:
    {
      long i, lx;
      z = cgetg_copy(x, &lx); if (lx!=lg(y)) break;
      for (i=1; i<lx; i++) gel(z,i) = chinese(gel(x,i),gel(y,i));
      return z;
    }
  }
  if (tx == t_POLMOD && ty == t_INTMOD) return chinese_intpol(y,x);
  if (ty == t_POLMOD && tx == t_INTMOD) return chinese_intpol(x,y);
  pari_err_OP("chinese",x,y);
  return NULL; /* LCOV_EXCL_LINE */
}

/* init chinese(Mod(.,A), Mod(.,B)) */
void
Z_chinese_pre(GEN A, GEN B, GEN *pC, GEN *pU, GEN *pd)
{
  GEN u, d = bezout(A,B,&u,NULL); /* U = u(A/d), u(A/d) + v(B/d) = 1 */
  GEN t = diviiexact(A,d);
  *pU = mulii(u, t);
  *pC = mulii(t, B);
  if (pd) *pd = d;
}
/* Assume C = lcm(A, B), U = 0 mod (A/d), U = 1 mod (B/d), a = b mod d,
 * where d = gcd(A,B) or NULL, return x = a (mod A), b (mod B).
 * If d not NULL, check whether a = b mod d. */
GEN
Z_chinese_post(GEN a, GEN b, GEN C, GEN U, GEN d)
{
  GEN b_a;
  if (!signe(a))
  {
    if (d && !dvdii(b, d)) return NULL;
    return Fp_mul(b, U, C);
  }
  b_a = subii(b,a);
  if (d && !dvdii(b_a, d)) return NULL;
  return modii(addii(a, mulii(U, b_a)), C);
}
static ulong
u_chinese_post(ulong a, ulong b, ulong C, ulong U)
{
  if (!a) return Fl_mul(b, U, C);
  return Fl_add(a, Fl_mul(U, Fl_sub(b,a,C), C), C);
}

GEN
Z_chinese(GEN a, GEN b, GEN A, GEN B)
{
  pari_sp av = avma;
  GEN C, U; Z_chinese_pre(A, B, &C, &U, NULL);
  return gerepileuptoint(av, Z_chinese_post(a,b, C, U, NULL));
}
GEN
Z_chinese_all(GEN a, GEN b, GEN A, GEN B, GEN *pC)
{
  GEN U; Z_chinese_pre(A, B, pC, &U, NULL);
  return Z_chinese_post(a,b, *pC, U, NULL);
}

/* return lift(chinese(a mod A, b mod B))
 * assume(A,B)=1, a,b,A,B integers and C = A*B */
GEN
Z_chinese_coprime(GEN a, GEN b, GEN A, GEN B, GEN C)
{
  pari_sp av = avma;
  GEN U = mulii(Fp_inv(A,B), A);
  return gerepileuptoint(av, Z_chinese_post(a,b,C,U, NULL));
}
ulong
u_chinese_coprime(ulong a, ulong b, ulong A, ulong B, ulong C)
{ return u_chinese_post(a,b,C, A * Fl_inv(A % B,B)); }

/* chinese1 for coprime moduli in Z */
static GEN
chinese1_coprime_Z_aux(GEN x, GEN y)
{
  GEN z = cgetg(3, t_INTMOD);
  GEN A = gel(x,1), a = gel(x, 2);
  GEN B = gel(y,1), b = gel(y, 2), C = mulii(A,B);
  pari_sp av = avma;
  GEN U = mulii(Fp_inv(A,B), A);
  gel(z,2) = gerepileuptoint(av, Z_chinese_post(a,b,C,U, NULL));
  gel(z,1) = C; return z;
}
GEN
chinese1_coprime_Z(GEN x) {return gen_chinese(x,chinese1_coprime_Z_aux);}

/*********************************************************************/
/**                                                                 **/
/**                    MODULAR EXPONENTIATION                       **/
/**                                                                 **/
/*********************************************************************/

/* xa, ya = t_VECSMALL */
GEN
ZV_producttree(GEN xa)
{
  long n = lg(xa)-1;
  long m = n==1 ? 1: expu(n-1)+1;
  GEN T = cgetg(m+1, t_VEC), t;
  long i, j, k;
  t = cgetg(((n+1)>>1)+1, t_VEC);
  if (typ(xa)==t_VECSMALL)
  {
    for (j=1, k=1; k<n; j++, k+=2)
      gel(t, j) = muluu(xa[k], xa[k+1]);
    if (k==n) gel(t, j) = utoi(xa[k]);
  } else {
    for (j=1, k=1; k<n; j++, k+=2)
      gel(t, j) = mulii(gel(xa,k), gel(xa,k+1));
    if (k==n) gel(t, j) = icopy(gel(xa,k));
  }
  gel(T,1) = t;
  for (i=2; i<=m; i++)
  {
    GEN u = gel(T, i-1);
    long n = lg(u)-1;
    t = cgetg(((n+1)>>1)+1, t_VEC);
    for (j=1, k=1; k<n; j++, k+=2)
      gel(t, j) = mulii(gel(u, k), gel(u, k+1));
    if (k==n) gel(t, j) = gel(u, k);
    gel(T, i) = t;
  }
  return T;
}

/* return [A mod P[i], i=1..#P], T = ZV_producttree(P) */
GEN
Z_ZV_mod_tree(GEN A, GEN P, GEN T)
{
  long i,j,k;
  long m = lg(T)-1, n = lg(P)-1;
  GEN t;
  GEN Tp = cgetg(m+1, t_VEC);
  gel(Tp, m) = mkvec(A);
  for (i=m-1; i>=1; i--)
  {
    GEN u = gel(T, i);
    GEN v = gel(Tp, i+1);
    long n = lg(u)-1;
    t = cgetg(n+1, t_VEC);
    for (j=1, k=1; k<n; j++, k+=2)
    {
      gel(t, k)   = modii(gel(v, j), gel(u, k));
      gel(t, k+1) = modii(gel(v, j), gel(u, k+1));
    }
    if (k==n) gel(t, k) = gel(v, j);
    gel(Tp, i) = t;
  }
  {
    GEN u = gel(T, i+1);
    GEN v = gel(Tp, i+1);
    long l = lg(u)-1;
    if (typ(P)==t_VECSMALL)
    {
      GEN R = cgetg(n+1, t_VECSMALL);
      for (j=1, k=1; j<=l; j++, k+=2)
      {
        uel(R,k) = umodiu(gel(v, j), P[k]);
        if (k < n)
          uel(R,k+1) = umodiu(gel(v, j), P[k+1]);
      }
      return R;
    }
    else
    {
      GEN R = cgetg(n+1, t_VEC);
      for (j=1, k=1; j<=l; j++, k+=2)
      {
        gel(R,k) = modii(gel(v, j), gel(P,k));
        if (k < n)
          gel(R,k+1) = modii(gel(v, j), gel(P,k+1));
      }
      return R;
    }
  }
}

/* T = ZV_producttree(P), R = ZV_chinesetree(P,T) */
GEN
ZV_chinese_tree(GEN A, GEN P, GEN T, GEN R)
{
  long m = lg(T)-1, n = lg(A)-1;
  long i,j,k;
  GEN Tp = cgetg(m+1, t_VEC);
  GEN M = gel(T, 1);
  GEN t = cgetg(lg(M), t_VEC);
  if (typ(P)==t_VECSMALL)
  {
    for (j=1, k=1; k<n; j++, k+=2)
    {
      pari_sp av = avma;
      GEN a = mului(A[k], gel(R,k)), b = mului(A[k+1], gel(R,k+1));
      GEN tj = modii(addii(mului(P[k],b), mului(P[k+1],a)), gel(M,j));
      gel(t, j) = gerepileuptoint(av, tj);
    }
    if (k==n) gel(t, j) = modii(mului(A[k], gel(R,k)), gel(M, j));
  } else
  {
    for (j=1, k=1; k<n; j++, k+=2)
    {
      pari_sp av = avma;
      GEN a = mulii(gel(A,k), gel(R,k)), b = mulii(gel(A,k+1), gel(R,k+1));
      GEN tj = modii(addii(mulii(gel(P,k),b), mulii(gel(P,k+1),a)), gel(M,j));
      gel(t, j) = gerepileuptoint(av, tj);
    }
    if (k==n) gel(t, j) = modii(mulii(gel(A,k), gel(R,k)), gel(M, j));
  }
  gel(Tp, 1) = t;
  for (i=2; i<=m; i++)
  {
    GEN u = gel(T, i-1), M = gel(T, i);
    GEN t = cgetg(lg(M), t_VEC);
    GEN v = gel(Tp, i-1);
    long n = lg(v)-1;
    for (j=1, k=1; k<n; j++, k+=2)
    {
      pari_sp av = avma;
      gel(t, j) = gerepileuptoint(av, modii(addii(mulii(gel(u, k), gel(v, k+1)),
            mulii(gel(u, k+1), gel(v, k))), gel(M, j)));
    }
    if (k==n) gel(t, j) = gel(v, k);
    gel(Tp, i) = t;
  }
  return gmael(Tp,m,1);
}

static GEN
ncV_polint_center_tree(GEN vA, GEN P, GEN T, GEN R, GEN m2)
{
  long i, l = lg(gel(vA,1)), n = lg(P);
  GEN mod = gmael(T, lg(T)-1, 1), V = cgetg(l, t_COL);
  for (i=1; i < l; i++)
  {
    pari_sp av = avma;
    GEN c, A = cgetg(n, typ(P));
    long j;
    for (j=1; j < n; j++) A[j] = mael(vA,j,i);
    c = Fp_center(ZV_chinese_tree(A, P, T, R), mod, m2);
    gel(V,i) = gerepileuptoint(av, c);
  }
  return V;
}

static GEN
nxV_polint_center_tree(GEN vA, GEN P, GEN T, GEN R, GEN m2)
{
  long i, j, l, n = lg(P);
  GEN mod = gmael(T, lg(T)-1, 1), V, w;
  w = cgetg(n, t_VECSMALL);
  for(j=1; j<n; j++) w[j] = lg(gel(vA,j));
  l = vecsmall_max(w);
  V = cgetg(l, t_POL);
  V[1] = mael(vA,1,1);
  for (i=2; i < l; i++)
  {
    pari_sp av = avma;
    GEN c, A = cgetg(n, typ(P));
    if (typ(P)==t_VECSMALL)
      for (j=1; j < n; j++) A[j] = i < w[j] ? mael(vA,j,i): 0;
    else
      for (j=1; j < n; j++) gel(A,j) = i < w[j] ? gmael(vA,j,i): gen_0;
    c = Fp_center(ZV_chinese_tree(A, P, T, R), mod, m2);
    gel(V,i) = gerepileuptoint(av, c);
  }
  return ZX_renormalize(V, l);
}

static GEN
nxCV_polint_center_tree(GEN vA, GEN P, GEN T, GEN R, GEN m2)
{
  long i, j, l = lg(gel(vA,1)), n = lg(P);
  GEN A = cgetg(n, t_VEC);
  GEN V = cgetg(l, t_COL);
  for (i=1; i < l; i++)
  {
    for (j=1; j < n; j++) gel(A,j) = gmael(vA,j,i);
    gel(V,i) = nxV_polint_center_tree(A, P, T, R, m2);
  }
  return V;
}

static GEN
polint_chinese(GEN worker, GEN mA, GEN P)
{
  long i, j, l = lg(gel(mA,1)), n = lg(P);
  long pending = 0, workid, cnt = 0;
  struct pari_mt pt;
  GEN done, va, M;
  GEN A = cgetg(n, t_VEC);
  va = mkvec(gen_0);
  M = cgetg(l, t_MAT);
  if (DEBUGLEVEL>2) err_printf("Start parallel Chinese remainder: ");
  mt_queue_start_lim(&pt, worker, l-1);
  for (i=1; i<l || pending; i++)
  {
    for(j=1; j < n; j++) gel(A,j) = gmael(mA,j,i);
    gel(va, 1) = A;
    mt_queue_submit(&pt, i, i<l? va: NULL);
    done = mt_queue_get(&pt, &workid, &pending);
    if (done)
    {
      gel(M,workid) = done;
      if (DEBUGLEVEL>2) err_printf("%ld%% ",(++cnt)*100/(l-1));
    }
  }
  if (DEBUGLEVEL>2) err_printf("\n");
  mt_queue_end(&pt);
  return M;
}

GEN
nxMV_polint_center_tree_worker(GEN vA, GEN T, GEN R, GEN P, GEN m2)
{
  return nxCV_polint_center_tree(vA, P, T, R, m2);
}

static GEN
nxMV_polint_center_tree_seq(GEN vA, GEN P, GEN T, GEN R, GEN m2)
{
  long i, j, l = lg(gel(vA,1)), n = lg(P);
  GEN A = cgetg(n, t_VEC);
  GEN V = cgetg(l, t_MAT);
  for (i=1; i < l; i++)
  {
    for (j=1; j < n; j++) gel(A,j) = gmael(vA,j,i);
    gel(V,i) = nxCV_polint_center_tree(A, P, T, R, m2);
  }
  return V;
}

static GEN
nxMV_polint_center_tree(GEN mA, GEN P, GEN T, GEN R, GEN m2)
{
  GEN worker = snm_closure(is_entry("_nxMV_polint_worker"), mkvec4(T, R, P, m2));
  return polint_chinese(worker, mA, P);
}

static GEN
nmV_polint_center_tree_seq(GEN vA, GEN P, GEN T, GEN R, GEN m2)
{
  long i, j, l = lg(gel(vA,1)), n = lg(P);
  GEN A = cgetg(n, t_VEC);
  GEN V = cgetg(l, t_MAT);
  for (i=1; i < l; i++)
  {
    for (j=1; j < n; j++) gel(A,j) = gmael(vA,j,i);
    gel(V,i) = ncV_polint_center_tree(A, P, T, R, m2);
  }
  return V;
}

GEN
nmV_polint_center_tree_worker(GEN vA, GEN T, GEN R, GEN P, GEN m2)
{
  return ncV_polint_center_tree(vA, P, T, R, m2);
}

static GEN
nmV_polint_center_tree(GEN mA, GEN P, GEN T, GEN R, GEN m2)
{
  GEN worker = snm_closure(is_entry("_polint_worker"), mkvec4(T, R, P, m2));
  return polint_chinese(worker, mA, P);
}

/* return [A mod P[i], i=1..#P] */
GEN
Z_ZV_mod(GEN A, GEN P)
{
  pari_sp av = avma;
  return gerepilecopy(av, Z_ZV_mod_tree(A, P, ZV_producttree(P)));
}
/* P a t_VECSMALL */
GEN
Z_nv_mod(GEN A, GEN P)
{
  pari_sp av = avma;
  return gerepileuptoleaf(av, Z_ZV_mod_tree(A, P, ZV_producttree(P)));
}
/* B a ZX, T = ZV_producttree(P) */
GEN
ZX_nv_mod_tree(GEN B, GEN A, GEN T)
{
  pari_sp av;
  long i, j, l = lg(B), n = lg(A)-1;
  GEN V = cgetg(n+1, t_VEC);
  for (j=1; j <= n; j++)
  {
    gel(V, j) = cgetg(l, t_VECSMALL);
    mael(V, j, 1) = B[1]&VARNBITS;
  }
  av = avma;
  for (i=2; i < l; i++)
  {
    GEN v = Z_ZV_mod_tree(gel(B, i), A, T);
    for (j=1; j <= n; j++)
      mael(V, j, i) = v[j];
    avma = av;
  }
  for (j=1; j <= n; j++)
    (void) Flx_renormalize(gel(V, j), l);
  return V;
}

static GEN
to_ZX(GEN a, long v) { return typ(a)==t_INT? scalarpol(a,v): a; }

GEN
ZXX_nv_mod_tree(GEN P, GEN xa, GEN T, long w)
{
  pari_sp av = avma;
  long i, j, l = lg(P), n = lg(xa)-1, vP = varn(P);
  GEN V = cgetg(n+1, t_VEC);
  for (j=1; j <= n; j++)
  {
    gel(V, j) = cgetg(l, t_POL);
    mael(V, j, 1) = vP;
  }
  for (i=2; i < l; i++)
  {
    GEN v = ZX_nv_mod_tree(to_ZX(gel(P, i), w), xa, T);
    for (j=1; j <= n; j++)
      gmael(V, j, i) = gel(v,j);
  }
  for (j=1; j <= n; j++)
    (void) FlxX_renormalize(gel(V, j), l);
  return gerepilecopy(av, V);
}

GEN
ZXC_nv_mod_tree(GEN C, GEN xa, GEN T, long w)
{
  pari_sp av = avma;
  long i, j, l = lg(C), n = lg(xa)-1;
  GEN V = cgetg(n+1, t_VEC);
  for (j = 1; j <= n; j++)
    gel(V, j) = cgetg(l, t_COL);
  for (i = 1; i < l; i++)
  {
    GEN v = ZX_nv_mod_tree(to_ZX(gel(C, i), w), xa, T);
    for (j = 1; j <= n; j++)
      gmael(V, j, i) = gel(v,j);
  }
  return gerepilecopy(av, V);
}

GEN
ZXM_nv_mod_tree(GEN M, GEN xa, GEN T, long w)
{
  pari_sp av = avma;
  long i, j, l = lg(M), n = lg(xa)-1;
  GEN V = cgetg(n+1, t_VEC);
  for (j=1; j <= n; j++)
    gel(V, j) = cgetg(l, t_MAT);
  for (i=1; i < l; i++)
  {
    GEN v = ZXC_nv_mod_tree(gel(M, i), xa, T, w);
    for (j=1; j <= n; j++)
      gmael(V, j, i) = gel(v,j);
  }
  return gerepilecopy(av, V);
}

/* B a ZX, T = ZV_producttree(P) */
GEN
ZV_nv_mod_tree(GEN B, GEN A, GEN T)
{
  pari_sp av;
  long i, j, l = lg(B), n = lg(A)-1;
  GEN V = cgetg(n+1, t_VEC);
  for (j=1; j <= n; j++)
    gel(V, j) = cgetg(l, t_VECSMALL);
  av = avma;
  for (i=1; i < l; i++)
  {
    GEN v = Z_ZV_mod_tree(gel(B, i), A, T);
    for (j=1; j <= n; j++)
      mael(V, j, i) = v[j];
    avma = av;
  }
  return V;
}

GEN
ZM_nv_mod_tree(GEN M, GEN xa, GEN T)
{
  pari_sp av = avma;
  long i, j, l = lg(M), n = lg(xa)-1;
  GEN V = cgetg(n+1, t_VEC);
  for (j=1; j <= n; j++)
    gel(V, j) = cgetg(l, t_MAT);
  for (i=1; i < l; i++)
  {
    GEN v = ZV_nv_mod_tree(gel(M, i), xa, T);
    for (j=1; j <= n; j++)
      gmael(V, j, i) = gel(v,j);
  }
  return gerepilecopy(av, V);
}

static GEN
ZV_sqr(GEN z)
{
  long i,l = lg(z);
  GEN x = cgetg(l, t_VEC);
  if (typ(z)==t_VECSMALL)
    for (i=1; i<l; i++) gel(x,i) = sqru(z[i]);
  else
    for (i=1; i<l; i++) gel(x,i) = sqri(gel(z,i));
  return x;
}

static GEN
ZT_sqr(GEN z)
{
  if (typ(z) == t_INT)
    return sqri(z);
  else
  {
    long i,l = lg(z);
    GEN x = cgetg(l, t_VEC);
    for (i=1; i<l; i++) gel(x,i) = ZT_sqr(gel(z,i));
    return x;
  }
}

static GEN
ZV_invdivexact(GEN y, GEN x)
{
  long i, l = lg(y);
  GEN z = cgetg(l,t_VEC);
  if (typ(x)==t_VECSMALL)
    for (i=1; i<l; i++)
    {
      pari_sp av = avma;
      ulong a = Fl_inv(umodiu(diviuexact(gel(y,i),x[i]), x[i]), x[i]);
      avma = av;
      gel(z,i) = utoipos(a);
    }
  else
    for (i=1; i<l; i++)
      gel(z,i) = Fp_inv(diviiexact(gel(y,i), gel(x,i)), gel(x,i));
  return z;
}

/* P t_VECSMALL or t_VEC of t_INT  */
GEN
ZV_chinesetree(GEN P, GEN T)
{
  GEN T2 = ZT_sqr(T), P2 = ZV_sqr(P);
  GEN mod = gmael(T,lg(T)-1,1);
  return ZV_invdivexact(Z_ZV_mod_tree(mod, P2, T2), P);
}

static GEN
gc_chinese(pari_sp av, GEN T, GEN a, GEN *pt_mod)
{
  if (!pt_mod)
    return gerepileupto(av, a);
  else
  {
    GEN mod = gmael(T, lg(T)-1, 1);
    gerepileall(av, 2, &a, &mod);
    *pt_mod = mod;
    return a;
  }
}

GEN
ZV_chinese_center(GEN A, GEN P, GEN *pt_mod)
{
  pari_sp av = avma;
  GEN T = ZV_producttree(P);
  GEN R = ZV_chinesetree(P, T);
  GEN a = ZV_chinese_tree(A, P, T, R);
  GEN mod = gmael(T, lg(T)-1, 1);
  GEN ca = Fp_center(a, mod, shifti(mod,-1));
  return gc_chinese(av, T, ca, pt_mod);
}

GEN
ZV_chinese(GEN A, GEN P, GEN *pt_mod)
{
  pari_sp av = avma;
  GEN T = ZV_producttree(P);
  GEN R = ZV_chinesetree(P, T);
  GEN a = ZV_chinese_tree(A, P, T, R);
  return gc_chinese(av, T, a, pt_mod);
}

GEN
nxV_chinese_center_tree(GEN A, GEN P, GEN T, GEN R)
{
  pari_sp av = avma;
  GEN m2 = shifti(gmael(T, lg(T)-1, 1), -1);
  GEN a = nxV_polint_center_tree(A, P, T, R, m2);
  return gerepileupto(av, a);
}

GEN
nxV_chinese_center(GEN A, GEN P, GEN *pt_mod)
{
  pari_sp av = avma;
  GEN T = ZV_producttree(P);
  GEN R = ZV_chinesetree(P, T);
  GEN m2 = shifti(gmael(T, lg(T)-1, 1), -1);
  GEN a = nxV_polint_center_tree(A, P, T, R, m2);
  return gc_chinese(av, T, a, pt_mod);
}

GEN
ncV_chinese_center(GEN A, GEN P, GEN *pt_mod)
{
  pari_sp av = avma;
  GEN T = ZV_producttree(P);
  GEN R = ZV_chinesetree(P, T);
  GEN m2 = shifti(gmael(T, lg(T)-1, 1), -1);
  GEN a = ncV_polint_center_tree(A, P, T, R, m2);
  return gc_chinese(av, T, a, pt_mod);
}

GEN
nmV_chinese_center_tree(GEN A, GEN P, GEN T, GEN R)
{
  pari_sp av = avma;
  GEN m2 = shifti(gmael(T, lg(T)-1, 1), -1);
  GEN a = nmV_polint_center_tree(A, P, T, R, m2);
  return gerepileupto(av, a);
}

GEN
nmV_chinese_center_tree_seq(GEN A, GEN P, GEN T, GEN R)
{
  pari_sp av = avma;
  GEN m2 = shifti(gmael(T, lg(T)-1, 1), -1);
  GEN a = nmV_polint_center_tree_seq(A, P, T, R, m2);
  return gerepileupto(av, a);
}

GEN
nmV_chinese_center(GEN A, GEN P, GEN *pt_mod)
{
  pari_sp av = avma;
  GEN T = ZV_producttree(P);
  GEN R = ZV_chinesetree(P, T);
  GEN m2 = shifti(gmael(T, lg(T)-1, 1), -1);
  GEN a = nmV_polint_center_tree(A, P, T, R, m2);
  return gc_chinese(av, T, a, pt_mod);
}

GEN
nxMV_chinese_center_tree_seq(GEN A, GEN P, GEN T, GEN R)
{
  pari_sp av = avma;
  GEN m2 = shifti(gmael(T, lg(T)-1, 1), -1);
  GEN a = nxMV_polint_center_tree_seq(A, P, T, R, m2);
  return gerepileupto(av, a);
}

GEN
nxMV_chinese_center(GEN A, GEN P, GEN *pt_mod)
{
  pari_sp av = avma;
  GEN T = ZV_producttree(P);
  GEN R = ZV_chinesetree(P, T);
  GEN m2 = shifti(gmael(T, lg(T)-1, 1), -1);
  GEN a = nxMV_polint_center_tree(A, P, T, R, m2);
  return gc_chinese(av, T, a, pt_mod);
}

/**********************************************************************
 **                                                                  **
 **                    Powering  over (Z/NZ)^*, small N              **
 **                                                                  **
 **********************************************************************/

/* 2^n mod p; assume n > 1 */
static ulong
Fl_2powu_pre(ulong n, ulong p, ulong pi)
{
  ulong y = 2;
  int j = 1+bfffo(n);
  /* normalize, i.e set highest bit to 1 (we know n != 0) */
  n<<=j; j = BITS_IN_LONG-j; /* first bit is now implicit */
  for (; j; n<<=1,j--)
  {
    y = Fl_sqr_pre(y,p,pi);
    if (n & HIGHBIT) y = Fl_double(y, p);
  }
  return y;
}

/* 2^n mod p; assume n > 1 and !(p & HIGHMASK) */
static ulong
Fl_2powu(ulong n, ulong p)
{
  ulong y = 2;
  int j = 1+bfffo(n);
  /* normalize, i.e set highest bit to 1 (we know n != 0) */
  n<<=j; j = BITS_IN_LONG-j; /* first bit is now implicit */
  for (; j; n<<=1,j--)
  {
    y = (y*y) % p;
    if (n & HIGHBIT) y = Fl_double(y, p);
  }
  return y;
}

ulong
Fl_powu_pre(ulong x, ulong n0, ulong p, ulong pi)
{
  ulong y, z, n;
  if (n0 <= 1)
  { /* frequent special cases */
    if (n0 == 1) return x;
    if (n0 == 0) return 1;
  }
  if (x <= 2)
  {
    if (x == 2) return Fl_2powu_pre(n0, p, pi);
    return x; /* 0 or 1 */
  }
  y = 1; z = x; n = n0;
  for(;;)
  {
    if (n&1) y = Fl_mul_pre(y,z,p,pi);
    n>>=1; if (!n) return y;
    z = Fl_sqr_pre(z,p,pi);
  }
}

ulong
Fl_powu(ulong x, ulong n0, ulong p)
{
  ulong y, z, n;
  if (n0 <= 2)
  { /* frequent special cases */
    if (n0 == 2) return Fl_sqr(x,p);
    if (n0 == 1) return x;
    if (n0 == 0) return 1;
  }
  if (x <= 1) return x; /* 0 or 1 */
  if (p & HIGHMASK)
    return Fl_powu_pre(x, n0, p, get_Fl_red(p));
  if (x == 2) return Fl_2powu(n0, p);
  y = 1; z = x; n = n0;
  for(;;)
  {
    if (n&1) y = (y*z) % p;
    n>>=1; if (!n) return y;
    z = (z*z) % p;
  }
}

/* Reduce data dependency to maximize internal parallelism */
GEN
Fl_powers_pre(ulong x, long n, ulong p, ulong pi)
{
  long i, k;
  GEN powers = cgetg(n + 2, t_VECSMALL);
  powers[1] = 1; if (n == 0) return powers;
  powers[2] = x;
  for (i = 3, k=2; i <= n; i+=2, k++)
  {
    powers[i] = Fl_sqr_pre(powers[k], p, pi);
    powers[i+1] = Fl_mul_pre(powers[k], powers[k+1], p, pi);
  }
  if (i==n+1)
    powers[i] = Fl_sqr_pre(powers[k], p, pi);
  return powers;
}

GEN
Fl_powers(ulong x, long n, ulong p)
{
  return Fl_powers_pre(x, n, p, get_Fl_red(p));
}

/**********************************************************************
 **                                                                  **
 **                    Powering  over (Z/NZ)^*, large N              **
 **                                                                  **
 **********************************************************************/

static GEN
Fp_dblsqr(GEN x, GEN N)
{
  GEN z = shifti(Fp_sqr(x, N), 1);
  return cmpii(z, N) >= 0? subii(z, N): z;
}

typedef struct muldata {
  GEN (*sqr)(void * E, GEN x);
  GEN (*mul)(void * E, GEN x, GEN y);
  GEN (*mul2)(void * E, GEN x);
} muldata;

/* modified Barrett reduction with one fold */
/* See Fast Modular Reduction, W. Hasenplaugh, G. Gaubatz, V. Gopal, ARITH 18 */

static GEN
Fp_invmBarrett(GEN p, long s)
{
  GEN R, Q = dvmdii(int2n(3*s),p,&R);
  return mkvec2(Q,R);
}

/* a <= (N-1)^2, 2^(2s-2) <= N < 2^(2s). Return 0 <= r < N such that
 * a = r (mod N) */
static GEN
Fp_rem_mBarrett(GEN a, GEN B, long s, GEN N)
{
  pari_sp av = avma;
  GEN P = gel(B, 1), Q = gel(B, 2); /* 2^(3s) = P N + Q, 0 <= Q < N */
  long t = expi(P)+1; /* 2^(t-1) <= P < 2^t */
  GEN u = shifti(a, -3*s), v = remi2n(a, 3*s); /* a = 2^(3s)u + v */
  GEN A = addii(v, mulii(Q,u)); /* 0 <= A < 2^(3s+1) */
  GEN q = shifti(mulii(shifti(A, t-3*s), P), -t); /* A/N - 4 < q <= A/N */
  GEN r = subii(A, mulii(q, N));
  GEN sr= subii(r,N);     /* 0 <= r < 4*N */
  if (signe(sr)<0) return gerepileuptoint(av, r);
  r=sr; sr = subii(r,N);  /* 0 <= r < 3*N */
  if (signe(sr)<0) return gerepileuptoint(av, r);
  r=sr; sr = subii(r,N);  /* 0 <= r < 2*N */
  return gerepileuptoint(av, signe(sr)>=0 ? sr:r);
}

/* Montgomery reduction */

INLINE ulong
init_montdata(GEN N) { return (ulong) -invmod2BIL(mod2BIL(N)); }

struct montred
{
  GEN N;
  ulong inv;
};

/* Montgomery reduction */
static GEN
_sqr_montred(void * E, GEN x)
{
  struct montred * D = (struct montred *) E;
  return red_montgomery(sqri(x), D->N, D->inv);
}

/* Montgomery reduction */
static GEN
_mul_montred(void * E, GEN x, GEN y)
{
  struct montred * D = (struct montred *) E;
  return red_montgomery(mulii(x, y), D->N, D->inv);
}

static GEN
_mul2_montred(void * E, GEN x)
{
  struct montred * D = (struct montred *) E;
  GEN z = shifti(_sqr_montred(E, x), 1);
  long l = lgefint(D->N);
  while (lgefint(z) > l) z = subii(z, D->N);
  return z;
}

static GEN
_sqr_remii(void* N, GEN x)
{ return remii(sqri(x), (GEN) N); }

static GEN
_mul_remii(void* N, GEN x, GEN y)
{ return remii(mulii(x, y), (GEN) N); }

static GEN
_mul2_remii(void* N, GEN x)
{ return Fp_dblsqr(x, (GEN) N); }

struct redbarrett
{
  GEN iM, N;
  long s;
};

static GEN
_sqr_remiibar(void *E, GEN x)
{
  struct redbarrett * D = (struct redbarrett *) E;
  return Fp_rem_mBarrett(sqri(x), D->iM, D->s, D->N);
}

static GEN
_mul_remiibar(void *E, GEN x, GEN y)
{
  struct redbarrett * D = (struct redbarrett *) E;
  return Fp_rem_mBarrett(mulii(x, y), D->iM, D->s, D->N);
}

static GEN
_mul2_remiibar(void *E, GEN x)
{
  struct redbarrett * D = (struct redbarrett *) E;
  return Fp_dblsqr(x, D->N);
}

static long
Fp_select_red(GEN *y, ulong k, GEN N, long lN, muldata *D, void **pt_E)
{
  if (lN >= Fp_POW_BARRETT_LIMIT && (k==0 || ((double)k)*expi(*y) > 2 + expi(N)))
  {
    struct redbarrett * E = (struct redbarrett *) stack_malloc(sizeof(struct redbarrett));
    D->sqr = &_sqr_remiibar;
    D->mul = &_mul_remiibar;
    D->mul2 = &_mul2_remiibar;
    E->N = N;
    E->s = 1+(expi(N)>>1);
    E->iM = Fp_invmBarrett(N, E->s);
    *pt_E = (void*) E;
    return 0;
  }
  else if (mod2(N) && lN < Fp_POW_REDC_LIMIT)
  {
    struct montred * E = (struct montred *) stack_malloc(sizeof(struct montred));
    *y = remii(shifti(*y, bit_accuracy(lN)), N);
    D->sqr = &_sqr_montred;
    D->mul = &_mul_montred;
    D->mul2 = &_mul2_montred;
    E->N = N;
    E->inv = init_montdata(N);
    *pt_E = (void*) E;
    return 1;
  }
  else
  {
    D->sqr = &_sqr_remii;
    D->mul = &_mul_remii;
    D->mul2 = &_mul2_remii;
    *pt_E = (void*) N;
    return 0;
  }
}

GEN
Fp_powu(GEN A, ulong k, GEN N)
{
  long lN = lgefint(N);
  int base_is_2, use_montgomery;
  muldata D;
  void *E;
  pari_sp av;

  if (lN == 3) {
    ulong n = uel(N,2);
    return utoi( Fl_powu(umodiu(A, n), k, n) );
  }
  if (k <= 2)
  { /* frequent special cases */
    if (k == 2) return Fp_sqr(A,N);
    if (k == 1) return A;
    if (k == 0) return gen_1;
  }
  av = avma; A = modii(A,N);
  base_is_2 = 0;
  if (lgefint(A) == 3) switch(A[2])
  {
    case 1: avma = av; return gen_1;
    case 2:  base_is_2 = 1; break;
  }

  /* TODO: Move this out of here and use for general modular computations */
  use_montgomery = Fp_select_red(&A, k, N, lN, &D, &E);
  if (base_is_2)
    A = gen_powu_fold_i(A, k, E, D.sqr, D.mul2);
  else
    A = gen_powu_i(A, k, E, D.sqr, D.mul);
  if (use_montgomery)
  {
    A = red_montgomery(A, N, ((struct montred *) E)->inv);
    if (cmpii(A, N) >= 0) A = subii(A,N);
  }
  return gerepileuptoint(av, A);
}

GEN
Fp_pows(GEN A, long k, GEN N)
{
  if (lgefint(N) == 3) {
    ulong n = N[2];
    ulong a = umodiu(A, n);
    if (k < 0) {
      a = Fl_inv(a, n);
      k = -k;
    }
    return utoi( Fl_powu(a, (ulong)k, n) );
  }
  if (k < 0) { A = Fp_inv(A, N); k = -k; };
  return Fp_powu(A, (ulong)k, N);
}

/* A^K mod N */
GEN
Fp_pow(GEN A, GEN K, GEN N)
{
  pari_sp av;
  long s, lN = lgefint(N), sA;
  int base_is_2, use_montgomery;
  GEN y;
  muldata D;
  void *E;

  s = signe(K);
  if (!s) return dvdii(A,N)? gen_0: gen_1;
  if (lN == 3 && lgefint(K) == 3)
  {
    ulong n = N[2], a = umodiu(A, n);
    if (s < 0) a = Fl_inv(a, n);
    if (a <= 1) return utoi(a); /* 0 or 1 */
    return utoi(Fl_powu(a, uel(K,2), n));
  }

  av = avma;
  if (s < 0) y = Fp_inv(A,N);
  else
  {
    y = modii(A,N);
    if (!signe(y)) { avma = av; return gen_0; }
  }
  if (lgefint(K) == 3) return gerepileuptoint(av, Fp_powu(y, K[2], N));

  base_is_2 = 0;
  sA = signe(y)==-1 && mod2(K);
  if (lgefint(y) == 3) switch(y[2])
  {
    case 1: return sA ? gen_m1 : gen_1;
    case 2:  base_is_2 = 1; break;
  }

  /* TODO: Move this out of here and use for general modular computations */
  use_montgomery = Fp_select_red(&y, 0UL, N, lN, &D, &E);
  if (base_is_2)
    y = gen_pow_fold_i(y, K, E, D.sqr, D.mul2);
  else
    y = gen_pow_i(y, K, E, D.sqr, D.mul);
  if (use_montgomery)
  {
    y = red_montgomery(y, N, ((struct montred *) E)->inv);
    if (cmpii(y,N) >= 0) y = subii(y,N);
    if (sA) y = subii(N, y);
  }
  return gerepileuptoint(av,y);
}

static GEN
_Fp_mul(void *E, GEN x, GEN y) { return Fp_mul(x,y,(GEN)E); }

static GEN
_Fp_sqr(void *E, GEN x) { return Fp_sqr(x,(GEN)E); }

static GEN
_Fp_one(void *E) { (void) E; return gen_1; }

GEN
Fp_pow_init(GEN x, GEN n, long k, GEN p)
{
  return gen_pow_init(x, n, k, (void*)p, &_Fp_sqr, &_Fp_mul);
}

GEN
Fp_pow_table(GEN R, GEN n, GEN p)
{
  return gen_pow_table(R, n, (void*)p, &_Fp_one, &_Fp_mul);
}

GEN
Fp_powers(GEN x, long n, GEN p)
{
  if (lgefint(p) == 3)
    return Flv_to_ZV(Fl_powers(umodiu(x, uel(p, 2)), n, uel(p, 2)));
  return gen_powers(x, n, 1, (void*)p, _Fp_sqr, _Fp_mul, _Fp_one);
}

static GEN
_Fp_pow(void *E, GEN x, GEN n) { return Fp_pow(x,n,(GEN)E); }

static GEN
_Fp_rand(void *E) { return addiu(randomi(subiu((GEN)E,1)),1); }

static GEN Fp_easylog(void *E, GEN a, GEN g, GEN ord);

static const struct bb_group Fp_star={_Fp_mul,_Fp_pow,_Fp_rand,hash_GEN,
                                      equalii,equali1,Fp_easylog};

static GEN
_Fp_red(void *E, GEN x) { return Fp_red(x, (GEN)E); }

static GEN
_Fp_add(void *E, GEN x, GEN y) { (void) E; return addii(x,y); }

static GEN
_Fp_neg(void *E, GEN x) { (void) E; return negi(x); }

static GEN
_Fp_rmul(void *E, GEN x, GEN y) { (void) E; return mulii(x,y); }

static GEN
_Fp_inv(void *E, GEN x) { return Fp_inv(x,(GEN)E); }

static int
_Fp_equal0(GEN x) { return signe(x)==0; }

static GEN
_Fp_s(void *E, long x) { (void) E; return stoi(x); }

static const struct bb_field Fp_field={_Fp_red,_Fp_add,_Fp_rmul,_Fp_neg,
                                        _Fp_inv,_Fp_equal0,_Fp_s};

const struct bb_field *get_Fp_field(void **E, GEN p)
{
  *E = (void*)p; return &Fp_field;
}

/*********************************************************************/
/**                                                                 **/
/**               ORDER of INTEGERMOD x  in  (Z/nZ)*                **/
/**                                                                 **/
/*********************************************************************/
ulong
Fl_order(ulong a, ulong o, ulong p)
{
  pari_sp av = avma;
  GEN m, P, E;
  long i;
  if (!o) o = p-1;
  m = factoru(o);
  P = gel(m,1);
  E = gel(m,2);
  for (i = lg(P)-1; i; i--)
  {
    ulong j, l = P[i], e = E[i], t = o / upowuu(l,e), y = Fl_powu(a, t, p);
    if (y == 1) o = t;
    else for (j = 1; j < e; j++)
    {
      y = Fl_powu(y, l, p);
      if (y == 1) { o = t *  upowuu(l, j); break; }
    }
  }
  avma = av; return o;
}

/*Find the exact order of a assuming a^o==1*/
GEN
Fp_order(GEN a, GEN o, GEN p) {
  if (lgefint(p) == 3 && (!o || typ(o) == t_INT))
  {
    ulong pp = p[2], oo = (o && lgefint(o)==3)? o[2]: pp-1;
    return utoi( Fl_order(umodiu(a, pp), oo, pp) );
  }
  return gen_order(a, o, (void*)p, &Fp_star);
}
GEN
Fp_factored_order(GEN a, GEN o, GEN p)
{ return gen_factored_order(a, o, (void*)p, &Fp_star); }

/* return order of a mod p^e, e > 0, pe = p^e */
static GEN
Zp_order(GEN a, GEN p, long e, GEN pe)
{
  GEN ap, op;
  if (absequaliu(p, 2))
  {
    if (e == 1) return gen_1;
    if (e == 2) return mod4(a) == 1? gen_1: gen_2;
    if (mod4(a) == 1)
      op = gen_1;
    else {
      op = gen_2;
      a = Fp_sqr(a, pe);
    }
  } else {
    ap = (e == 1)? a: remii(a,p);
    op = Fp_order(ap, subiu(p,1), p);
    if (e == 1) return op;
    a = Fp_pow(a, op, pe); /* 1 mod p */
  }
  if (equali1(a)) return op;
  return mulii(op, powiu(p, e - Z_pval(subiu(a,1), p)));
}

GEN
znorder(GEN x, GEN o)
{
  pari_sp av = avma;
  GEN b, a;

  if (typ(x) != t_INTMOD) pari_err_TYPE("znorder [t_INTMOD expected]",x);
  b = gel(x,1); a = gel(x,2);
  if (!equali1(gcdii(a,b))) pari_err_COPRIME("znorder", a,b);
  if (!o)
  {
    GEN fa = Z_factor(b), P = gel(fa,1), E = gel(fa,2);
    long i, l = lg(P);
    o = gen_1;
    for (i = 1; i < l; i++)
    {
      GEN p = gel(P,i);
      long e = itos(gel(E,i));

      if (l == 2)
        o = Zp_order(a, p, e, b);
      else {
        GEN pe = powiu(p,e);
        o = lcmii(o, Zp_order(remii(a,pe), p, e, pe));
      }
    }
    return gerepileuptoint(av, o);
  }
  return Fp_order(a, o, b);
}
GEN
order(GEN x) { return znorder(x, NULL); }

/*********************************************************************/
/**                                                                 **/
/**               DISCRETE LOGARITHM  in  (Z/nZ)*                   **/
/**                                                                 **/
/*********************************************************************/
static GEN
Fp_log_halfgcd(ulong bnd, GEN C, GEN g, GEN p)
{
  pari_sp av = avma;
  GEN h1, h2, F, G;
  if (!Fp_ratlift(g,p,C,shifti(C,-1),&h1,&h2)) return NULL;
  if ((F = Z_issmooth_fact(h1, bnd)) && (G = Z_issmooth_fact(h2, bnd)))
  {
    GEN M = cgetg(3, t_MAT);
    gel(M,1) = vecsmall_concat(gel(F, 1),gel(G, 1));
    gel(M,2) = vecsmall_concat(gel(F, 2),zv_neg_inplace(gel(G, 2)));
    return gerepileupto(av, M);
  }
  avma = av; return NULL;
}

static GEN
Fp_log_find_rel(GEN b, ulong bnd, GEN C, GEN p, GEN *g, long *e)
{
  GEN rel;
  do
  {
    (*e)++; *g = Fp_mul(*g, b, p);
    rel = Fp_log_halfgcd(bnd, C, *g, p);
  } while (!rel);
  return rel;
}

struct Fp_log_rel
{
  GEN rel;
  ulong prmax;
  long nbrel, nbmax, nbgen;
};

/* add u^e */
static void
addifsmooth1(struct Fp_log_rel *r, GEN z, long u, long e)
{
  pari_sp av = avma;
  long off = r->prmax+1;
  GEN F = cgetg(3, t_MAT);
  gel(F,1) = vecsmall_append(gel(z,1), off+u);
  gel(F,2) = vecsmall_append(gel(z,2), e);
  gel(r->rel,++r->nbrel) = gerepileupto(av, F);
}

/* add u^-1 v^-1 */
static void
addifsmooth2(struct Fp_log_rel *r, GEN z, long u, long v)
{
  pari_sp av = avma;
  long off = r->prmax+1;
  GEN P = mkvecsmall2(off+u,off+v), E = mkvecsmall2(-1,-1);
  GEN F = cgetg(3, t_MAT);
  gel(F,1) = vecsmall_concat(gel(z,1), P);
  gel(F,2) = vecsmall_concat(gel(z,2), E);
  gel(r->rel,++r->nbrel) = gerepileupto(av, F);
}

/*
Let p=C^2+c
Solve h = (C+x)*(C+a)-p = 0 [mod l]
h= -c+x*(C+a)+C*a = 0  [mod l]
x = (c-C*a)/(C+a) [mod l]
h = -c+C*(x+a)+a*x
*/

GEN
Fp_log_sieve_worker(long a, long prmax, GEN C, GEN c, GEN Ci, GEN ci, GEN pi, GEN sz)
{
  pari_sp ltop = avma;
  long th = expi(mulis(C,a)), n = lg(pi)-1;
  long i, j;
  GEN sieve = zero_zv(a+2)+1;
  GEN L = cgetg(1+a+2, t_VEC);
  pari_sp av = avma;
  long rel = 1;
  GEN z, h;
  h = addis(C,a);
  if ((z = Z_issmooth_fact(h, prmax)))
  {
    gel(L, rel++) = mkvec2(z, mkvecsmall3(1, a, -1));
    av = avma;
  }
  for(i=1; i<=n; i++)
  {
    ulong li = pi[i], s = sz[i], al = a % li;
    ulong u, iv = Fl_invsafe(Fl_add(Ci[i],al,li),li);
    if (!iv) continue;
    u = Fl_mul(Fl_sub(ci[i],Fl_mul(Ci[i],al,li),li), iv ,li);
    for(j = u; j<=a; j+=li)
      sieve[j] += s;
  }
  th = th - expu(th)-1;
  for(j=0; j<a; j++)
    if (sieve[j]>=th)
    {
      GEN h = addiu(subii(muliu(C,a+j),c), a*j);
      if ((z = Z_issmooth_fact(h, prmax)))
      {
        gel(L, rel++) = mkvec2(z, mkvecsmall3(2, a, j));
        av = avma;
      } else avma = av;
    }
  /* j = a */
  if (sieve[a]>=th)
  {
    GEN h = addiu(subii(muliu(C,2*a),c), a*a);
    if ((z = Z_issmooth_fact(h, prmax)))
    {
      gel(L, rel++) = mkvec2(z, mkvecsmall3(1, a, -2));
      av = avma;
    }
  }
  setlg(L, rel);
  return gerepilecopy(ltop, L);
}

static long
Fp_log_sieve(struct Fp_log_rel *r, GEN C, GEN c, GEN Ci, GEN ci, GEN pi, GEN sz)
{
  struct pari_mt pt;
  long i, j, nb = 0;
  GEN worker = snm_closure(is_entry("_Fp_log_sieve_worker"),
               mkvecn(7, utoi(r->prmax), C, c, Ci, ci, pi, sz));
  long running, pending = 0;
  GEN W = zerovec(r->nbgen);
  mt_queue_start_lim(&pt, worker, r->nbgen);
  for (i = 0; (running = (i < r->nbgen)) || pending; i++)
  {
    GEN done;
    long idx;
    mt_queue_submit(&pt, i, running ? mkvec(stoi(i)): NULL);
    done = mt_queue_get(&pt, &idx, &pending);
    if (!done || lg(done)==1) continue;
    gel(W, idx+1) = done;
    nb += lg(done)-1;
    if (DEBUGLEVEL && (i&127)==0)
      err_printf("%ld%% ",100*nb/r->nbmax);
  }
  mt_queue_end(&pt);
  for(j = 1; j <= r->nbgen && r->nbrel < r->nbmax; j++)
  {
    long ll, m;
    GEN L = gel(W,j);
    if (isintzero(L)) continue;
    ll = lg(L);
    for (m=1; m<ll && r->nbrel < r->nbmax ; m++)
    {
      GEN Lm = gel(L,m), h = gel(Lm, 1), v = gel(Lm, 2);
      if (v[1] == 1)
        addifsmooth1(r, h, v[2], v[3]);
      else
        addifsmooth2(r, h, v[2], v[3]);
    }
  }
  return j;
}

static GEN
ECP_psi(GEN x, GEN y)
{
  long prec = realprec(x);
  GEN lx = glog(x, prec), ly = glog(y, prec);
  GEN u = gdiv(lx, ly);
  return gpow(u, gneg(u),prec);
}

struct computeG
{
  GEN C;
  long bnd, nbi;
};

static GEN
_computeG(void *E, GEN gen)
{
  struct computeG * d = (struct computeG *) E;
  GEN ps = ECP_psi(gmul(gen,d->C), stoi(d->bnd));
  return gsub(gmul(gsqr(gen),ps),gmul2n(gaddgs(gen,d->nbi),2));
}

static long
compute_nbgen(GEN C, long bnd, long nbi)
{
  struct computeG d;
  d.C = shifti(C, 1);
  d.bnd = bnd;
  d.nbi = nbi;
  return itos(ground(zbrent((void*)&d, _computeG, gen_2, stoi(bnd), DEFAULTPREC)));
}

static GEN
_psi(void*E, GEN y)
{
  GEN lx = (GEN) E;
  long prec = realprec(lx);
  GEN ly = glog(y, prec);
  GEN u = gdiv(lx, ly);
  return gsub(gdiv(y ,ly), gpow(u, u, prec));
}

static GEN
opt_param(GEN x, long prec)
{
  return zbrent((void*)glog(x,prec), _psi, gen_2, x, prec);
}

static GEN
check_kernel(long nbg, long N, long prmax, GEN C, GEN M, GEN p, GEN m)
{
  pari_sp av = avma;
  long lM = lg(M)-1, nbcol = lM;
  long tbs = maxss(1, expu(nbg/expi(m)));
  for (;;)
  {
    GEN K = FpMs_leftkernel_elt_col(M, nbcol, N, m);
    GEN tab;
    long i, f=0;
    long l = lg(K), lm = lgefint(m);
    GEN idx = diviiexact(subiu(p,1),m), g;
    pari_timer ti;
    if (DEBUGLEVEL) timer_start(&ti);
    for(i=1; i<l; i++)
      if (signe(gel(K,i)))
        break;
    g = Fp_pow(utoi(i), idx, p);
    tab = Fp_pow_init(g, p, tbs, p);
    K = FpC_Fp_mul(K, Fp_inv(gel(K,i), m), m);
    for(i=1; i<l; i++)
    {
      GEN k = gel(K,i);
      GEN j = i<=prmax ? utoi(i): addis(C,i-(prmax+1));
      if (signe(k)==0 || !equalii(Fp_pow_table(tab, k, p), Fp_pow(j, idx, p)))
        gel(K,i) = cgetineg(lm);
      else
        f++;
    }
    if (DEBUGLEVEL) timer_printf(&ti,"found %ld/%ld logs", f, nbg);
    if(f > (nbg>>1)) return gerepileupto(av, K);
    for(i=1; i<=nbcol; i++)
    {
      long a = 1+random_Fl(lM);
      swap(gel(M,a),gel(M,i));
    }
    if (4*nbcol>5*nbg) nbcol = nbcol*9/10;
  }
}

static GEN
Fp_log_find_ind(GEN a, GEN K, long prmax, GEN C, GEN p, GEN m)
{
  pari_sp av=avma;
  GEN aa = gen_1;
  long AV = 0;
  for(;;)
  {
    GEN A = Fp_log_find_rel(a, prmax, C, p, &aa, &AV);
    GEN F = gel(A,1), E = gel(A,2);
    GEN Ao = gen_0;
    long i, l = lg(F);
    for(i=1; i<l; i++)
    {
      GEN Ki = gel(K,F[i]);
      if (signe(Ki)<0) break;
      Ao = addii(Ao, mulis(Ki, E[i]));
    }
    if (i==l) return Fp_div(Ao, utoi(AV), m);
    aa = gerepileuptoint(av, aa);
  }
}

static GEN
Fp_log_index(GEN a, GEN b, GEN m, GEN p)
{
  pari_sp av = avma, av2;
  long i, j, nbi, nbr = 0, nbrow, nbg;
  GEN C, c, Ci, ci, pi, pr, sz, l, Ao, Bo, K, d, p_1;
  pari_timer ti;
  struct Fp_log_rel r;
  ulong bnds = itou(roundr_safe(opt_param(sqrti(p),DEFAULTPREC)));
  ulong bnd = 4*bnds;
  if (!bnds || cmpii(sqru(bnds),m)>=0) return NULL;

  p_1 = subiu(p,1);
  if (!is_pm1(gcdii(m,diviiexact(p_1,m))))
    m = diviiexact(p_1, Z_ppo(p_1, m));
  pr = primes_upto_zv(bnd);
  nbi = lg(pr)-1;
  C = sqrtremi(p, &c);
  av2 = avma;
  for (i = 1; i <= nbi; ++i)
  {
    ulong lp = pr[i];
    while (lp <= bnd)
    {
      nbr++;
      lp *= pr[i];
    }
  }
  pi = cgetg(nbr+1,t_VECSMALL);
  Ci = cgetg(nbr+1,t_VECSMALL);
  ci = cgetg(nbr+1,t_VECSMALL);
  sz = cgetg(nbr+1,t_VECSMALL);
  for (i = 1, j = 1; i <= nbi; ++i)
  {
    ulong lp = pr[i], sp = expu(2*lp-1);
    while (lp <= bnd)
    {
      pi[j] = lp;
      Ci[j] = umodiu(C, lp);
      ci[j] = umodiu(c, lp);
      sz[j] = sp;
      lp *= pr[i];
      j++;
    }
  }
  r.nbrel = 0;
  r.nbgen = compute_nbgen(C, bnd, nbi);
  r.nbmax = 2*(nbi+r.nbgen);
  r.rel = cgetg(r.nbmax+1,t_VEC);
  r.prmax = pr[nbi];
  if (DEBUGLEVEL)
  {
    err_printf("bnd=%lu Size FB=%ld extra gen=%ld \n", bnd, nbi, r.nbgen);
    timer_start(&ti);
  }
  nbg = Fp_log_sieve(&r, C, c, Ci, ci, pi, sz);
  nbrow = r.prmax + nbg;
  if (DEBUGLEVEL)
  {
    err_printf("\n");
    timer_printf(&ti," %ld relations, %ld generators", r.nbrel, nbi+nbg);
  }
  setlg(r.rel,r.nbrel+1);
  r.rel = gerepilecopy(av2, r.rel);
  K = check_kernel(nbi+nbrow-r.prmax, nbrow, r.prmax, C, r.rel, p, m);
  if (DEBUGLEVEL) timer_start(&ti);
  Ao = Fp_log_find_ind(a, K, r.prmax, C, p, m);
  if (DEBUGLEVEL) timer_printf(&ti," log element");
  Bo = Fp_log_find_ind(b, K, r.prmax, C, p, m);
  if (DEBUGLEVEL) timer_printf(&ti," log generator");
  d = gcdii(Ao,Bo);
  l = Fp_div(diviiexact(Ao, d) ,diviiexact(Bo, d), m);
  if (!equalii(a,Fp_pow(b,l,p))) pari_err_BUG("Fp_log_index");
  return gerepileuptoint(av, l);
}

static int
Fp_log_use_index(long e, long p)
{
  return (e >= 27 && 20*(p+6)<=e*e);
}

/* Trivial cases a = 1, -1. Return x s.t. g^x = a or [] if no such x exist */
static GEN
Fp_easylog(void *E, GEN a, GEN g, GEN ord)
{
  pari_sp av = avma;
  GEN p = (GEN)E;
  /* assume a reduced mod p, p not necessarily prime */
  if (equali1(a)) return gen_0;
  /* p > 2 */
  if (equalii(subiu(p,1), a))  /* -1 */
  {
    pari_sp av2;
    GEN t;
    ord = get_arith_Z(ord);
    if (mpodd(ord)) { avma = av; return cgetg(1, t_VEC); } /* no solution */
    t = shifti(ord,-1); /* only possible solution */
    av2 = avma;
    if (!equalii(Fp_pow(g, t, p), a)) { avma = av; return cgetg(1, t_VEC); }
    avma = av2; return gerepileuptoint(av, t);
  }
  if (typ(ord)==t_INT && BPSW_psp(p) && Fp_log_use_index(expi(ord),expi(p)))
    return Fp_log_index(a, g, ord, p);
  avma = av; return NULL; /* not easy */
}

GEN
Fp_log(GEN a, GEN g, GEN ord, GEN p)
{
  GEN v = get_arith_ZZM(ord);
  GEN F = gmael(v,2,1);
  long lF = lg(F)-1, lmax;
  if (lF == 0) return equali1(a)? gen_0: cgetg(1, t_VEC);
  lmax = expi(gel(F,lF));
  if (BPSW_psp(p) && Fp_log_use_index(lmax,expi(p)))
    v = mkvec2(gel(v,1),ZM_famat_limit(gel(v,2),int2n(27)));
  return gen_PH_log(a,g,v,(void*)p,&Fp_star);
}

static ulong
Fl_log_naive(ulong a, ulong g, ulong ord, ulong p)
{
  ulong i, h=1;
  for(i=0; i<ord; i++, h = Fl_mul(h, g, p))
    if(a==h) return i;
  return ~0UL;
}

static ulong
Fl_log_naive_pre(ulong a, ulong g, ulong ord, ulong p, ulong pi)
{
  ulong i, h=1;
  for(i=0; i<ord; i++, h = Fl_mul_pre(h, g, p, pi))
    if(a==h) return i;
  return ~0UL;
}

static ulong
Fl_log_Fp(ulong a, ulong g, ulong ord, ulong p)
{
  pari_sp av = avma;
  GEN r = Fp_log(utoi(a),utoi(g),utoi(ord),utoi(p));
  ulong z = typ(r)==t_INT ? itou(r): ~0L;
  avma = av; return z;
}

ulong
Fl_log_pre(ulong a, ulong g, ulong ord, ulong p, ulong pi)
{
  if (ord <= 200) return Fl_log_naive_pre(a, g, ord, p, pi);
  return Fl_log_Fp(a, g, ord, p);
}

ulong
Fl_log(ulong a, ulong g, ulong ord, ulong p)
{
  if (ord <= 200)
  return (p&HIGHMASK) ? Fl_log_naive_pre(a, g, ord, p, get_Fl_red(p))
                      : Fl_log_naive(a, g, ord, p);
  return Fl_log_Fp(a, g, ord, p);
}

/* find x such that h = g^x mod N > 1, N = prod_{i <= l} P[i]^E[i], P[i] prime.
 * PHI[l] = eulerphi(N / P[l]^E[l]).   Destroys P/E */
static GEN
znlog_rec(GEN h, GEN g, GEN N, GEN P, GEN E, GEN PHI)
{
  long l = lg(P) - 1, e = E[l];
  GEN p = gel(P, l), phi = gel(PHI,l), pe = e == 1? p: powiu(p, e);
  GEN a,b, hp,gp, hpe,gpe, ogpe; /* = order(g mod p^e) | p^(e-1)(p-1) */

  if (l == 1) {
    hpe = h;
    gpe = g;
  } else {
    hpe = modii(h, pe);
    gpe = modii(g, pe);
  }
  if (e == 1) {
    hp = hpe;
    gp = gpe;
  } else {
    hp = remii(hpe, p);
    gp = remii(gpe, p);
  }
  if (hp == gen_0 || gp == gen_0) return NULL;
  if (absequaliu(p, 2))
  {
    GEN n = int2n(e);
    ogpe = Zp_order(gpe, gen_2, e, n);
    a = Fp_log(hpe, gpe, ogpe, n);
    if (typ(a) != t_INT) return NULL;
  }
  else
  { /* Avoid black box groups: (Z/p^2)^* / (Z/p)^* ~ (Z/pZ, +), where DL
       is trivial */
    /* [order(gp), factor(order(gp))] */
    GEN v = Fp_factored_order(gp, subiu(p,1), p);
    GEN ogp = gel(v,1);
    if (!equali1(Fp_pow(hp, ogp, p))) return NULL;
    a = Fp_log(hp, gp, v, p);
    if (typ(a) != t_INT) return NULL;
    if (e == 1) ogpe = ogp;
    else
    { /* find a s.t. g^a = h (mod p^e), p odd prime, e > 0, (h,p) = 1 */
      /* use p-adic log: O(log p + e) mul*/
      long vpogpe, vpohpe;

      hpe = Fp_mul(hpe, Fp_pow(gpe, negi(a), pe), pe);
      gpe = Fp_pow(gpe, ogp, pe);
      /* g,h = 1 mod p; compute b s.t. h = g^b */

      /* v_p(order g mod pe) */
      vpogpe = equali1(gpe)? 0: e - Z_pval(subiu(gpe,1), p);
      /* v_p(order h mod pe) */
      vpohpe = equali1(hpe)? 0: e - Z_pval(subiu(hpe,1), p);
      if (vpohpe > vpogpe) return NULL;

      ogpe = mulii(ogp, powiu(p, vpogpe)); /* order g mod p^e */
      if (is_pm1(gpe)) return is_pm1(hpe)? a: NULL;
      b = gdiv(Qp_log(cvtop(hpe, p, e)), Qp_log(cvtop(gpe, p, e)));
      a = addii(a, mulii(ogp, padic_to_Q(b)));
    }
  }
  /* gp^a = hp => x = a mod ogpe => generalized Pohlig-Hellman strategy */
  if (l == 1) return a;

  N = diviiexact(N, pe); /* make N coprime to p */
  h = Fp_mul(h, Fp_pow(g, modii(negi(a), phi), N), N);
  g = Fp_pow(g, modii(ogpe, phi), N);
  setlg(P, l); /* remove last element */
  setlg(E, l);
  b = znlog_rec(h, g, N, P, E, PHI);
  if (!b) return NULL;
  return addmulii(a, b, ogpe);
}

static GEN
get_PHI(GEN P, GEN E)
{
  long i, l = lg(P);
  GEN PHI = cgetg(l, t_VEC);
  gel(PHI,1) = gen_1;
  for (i=1; i<l-1; i++)
  {
    GEN t, p = gel(P,i);
    long e = E[i];
    t = mulii(powiu(p, e-1), subiu(p,1));
    if (i > 1) t = mulii(t, gel(PHI,i));
    gel(PHI,i+1) = t;
  }
  return PHI;
}

GEN
znlog(GEN h, GEN g, GEN o)
{
  pari_sp av = avma;
  GEN N, fa, P, E, x;
  switch (typ(g))
  {
    case t_PADIC:
    {
      GEN p = gel(g,2);
      long v = valp(g);
      if (v < 0) pari_err_DIM("znlog");
      if (v > 0) {
        long k = gvaluation(h, p);
        if (k % v) return cgetg(1,t_VEC);
        k /= v;
        if (!gequal(h, gpowgs(g,k))) { avma = av; return cgetg(1,t_VEC); }
        avma = av; return stoi(k);
      }
      N = gel(g,3);
      g = Rg_to_Fp(g, N);
      break;
    }
    case t_INTMOD:
      N = gel(g,1);
      g = gel(g,2); break;
    default: pari_err_TYPE("znlog", g);
      return NULL; /* LCOV_EXCL_LINE */
  }
  if (equali1(N)) { avma = av; return gen_0; }
  h = Rg_to_Fp(h, N);
  if (o) return gerepileupto(av, Fp_log(h, g, o, N));
  fa = Z_factor(N);
  P = gel(fa,1);
  E = vec_to_vecsmall(gel(fa,2));
  x = znlog_rec(h, g, N, P, E, get_PHI(P,E));
  if (!x) { avma = av; return cgetg(1,t_VEC); }
  return gerepileuptoint(av, x);
}

GEN
Fp_sqrtn(GEN a, GEN n, GEN p, GEN *zeta)
{
  if (lgefint(p)==3)
  {
    long nn = itos_or_0(n);
    if (nn)
    {
      ulong pp = p[2];
      ulong uz;
      ulong r = Fl_sqrtn(umodiu(a,pp),nn,pp, zeta ? &uz:NULL);
      if (r==ULONG_MAX) return NULL;
      if (zeta) *zeta = utoi(uz);
      return utoi(r);
    }
  }
  a = modii(a,p);
  if (!signe(a))
  {
    if (zeta) *zeta = gen_1;
    if (signe(n) < 0) pari_err_INV("Fp_sqrtn", mkintmod(gen_0,p));
    return gen_0;
  }
  if (absequaliu(n,2))
  {
    if (zeta) *zeta = subiu(p,1);
    return signe(n) > 0 ? Fp_sqrt(a,p): Fp_sqrt(Fp_inv(a, p),p);
  }
  return gen_Shanks_sqrtn(a,n,subiu(p,1),zeta,(void*)p,&Fp_star);
}

/*********************************************************************/
/**                                                                 **/
/**                    FUNDAMENTAL DISCRIMINANTS                    **/
/**                                                                 **/
/*********************************************************************/
static int
fa_isfundamental(GEN F)
{
  GEN P = gel(F,1), E = gel(F,2);
  long i, s, l = lg(P);

  if (l == 1) return 1;
  s = signe(gel(P,1)); /* = signe(x) */
  if (!s) return 0;
  if (s < 0) { l--; P = vecslice(P,2,l); E = vecslice(E,2,l); }
  if (l == 1) return 0;
  if (!absequaliu(gel(P,1), 2))
    i = 1; /* need x = 1 mod 4 */
  else
  {
    i = 2;
    switch(itou(gel(E,1)))
    {
      case 2: s = -s; break; /* need x/4 = 3 mod 4 */
      case 3: s = 0; break; /* no condition mod 4 */
      default: return 0;
    }
  }
  for(; i < l; i++)
  {
    if (!equali1(gel(E,i))) return 0;
    if (s && Mod4(gel(P,i)) == 3) s = -s;
  }
  return s >= 0;
}
long
isfundamental(GEN x)
{
  if (typ(x) != t_INT)
  {
    pari_sp av = avma;
    int v = fa_isfundamental(check_arith_all(x,"isfundamental"));
    avma = av; return v;
  }
  return Z_isfundamental(x);
}

/* x fundamental ? */
long
uposisfundamental(ulong x)
{
  ulong r = x & 15; /* x mod 16 */
  if (!r) return 0;
  switch(r & 3)
  { /* x mod 4 */
    case 0: return (r == 4)? 0: uissquarefree(x >> 2);
    case 1: return uissquarefree(x);
    default: return 0;
  }
}
/* -x fundamental ? */
long
unegisfundamental(ulong x)
{
  ulong r = x & 15; /* x mod 16 */
  if (!r) return 0;
  switch(r & 3)
  { /* x mod 4 */
    case 0: return (r == 12)? 0: uissquarefree(x >> 2);
    case 3: return uissquarefree(x);
    default: return 0;
  }
}
long
sisfundamental(long x)
{ return x < 0? unegisfundamental((ulong)(-x)): uposisfundamental(x); }

long
Z_isfundamental(GEN x)
{
  long r;
  switch(lgefint(x))
  {
    case 2: return 0;
    case 3: return signe(x) < 0? unegisfundamental(x[2])
                               : uposisfundamental(x[2]);
  }
  r = mod16(x);
  if (!r) return 0;
  if ((r & 3) == 0)
  {
    pari_sp av;
    r >>= 2; /* |x|/4 mod 4 */
    if (signe(x) < 0) r = 4-r;
    if (r == 1) return 0;
    av = avma;
    r = Z_issquarefree( shifti(x,-2) );
    avma = av; return r;
  }
  r &= 3; /* |x| mod 4 */
  if (signe(x) < 0) r = 4-r;
  return (r==1) ? Z_issquarefree(x) : 0;
}

static GEN
fa_quaddisc(GEN f)
{
  GEN P = gel(f,1), E = gel(f,2), s = gen_1;
  long i, l = lg(P);
  for (i = 1; i < l; i++) /* possibly including -1 */
    if (mpodd(gel(E,i))) s = mulii(s, gel(P,i));
  if (Mod4(s) > 1) s = shifti(s,2);
  return s;
}

GEN
quaddisc(GEN x)
{
  const pari_sp av = avma;
  if (is_rational_t(typ(x))) x = factor(x);
  else x = check_arith_all(x,"quaddisc");
  return gerepileuptoint(av, fa_quaddisc(x));
}

/*********************************************************************/
/**                                                                 **/
/**                              FACTORIAL                          **/
/**                                                                 **/
/*********************************************************************/
/* return a * (a+1) * ... * b. Assume a <= b  [ note: factoring out powers of 2
 * first is slower ... ] */
GEN
mulu_interval(ulong a, ulong b)
{
  pari_sp av = avma;
  ulong k, l, N, n;
  long lx;
  GEN x;

  if (!a) return gen_0;
  n = b - a + 1;
  if (n < 61)
  {
    if (n == 1) return utoi(a);
    x = muluu(a,a+1); if (n == 2) return x;
    for (k=a+2; k<=b; k++) x = mului(k,x);
    return gerepileuptoint(av, x);
  }
  lx = 1; x = cgetg(2 + n/2, t_VEC);
  N = b + a;
  for (k = a;; k++)
  {
    l = N - k; if (l <= k) break;
    gel(x,lx++) = muluu(k,l);
  }
  if (l == k) gel(x,lx++) = utoipos(k);
  setlg(x, lx);
  return gerepileuptoint(av, ZV_prod(x));
}
GEN
muls_interval(long a, long b)
{
  pari_sp av = avma;
  long lx, k, l, N, n = b - a + 1;
  GEN x;

  if (a <= 0 && b >= 0) return gen_0;
  if (n < 61)
  {
    x = stoi(a);
    for (k=a+1; k<=b; k++) x = mulsi(k,x);
    return gerepileuptoint(av, x);
  }
  lx = 1; x = cgetg(2 + n/2, t_VEC);
  N = b + a;
  for (k = a;; k++)
  {
    l = N - k; if (l <= k) break;
    gel(x,lx++) = mulss(k,l);
  }
  if (l == k) gel(x,lx++) = stoi(k);
  setlg(x, lx);
  return gerepileuptoint(av, ZV_prod(x));
}

GEN
mpfact(long n)
{
  if (n < 2)
  {
    if (n < 0) pari_err_DOMAIN("factorial", "argument","<",gen_0,stoi(n));
    return gen_1;
  }
  return mulu_interval(2UL, (ulong)n);
}

/*******************************************************************/
/**                                                               **/
/**                      LUCAS & FIBONACCI                        **/
/**                                                               **/
/*******************************************************************/
static void
lucas(ulong n, GEN *a, GEN *b)
{
  GEN z, t, zt;
  if (!n) { *a = gen_2; *b = gen_1; return; }
  lucas(n >> 1, &z, &t); zt = mulii(z, t);
  switch(n & 3) {
    case  0: *a = subiu(sqri(z),2); *b = subiu(zt,1); break;
    case  1: *a = subiu(zt,1);      *b = addiu(sqri(t),2); break;
    case  2: *a = addiu(sqri(z),2); *b = addiu(zt,1); break;
    case  3: *a = addiu(zt,1);      *b = subiu(sqri(t),2);
  }
}

GEN
fibo(long n)
{
  pari_sp av = avma;
  GEN a, b;
  if (!n) return gen_0;
  lucas((ulong)(labs(n)-1), &a, &b);
  a = diviuexact(addii(shifti(a,1),b), 5);
  if (n < 0 && !odd(n)) setsigne(a, -1);
  return gerepileuptoint(av, a);
}

/*******************************************************************/
/*                                                                 */
/*                      CONTINUED FRACTIONS                        */
/*                                                                 */
/*******************************************************************/
static GEN
icopy_lg(GEN x, long l)
{
  long lx = lgefint(x);
  GEN y;

  if (lx >= l) return icopy(x);
  y = cgeti(l); affii(x, y); return y;
}

/* continued fraction of a/b. If y != NULL, stop when partial quotients
 * differ from y */
static GEN
Qsfcont(GEN a, GEN b, GEN y, ulong k)
{
  GEN  z, c;
  ulong i, l, ly = lgefint(b);

  /* times 1 / log2( (1+sqrt(5)) / 2 )  */
  l = (ulong)(3 + bit_accuracy_mul(ly, 1.44042009041256));
  if (k > 0 && k+1 > 0 && l > k+1) l = k+1; /* beware overflow */
  if (l > LGBITS) l = LGBITS;

  z = cgetg(l,t_VEC);
  l--;
  if (y) {
    pari_sp av = avma;
    if (l >= (ulong)lg(y)) l = lg(y)-1;
    for (i = 1; i <= l; i++)
    {
      GEN q = gel(y,i);
      gel(z,i) = q;
      c = b; if (!gequal1(q)) c = mulii(q, b);
      c = subii(a, c);
      if (signe(c) < 0)
      { /* partial quotient too large */
        c = addii(c, b);
        if (signe(c) >= 0) i++; /* by 1 */
        break;
      }
      if (cmpii(c, b) >= 0)
      { /* partial quotient too small */
        c = subii(c, b);
        if (cmpii(c, b) < 0) {
          /* by 1. If next quotient is 1 in y, add 1 */
          if (i < l && equali1(gel(y,i+1))) gel(z,i) = addiu(q,1);
          i++;
        }
        break;
      }
      if ((i & 0xff) == 0) gerepileall(av, 2, &b, &c);
      a = b; b = c;
    }
  } else {
    a = icopy_lg(a, ly);
    b = icopy(b);
    for (i = 1; i <= l; i++)
    {
      gel(z,i) = truedvmdii(a,b,&c);
      if (c == gen_0) { i++; break; }
      affii(c, a); cgiv(c); c = a;
      a = b; b = c;
    }
  }
  i--;
  if (i > 1 && gequal1(gel(z,i)))
  {
    cgiv(gel(z,i)); --i;
    gel(z,i) = addui(1, gel(z,i)); /* unclean: leave old z[i] on stack */
  }
  setlg(z,i+1); return z;
}

static GEN
sersfcont(GEN a, GEN b, long k)
{
  long i, l = typ(a) == t_POL? lg(a): 3;
  GEN y, c;
  if (lg(b) > l) l = lg(b);
  if (k > 0 && l > k+1) l = k+1;
  y = cgetg(l,t_VEC);
  for (i=1; i<l; i++)
  {
    gel(y,i) = poldivrem(a,b,&c);
    if (gequal0(c)) { i++; break; }
    a = b; b = c;
  }
  setlg(y, i); return y;
}

GEN
gboundcf(GEN x, long k)
{
  pari_sp av;
  long tx = typ(x), e;
  GEN y, a, b, c;

  if (k < 0) pari_err_DOMAIN("gboundcf","nmax","<",gen_0,stoi(k));
  if (is_scalar_t(tx))
  {
    if (gequal0(x)) return mkvec(gen_0);
    switch(tx)
    {
      case t_INT: return mkveccopy(x);
      case t_REAL:
        av = avma;
        c = mantissa_real(x,&e);
        if (e < 0) pari_err_PREC("gboundcf");
        y = int2n(e);
        a = Qsfcont(c,y, NULL, k);
        b = addsi(signe(x), c);
        return gerepilecopy(av, Qsfcont(b,y, a, k));

      case t_FRAC:
        av = avma;
        return gerepileupto(av, Qsfcont(gel(x,1),gel(x,2), NULL, k));
    }
    pari_err_TYPE("gboundcf",x);
  }

  switch(tx)
  {
    case t_POL: return mkveccopy(x);
    case t_SER:
      av = avma;
      return gerepileupto(av, gboundcf(ser2rfrac_i(x), k));
    case t_RFRAC:
      av = avma;
      return gerepilecopy(av, sersfcont(gel(x,1), gel(x,2), k));
  }
  pari_err_TYPE("gboundcf",x);
  return NULL; /* LCOV_EXCL_LINE */
}

static GEN
sfcont2(GEN b, GEN x, long k)
{
  pari_sp av = avma;
  long lb = lg(b), tx = typ(x), i;
  GEN y,p1;

  if (k)
  {
    if (k >= lb) pari_err_DIM("contfrac [too few denominators]");
    lb = k+1;
  }
  y = cgetg(lb,t_VEC);
  if (lb==1) return y;
  if (is_scalar_t(tx))
  {
    if (!is_intreal_t(tx) && tx != t_FRAC) pari_err_TYPE("sfcont2",x);
  }
  else if (tx == t_SER) x = ser2rfrac_i(x);

  if (!gequal1(gel(b,1))) x = gmul(gel(b,1),x);
  for (i = 1;;)
  {
    if (tx == t_REAL)
    {
      long e = expo(x);
      if (e > 0 && nbits2prec(e+1) > realprec(x)) break;
      gel(y,i) = floorr(x);
      p1 = subri(x, gel(y,i));
    }
    else
    {
      gel(y,i) = gfloor(x);
      p1 = gsub(x, gel(y,i));
    }
    if (++i >= lb) break;
    if (gequal0(p1)) break;
    x = gdiv(gel(b,i),p1);
  }
  setlg(y,i);
  return gerepilecopy(av,y);
}


GEN
gcf(GEN x) { return gboundcf(x,0); }
GEN
gcf2(GEN b, GEN x) { return contfrac0(x,b,0); }
GEN
contfrac0(GEN x, GEN b, long nmax)
{
  long tb;

  if (!b) return gboundcf(x,nmax);
  tb = typ(b);
  if (tb == t_INT) return gboundcf(x,itos(b));
  if (! is_vec_t(tb)) pari_err_TYPE("contfrac0",b);
  if (nmax < 0) pari_err_DOMAIN("contfrac","nmax","<",gen_0,stoi(nmax));
  return sfcont2(b,x,nmax);
}

GEN
contfracpnqn(GEN x, long n)
{
  pari_sp av = avma;
  long i, lx = lg(x);
  GEN M,A,B, p0,p1, q0,q1;

  if (lx == 1)
  {
    if (! is_matvec_t(typ(x))) pari_err_TYPE("pnqn",x);
    if (n >= 0) return cgetg(1,t_MAT);
    return matid(2);
  }
  switch(typ(x))
  {
    case t_VEC: case t_COL: A = x; B = NULL; break;
    case t_MAT:
      switch(lgcols(x))
      {
        case 2: A = row(x,1); B = NULL; break;
        case 3: A = row(x,2); B = row(x,1); break;
        default: pari_err_DIM("pnqn [ nbrows != 1,2 ]");
                 return NULL; /*LCOV_EXCL_LINE*/
      }
      break;
    default: pari_err_TYPE("pnqn",x);
      return NULL; /*LCOV_EXCL_LINE*/
  }
  p1 = gel(A,1);
  q1 = B? gel(B,1): gen_1; /* p[0], q[0] */
  if (n >= 0)
  {
    lx = minss(lx, n+2);
    if (lx == 2) return gerepilecopy(av, mkmat(mkcol2(p1,q1)));
  }
  else if (lx == 2)
    return gerepilecopy(av, mkmat2(mkcol2(p1,q1), mkcol2(gen_1,gen_0)));
  /* lx >= 3 */
  p0 = gen_1;
  q0 = gen_0; /* p[-1], q[-1] */
  M = cgetg(lx, t_MAT);
  gel(M,1) = mkcol2(p1,q1);
  for (i=2; i<lx; i++)
  {
    GEN a = gel(A,i), p2,q2;
    if (B) {
      GEN b = gel(B,i);
      p0 = gmul(b,p0);
      q0 = gmul(b,q0);
    }
    p2 = gadd(gmul(a,p1),p0); p0=p1; p1=p2;
    q2 = gadd(gmul(a,q1),q0); q0=q1; q1=q2;
    gel(M,i) = mkcol2(p1,q1);
  }
  if (n < 0) M = mkmat2(gel(M,lx-1), gel(M,lx-2));
  return gerepilecopy(av, M);
}
GEN
pnqn(GEN x) { return contfracpnqn(x,-1); }
/* x = [a0, ..., an] from gboundcf, n >= 0;
 * return [[p0, ..., pn], [q0,...,qn]] */
GEN
ZV_allpnqn(GEN x)
{
  long i, lx = lg(x);
  GEN p0, p1, q0, q1, p2, q2, P,Q, v = cgetg(3,t_VEC);

  gel(v,1) = P = cgetg(lx, t_VEC);
  gel(v,2) = Q = cgetg(lx, t_VEC);
  p0 = gen_1; q0 = gen_0;
  gel(P, 1) = p1 = gel(x,1); gel(Q, 1) = q1 = gen_1;
  for (i=2; i<lx; i++)
  {
    GEN a = gel(x,i);
    gel(P, i) = p2 = addmulii(p0, a, p1); p0 = p1; p1 = p2;
    gel(Q, i) = q2 = addmulii(q0, a, q1); q0 = q1; q1 = q2;
  }
  return v;
}

/* write Mod(x,N) as a/b, gcd(a,b) = 1, b <= B (no condition if B = NULL) */
static GEN
mod_to_frac(GEN x, GEN N, GEN B)
{
  GEN a, b, A;
  if (B) A = divii(shifti(N, -1), B);
  else
  {
    A = sqrti(shifti(N, -1));
    B = A;
  }
  if (!Fp_ratlift(x, N, A,B,&a,&b) || !equali1( gcdii(a,b) )) return NULL;
  return equali1(b)? a: mkfrac(a,b);
}

static GEN
mod_to_rfrac(GEN x, GEN N, long B)
{
  GEN a, b;
  long A, d = degpol(N);
  if (B >= 0) A = d-1 - B;
  else
  {
    B = d >> 1;
    A = odd(d)? B : B-1;
  }
  if (varn(N) != varn(x)) x = scalarpol(x, varn(N));
  if (!RgXQ_ratlift(x, N, A, B, &a,&b) || degpol(RgX_gcd(a,b)) > 0) return NULL;
  return gdiv(a,b);
}

/* k > 0 t_INT, x a t_FRAC, returns the convergent a/b
 * of the continued fraction of x with b <= k maximal */
static GEN
bestappr_frac(GEN x, GEN k)
{
  pari_sp av;
  GEN p0, p1, p, q0, q1, q, a, y;

  if (cmpii(gel(x,2),k) <= 0) return gcopy(x);
  av = avma; y = x;
  p1 = gen_1; p0 = truedvmdii(gel(x,1), gel(x,2), &a); /* = floor(x) */
  q1 = gen_0; q0 = gen_1;
  x = mkfrac(a, gel(x,2)); /* = frac(x); now 0<= x < 1 */
  for(;;)
  {
    x = ginv(x); /* > 1 */
    a = typ(x)==t_INT? x: divii(gel(x,1), gel(x,2));
    if (cmpii(a,k) > 0)
    { /* next partial quotient will overflow limits */
      GEN n, d;
      a = divii(subii(k, q1), q0);
      p = addii(mulii(a,p0), p1); p1=p0; p0=p;
      q = addii(mulii(a,q0), q1); q1=q0; q0=q;
      /* compare |y-p0/q0|, |y-p1/q1| */
      n = gel(y,1);
      d = gel(y,2);
      if (abscmpii(mulii(q1, subii(mulii(q0,n), mulii(d,p0))),
                   mulii(q0, subii(mulii(q1,n), mulii(d,p1)))) < 0)
                   { p1 = p0; q1 = q0; }
      break;
    }
    p = addii(mulii(a,p0), p1); p1=p0; p0=p;
    q = addii(mulii(a,q0), q1); q1=q0; q0=q;

    if (cmpii(q0,k) > 0) break;
    x = gsub(x,a); /* 0 <= x < 1 */
    if (typ(x) == t_INT) { p1 = p0; q1 = q0; break; } /* x = 0 */

  }
  return gerepileupto(av, gdiv(p1,q1));
}
/* k > 0 t_INT, x != 0 a t_REAL, returns the convergent a/b
 * of the continued fraction of x with b <= k maximal */
static GEN
bestappr_real(GEN x, GEN k)
{
  pari_sp av = avma;
  GEN kr, p0, p1, p, q0, q1, q, a, y = x;

  p1 = gen_1; a = p0 = floorr(x);
  q1 = gen_0; q0 = gen_1;
  x = subri(x,a); /* 0 <= x < 1 */
  if (!signe(x)) { cgiv(x); return a; }
  kr = itor(k, realprec(x));
  for(;;)
  {
    long d;
    x = invr(x); /* > 1 */
    if (cmprr(x,kr) > 0)
    { /* next partial quotient will overflow limits */
      a = divii(subii(k, q1), q0);
      p = addii(mulii(a,p0), p1); p1=p0; p0=p;
      q = addii(mulii(a,q0), q1); q1=q0; q0=q;
      /* compare |y-p0/q0|, |y-p1/q1| */
      if (abscmprr(mulir(q1, subri(mulir(q0,y), p0)),
                   mulir(q0, subri(mulir(q1,y), p1))) < 0)
                   { p1 = p0; q1 = q0; }
      break;
    }
    d = nbits2prec(expo(x) + 1);
    if (d > lg(x)) { p1 = p0; q1 = q0; break; } /* original x was ~ 0 */

    a = truncr(x); /* truncr(x) will NOT raise e_PREC */
    p = addii(mulii(a,p0), p1); p1=p0; p0=p;
    q = addii(mulii(a,q0), q1); q1=q0; q0=q;

    if (cmpii(q0,k) > 0) break;
    x = subri(x,a); /* 0 <= x < 1 */
    if (!signe(x)) { p1 = p0; q1 = q0; break; }
  }
  if (signe(q1) < 0) { togglesign_safe(&p1); togglesign_safe(&q1); }
  return gerepilecopy(av, equali1(q1)? p1: mkfrac(p1,q1));
}

/* k t_INT or NULL */
static GEN
bestappr_Q(GEN x, GEN k)
{
  long lx, tx = typ(x), i;
  GEN a, y;

  switch(tx)
  {
    case t_INT: return icopy(x);
    case t_FRAC: return k? bestappr_frac(x, k): gcopy(x);
    case t_REAL:
      if (!signe(x)) return gen_0;
      /* i <= e iff nbits2lg(e+1) > lg(x) iff floorr(x) fails */
      i = bit_prec(x); if (i <= expo(x)) return NULL;
      return bestappr_real(x, k? k: int2n(i));

    case t_INTMOD: {
      pari_sp av = avma;
      a = mod_to_frac(gel(x,2), gel(x,1), k); if (!a) return NULL;
      return gerepilecopy(av, a);
    }
    case t_PADIC: {
      pari_sp av = avma;
      long v = valp(x);
      a = mod_to_frac(gel(x,4), gel(x,3), k); if (!a) return NULL;
      if (v) a = gmul(a, powis(gel(x,2), v));
      return gerepilecopy(av, a);
    }

    case t_COMPLEX: {
      pari_sp av = avma;
      y = cgetg(3, t_COMPLEX);
      gel(y,2) = bestappr(gel(x,2), k);
      gel(y,1) = bestappr(gel(x,1), k);
      if (gequal0(gel(y,2))) return gerepileupto(av, gel(y,1));
      return y;
    }
    case t_SER:
      if (ser_isexactzero(x)) return gcopy(x);
      /* fall through */
    case t_POLMOD: case t_POL: case t_RFRAC:
    case t_VEC: case t_COL: case t_MAT:
      y = cgetg_copy(x, &lx);
      if (lontyp[tx] == 1) i = 1; else { y[1] = x[1]; i = 2; }
      for (; i<lx; i++)
      {
        a = bestappr_Q(gel(x,i),k); if (!a) return NULL;
        gel(y,i) = a;
      }
      if (tx == t_POL) return normalizepol(y);
      if (tx == t_SER) return normalize(y);
      return y;
  }
  pari_err_TYPE("bestappr_Q",x);
  return NULL; /* LCOV_EXCL_LINE */
}

static GEN
bestappr_ser(GEN x, long B)
{
  long dN, v = valp(x), lx = lg(x);
  GEN t;
  x = normalizepol(ser2pol_i(x, lx));
  dN = lx-2;
  if (v > 0)
  {
    x = RgX_shift_shallow(x, v);
    dN += v;
  }
  else if (v < 0)
  {
    if (B >= 0) B = maxss(B+v, 0);
  }
  t = mod_to_rfrac(x, pol_xn(dN, varn(x)), B);
  if (!t) return NULL;
  if (v < 0)
  {
    GEN a, b;
    long vx;
    if (typ(t) == t_POL) return RgX_mulXn(t, v);
    /* t_RFRAC */
    vx = varn(x);
    a = gel(t,1);
    b = gel(t,2);
    v -= RgX_valrem(b, &b);
    if (typ(a) == t_POL && varn(a) == vx) v += RgX_valrem(a, &a);
    if (v < 0) b = RgX_shift(b, -v);
    else if (v > 0) {
      if (typ(a) != t_POL || varn(a) != vx) a = scalarpol_shallow(a, vx);
      a = RgX_shift(a, v);
    }
    t = mkrfraccopy(a, b);
  }
  return t;
}
static GEN bestappr_RgX(GEN x, long B);
/* x t_POLMOD, B >= 0 or < 0 [omit condition on B].
 * Look for coprime t_POL a,b, deg(b)<=B, such that a/b = x */
static GEN
bestappr_RgX(GEN x, long B)
{
  long i, lx, tx = typ(x);
  GEN y, t;
  switch(tx)
  {
    case t_INT: case t_REAL: case t_INTMOD: case t_FRAC:
    case t_COMPLEX: case t_PADIC: case t_QUAD: case t_POL:
      return gcopy(x);

    case t_RFRAC: {
      pari_sp av = avma;
      if (B < 0 || degpol(gel(x,2)) <= B) return gcopy(x);
      x = rfrac_to_ser(x, 2*B+1);
      t = bestappr_ser(x, B); if (!t) return NULL;
      return gerepileupto(av, t);
    }
    case t_POLMOD: {
      pari_sp av = avma;
      t = mod_to_rfrac(gel(x,2), gel(x,1), B); if (!t) return NULL;
      return gerepileupto(av, t);
    }
    case t_SER: {
      pari_sp av = avma;
      t = bestappr_ser(x, B); if (!t) return NULL;
      return gerepileupto(av, t);
    }

    case t_VEC: case t_COL: case t_MAT:
      y = cgetg_copy(x, &lx);
      if (lontyp[tx] == 1) i = 1; else { y[1] = x[1]; i = 2; }
      for (; i<lx; i++)
      {
        t = bestappr_RgX(gel(x,i),B); if (!t) return NULL;
        gel(y,i) = t;
      }
      return y;
  }
  pari_err_TYPE("bestappr_RgX",x);
  return NULL; /* LCOV_EXCL_LINE */
}

/* allow k = NULL: maximal accuracy */
GEN
bestappr(GEN x, GEN k)
{
  pari_sp av = avma;
  if (k) { /* replace by floor(k) */
    switch(typ(k))
    {
      case t_INT:
        break;
      case t_REAL: case t_FRAC:
        k = floor_safe(k); /* left on stack for efficiency */
        if (!signe(k)) k = gen_1;
        break;
      default:
        pari_err_TYPE("bestappr [bound type]", k);
        break;
    }
  }
  x = bestappr_Q(x, k);
  if (!x) { avma = av; return cgetg(1,t_VEC); }
  return x;
}
GEN
bestapprPade(GEN x, long B)
{
  pari_sp av = avma;
  GEN t = bestappr_RgX(x, B);
  if (!t) { avma = av; return cgetg(1,t_VEC); }
  return t;
}

/***********************************************************************/
/**                                                                   **/
/**         FUNDAMENTAL UNIT AND REGULATOR (QUADRATIC FIELDS)         **/
/**                                                                   **/
/***********************************************************************/

static GEN
get_quad(GEN f, GEN pol, long r)
{
  GEN p1 = gcoeff(f,1,2), q1 = gcoeff(f,2,2);
  return mkquad(pol, r? subii(p1,q1): p1, q1);
}

/* replace f by f * [a,1; 1,0] */
static void
update_f(GEN f, GEN a)
{
  GEN p1;
  p1 = gcoeff(f,1,1);
  gcoeff(f,1,1) = addii(mulii(a,p1), gcoeff(f,1,2));
  gcoeff(f,1,2) = p1;

  p1 = gcoeff(f,2,1);
  gcoeff(f,2,1) = addii(mulii(a,p1), gcoeff(f,2,2));
  gcoeff(f,2,2) = p1;
}

GEN
quadunit(GEN x)
{
  pari_sp av = avma, av2;
  GEN pol, y, a, u, v, sqd, f;
  long r;

  check_quaddisc_real(x, &r, "quadunit");
  pol = quadpoly(x);
  sqd = sqrti(x); av2 = avma;
  a = shifti(addui(r,sqd),-1);
  f = mkmat2(mkcol2(a, gen_1), mkcol2(gen_1, gen_0)); /* [a,0; 1,0] */
  u = stoi(r); v = gen_2;
  for(;;)
  {
    GEN u1, v1;
    u1 = subii(mulii(a,v),u);
    v1 = divii(subii(x,sqri(u1)),v);
    if ( equalii(v,v1) ) {
      y = get_quad(f,pol,r);
      update_f(f,a);
      y = gdiv(get_quad(f,pol,r), conj_i(y));
      break;
    }
    a = divii(addii(sqd,u1), v1);
    if ( equalii(u,u1) ) {
      y = get_quad(f,pol,r);
      y = gdiv(y, conj_i(y));
      break;
    }
    update_f(f,a);
    u = u1; v = v1;
    if (gc_needed(av2,2))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"quadunit");
      gerepileall(av2,4, &a,&f,&u,&v);
    }
  }
  if (signe(gel(y,3)) < 0) y = gneg(y);
  return gerepileupto(av, y);
}

GEN
quadunit0(GEN x, long v)
{
  GEN y = quadunit(x);
  if (v==-1) v = fetch_user_var("w");
  setvarn(gel(y,1), v);
  return y;
}

GEN
quadregulator(GEN x, long prec)
{
  pari_sp av = avma, av2;
  GEN R, rsqd, u, v, sqd;
  long r, Rexpo;

  check_quaddisc_real(x, &r, "quadregulator");
  sqd = sqrti(x);
  rsqd = gsqrt(x,prec);
  Rexpo = 0; R = real2n(1, prec); /* = 2 */
  av2 = avma;
  u = stoi(r); v = gen_2;
  for(;;)
  {
    GEN u1 = subii(mulii(divii(addii(u,sqd),v), v), u);
    GEN v1 = divii(subii(x,sqri(u1)),v);
    if (equalii(v,v1))
    {
      R = sqrr(R); shiftr_inplace(R, -1);
      R = mulrr(R, divri(addir(u1,rsqd),v));
      break;
    }
    if (equalii(u,u1))
    {
      R = sqrr(R); shiftr_inplace(R, -1);
      break;
    }
    R = mulrr(R, divri(addir(u1,rsqd),v));
    Rexpo += expo(R); setexpo(R,0);
    u = u1; v = v1;
    if (Rexpo & ~EXPOBITS) pari_err_OVERFLOW("quadregulator [exponent]");
    if (gc_needed(av2,2))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"quadregulator");
      gerepileall(av2,3, &R,&u,&v);
    }
  }
  R = logr_abs(divri(R,v));
  if (Rexpo)
  {
    GEN t = mulsr(Rexpo, mplog2(prec));
    shiftr_inplace(t, 1);
    R = addrr(R,t);
  }
  return gerepileuptoleaf(av, R);
}

/*************************************************************************/
/**                                                                     **/
/**                            CLASS NUMBER                             **/
/**                                                                     **/
/*************************************************************************/

int
qfb_equal1(GEN f) { return equali1(gel(f,1)); }

static GEN qfi_pow(void *E, GEN f, GEN n)
{ return E? nupow(f,n,(GEN)E): powgi(f,n); }
static GEN qfi_comp(void *E, GEN f, GEN g)
{ return E? nucomp(f,g,(GEN)E): qficomp(f,g); }
static const struct bb_group qfi_group={ qfi_comp,qfi_pow,NULL,hash_GEN,
                                         gidentical,qfb_equal1,NULL};

GEN
qfi_order(GEN q, GEN o)
{ return gen_order(q, o, NULL, &qfi_group); }

GEN
qfi_log(GEN a, GEN g, GEN o)
{ return gen_PH_log(a, g, o, NULL, &qfi_group); }

GEN
qfi_Shanks(GEN a, GEN g, long n)
{
  pari_sp av = avma;
  GEN T, X;
  long rt_n, c;

  a = redimag(a);
  g = redimag(g);

  rt_n = sqrt((double)n);
  c = n / rt_n;
  c = (c * rt_n < n + 1) ? c + 1 : c;

  T = gen_Shanks_init(g, rt_n, NULL, &qfi_group);
  X = gen_Shanks(T, a, c, NULL, &qfi_group);

  if (!X) { avma = av; return X; }
  return gerepileuptoint(av, X);
}

GEN
qfbclassno0(GEN x,long flag)
{
  switch(flag)
  {
    case 0: return map_proto_G(classno,x);
    case 1: return map_proto_G(classno2,x);
    default: pari_err_FLAG("qfbclassno");
  }
  return NULL; /* LCOV_EXCL_LINE */
}

/* f^h = 1, return order(f). Set *pfao to its factorization */
static GEN
find_order(void *E, GEN f, GEN h, GEN *pfao)
{
  GEN v = gen_factored_order(f, h, E, &qfi_group);
  *pfao = gel(v,2); return gel(v,1);
}

static int
ok_q(GEN q, GEN h, GEN d2, long r2)
{
  if (d2)
  {
    if (r2 <= 2 && !mpodd(q)) return 0;
    return is_pm1(Z_ppo(q,d2));
  }
  else
  {
    if (r2 <= 1 && !mpodd(q)) return 0;
    return is_pm1(Z_ppo(q,h));
  }
}

/* a,b given by their factorizations. Return factorization of lcm(a,b).
 * Set A,B such that A*B = lcm(a, b), (A,B)=1, A|a, B|b */
static GEN
split_lcm(GEN a, GEN Fa, GEN b, GEN Fb, GEN *pA, GEN *pB)
{
  GEN P = ZC_union_shallow(gel(Fa,1), gel(Fb,1));
  GEN A = gen_1, B = gen_1;
  long i, l = lg(P);
  GEN E = cgetg(l, t_COL);
  for (i=1; i<l; i++)
  {
    GEN p = gel(P,i);
    long va = Z_pval(a,p);
    long vb = Z_pval(b,p);
    if (va < vb)
    {
      B = mulii(B,powiu(p,vb));
      gel(E,i) = utoi(vb);
    }
    else
    {
      A = mulii(A,powiu(p,va));
      gel(E,i) = utoi(va);
    }
  }
  *pA = A;
  *pB = B; return mkmat2(P,E);
}

/* g1 has order d1, f has order o, replace g1 by an element of order lcm(d1,o)*/
static void
update_g1(GEN *pg1, GEN *pd1, GEN *pfad1, GEN f, GEN o, GEN fao)
{
  GEN A,B, g1 = *pg1, d1 = *pd1;
  *pfad1 = split_lcm(d1,*pfad1, o,fao, &A,&B);
  *pg1 = gmul(powgi(g1, diviiexact(d1,A)),  powgi(f, diviiexact(o,B)));
  *pd1 = mulii(A,B); /* g1 has order d1 <- lcm(d1,o) */
}

/* Write x = Df^2, where D = fundamental discriminant,
 * P^E = factorisation of conductor f, with E[i] >= 0 */
static void
corediscfact(GEN x, long xmod4, GEN *ptD, GEN *ptP, GEN *ptE)
{
  long s = signe(x), l, i;
  GEN fa = absZ_factor(x);
  GEN d, P = gel(fa,1), E = gtovecsmall(gel(fa,2));

  l = lg(P); d = gen_1;
  for (i=1; i<l; i++)
  {
    if (E[i] & 1) d = mulii(d, gel(P,i));
    E[i] >>= 1;
  }
  if (!xmod4 && mod4(d) != ((s < 0)? 3: 1)) { d = shifti(d,2); E[1]--; }
  *ptD = (s < 0)? negi(d): d;
  *ptP = P;
  *ptE = E;
}

static GEN
conductor_part(GEN x, long xmod4, GEN *ptD, GEN *ptreg)
{
  long l, i, s = signe(x);
  GEN E, H, D, P, reg;

  corediscfact(x, xmod4, &D, &P, &E);
  H = gen_1; l = lg(P);
  /* f \prod_{p|f}  [ 1 - (D/p) p^-1 ] = \prod_{p^e||f} p^(e-1) [ p - (D/p) ] */
  for (i=1; i<l; i++)
  {
    long e = E[i];
    if (e)
    {
      GEN p = gel(P,i);
      H = mulii(H, subis(p, kronecker(D,p)));
      if (e >= 2) H = mulii(H, powiu(p,e-1));
    }
  }

  /* divide by [ O_K^* : O^* ] */
  if (s < 0)
  {
    reg = NULL;
    switch(itou_or_0(D))
    {
      case 4: H = shifti(H,-1); break;
      case 3: H = divis(H,3); break;
    }
  } else {
    reg = quadregulator(D,DEFAULTPREC);
    if (!equalii(x,D))
      H = divii(H, roundr(divrr(quadregulator(x,DEFAULTPREC), reg)));
  }
  if (ptreg) *ptreg = reg;
  *ptD = D; return H;
}

static long
two_rank(GEN x)
{
  GEN p = gel(absZ_factor(x),1);
  long l = lg(p)-1;
#if 0 /* positive disc not needed */
  if (signe(x) > 0)
  {
    long i;
    for (i=1; i<=l; i++)
      if (mod4(gel(p,i)) == 3) { l--; break; }
  }
#endif
  return l-1;
}

static GEN
sqr_primeform(GEN x, ulong p) { return redimag(qfisqr(primeform_u(x, p))); }
/* return a set of forms hopefully generating Cl(K)^2; set L ~ L(chi_D,1) */
static GEN
get_forms(GEN D, GEN *pL)
{
  const long MAXFORM = 20;
  GEN L, sqrtD = gsqrt(absi_shallow(D),DEFAULTPREC);
  GEN forms = vectrunc_init(MAXFORM+1);
  long s, nforms = 0;
  ulong p;
  forprime_t S;
  L = mulrr(divrr(sqrtD,mppi(DEFAULTPREC)), dbltor(1.005));/*overshoot by 0.5%*/
  s = itos_or_0( truncr(shiftr(sqrtr(sqrtD), 1)) );
  if (!s) pari_err_OVERFLOW("classno [discriminant too large]");
  if      (s < 10)   s = 200;
  else if (s < 20)   s = 1000;
  else if (s < 5000) s = 5000;
  u_forprime_init(&S, 2, s);
  while ( (p = u_forprime_next(&S)) )
  {
    long d, k = kroiu(D,p);
    pari_sp av2;
    if (!k) continue;
    if (k > 0)
    {
      if (++nforms < MAXFORM) vectrunc_append(forms, sqr_primeform(D,p));
      d = p-1;
    }
    else
      d = p+1;
    av2 = avma; affrr(divru(mulur(p,L),d), L); avma = av2;
  }
  *pL = L; return forms;
}

/* h ~ #G, return o = order of f, set fao = its factorization */
static  GEN
Shanks_order(void *E, GEN f, GEN h, GEN *pfao)
{
  long s = minss(itos(sqrti(h)), 10000);
  GEN T = gen_Shanks_init(f, s, E, &qfi_group);
  GEN v = gen_Shanks(T, ginv(f), ULONG_MAX, E, &qfi_group);
  return find_order(E, f, addiu(v,1), pfao);
}

/* if g = 1 in  G/<f> ? */
static int
equal1(void *E, GEN T, ulong N, GEN g)
{ return !!gen_Shanks(T, g, N, E, &qfi_group); }

/* Order of 'a' in G/<f>, T = gen_Shanks_init(f,n), order(f) < n*N
 * FIXME: should be gen_order, but equal1 has the wrong prototype */
static GEN
relative_order(void *E, GEN a, GEN o, ulong N,  GEN T)
{
  pari_sp av = avma;
  long i, l;
  GEN m;

  m = get_arith_ZZM(o);
  if (!m) pari_err_TYPE("gen_order [missing order]",a);
  o = gel(m,1);
  m = gel(m,2); l = lgcols(m);
  for (i = l-1; i; i--)
  {
    GEN t, y, p = gcoeff(m,i,1);
    long j, e = itos(gcoeff(m,i,2));
    if (l == 2) {
      t = gen_1;
      y = a;
    } else {
      t = diviiexact(o, powiu(p,e));
      y = powgi(a, t);
    }
    if (equal1(E, T,N,y)) o = t;
    else {
      for (j = 1; j < e; j++)
      {
        y = powgi(y, p);
        if (equal1(E, T,N,y)) break;
      }
      if (j < e) {
        if (j > 1) p = powiu(p, j);
        o = mulii(t, p);
      }
    }
  }
  return gerepilecopy(av, o);
}

/* h(x) for x<0 using Baby Step/Giant Step.
 * Assumes G is not too far from being cyclic.
 *
 * Compute G^2 instead of G so as to kill most of the non-cyclicity */
GEN
classno(GEN x)
{
  pari_sp av = avma;
  long r2, k, s, i, l;
  GEN forms, hin, Hf, D, g1, d1, d2, q, L, fad1, order_bound;
  void *E;

  if (signe(x) >= 0) return classno2(x);

  check_quaddisc(x, &s, &k, "classno");
  if (abscmpiu(x,12) <= 0) return gen_1;

  Hf = conductor_part(x, k, &D, NULL);
  if (abscmpiu(D,12) <= 0) return gerepilecopy(av, Hf);
  forms =  get_forms(D, &L);
  r2 = two_rank(D);
  hin = roundr(shiftr(L, -r2)); /* rough approximation for #G, G = Cl(K)^2 */

  l = lg(forms);
  order_bound = const_vec(l-1, NULL);
  E = expi(D) > 60? (void*)sqrtnint(shifti(absi_shallow(D),-2),4): NULL;
  g1 = gel(forms,1);
  gel(order_bound,1) = d1 = Shanks_order(E, g1, hin, &fad1);
  q = diviiround(hin, d1); /* approximate order of G/<g1> */
  d2 = NULL; /* not computed yet */
  if (is_pm1(q)) goto END;
  for (i=2; i < l; i++)
  {
    GEN o, fao, a, F, fd, f = gel(forms,i);
    fd = powgi(f, d1); if (is_pm1(gel(fd,1))) continue;
    F = powgi(fd, q);
    a = gel(F,1);
    o = is_pm1(a)? find_order(E, fd, q, &fao): Shanks_order(E, fd, q, &fao);
    /* f^(d1 q) = 1 */
    fao = merge_factor(fad1,fao, (void*)&cmpii, &cmp_nodata);
    o = find_order(E, f, fao, &fao);
    gel(order_bound,i) = o;
    /* o = order of f, fao = factor(o) */
    update_g1(&g1,&d1,&fad1, f,o,fao);
    q = diviiround(hin, d1);
    if (is_pm1(q)) goto END;
  }
  /* very probably d1 = expo(Cl^2(K)), q ~ #Cl^2(K) / d1 */
  if (expi(q) > 3)
  { /* q large: compute d2, 2nd elt divisor */
    ulong N, n = 2*itou(sqrti(d1));
    GEN D = d1, T = gen_Shanks_init(g1, n, E, &qfi_group);
    d2 = gen_1;
    N = itou( gceil(gdivgs(d1,n)) ); /* order(g1) <= n*N */
    for (i = 1; i < l; i++)
    {
      GEN d, f = gel(forms,i), B = gel(order_bound,i);
      if (!B) B = find_order(E, f, fad1, /*junk*/&d);
      f = powgi(f,d2);
      if (equal1(E, T,N,f)) continue;
      B = gdiv(B,d2); if (typ(B) == t_FRAC) B = gel(B,1);
      /* f^B = 1 */
      d = relative_order(E, f, B, N,T);
      d2= mulii(d,d2);
      D = mulii(d1,d2);
      q = diviiround(hin,D);
      if (is_pm1(q)) { d1 = D; goto END; }
    }
    /* very probably, d2 is the 2nd elementary divisor */
    d1 = D; /* product of first two elt divisors */
  }
  /* impose q | d2^oo (d1^oo if d2 not computed), and compatible with known
   * 2-rank */
  if (!ok_q(q,d1,d2,r2))
  {
    GEN q0 = q;
    long d;
    if (cmpii(mulii(q,d1), hin) < 0)
    { /* try q = q0+1,-1,+2,-2 */
      d = 1;
      do { q = addis(q0,d); d = d>0? -d: 1-d; } while(!ok_q(q,d1,d2,r2));
    }
    else
    { /* q0-1,+1,-2,+2  */
      d = -1;
      do { q = addis(q0,d); d = d<0? -d: -1-d; } while(!ok_q(q,d1,d2,r2));
    }
  }
  d1 = mulii(d1,q);

END:
  return gerepileuptoint(av, shifti(mulii(d1,Hf), r2));
}

GEN
quadclassno(GEN x)
{
  pari_sp av = avma;
  GEN Hf, D;
  long s, r;
  check_quaddisc(x, &s, &r, "quadclassno");
  if (s < 0 && abscmpiu(x,12) <= 0) return gen_1;
  Hf = conductor_part(x, r, &D, NULL);
  return gerepileuptoint(av, mulii(Hf, gel(quadclassunit0(D,0,NULL,0),1)));
}

/* use Euler products */
GEN
classno2(GEN x)
{
  pari_sp av = avma;
  const long prec = DEFAULTPREC;
  long n, i, r, s;
  GEN p1, p2, S, p4, p5, p7, Hf, Pi, reg, logd, d, dr, D, half;

  check_quaddisc(x, &s, &r, "classno2");
  if (s < 0 && abscmpiu(x,12) <= 0) return gen_1;

  Hf = conductor_part(x, r, &D, &reg);
  if (s < 0 && abscmpiu(D,12) <= 0) return gerepilecopy(av, Hf); /* |D| < 12*/

  Pi = mppi(prec);
  d = absi_shallow(D); dr = itor(d, prec);
  logd = logr_abs(dr);
  p1 = sqrtr(divrr(mulir(d,logd), gmul2n(Pi,1)));
  if (s > 0)
  {
    GEN invlogd = invr(logd);
    p2 = subsr(1, shiftr(mulrr(logr_abs(reg),invlogd),1));
    if (cmprr(sqrr(p2), shiftr(invlogd,1)) >= 0) p1 = mulrr(p2,p1);
  }
  n = itos_or_0( mptrunc(p1) );
  if (!n) pari_err_OVERFLOW("classno [discriminant too large]");

  p4 = divri(Pi,d);
  p7 = invr(sqrtr_abs(Pi));
  half = real2n(-1, prec);
  if (s > 0)
  { /* i = 1, shortcut */
    p1 = sqrtr_abs(dr);
    p5 = subsr(1, mulrr(p7,incgamc(half,p4,prec)));
    S = addrr(mulrr(p1,p5), eint1(p4,prec));
    for (i=2; i<=n; i++)
    {
      long k = kroiu(D,i); if (!k) continue;
      p2 = mulir(sqru(i), p4);
      p5 = subsr(1, mulrr(p7,incgamc(half,p2,prec)));
      p5 = addrr(divru(mulrr(p1,p5),i), eint1(p2,prec));
      S = (k>0)? addrr(S,p5): subrr(S,p5);
    }
    S = shiftr(divrr(S,reg),-1);
  }
  else
  { /* i = 1, shortcut */
    p1 = gdiv(sqrtr_abs(dr), Pi);
    p5 = subsr(1, mulrr(p7,incgamc(half,p4,prec)));
    S = addrr(p5, divrr(p1, mpexp(p4)));
    for (i=2; i<=n; i++)
    {
      long k = kroiu(D,i); if (!k) continue;
      p2 = mulir(sqru(i), p4);
      p5 = subsr(1, mulrr(p7,incgamc(half,p2,prec)));
      p5 = addrr(p5, divrr(p1, mulur(i, mpexp(p2))));
      S = (k>0)? addrr(S,p5): subrr(S,p5);
    }
  }
  return gerepileuptoint(av, mulii(Hf, roundr(S)));
}

/* 1 + q + ... + q^v, v > 0 */
static GEN
geomsumu(ulong q, long v)
{
  GEN u = utoipos(1+q);
  for (; v > 1; v--) u = addui(1, mului(q, u));
  return u;
}
static GEN
geomsum(GEN q, long v)
{
  GEN u;
  if (lgefint(q) == 3) return geomsumu(q[2], v);
  u = addiu(q,1);
  for (; v > 1; v--) u = addui(1, mulii(q, u));
  return u;
}

static GEN
hclassno6_large(GEN x)
{
  long i, l, s, xmod4;
  GEN Q, H, D, P, E;

  x = negi(x);
  check_quaddisc(x, &s, &xmod4, "hclassno");
  corediscfact(x, xmod4, &D, &P, &E);

  Q = quadclassunit0(D, 0, NULL, 0);
  H = gel(Q,1); l = lg(P);

  /* H \prod_{p^e||f}  (1 + (p^e-1)/(p-1))[ p - (D/p) ] */
  for (i=1; i<l; i++)
  {
    long e = E[i], s;
    GEN p, t;
    if (!e) continue;
    p = gel(P,i); s = kronecker(D,p);
    if (e == 1) t = addiu(p, 1-s);
    else if (s == 1) t = powiu(p,e);
    else t = addui(1, mulii(subis(p, s), geomsum(p,e-1)));
    H = mulii(H,t);
  }
  switch( itou_or_0(D) )
  {
    case 3: H = shifti(H,1);break;
    case 4: H = muliu(H,3); break;
    default:H = muliu(H,6); break;
  }
  return H;
}

/* x > 0, x = 0,3 (mod 4). Return 6*hclassno(x), an integer */
GEN
hclassno6(GEN x)
{
  ulong d = itou_or_0(x);
  if (!d || d > 500000) return hclassno6_large(x);
  return utoipos(hclassno6u(d));
}

GEN
hclassno(GEN x)
{
  long a, s;
  if (typ(x) != t_INT) pari_err_TYPE("hclassno",x);
  s = signe(x);
  if (s < 0) return gen_0;
  if (!s) return gdivgs(gen_1, -12);
  a = mod4(x); if (a == 1 || a == 2) return gen_0;
  return gdivgs(hclassno6(x), 6);
}
/******************************************************************/
/*                                                                */
/*                 RAMANUJAN's TAU FUNCTION                       */
/*                                                                */
/******************************************************************/
/* 4|N > 0, not fundamental at 2; 6 * Hurwitz class number in level 2,
 * equal to 6*(H(N)+2H(N/4)), H=qfbhclassno */
static GEN
Hspec(GEN N)
{
  long v2 = Z_lvalrem(N, 2, &N), v2f = v2 >> 1;
  GEN t;
  if (odd(v2)) { v2f--; N = shifti(N,3); }
  else if (mod4(N)!=3) { v2f--; N = shifti(N,2); }
  /* N fundamental at 2, v2f = v2(f) s.t. N = f^2 D, D fundamental */
  t = addui(3, muliu(subiu(int2n(v2f+1), 3), 2 - kroiu(N,2)));
  return mulii(t, hclassno6(N));
}

/* Ramanujan tau function for p prime */
static GEN
tauprime(GEN p)
{
  pari_sp av = avma, av2;
  GEN s, p2, p2_7, p_9, T;
  ulong lim, t, tin;

  if (absequaliu(p, 2)) return utoineg(24);
  /* p > 2 */
  p2 = sqri(p);
  p2_7 = mului(7, p2);
  p_9 = mului(9, p);
  av2 = avma;
  lim = itou(sqrtint(p));
  tin = mod4(p) == 3? 1: 0;
  s = gen_0;
  for (t = 1; t <= lim; ++t)
  {
    GEN h, a, t2 = sqru(t), D = shifti(subii(p, t2), 2); /* 4(p-t^2) */
    /* t mod 2 != tin <=> D not fundamental at 2 */
    h = ((t&1UL) == tin)? hclassno6(D): Hspec(D);
    a = mulii(powiu(t2,3), addii(p2_7, mulii(t2, subii(shifti(t2,2), p_9))));
    s = addii(s, mulii(a,h));
    if (!(t & 255)) s = gerepileuptoint(av2, s);
  }
  /* 28p^3 - 28p^2 - 90p - 35 */
  T = subii(shifti(mulii(p2_7, subiu(p,1)), 2), addiu(mului(90,p), 35));
  s = shifti(diviuexact(s, 3), 6);
  return gerepileuptoint(av, subii(mulii(mulii(p2,p),T), addui(1, s)));
}

/* Ramanujan tau function, return 0 for <= 0 */
GEN
ramanujantau(GEN n)
{
  pari_sp ltop = avma;
  GEN T, F, P, E;
  long j, lP;

  if (!(F = check_arith_all(n,"ramanujantau")))
  {
    if (signe(n) <= 0) return gen_0;
    F = Z_factor(n);
  }
  else
  {
    P = gel(F,1);
    if (lg(P) == 1 || signe(gel(P,1)) <= 0) return gen_0;
  }

  P = gel(F,1);
  E = gel(F,2); lP = lg(P);
  T = gen_1;
  for (j = 1; j < lP; j++)
  {
    GEN p = gel(P,j), tp = tauprime(p), t1 = tp, t0 = gen_1;
    long k, e = itou(gel(E,j));
    for (k = 1; k < e; k++)
    {
      GEN t2 = subii(mulii(tp, t1), mulii(powiu(p, 11), t0));
      t0 = t1; t1 = t2;
    }
    T = mulii(T, t1);
  }
  return gerepileuptoint(ltop, T);
}
