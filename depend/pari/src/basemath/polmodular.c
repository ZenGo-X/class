/* Copyright (C) 2014  The PARI group.

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

#define dbg_printf(lvl) if (DEBUGLEVEL >= (lvl) + 3) err_printf

/**
 * START Code from AVSs "class_inv.h"
 */

/* actually just returns the square-free part of the level, which is
 * all we care about */
long
modinv_level(long inv)
{
  switch (inv) {
    case INV_J:     return 1;
    case INV_G2:
    case INV_W3W3E2:return 3;
    case INV_F:
    case INV_F2:
    case INV_F4:
    case INV_F8:    return 6;
    case INV_F3:    return 2;
    case INV_W3W3:  return 6;
    case INV_W2W7E2:
    case INV_W2W7:  return 14;
    case INV_W3W5:  return 15;
    case INV_W2W3E2:
    case INV_W2W3:  return 6;
    case INV_W2W5E2:
    case INV_W2W5:  return 30;
    case INV_W2W13: return 26;
    case INV_W3W7:  return 42;
    case INV_W5W7:  return 35;
    case INV_W3W13: return 39;
  }
  pari_err_BUG("modinv_level"); return 0;/*LCOV_EXCL_LINE*/
}

/* Where applicable, returns N=p1*p2 (possibly p2=1) s.t. two j's
 * related to the same f are N-isogenous, and 0 otherwise.  This is
 * often (but not necessarily) equal to the level. */
long
modinv_degree(long *P1, long *P2, long inv)
{
  long *p1, *p2, ignored;
  p1 = P1? P1: &ignored;
  p2 = P2? P2: &ignored;
  switch (inv) {
    case INV_W3W5:  return (*p1 = 3) * (*p2 = 5);
    case INV_W2W3E2:
    case INV_W2W3:  return (*p1 = 2) * (*p2 = 3);
    case INV_W2W5E2:
    case INV_W2W5:  return (*p1 = 2) * (*p2 = 5);
    case INV_W2W7E2:
    case INV_W2W7:  return (*p1 = 2) * (*p2 = 7);
    case INV_W2W13: return (*p1 = 2) * (*p2 = 13);
    case INV_W3W7:  return (*p1 = 3) * (*p2 = 7);
    case INV_W3W3E2:
    case INV_W3W3:  return (*p1 = 3) * (*p2 = 3);
    case INV_W5W7:  return (*p1 = 5) * (*p2 = 7);
    case INV_W3W13: return (*p1 = 3) * (*p2 = 13);
  }
  *p1 = *p2 = 1; return 0;
}

/* Certain invariants require that D not have 2 in it's conductor, but
 * this doesn't apply to every invariant with even level so we handle
 * it separately */
INLINE int
modinv_odd_conductor(long inv)
{
  switch (inv) {
    case INV_F:
    case INV_W3W3:
    case INV_W3W7: return 1;
  }
  return 0;
}

long
modinv_height_factor(long inv)
{
  switch (inv) {
    case INV_J:     return 1;
    case INV_G2:    return 3;
    case INV_F:     return 72;
    case INV_F2:    return 36;
    case INV_F3:    return 24;
    case INV_F4:    return 18;
    case INV_F8:    return 9;
    case INV_W2W3:  return 72;
    case INV_W3W3:  return 36;
    case INV_W2W5:  return 54;
    case INV_W2W7:  return 48;
    case INV_W3W5:  return 36;
    case INV_W2W13: return 42;
    case INV_W3W7:  return 32;
    case INV_W2W3E2:return 36;
    case INV_W2W5E2:return 27;
    case INV_W2W7E2:return 24;
    case INV_W3W3E2:return 18;
    case INV_W5W7:  return 24;
    case INV_W3W13: return 28;
    default: pari_err_BUG("modinv_height_factor"); return 0;/*LCOV_EXCL_LINE*/
  }
}

long
disc_best_modinv(long D)
{
  long ret;
  ret = INV_F;     if (modinv_good_disc(ret, D)) return ret;
  ret = INV_W2W3;  if (modinv_good_disc(ret, D)) return ret;
  ret = INV_W2W5;  if (modinv_good_disc(ret, D)) return ret;
  ret = INV_W2W7;  if (modinv_good_disc(ret, D)) return ret;
  ret = INV_W2W13; if (modinv_good_disc(ret, D)) return ret;
  ret = INV_W3W3;  if (modinv_good_disc(ret, D)) return ret;
  ret = INV_W2W3E2;if (modinv_good_disc(ret, D)) return ret;
  ret = INV_W3W5;  if (modinv_good_disc(ret, D)) return ret;
  ret = INV_W3W7;  if (modinv_good_disc(ret, D)) return ret;
  ret = INV_W3W13; if (modinv_good_disc(ret, D)) return ret;
  ret = INV_W2W5E2;if (modinv_good_disc(ret, D)) return ret;
  ret = INV_F3;    if (modinv_good_disc(ret, D)) return ret;
  ret = INV_W2W7E2;if (modinv_good_disc(ret, D)) return ret;
  ret = INV_W5W7;  if (modinv_good_disc(ret, D)) return ret;
  ret = INV_W3W3E2;if (modinv_good_disc(ret, D)) return ret;
  ret = INV_G2;    if (modinv_good_disc(ret, D)) return ret;
  return INV_J;
}

INLINE long
modinv_sparse_factor(long inv)
{
  switch (inv) {
  case INV_G2:
  case INV_F8:
  case INV_W3W5:
  case INV_W2W5E2:
  case INV_W3W3E2:
    return 3;
  case INV_F:
    return 24;
  case INV_F2:
  case INV_W2W3:
    return 12;
  case INV_F3:
    return 8;
  case INV_F4:
  case INV_W2W3E2:
  case INV_W2W5:
  case INV_W3W3:
    return 6;
  case INV_W2W7:
    return 4;
  case INV_W2W7E2:
  case INV_W2W13:
  case INV_W3W7:
    return 2;
  }
  return 1;
}

#define IQ_FILTER_1MOD3 1
#define IQ_FILTER_2MOD3 2
#define IQ_FILTER_1MOD4 4
#define IQ_FILTER_3MOD4 8

INLINE long
modinv_pfilter(long inv)
{
  switch (inv) {
  case INV_G2:
  case INV_W3W3:
  case INV_W3W3E2:
  case INV_W3W5:
  case INV_W2W5:
  case INV_W2W3E2:
  case INV_W2W5E2:
  case INV_W5W7:
  case INV_W3W13:
    return IQ_FILTER_1MOD3; /* ensure unique cube roots */
  case INV_W2W7:
  case INV_F3:
    return IQ_FILTER_1MOD4; /* ensure at most two 4th/8th roots */
  case INV_F:
  case INV_F2:
  case INV_F4:
  case INV_F8:
  case INV_W2W3:
    /* Ensure unique cube roots and at most two 4th/8th roots */
    return IQ_FILTER_1MOD3 | IQ_FILTER_1MOD4;
  }
  return 0;
}

int
modinv_good_prime(long inv, long p)
{
  switch (inv) {
  case INV_G2:
  case INV_W2W3E2:
  case INV_W3W3:
  case INV_W3W3E2:
  case INV_W3W5:
  case INV_W2W5E2:
  case INV_W2W5:
    return (p % 3) == 2;
  case INV_W2W7:
  case INV_F3:
    return (p & 3) != 1;
  case INV_F2:
  case INV_F4:
  case INV_F8:
  case INV_F:
  case INV_W2W3:
    return ((p % 3) == 2) && (p & 3) != 1;
  }
  return 1;
}

/* Returns true if the prime p does not divide the conductor of D */
INLINE int
prime_to_conductor(long D, long p)
{
  long b;
  if (p > 2) return (D % (p * p));
  b = D & 0xF;
  return (b && b != 4); /* 2 divides the conductor of D <=> D=0,4 mod 16 */
}

INLINE GEN
red_primeform(long D, long p)
{
  pari_sp av = avma;
  GEN P;
  if (!prime_to_conductor(D, p)) return NULL;
  P = primeform_u(stoi(D), p); /* primitive since p \nmid conductor */
  return gerepileupto(av, redimag(P));
}

/* Computes product of primeforms over primes appearing in the prime
 * factorization of n (including multiplicity) */
GEN
qfb_nform(long D, long n)
{
  pari_sp av = avma;
  GEN N = NULL, fa = factoru(n), P = gel(fa,1), E = gel(fa,2);
  long i, l = lg(P);

  for (i = 1; i < l; ++i)
  {
    long j, e;
    GEN Q = red_primeform(D, P[i]);
    if (!Q) { avma = av; return NULL; }
    e = E[i];
    if (i == 1) { N = Q; j = 1; } else j = 0;
    for (; j < e; ++j) N = qficomp(Q, N);
  }
  return gerepileupto(av, N);
}

INLINE int
qfb_is_two_torsion(GEN x)
{
  return equali1(gel(x,1)) || !signe(gel(x,2))
    || equalii(gel(x,1), gel(x,2)) || equalii(gel(x,1), gel(x,3));
}

/* Returns true iff the products p1*p2, p1*p2^-1, p1^-1*p2, and
 * p1^-1*p2^-1 are all distinct in cl(D) */
INLINE int
qfb_distinct_prods(long D, long p1, long p2)
{
  GEN P1, P2;

  P1 = red_primeform(D, p1);
  if (!P1) return 0;
  P1 = qfisqr(P1);

  P2 = red_primeform(D, p2);
  if (!P2) return 0;
  P2 = qfisqr(P2);

  return !(equalii(gel(P1,1), gel(P2,1)) && absequalii(gel(P1,2), gel(P2,2)));
}

/* By Corollary 3.1 of Enge-Schertz Constructing elliptic curves over finite
 * fields using double eta-quotients, we need p1 != p2 to both be non-inert
 * and prime to the conductor, and if p1=p2=p we want p split and prime to the
 * conductor. We exclude the case that p1=p2 divides the conductor, even
 * though this does yield class invariants */
INLINE int
modinv_double_eta_good_disc(long D, long inv)
{
  pari_sp av = avma;
  GEN P;
  long i1, i2, p1, p2, N;

  N = modinv_degree(&p1, &p2, inv);
  if (! N) return 0;
  i1 = kross(D, p1);
  if (i1 < 0) return 0;
  /* Exclude ramified case for w_{p,p} */
  if (p1 == p2 && !i1) return 0;
  i2 = kross(D, p2);
  if (i2 < 0) return 0;
  /* this also verifies that p1 is prime to the conductor */
  P = red_primeform(D, p1);
  if (!P || gequal1(gel(P,1)) /* don't allow p1 to be principal */
      /* if p1 is unramified, require it to have order > 2 */
      || (i1 && qfb_is_two_torsion(P))) { avma = av; return 0; }
  if (p1 == p2)
  { /* if p1=p2 we need p1*p1 to be distinct from its inverse */
    int ok = ! qfb_is_two_torsion(qfisqr(P));
    avma = av; return ok;
  }
  /* this also verifies that p2 is prime to the conductor */
  P = red_primeform(D, p2);
  if (!P || gequal1(gel(P,1)) /* don't allow p2 to be principal */
      /* if p2 is unramified, require it to have order > 2 */
      || (i2 && qfb_is_two_torsion(P))) { avma = av; return 0; }
  avma = av;

  /* if p1 and p2 are split, we also require p1*p2, p1*p2^-1, p1^-1*p2,
   * and p1^-1*p2^-1 to be distinct */
  if (i1>0 && i2>0 && !qfb_distinct_prods(D, p1, p2)) { avma = av; return 0; }
  if (!i1 && !i2) {
    /* if both p1 and p2 are ramified, make sure their product is not
     * principal */
    P = qfb_nform(D, N);
    if (equali1(gel(P,1))) { avma = av; return 0; }
    avma = av;
  }
  return 1;
}

/* Assumes D is a good discriminant for inv, which implies that the
 * level is prime to the conductor */
long
modinv_ramified(long D, long inv)
{
  long p1, p2, N = modinv_degree(&p1, &p2, inv);
  if (N <= 1) return 0;
  return !(D % p1) && !(D % p2);
}

int
modinv_good_disc(long inv, long D)
{
  switch (inv) {
  case INV_J:
    return 1;
  case INV_G2:
    return !!(D % 3);
  case INV_F3:
    return (-D & 7) == 7;
  case INV_F:
  case INV_F2:
  case INV_F4:
  case INV_F8:
    return ((-D & 7) == 7) && (D % 3);
  case INV_W3W5:
    return (D % 3) && modinv_double_eta_good_disc(D, inv);
  case INV_W3W3E2:
    return (D % 3) && modinv_double_eta_good_disc(D, inv);
  case INV_W3W3:
    return (D & 1) && (D % 3) && modinv_double_eta_good_disc(D, inv);
  case INV_W2W3E2:
    return (D % 3) && modinv_double_eta_good_disc(D, inv);
  case INV_W2W3:
    return ((-D & 7) == 7) && (D % 3) && modinv_double_eta_good_disc(D, inv);
  case INV_W2W5:
    return ((-D % 80) != 20) && (D % 3) && modinv_double_eta_good_disc(D, inv);
  case INV_W2W5E2:
    return (D % 3) && modinv_double_eta_good_disc(D, inv);
  case INV_W2W7E2:
    return ((-D % 112) != 84) && modinv_double_eta_good_disc(D, inv);
  case INV_W2W7:
    return ((-D & 7) == 7) && modinv_double_eta_good_disc(D, inv);
  case INV_W2W13:
    return ((-D % 208) != 52) && modinv_double_eta_good_disc(D, inv);
  case INV_W3W7:
    return (D & 1) && (-D % 21) && modinv_double_eta_good_disc(D, inv);
  case INV_W5W7: /* NB: This is a guess; avs doesn't have an entry */
    return (D % 3) && modinv_double_eta_good_disc(D, inv);
  case INV_W3W13: /* NB: This is a guess; avs doesn't have an entry */
    return (D & 1) && (D % 3) && modinv_double_eta_good_disc(D, inv);
  }
  pari_err_BUG("modinv_good_discriminant");
  return 0;/*LCOV_EXCL_LINE*/
}

int
modinv_is_Weber(long inv)
{
  return inv == INV_F || inv == INV_F2 || inv == INV_F3 || inv == INV_F4
    || inv == INV_F8;
}

int
modinv_is_double_eta(long inv)
{
  switch (inv) {
  case INV_W2W3:
  case INV_W2W3E2:
  case INV_W2W5:
  case INV_W2W5E2:
  case INV_W2W7:
  case INV_W2W7E2:
  case INV_W2W13:
  case INV_W3W3:
  case INV_W3W3E2:
  case INV_W3W5:
  case INV_W3W7:
  case INV_W5W7:
  case INV_W3W13:
    return 1;
  }
  return 0;
}

/* END Code from "class_inv.h" */

INLINE int
safe_abs_sqrt(ulong *r, ulong x, ulong p, ulong pi, ulong s2)
{
  if (krouu(x, p) == -1)
  {
    if (p%4 == 1) return 0;
    x = Fl_neg(x, p);
  }
  *r = Fl_sqrt_pre_i(x, s2, p, pi);
  return 1;
}

INLINE int
eighth_root(ulong *r, ulong x, ulong p, ulong pi, ulong s2)
{
  ulong s;
  if (krouu(x, p) == -1) return 0;
  s = Fl_sqrt_pre_i(x, s2, p, pi);
  return safe_abs_sqrt(&s, s, p, pi, s2) && safe_abs_sqrt(r, s, p, pi, s2);
}

INLINE ulong
modinv_f_from_j(ulong j, ulong p, ulong pi, ulong s2, long only_residue)
{
  pari_sp av = avma;
  GEN pol, r;
  long i;
  ulong g2, f = ULONG_MAX;

  /* f^8 must be a root of X^3 - \gamma_2 X - 16 */
  g2 = Fl_sqrtl_pre(j, 3, p, pi);

  pol = mkvecsmall5(0UL, Fl_neg(16 % p, p), Fl_neg(g2, p), 0UL, 1UL);
  r = Flx_roots(pol, p);
  for (i = 1; i < lg(r); ++i)
    if (only_residue) { if (krouu(r[i], p) != -1) { avma = av; return r[i]; } }
    else if (eighth_root(&f, r[i], p, pi, s2)) { avma = av; return f; }
  pari_err_BUG("modinv_f_from_j");
  return 0;/*LCOV_EXCL_LINE*/
}

INLINE ulong
modinv_f3_from_j(ulong j, ulong p, ulong pi, ulong s2)
{
  pari_sp av = avma;
  GEN pol, r;
  long i;
  ulong f = ULONG_MAX;

  pol = mkvecsmall5(0UL,
      Fl_neg(4096 % p, p), Fl_sub(768 % p, j, p), Fl_neg(48 % p, p), 1UL);
  r = Flx_roots(pol, p);
  for (i = 1; i < lg(r); ++i)
    if (eighth_root(&f, r[i], p, pi, s2)) { avma = av; return f; }
  pari_err_BUG("modinv_f3_from_j");
  return 0;/*LCOV_EXCL_LINE*/
}

/* Return the exponent e for the double-eta "invariant" w such that
 * w^e is a class invariant.  For example w2w3^12 is a class
 * invariant, so double_eta_exponent(INV_W2W3) is 12 and
 * double_eta_exponent(INV_W2W3E2) is 6. */
INLINE ulong
double_eta_exponent(long inv)
{
  switch (inv) {
  case INV_W2W3:
    return 12;
  case INV_W2W3E2:
  case INV_W2W5:
  case INV_W3W3:
    return 6;
  case INV_W2W7:
    return 4;
  case INV_W3W5:
  case INV_W2W5E2:
  case INV_W3W3E2:
    return 3;
  case INV_W2W7E2:
  case INV_W2W13:
  case INV_W3W7:
    return 2;
  default:
    return 1;
  }
}

INLINE ulong
weber_exponent(long inv)
{
  switch (inv)
  {
  case INV_F:  return 24;
  case INV_F2: return 12;
  case INV_F3: return 8;
  case INV_F4: return 6;
  case INV_F8: return 3;
  default:     return 1;
  }
}

INLINE ulong
double_eta_power(long inv, ulong w, ulong p, ulong pi)
{
  return Fl_powu_pre(w, double_eta_exponent(inv), p, pi);
}

static GEN
double_eta_raw_to_Fp(GEN f, GEN p)
{
  GEN u = FpX_red(RgV_to_RgX(gel(f,1), 0), p);
  GEN v = FpX_red(RgV_to_RgX(gel(f,2), 0), p);
  return mkvec3(u, v, gel(f,3));
}

/* Given a root x of polclass(D, inv) modulo N, returns a root of polclass(D,0)
 * modulo N by plugging x to a modular polynomial. For double-eta quotients,
 * this is done by plugging x into the modular polynomial Phi(INV_WpWq, j)
 * Enge, Morain 2013: Generalised Weber Functions. */
GEN
Fp_modinv_to_j(GEN x, long inv, GEN p)
{
  switch(inv)
  {
    case INV_J: return Fp_red(x, p);
    case INV_G2: return Fp_powu(x, 3, p);
    case INV_F: case INV_F2: case INV_F3: case INV_F4: case INV_F8:
    {
      GEN xe = Fp_powu(x, weber_exponent(inv), p);
      return Fp_div(Fp_powu(subiu(xe, 16), 3, p), xe, p);
    }
    default:
    if (modinv_is_double_eta(inv))
    {
      GEN xe = Fp_powu(x, double_eta_exponent(inv), p);
      GEN uvk = double_eta_raw_to_Fp(double_eta_raw(inv), p);
      GEN J0 = FpX_eval(gel(uvk,1), xe, p);
      GEN J1 = FpX_eval(gel(uvk,2), xe, p);
      GEN J2 = Fp_pow(xe, gel(uvk,3), p);
      GEN phi = mkvec3(J0, J1, J2);
      return FpX_oneroot(RgX_to_FpX(RgV_to_RgX(phi,1), p),p);
    }
    pari_err_BUG("Fp_modinv_to_j"); return NULL;/* LCOV_EXCL_LINE */
  }
}

/* Assuming p = 2 (mod 3) and p = 3 (mod 4): if the two 12th roots of
 * x (mod p) exist, set *r to one of them and return 1, otherwise
 * return 0 (without touching *r). */
INLINE int
twelth_root(ulong *r, ulong x, ulong p, ulong pi, ulong s2)
{
  register ulong t;

  t = Fl_sqrtl_pre(x, 3, p, pi);
  if (krouu(t, p) == -1)
    return 0;
  t = Fl_sqrt_pre_i(t, s2, p, pi);
  return safe_abs_sqrt(r, t, p, pi, s2);
}

INLINE int
sixth_root(ulong *r, ulong x, ulong p, ulong pi, ulong s2)
{
  register ulong t;

  t = Fl_sqrtl_pre(x, 3, p, pi);
  if (krouu(t, p) == -1)
    return 0;
  *r = Fl_sqrt_pre_i(t, s2, p, pi);
  return 1;
}

INLINE int
fourth_root(ulong *r, ulong x, ulong p, ulong pi, ulong s2)
{
  register ulong s;
  if (krouu(x, p) == -1)
    return 0;
  s = Fl_sqrt_pre_i(x, s2, p, pi);
  return safe_abs_sqrt(r, s, p, pi, s2);
}

INLINE int
double_eta_root(long inv, ulong *r, ulong w, ulong p, ulong pi, ulong s2)
{
  switch (double_eta_exponent(inv)) {
  case 12: return twelth_root(r, w, p, pi, s2);
  case 6: return sixth_root(r, w, p, pi, s2);
  case 4: return fourth_root(r, w, p, pi, s2);
  case 3: *r = Fl_sqrtl_pre(w, 3, p, pi); return 1;
  case 2: return krouu(w, p) != -1 && !!(*r = Fl_sqrt_pre_i(w, s2, p, pi));
  case 1: *r = w; return 1;
  }
  pari_err_BUG("double_eta_root"); return 0;/*LCOV_EXCL_LINE*/
}

/* F = double_eta_Fl(inv, p) */
static GEN
Flx_double_eta_xpoly(GEN F, ulong j, ulong p, ulong pi)
{
  GEN u = gel(F,1), v = gel(F,2), w;
  long i, k = itos(gel(F,3)), lu = lg(u), lv = lg(v), lw = lu + 1;

  w = cgetg(lw, t_VECSMALL); /* lu >= max(lv,k) */
  w[1] = 0; /* variable number */
  for (i = 1; i < lv; i++)
    uel(w, i + 1) = Fl_add(uel(u, i), Fl_mul_pre(j, uel(v, i), p, pi), p);
  for (     ; i < lu; i++)
    uel(w, i + 1) = uel(u, i);
  uel(w, k + 2) = Fl_add(uel(w, k + 2), Fl_sqr_pre(j, p, pi), p);
  return Flx_renormalize(w, lw);
}

/* F = double_eta_Fl(inv, p) */
static GEN
Flx_double_eta_jpoly(GEN F, ulong x, ulong p, ulong pi)
{
  pari_sp av = avma;
  GEN u = gel(F,1), v = gel(F,2), xs;
  long k = itos(gel(F,3));
  ulong a, b, c;

  /* u is always longest and the length is bigger than k */
  xs = Fl_powers_pre(x, lg(u) - 1, p, pi);
  c = Flv_dotproduct_pre(u, xs, p, pi);
  b = Flv_dotproduct_pre(v, xs, p, pi);
  a = uel(xs, k + 1);
  avma = av;
  return mkvecsmall4(0, c, b, a);
}

/* reduce F = double_eta_raw(inv) mod p */
static GEN
double_eta_raw_to_Fl(GEN f, ulong p)
{
  GEN u = ZV_to_Flv(gel(f,1), p);
  GEN v = ZV_to_Flv(gel(f,2), p);
  return mkvec3(u, v, gel(f,3));
}
/* double_eta_raw(inv) mod p */
static GEN
double_eta_Fl(long inv, ulong p)
{ return double_eta_raw_to_Fl(double_eta_raw(inv), p); }

/* Go through roots of Psi(X,j) until one has an double_eta_exponent(inv)-th
 * root, and return that root. F = double_eta_Fl(inv,p) */
INLINE ulong
modinv_double_eta_from_j(GEN F, long inv, ulong j, ulong p, ulong pi, ulong s2)
{
  pari_sp av = avma;
  long i;
  ulong f = ULONG_MAX;
  GEN a = Flx_double_eta_xpoly(F, j, p, pi);
  a = Flx_roots(a, p);
  for (i = 1; i < lg(a); ++i)
    if (double_eta_root(inv, &f, uel(a, i), p, pi, s2)) break;
  if (i == lg(a)) pari_err_BUG("modinv_double_eta_from_j");
  avma = av; return f;
}

/* assume j1 != j2 */
static long
modinv_double_eta_from_2j(
  ulong *r, long inv, ulong j1, ulong j2, ulong p, ulong pi, ulong s2)
{
  pari_sp av = avma;
  GEN f, g, d, F = double_eta_Fl(inv, p);

  f = Flx_double_eta_xpoly(F, j1, p, pi);
  g = Flx_double_eta_xpoly(F, j2, p, pi);
  d = Flx_gcd(f, g, p);
  /* NB: Morally the next conditional should be written as follows, but,
   * because of the case when j1 or j2 may not have the correct endomorphism
   * ring, we need to use the less strict conditional underneath */
#if 0
  if (degpol(d) != 1
      || (*r = Flx_oneroot(d, p)) == p
      || ! double_eta_root(inv, r, *r, p, pi, s2))
    pari_err_BUG("modinv_double_eta_from_2j");
#endif
  if (degpol(d) > 2
      || (*r = Flx_oneroot(d, p)) == p
      || ! double_eta_root(inv, r, *r, p, pi, s2)) return 0;
  avma = av; return 1;
}

long
modfn_unambiguous_root(ulong *r, long inv, ulong j0, norm_eqn_t ne, GEN jdb)
{
  pari_sp av = avma;
  long p1, p2, v = ne->v, p1_depth;
  ulong j1, p = ne->p, pi = ne->pi, s2 = ne->s2;
  GEN phi;

  (void) modinv_degree(&p1, &p2, inv);
  p1_depth = u_lval(v, p1);

  phi = polmodular_db_getp(jdb, p1, p);
  if (!next_surface_nbr(&j1, phi, p1, p1_depth, j0, NULL, p, pi))
    pari_err_BUG("modfn_unambiguous_root");
  if (p2 == p1) {
    if (!next_surface_nbr(&j1, phi, p1, p1_depth, j1, &j0, p, pi))
      pari_err_BUG("modfn_unambiguous_root");
  } else {
    long p2_depth = u_lval(v, p2);
    phi = polmodular_db_getp(jdb, p2, p);
    if (!next_surface_nbr(&j1, phi, p2, p2_depth, j1, NULL, p, pi))
      pari_err_BUG("modfn_unambiguous_root");
  }
  avma = av;
  return j1 != j0 && modinv_double_eta_from_2j(r, inv, j0, j1, p, pi, s2);
}

ulong
modfn_root(ulong j, norm_eqn_t ne, long inv)
{
  ulong f, p = ne->p, pi = ne->pi, s2 = ne->s2;
  switch (inv) {
    case INV_J:  return j;
    case INV_G2: return Fl_sqrtl_pre(j, 3, p, pi);
    case INV_F:  return modinv_f_from_j(j, p, pi, s2, 0);
    case INV_F2:
      f = modinv_f_from_j(j, p, pi, s2, 0);
      return Fl_sqr_pre(f, p, pi);
    case INV_F3: return modinv_f3_from_j(j, p, pi, s2);
    case INV_F4:
      f = modinv_f_from_j(j, p, pi, s2, 0);
      return Fl_sqr_pre(Fl_sqr_pre(f, p, pi), p, pi);
    case INV_F8: return modinv_f_from_j(j, p, pi, s2, 1);
  }
  if (modinv_is_double_eta(inv))
  {
    pari_sp av = avma;
    ulong f = modinv_double_eta_from_j(double_eta_Fl(inv,p), inv, j, p, pi, s2);
    avma = av; return f;
  }
  pari_err_BUG("modfn_root"); return ULONG_MAX;/*LCOV_EXCL_LINE*/
}

INLINE ulong
modinv_j_from_f(ulong x, ulong n, ulong p, ulong pi)
{ /* If x satisfies (X^24 - 16)^3 - X^24 * j = 0
   * then j = (x^24 - 16)^3 / x^24 */
  ulong x24 = Fl_powu_pre(x, 24 / n, p, pi);
  return Fl_div(Fl_powu_pre(Fl_sub(x24, 16 % p, p), 3, p, pi), x24, p);
}

/* TODO: Check whether I can use this to refactor something
 * F = double_eta_raw(inv) */
long
modinv_j_from_2double_eta(
  GEN F, long inv, ulong *j, ulong x0, ulong x1, ulong p, ulong pi)
{
  GEN f, g, d;

  x0 = double_eta_power(inv, x0, p, pi);
  x1 = double_eta_power(inv, x1, p, pi);
  F = double_eta_raw_to_Fl(F, p);
  f = Flx_double_eta_jpoly(F, x0, p, pi);
  g = Flx_double_eta_jpoly(F, x1, p, pi);
  d = Flx_gcd(f, g, p);
  if (degpol(d) > 1)
    pari_err_BUG("modinv_j_from_2double_eta");
  else if (degpol(d) < 1)
    return 0;
  if (j) *j = Flx_deg1_root(d, p);
  return 1;
}

INLINE ulong
modfn_preimage(ulong x, norm_eqn_t ne, long inv)
{
  ulong p = ne->p, pi = ne->pi;
  switch (inv) {
    case INV_J:  return x;
    case INV_G2: return Fl_powu_pre(x, 3, p, pi);
    /* NB: could replace these with a single call modinv_j_from_f(x,inv,p,pi)
     * but avoid the dependence on the actual value of inv */
    case INV_F:  return modinv_j_from_f(x, 1, p, pi);
    case INV_F2: return modinv_j_from_f(x, 2, p, pi);
    case INV_F3: return modinv_j_from_f(x, 3, p, pi);
    case INV_F4: return modinv_j_from_f(x, 4, p, pi);
    case INV_F8: return modinv_j_from_f(x, 8, p, pi);
  }
  /* NB: This function should never be called if modinv_double_eta(inv) is
   * true */
  pari_err_BUG("modfn_preimage"); return ULONG_MAX;/*LCOV_EXCL_LINE*/
}

/**
 * SECTION: class group bb_group.
 */

INLINE GEN
mkqfis(long a, long b, long c)
{
  retmkqfi(stoi(a), stoi(b), stoi(c));
}

/**
 * SECTION: Fixed-length dot-product-like functions on Fl's with
 * precomputed inverse.
 */

/* Computes x0y1 + y0x1 (mod p); assumes p < 2^63. */
INLINE ulong
Fl_addmul2(
  ulong x0, ulong x1, ulong y0, ulong y1,
  ulong p, ulong pi)
{
  return Fl_addmulmul_pre(x0,y1,y0,x1,p,pi);
}

/* Computes x0y2 + x1y1 + x2y0 (mod p); assumes p < 2^62. */
INLINE ulong
Fl_addmul3(
  ulong x0, ulong x1, ulong x2, ulong y0, ulong y1, ulong y2,
  ulong p, ulong pi)
{
  ulong l0, l1, h0, h1;
  LOCAL_OVERFLOW;
  LOCAL_HIREMAINDER;
  l0 = mulll(x0, y2); h0 = hiremainder;
  l1 = mulll(x1, y1); h1 = hiremainder;
  l1 = addll(l0, l1); h1 = addllx(h0, h1);
  l0 = mulll(x2, y0); h0 = hiremainder;
  l1 = addll(l0, l1); h1 = addllx(h0, h1);
  return remll_pre(h1, l1, p, pi);
}

/* Computes x0y3 + x1y2 + x2y1 + x3y0 (mod p); assumes p < 2^62. */
INLINE ulong
Fl_addmul4(
  ulong x0, ulong x1, ulong x2, ulong x3,
  ulong y0, ulong y1, ulong y2, ulong y3,
  ulong p, ulong pi)
{
  ulong l0, l1, h0, h1;
  LOCAL_OVERFLOW;
  LOCAL_HIREMAINDER;
  l0 = mulll(x0, y3); h0 = hiremainder;
  l1 = mulll(x1, y2); h1 = hiremainder;
  l1 = addll(l0, l1); h1 = addllx(h0, h1);
  l0 = mulll(x2, y1); h0 = hiremainder;
  l1 = addll(l0, l1); h1 = addllx(h0, h1);
  l0 = mulll(x3, y0); h0 = hiremainder;
  l1 = addll(l0, l1); h1 = addllx(h0, h1);
  return remll_pre(h1, l1, p, pi);
}

/* Computes x0y4 + x1y3 + x2y2 + x3y1 + x4y0 (mod p); assumes p < 2^62. */
INLINE ulong
Fl_addmul5(
  ulong x0, ulong x1, ulong x2, ulong x3, ulong x4,
  ulong y0, ulong y1, ulong y2, ulong y3, ulong y4,
  ulong p, ulong pi)
{
  ulong l0, l1, h0, h1;
  LOCAL_OVERFLOW;
  LOCAL_HIREMAINDER;
  l0 = mulll(x0, y4); h0 = hiremainder;
  l1 = mulll(x1, y3); h1 = hiremainder;
  l1 = addll(l0, l1); h1 = addllx(h0, h1);
  l0 = mulll(x2, y2); h0 = hiremainder;
  l1 = addll(l0, l1); h1 = addllx(h0, h1);
  l0 = mulll(x3, y1); h0 = hiremainder;
  l1 = addll(l0, l1); h1 = addllx(h0, h1);
  l0 = mulll(x4, y0); h0 = hiremainder;
  l1 = addll(l0, l1); h1 = addllx(h0, h1);
  return remll_pre(h1, l1, p, pi);
}

/* A polmodular database for a given class invariant consists of a t_VEC whose
 * L-th entry is 0 or a GEN pointing to Phi_L.  This function produces a pair
 * of databases corresponding to the j-invariant and inv */
GEN
polmodular_db_init(long inv)
{
  GEN res, jdb, fdb;
  enum { DEFAULT_MODPOL_DB_LEN = 32 };

  res = cgetg_block(2 + 1, t_VEC);
  jdb = zerovec_block(DEFAULT_MODPOL_DB_LEN);
  gel(res, 1) = jdb;
  if (inv != INV_J) {
    fdb = zerovec_block(DEFAULT_MODPOL_DB_LEN);
    gel(res, 2) = fdb;
  } else {
    gel(res, 2) = gen_0;
  }
  return res;
}

void
polmodular_db_add_level(GEN *DB, long L, long inv)
{
  long max_L;
  GEN db;

  if (inv == INV_J) {
    db = gel(*DB, 1);
  } else {
    db = gel(*DB, 2);
    if ( isintzero(db)) pari_err_BUG("polmodular_db_add_level");
  }

  max_L = lg(db) - 1;
  if (L > max_L) {
    GEN newdb;
    long i, newlen = 2 * L;

    newdb = cgetg_block(newlen + 1, t_VEC);
    for (i = 1; i <= max_L; ++i) gel(newdb, i) = gel(db, i);
    for (     ; i <= newlen; ++i) gel(newdb, i) = gen_0;
    killblock(db);
    gel(*DB, (inv == INV_J)? 1: 2) = db = newdb;
  }
  if (typ(gel(db, L)) == t_INT) {
    pari_sp av = avma;
    GEN x = polmodular0_ZM(L, inv, NULL, NULL, 0, DB); /* may set db[L] */
    GEN y = gel(db, L);
    gel(db, L) = gclone(x);
    if (typ(y) != t_INT) gunclone(y);
    avma = av;
  }
}

void
polmodular_db_add_levels(GEN *db, long *levels, long k, long inv)
{
  long i;
  for (i = 0; i < k; ++i) polmodular_db_add_level(db, levels[i], inv);
}

GEN
polmodular_db_for_inv(GEN db, long inv)
{ return (inv == INV_J)? gel(db,1): gel(db,2); }

/* TODO: Also cache modpoly mod p for most recent p (avoid repeated
 * reductions in, for example, polclass.c:oneroot_of_classpoly(). */
GEN
polmodular_db_getp(GEN db, long L, ulong p)
{
  GEN f = gel(db, L);
  if (isintzero(f)) pari_err_BUG("polmodular_db_getp");
  return ZM_to_Flm(f, p);
}

/**
 * SECTION: Table of discriminants to use.
 */
typedef struct {
  long GENcode0;  /* used when serializing the struct to a t_VECSMALL */
  long inv;      /* invariant */
  long L;        /* modpoly level */
  long D0;       /* fundamental discriminant */
  long D1;       /* chosen discriminant */
  long L0;       /* first generator norm */
  long L1;       /* second generator norm */
  long n1;       /* order of L0 in cl(D1) */
  long n2;       /* order of L0 in cl(D2) where D2 = L^2 D1 */
  long dl1;      /* m such that L0^m = L in cl(D1) */
  long dl2_0;    /* These two are (m, n) such that L0^m L1^n = form of norm L^2 in D2 */
  long dl2_1;    /* This n is always 1 or 0. */
  /* this part is not serialized */
  long nprimes;  /* number of primes needed for D1 */
  long cost;     /* cost to enumerate  subgroup of cl(L^2D): subgroup size is n2 if L1=0, 2*n2 o.w. */
  long bits;
  ulong *primes;
  ulong *traces;
} disc_info;

#define MODPOLY_MAX_DCNT    64

/* Flag for last parameter of discriminant_with_classno_at_least.
 * Warning: ignoring the sparse factor makes everything slower by
 * something like (sparse factor)^3. */
#define USE_SPARSE_FACTOR 0
#define IGNORE_SPARSE_FACTOR 1

static long
discriminant_with_classno_at_least(disc_info Ds[MODPOLY_MAX_DCNT], long L,
  long inv, long ignore_sparse);

/**
 * SECTION: Hard-coded evaluation functions for modular polynomials of
 * small level.
 */

/* Based on phi2_eval_ff() in Sutherland's classpoly programme.
 * Calculates Phi_2(X, j) (mod p) with 6M+7A (4 reductions, not
 * counting those for Phi_2) */
INLINE GEN
Flm_Fl_phi2_evalx(GEN phi2, ulong j, ulong p, ulong pi)
{
  GEN res = cgetg(6, t_VECSMALL);
  ulong j2, t1;

  res[1] = 0; /* variable name */

  j2 = Fl_sqr_pre(j, p, pi);
  t1 = Fl_add(j, coeff(phi2, 3, 1), p);
  t1 = Fl_addmul2(j, j2, t1, coeff(phi2, 2, 1), p, pi);
  res[2] = Fl_add(t1, coeff(phi2, 1, 1), p);

  t1 = Fl_addmul2(j, j2, coeff(phi2, 3, 2), coeff(phi2, 2, 2), p, pi);
  res[3] = Fl_add(t1, coeff(phi2, 2, 1), p);

  t1 = Fl_mul_pre(j, coeff(phi2, 3, 2), p, pi);
  t1 = Fl_add(t1, coeff(phi2, 3, 1), p);
  res[4] = Fl_sub(t1, j2, p);

  res[5] = 1;
  return res;
}

/* Based on phi3_eval_ff() in Sutherland's classpoly programme.
 * Calculates Phi_3(X, j) (mod p) with 13M+13A (6 reductions, not
 * counting those for Phi_3) */
INLINE GEN
Flm_Fl_phi3_evalx(GEN phi3, ulong j, ulong p, ulong pi)
{
  GEN res = cgetg(7, t_VECSMALL);
  ulong j2, j3, t1;

  res[1] = 0; /* variable name */

  j2 = Fl_sqr_pre(j, p, pi);
  j3 = Fl_mul_pre(j, j2, p, pi);

  t1 = Fl_add(j, coeff(phi3, 4, 1), p);
  res[2] = Fl_addmul3(j, j2, j3, t1,
                      coeff(phi3, 3, 1), coeff(phi3, 2, 1), p, pi);

  t1 = Fl_addmul3(j, j2, j3, coeff(phi3, 4, 2),
                  coeff(phi3, 3, 2), coeff(phi3, 2, 2), p, pi);
  res[3] = Fl_add(t1, coeff(phi3, 2, 1), p);

  t1 = Fl_addmul3(j, j2, j3, coeff(phi3, 4, 3),
                  coeff(phi3, 3, 3), coeff(phi3, 3, 2), p, pi);
  res[4] = Fl_add(t1, coeff(phi3, 3, 1), p);

  t1 = Fl_addmul2(j, j2, coeff(phi3, 4, 3), coeff(phi3, 4, 2), p, pi);
  t1 = Fl_add(t1, coeff(phi3, 4, 1), p);
  res[5] = Fl_sub(t1, j3, p);

  res[6] = 1;
  return res;
}

/* Based on phi5_eval_ff() in Sutherland's classpoly programme.
 * Calculates Phi_5(X, j) (mod p) with 33M+31A (10 reductions, not
 * counting those for Phi_5) */
INLINE GEN
Flm_Fl_phi5_evalx(GEN phi5, ulong j, ulong p, ulong pi)
{
  GEN res = cgetg(9, t_VECSMALL);
  ulong j2, j3, j4, j5, t1;

  res[1] = 0; /* variable name */

  j2 = Fl_sqr_pre(j, p, pi);
  j3 = Fl_mul_pre(j, j2, p, pi);
  j4 = Fl_sqr_pre(j2, p, pi);
  j5 = Fl_mul_pre(j, j4, p, pi);

  t1 = Fl_add(j, coeff(phi5, 6, 1), p);
  t1 = Fl_addmul5(j, j2, j3, j4, j5, t1,
                  coeff(phi5, 5, 1), coeff(phi5, 4, 1),
                  coeff(phi5, 3, 1), coeff(phi5, 2, 1),
                  p, pi);
  res[2] = Fl_add(t1, coeff(phi5, 1, 1), p);

  t1 = Fl_addmul5(j, j2, j3, j4, j5,
                  coeff(phi5, 6, 2), coeff(phi5, 5, 2),
                  coeff(phi5, 4, 2), coeff(phi5, 3, 2), coeff(phi5, 2, 2),
                  p, pi);
  res[3] = Fl_add(t1, coeff(phi5, 2, 1), p);

  t1 = Fl_addmul5(j, j2, j3, j4, j5,
                  coeff(phi5, 6, 3), coeff(phi5, 5, 3),
                  coeff(phi5, 4, 3), coeff(phi5, 3, 3), coeff(phi5, 3, 2),
                  p, pi);
  res[4] = Fl_add(t1, coeff(phi5, 3, 1), p);

  t1 = Fl_addmul5(j, j2, j3, j4, j5,
                  coeff(phi5, 6, 4), coeff(phi5, 5, 4),
                  coeff(phi5, 4, 4), coeff(phi5, 4, 3), coeff(phi5, 4, 2),
                  p, pi);
  res[5] = Fl_add(t1, coeff(phi5, 4, 1), p);

  t1 = Fl_addmul5(j, j2, j3, j4, j5,
                  coeff(phi5, 6, 5), coeff(phi5, 5, 5),
                  coeff(phi5, 5, 4), coeff(phi5, 5, 3), coeff(phi5, 5, 2),
                  p, pi);
  res[6] = Fl_add(t1, coeff(phi5, 5, 1), p);

  t1 = Fl_addmul4(j, j2, j3, j4,
                  coeff(phi5, 6, 5), coeff(phi5, 6, 4),
                  coeff(phi5, 6, 3), coeff(phi5, 6, 2),
                  p, pi);
  t1 = Fl_add(t1, coeff(phi5, 6, 1), p);
  res[7] = Fl_sub(t1, j5, p);

  res[8] = 1;
  return res;
}

GEN
Flm_Fl_polmodular_evalx(GEN phi, long L, ulong j, ulong p, ulong pi)
{
  switch (L) {
    case 2: return Flm_Fl_phi2_evalx(phi, j, p, pi);
    case 3: return Flm_Fl_phi3_evalx(phi, j, p, pi);
    case 5: return Flm_Fl_phi5_evalx(phi, j, p, pi);
    default: { /* not GC clean, but gerepileupto-safe */
      GEN j_powers = Fl_powers_pre(j, L + 1, p, pi);
      return Flm_Flc_mul_pre_Flx(phi, j_powers, p, pi, 0);
    }
  }
}

/**
 * SECTION: Velu's formula for the codmain curve in the case of small
 * prime base field.
 */

INLINE ulong
Fl_mul4(ulong x, ulong p)
{ return Fl_double(Fl_double(x, p), p); }

INLINE ulong
Fl_mul5(ulong x, ulong p)
{ return Fl_add(x, Fl_mul4(x, p), p); }

INLINE ulong
Fl_mul8(ulong x, ulong p)
{ return Fl_double(Fl_mul4(x, p), p); }

INLINE ulong
Fl_mul6(ulong x, ulong p)
{ return Fl_sub(Fl_mul8(x, p), Fl_double(x, p), p); }

INLINE ulong
Fl_mul7(ulong x, ulong p)
{ return Fl_sub(Fl_mul8(x, p), x, p); }

/* Given an elliptic curve E = [a4, a6] over F_p and a non-zero point
 * pt on E, return the quotient E' = E/<P> = [a4_img, a6_img] */
static void
Fle_quotient_from_kernel_generator(
  ulong *a4_img, ulong *a6_img, ulong a4, ulong a6, GEN pt, ulong p, ulong pi)
{
  pari_sp av = avma;
  ulong t = 0, w = 0;
  GEN Q;
  ulong xQ, yQ, tQ, uQ;

  Q = gcopy(pt);
  /* Note that, as L is odd, say L = 2n + 1, we necessarily have
   * [(L - 1)/2]P = [n]P = [n - L]P = -[n + 1]P = -[(L + 1)/2]P.  This is
   * what the condition Q[1] != xQ tests, so the loop will execute n times. */
  do {
    xQ = uel(Q, 1);
    yQ = uel(Q, 2);
    /* tQ = 6 xQ^2 + b2 xQ + b4
     *    = 6 xQ^2 + 2 a4 (since b2 = 0 and b4 = 2 a4) */
    tQ = Fl_add(Fl_mul6(Fl_sqr_pre(xQ, p, pi), p), Fl_double(a4, p), p);
    uQ = Fl_add(Fl_mul4(Fl_sqr_pre(yQ, p, pi), p),
                Fl_mul_pre(tQ, xQ, p, pi), p);

    t = Fl_add(t, tQ, p);
    w = Fl_add(w, uQ, p);
    Q = gerepileupto(av, Fle_add(pt, Q, a4, p));
  } while (uel(Q, 1) != xQ);

  avma = av;
  /* a4_img = a4 - 5 * t */
  *a4_img = Fl_sub(a4, Fl_mul5(t, p), p);
  /* a6_img = a6 - b2 * t - 7 * w = a6 - 7 * w (since a1 = a2 = 0 ==> b2 = 0) */
  *a6_img = Fl_sub(a6, Fl_mul7(w, p), p);
}

/**
 * SECTION: Calculation of modular polynomials.
 */

/* Given an elliptic curve [a4, a6] over FF_p, try to find a
 * non-trivial L-torsion point on the curve by considering n times a
 * random point; val controls the maximum L-valuation expected of n
 * times a random point */
static GEN
find_L_tors_point(
  ulong *ival,
  ulong a4, ulong a6, ulong p, ulong pi,
  ulong n, ulong L, ulong val)
{
  pari_sp av = avma;
  ulong i;
  GEN P, Q;
  do {
    Q = random_Flj_pre(a4, a6, p, pi);
    P = Flj_mulu_pre(Q, n, a4, p, pi);
  } while (P[3] == 0);

  for (i = 0; i < val; ++i) {
    Q = Flj_mulu_pre(P, L, a4, p, pi);
    if (Q[3] == 0) break;
    P = Q;
  }
  if (ival) *ival = i;
  return gerepilecopy(av, P);
}

static GEN
select_curve_with_L_tors_point(
  ulong *a4, ulong *a6,
  ulong L, ulong j, ulong n, ulong card, ulong val,
  norm_eqn_t ne)
{
  pari_sp av = avma;
  ulong A4, A4t, A6, A6t;
  ulong p = ne->p, pi = ne->pi;
  GEN P;
  if (card % L != 0) {
    pari_err_BUG("select_curve_with_L_tors_point: "
                 "Cardinality not divisible by L");
  }

  Fl_ellj_to_a4a6(j, p, &A4, &A6);
  Fl_elltwist_disc(A4, A6, ne->T, p, &A4t, &A6t);

  /* Either E = [a4, a6] or its twist has cardinality divisible by L
   * because of the choice of p and t earlier on.  We find out which
   * by attempting to find a point of order L on each.  See bot p16 of
   * Sutherland 2012. */
  while (1) {
    ulong i;
    P = find_L_tors_point(&i, A4, A6, p, pi, n, L, val);
    if (i < val)
      break;
    avma = av;
    lswap(A4, A4t);
    lswap(A6, A6t);
  }
  *a4 = A4;
  *a6 = A6; return gerepilecopy(av, P);
}

/* Return 1 if the L-Sylow subgroup of the curve [a4, a6] (mod p) is
 * cyclic, return 0 if it is not cyclic with "high" probability (I
 * guess around 1/L^3 chance it is still cyclic when we return 0).
 *
 * Based on Sutherland's velu.c:velu_verify_Sylow_cyclic() in classpoly-1.0.1 */
INLINE long
verify_L_sylow_is_cyclic(long e, ulong a4, ulong a6, ulong p, ulong pi)
{
  /* Number of times to try to find a point with maximal order in the
   * L-Sylow subgroup. */
  enum { N_RETRIES = 3 };
  pari_sp av = avma;
  long i, res = 0;
  GEN P;
  for (i = 0; i < N_RETRIES; ++i) {
    P = random_Flj_pre(a4, a6, p, pi);
    P = Flj_mulu_pre(P, e, a4, p, pi);
    if (P[3] != 0) { res = 1; break; }
  }
  avma = av; return res;
}

static ulong
find_noniso_L_isogenous_curve(
  ulong L, ulong n,
  norm_eqn_t ne, long e, ulong val, ulong a4, ulong a6, GEN init_pt, long verify)
{
  pari_sp ltop, av;
  ulong p = ne->p, pi = ne->pi, j_res = 0;
  GEN pt = init_pt;
  ltop = av = avma;
  while (1) {
    /* c. Use Velu to calculate L-isogenous curve E' = E/<P> */
    ulong a4_img, a6_img;
    ulong z2 = Fl_sqr_pre(pt[3], p, pi);
    pt = mkvecsmall2(Fl_div(pt[1], z2, p),
                     Fl_div(pt[2], Fl_mul_pre(z2, pt[3], p, pi), p));
    Fle_quotient_from_kernel_generator(&a4_img, &a6_img,
                                       a4, a6, pt, p, pi);

    /* d. If j(E') = j_res has a different endo ring to j(E), then
     *    return j(E').  Otherwise, go to b. */
    if (!verify || verify_L_sylow_is_cyclic(e, a4_img, a6_img, p, pi)) {
      j_res = Fl_ellj_pre(a4_img, a6_img, p, pi);
      break;
    }

    /* b. Generate random point P on E of order L */
    avma = av;
    pt = find_L_tors_point(NULL, a4, a6, p, pi, n, L, val);
  }
  avma = ltop; return j_res;
}

/* Given a prime L and a j-invariant j (mod p), return the j-invariant
 * of a curve which has a different endomorphism ring to j and is
 * L-isogenous to j */
INLINE ulong
compute_L_isogenous_curve(
  ulong L, ulong n, norm_eqn_t ne,
  ulong j, ulong card, ulong val, long verify)
{
  ulong a4, a6;
  long e;
  GEN pt;

  if (ne->p < 5 || j == 0 || j == 1728 % ne->p)
    pari_err_BUG("compute_L_isogenous_curve");
  pt = select_curve_with_L_tors_point(&a4, &a6, L, j, n, card, val, ne);
  e = card / L;
  if (e * L != card) pari_err_BUG("compute_L_isogenous_curve");

  return find_noniso_L_isogenous_curve(L, n, ne, e, val, a4, a6, pt, verify);
}

INLINE GEN
get_Lsqr_cycle(const disc_info *dinfo)
{
  long i, n1 = dinfo->n1, L = dinfo->L;
  GEN cyc = cgetg(L, t_VECSMALL);
  cyc[1] = 0;
  for (i = 2; i <= L / 2; ++i) cyc[i] = cyc[i - 1] + n1;
  if ( ! dinfo->L1) {
    for ( ; i < L; ++i) cyc[i] = cyc[i - 1] + n1;
  } else {
    cyc[L - 1] = 2 * dinfo->n2 - n1 / 2;
    for (i = L - 2; i > L / 2; --i) cyc[i] = cyc[i + 1] - n1;
  }
  return cyc;
}

INLINE void
update_Lsqr_cycle(GEN cyc, const disc_info *dinfo)
{
  long i, L = dinfo->L;
  for (i = 1; i < L; ++i) ++cyc[i];
  if (dinfo->L1 && cyc[L - 1] == 2 * dinfo->n2) {
    long n1 = dinfo->n1;
    for (i = L / 2 + 1; i < L; ++i) cyc[i] -= n1;
  }
}

static ulong
oneroot_of_classpoly(
  GEN hilb, GEN factu, norm_eqn_t ne, GEN jdb)
{
  pari_sp av = avma;
  ulong j0, p = ne->p, pi = ne->pi;
  long i, nfactors = lg(gel(factu, 1)) - 1;
  GEN hilbp = ZX_to_Flx(hilb, p);

  /* TODO: Work out how to use hilb with better invariant */
  j0 = Flx_oneroot_split(hilbp, p);
  if (j0 == p) {
    pari_err_BUG("oneroot_of_classpoly: "
                 "Didn't find a root of the class polynomial");
  }
  for (i = 1; i <= nfactors; ++i) {
    long L = gel(factu, 1)[i];
    long val = gel(factu, 2)[i];
    GEN phi = polmodular_db_getp(jdb, L, p);
    val += z_lval(ne->v, L);
    j0 = descend_volcano(phi, j0, p, pi, 0, L, val, val);
    avma = av;
  }
  avma = av; return j0;
}

/* TODO: Precompute the classgp_pcp_t structs and link them to dinfo */
INLINE void
make_pcp_surface(const disc_info *dinfo, classgp_pcp_t G)
{
  long k = 1, datalen = 3 * k;

  memset(G, 0, sizeof *G);

  G->_data = cgetg(datalen + 1, t_VECSMALL);
  G->L = G->_data + 1;
  G->n = G->L + k;
  G->o = G->L + k;

  G->k = k;
  G->h = G->enum_cnt = dinfo->n1;
  G->L[0] = dinfo->L0;
  G->n[0] = dinfo->n1;
  G->o[0] = dinfo->n1;
}

INLINE void
make_pcp_floor(const disc_info *dinfo, classgp_pcp_t G)
{
  long k = dinfo->L1 ? 2 : 1, datalen = 3 * k;

  memset(G, 0, sizeof *G);
  G->_data = cgetg(datalen + 1, t_VECSMALL);
  G->L = G->_data + 1;
  G->n = G->L + k;
  G->o = G->L + k;

  G->k = k;
  G->h = G->enum_cnt = dinfo->n2 * k;
  G->L[0] = dinfo->L0;
  G->n[0] = dinfo->n2;
  G->o[0] = dinfo->n2;
  if (dinfo->L1) {
    G->L[1] = dinfo->L1;
    G->n[1] = 2;
    G->o[1] = 2;
  }
}

INLINE GEN
enum_volcano_surface(const disc_info *dinfo, norm_eqn_t ne, ulong j0, GEN fdb)
{
  pari_sp av = avma;
  classgp_pcp_t G;
  make_pcp_surface(dinfo, G);
  return gerepileupto(av, enum_roots(j0, ne, fdb, G));
}

INLINE GEN
enum_volcano_floor(long L, norm_eqn_t ne, ulong j0_pr, GEN fdb, const disc_info *dinfo)
{
  pari_sp av = avma;
  /* L^2 D is the discriminant for the order R = Z + L OO. */
  long DR = L * L * ne->D;
  long R_cond = L * ne->u; /* conductor(DR); */
  long w = R_cond * ne->v;
  /* TODO: Calculate these once and for all in polmodular0_ZM(). */
  classgp_pcp_t G;
  norm_eqn_t eqn;
  memcpy(eqn, ne, sizeof *ne);
  eqn->D = DR;
  eqn->u = R_cond;
  eqn->v = w;
  make_pcp_floor(dinfo, G);
  return gerepileupto(av, enum_roots(j0_pr, eqn, fdb, G));
}

INLINE void
carray_reverse_inplace(long *arr, long n)
{
  long lim = n>>1, i;
  --n;
  for (i = 0; i < lim; i++) lswap(arr[i], arr[n - i]);
}

INLINE void
append_neighbours(GEN rts, GEN surface_js, long njs, long L, long m, long i)
{
  long r_idx = (((i - 1) + m) % njs) + 1; /* (i + m) % njs */
  long l_idx = smodss((i - 1) - m, njs) + 1; /* (i - m) % njs */
  rts[L] = surface_js[l_idx];
  rts[L + 1] = surface_js[r_idx];
}

INLINE GEN
roots_to_coeffs(GEN rts, ulong p, long L)
{
  long i, k, lrts= lg(rts);
  GEN M = cgetg(L+2+1, t_MAT);
  for (i = 1; i <= L+2; ++i)
    gel(M, i) = cgetg(lrts, t_VECSMALL);
  for (i = 1; i < lrts; ++i) {
    pari_sp av = avma;
    GEN modpol = Flv_roots_to_pol(gel(rts, i), p, 0);
    for (k = 1; k <= L + 2; ++k) mael(M, k, i) = modpol[k + 1];
    avma = av;
  }
  return M;
}

/* NB: Assumes indices are offset at 0, not at 1 like in GENs;
 * i.e. indices[i] will pick out v[indices[i] + 1] from v. */
INLINE void
vecsmall_pick(GEN res, GEN v, GEN indices)
{
  long i;
  for (i = 1; i < lg(indices); ++i) res[i] = v[indices[i] + 1];
}

/* First element of surface_js must lie above the first element of floor_js.
 * Reverse surface_js if it is not oriented in the same direction as floor_js */
INLINE GEN
root_matrix(long L, const disc_info *dinfo, long njinvs, GEN surface_js,
  GEN floor_js, ulong n, ulong card, ulong val, norm_eqn_t ne)
{
  pari_sp av;
  long i, m = dinfo->dl1, njs = lg(surface_js) - 1, inv = dinfo->inv, rev;
  GEN rt_mat = zero_Flm_copy(L + 1, njinvs), rts, cyc;
  av = avma;

  i = 1;
  cyc = get_Lsqr_cycle(dinfo);
  rts = gel(rt_mat, i);
  vecsmall_pick(rts, floor_js, cyc);
  append_neighbours(rts, surface_js, njs, L, m, i);

  i = 2;
  update_Lsqr_cycle(cyc, dinfo);
  rts = gel(rt_mat, i);
  vecsmall_pick(rts, floor_js, cyc);

  /* Fix orientation if necessary */
  if (modinv_is_double_eta(inv)) {
    /* TODO: There is potential for refactoring between this,
     * double_eta_initial_js and modfn_preimage. */
    pari_sp av0 = avma;
    ulong p = ne->p, pi = ne->pi, j;
    GEN F = double_eta_Fl(inv, p);
    pari_sp av = avma;
    ulong r1 = double_eta_power(inv, uel(rts, 1), p, pi);
    GEN r, f = Flx_double_eta_jpoly(F, r1, p, pi);
    if ((j = Flx_oneroot(f, p)) == p) pari_err_BUG("root_matrix");
    j = compute_L_isogenous_curve(L, n, ne, j, card, val, 0);
    avma = av;
    r1 = double_eta_power(inv, uel(surface_js, i), p, pi);
    f = Flx_double_eta_jpoly(F, r1, p, pi);
    r = Flx_roots(f, p);
    if (lg(r) != 3) pari_err_BUG("root_matrix");
    rev = (j != uel(r, 1)) && (j != uel(r, 2));
    avma = av0;
  } else {
    ulong j1pr, j1;
    j1pr = modfn_preimage(uel(rts, 1), ne, dinfo->inv);
    j1 = compute_L_isogenous_curve(L, n, ne, j1pr, card, val, 0);
    rev = j1 != modfn_preimage(uel(surface_js, i), ne, dinfo->inv);
  }
  if (rev)
    carray_reverse_inplace(surface_js + 2, njs - 1);
  append_neighbours(rts, surface_js, njs, L, m, i);

  for (i = 3; i <= njinvs; ++i) {
    update_Lsqr_cycle(cyc, dinfo);
    rts = gel(rt_mat, i);
    vecsmall_pick(rts, floor_js, cyc);
    append_neighbours(rts, surface_js, njs, L, m, i);
  }
  avma = av; return rt_mat;
}

INLINE void
interpolate_coeffs(GEN phi_modp, ulong p, GEN j_invs, GEN coeff_mat)
{
  pari_sp av = avma;
  long i;
  GEN pols = Flv_Flm_polint(j_invs, coeff_mat, p, 0);
  for (i = 1; i < lg(pols); ++i) {
    GEN pol = gel(pols, i);
    long k, maxk = lg(pol);
    for (k = 2; k < maxk; ++k) coeff(phi_modp, k - 1, i) = pol[k];
  }
  avma = av;
}

INLINE long
Flv_lastnonzero(GEN v)
{
  long i;
  for (i = lg(v) - 1; i > 0; --i)
    if (v[i]) break;
  return i;
}

/* Assuming the matrix of coefficients in phi corresponds to polynomials
 * phi_k^* satisfying Y^c phi_k^*(Y^s) for c in {0, 1, ..., s} satisfying
 * c + Lk = L + 1 (mod s), change phi so that the coefficients are for the
 * polynomials Y^c phi_k^*(Y^s) (s is the sparsity factor) */
INLINE void
inflate_polys(GEN phi, long L, long s)
{
  long k, deg = L + 1;
  long maxr;
  maxr = nbrows(phi);
  for (k = 0; k <= deg; ) {
    long i, c = smodss(L * (1 - k) + 1, s);
    /* TODO: We actually know that the last non-zero element of gel(phi, k)
     * can't be later than index n+1, where n is about (L + 1)/s. */
    ++k;
    for (i = Flv_lastnonzero(gel(phi, k)); i > 0; --i) {
      long r = c + (i - 1) * s + 1;
      if (r > maxr) { coeff(phi, i, k) = 0; continue; }
      if (r != i) {
        coeff(phi, r, k) = coeff(phi, i, k);
        coeff(phi, i, k) = 0;
      }
    }
  }
}

INLINE void
Flv_powu_inplace_pre(GEN v, ulong n, ulong p, ulong pi)
{
  long i;
  for (i = 1; i < lg(v); ++i) v[i] = Fl_powu_pre(v[i], n, p, pi);
}

INLINE void
normalise_coeffs(GEN coeffs, GEN js, long L, long s, ulong p, ulong pi)
{
  pari_sp av = avma;
  long k;
  GEN pows, modinv_js;

  /* NB: In fact it would be correct to return the coefficients "as is" when
   * s = 1, but we make that an error anyway since this function should never
   * be called with s = 1. */
  if (s <= 1) pari_err_BUG("normalise_coeffs");

  /* pows[i + 1] contains 1 / js[i + 1]^i for i = 0, ..., s - 1. */
  pows = cgetg(s + 1, t_VEC);
  gel(pows, 1) = const_vecsmall(lg(js) - 1, 1);
  modinv_js = Flv_inv_pre(js, p, pi);
  gel(pows, 2) = modinv_js;
  for (k = 3; k <= s; ++k) {
    gel(pows, k) = gcopy(modinv_js);
    Flv_powu_inplace_pre(gel(pows, k), k - 1, p, pi);
  }

  /* For each column of coefficients coeffs[k] = [a0 .. an],
   *   replace ai by ai / js[i]^c.
   * Said in another way, normalise each row i of coeffs by
   * dividing through by js[i - 1]^c (where c depends on i). */
  for (k = 1; k < lg(coeffs); ++k) {
    long i, c = smodss(L * (1 - (k - 1)) + 1, s);
    GEN col = gel(coeffs, k), C = gel(pows, c + 1);
    for (i = 1; i < lg(col); ++i)
      col[i] = Fl_mul_pre(col[i], C[i], p, pi);
  }
  avma = av;
}

INLINE void
double_eta_initial_js(
  ulong *x0, ulong *x0pr, ulong j0, ulong j0pr, norm_eqn_t ne,
  long inv, ulong L, ulong n, ulong card, ulong val)
{
  pari_sp av0 = avma;
  ulong p = ne->p, pi = ne->pi, s2 = ne->s2;
  GEN F = double_eta_Fl(inv, p);
  pari_sp av = avma;
  ulong j1pr, j1, r, t;
  GEN f, g;

  *x0pr = modinv_double_eta_from_j(F, inv, j0pr, p, pi, s2);
  t = double_eta_power(inv, *x0pr, p, pi);
  f = Flx_div_by_X_x(Flx_double_eta_jpoly(F, t, p, pi), j0pr, p, &r);
  if (r) pari_err_BUG("double_eta_initial_js");
  j1pr = Flx_deg1_root(f, p);
  avma = av;

  j1 = compute_L_isogenous_curve(L, n, ne, j1pr, card, val, 0);
  f = Flx_double_eta_xpoly(F, j0, p, pi);
  g = Flx_double_eta_xpoly(F, j1, p, pi);
  /* x0 is the unique common root of f and g */
  *x0 = Flx_deg1_root(Flx_gcd(f, g, p), p);
  avma = av0;

  if ( ! double_eta_root(inv, x0, *x0, p, pi, s2))
    pari_err_BUG("double_eta_initial_js");
}

/* This is Sutherland 2012, Algorithm 2.1, p16. */
static GEN
polmodular_split_p_Flm(ulong L, GEN hilb, GEN factu, norm_eqn_t ne, GEN db,
  const disc_info *dinfo)
{
  ulong j0, j0_rt, j0pr, j0pr_rt;
  ulong n, card, val, p = ne->p, pi = ne->pi;
  long s = modinv_sparse_factor(dinfo->inv);
  long nj_selected = ceil((L + 1)/(double)s) + 1;
  GEN surface_js, floor_js, rts;
  GEN phi_modp;
  GEN jdb, fdb;
  long switched_signs = 0;

  jdb = polmodular_db_for_inv(db, INV_J);
  fdb = polmodular_db_for_inv(db, dinfo->inv);

  /* Precomputation */
  card = p + 1 - ne->t;
  val = u_lvalrem(card, L, &n); /* n = card / L^{v_L(card)} */

  j0 = oneroot_of_classpoly(hilb, factu, ne, jdb);
  j0pr = compute_L_isogenous_curve(L, n, ne, j0, card, val, 1);
  if (modinv_is_double_eta(dinfo->inv)) {
    double_eta_initial_js(&j0_rt, &j0pr_rt, j0, j0pr, ne, dinfo->inv,
        L, n, card, val);
  } else {
    j0_rt = modfn_root(j0, ne, dinfo->inv);
    j0pr_rt = modfn_root(j0pr, ne, dinfo->inv);
  }
  surface_js = enum_volcano_surface(dinfo, ne, j0_rt, fdb);
  floor_js = enum_volcano_floor(L, ne, j0pr_rt, fdb, dinfo);
  rts = root_matrix(L, dinfo, nj_selected, surface_js, floor_js,
                    n, card, val, ne);
  do {
    pari_sp btop = avma;
    long i;
    GEN coeffs, surf;

    coeffs = roots_to_coeffs(rts, p, L);
    surf = vecsmall_shorten(surface_js, nj_selected);
    if (s > 1) {
      normalise_coeffs(coeffs, surf, L, s, p, pi);
      Flv_powu_inplace_pre(surf, s, p, pi);
    }
    phi_modp = zero_Flm_copy(L + 2, L + 2);
    interpolate_coeffs(phi_modp, p, surf, coeffs);
    if (s > 1) inflate_polys(phi_modp, L, s);

    /* TODO: Calculate just this coefficient of X^L Y^L, so we can do this
     * test, then calculate the other coefficients; at the moment we are
     * sometimes doing all the roots-to-coeffs, normalisation and interpolation
     * work twice. */
    if (ucoeff(phi_modp, L + 1, L + 1) == p - 1) break;

    if (switched_signs) pari_err_BUG("polmodular_split_p_Flm");

    avma = btop;
    for (i = 1; i < lg(rts); ++i) {
      surface_js[i] = Fl_neg(surface_js[i], p);
      coeff(rts, L, i) = Fl_neg(coeff(rts, L, i), p);
      coeff(rts, L + 1, i) = Fl_neg(coeff(rts, L + 1, i), p);
    }
    switched_signs = 1;
  } while (1);
  dbg_printf(4)("  Phi_%lu(X, Y) (mod %lu) = %Ps\n", L, p, phi_modp);

  return phi_modp;
}

INLINE void
norm_eqn_update(norm_eqn_t ne, GEN vne, ulong t, ulong p, long L)
{
  long res;
  ulong vL_sqr, vL;

  ne->D = vne[1];
  ne->u = vne[2];
  ne->t = t;
  ne->p = p;
  ne->pi = get_Fl_red(p);
  ne->s2 = Fl_2gener_pre(p, ne->pi);

  vL_sqr = (4 * p - t * t) / -ne->D;
  res = uissquareall(vL_sqr, &vL);
  if (!res || vL % L) pari_err_BUG("norm_eqn_update");
  ne->v = vL;

  /* select twisting parameter */
  do ne->T = random_Fl(p); while (krouu(ne->T, p) != -1);
}

INLINE void
Flv_deriv_pre_inplace(GEN v, long deg, ulong p, ulong pi)
{
  long i, ln = lg(v), d = deg % p;
  for (i = ln - 1; i > 1; --i, --d) v[i] = Fl_mul_pre(v[i - 1], d, p, pi);
  v[1] = 0;
}

INLINE GEN
eval_modpoly_modp(GEN Tp, GEN j_powers, norm_eqn_t ne, int compute_derivs)
{
  ulong p = ne->p, pi = ne->pi;
  long L = lg(j_powers) - 3;
  GEN j_pows_p = ZV_to_Flv(j_powers, p);
  GEN tmp = cgetg(2 + 2 * compute_derivs, t_VEC);
  /* We wrap the result in this t_VEC Tp to trick the
   * ZM_*_CRT() functions into thinking it's a matrix. */
  gel(tmp, 1) = Flm_Flc_mul_pre(Tp, j_pows_p, p, pi);
  if (compute_derivs) {
    Flv_deriv_pre_inplace(j_pows_p, L + 1, p, pi);
    gel(tmp, 2) = Flm_Flc_mul_pre(Tp, j_pows_p, p, pi);
    Flv_deriv_pre_inplace(j_pows_p, L + 1, p, pi);
    gel(tmp, 3) = Flm_Flc_mul_pre(Tp, j_pows_p, p, pi);
  }
  return tmp;
}

/* Parallel interface */
GEN
polmodular_worker(ulong p, ulong t, ulong L,
                  GEN hilb, GEN factu, GEN vne, GEN vinfo,
                  long derivs, GEN j_powers, GEN fdb)
{
  pari_sp av = avma;
  norm_eqn_t ne;
  GEN Tp;
  norm_eqn_update(ne, vne, t, p, L);
  Tp = polmodular_split_p_Flm(L, hilb, factu, ne, fdb, (const disc_info*)vinfo);
  if (!isintzero(j_powers)) Tp = eval_modpoly_modp(Tp, j_powers, ne, derivs);
  return gerepileupto(av, Tp);
}

static GEN
sympol_to_ZM(GEN phi, long L)
{
  pari_sp av = avma;
  GEN res = zeromatcopy(L + 2, L + 2);
  long i, j, c = 1;
  for (i = 1; i <= L + 1; ++i)
    for (j = 1; j <= i; ++j, ++c)
      gcoeff(res, i, j) = gcoeff(res, j, i) = gel(phi, c);
  gcoeff(res, L + 2, 1) = gcoeff(res, 1, L + 2) = gen_1;
  return gerepilecopy(av, res);
}

static GEN polmodular_small_ZM(long L, long inv, GEN *db);

INLINE long
modinv_max_internal_level(long inv)
{
  switch (inv) {
    case INV_J: return 5;
    case INV_G2: return 2;
    case INV_F:
    case INV_F2:
    case INV_F4:
    case INV_F8: return 5;
    case INV_W2W5:
    case INV_W2W5E2: return 7;
    case INV_W2W3:
    case INV_W2W3E2:
    case INV_W3W3:
    case INV_W3W7:  return 5;
    case INV_W3W3E2:return 2;
    case INV_F3:
    case INV_W2W7:
    case INV_W2W7E2:
    case INV_W2W13: return 3;
    case INV_W3W5:
    case INV_W5W7:
    case INV_W3W13: return 2;
  }
  pari_err_BUG("modinv_max_internal_level"); return LONG_MAX;/*LCOV_EXCL_LINE*/
}

GEN
polmodular0_ZM(long L, long inv, GEN J, GEN Q, int compute_derivs, GEN *db)
{
  pari_sp ltop = avma;
  long k, d, Dcnt, nprimes = 0;
  GEN modpoly, plist;
  disc_info Ds[MODPOLY_MAX_DCNT];
  long lvl = modinv_level(inv);
  if (ugcd(L, lvl) != 1)
    pari_err_DOMAIN("polmodular0_ZM", "invariant",
                    "incompatible with", stoi(L), stoi(lvl));

  dbg_printf(1)("Calculating modular polynomial of level %lu for invariant %d\n", L, inv);
  if (L <= modinv_max_internal_level(inv)) return polmodular_small_ZM(L,inv,db);

  Dcnt = discriminant_with_classno_at_least(Ds, L, inv, USE_SPARSE_FACTOR);
  for (d = 0; d < Dcnt; d++) nprimes += Ds[d].nprimes;
  modpoly = cgetg(nprimes+1, t_VEC);
  plist = cgetg(nprimes+1, t_VECSMALL);
  for (d = 0, k = 1; d < Dcnt; d++)
  {
    disc_info *dinfo = &Ds[d];
    struct pari_mt pt;
    const long D = dinfo->D1, DK = dinfo->D0;
    const ulong cond = usqrt(D / DK);
    long i, pending = 0;
    GEN worker, j_powers, factu, hilb;

    polmodular_db_add_level(db, dinfo->L0, inv);
    if (dinfo->L1) polmodular_db_add_level(db, dinfo->L1, inv);
    factu = factoru(cond);
    dbg_printf(1)("Selected discriminant D = %ld = %ld^2 * %ld.\n", D,cond,DK);

    hilb = polclass0(DK, INV_J, 0, db);
    if (cond > 1)
      polmodular_db_add_levels(db, zv_to_longptr(gel(factu,1)), lg(gel(factu,1))-1, INV_J);

    dbg_printf(1)("D = %ld, L0 = %lu, L1 = %lu, ", dinfo->D1, dinfo->L0, dinfo->L1);
    dbg_printf(1)("n1 = %lu, n2 = %lu, dl1 = %lu, dl2_0 = %lu, dl2_1 = %lu\n",
          dinfo->n1, dinfo->n2, dinfo->dl1, dinfo->dl2_0, dinfo->dl2_1);
    dbg_printf(0)("Calculating modular polynomial of level %lu:", L);

    j_powers = gen_0;
    if (J) {
      compute_derivs = !!compute_derivs;
      j_powers = Fp_powers(J, L+1, Q);
    }
    worker = strtoclosure("_polmodular_worker", 8, utoi(L), hilb, factu,
        mkvecsmall2(D, cond), (GEN)dinfo, stoi(compute_derivs), j_powers, *db);
    mt_queue_start_lim(&pt, worker, dinfo->nprimes);
    for (i = 0; i < dinfo->nprimes || pending; i++)
    {
      GEN done;
      long workid;
      ulong p = dinfo->primes[i], t = dinfo->traces[i];
      mt_queue_submit(&pt, p, i < dinfo->nprimes? mkvec2(utoi(p), utoi(t)): NULL);
      done = mt_queue_get(&pt, &workid, &pending);
      if (done)
      {
        gel(modpoly, k) = done;
        plist[k] = workid; k++;
        dbg_printf(0)(" %ld%%", k*100/nprimes);
      }
    }
    dbg_printf(0)("\n");
    mt_queue_end(&pt);
    killblock((GEN)dinfo->primes);
  }
  modpoly = nmV_chinese_center(modpoly, plist, NULL);
  if (J) modpoly = FpM_red(modpoly, Q);
  return gerepileupto(ltop, modpoly);
}

GEN
polmodular_ZM(long L, long inv)
{
  GEN db, Phi;

  if (L < 2)
    pari_err_DOMAIN("polmodular_ZM", "L", "<", gen_2, stoi(L));

  /* TODO: Handle non-prime L.  This is Algorithm 1.1 and Corollary
   * 3.4 in Sutherland, "Class polynomials for nonholomorphic modular
   * functions". */
  if ( ! uisprime(L))
    pari_err_IMPL("composite level");

  db = polmodular_db_init(inv);
  Phi = polmodular0_ZM(L, inv, NULL, NULL, 0, &db);
  gunclone_deep(db);

  return Phi;
}

GEN
polmodular_ZXX(long L, long inv, long vx, long vy)
{
  pari_sp av = avma;
  GEN phi = polmodular_ZM(L, inv);

  if (vx < 0) vx = 0;
  if (vy < 0) vy = 1;
  if (varncmp(vx, vy) >= 0)
    pari_err_PRIORITY("polmodular_ZXX", pol_x(vx), "<=", vy);
  return gerepilecopy(av, RgM_to_RgXX(phi, vx, vy));
}

INLINE GEN
FpV_deriv(GEN v, long deg, GEN P)
{
  long i, ln = lg(v);
  GEN dv = cgetg(ln, t_VEC);
  for (i = ln - 1; i > 1; --i, --deg)
    gel(dv, i) = Fp_mulu(gel(v, i - 1), deg, P);
  gel(dv, 1) = gen_0;
  return dv;
}

GEN
Fp_polmodular_evalx(
  long L, long inv, GEN J, GEN P, long v, int compute_derivs)
{
  pari_sp av = avma;
  GEN db, phi;

  if (L <= modinv_max_internal_level(inv)) {
    GEN tmp;
    GEN phi = RgM_to_FpM(polmodular_ZM(L, inv), P);
    GEN j_powers = Fp_powers(J, L + 1, P);
    GEN modpol = RgV_to_RgX(FpM_FpC_mul(phi, j_powers, P), v);
    if (compute_derivs) {
      tmp = cgetg(4, t_VEC);
      gel(tmp, 1) = modpol;
      j_powers = FpV_deriv(j_powers, L + 1, P);
      gel(tmp, 2) = RgV_to_RgX(FpM_FpC_mul(phi, j_powers, P), v);
      j_powers = FpV_deriv(j_powers, L + 1, P);
      gel(tmp, 3) = RgV_to_RgX(FpM_FpC_mul(phi, j_powers, P), v);
    } else
      tmp = modpol;
    return gerepilecopy(av, tmp);
  }

  db = polmodular_db_init(inv);
  phi = polmodular0_ZM(L, inv, J, P, compute_derivs, &db);
  phi = RgM_to_RgXV(phi, v);
  gunclone_deep(db);
  return gerepilecopy(av, compute_derivs ? phi : gel(phi, 1));
}

GEN
polmodular(long L, long inv, GEN x, long v, long compute_derivs)
{
  pari_sp av = avma;
  long tx;
  GEN J = NULL, P = NULL, res = NULL, one = NULL;

  check_modinv(inv);
  if ( ! x || gequalX(x)) {
    long xv = 0;
    if (x) xv = varn(x);
    if (compute_derivs) pari_err_FLAG("polmodular");
    return polmodular_ZXX(L, inv, xv, v);
  }

  tx = typ(x);
  if (tx == t_INTMOD) {
    J = gel(x, 2);
    P = gel(x, 1);
    one = mkintmod(gen_1, P);
  } else if (tx == t_FFELT) {
    J = FF_to_FpXQ_i(x);
    if (degpol(J) > 0)
      pari_err_DOMAIN("polmodular", "x", "not in prime subfield ", gen_0, x);
    J = constant_coeff(J);
    P = FF_p_i(x);
    one = p_to_FF(P, 0);
  } else {
    pari_err_TYPE("polmodular", x);
  }

  if (v < 0) v = 1;
  res = Fp_polmodular_evalx(L, inv, J, P, v, compute_derivs);
  res = gmul(res, one);
  return gerepileupto(av, res);
}

/**
 * SECTION: Modular polynomials of level <= MAX_INTERNAL_MODPOLY_LEVEL.
 */

/* These functions return a vector of unique coefficients of classical
 * modular polynomials \Phi_L(X, Y) of small level L.  The number of
 * such coefficients is (L + 1)(L + 2)/2 since \Phi is symmetric.
 * (Note that we omit the common coefficient of X^{L + 1} and Y^{L + 1} since
 * it is always 1.)  See sympol_to_ZM() for how to interpret the coefficients,
 * and use that function to get the corresponding full (desymmetrised) matrix
 * of coefficients. */

/*  Phi2, the modular polynomial of level 2:
 *
 *  X^3
 *  + X^2 * (-Y^2 + 1488*Y - 162000)
 *  + X * (1488*Y^2 + 40773375*Y + 8748000000)
 *  + Y^3 - 162000*Y^2 + 8748000000*Y - 157464000000000
 *
 *  [[3, 0, 1],
 *   [2, 2, -1],
 *   [2, 1, 1488],
 *   [2, 0, -162000],
 *   [1, 1, 40773375],
 *   [1, 0, 8748000000],
 *   [0, 0, -157464000000000]], */
static GEN
phi2_ZV(void)
{
  GEN phi2 = cgetg(7, t_VEC);
  gel(phi2, 1) = uu32toi(36662, 1908994048);
  setsigne(gel(phi2, 1), -1);
  gel(phi2, 2) = uu32toi(2, 158065408);
  gel(phi2, 3) = stoi(40773375);
  gel(phi2, 4) = stoi(-162000);
  gel(phi2, 5) = stoi(1488);
  gel(phi2, 6) = gen_m1;
  return phi2;
}

/* L = 3
 *
 * [4, 0, 1],
 * [3, 3, -1],
 * [3, 2, 2232],
 * [3, 1, -1069956],
 * [3, 0, 36864000],
 * [2, 2, 2587918086],
 * [2, 1, 8900222976000],
 * [2, 0, 452984832000000],
 * [1, 1, -770845966336000000],
 * [1, 0, 1855425871872000000000]
 * [0, 0, 0]
 *
 * X^4
 * + X^3 (-Y^3 + 2232*Y^2 - 1069956*Y + 36864000)
 * + X^2 (2232*Y^3 + 2587918086*Y^2 + 8900222976000*Y + 452984832000000)
 * + X (-1069956*Y^3 + 8900222976000*Y^2 - 770845966336000000*Y + 1855425871872000000000)
 * + Y^4 + 36864000*Y^3 + 452984832000000*Y^2 + 1855425871872000000000*Y
 *
 * 1855425871872000000000 == 2^32 * (100 * 2^32 + 2503270400) */
static GEN
phi3_ZV(void)
{
  GEN phi3 = cgetg(11, t_VEC);
  pari_sp av = avma;
  gel(phi3, 1) = gen_0;
  gel(phi3, 2) = gerepileupto(av, shifti(uu32toi(100, 2503270400UL), 32));
  gel(phi3, 3) = uu32toi(179476562, 2147483648UL);
  setsigne(gel(phi3, 3), -1);
  gel(phi3, 4) = uu32toi(105468, 3221225472UL);
  gel(phi3, 5) = uu32toi(2072, 1050738688);
  gel(phi3, 6) = utoi(2587918086UL);
  gel(phi3, 7) = stoi(36864000);
  gel(phi3, 8) = stoi(-1069956);
  gel(phi3, 9) = stoi(2232);
  gel(phi3, 10) = gen_m1;
  return phi3;
}

static GEN
phi5_ZV(void)
{
  GEN phi5 = cgetg(22, t_VEC);
  gel(phi5, 1) = mkintn(5, 0x18c2cc9cUL, 0x484382b2UL, 0xdc000000UL, 0x0UL, 0x0UL);
  gel(phi5, 2) = mkintn(5, 0x2638fUL, 0x2ff02690UL, 0x68026000UL, 0x0UL, 0x0UL);
  gel(phi5, 3) = mkintn(5, 0x308UL, 0xac9d9a4UL, 0xe0fdab12UL, 0xc0000000UL, 0x0UL);
  setsigne(gel(phi5, 3), -1);
  gel(phi5, 4) = mkintn(5, 0x13UL, 0xaae09f9dUL, 0x1b5ef872UL, 0x30000000UL, 0x0UL);
  gel(phi5, 5) = mkintn(4, 0x1b802fa9UL, 0x77ba0653UL, 0xd2f78000UL, 0x0UL);
  gel(phi5, 6) = mkintn(4, 0xfbfdUL, 0x278e4756UL, 0xdf08a7c4UL, 0x40000000UL);
  gel(phi5, 7) = mkintn(4, 0x35f922UL, 0x62ccea6fUL, 0x153d0000UL, 0x0UL);
  gel(phi5, 8) = mkintn(4, 0x97dUL, 0x29203fafUL, 0xc3036909UL, 0x80000000UL);
  setsigne(gel(phi5, 8), -1);
  gel(phi5, 9) = mkintn(3, 0x56e9e892UL, 0xd7781867UL, 0xf2ea0000UL);
  gel(phi5, 10) = mkintn(3, 0x5d6dUL, 0xe0a58f4eUL, 0x9ee68c14UL);
  setsigne(gel(phi5, 10), -1);
  gel(phi5, 11) = mkintn(3, 0x1100dUL, 0x85cea769UL, 0x40000000UL);
  gel(phi5, 12) = mkintn(3, 0x1b38UL, 0x43cf461fUL, 0x3a900000UL);
  gel(phi5, 13) = mkintn(3, 0x14UL, 0xc45a616eUL, 0x4801680fUL);
  gel(phi5, 14) = uu32toi(0x17f4350UL, 0x493ca3e0UL);
  gel(phi5, 15) = uu32toi(0x183UL, 0xe54ce1f8UL);
  gel(phi5, 16) = uu32toi(0x1c9UL, 0x18860000UL);
  gel(phi5, 17) = uu32toi(0x39UL, 0x6f7a2206UL);
  setsigne(gel(phi5, 17), -1);
  gel(phi5, 18) = stoi(2028551200);
  gel(phi5, 19) = stoi(-4550940);
  gel(phi5, 20) = stoi(3720);
  gel(phi5, 21) = gen_m1;
  return phi5;
}

static GEN
phi5_f_ZV(void)
{
  GEN phi = zerovec(21);
  gel(phi, 3) = stoi(4);
  gel(phi, 21) = gen_m1;
  return phi;
}

static GEN
phi3_f3_ZV(void)
{
  GEN phi = zerovec(10);
  gel(phi, 3) = stoi(8);
  gel(phi, 10) = gen_m1;
  return phi;
}

static GEN
phi2_g2_ZV(void)
{
  GEN phi = zerovec(6);
  gel(phi, 1) = stoi(-54000);
  gel(phi, 3) = stoi(495);
  gel(phi, 6) = gen_m1;
  return phi;
}

static GEN
phi5_w2w3_ZV(void)
{
  GEN phi = zerovec(21);
  gel(phi, 3) = gen_m1;
  gel(phi, 10) = stoi(5);
  gel(phi, 21) = gen_m1;
  return phi;
}

static GEN
phi7_w2w5_ZV(void)
{
  GEN phi = zerovec(36);
  gel(phi, 3) = gen_m1;
  gel(phi, 15) = stoi(56);
  gel(phi, 19) = stoi(42);
  gel(phi, 24) = stoi(21);
  gel(phi, 30) = stoi(7);
  gel(phi, 36) = gen_m1;
  return phi;
}

static GEN
phi5_w3w3_ZV(void)
{
  GEN phi = zerovec(21);
  gel(phi, 3) = stoi(9);
  gel(phi, 6) = stoi(-15);
  gel(phi, 15) = stoi(5);
  gel(phi, 21) = gen_m1;
  return phi;
}

static GEN
phi3_w2w7_ZV(void)
{
  GEN phi = zerovec(10);
  gel(phi, 3) = gen_m1;
  gel(phi, 6) = stoi(3);
  gel(phi, 10) = gen_m1;
  return phi;
}

static GEN
phi2_w3w5_ZV(void)
{
  GEN phi = zerovec(6);
  gel(phi, 3) = gen_1;
  gel(phi, 6) = gen_m1;
  return phi;
}

static GEN
phi5_w3w7_ZV(void)
{
  GEN phi = zerovec(21);
  gel(phi, 3) = gen_m1;
  gel(phi, 6) = stoi(10);
  gel(phi, 8) = stoi(5);
  gel(phi, 10) = stoi(35);
  gel(phi, 13) = stoi(20);
  gel(phi, 15) = stoi(10);
  gel(phi, 17) = stoi(5);
  gel(phi, 19) = stoi(5);
  gel(phi, 21) = gen_m1;
  return phi;
}

static GEN
phi3_w2w13_ZV(void)
{
  GEN phi = zerovec(10);
  gel(phi, 3) = gen_m1;
  gel(phi, 6) = stoi(3);
  gel(phi, 8) = stoi(3);
  gel(phi, 10) = gen_m1;
  return phi;
}

static GEN
phi2_w3w3e2_ZV(void)
{
  GEN phi = zerovec(6);
  gel(phi, 3) = stoi(3);
  gel(phi, 6) = gen_m1;
  return phi;
}

static GEN
phi2_w5w7_ZV(void)
{
  GEN phi = zerovec(6);
  gel(phi, 3) = gen_1;
  gel(phi, 5) = gen_2;
  gel(phi, 6) = gen_m1;
  return phi;
}

static GEN
phi2_w3w13_ZV(void)
{
  GEN phi = zerovec(6);
  gel(phi, 3) = gen_m1;
  gel(phi, 5) = gen_2;
  gel(phi, 6) = gen_m1;
  return phi;
}

INLINE long
modinv_parent(long inv)
{
  switch (inv) {
    case INV_F2:
    case INV_F4:
    case INV_F8:     return INV_F;
    case INV_W2W3E2: return INV_W2W3;
    case INV_W2W5E2: return INV_W2W5;
    case INV_W2W7E2: return INV_W2W7;
    case INV_W3W3E2: return INV_W3W3;
    default: pari_err_BUG("modinv_parent"); return -1;/*LCOV_EXCL_LINE*/
  }
}

/* TODO: Think of a better name than "parent power"; sheesh. */
INLINE long
modinv_parent_power(long inv)
{
  switch (inv) {
    case INV_F4: return 4;
    case INV_F8: return 8;
    case INV_F2:
    case INV_W2W3E2:
    case INV_W2W5E2:
    case INV_W2W7E2:
    case INV_W3W3E2: return 2;
    default: pari_err_BUG("modinv_parent_power"); return -1;/*LCOV_EXCL_LINE*/
  }
}

static GEN
polmodular0_powerup_ZM(long L, long inv, GEN *db)
{
  pari_sp ltop = avma, av;
  long s, D, nprimes, N;
  GEN mp, pol, P, H;
  long parent = modinv_parent(inv);
  long e = modinv_parent_power(inv);
  disc_info Ds[MODPOLY_MAX_DCNT];
  /* FIXME: We throw away the table of fundamental discriminants here. */
  long nDs = discriminant_with_classno_at_least(Ds, L, inv, IGNORE_SPARSE_FACTOR);
  if (nDs != 1) pari_err_BUG("polmodular0_powerup_ZM");
  D = Ds[0].D1;
  nprimes = Ds[0].nprimes + 1;
  mp = polmodular0_ZM(L, parent, NULL, NULL, 0, db);
  H = polclass0(D, parent, 0, db);

  N = L + 2;
  if (degpol(H) < N) pari_err_BUG("polmodular0_powerup_ZM");

  av = avma;
  pol = ZM_init_CRT(zero_Flm_copy(N, L + 2), 1);
  P = gen_1;
  for (s = 1; s < nprimes; ++s) {
    pari_sp av1, av2;
    ulong p = Ds[0].primes[s-1], pi = get_Fl_red(p);
    long i;
    GEN Hrts, js, Hp, Phip, coeff_mat, phi_modp;

    phi_modp = zero_Flm_copy(N, L + 2);
    av1 = avma;
    Hp = ZX_to_Flx(H, p);
    Hrts = Flx_roots(Hp, p);
    if (lg(Hrts)-1 < N) pari_err_BUG("polmodular0_powerup_ZM");
    js = cgetg(N + 1, t_VECSMALL);
    for (i = 1; i <= N; ++i)
      uel(js, i) = Fl_powu_pre(uel(Hrts, i), e, p, pi);

    Phip = ZM_to_Flm(mp, p);
    coeff_mat = zero_Flm_copy(N, L + 2);
    av2 = avma;
    for (i = 1; i <= N; ++i) {
      long k;
      GEN phi_at_ji, mprts;

      phi_at_ji = Flm_Fl_polmodular_evalx(Phip, L, uel(Hrts, i), p, pi);
      mprts = Flx_roots(phi_at_ji, p);
      if (lg(mprts) != L + 2) pari_err_BUG("polmodular0_powerup_ZM");

      Flv_powu_inplace_pre(mprts, e, p, pi);
      phi_at_ji = Flv_roots_to_pol(mprts, p, 0);

      for (k = 1; k <= L + 2; ++k)
        ucoeff(coeff_mat, i, k) = uel(phi_at_ji, k + 1);
      avma = av2;
    }

    interpolate_coeffs(phi_modp, p, js, coeff_mat);
    avma = av1;

    (void) ZM_incremental_CRT(&pol, phi_modp, &P, p);
    if (gc_needed(av, 2)) gerepileall(av, 2, &pol, &P);
  }
  killblock((GEN)Ds[0].primes); return gerepileupto(ltop, pol);
}

/* Returns the modular polynomial with the smallest level for the given
 * invariant, except if inv is INV_J, in which case return the modular
 * polynomial of level L in {2,3,5}.  NULL is returned if the modular
 * polynomial can be calculated using polmodular0_powerup_ZM. */
INLINE GEN
internal_db(long L, long inv)
{
  switch (inv) {
  case INV_J: switch (L) {
    case 2: return phi2_ZV();
    case 3: return phi3_ZV();
    case 5: return phi5_ZV();
    default: break;
  }
  case INV_F: return phi5_f_ZV();
  case INV_F2: return NULL;
  case INV_F3: return phi3_f3_ZV();
  case INV_F4: return NULL;
  case INV_G2: return phi2_g2_ZV();
  case INV_W2W3: return phi5_w2w3_ZV();
  case INV_F8: return NULL;
  case INV_W3W3: return phi5_w3w3_ZV();
  case INV_W2W5: return phi7_w2w5_ZV();
  case INV_W2W7: return phi3_w2w7_ZV();
  case INV_W3W5: return phi2_w3w5_ZV();
  case INV_W3W7: return phi5_w3w7_ZV();
  case INV_W2W3E2: return NULL;
  case INV_W2W5E2: return NULL;
  case INV_W2W13: return phi3_w2w13_ZV();
  case INV_W2W7E2: return NULL;
  case INV_W3W3E2: return phi2_w3w3e2_ZV();
  case INV_W5W7: return phi2_w5w7_ZV();
  case INV_W3W13: return phi2_w3w13_ZV();
  }
  pari_err_BUG("internal_db");
  return NULL;
}

/* NB: Should only be called if L <= modinv_max_internal_level(inv) */
static GEN
polmodular_small_ZM(long L, long inv, GEN *db)
{
  GEN f = internal_db(L, inv);
  if (!f) return polmodular0_powerup_ZM(L, inv, db);
  return sympol_to_ZM(f, L);
}

/* Each function phi_w?w?_j() returns a vector V containing two
 * vectors u and v, and a scalar k, which together represent the
 * bivariate polnomial
 *
 *   phi(X, Y) = \sum_i u[i] X^i + Y \sum_i v[i] X^i + Y^2 X^k
 */
static GEN
phi_w2w3_j(void)
{
  GEN phi, phi0, phi1;
  phi = cgetg(4, t_VEC);

  phi0 = cgetg(14, t_VEC);
  gel(phi0, 1) = gen_1;
  gel(phi0, 2) = utoineg(0x3cUL);
  gel(phi0, 3) = utoi(0x702UL);
  gel(phi0, 4) = utoineg(0x797cUL);
  gel(phi0, 5) = utoi(0x5046fUL);
  gel(phi0, 6) = utoineg(0x1be0b8UL);
  gel(phi0, 7) = utoi(0x28ef9cUL);
  gel(phi0, 8) = utoi(0x15e2968UL);
  gel(phi0, 9) = utoi(0x1b8136fUL);
  gel(phi0, 10) = utoi(0xa67674UL);
  gel(phi0, 11) = utoi(0x23982UL);
  gel(phi0, 12) = utoi(0x294UL);
  gel(phi0, 13) = gen_1;

  phi1 = cgetg(13, t_VEC);
  gel(phi1, 1) = gen_0;
  gel(phi1, 2) = gen_0;
  gel(phi1, 3) = gen_m1;
  gel(phi1, 4) = utoi(0x23UL);
  gel(phi1, 5) = utoineg(0xaeUL);
  gel(phi1, 6) = utoineg(0x5b8UL);
  gel(phi1, 7) = utoi(0x12d7UL);
  gel(phi1, 8) = utoineg(0x7c86UL);
  gel(phi1, 9) = utoi(0x37c8UL);
  gel(phi1, 10) = utoineg(0x69cUL);
  gel(phi1, 11) = utoi(0x48UL);
  gel(phi1, 12) = gen_m1;

  gel(phi, 1) = phi0;
  gel(phi, 2) = phi1;
  gel(phi, 3) = utoi(5); return phi;
}

static GEN
phi_w3w3_j(void)
{
  GEN phi, phi0, phi1;
  phi = cgetg(4, t_VEC);

  phi0 = cgetg(14, t_VEC);
  gel(phi0, 1) = utoi(0x2d9UL);
  gel(phi0, 2) = utoi(0x4fbcUL);
  gel(phi0, 3) = utoi(0x5828aUL);
  gel(phi0, 4) = utoi(0x3a7a3cUL);
  gel(phi0, 5) = utoi(0x1bd8edfUL);
  gel(phi0, 6) = utoi(0x8348838UL);
  gel(phi0, 7) = utoi(0x1983f8acUL);
  gel(phi0, 8) = utoi(0x14e4e098UL);
  gel(phi0, 9) = utoi(0x69ed1a7UL);
  gel(phi0, 10) = utoi(0xc3828cUL);
  gel(phi0, 11) = utoi(0x2696aUL);
  gel(phi0, 12) = utoi(0x2acUL);
  gel(phi0, 13) = gen_1;

  phi1 = cgetg(13, t_VEC);
  gel(phi1, 1) = gen_0;
  gel(phi1, 2) = utoineg(0x1bUL);
  gel(phi1, 3) = utoineg(0x5d6UL);
  gel(phi1, 4) = utoineg(0x1c7bUL);
  gel(phi1, 5) = utoi(0x7980UL);
  gel(phi1, 6) = utoi(0x12168UL);
  gel(phi1, 7) = utoineg(0x3528UL);
  gel(phi1, 8) = utoineg(0x6174UL);
  gel(phi1, 9) = utoi(0x2208UL);
  gel(phi1, 10) = utoineg(0x41dUL);
  gel(phi1, 11) = utoi(0x36UL);
  gel(phi1, 12) = gen_m1;

  gel(phi, 1) = phi0;
  gel(phi, 2) = phi1;
  gel(phi, 3) = gen_2; return phi;
}

static GEN
phi_w2w5_j(void)
{
  GEN phi, phi0, phi1;
  phi = cgetg(4, t_VEC);

  phi0 = cgetg(20, t_VEC);
  gel(phi0, 1) = gen_1;
  gel(phi0, 2) = utoineg(0x2aUL);
  gel(phi0, 3) = utoi(0x549UL);
  gel(phi0, 4) = utoineg(0x6530UL);
  gel(phi0, 5) = utoi(0x60504UL);
  gel(phi0, 6) = utoineg(0x3cbbc8UL);
  gel(phi0, 7) = utoi(0x1d1ee74UL);
  gel(phi0, 8) = utoineg(0x7ef9ab0UL);
  gel(phi0, 9) = utoi(0x12b888beUL);
  gel(phi0, 10) = utoineg(0x15fa174cUL);
  gel(phi0, 11) = utoi(0x615d9feUL);
  gel(phi0, 12) = utoi(0xbeca070UL);
  gel(phi0, 13) = utoineg(0x88de74cUL);
  gel(phi0, 14) = utoineg(0x2b3a268UL);
  gel(phi0, 15) = utoi(0x24b3244UL);
  gel(phi0, 16) = utoi(0xb56270UL);
  gel(phi0, 17) = utoi(0x25989UL);
  gel(phi0, 18) = utoi(0x2a6UL);
  gel(phi0, 19) = gen_1;

  phi1 = cgetg(19, t_VEC);
  gel(phi1, 1) = gen_0;
  gel(phi1, 2) = gen_0;
  gel(phi1, 3) = gen_m1;
  gel(phi1, 4) = utoi(0x1eUL);
  gel(phi1, 5) = utoineg(0xffUL);
  gel(phi1, 6) = utoi(0x243UL);
  gel(phi1, 7) = utoineg(0xf3UL);
  gel(phi1, 8) = utoineg(0x5c4UL);
  gel(phi1, 9) = utoi(0x107bUL);
  gel(phi1, 10) = utoineg(0x11b2fUL);
  gel(phi1, 11) = utoi(0x48fa8UL);
  gel(phi1, 12) = utoineg(0x6ff7cUL);
  gel(phi1, 13) = utoi(0x4bf48UL);
  gel(phi1, 14) = utoineg(0x187efUL);
  gel(phi1, 15) = utoi(0x404cUL);
  gel(phi1, 16) = utoineg(0x582UL);
  gel(phi1, 17) = utoi(0x3cUL);
  gel(phi1, 18) = gen_m1;

  gel(phi, 1) = phi0;
  gel(phi, 2) = phi1;
  gel(phi, 3) = utoi(7); return phi;
}

static GEN
phi_w2w7_j(void)
{
  GEN phi, phi0, phi1;
  phi = cgetg(4, t_VEC);

  phi0 = cgetg(26, t_VEC);
  gel(phi0, 1) = gen_1;
  gel(phi0, 2) = utoineg(0x24UL);
  gel(phi0, 3) = utoi(0x4ceUL);
  gel(phi0, 4) = utoineg(0x5d60UL);
  gel(phi0, 5) = utoi(0x62b05UL);
  gel(phi0, 6) = utoineg(0x47be78UL);
  gel(phi0, 7) = utoi(0x2a3880aUL);
  gel(phi0, 8) = utoineg(0x114bccf4UL);
  gel(phi0, 9) = utoi(0x4b95e79aUL);
  gel(phi0, 10) = utoineg(0xe2cfee1cUL);
  gel(phi0, 11) = uu32toi(0x1UL, 0xe43d1126UL);
  gel(phi0, 12) = uu32toineg(0x2UL, 0xf04dc6f8UL);
  gel(phi0, 13) = uu32toi(0x3UL, 0x5384987dUL);
  gel(phi0, 14) = uu32toineg(0x2UL, 0xa5ccbe18UL);
  gel(phi0, 15) = uu32toi(0x1UL, 0x4c52c8a6UL);
  gel(phi0, 16) = utoineg(0x2643fdecUL);
  gel(phi0, 17) = utoineg(0x49f5ab66UL);
  gel(phi0, 18) = utoi(0x33074d3cUL);
  gel(phi0, 19) = utoineg(0x6a3e376UL);
  gel(phi0, 20) = utoineg(0x675aa58UL);
  gel(phi0, 21) = utoi(0x2674005UL);
  gel(phi0, 22) = utoi(0xba5be0UL);
  gel(phi0, 23) = utoi(0x2644eUL);
  gel(phi0, 24) = utoi(0x2acUL);
  gel(phi0, 25) = gen_1;

  phi1 = cgetg(25, t_VEC);
  gel(phi1, 1) = gen_0;
  gel(phi1, 2) = gen_0;
  gel(phi1, 3) = gen_m1;
  gel(phi1, 4) = utoi(0x1cUL);
  gel(phi1, 5) = utoineg(0x10aUL);
  gel(phi1, 6) = utoi(0x3f0UL);
  gel(phi1, 7) = utoineg(0x5d3UL);
  gel(phi1, 8) = utoi(0x3efUL);
  gel(phi1, 9) = utoineg(0x102UL);
  gel(phi1, 10) = utoineg(0x5c8UL);
  gel(phi1, 11) = utoi(0x102fUL);
  gel(phi1, 12) = utoineg(0x13f8aUL);
  gel(phi1, 13) = utoi(0x86538UL);
  gel(phi1, 14) = utoineg(0x1bbd10UL);
  gel(phi1, 15) = utoi(0x3614e8UL);
  gel(phi1, 16) = utoineg(0x42f793UL);
  gel(phi1, 17) = utoi(0x364698UL);
  gel(phi1, 18) = utoineg(0x1c7a10UL);
  gel(phi1, 19) = utoi(0x97cc8UL);
  gel(phi1, 20) = utoineg(0x1fc8aUL);
  gel(phi1, 21) = utoi(0x4210UL);
  gel(phi1, 22) = utoineg(0x524UL);
  gel(phi1, 23) = utoi(0x38UL);
  gel(phi1, 24) = gen_m1;

  gel(phi, 1) = phi0;
  gel(phi, 2) = phi1;
  gel(phi, 3) = utoi(9); return phi;
}

static GEN
phi_w2w13_j(void)
{
  GEN phi, phi0, phi1;
  phi = cgetg(4, t_VEC);

  phi0 = cgetg(44, t_VEC);
  gel(phi0, 1) = gen_1;
  gel(phi0, 2) = utoineg(0x1eUL);
  gel(phi0, 3) = utoi(0x45fUL);
  gel(phi0, 4) = utoineg(0x5590UL);
  gel(phi0, 5) = utoi(0x64407UL);
  gel(phi0, 6) = utoineg(0x53a792UL);
  gel(phi0, 7) = utoi(0x3b21af3UL);
  gel(phi0, 8) = utoineg(0x20d056d0UL);
  gel(phi0, 9) = utoi(0xe02db4a6UL);
  gel(phi0, 10) = uu32toineg(0x4UL, 0xb23400b0UL);
  gel(phi0, 11) = uu32toi(0x14UL, 0x57fbb906UL);
  gel(phi0, 12) = uu32toineg(0x49UL, 0xcf80c00UL);
  gel(phi0, 13) = uu32toi(0xdeUL, 0x84ff421UL);
  gel(phi0, 14) = uu32toineg(0x244UL, 0xc500c156UL);
  gel(phi0, 15) = uu32toi(0x52cUL, 0x79162979UL);
  gel(phi0, 16) = uu32toineg(0xa64UL, 0x8edc5650UL);
  gel(phi0, 17) = uu32toi(0x1289UL, 0x4225bb41UL);
  gel(phi0, 18) = uu32toineg(0x1d89UL, 0x2a15229aUL);
  gel(phi0, 19) = uu32toi(0x2a3eUL, 0x4539f1ebUL);
  gel(phi0, 20) = uu32toineg(0x366aUL, 0xa5ea1130UL);
  gel(phi0, 21) = uu32toi(0x3f47UL, 0xa19fecb4UL);
  gel(phi0, 22) = uu32toineg(0x4282UL, 0x91a3c4a0UL);
  gel(phi0, 23) = uu32toi(0x3f30UL, 0xbaa305b4UL);
  gel(phi0, 24) = uu32toineg(0x3635UL, 0xd11c2530UL);
  gel(phi0, 25) = uu32toi(0x29e2UL, 0x89df27ebUL);
  gel(phi0, 26) = uu32toineg(0x1d03UL, 0x6509d48aUL);
  gel(phi0, 27) = uu32toi(0x11e2UL, 0x272cc601UL);
  gel(phi0, 28) = uu32toineg(0x9b0UL, 0xacd58ff0UL);
  gel(phi0, 29) = uu32toi(0x485UL, 0x608d7db9UL);
  gel(phi0, 30) = uu32toineg(0x1bfUL, 0xa941546UL);
  gel(phi0, 31) = uu32toi(0x82UL, 0x56e48b21UL);
  gel(phi0, 32) = uu32toineg(0x13UL, 0xc36b2340UL);
  gel(phi0, 33) = uu32toineg(0x5UL, 0x6637257aUL);
  gel(phi0, 34) = uu32toi(0x5UL, 0x40f70bd0UL);
  gel(phi0, 35) = uu32toineg(0x1UL, 0xf70842daUL);
  gel(phi0, 36) = utoi(0x53eea5f0UL);
  gel(phi0, 37) = utoi(0xda17bf3UL);
  gel(phi0, 38) = utoineg(0xaf246c2UL);
  gel(phi0, 39) = utoi(0x278f847UL);
  gel(phi0, 40) = utoi(0xbf5550UL);
  gel(phi0, 41) = utoi(0x26f1fUL);
  gel(phi0, 42) = utoi(0x2b2UL);
  gel(phi0, 43) = gen_1;

  phi1 = cgetg(43, t_VEC);
  gel(phi1, 1) = gen_0;
  gel(phi1, 2) = gen_0;
  gel(phi1, 3) = gen_m1;
  gel(phi1, 4) = utoi(0x1aUL);
  gel(phi1, 5) = utoineg(0x111UL);
  gel(phi1, 6) = utoi(0x5e4UL);
  gel(phi1, 7) = utoineg(0x1318UL);
  gel(phi1, 8) = utoi(0x2804UL);
  gel(phi1, 9) = utoineg(0x3cd6UL);
  gel(phi1, 10) = utoi(0x467cUL);
  gel(phi1, 11) = utoineg(0x3cd6UL);
  gel(phi1, 12) = utoi(0x2804UL);
  gel(phi1, 13) = utoineg(0x1318UL);
  gel(phi1, 14) = utoi(0x5e3UL);
  gel(phi1, 15) = utoineg(0x10dUL);
  gel(phi1, 16) = utoineg(0x5ccUL);
  gel(phi1, 17) = utoi(0x100bUL);
  gel(phi1, 18) = utoineg(0x160e1UL);
  gel(phi1, 19) = utoi(0xd2cb0UL);
  gel(phi1, 20) = utoineg(0x4c85fcUL);
  gel(phi1, 21) = utoi(0x137cb98UL);
  gel(phi1, 22) = utoineg(0x3c75568UL);
  gel(phi1, 23) = utoi(0x95c69c8UL);
  gel(phi1, 24) = utoineg(0x131557bcUL);
  gel(phi1, 25) = utoi(0x20aacfd0UL);
  gel(phi1, 26) = utoineg(0x2f9164e6UL);
  gel(phi1, 27) = utoi(0x3b6a5e40UL);
  gel(phi1, 28) = utoineg(0x3ff54344UL);
  gel(phi1, 29) = utoi(0x3b6a9140UL);
  gel(phi1, 30) = utoineg(0x2f927fa6UL);
  gel(phi1, 31) = utoi(0x20ae6450UL);
  gel(phi1, 32) = utoineg(0x131cd87cUL);
  gel(phi1, 33) = utoi(0x967d1e8UL);
  gel(phi1, 34) = utoineg(0x3d48ca8UL);
  gel(phi1, 35) = utoi(0x14333b8UL);
  gel(phi1, 36) = utoineg(0x5406bcUL);
  gel(phi1, 37) = utoi(0x10c130UL);
  gel(phi1, 38) = utoineg(0x27ba1UL);
  gel(phi1, 39) = utoi(0x433cUL);
  gel(phi1, 40) = utoineg(0x4c6UL);
  gel(phi1, 41) = utoi(0x34UL);
  gel(phi1, 42) = gen_m1;

  gel(phi, 1) = phi0;
  gel(phi, 2) = phi1;
  gel(phi, 3) = utoi(15); return phi;
}

static GEN
phi_w3w5_j(void)
{
  GEN phi, phi0, phi1;
  phi = cgetg(4, t_VEC);

  phi0 = cgetg(26, t_VEC);
  gel(phi0, 1) = gen_1;
  gel(phi0, 2) = utoi(0x18UL);
  gel(phi0, 3) = utoi(0xb4UL);
  gel(phi0, 4) = utoineg(0x178UL);
  gel(phi0, 5) = utoineg(0x2d7eUL);
  gel(phi0, 6) = utoineg(0x89b8UL);
  gel(phi0, 7) = utoi(0x35c24UL);
  gel(phi0, 8) = utoi(0x128a18UL);
  gel(phi0, 9) = utoineg(0x12a911UL);
  gel(phi0, 10) = utoineg(0xcc0190UL);
  gel(phi0, 11) = utoi(0x94368UL);
  gel(phi0, 12) = utoi(0x1439d0UL);
  gel(phi0, 13) = utoi(0x96f931cUL);
  gel(phi0, 14) = utoineg(0x1f59ff0UL);
  gel(phi0, 15) = utoi(0x20e7e8UL);
  gel(phi0, 16) = utoineg(0x25fdf150UL);
  gel(phi0, 17) = utoineg(0x7091511UL);
  gel(phi0, 18) = utoi(0x1ef52f8UL);
  gel(phi0, 19) = utoi(0x341f2de4UL);
  gel(phi0, 20) = utoi(0x25d72c28UL);
  gel(phi0, 21) = utoi(0x95d2082UL);
  gel(phi0, 22) = utoi(0xd2d828UL);
  gel(phi0, 23) = utoi(0x281f4UL);
  gel(phi0, 24) = utoi(0x2b8UL);
  gel(phi0, 25) = gen_1;

  phi1 = cgetg(25, t_VEC);
  gel(phi1, 1) = gen_0;
  gel(phi1, 2) = gen_0;
  gel(phi1, 3) = gen_0;
  gel(phi1, 4) = gen_1;
  gel(phi1, 5) = utoi(0xfUL);
  gel(phi1, 6) = utoi(0x2eUL);
  gel(phi1, 7) = utoineg(0x1fUL);
  gel(phi1, 8) = utoineg(0x2dUL);
  gel(phi1, 9) = utoineg(0x5caUL);
  gel(phi1, 10) = utoineg(0x358UL);
  gel(phi1, 11) = utoi(0x2f1cUL);
  gel(phi1, 12) = utoi(0xd8eaUL);
  gel(phi1, 13) = utoineg(0x38c70UL);
  gel(phi1, 14) = utoineg(0x1a964UL);
  gel(phi1, 15) = utoi(0x93512UL);
  gel(phi1, 16) = utoineg(0x58f2UL);
  gel(phi1, 17) = utoineg(0x5af1eUL);
  gel(phi1, 18) = utoi(0x1afb8UL);
  gel(phi1, 19) = utoi(0xc084UL);
  gel(phi1, 20) = utoineg(0x7fcbUL);
  gel(phi1, 21) = utoi(0x1c89UL);
  gel(phi1, 22) = utoineg(0x32aUL);
  gel(phi1, 23) = utoi(0x2dUL);
  gel(phi1, 24) = gen_m1;

  gel(phi, 1) = phi0;
  gel(phi, 2) = phi1;
  gel(phi, 3) = utoi(8); return phi;
}

static GEN
phi_w3w7_j(void)
{
  GEN phi, phi0, phi1;
  phi = cgetg(4, t_VEC);

  phi0 = cgetg(34, t_VEC);
  gel(phi0, 1) = gen_1;
  gel(phi0, 2) = utoineg(0x14UL);
  gel(phi0, 3) = utoi(0x82UL);
  gel(phi0, 4) = utoi(0x1f8UL);
  gel(phi0, 5) = utoineg(0x2a45UL);
  gel(phi0, 6) = utoi(0x9300UL);
  gel(phi0, 7) = utoi(0x32abeUL);
  gel(phi0, 8) = utoineg(0x19c91cUL);
  gel(phi0, 9) = utoi(0xc1ba9UL);
  gel(phi0, 10) = utoi(0x1788f68UL);
  gel(phi0, 11) = utoineg(0x2b1989cUL);
  gel(phi0, 12) = utoineg(0x7a92408UL);
  gel(phi0, 13) = utoi(0x1238d56eUL);
  gel(phi0, 14) = utoi(0x13dd66a0UL);
  gel(phi0, 15) = utoineg(0x2dbedca8UL);
  gel(phi0, 16) = utoineg(0x34282eb8UL);
  gel(phi0, 17) = utoi(0x2c2a54d2UL);
  gel(phi0, 18) = utoi(0x98db81a8UL);
  gel(phi0, 19) = utoineg(0x4088be8UL);
  gel(phi0, 20) = utoineg(0xe424a220UL);
  gel(phi0, 21) = utoineg(0x67bbb232UL);
  gel(phi0, 22) = utoi(0x7dd8bb98UL);
  gel(phi0, 23) = uu32toi(0x1UL, 0xcaff744UL);
  gel(phi0, 24) = utoineg(0x1d46a378UL);
  gel(phi0, 25) = utoineg(0x82fa50f7UL);
  gel(phi0, 26) = utoineg(0x700ef38cUL);
  gel(phi0, 27) = utoi(0x20aa202eUL);
  gel(phi0, 28) = utoi(0x299b3440UL);
  gel(phi0, 29) = utoi(0xa476c4bUL);
  gel(phi0, 30) = utoi(0xd80558UL);
  gel(phi0, 31) = utoi(0x28a32UL);
  gel(phi0, 32) = utoi(0x2bcUL);
  gel(phi0, 33) = gen_1;

  phi1 = cgetg(33, t_VEC);
  gel(phi1, 1) = gen_0;
  gel(phi1, 2) = gen_0;
  gel(phi1, 3) = gen_0;
  gel(phi1, 4) = gen_m1;
  gel(phi1, 5) = utoi(0xeUL);
  gel(phi1, 6) = utoineg(0x31UL);
  gel(phi1, 7) = utoineg(0xeUL);
  gel(phi1, 8) = utoi(0x99UL);
  gel(phi1, 9) = utoineg(0x8UL);
  gel(phi1, 10) = utoineg(0x2eUL);
  gel(phi1, 11) = utoineg(0x5ccUL);
  gel(phi1, 12) = utoi(0x308UL);
  gel(phi1, 13) = utoi(0x2904UL);
  gel(phi1, 14) = utoineg(0x15700UL);
  gel(phi1, 15) = utoineg(0x2b9ecUL);
  gel(phi1, 16) = utoi(0xf0966UL);
  gel(phi1, 17) = utoi(0xb3cc8UL);
  gel(phi1, 18) = utoineg(0x38241cUL);
  gel(phi1, 19) = utoineg(0x8604cUL);
  gel(phi1, 20) = utoi(0x578a64UL);
  gel(phi1, 21) = utoineg(0x11a798UL);
  gel(phi1, 22) = utoineg(0x39c85eUL);
  gel(phi1, 23) = utoi(0x1a5084UL);
  gel(phi1, 24) = utoi(0xcdeb4UL);
  gel(phi1, 25) = utoineg(0xb0364UL);
  gel(phi1, 26) = utoi(0x129d4UL);
  gel(phi1, 27) = utoi(0x126fcUL);
  gel(phi1, 28) = utoineg(0x8649UL);
  gel(phi1, 29) = utoi(0x1aa2UL);
  gel(phi1, 30) = utoineg(0x2dfUL);
  gel(phi1, 31) = utoi(0x2aUL);
  gel(phi1, 32) = gen_m1;

  gel(phi, 1) = phi0;
  gel(phi, 2) = phi1;
  gel(phi, 3) = utoi(10); return phi;
}

static GEN
phi_w3w13_j(void)
{
  GEN phi, phi0, phi1;
  phi = cgetg(4, t_VEC);

  phi0 = cgetg(58, t_VEC);
  gel(phi0, 1) = gen_1;
  gel(phi0, 2) = utoineg(0x10UL);
  gel(phi0, 3) = utoi(0x58UL);
  gel(phi0, 4) = utoi(0x258UL);
  gel(phi0, 5) = utoineg(0x270cUL);
  gel(phi0, 6) = utoi(0x9c00UL);
  gel(phi0, 7) = utoi(0x2b40cUL);
  gel(phi0, 8) = utoineg(0x20e250UL);
  gel(phi0, 9) = utoi(0x4f46baUL);
  gel(phi0, 10) = utoi(0x1869448UL);
  gel(phi0, 11) = utoineg(0xa49ab68UL);
  gel(phi0, 12) = utoi(0x96c7630UL);
  gel(phi0, 13) = utoi(0x4f7e0af6UL);
  gel(phi0, 14) = utoineg(0xea093590UL);
  gel(phi0, 15) = utoineg(0x6735bc50UL);
  gel(phi0, 16) = uu32toi(0x5UL, 0x971a2e08UL);
  gel(phi0, 17) = uu32toineg(0x6UL, 0x29c9d965UL);
  gel(phi0, 18) = uu32toineg(0xdUL, 0xeb9aa360UL);
  gel(phi0, 19) = uu32toi(0x26UL, 0xe9c0584UL);
  gel(phi0, 20) = uu32toineg(0x1UL, 0xb0cadce8UL);
  gel(phi0, 21) = uu32toineg(0x62UL, 0x73586014UL);
  gel(phi0, 22) = uu32toi(0x66UL, 0xaf672e38UL);
  gel(phi0, 23) = uu32toi(0x6bUL, 0x93c28cdcUL);
  gel(phi0, 24) = uu32toineg(0x11eUL, 0x4f633080UL);
  gel(phi0, 25) = uu32toi(0x3cUL, 0xcc42461bUL);
  gel(phi0, 26) = uu32toi(0x17bUL, 0xdec0a78UL);
  gel(phi0, 27) = uu32toineg(0x166UL, 0x910d8bd0UL);
  gel(phi0, 28) = uu32toineg(0xd4UL, 0x47873030UL);
  gel(phi0, 29) = uu32toi(0x204UL, 0x811828baUL);
  gel(phi0, 30) = uu32toineg(0x50UL, 0x5d713960UL);
  gel(phi0, 31) = uu32toineg(0x198UL, 0xa27e42b0UL);
  gel(phi0, 32) = uu32toi(0xe1UL, 0x25685138UL);
  gel(phi0, 33) = uu32toi(0xe3UL, 0xaa5774bbUL);
  gel(phi0, 34) = uu32toineg(0xcfUL, 0x392a9a00UL);
  gel(phi0, 35) = uu32toineg(0x81UL, 0xfb334d04UL);
  gel(phi0, 36) = uu32toi(0xabUL, 0x59594a68UL);
  gel(phi0, 37) = uu32toi(0x42UL, 0x356993acUL);
  gel(phi0, 38) = uu32toineg(0x86UL, 0x307ba678UL);
  gel(phi0, 39) = uu32toineg(0xbUL, 0x7a9e59dcUL);
  gel(phi0, 40) = uu32toi(0x4cUL, 0x27935f20UL);
  gel(phi0, 41) = uu32toineg(0x2UL, 0xe0ac9045UL);
  gel(phi0, 42) = uu32toineg(0x24UL, 0x14495758UL);
  gel(phi0, 43) = utoi(0x20973410UL);
  gel(phi0, 44) = uu32toi(0x13UL, 0x99ff4e00UL);
  gel(phi0, 45) = uu32toineg(0x1UL, 0xa710d34aUL);
  gel(phi0, 46) = uu32toineg(0x7UL, 0xfe5405c0UL);
  gel(phi0, 47) = uu32toi(0x1UL, 0xcdee0f8UL);
  gel(phi0, 48) = uu32toi(0x2UL, 0x660c92a8UL);
  gel(phi0, 49) = utoi(0x3f13a35aUL);
  gel(phi0, 50) = utoineg(0xe4eb4ba0UL);
  gel(phi0, 51) = utoineg(0x6420f4UL);
  gel(phi0, 52) = utoi(0x2c624370UL);
  gel(phi0, 53) = utoi(0xb31b814UL);
  gel(phi0, 54) = utoi(0xdd3ad8UL);
  gel(phi0, 55) = utoi(0x29278UL);
  gel(phi0, 56) = utoi(0x2c0UL);
  gel(phi0, 57) = gen_1;

  phi1 = cgetg(57, t_VEC);
  gel(phi1, 1) = gen_0;
  gel(phi1, 2) = gen_0;
  gel(phi1, 3) = gen_0;
  gel(phi1, 4) = gen_m1;
  gel(phi1, 5) = utoi(0xdUL);
  gel(phi1, 6) = utoineg(0x34UL);
  gel(phi1, 7) = utoi(0x1aUL);
  gel(phi1, 8) = utoi(0xf7UL);
  gel(phi1, 9) = utoineg(0x16cUL);
  gel(phi1, 10) = utoineg(0xddUL);
  gel(phi1, 11) = utoi(0x28aUL);
  gel(phi1, 12) = utoineg(0xddUL);
  gel(phi1, 13) = utoineg(0x16cUL);
  gel(phi1, 14) = utoi(0xf6UL);
  gel(phi1, 15) = utoi(0x1dUL);
  gel(phi1, 16) = utoineg(0x31UL);
  gel(phi1, 17) = utoineg(0x5ceUL);
  gel(phi1, 18) = utoi(0x2e4UL);
  gel(phi1, 19) = utoi(0x252cUL);
  gel(phi1, 20) = utoineg(0x1b34cUL);
  gel(phi1, 21) = utoi(0xaf80UL);
  gel(phi1, 22) = utoi(0x1cc5f9UL);
  gel(phi1, 23) = utoineg(0x3e1aa5UL);
  gel(phi1, 24) = utoineg(0x86d17aUL);
  gel(phi1, 25) = utoi(0x2427264UL);
  gel(phi1, 26) = utoineg(0x691c1fUL);
  gel(phi1, 27) = utoineg(0x862ad4eUL);
  gel(phi1, 28) = utoi(0xab21e1fUL);
  gel(phi1, 29) = utoi(0xbc19ddcUL);
  gel(phi1, 30) = utoineg(0x24331db8UL);
  gel(phi1, 31) = utoi(0x972c105UL);
  gel(phi1, 32) = utoi(0x363d7107UL);
  gel(phi1, 33) = utoineg(0x39696450UL);
  gel(phi1, 34) = utoineg(0x1bce7c48UL);
  gel(phi1, 35) = utoi(0x552ecba0UL);
  gel(phi1, 36) = utoineg(0x1c7771b8UL);
  gel(phi1, 37) = utoineg(0x393029b8UL);
  gel(phi1, 38) = utoi(0x3755be97UL);
  gel(phi1, 39) = utoi(0x83402a9UL);
  gel(phi1, 40) = utoineg(0x24d5be62UL);
  gel(phi1, 41) = utoi(0xdb6d90aUL);
  gel(phi1, 42) = utoi(0xa0ef177UL);
  gel(phi1, 43) = utoineg(0x99ff162UL);
  gel(phi1, 44) = utoi(0xb09e27UL);
  gel(phi1, 45) = utoi(0x26a7adcUL);
  gel(phi1, 46) = utoineg(0x116e2fcUL);
  gel(phi1, 47) = utoineg(0x1383b5UL);
  gel(phi1, 48) = utoi(0x35a9e7UL);
  gel(phi1, 49) = utoineg(0x1082a0UL);
  gel(phi1, 50) = utoineg(0x4696UL);
  gel(phi1, 51) = utoi(0x19f98UL);
  gel(phi1, 52) = utoineg(0x8bb3UL);
  gel(phi1, 53) = utoi(0x18bbUL);
  gel(phi1, 54) = utoineg(0x297UL);
  gel(phi1, 55) = utoi(0x27UL);
  gel(phi1, 56) = gen_m1;

  gel(phi, 1) = phi0;
  gel(phi, 2) = phi1;
  gel(phi, 3) = utoi(16); return phi;
}

static GEN
phi_w5w7_j(void)
{
  GEN phi, phi0, phi1;
  phi = cgetg(4, t_VEC);

  phi0 = cgetg(50, t_VEC);
  gel(phi0, 1) = gen_1;
  gel(phi0, 2) = utoi(0xcUL);
  gel(phi0, 3) = utoi(0x2aUL);
  gel(phi0, 4) = utoi(0x10UL);
  gel(phi0, 5) = utoineg(0x69UL);
  gel(phi0, 6) = utoineg(0x318UL);
  gel(phi0, 7) = utoineg(0x148aUL);
  gel(phi0, 8) = utoineg(0x17c4UL);
  gel(phi0, 9) = utoi(0x1a73UL);
  gel(phi0, 10) = gen_0;
  gel(phi0, 11) = utoi(0x338a0UL);
  gel(phi0, 12) = utoi(0x61698UL);
  gel(phi0, 13) = utoineg(0x96e8UL);
  gel(phi0, 14) = utoi(0x140910UL);
  gel(phi0, 15) = utoineg(0x45f6b4UL);
  gel(phi0, 16) = utoineg(0x309f50UL);
  gel(phi0, 17) = utoineg(0xef9f8bUL);
  gel(phi0, 18) = utoineg(0x283167cUL);
  gel(phi0, 19) = utoi(0x625e20aUL);
  gel(phi0, 20) = utoineg(0x16186350UL);
  gel(phi0, 21) = utoi(0x46861281UL);
  gel(phi0, 22) = utoineg(0x754b96a0UL);
  gel(phi0, 23) = uu32toi(0x1UL, 0x421ca02aUL);
  gel(phi0, 24) = uu32toineg(0x2UL, 0xdb76a5cUL);
  gel(phi0, 25) = uu32toi(0x4UL, 0xf6afd8eUL);
  gel(phi0, 26) = uu32toineg(0x6UL, 0xaafd3cb4UL);
  gel(phi0, 27) = uu32toi(0x8UL, 0xda2539caUL);
  gel(phi0, 28) = uu32toineg(0xfUL, 0x84343790UL);
  gel(phi0, 29) = uu32toi(0xfUL, 0x914ff421UL);
  gel(phi0, 30) = uu32toineg(0x19UL, 0x3c123950UL);
  gel(phi0, 31) = uu32toi(0x15UL, 0x381f722aUL);
  gel(phi0, 32) = uu32toineg(0x15UL, 0xe01c0c24UL);
  gel(phi0, 33) = uu32toi(0x19UL, 0x3360b375UL);
  gel(phi0, 34) = utoineg(0x59fda9c0UL);
  gel(phi0, 35) = uu32toi(0x20UL, 0xff55024cUL);
  gel(phi0, 36) = uu32toi(0x16UL, 0xcc600800UL);
  gel(phi0, 37) = uu32toi(0x24UL, 0x1879c898UL);
  gel(phi0, 38) = uu32toi(0x1cUL, 0x37f97498UL);
  gel(phi0, 39) = uu32toi(0x19UL, 0x39ec4b60UL);
  gel(phi0, 40) = uu32toi(0x10UL, 0x52c660d0UL);
  gel(phi0, 41) = uu32toi(0x9UL, 0xcab00333UL);
  gel(phi0, 42) = uu32toi(0x4UL, 0x7fe69be4UL);
  gel(phi0, 43) = uu32toi(0x1UL, 0xa0c6f116UL);
  gel(phi0, 44) = utoi(0x69244638UL);
  gel(phi0, 45) = utoi(0xed560f7UL);
  gel(phi0, 46) = utoi(0xe7b660UL);
  gel(phi0, 47) = utoi(0x29d8aUL);
  gel(phi0, 48) = utoi(0x2c4UL);
  gel(phi0, 49) = gen_1;

  phi1 = cgetg(49, t_VEC);
  gel(phi1, 1) = gen_0;
  gel(phi1, 2) = gen_0;
  gel(phi1, 3) = gen_0;
  gel(phi1, 4) = gen_0;
  gel(phi1, 5) = gen_0;
  gel(phi1, 6) = gen_1;
  gel(phi1, 7) = utoi(0x7UL);
  gel(phi1, 8) = utoi(0x8UL);
  gel(phi1, 9) = utoineg(0x9UL);
  gel(phi1, 10) = gen_0;
  gel(phi1, 11) = utoineg(0x13UL);
  gel(phi1, 12) = utoineg(0x7UL);
  gel(phi1, 13) = utoineg(0x5ceUL);
  gel(phi1, 14) = utoineg(0xb0UL);
  gel(phi1, 15) = utoi(0x460UL);
  gel(phi1, 16) = utoineg(0x194bUL);
  gel(phi1, 17) = utoi(0x87c3UL);
  gel(phi1, 18) = utoi(0x3cdeUL);
  gel(phi1, 19) = utoineg(0xd683UL);
  gel(phi1, 20) = utoi(0x6099bUL);
  gel(phi1, 21) = utoineg(0x111ea8UL);
  gel(phi1, 22) = utoi(0xfa113UL);
  gel(phi1, 23) = utoineg(0x1a6561UL);
  gel(phi1, 24) = utoineg(0x1e997UL);
  gel(phi1, 25) = utoi(0x214e54UL);
  gel(phi1, 26) = utoineg(0x29c3f4UL);
  gel(phi1, 27) = utoi(0x67e102UL);
  gel(phi1, 28) = utoineg(0x227eaaUL);
  gel(phi1, 29) = utoi(0x191d10UL);
  gel(phi1, 30) = utoi(0x1a9cd5UL);
  gel(phi1, 31) = utoineg(0x58386fUL);
  gel(phi1, 32) = utoi(0x2e49f6UL);
  gel(phi1, 33) = utoineg(0x31194bUL);
  gel(phi1, 34) = utoi(0x9e07aUL);
  gel(phi1, 35) = utoi(0x260d59UL);
  gel(phi1, 36) = utoineg(0x189921UL);
  gel(phi1, 37) = utoi(0xeca4aUL);
  gel(phi1, 38) = utoineg(0xa3d9cUL);
  gel(phi1, 39) = utoineg(0x426daUL);
  gel(phi1, 40) = utoi(0x91875UL);
  gel(phi1, 41) = utoineg(0x3b55bUL);
  gel(phi1, 42) = utoineg(0x56f4UL);
  gel(phi1, 43) = utoi(0xcd1bUL);
  gel(phi1, 44) = utoineg(0x5159UL);
  gel(phi1, 45) = utoi(0x10f4UL);
  gel(phi1, 46) = utoineg(0x20dUL);
  gel(phi1, 47) = utoi(0x23UL);
  gel(phi1, 48) = gen_m1;

  gel(phi, 1) = phi0;
  gel(phi, 2) = phi1;
  gel(phi, 3) = utoi(12); return phi;
}

GEN
double_eta_raw(long inv)
{
  switch (inv) {
    case INV_W2W3:
    case INV_W2W3E2: return phi_w2w3_j();
    case INV_W3W3:
    case INV_W3W3E2: return phi_w3w3_j();
    case INV_W2W5:
    case INV_W2W5E2: return phi_w2w5_j();
    case INV_W2W7:
    case INV_W2W7E2: return phi_w2w7_j();
    case INV_W3W5:   return phi_w3w5_j();
    case INV_W3W7:   return phi_w3w7_j();
    case INV_W2W13:  return phi_w2w13_j();
    case INV_W3W13:  return phi_w3w13_j();
    case INV_W5W7:   return phi_w5w7_j();
    default: pari_err_BUG("double_eta_raw"); return NULL;/*LCOV_EXCL_LINE*/
  }
}

/**
 * SECTION: Select discriminant for given modpoly level.
 */

/* require an L1, useful for multi-threading */
#define MODPOLY_USE_L1    1
/* no bound on L1 other than the fixed bound MAX_L1 - needed to
 * handle small L for certain invariants (but not for j) */
#define MODPOLY_NO_MAX_L1 2
/* don't use any auxilliary primes - needed to handle small L for
 * certain invariants (but not for j) */
#define MODPOLY_NO_AUX_L  4
#define MODPOLY_IGNORE_SPARSE_FACTOR 8

INLINE double
modpoly_height_bound(long L, long inv)
{
  double nbits, nbits2;
  double c;
  long hf;

  /* proven bound (in bits), derived from: 6l*log(l)+16*l+13*sqrt(l)*log(l) */
  nbits = 6.0*L*log2(L)+16/M_LN2*L+8.0*sqrt((double)L)*log2(L);
  /* alternative proven bound (in bits), derived from: 6l*log(l)+17*l */
  nbits2 = 6.0*L*log2(L)+17/M_LN2*L;
  if ( nbits2 < nbits ) nbits = nbits2;
  hf = modinv_height_factor(inv);
  if (hf > 1) {
   /* IMPORTANT: when dividing by the height factor, we only want to reduce
   terms related to the bound on j (the roots of Phi_l(X,y)), not terms arising
   from binomial coefficients. These arise in lemmas 2 and 3 of the height
   bound paper, terms of (log 2)*L and 2.085*(L+1) which we convert here to
   binary logs */
    /* Massive overestimate: if you care about speed, determine a good height
     * bound empirically as done for INV_F below */
    nbits2 = nbits - 4.01*L -3.0;
    nbits = nbits2/hf + 4.01*L + 3.0;
  }
  if (inv == INV_F) {
    if (L < 30) c = 45;
    else if (L < 100) c = 36;
    else if (L < 300) c = 32;
    else if (L < 600) c = 26;
    else if (L < 1200) c = 24;
    else if (L < 2400) c = 22;
    else c = 20;
    nbits = (6.0*L*log2(L) + c*L)/hf;
  }
  return nbits;
}

/* small enough to write the factorization of a smooth in a BIL bit integer */
#define SMOOTH_PRIMES  ((BITS_IN_LONG >> 1) - 1)

#define MAX_ATKIN 255

/* Must have primes at least up to MAX_ATKIN */
static const long PRIMES[] = {
    0,   2,   3,   5,   7,  11,  13,  17,  19,  23,
   29,  31,  37,  41,  43,  47,  53,  59,  61,  67,
   71,  73,  79,  83,  89,  97, 101, 103, 107, 109,
  113, 127, 131, 137, 139, 149, 151, 157, 163, 167,
  173, 179, 181, 191, 193, 197, 199, 211, 223, 227,
  229, 233, 239, 241, 251, 257, 263, 269, 271, 277
};

#define MAX_L1      255

typedef struct D_entry_struct {
  ulong m;
  long D, h;
} D_entry;

/* Returns a form that generates the classes of norm p^2 in cl(p^2D)
 * (i.e. one with order p-1), where p is an odd prime that splits in D
 * and does not divide its conductor (but this is not verified) */
INLINE GEN
qform_primeform2(long p, long D)
{
  pari_sp ltop = avma, av;
  GEN M;
  register long k;

  M = factor_pn_1(stoi(p), 1);
  av = avma;
  for (k = D & 1; k <= p; k += 2)
  {
    GEN Q;
    long ord, a, b, c = (k * k - D) / 4;

    if (!(c % p)) continue;
    a = p * p;
    b = k * p;
    Q = redimag(mkqfis(a, b, c));
    /* TODO: How do we know that Q has order dividing p - 1? If we don't, then
     * the call to gen_order should be replaced with a call to something with
     * fastorder semantics (i.e. return 0 if ord(Q) \ndiv M). */
    ord = itos(qfi_order(Q, M));
    if (ord == p - 1) {
      /* TODO: This check that gen_order returned the correct result should be
       * removed when gen_order is replaced with fastorder semantics. */
      GEN tst = gpowgs(Q, p - 1);
      if (qfb_equal1(tst)) { avma = ltop; return mkqfis(a, b, c); }
        break;
    }
    avma = av;
  }
  avma = ltop; return NULL;
}

/* Let n = #cl(D); return x such that [L0]^x = [L] in cl(D), or -1 if x was
 * not found */
INLINE long
primeform_discrete_log(long L0, long L, long n, long D)
{
  pari_sp av = avma;
  GEN X, Q, R, DD = stoi(D);
  Q = primeform_u(DD, L0);
  R = primeform_u(DD, L);
  X = qfi_Shanks(R, Q, n);
  avma = av; return X? itos(X): -1;
}

/* Return the norm of a class group generator appropriate for a discriminant
 * that will be used to calculate the modular polynomial of level L and
 * invariant inv.  Don't consider norms less than initial_L0 */
static long
select_L0(long L, long inv, long initial_L0)
{
  long L0, modinv_N = modinv_level(inv);

  if (modinv_N % L == 0) pari_err_BUG("select_L0");

  /* TODO: Clean up these anomolous L0 choices */

  /* I've no idea why the discriminant-finding code fails with L0=5
   * when L=19 and L=29, nor why L0=7 and L0=11 don't work for L=19
   * either, nor why this happens for the otherwise unrelated
   * invariants Weber-f and (2,3) double-eta. */
  if (inv == INV_W3W3E2 && L == 5) return 2;

  if (inv == INV_F || inv == INV_F2 || inv == INV_F4 || inv == INV_F8
      || inv == INV_W2W3 || inv == INV_W2W3E2
      || inv == INV_W3W3 /* || inv == INV_W3W3E2 */) {
    if (L == 19) return 13;
    else if (L == 29 || L == 5) return 7;
    return 5;
  }
  if ((inv == INV_W2W5 || inv == INV_W2W5E2)
      && (L == 7 || L == 19)) return 13;
  if ((inv == INV_W2W7 || inv == INV_W2W7E2)
      && L == 11) return 13;
  if (inv == INV_W3W5) {
    if (L == 7) return 13;
    else if (L == 17) return 7;
  }
  if (inv == INV_W3W7) {
    if (L == 29 || L == 101) return 11;
    if (L == 11 || L == 19) return 13;
  }
  if (inv == INV_W5W7 && L == 17) return 3;

  /* L0 = smallest small prime different from L that doesn't divide modinv_N */
  for (L0 = unextprime(initial_L0 + 1);
       L0 == L || modinv_N % L0 == 0;
       L0 = unextprime(L0 + 1))
    ;
  return L0;
}

/* Return the order of [L]^n in cl(D), where #cl(D) = ord. */
INLINE long
primeform_exp_order(long L, long n, long D, long ord)
{
  pari_sp av = avma;
  GEN Q = gpowgs(primeform_u(stoi(D), L), n);
  long m = itos(qfi_order(Q, Z_factor(stoi(ord))));
  avma = av; return m;
}

/* If an ideal of norm modinv_deg is equivalent to an ideal of norm L0, we
 * have an orientation ambiguity that we need to avoid. Note that we need to
 * check all the possibilities (up to 8), but we can cheaply check inverses
 * (so at most 2) */
static long
orientation_ambiguity(long D1, long L0, long modinv_p1, long modinv_p2, long modinv_N)
{
  pari_sp av = avma;
  long ambiguity = 0;
  GEN D = stoi(D1), Q1 = primeform_u(D, modinv_p1), Q2 = NULL;

  if (modinv_p2 > 1)
  {
    if (modinv_p1 == modinv_p2) Q1 = gsqr(Q1);
    else
    {
      GEN P2 = primeform_u(D, modinv_p2);
      GEN Q = gsqr(P2), R = gsqr(Q1);
      /* check that p1^2 != p2^{+/-2}, since this leads to
       * ambiguities when converting j's to f's */
      if (equalii(gel(Q,1), gel(R,1)) && absequalii(gel(Q,2), gel(R,2)))
      {
        dbg_printf(3)("Bad D=%ld, a^2=b^2 problem between modinv_p1=%ld and modinv_p2=%ld\n",
                      D1, modinv_p1, modinv_p2);
        ambiguity = 1;
      }
      else
      { /* generate both p1*p2 and p1*p2^{-1} */
        Q2 = gmul(Q1, P2);
        P2 = ginv(P2);
        Q1 = gmul(Q1, P2);
      }
    }
  }
  if (!ambiguity)
  {
    GEN P = gsqr(primeform_u(D, L0));
    if (equalii(gel(P,1), gel(Q1,1))
        || (modinv_p2 && modinv_p1 != modinv_p2
                      && equalii(gel(P,1), gel(Q2,1)))) {
      dbg_printf(3)("Bad D=%ld, a=b^{+/-2} problem between modinv_N=%ld and L0=%ld\n",
                    D1, modinv_N, L0);
      ambiguity = 1;
    }
  }
  avma = av; return ambiguity;
}

static long
check_generators(
  long *n1_, long *m_,
  long D, long h, long n, long subgrp_sz, long L0, long L1)
{
  long n1, m = primeform_exp_order(L0, n, D, h);
  if (m_) *m_ = m;
  n1 = n * m;
  if (!n1) pari_err_BUG("check_generators");
  *n1_ = n1;
  if (n1 < subgrp_sz/2 || ( ! L1 && n1 < subgrp_sz))  {
    dbg_printf(3)("Bad D1=%ld with n1=%ld, h1=%ld, L1=%ld: "
                  "L0 and L1 don't span subgroup of size d in cl(D1)\n",
                  D, n, h, L1);
    return 0;
  }
  if (n1 < subgrp_sz && ! (n1 & 1)) {
    int res;
    /* check whether L1 is generated by L0, use the fact that it has order 2 */
    pari_sp av = avma;
    GEN D1 = stoi(D);
    GEN Q = gpowgs(primeform_u(D1, L0), n1 / 2);
    res = gequal(Q, redimag(primeform_u(D1, L1)));
    avma = av;
    if (res) {
      dbg_printf(3)("Bad D1=%ld, with n1=%ld, h1=%ld, L1=%ld: "
                    "L1 generated by L0 in cl(D1)\n", D, n, h, L1);
      return 0;
    }
  }
  return 1;
}

/* Calculate solutions (p, t) to the norm equation
 *   4 p = t^2 - v^2 L^2 D   (*)
 * corresponding to the descriminant described by Dinfo.
 *
 * INPUT:
 * - max: length of primes and traces
 * - xprimes: p to exclude from primes (if they arise)
 * - xcnt: length of xprimes
 * - minbits: sum of log2(p) must be larger than this
 * - Dinfo: discriminant, invariant and L for which we seek solutions to (*)
 *
 * OUTPUT:
 * - primes: array of p in (*)
 * - traces: array of t in (*)
 * - totbits: sum of log2(p) for p in primes.
 *
 * RETURN:
 * - the number of primes and traces found (these are always the same).
 *
 * NOTE: primes and traces are both NULL or both non-NULL.
 * xprimes can be zero, in which case it is treated as empty. */
static long
modpoly_pickD_primes(
  ulong *primes, ulong *traces, long max, ulong *xprimes, long xcnt,
  long *totbits, long minbits, disc_info *Dinfo)
{
  double bits;
  long D, m, n, vcnt, pfilter, one_prime, inv;
  ulong maxp;
  register ulong a1, a2, v, t, p, a1_start, a1_delta, L0, L1, L, absD;
  ulong FF_BITS = BITS_IN_LONG - 2; /* BITS_IN_LONG - NAIL_BITS */

  D = Dinfo->D1; absD = -D;
  L0 = Dinfo->L0;
  L1 = Dinfo->L1;
  L = Dinfo->L;
  inv = Dinfo->inv;

  /* make sure pfilter and D don't preclude the possibility of p=(t^2-v^2D)/4 being prime */
  pfilter = modinv_pfilter(inv);
  if ((pfilter & IQ_FILTER_1MOD3) && ! (D % 3)) return 0;
  if ((pfilter & IQ_FILTER_1MOD4) && ! (D & 0xF)) return 0;

  /* Naively estimate the number of primes satisfying 4p=t^2-L^2D with
   * t=2 mod L and pfilter. This is roughly
   * #{t: t^2 < max p and t=2 mod L} / pi(max p) * filter_density,
   * where filter_density is 1, 2, or 4 depending on pfilter.  If this quantity
   * is already more than twice the number of bits we need, assume that,
   * barring some obstruction, we should have no problem getting enough primes.
   * In this case we just verify we can get one prime (which should always be
   * true, assuming we chose D properly). */
  one_prime = 0;
  *totbits = 0;
  if (max <= 1 && ! one_prime) {
    p = ((pfilter & IQ_FILTER_1MOD3) ? 2 : 1) * ((pfilter & IQ_FILTER_1MOD4) ? 2 : 1);
    one_prime = (1UL << ((FF_BITS+1)/2)) * (log2(L*L*(-D))-1)
        > p*L*minbits*FF_BITS*M_LN2;
    if (one_prime) *totbits = minbits+1;   /* lie */
  }

  m = n = 0;
  bits = 0.0;
  maxp = 0;
  for (v = 1; v < 100 && bits < minbits; v++) {
    /* Don't allow v dividing the conductor. */
    if (ugcd(absD, v) != 1) continue;
    /* Avoid v dividing the level. */
    if (v > 2 && modinv_is_double_eta(inv) && ugcd(modinv_level(inv), v) != 1)
      continue;
    /* can't get odd p with D=1 mod 8 unless v is even */
    if ((v & 1) && (D & 7) == 1) continue;
    /* disallow 4 | v for L0=2 (removing this restriction is costly) */
    if (L0 == 2 && !(v & 3)) continue;
    /* can't get p=3mod4 if v^2D is 0 mod 16 */
    if ((pfilter & IQ_FILTER_1MOD4) && !((v*v*D) & 0xF)) continue;
    if ((pfilter & IQ_FILTER_1MOD3) && !(v%3) ) continue;
    /* avoid L0-volcanos with non-zero height */
    if (L0 != 2 && ! (v % L0)) continue;
    /* ditto for L1 */
    if (L1 && !(v % L1)) continue;
    vcnt = 0;
    if ((v*v*absD)/4 > (1L<<FF_BITS)/(L*L)) break;
    if (both_odd(v,D)) {
      a1_start = 1;
      a1_delta = 2;
    } else {
      a1_start = ((v*v*D) & 7)? 2: 0;
      a1_delta = 4;
    }
    for (a1 = a1_start; bits < minbits; a1 += a1_delta) {
      a2 = (a1*a1 + v*v*absD) >> 2;
      if (!(a2 % L)) continue;
      t = a1*L + 2;
      p = a2*L*L + t - 1;
      /* double check calculation just in case of overflow or other weirdness */
      if (!odd(p) || t*t + v*v*L*L*absD != 4*p)
        pari_err_BUG("modpoly_pickD_primes");
      if (p > (1UL<<FF_BITS)) break;
      if (xprimes) {
        while (m < xcnt && xprimes[m] < p) m++;
        if (m < xcnt && p == xprimes[m]) {
          dbg_printf(1)("skipping duplicate prime %ld\n", p);
          continue;
        }
      }
      if (!uisprime(p) || !modinv_good_prime(inv, p)) continue;
      if (primes) {
        if (n >= max) goto done;
        /* TODO: Implement test to filter primes that lead to
         * L-valuation != 2 */
        primes[n] = p;
        traces[n] = t;
      }
      n++;
      vcnt++;
      bits += log2(p);
      if (p > maxp) maxp = p;
      if (one_prime) goto done;
    }
    if (vcnt)
      dbg_printf(3)("%ld primes with v=%ld, maxp=%ld (%.2f bits)\n",
                 vcnt, v, maxp, log2(maxp));
  }
done:
  if (!n) {
    dbg_printf(3)("check_primes failed completely for D=%ld\n", D);
    return 0;
  }
  dbg_printf(3)("D=%ld: Found %ld primes totalling %0.2f of %ld bits\n",
             D, n, bits, minbits);
  if (!*totbits) *totbits = (long)bits;
  return n;
}

#define MAX_VOLCANO_FLOOR_SIZE 100000000

static long
calc_primes_for_discriminants(disc_info Ds[], long Dcnt, long L, long minbits)
{
  pari_sp av = avma;
  long i, j, k, m, n, D1, pcnt, totbits;
  ulong *primes, *Dprimes, *Dtraces;

  /* D1 is the discriminant with smallest absolute value among those we found */
  D1 = Ds[0].D1;
  for (i = 1; i < Dcnt; i++)
    if (Ds[i].D1 > D1) D1 = Ds[i].D1;

  /* n is an upper bound on the number of primes we might get. */
  n = ceil(minbits / (log2(L * L * (-D1)) - 2)) + 1;
  primes = (ulong *) stack_malloc(n * sizeof(*primes));
  Dprimes = (ulong *) stack_malloc(n * sizeof(*Dprimes));
  Dtraces = (ulong *) stack_malloc(n * sizeof(*Dtraces));
  for (i = 0, totbits = 0, pcnt = 0; i < Dcnt && totbits < minbits; i++)
  {
    long np = modpoly_pickD_primes(Dprimes, Dtraces, n, primes, pcnt,
                                   &Ds[i].bits, minbits - totbits, Ds + i);
    ulong *T = (ulong *)newblock(2*np);
    Ds[i].nprimes = np;
    Ds[i].primes = T;    memcpy(T   , Dprimes, np * sizeof(*Dprimes));
    Ds[i].traces = T+np; memcpy(T+np, Dtraces, np * sizeof(*Dtraces));

    totbits += Ds[i].bits;
    pcnt += np;

    if (totbits >= minbits || i == Dcnt - 1) { Dcnt = i + 1; break; }
    /* merge lists */
    for (j = pcnt - np - 1, k = np - 1, m = pcnt - 1; m >= 0; m--) {
      if (k >= 0) {
        if (j >= 0 && primes[j] > Dprimes[k])
          primes[m] = primes[j--];
        else
          primes[m] = Dprimes[k--];
      } else {
        primes[m] = primes[j--];
      }
    }
  }
  if (totbits < minbits) {
    dbg_printf(1)("Only obtained %ld of %ld bits using %ld discriminants\n",
                  totbits, minbits, Dcnt);
    for (i = 0; i < Dcnt; i++) killblock((GEN)Ds[i].primes);
    Dcnt = 0;
  }
  avma = av; return Dcnt;
}

/* Select discriminant(s) to use when calculating the modular
 * polynomial of level L and invariant inv.
 *
 * INPUT:
 * - L: level of modular polynomial (must be odd)
 * - inv: invariant of modular polynomial
 * - L0: result of select_L0(L, inv)
 * - minbits: height of modular polynomial
 * - flags: see below
 * - tab: result of scanD0(L0)
 * - tablen: length of tab
 *
 * OUTPUT:
 * - Ds: the selected discriminant(s)
 *
 * RETURN:
 * - the number of Ds found
 *
 * The flags parameter is constructed by ORing zero or more of the
 * following values:
 * - MODPOLY_USE_L1: force use of second class group generator
 * - MODPOLY_NO_AUX_L: don't use auxillary class group elements
 * - MODPOLY_IGNORE_SPARSE_FACTOR: obtain D for which h(D) > L + 1
 *   rather than h(D) > (L + 1)/s */
static long
modpoly_pickD(disc_info Ds[MODPOLY_MAX_DCNT], long L, long inv,
  long L0, long max_L1, long minbits, long flags, D_entry *tab, long tablen)
{
  pari_sp ltop = avma, btop;
  disc_info Dinfo;
  pari_timer T;
  long modinv_p1, modinv_p2; /* const after next line */
  const long modinv_deg = modinv_degree(&modinv_p1, &modinv_p2, inv);
  const long pfilter = modinv_pfilter(inv), modinv_N = modinv_level(inv);
  long i, k, use_L1, Dcnt, D0_i, d, cost, enum_cost, best_cost, totbits;
  const double L_bits = log2(L);

  if (!odd(L)) pari_err_BUG("modpoly_pickD");

  timer_start(&T);
  if (flags & MODPOLY_IGNORE_SPARSE_FACTOR) d = L+2;
  else d = ceildivuu(L+1, modinv_sparse_factor(inv)) + 1;

  /* Now set level to 0 unless we will need to compute N-isogenies */
  dbg_printf(1)("Using L0=%ld for L=%ld, d=%ld, modinv_N=%ld, modinv_deg=%ld\n",
                L0, L, d, modinv_N, modinv_deg);

  /* We use L1 if (L0|L) == 1 or if we are forced to by flags. */
  use_L1 = (kross(L0,L) > 0 || (flags & MODPOLY_USE_L1));

  Dcnt = best_cost = totbits = 0;
  dbg_printf(3)("use_L1=%ld\n", use_L1);
  dbg_printf(3)("minbits = %ld\n", minbits);

  /* Iterate over the fundamental discriminants for L0 */
  for (D0_i = 0; D0_i < tablen; D0_i++)
  {
    D_entry D0_entry = tab[D0_i];
    long m, n0, h0, deg, L1, H_cost, twofactor, D0 = D0_entry.D;
    double D0_bits;
    if (! modinv_good_disc(inv, D0)) continue;
    dbg_printf(3)("D0=%ld\n", D0);
    /* don't allow either modinv_p1 or modinv_p2 to ramify */
    if (kross(D0, L) < 1
        || (modinv_p1 > 1 && kross(D0, modinv_p1) < 1)
        || (modinv_p2 > 1 && kross(D0, modinv_p2) < 1)) {
      dbg_printf(3)("Bad D0=%ld due to non-split L or ramified level\n", D0);
      continue;
    }
    deg = D0_entry.h; /* class poly degree */
    h0 = ((D0_entry.m & 2) ? 2*deg : deg); /* class number */
    /* (D0_entry.m & 1) is 1 if ord(L0) < h0 (hence = h0/2),
     *                  is 0 if ord(L0) = h0 */
    n0 = h0 / ((D0_entry.m & 1) + 1); /* = ord(L0) */

    /* Look for L1: for each smooth prime p */
    L1 = 0;
    for (i = 1 ; i <= SMOOTH_PRIMES; i++)
    {
      long p = PRIMES[i];
      if (p <= L0) continue;
      /* If 1 + (D0 | p) = 1, i.e. p | D0 */
      if (((D0_entry.m >> (2*i)) & 3) == 1) {
        /* XXX: Why (p | L) = -1?  Presumably so (L^2 v^2 D0 | p) = -1? */
        if (p <= max_L1 && modinv_N % p && kross(p,L) < 0) { L1 = p; break; }
      }
    }
    if (i > SMOOTH_PRIMES && (n0 < h0 || use_L1))
    { /* Didn't find suitable L1 though we need one */
      dbg_printf(3)("Bad D0=%ld because there is no good L1\n", D0);
      continue;
    }
    dbg_printf(3)("Good D0=%ld with L1=%ld, n0=%ld, h0=%ld, d=%ld\n",
                  D0, L1, n0, h0, d);

    /* We're finished if we have sufficiently many discriminants that satisfy
     * the cost requirement */
    if (totbits > minbits && best_cost && h0*(L-1) > 3*best_cost) break;

    D0_bits = log2(-D0);
    /* If L^2 D0 is too big to fit in a BIL bit integer, skip D0. */
    if (D0_bits + 2 * L_bits > (BITS_IN_LONG - 1)) continue;

    /* m is the order of L0^n0 in L^2 D0? */
    m = primeform_exp_order(L0, n0, L * L * D0, n0 * (L-1));
    if (m < (L-1)/2) {
      dbg_printf(3)("Bad D0=%ld because %ld is less than (L-1)/2=%ld\n",
                    D0, m, (L - 1)/2);
      continue;
    }
    /* Heuristic.  Doesn't end up contributing much. */
    H_cost = 2 * deg * deg;

    /* 0xc = 0b1100, so D0_entry.m & 0xc == 1 + (D0 | 2) */
    if ((D0 & 7) == 5) /* D0 = 5 (mod 8) */
      twofactor = ((D0_entry.m & 0xc) ? 1 : 3);
    else
      twofactor = 0;

    btop = avma;
    /* For each small prime... */
    for (i = 0; i <= SMOOTH_PRIMES; i++) {
      long h1, h2, D1, D2, n1, n2, dl1, dl20, dl21, p, q, j;
      double p_bits;
      avma = btop;
      /* i = 0 corresponds to 1, which we do not want to skip! (i.e. DK = D) */
      if (i) {
        if (modinv_odd_conductor(inv) && i == 1) continue;
        p = PRIMES[i];
        /* Don't allow large factors in the conductor. */
        if (p > max_L1) break;
        if (p == L0 || p == L1 || p == L || p == modinv_p1 || p == modinv_p2)
          continue;
        p_bits = log2(p);
        /* h1 is the class number of D1 = q^2 D0, where q = p^j (j defined in the loop below) */
        h1 = h0 * (p - ((D0_entry.m >> (2*i)) & 0x3) + 1);
        /* q is the smallest power of p such that h1 >= d ~ "L + 1". */
        for (j = 1, q = p; h1 < d; j++, q *= p, h1 *= p)
          ;
        D1 = q * q * D0;
        /* can't have D1 = 0 mod 16 and hope to get any primes congruent to 3 mod 4 */
        if ((pfilter & IQ_FILTER_1MOD4) && !(D1 & 0xF)) continue;
      } else {
        /* i = 0, corresponds to "p = 1". */
        h1 = h0;
        D1 = D0;
        p = q = j = 1;
        p_bits = 0;
      }
      /* include a factor of 4 if D1 is 5 mod 8 */
      /* XXX: No idea why he does this. */
      if (twofactor && (q & 1)) {
        if (modinv_odd_conductor(inv)) continue;
        D1 *= 4;
        h1 *= twofactor;
      }
      /* heuristic early abort; we may miss good D1's, but this saves time */
      if (totbits > minbits && best_cost && h1*(L-1) > 2.2*best_cost) continue;

      /* log2(D0 * (p^j)^2 * L^2 * twofactor) > (BIL - 1) -- params too big. */
      if (D0_bits + 2*j*p_bits + 2*L_bits
          + (twofactor && (q & 1) ? 2.0 : 0.0) > (BITS_IN_LONG-1)) continue;

      if (! check_generators(&n1, NULL, D1, h1, n0, d, L0, L1)) continue;

      if (n1 >= h1) dl1 = -1; /* fill it in later */
      else if ((dl1 = primeform_discrete_log(L0, L, n1, D1)) < 0) continue;
      dbg_printf(3)("Good D0=%ld, D1=%ld with q=%ld, L1=%ld, n1=%ld, h1=%ld\n",
                    D0, D1, q, L1, n1, h1);
      if (modinv_deg && orientation_ambiguity(D1, L0, modinv_p1, modinv_p2, modinv_N))
        continue;

      D2 = L * L * D1;
      h2 = h1 * (L-1);
      /* m is the order of L0^n1 in cl(D2) */
      if (!check_generators(&n2, &m, D2, h2, n1, d*(L-1), L0, L1)) continue;

      /* This restriction on m is not necessary, but simplifies life later */
      if (m < (L-1)/2 || (!L1 && m < L-1)) {
        dbg_printf(3)("Bad D2=%ld for D1=%ld, D0=%ld, with n2=%ld, h2=%ld, L1=%ld, "
                      "order of L0^n1 in cl(D2) is too small\n", D2, D1, D0, n2, h2, L1);
        continue;
      }
      dl20 = n1;
      dl21 = 0;
      if (m < L-1) {
        GEN Q1 = qform_primeform2(L, D1), Q2, X;
        if (!Q1) pari_err_BUG("modpoly_pickD");
        Q2 = primeform_u(stoi(D2), L1);
        Q2 = gmul(Q1, Q2); /* we know this element has order L-1 */
        Q1 = primeform_u(stoi(D2), L0);
        k = ((n2 & 1) ? 2*n2 : n2)/(L-1);
        Q1 = gpowgs(Q1, k);
        X = qfi_Shanks(Q2, Q1, L-1);
        if (!X) {
          dbg_printf(3)("Bad D2=%ld for D1=%ld, D0=%ld, with n2=%ld, h2=%ld, L1=%ld, "
              "form of norm L^2 not generated by L0 and L1\n",
              D2, D1, D0, n2, h2, L1);
          continue;
        }
        dl20 = itos(X) * k;
        dl21 = 1;
      }
      if (! (m < L-1 || n2 < d*(L-1)) && n1 >= d && ! use_L1)
        L1 = 0;  /* we don't need L1 */

      if (!L1 && use_L1) {
        dbg_printf(3)("not using D2=%ld for D1=%ld, D0=%ld, with n2=%ld, h2=%ld, L1=%ld, "
                   "because we don't need L1 but must use it\n",
                   D2, D1, D0, n2, h2, L1);
        continue;
      }
      /* don't allow zero dl21 with L1 for the moment, since
       * modpoly doesn't handle it - we may change this in the future */
      if (L1 && ! dl21) continue;
      dbg_printf(3)("Good D0=%ld, D1=%ld, D2=%ld with s=%ld^%ld, L1=%ld, dl2=%ld, n2=%ld, h2=%ld\n",
                 D0, D1, D2, p, j, L1, dl20, n2, h2);

      /* This estimate is heuristic and fiddling with the
       * parameters 5 and 0.25 can change things quite a bit. */
      enum_cost = n2 * (5 * L0 * L0 + 0.25 * L1 * L1);
      cost = enum_cost + H_cost;
      if (best_cost && cost > 2.2*best_cost) break;
      if (best_cost && cost >= 0.99*best_cost) continue;

      Dinfo.GENcode0 = evaltyp(t_VECSMALL)|evallg(13);
      Dinfo.inv = inv;
      Dinfo.L = L;
      Dinfo.D0 = D0;
      Dinfo.D1 = D1;
      Dinfo.L0 = L0;
      Dinfo.L1 = L1;
      Dinfo.n1 = n1;
      Dinfo.n2 = n2;
      Dinfo.dl1 = dl1;
      Dinfo.dl2_0 = dl20;
      Dinfo.dl2_1 = dl21;
      Dinfo.cost = cost;

      if (!modpoly_pickD_primes(NULL, NULL, 0, NULL, 0, &Dinfo.bits, minbits, &Dinfo))
        continue;
      dbg_printf(2)("Best D2=%ld, D1=%ld, D0=%ld with s=%ld^%ld, L1=%ld, "
                 "n1=%ld, n2=%ld, cost ratio %.2f, bits=%ld\n",
                 D2, D1, D0, p, j, L1, n1, n2,
                 (double)cost/(d*(L-1)), Dinfo.bits);
      /* Insert Dinfo into the Ds array.  Ds is sorted by ascending cost. */
      for (j = 0; j < Dcnt; j++)
        if (Dinfo.cost < Ds[j].cost) break;
      if (n2 > MAX_VOLCANO_FLOOR_SIZE && n2*(L1 ? 2 : 1) > 1.2* (d*(L-1)) ) {
        dbg_printf(3)("Not using D1=%ld, D2=%ld for space reasons\n", D1, D2);
        continue;
      }
      if (j == Dcnt && Dcnt == MODPOLY_MAX_DCNT)
        continue;
      totbits += Dinfo.bits;
      if (Dcnt == MODPOLY_MAX_DCNT) totbits -= Ds[Dcnt-1].bits;
      if (Dcnt < MODPOLY_MAX_DCNT) Dcnt++;
      if (n2 > MAX_VOLCANO_FLOOR_SIZE)
        dbg_printf(3)("totbits=%ld, minbits=%ld\n", totbits, minbits);
      for (k = Dcnt-1; k > j; k--) Ds[k] = Ds[k-1];
      Ds[k] = Dinfo;
      best_cost = (totbits > minbits)? Ds[Dcnt-1].cost: 0;
      /* if we were able to use D1 with s = 1, there is no point in
       * using any larger D1 for the same D0 */
      if (!i) break;
    } /* END FOR over small primes */
  } /* END WHILE over D0's */
  dbg_printf(2)("  checked %ld of %ld fundamental discriminants to find suitable "
                "discriminant (Dcnt = %ld)\n", D0_i, tablen, Dcnt);
  if ( ! Dcnt) {
    dbg_printf(1)("failed completely for L=%ld\n", L);
    return 0;
  }

  Dcnt = calc_primes_for_discriminants(Ds, Dcnt, L, minbits);

  /* fill in any missing dl1's */
  for (i = 0 ; i < Dcnt; i++)
    if (Ds[i].dl1 < 0 &&
       (Ds[i].dl1 = primeform_discrete_log(L0, L, Ds[i].n1, Ds[i].D1)) < 0)
        pari_err_BUG("modpoly_pickD");
  if (DEBUGLEVEL > 1+3) {
    err_printf("Selected %ld discriminants using %ld msecs\n", Dcnt, timer_delay(&T));
    for (i = 0 ; i < Dcnt ; i++)
    {
      GEN H = classno(stoi(Ds[i].D0));
      long h0 = itos(H);
      err_printf ("    D0=%ld, h(D0)=%ld, D=%ld, L0=%ld, L1=%ld, "
          "cost ratio=%.2f, enum ratio=%.2f,",
          Ds[i].D0, h0, Ds[i].D1, Ds[i].L0, Ds[i].L1,
          (double)Ds[i].cost/(d*(L-1)),
          (double)(Ds[i].n2*(Ds[i].L1 ? 2 : 1))/(d*(L-1)));
      err_printf (" %ld primes, %ld bits\n", Ds[i].nprimes, Ds[i].bits);
    }
  }
  avma = ltop; return Dcnt;
}

static int
_qsort_cmp(const void *a, const void *b)
{
  D_entry *x = (D_entry *)a, *y = (D_entry *)b;
  long u, v;

  /* u and v are the class numbers of x and y */
  u = x->h * (!!(x->m & 2) + 1);
  v = y->h * (!!(y->m & 2) + 1);
  /* Sort by class number */
  if (u < v) return -1;
  if (u > v) return 1;
  /* Sort by discriminant (which is < 0, hence the sign reversal) */
  if (x->D > y->D) return -1;
  if (x->D < y->D) return 1;
  return 0;
}

/* Build a table containing fundamental D, |D| <= maxD whose class groups
 * - are cyclic generated by an element of norm L0
 * - have class number at most maxh
 * The table is ordered using _qsort_cmp above, which ranks the discriminants
 * by class number, then by absolute discriminant.
 *
 * INPUT:
 * - maxd: largest allowed discriminant
 * - maxh: largest allowed class number
 * - L0: norm of class group generator
 *
 * OUTPUT:
 * - tablelen: length of return value
 *
 * RETURN:
 * - array of {D, h(D), kronecker symbols for small p} */
static D_entry *
scanD0(long *tablelen, long *minD, long maxD, long maxh, long L0)
{
  pari_sp av;
  D_entry *tab;
  long d, cnt;

  /* NB: As seen in the loop below, the real class number of D can be */
  /* 2*maxh if cl(D) is cyclic. */
  if (maxh < 0) pari_err_BUG("scanD0");

  /* Not checked, but L0 should be 2, 3, 5 or 7. */
  tab = (D_entry *) stack_malloc((maxD/4)*sizeof(*tab)); /* Overestimate */
  /* d = 7, 11, 15, 19, 23, ... */
  for (av = avma, d = *minD, cnt = 0; d <= maxD; d += 4, avma = av)
  {
    GEN DD, H, fact, ordL, frm;
    long i, j, k, n, h, L1, D = -d;
    long *q, *e;
    ulong m;
    /* Check to see if (D | L0) = 1 */
    if (kross(D, L0) < 1) continue;

    /* [q, e] is the factorisation of d. */
    fact = factoru(d);
    q = zv_to_longptr(gel(fact, 1));
    e = zv_to_longptr(gel(fact, 2));
    k = lg(gel(fact, 1)) - 1;

    /* Check if the discriminant is square-free */
    for (i = 0; i < k; i++)
      if (e[i] > 1) break;
    if (i < k) continue;

    /* L1 initially the first factor of d if small enough, otherwise ignored */
    L1 = (k > 1 && q[0] <= MAX_L1)? q[0]: 0;

    /* restrict to possibly cyclic class groups */
    if (k > 2) continue;

    /* Check if h(D) is too big */
    DD = stoi(D);
    H = classno(DD);
    h = itos(H);
    if (h > 2*maxh || (!L1 && h > maxh)) continue;

    /* Check if ord(q) is not big enough to generate at least half the
     * class group (where q is the L0-primeform). */
    frm = primeform_u(DD, L0);
    ordL = qfi_order(redimag(frm), H);
    n = itos(ordL);
    if (n < h/2 || (!L1 && n < h)) continue;

    /* If q is big enough, great!  Otherwise, for each potential L1,
     * do a discrete log to see if it is NOT in the subgroup generated
     * by L0; stop as soon as such is found. */
    for (j = 0; ; j++) {
      if (n == h || (L1 && !qfi_Shanks(primeform_u(DD, L1), frm, n))) {
        dbg_printf(2)("D0=%ld good with L1=%ld\n", D, L1);
        break;
      }
      if (!L1) break;
      L1 = (j < k && k > 1 && q[j] <= MAX_L1 ? q[j] : 0);
    }
    /* The first bit of m indicates whether q generates a proper
     * subgroup of cl(D) (hence implying that we need L1) or if q
     * generates the whole class group. */
    m = (n < h ? 1 : 0);
    /* bits i and i+1 of m give the 2-bit number 1 + (D|p) where p is
     * the ith prime. */
    for (i = 1 ; i <= SMOOTH_PRIMES; i++)
    {
      ulong x  = (ulong) (1 + kross(D, PRIMES[i]));
      m |= x << (2*i);
    }

    /* Insert d, h and m into the table */
    tab[cnt].D = D;
    tab[cnt].h = h;
    tab[cnt].m = m;
    cnt++;
  }

  /* Sort the table */
  qsort(tab, cnt, sizeof(*tab), _qsort_cmp);
  *tablelen = cnt; *minD = d; return tab;
}

/* Populate Ds with discriminants (and attached data) that can be
 * used to calculate the modular polynomial of level L and invariant
 * inv.  Return the number of discriminants found. */
static long
discriminant_with_classno_at_least(disc_info bestD[MODPOLY_MAX_DCNT],
  long L, long inv, long ignore_sparse)
{
  enum { SMALL_L_BOUND = 101 };
  long max_max_D = 160000 * (inv ? 2 : 1);
  long minD, maxD, maxh, L0, max_L1, minbits, Dcnt, flags, s, d, h, i, tablen;
  D_entry *tab;
  double eps, cost, best_eps = -1.0, best_cost = -1.0;
  disc_info Ds[MODPOLY_MAX_DCNT];
  long best_cnt = 0;
  pari_timer T;
  timer_start(&T);

  s = modinv_sparse_factor(inv);
  d = ceildivuu(L+1, s) + 1;

  /* maxD of 10000 allows us to get a satisfactory discriminant in
   * under 250ms in most cases. */
  maxD = 10000;
  /* Allow the class number to overshoot L by 50%.  Must be at least
   * 1.1*L, and higher values don't seem to provide much benefit,
   * except when L is small, in which case it's necessary to get any
   * discriminant at all in some cases. */
  maxh = (L / s < SMALL_L_BOUND) ? 10 * L : 1.5 * L;

  flags = ignore_sparse ? MODPOLY_IGNORE_SPARSE_FACTOR : 0;
  L0 = select_L0(L, inv, 0);
  max_L1 = L / 2 + 2;    /* for L=11 we need L1=7 for j */
  minbits = modpoly_height_bound(L, inv);
  minD = 7;

  while ( ! best_cnt) {
    while (maxD <= max_max_D) {
      /* TODO: Find a way to re-use tab when we need multiple modpolys */
      tab = scanD0(&tablen, &minD, maxD, maxh, L0);
      dbg_printf(1)("Found %ld potential fundamental discriminants\n", tablen);

      Dcnt = modpoly_pickD(Ds, L, inv, L0, max_L1, minbits, flags, tab, tablen);
      eps = 0.0;
      cost = 0.0;

      if (Dcnt) {
        long n1 = 0;
        for (i = 0; i < Dcnt; i++) {
          n1 = maxss(n1, Ds[i].n1);
          cost += Ds[i].cost;
        }
        eps = (n1 * s - L) / (double)L;

        if (best_cost < 0.0 || cost < best_cost) {
          if (best_cnt)
            for (i = 0; i < best_cnt; i++) killbloc((GEN)bestD[i].primes);
          (void) memcpy(bestD, Ds, Dcnt * sizeof(disc_info));
          best_cost = cost;
          best_cnt = Dcnt;
          best_eps = eps;
          /* We're satisfied if n1 is within 5% of L. */
          if (L / s <= SMALL_L_BOUND || eps < 0.05) break;
        } else {
          for (i = 0; i < Dcnt; i++) killbloc((GEN)Ds[i].primes);
        }
      } else {
        if (log2(maxD) > BITS_IN_LONG - 2 * (log2(L) + 2))
        {
          char *err = stack_sprintf("modular polynomial of level %ld and invariant %ld",L,inv);
          pari_err(e_ARCH, err);
        }
      }
      maxD *= 2;
      minD += 4;
      dbg_printf(0)("  Doubling discriminant search space (closest: %.1f%%, cost ratio: %.1f)...\n", eps*100, cost/(double)(d*(L-1)));
    }
    max_max_D *= 2;
  }

  if (DEBUGLEVEL > 3) {
    pari_sp av = avma;
    err_printf("Found discriminant(s):\n");
    for (i = 0; i < best_cnt; ++i) {
      h = itos(classno(stoi(bestD[i].D1)));
      avma = av;
      err_printf("  D = %ld, h = %ld, u = %ld, L0 = %ld, L1 = %ld, n1 = %ld, n2 = %ld, cost = %ld\n",
          bestD[i].D1, h, usqrt(bestD[i].D1 / bestD[i].D0), bestD[i].L0,
          bestD[i].L1, bestD[i].n1, bestD[i].n2, bestD[i].cost);
    }
    err_printf("(off target by %.1f%%, cost ratio: %.1f)\n",
               best_eps*100, best_cost/(double)(d*(L-1)));
  }
  return best_cnt;
}
