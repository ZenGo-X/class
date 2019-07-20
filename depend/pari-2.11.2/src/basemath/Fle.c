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

/* Not so fast arithmetic with points over elliptic curves over Fl */

/***********************************************************************/
/**                                                                   **/
/**                              Flj                                  **/
/**                                                                   **/
/***********************************************************************/

/* Arithmetic is implemented using Jacobian coordinates, representing
 * a projective point (x : y : z) on E by [z*x , z^2*y , z].  This is
 * probably not the fastest representation available for the given
 * problem, but they're easy to implement and up to 60% faster than
 * the school-book method used in Fle_mulu(). */

/* Cost: 1M + 8S + 1*a + 10add + 1*8 + 2*2 + 1*3.
 * Source: http://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian.html#doubling-dbl-2007-bl */
INLINE void
Flj_dbl_indir_pre(GEN P, GEN Q, ulong a4, ulong p, ulong pi)
{
  ulong X1, Y1, Z1;
  ulong XX, YY, YYYY, ZZ, S, M, T;

  X1 = P[1]; Y1 = P[2]; Z1 = P[3];

  if (Z1 == 0) { Q[1] = X1; Q[2] = Y1; Q[3] = Z1; return; }

  XX = Fl_sqr_pre(X1, p, pi);
  YY = Fl_sqr_pre(Y1, p, pi);
  YYYY = Fl_sqr_pre(YY, p, pi);
  ZZ = Fl_sqr_pre(Z1, p, pi);
  S = Fl_double(Fl_sub(Fl_sqr_pre(Fl_add(X1, YY, p), p, pi),
                       Fl_add(XX, YYYY, p), p), p);
  M = Fl_addmul_pre(Fl_triple(XX, p), a4, Fl_sqr_pre(ZZ, p, pi), p, pi);
  T = Fl_sub(Fl_sqr_pre(M, p, pi), Fl_double(S, p), p);
  Q[1] = T;
  Q[2] = Fl_sub(Fl_mul_pre(M, Fl_sub(S, T, p), p, pi),
                Fl_double(Fl_double(Fl_double(YYYY, p), p), p), p);
  Q[3] = Fl_sub(Fl_sqr_pre(Fl_add(Y1, Z1, p), p, pi),
                Fl_add(YY, ZZ, p), p);
}

INLINE void
Flj_dbl_pre_inplace(GEN P, ulong a4, ulong p, ulong pi)
{
  Flj_dbl_indir_pre(P, P, a4, p, pi);
}

GEN
Flj_dbl_pre(GEN P, ulong a4, ulong p, ulong pi)
{
  GEN Q = cgetg(4, t_VECSMALL);
  Flj_dbl_indir_pre(P, Q, a4, p, pi);
  return Q;
}

/* Cost: 11M + 5S + 9add + 4*2.
 * Source: http://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian.html#addition-add-2007-bl */
INLINE void
Flj_add_indir_pre(GEN P, GEN Q, GEN R, ulong a4, ulong p, ulong pi)
{
  ulong X1, Y1, Z1, X2, Y2, Z2;
  ulong Z1Z1, Z2Z2, U1, U2, S1, S2, H, I, J, r, V, W;
  X1 = P[1]; Y1 = P[2]; Z1 = P[3];
  X2 = Q[1]; Y2 = Q[2]; Z2 = Q[3];

  if (Z2 == 0) { R[1] = X1; R[2] = Y1; R[3] = Z1; return; }
  if (Z1 == 0) { R[1] = X2; R[2] = Y2; R[3] = Z2; return; }

  Z1Z1 = Fl_sqr_pre(Z1, p, pi);
  Z2Z2 = Fl_sqr_pre(Z2, p, pi);
  U1 = Fl_mul_pre(X1, Z2Z2, p, pi);
  U2 = Fl_mul_pre(X2, Z1Z1, p, pi);
  S1 = Fl_mul_pre(Y1, Fl_mul_pre(Z2, Z2Z2, p, pi), p, pi);
  S2 = Fl_mul_pre(Y2, Fl_mul_pre(Z1, Z1Z1, p, pi), p, pi);
  H = Fl_sub(U2, U1, p);
  r = Fl_double(Fl_sub(S2, S1, p), p);

  if (H == 0) {
    if (r == 0) Flj_dbl_indir_pre(P, R, a4, p, pi); /*Points are equal, double*/
    else { R[1] = R[2] = 1; R[3] = 0; } /* Points are opposite, return zero */
    return;
  }
  I = Fl_sqr_pre(Fl_double(H, p), p, pi);
  J = Fl_mul_pre(H, I, p, pi);
  V = Fl_mul_pre(U1, I, p, pi);
  W = Fl_sub(Fl_sqr_pre(r, p, pi), Fl_add(J, Fl_double(V, p), p), p);
  R[1] = W;
  R[2] = Fl_sub(Fl_mul_pre(r, Fl_sub(V, W, p), p, pi),
                Fl_double(Fl_mul_pre(S1, J, p, pi), p), p);
  R[3] = Fl_mul_pre(Fl_sub(Fl_sqr_pre(Fl_add(Z1, Z2, p), p, pi),
                           Fl_add(Z1Z1, Z2Z2, p), p), H, p, pi);
}

INLINE void
Flj_add_pre_inplace(GEN P, GEN Q, ulong a4, ulong p, ulong pi)
{ Flj_add_indir_pre(P, Q, P, a4, p, pi); }

GEN
Flj_add_pre(GEN P, GEN Q, ulong a4, ulong p, ulong pi)
{
  GEN R = cgetg(4, t_VECSMALL);
  Flj_add_indir_pre(P, Q, R, a4, p, pi);
  return R;
}

GEN
Flj_neg(GEN Q, ulong p)
{ return mkvecsmall3(Q[1], Fl_neg(Q[2], p), Q[3]); }

typedef struct {
  ulong n; /* The number being represented */
  ulong pbits, nbits;  /* Positive bits and negative bits */
  ulong lnzb; /* Leading non-zero bit */
} naf_t;

/* Return the signed binary representation (i.e. the Non-Adjacent Form
 * in base 2) of 0 <= a < 2^63 */
static void
naf_repr(naf_t *x, ulong a)
{
  long t, i;
  ulong pbits, nbits;
  ulong c0 = 0, c1, a0;

  x->n = a;
  pbits = nbits = 0;
  for (i = 0; a; a >>= 1, ++i) {
    a0 = a & 1;
    c1 = (c0 + a0 + ((a & 2) >> 1)) >> 1;
    t = c0 + a0 - (c1 << 1);
    if (t < 0)
      nbits |= (1UL << i);
    else if (t > 0)
      pbits |= (1UL << i);
    c0 = c1;
  }
  c1 = c0 >> 1;
  t = c0 - (c1 << 1);
  /* Note that we don't need to check whether t < 0, since a >= 0 implies
   * that this most significant signed bit must be non-negative. */
  if (t > 0 && i != BITS_IN_LONG) pbits |= (1UL << i);

  x->pbits = pbits;
  x->nbits = nbits;
  /* Note that expu returns the least nonzero bit in the argument,
   * like the bit-scan-rev instruction on Intel architectures. */
  /* Using pbits here is justified by the fact that a >= 0, so the
   * most significant bit must be positive. */
  x->lnzb = t? i-2: i-3;
}

/* Standard left-to-right signed double-and-add to compute [n]P. */
static GEN
Flj_mulu_pre_naf(GEN P, ulong n, ulong a4, ulong p, ulong pi, const naf_t *x)
{
  GEN R, Pinv;
  ulong pbits, nbits, lnzb;
  ulong m;

  if (n == 0) return mkvecsmall3(1, 1, 0);
  if (n == 1) return Flv_copy(P);

  R = Flj_dbl_pre(P, a4, p, pi);
  if (n == 2) return R;

  pbits = x->pbits;
  nbits = x->nbits;
  lnzb = x->lnzb;

  Pinv = Flj_neg(P, p);
  m = (1UL << lnzb);
  for ( ; m; m >>= 1) {
    Flj_dbl_pre_inplace(R, a4, p, pi);
    if (m & pbits)
      Flj_add_pre_inplace(R, P, a4, p, pi);
    else if (m & nbits)
      Flj_add_pre_inplace(R, Pinv, a4, p, pi);
  }
  avma = (pari_sp)R; return R;
}

GEN
Flj_mulu_pre(GEN P, ulong n, ulong a4, ulong p, ulong pi)
{
  naf_t x;
  naf_repr(&x, n);
  return Flj_mulu_pre_naf(P, n, a4, p, pi, &x);
}

ulong
Flj_order_ufact(GEN P, ulong n, GEN F, ulong a4, ulong p, ulong pi)
{
  pari_sp av = avma;
  ulong res = 1;
  long i, nfactors;
  GEN primes, exps;

  primes = gel(F, 1);
  nfactors = lg(primes);
  exps = gel(F, 2);

  for (i = 1; i < nfactors; ++i) {
    ulong q, pp = primes[i];
    long j, k, ei = exps[i];
    naf_t x;
    GEN b;

    for (q = pp, j = 1; j < ei; ++j) q *= pp;
    b = Flj_mulu_pre(P, n / q, a4, p, pi);

    naf_repr(&x, pp);
    for (j = 0; j < ei && b[3] != 0; ++j)
      b = Flj_mulu_pre_naf(b, pp, a4, p, pi, &x);
    if (b[3] != 0) return 0;
    for (k = 0; k < j; ++k) res *= pp;
    avma = av;
  }
  return res;
}

GEN
Fle_to_Flj(GEN P)
{ return ell_is_inf(P) ? mkvecsmall3(1UL, 1UL, 0UL):
                         mkvecsmall3(P[1], P[2], 1UL);
}

GEN
Flj_to_Fle_pre(GEN P, ulong p, ulong pi)
{
  if (P[3] == 0) return ellinf();
  else
  {
    ulong Z = Fl_inv(P[3], p);
    ulong Z2 = Fl_sqr_pre(Z, p, pi);
    ulong X3 = Fl_mul_pre(P[1], Z2, p, pi);
    ulong Y3 = Fl_mul_pre(P[2], Fl_mul_pre(Z, Z2, p, pi), p, pi);
    return mkvecsmall2(X3, Y3);
  }
}

INLINE void
random_Fle_pre_indir(ulong a4, ulong a6, ulong p, ulong pi,
                     ulong *pt_x, ulong *pt_y)
{
  ulong x, x2, y, rhs;
  do
  {
    x   = random_Fl(p); /*  x^3+a4*x+a6 = x*(x^2+a4)+a6  */
    x2  = Fl_sqr_pre(x, p, pi);
    rhs = Fl_addmul_pre(a6, x, Fl_add(x2, a4, p), p, pi);
  } while ((!rhs && !Fl_add(Fl_triple(x2,p),a4,p)) || krouu(rhs, p) < 0);
  y = Fl_sqrt_pre(rhs, p, pi);
  *pt_x = x; *pt_y = y;
}

GEN
random_Flj_pre(ulong a4, ulong a6, ulong p, ulong pi)
{
  ulong x, y;
  random_Fle_pre_indir(a4, a6, p, pi, &x, &y);
  return mkvecsmall3(x, y, 1);
}

/***********************************************************************/
/**                                                                   **/
/**                              Fle                                  **/
/**                                                                   **/
/***********************************************************************/
GEN
Fle_changepoint(GEN x, GEN ch, ulong p)
{
  ulong p1,u,r,s,t,v,v2,v3;
  GEN z;
  if (ell_is_inf(x)) return x;
  u = ch[1]; r = ch[2];
  s = ch[3]; t = ch[4];
  v = Fl_inv(u, p); v2 = Fl_sqr(v,p); v3 = Fl_mul(v,v2,p);
  p1 = Fl_sub(x[1],r,p);
  z = cgetg(3,t_VECSMALL);
  z[1] = Fl_mul(v2, p1, p);
  z[2] = Fl_mul(v3, Fl_sub(x[2], Fl_add(Fl_mul(s,p1, p),t, p),p),p);
  return z;
}

GEN
Fle_changepointinv(GEN x, GEN ch, ulong p)
{
  ulong u, r, s, t, X, Y, u2, u3, u2X;
  GEN z;
  if (ell_is_inf(x)) return x;
  X = x[1]; Y = x[2];
  u = ch[1]; r = ch[2];
  s = ch[3]; t = ch[4];
  u2 = Fl_sqr(u, p); u3 = Fl_mul(u,u2,p);
  u2X = Fl_mul(u2,X, p);
  z = cgetg(3, t_VECSMALL);
  z[1] = Fl_add(u2X,r,p);
  z[2] = Fl_add(Fl_mul(u3,Y,p), Fl_add(Fl_mul(s,u2X,p), t, p), p);
  return z;
}
static GEN
Fle_dbl_slope(GEN P, ulong a4, ulong p, ulong *slope)
{
  ulong x, y, Qx, Qy;
  if (ell_is_inf(P) || !P[2]) return ellinf();
  x = P[1]; y = P[2];
  *slope = Fl_div(Fl_add(Fl_triple(Fl_sqr(x,p), p), a4, p),
                  Fl_double(y, p), p);
  Qx = Fl_sub(Fl_sqr(*slope, p), Fl_double(x, p), p);
  Qy = Fl_sub(Fl_mul(*slope, Fl_sub(x, Qx, p), p), y, p);
  return mkvecsmall2(Qx, Qy);
}

GEN
Fle_dbl(GEN P, ulong a4, ulong p)
{
  ulong slope;
  return Fle_dbl_slope(P,a4,p,&slope);
}

static GEN
Fle_add_slope(GEN P, GEN Q, ulong a4, ulong p, ulong *slope)
{
  ulong Px, Py, Qx, Qy, Rx, Ry;
  if (ell_is_inf(P)) return Q;
  if (ell_is_inf(Q)) return P;
  Px = P[1]; Py = P[2];
  Qx = Q[1]; Qy = Q[2];
  if (Px==Qx) return Py==Qy ? Fle_dbl_slope(P, a4, p, slope): ellinf();
  *slope = Fl_div(Fl_sub(Py, Qy, p), Fl_sub(Px, Qx, p), p);
  Rx = Fl_sub(Fl_sub(Fl_sqr(*slope, p), Px, p), Qx, p);
  Ry = Fl_sub(Fl_mul(*slope, Fl_sub(Px, Rx, p), p), Py, p);
  return mkvecsmall2(Rx, Ry);
}

GEN
Fle_add(GEN P, GEN Q, ulong a4, ulong p)
{
  ulong slope;
  return Fle_add_slope(P,Q,a4,p,&slope);
}

static GEN
Fle_neg(GEN P, ulong p)
{
  if (ell_is_inf(P)) return P;
  return mkvecsmall2(P[1], Fl_neg(P[2], p));
}

GEN
Fle_sub(GEN P, GEN Q, ulong a4, ulong p)
{
  pari_sp av = avma;
  ulong slope;
  return gerepileupto(av, Fle_add_slope(P, Fle_neg(Q, p), a4, p, &slope));
}

struct _Fle { ulong a4, a6, p; };

static GEN
_Fle_dbl(void *E, GEN P)
{
  struct _Fle *ell = (struct _Fle *) E;
  return Fle_dbl(P, ell->a4, ell->p);
}

static GEN
_Fle_add(void *E, GEN P, GEN Q)
{
  struct _Fle *ell=(struct _Fle *) E;
  return Fle_add(P, Q, ell->a4, ell->p);
}

GEN
Fle_mulu(GEN P, ulong n, ulong a4, ulong p)
{
  ulong pi;
  if (!n || ell_is_inf(P)) return ellinf();
  if (n==1) return zv_copy(P);
  if (n==2) return Fle_dbl(P, a4, p);
  pi = get_Fl_red(p);
  return Flj_to_Fle_pre(Flj_mulu_pre(Fle_to_Flj(P), n, a4, p, pi), p, pi);
}

static GEN
_Fle_mul(void *E, GEN P, GEN n)
{
  pari_sp av = avma;
  struct _Fle *e=(struct _Fle *) E;
  long s = signe(n);
  GEN Q;
  if (!s || ell_is_inf(P)) return ellinf();
  if (s < 0) P = Fle_neg(P, e->p);
  if (is_pm1(n)) return s > 0? zv_copy(P): P;
  Q = (lgefint(n)==3) ? Fle_mulu(P, uel(n,2), e->a4, e->p):
                        gen_pow(P, n, (void*)e, &_Fle_dbl, &_Fle_add);
  return s > 0? Q: gerepileuptoleaf(av, Q);
}

GEN
Fle_mul(GEN P, GEN n, ulong a4, ulong p)
{
  struct _Fle E;
  E.a4 = a4; E.p = p;
  return _Fle_mul(&E, P, n);
}

/* Finds a random non-singular point on E */
GEN
random_Fle_pre(ulong a4, ulong a6, ulong p, ulong pi)
{
  ulong x, y;
  random_Fle_pre_indir(a4, a6, p, pi, &x, &y);
  return mkvecsmall2(x, y);
}

GEN
random_Fle(ulong a4, ulong a6, ulong p)
{ return random_Fle_pre(a4, a6, p, get_Fl_red(p)); }

static GEN
_Fle_rand(void *E)
{
  struct _Fle *e=(struct _Fle *) E;
  return random_Fle(e->a4, e->a6, e->p);
}

static const struct bb_group Fle_group={_Fle_add,_Fle_mul,_Fle_rand,hash_GEN,zv_equal,ell_is_inf,NULL};

GEN
Fle_order(GEN z, GEN o, ulong a4, ulong p)
{
  pari_sp av = avma;
  struct _Fle e;
  e.a4=a4;
  e.p=p;
  return gerepileuptoint(av, gen_order(z, o, (void*)&e, &Fle_group));
}

GEN
Fle_log(GEN a, GEN b, GEN o, ulong a4, ulong p)
{
  pari_sp av = avma;
  struct _Fle e;
  e.a4=a4;
  e.p=p;
  return gerepileuptoint(av, gen_PH_log(a, b, o, (void*)&e, &Fle_group));
}

ulong
Fl_ellj(ulong a4, ulong a6, ulong p)
{
  if (SMALL_ULONG(p))
  { /* a43 = 4 a4^3 */
    ulong a43 = Fl_double(Fl_double(Fl_mul(a4, Fl_sqr(a4, p), p), p), p);
    /* a62 = 27 a6^2 */
    ulong a62 = Fl_mul(Fl_sqr(a6, p), 27 % p, p);
    ulong z1 = Fl_mul(a43, 1728 % p, p);
    ulong z2 = Fl_add(a43, a62, p);
    return Fl_div(z1, z2, p);
  }
  return Fl_ellj_pre(a4, a6, p, get_Fl_red(p));
}

void
Fl_ellj_to_a4a6(ulong j, ulong p, ulong *pt_a4, ulong *pt_a6)
{
  ulong zagier = 1728 % p;
  if (j == 0)           { *pt_a4 = 0; *pt_a6 =1; }
  else if (j == zagier) { *pt_a4 = 1; *pt_a6 =0; }
  else
  {
    ulong k = Fl_sub(zagier, j, p);
    ulong kj = Fl_mul(k, j, p);
    ulong k2j = Fl_mul(kj, k, p);
    *pt_a4 = Fl_triple(kj, p);
    *pt_a6 = Fl_double(k2j, p);
  }
}

ulong
Fl_elldisc_pre(ulong a4, ulong a6, ulong p, ulong pi)
{ /* D = -(4A^3 + 27B^2) */
  ulong t1, t2;
  t1 = Fl_mul_pre(a4, Fl_sqr_pre(a4, p, pi), p, pi);
  t1 = Fl_double(Fl_double(t1, p), p);
  t2 = Fl_mul_pre(27 % p, Fl_sqr_pre(a6, p, pi), p, pi);
  return Fl_neg(Fl_add(t1, t2, p), p);
}

ulong
Fl_elldisc(ulong a4, ulong a6, ulong p)
{
  if (SMALL_ULONG(p))
  { /* D = -(4A^3 + 27B^2) */
    ulong t1, t2;
    t1 = Fl_mul(a4, Fl_sqr(a4, p), p);
    t1 = Fl_double(Fl_double(t1, p), p);
    t2 = Fl_mul(27 % p, Fl_sqr(a6, p), p);
    return Fl_neg(Fl_add(t1, t2, p), p);
  }
  return Fl_elldisc_pre(a4, a6, p, get_Fl_red(p));
}

static ulong
nonsquare_Fl(ulong p)
{
  ulong a;
  do a = random_Fl(p); while (krouu(a, p) >= 0);
  return a;
}

void
Fl_elltwist_disc(ulong a4, ulong a6, ulong D, ulong p, ulong *pa4, ulong *pa6)
{
  ulong D2 = Fl_sqr(D, p);
  *pa4 = Fl_mul(a4, D2, p);
  *pa6 = Fl_mul(a6, Fl_mul(D, D2, p), p);
}

void
Fl_elltwist(ulong a4, ulong a6, ulong p, ulong *pt_a4, ulong *pt_a6)
{ Fl_elltwist_disc(a4, a6, nonsquare_Fl(p), p, pt_a4, pt_a6); }

static void
Fle_dbl_sinv_pre_inplace(GEN P, ulong a4, ulong sinv, ulong p, ulong pi)
{
  ulong x, y, slope;
  if (uel(P,1)==p) return;
  if (!P[2]) { P[1] = p; return; }
  x = P[1]; y = P[2];
  slope = Fl_mul_pre(Fl_add(Fl_triple(Fl_sqr_pre(x, p, pi), p), a4, p),
                sinv, p, pi);
  P[1] = Fl_sub(Fl_sqr_pre(slope, p, pi), Fl_double(x, p), p);
  P[2] = Fl_sub(Fl_mul_pre(slope, Fl_sub(x, P[1], p), p, pi), y, p);
}

static void
Fle_add_sinv_pre_inplace(GEN P, GEN Q, ulong a4, ulong sinv, ulong p, ulong pi)
{
  ulong Px, Py, Qx, Qy, slope;
  if (uel(P,1)==p) { P[1] = Q[1]; P[2] = Q[2]; }
  if (ell_is_inf(Q)) return;
  Px = P[1]; Py = P[2];
  Qx = Q[1]; Qy = Q[2];
  if (Px==Qx)
  {
    if (Py==Qy) Fle_dbl_sinv_pre_inplace(P, a4, sinv, p, pi);
    else P[1] = p;
    return;
  }
  slope = Fl_mul_pre(Fl_sub(Py, Qy, p), sinv, p, pi);
  P[1] = Fl_sub(Fl_sub(Fl_sqr_pre(slope, p, pi), Px, p), Qx, p);
  P[2] = Fl_sub(Fl_mul_pre(slope, Fl_sub(Px, P[1], p), p, pi), Py, p);
}

static void
Fle_sub_sinv_pre_inplace(GEN P, GEN Q, ulong a4, ulong sinv, ulong p, ulong pi)
{
  ulong Px, Py, Qx, Qy, slope;
  if (uel(P,1)==p) { P[1] = Q[1]; P[2] = Fl_neg(Q[2], p); }
  if (ell_is_inf(Q)) return;
  Px = P[1]; Py = P[2];
  Qx = Q[1]; Qy = Q[2];
  if (Px==Qx)
  {
    if (Py==Qy) P[1] = p;
    else
      Fle_dbl_sinv_pre_inplace(P, a4, sinv, p, pi);
    return;
  }
  slope = Fl_mul_pre(Fl_add(Py, Qy, p), sinv, p, pi);
  P[1] = Fl_sub(Fl_sub(Fl_sqr_pre(slope, p, pi), Px, p), Qx, p);
  P[2] = Fl_sub(Fl_mul_pre(slope, Fl_sub(Px, P[1], p), p, pi), Py, p);
}

static long
skipzero(long n) { return n ? n:1; }

void
FleV_add_pre_inplace(GEN P, GEN Q, GEN a4, ulong p, ulong pi)
{
  long i, l=lg(a4);
  GEN sinv = cgetg(l, t_VECSMALL);
  for(i=1; i<l; i++)
    uel(sinv,i) = umael(P,i,1)==p? 1: skipzero(Fl_sub(mael(P,i,1), mael(Q,i,1), p));
  Flv_inv_pre_inplace(sinv, p, pi);
  for (i=1; i<l; i++)
    Fle_add_sinv_pre_inplace(gel(P,i), gel(Q,i), uel(a4,i), uel(sinv,i), p, pi);
}

void
FleV_sub_pre_inplace(GEN P, GEN Q, GEN a4, ulong p, ulong pi)
{
  long i, l=lg(a4);
  GEN sinv = cgetg(l, t_VECSMALL);
  for(i=1; i<l; i++)
    uel(sinv,i) = umael(P,i,1)==p? 1: skipzero(Fl_sub(mael(P,i,1), mael(Q,i,1), p));
  Flv_inv_pre_inplace(sinv, p, pi);
  for (i=1; i<l; i++)
    Fle_sub_sinv_pre_inplace(gel(P,i), gel(Q,i), uel(a4,i), uel(sinv,i), p, pi);
}

void
FleV_dbl_pre_inplace(GEN P, GEN a4, ulong p, ulong pi)
{
  long i, l=lg(a4);
  GEN sinv = cgetg(l, t_VECSMALL);
  for(i=1; i<l; i++)
    uel(sinv,i) = umael(P,i,1)==p? 1: skipzero(Fl_double(umael(P,i,2), p));
  Flv_inv_pre_inplace(sinv, p, pi);
  for(i=1; i<l; i++)
    Fle_dbl_sinv_pre_inplace(gel(P,i), uel(a4,i), uel(sinv,i), p, pi);
}

static void
FleV_mulu_pre_naf_inplace(GEN P, ulong n, GEN a4, ulong p, ulong pi, const naf_t *x)
{
  pari_sp av = avma;
  ulong pbits, nbits, lnzb, m;
  GEN R;
  if (n == 1) return;

  R = P; P = gcopy(P);
  FleV_dbl_pre_inplace(R, a4, p, pi);
  if (n == 2) return;

  pbits = x->pbits;
  nbits = x->nbits;
  lnzb = x->lnzb;

  m = (1UL << lnzb);
  for ( ; m; m >>= 1) {
    FleV_dbl_pre_inplace(R, a4, p, pi);
    if (m & pbits)
      FleV_add_pre_inplace(R, P, a4, p, pi);
    else if (m & nbits)
      FleV_sub_pre_inplace(R, P, a4, p, pi);
  }
  avma = av;
}

void
FleV_mulu_pre_inplace(GEN P, ulong n, GEN a4, ulong p, ulong pi)
{
  naf_t x;
  naf_repr(&x, n);
  FleV_mulu_pre_naf_inplace(P, n, a4, p, pi, &x);
}
