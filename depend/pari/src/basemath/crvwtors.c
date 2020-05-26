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

/* In the database, the curve X1(N) is given by the bivariate
 * polynomial X.  The degree of X in its main variable is at least
 * the degree of its secondary variable, except for N = 6, 7, 8, 9,
 * 10, 12.  Note that X1(N) is genus 0 for N <= 10 and N = 12, and
 * genus 1 for N = 11, 14, and 15. */


INLINE ulong
Fl_div4(ulong x, ulong p)
{
  return Fl_halve(Fl_halve(x, p), p);
}


INLINE ulong
Fl_div8(ulong x, ulong p)
{
  return Fl_halve(Fl_div4(x, p), p);
}

/* These tags describe which map to use to convert from (r,s) to (b,c)
 * coeffs. */
typedef enum {
  RS_MAP, T_MAP, QT_MAP, TQ_MAP
} map_type;

typedef struct {
  GEN crv;
  GEN r_num, r_den;
  long rplus1;
  GEN s_num, s_den;
  long splus1;
  map_type map;
} X1_info;

#define FIRST_X1_LEVEL 13
#define LAST_X1_LEVEL 39
/* The table is defined at the end of the file. */
INLINE const X1_info *get_X1_info(ulong N);

/* Compute the image of
 * (x,y) |--> (r_n(x,y)/r_d(x,y), s_n(x,y), s_d(x,y)) */
static void
map_X1_points(
  GEN r, GEN s,
  const X1_info *X1, long ncurves, ulong p, ulong pi)
{
  pari_sp ltop = avma, av;
  GEN X1_c, rn_pol, rd_pol, sn_pol, sd_pol, rn, sn, rd, sd;
  long xdeg, ydeg, i;

  X1_c = zxX_to_FlxX(X1->crv, p);
  xdeg = degpol(X1_c);
  ydeg = FlxY_degreex(X1_c);

  rn_pol = zxX_to_FlxX(X1->r_num, p);
  rd_pol = zxX_to_FlxX(X1->r_den, p);
  sn_pol = zxX_to_FlxX(X1->s_num, p);
  sd_pol = zxX_to_FlxX(X1->s_den, p);

  xdeg = maxss(xdeg, degpol(rn_pol));
  xdeg = maxss(xdeg, degpol(rd_pol));
  xdeg = maxss(xdeg, degpol(sn_pol));
  xdeg = maxss(xdeg, degpol(sd_pol));

  ydeg = maxss(ydeg, FlxY_degreex(rn_pol));
  ydeg = maxss(ydeg, FlxY_degreex(rd_pol));
  ydeg = maxss(ydeg, FlxY_degreex(sn_pol));
  ydeg = maxss(ydeg, FlxY_degreex(sd_pol));

  rn = cgetg(ncurves + 1, t_VECSMALL);
  rd = cgetg(ncurves + 1, t_VECSMALL);
  sn = cgetg(ncurves + 1, t_VECSMALL);
  sd = cgetg(ncurves + 1, t_VECSMALL);

  av = avma;
  for (i = 1; i <= ncurves; ) {
    GEN pol, ypowers, xpowers;
    ulong y, x;
    y = random_Fl(p);
    ypowers = Fl_powers_pre(y, ydeg, p, pi);
    pol = FlxY_evalx_powers_pre(X1_c, ypowers, p, pi);
    x = Flx_oneroot(pol, p);
    if (x != p) {
      xpowers = Fl_powers_pre(x, xdeg, p, pi);
      rd[i] = FlxY_eval_powers_pre(rd_pol, ypowers, xpowers, p, pi);
      sd[i] = FlxY_eval_powers_pre(sd_pol, ypowers, xpowers, p, pi);
      if (rd[i] != 0 && sd[i] != 0) {
        rn[i] = FlxY_eval_powers_pre(rn_pol, ypowers, xpowers, p, pi);
        sn[i] = FlxY_eval_powers_pre(sn_pol, ypowers, xpowers, p, pi);
        ++i;
      }
    }
    avma = av;
  }

  Flv_inv_pre_inplace(rd, p, pi);
  Flv_inv_pre_inplace(sd, p, pi);

  for (i = 1; i <= ncurves; ++i) {
    r[i] = Fl_addmul_pre(X1->rplus1, rn[i], rd[i], p, pi);
    s[i] = Fl_addmul_pre(X1->splus1, sn[i], sd[i], p, pi);
  }
  avma = ltop;
}

/*
 * A curve y^2 = x^3 + a2 x^2 + a4 x is isomorphic to the curve
 *
 *   y^2 = x^3 + (a4 - 1/3*a2^2) x + (2/27*a2^3 - 1/3*a4*a2)
 *       = x^3 + (a4 - a2 c) x + (2 c^3 - a4 c)
 *
 * (where c = a2/3) which is in short form.
 */
INLINE void
a2a4_to_a4a6(ulong *a4, ulong *a6, ulong A2, ulong A4, ulong inv3, ulong p, ulong pi)
{
    ulong c = Fl_mul_pre(A2, inv3, p, pi);
    *a4 = Fl_sub(A4, Fl_mul_pre(A2, c, p, pi), p);
    *a6 = Fl_sub(Fl_double(Fl_mul_pre(c, Fl_sqr_pre(c, p, pi), p, pi), p),
                 Fl_mul_pre(A4, c, p, pi), p);
}


/*
 * A curve y^2 + a1 xy + a3 y = x^3 is isomorphic to the curve
 *
 *   y^2 = x^3 + (1/2*a3*a1 -1/48*a1^4) x + (1/864*a1^6 - 1/24*a3*a1^3 + 1/4*a3^2
 *       = x^3 + c (a3 - 1/3 * c^3) x + 1/3 * c^3(1/9 c^2 a1 - a3) + 1/4 a3^2
 *
 * (where c = a1/2) which is in short form.
 */
INLINE void
a1a3_to_a4a6(
  ulong *a4, ulong *a6,
  ulong a1, ulong a3, ulong inv3, ulong inv4, ulong inv9, ulong p, ulong pi)
{
  ulong c = Fl_halve(a1, p);
  ulong c2 = Fl_sqr_pre(c, p, pi);
  ulong c3_on_3 = Fl_mul_pre(Fl_mul_pre(c, c2, p, pi), inv3, p, pi);
  /* t1 = c^2 * a1 / 9 */
  ulong t1 = Fl_mul_pre(c2, Fl_mul_pre(a1, inv9, p, pi), p, pi);
  /* t1 = c^3/3 (c^2 * a1 / 9 - a3) */
  t1 = Fl_mul_pre(c3_on_3, Fl_sub(t1, a3, p), p, pi);

  *a4 = Fl_mul_pre(c, Fl_sub(a3, c3_on_3, p), p, pi);
  *a6 = Fl_addmul_pre(t1, inv4, Fl_sqr_pre(a3, p, pi), p, pi);
}


/* Assumes m > 3, p > 5 */
/* FIXME: Where do we assume that p > 5?  Some testing suggests that
 * this works for p == 5 also. */
/* Sutherland has a version of this function in tecurve.c
 * around line 306. */
/* FIXME: Could precompute some of the constants. */
INLINE void
bc_to_a4a6(
  ulong *a4, ulong *a6, ulong b, ulong c, ulong p, ulong pi)
{
  /* E: y^2 + (1 - c)xy - by = x^3 - bx^2, so a1 = 1 - c
   * and a2 = a3 = -b. */
  ulong t0, t2, b2, b4, b6, c4, c6;

  b6 = Fl_sub(c, 1, p);
  t0 = Fl_sqr_pre(b6, p, pi);
  b4 = Fl_double(Fl_double(b, p), p);
  b2 = Fl_sub(t0, b4, p);
  b4 = Fl_mul_pre(b6, b, p, pi);
  b6 = Fl_sqr_pre(b, p, pi);
  t2 = Fl_sqr_pre(b2, p, pi);
  c4 = Fl_mul_pre(24 % p, b4, p, pi);
  c4 = Fl_sub(c4, t2, p);

  t0 = Fl_mul_pre(36 % p, b4, p, pi);
  t2 = Fl_sub(t2, t0, p);
  c6 = Fl_mul_pre(b2, t2, p, pi);
  t0 = Fl_mul_pre(216 % p, b6, p, pi);
  c6 = Fl_add(c6, t0, p);

  *a4 = Fl_mul_pre(27 % p, c4, p, pi);
  *a6 = Fl_mul_pre(54 % p, c6, p, pi);
}


INLINE void
bc_to_a4a6_and_tors(
  ulong *a4, ulong *a6, ulong *tx, ulong *ty,
  ulong b, ulong c, ulong p, ulong pi)
{
  bc_to_a4a6(a4, a6, b, c, p, pi);

  /* tx = 3((c - 1)^2 - 4b) */
  *tx = Fl_triple(Fl_sub(Fl_sqr(Fl_sub(c, 1, p), p),
                         Fl_double(Fl_double(b, p), p), p), p);
  /* ty = -108 b */
  *ty = Fl_neg(Fl_mul_pre(108 % p, b, p, pi), p);
}


INLINE void
tq_to_a4a6_and_tors(
  ulong *a4, ulong *a6, ulong *tx, ulong *ty,
  ulong q, ulong t, ulong p, ulong pi, ulong inv3)
{
  ulong A2, A4;
  ulong t2 = Fl_sqr_pre(t, p, pi);
  ulong qtp1 = Fl_addmul_pre(1L, q, t, p, pi);
  /* a2 = t^2-2*(q*t+1), a4 = (1-t^2)*(q*t+1)^2 */
  A2 = Fl_sub(t2, Fl_double(qtp1, p), p);
  A4 = Fl_mul_pre(Fl_sub(1L, t2, p), Fl_sqr_pre(qtp1, p, pi), p, pi);
  a2a4_to_a4a6(a4, a6, A2, A4, inv3, p, pi);

  /* [tx, ty] = [(t+1)*(q*t+1),t*(q*t+1)*(t+1)] */
  *tx = Fl_mul_pre(Fl_add(t, 1L, p), qtp1, p, pi);
  *ty = Fl_mul_pre(t, *tx, p, pi);
  /* Map to isomorphic curve */
  *tx = Fl_addmul_pre(*tx, A2, inv3, p, pi);
}


INLINE void
qt_to_a4a6_and_tors(
  ulong *a4, ulong *a6, ulong *tx, ulong *ty,
  ulong q, ulong t, ulong p, ulong pi, ulong c_12, ulong c_108)
{
  /* z = (q+1)*(t^2-1)/8 */
  ulong z = Fl_div8(Fl_mul_pre(Fl_add(q, 1L, p),
                               Fl_sub(Fl_sqr_pre(t, p, pi),
                                      1L, p), p, pi), p);
  ulong bb = Fl_mul_pre(Fl_sub(q, 1L, p), z, p, pi);
  ulong b = Fl_halve(bb, p);
  /* E=[1,(q^2-1)*(t^2-1)/16,(q^2-1)*(t^2-1)/16,0,0];
   *  = [1, (q-1)*(q+1)*(t^2-1)/16, idem]
   *  = [1, b, b, 0, 0] */
  bc_to_a4a6(a4, a6, Fl_neg(b, p), 0L, p, pi);

  /* [tx,ty]= [(q+1)*(t^2-1)/8,(q+1)^2*(t^2-1)*(t-1)/32];
   *        = [z, (q+1)*(t-1)*z*1/4] */
  *tx = z;
  *ty = Fl_mul_pre(Fl_add(q, 1L, p),
                   Fl_mul_pre(Fl_div4(z, p),
                              Fl_sub(t, 1L, p), p, pi), p, pi);
  /* Map to isomorphic curve:
   * (x, y) |--> (3(12x + 4b + 1), 108(2y + x + b)) */
  *ty = Fl_mul_pre(c_108, Fl_add(Fl_double(*ty, p),
                                 Fl_add(b, *tx, p), p), p, pi);
  *tx = Fl_triple(Fl_addmul_pre(Fl_add(Fl_double(bb, p), 1L, p), c_12, *tx, p, pi),
                  p);
}


INLINE void
t_to_a4a6_and_tors(
  ulong *a4, ulong *a6, ulong *tx, ulong *ty,
  ulong q, ulong t, ulong p, ulong pi,
  ulong inv3, ulong inv4, ulong inv9)
{
  ulong a1, a3, qt = Fl_mul_pre(q, t, p, pi), t1;
  /* a1 = q*t+t+(2-q), a3 = (q*t)*(t-1)+t */
  a1 = Fl_add(Fl_add(qt, t, p), Fl_sub(2L, q, p), p);
  a3 = Fl_addmul_pre(t, qt, Fl_sub(t, 1L, p), p, pi);
  a1a3_to_a4a6(a4, a6, a1, a3, inv3, inv4, inv9, p, pi);
  *tx = Fl_neg(t, p);
  *ty = Fl_sqr_pre(t, p, pi);
  /* Map to isomorphic curve:
   * (x, y) |--> (x + 1/12*a1^2, 1/2*a1*x + (y + 1/2*a3))  */
  t1 = Fl_halve(a1, p);
  *ty = Fl_addmul_pre(Fl_add(*ty, Fl_halve(a3, p), p), *tx, t1, p, pi);
  *tx = Fl_addmul_pre(*tx, inv3, Fl_sqr_pre(t1, p, pi), p, pi);
}


INLINE void
rs_to_a4a6_and_tors(
  ulong *a4, ulong *a6, ulong *tx, ulong *ty,
  ulong r, ulong s, ulong p, ulong pi)
{
  /* c = s (r - 1) */
  ulong c = Fl_mul_pre(s, Fl_sub(r, 1, p), p, pi);
  /* b = rc */
  ulong b = Fl_mul_pre(r, c, p, pi);
  bc_to_a4a6_and_tors(a4, a6, tx, ty, b, c, p, pi);
}


INLINE void
random_curves_with_general_X1(
  ulong *a4, ulong *a6, ulong *tx, ulong *ty,
  long ncurves, long m, ulong p, ulong pi)
{
  pari_sp av = avma;
  const X1_info *X1 = get_X1_info(m);
  GEN r, r_, s, s_;

  r_ = cgetg(ncurves + 1, t_VECSMALL); r = r_ + 1;
  s_ = cgetg(ncurves + 1, t_VECSMALL); s = s_ + 1;
  map_X1_points(r_, s_, X1, ncurves, p, pi);

  switch (X1->map) {
  case RS_MAP:
    while (ncurves--)
      rs_to_a4a6_and_tors(a4++, a6++, tx++, ty++, *r++, *s++, p, pi);
    break;
  case T_MAP:
  {
    ulong inv3 = Fl_inv(3L, p), inv4 = Fl_div4(1L, p);
    ulong inv9 = Fl_sqr_pre(inv3, p, pi);
    while (ncurves--) {
      t_to_a4a6_and_tors(a4++, a6++, tx++, ty++, *r++, *s++,
                         p, pi, inv3, inv4, inv9);
    }
    break;
  }
  case TQ_MAP:
  {
    ulong inv3 = Fl_inv(3L, p);
    while (ncurves--) {
      tq_to_a4a6_and_tors(a4++, a6++, tx++, ty++, *r++, *s++,
                          p, pi, inv3);
    }
    break;
  }
  case QT_MAP:
  {
    ulong c_12 = 12 % p, c_108 = 108 % p;
    while (ncurves--) {
      qt_to_a4a6_and_tors(a4++, a6++, tx++, ty++, *r++, *s++,
                          p, pi, c_12, c_108);
    }
    break;
  }
  }
  avma = av;
}


INLINE void
random_curves_with_11_torsion(
  ulong *a4, ulong *a6, ulong *tx, ulong *ty,
  long ncurves, ulong p, ulong pi)
{
  pari_sp ltop = avma, av;
  const ulong A4 = Fl_neg(432 % p, p), A6 = 8208 % p;
  const ulong c_6 = 6 % p, c_72 = 72 % p, c_108 = 108 % p;
  const ulong inv216 = Fl_inv(216 % p, p);

  av = avma;
  while (ncurves) {
    GEN Q;
    ulong r, s, den;

    /* FIXME: Curve arithmetic in Pari is slow enough that it's faster
     * to generate random points on the curve than it is to compute
     * random multiples of a point. I don't know if this is to be
     * expected or not.  Should check if this is still true when using
     * the fast jac_{add,mul} routines in 'classpoly.c'. Anyway,
     * disabled for now. */
#if 0
    /* Must guard against the possibility that [n]Q = 0 */
    do {
      /* FIXME: should perhaps use p + 1 + 2\sqrt{p} instead of p - 1 */
      n = random_Fl(m1) + 1;  /* m1 = p - 1; */
      Q = Fle_mulu(P, n, A4, p);
    } while (ell_is_inf(Q));
#endif
    /* FIXME: Thing is, if I'm going to do it this way *anyway*, I
     * might as well use the non-elliptic version of X1(11), since the
     * formulae are much nicer. */
    Q = random_Fle_pre(A4, A6, p, pi);

    /* den = 6x + 72 */
    den = Fl_addmul_pre(c_72, c_6, Q[1], p, pi);
    if (den == 0)
      continue;

    /* r = (y + 108)/216, s = 1 + (y - 108)/(6x + 72) */
    r = Fl_mul_pre(Fl_add(Q[2], c_108, p), inv216, p, pi);
    s = Fl_add(1, Fl_div(Fl_sub(Q[2], c_108, p), den, p), p);
    rs_to_a4a6_and_tors(a4++, a6++, tx++, ty++, r, s, p, pi);
    avma = av;
    --ncurves;
  }
  avma = ltop;
}


INLINE void
random_curves_with_elliptic_X1(
  ulong *a4, ulong *a6, ulong *tx, ulong *ty,
  long ncurves, long m, ulong p, ulong pi)
{
  switch (m) {
  case 11:
    random_curves_with_11_torsion(a4, a6, tx, ty, ncurves, p, pi);
    break;
  /* cases 12 and 13 are not missing, it is handled by
   * random_curves_with_rational_X1() and
   * random_curves_with_general_X1() respectively. */
  case 14:
    /*random_curves_with_14_torsion(a4, a6, tx, ty, ncurves, p, pi);
      break;*/
  case 15:
    /*random_curves_with_14_torsion(a4, a6, tx, ty, ncurves, p, pi);
      break;*/
    /* FIXME: random_curves_with_elliptic_X1() currently uses the
     * alternative (but nevertheless very efficient) non-elliptic
     * implementation for levels 14 and 15. */
    random_curves_with_general_X1(a4, a6, tx, ty, ncurves, m, p, pi);
    break;
  default:
    pari_err_BUG("random_curves_with_elliptic_X1");
  }
}


INLINE void
random_curves_with_2_torsion(
  ulong *a4, ulong *a6, ulong *tx, ulong *ty,
  long ncurves, ulong p, ulong pi)
{
  const ulong m1 = p - 1, inv3 = Fl_inv(3L, p);
  while (ncurves--) {
    ulong A2 = random_Fl(m1) + 1;  /* non-zero */
    ulong A4 = random_Fl(m1) + 1;  /* non-zero */

    a2a4_to_a4a6(a4++, a6++, A2, A4, inv3, p, pi);

    /* [0,0] is a 2-torsion point on y^2 = x(x^2 + a2x + a4) which
     * is mapped to [(1/3)a2, 0] on y^2 = x^3 + A4x + A6. */
    *tx++ = Fl_mul_pre(inv3, A2, p, pi);
    *ty++ = 0L;
  };
}


INLINE void
random_curves_with_3_torsion(
  ulong *a4, ulong *a6, ulong *tx, ulong *ty,
  long ncurves, ulong p, ulong pi)
{
  const ulong m1 = p - 1;
  const ulong inv3 = Fl_inv(3, p), inv4 = Fl_inv(4, p);
  const ulong inv9 = Fl_sqr_pre(inv3, p, pi);

  while (ncurves--) {
    ulong a1 = random_Fl(m1) + 1;  /* non-zero */
    ulong a3 = random_Fl(m1) + 1;  /* non-zero */

    a1a3_to_a4a6(a4++, a6++, a1, a3, inv3, inv4, inv9, p, pi);

    /* [0,0] is a 3-torsion point on y^2 + a1xy + a3y = x^3 which
     * is mapped to [a1^2/12, a3/2] on y^2 = x^3 + a4x + a6. */
    *tx++ = Fl_mul_pre(Fl_sqr_pre(Fl_halve(a1, p), p, pi), inv3, p, pi);
    *ty++ = Fl_halve(a3, p);
  }
}


INLINE void
random_curves_with_4_torsion(
  ulong *a4, ulong *a6, ulong *tx, ulong *ty,
  long ncurves, ulong p, ulong pi)
{
  const ulong m1 = p - 1;
  while (ncurves--) {
    ulong b = random_Fl(m1) + 1;  /* non-zero */
    bc_to_a4a6_and_tors(a4++, a6++, tx++, ty++, b, 0L, p, pi);
  }
}


INLINE void
random_curves_with_5_torsion(
  ulong *a4, ulong *a6, ulong *tx, ulong *ty,
  long ncurves, ulong p, ulong pi)
{
  const ulong m1 = p - 1;
  while (ncurves--) {
    ulong b = random_Fl(m1) + 1;  /* non-zero */
    bc_to_a4a6_and_tors(a4++, a6++, tx++, ty++, b, b, p, pi);
  }
}


INLINE void
random_curves_with_6_torsion(
  ulong *a4, ulong *a6, ulong *tx, ulong *ty,
  long ncurves, ulong p, ulong pi)
{
  const ulong m2 = p - 2;
  while (ncurves--) {
    ulong c = random_Fl(m2) + 1; /* in [1, p - 2] */
    ulong b = Fl_add(c, Fl_sqr_pre(c, p, pi), p); /* b = c + c^2 */
    bc_to_a4a6_and_tors(a4++, a6++, tx++, ty++, b, c, p, pi);
  }
}


INLINE void
random_curves_with_7_torsion(
  ulong *a4, ulong *a6, ulong *tx, ulong *ty,
  long ncurves, ulong p, ulong pi)
{
  const ulong m2 = p - 2;
  while (ncurves--) {
    ulong d = random_Fl(m2) + 2; /* in [2, p - 2] */
    ulong c = Fl_sub(Fl_sqr_pre(d, p, pi), d, p); /* c = d^2 - d */
    ulong b = Fl_mul_pre(c, d, p, pi); /* b = d^3 - d^2 */
    bc_to_a4a6_and_tors(a4++, a6++, tx++, ty++, b, c, p, pi);
  }
}


INLINE void
random_curves_with_8_torsion(
  ulong *a4, ulong *a6, ulong *tx, ulong *ty,
  long ncurves, ulong p, ulong pi)
{
  const ulong m1 = p - 1;
  while (ncurves--) {
    ulong d = random_Fl(m1) + 1;  /* non-zero */
    /* b = (2d - 1)(d - 1) */
    ulong b = Fl_mul_pre(Fl_sub(Fl_double(d, p), 1, p),
                         Fl_sub(d, 1, p), p, pi);
    /* c = (2d - 1)(d - 1)/d */
    ulong c = Fl_div(b, d, p);
    bc_to_a4a6_and_tors(a4++, a6++, tx++, ty++, b, c, p, pi);
  }
}


INLINE void
random_curves_with_9_torsion(
  ulong *a4, ulong *a6, ulong *tx, ulong *ty,
  long ncurves, ulong p, ulong pi)
{
  while (ncurves--) {
    ulong f = random_Fl(p);
    /* d = f(f - 1) + 1 = f^2 - f + 1 = f^2 - (f - 1) */
    ulong d = Fl_sub(Fl_sqr_pre(f, p, pi), Fl_sub(f, 1, p), p);
    /* c = fd - f */
    ulong c = Fl_mul_pre(f, Fl_sub(d, 1, p), p, pi);
    /* b = cd */
    ulong b = Fl_mul_pre(c, d, p, pi);
    bc_to_a4a6_and_tors(a4++, a6++, tx++, ty++, b, c, p, pi);
  }
}

INLINE void
random_curves_with_10_torsion(
  ulong *a4, ulong *a6, ulong *tx, ulong *ty,
  long ncurves, ulong p, ulong pi)
{
  while (ncurves) {
    ulong f, f2, d, c, b, t;

    f = random_Fl(p);
    /* t = f - (f - 1)^2 = (3f - 1) - f^2 */
    f2 = Fl_sqr_pre(f, p, pi);
    t = Fl_sub(Fl_sub(Fl_triple(f, p), 1, p), f2, p);
    if (t == 0)
      continue;

    /* d = f^2 / (f - (f - 1)^2) */
    d = Fl_div(f2, t, p);
    /* c = fd - f */
    c = Fl_mul_pre(f, Fl_sub(d, 1, p), p, pi);
    /* b = cd */
    b = Fl_mul_pre(c, d, p, pi);
    bc_to_a4a6_and_tors(a4++, a6++, tx++, ty++, b, c, p, pi);
    --ncurves;
  }
}

INLINE void
random_curves_with_12_torsion(
  ulong *a4, ulong *a6, ulong *tx, ulong *ty,
  long ncurves, ulong p, ulong pi)
{
  while (ncurves--) {
    ulong tau, t1, t2, M, f, d, c, b;
    tau = random_Fl(p);
    /* tau mustn't be = 1.  If it is, just set tau = 2. */
    tau += tau == 1;

    /* t1 = tau - 1 */
    t1 = Fl_sub(tau, 1, p);
    /* M = (3 tau - 3 tau^2 - 1)/(tau - 1) = -(3 tau + 1/(tau - 1)) */
    t2 = Fl_inv(t1, p);
    M = Fl_neg(Fl_add(Fl_triple(tau, p), t2, p), p);
    /* f = M/(1 - tau) = -M / (tau - 1) */
    f = Fl_neg(Fl_mul_pre(M, t2, p, pi), p);
    /* d = M + tau */
    d = Fl_add(M, tau, p);
    /* c = fd - f */
    c = Fl_mul_pre(f, Fl_sub(d, 1, p), p, pi);
    /* b = cd */
    b = Fl_mul_pre(c, d, p, pi);
    bc_to_a4a6_and_tors(a4++, a6++, tx++, ty++, b, c, p, pi);
  }
}


INLINE void
random_curves_with_rational_X1(
  ulong *a4, ulong *a6, ulong *tx, ulong *ty,
  long ncurves, long m, ulong p, ulong pi)
{
  switch (m) {
  case 2:
    random_curves_with_2_torsion(a4, a6, tx, ty, ncurves, p, pi);
    break;
  case 3:
    random_curves_with_3_torsion(a4, a6, tx, ty, ncurves, p, pi);
    break;
  case 4:
    random_curves_with_4_torsion(a4, a6, tx, ty, ncurves, p, pi);
    break;
  case 5:
    random_curves_with_5_torsion(a4, a6, tx, ty, ncurves, p, pi);
    break;
  case 6:
    random_curves_with_6_torsion(a4, a6, tx, ty, ncurves, p, pi);
    break;
  case 7:
    random_curves_with_7_torsion(a4, a6, tx, ty, ncurves, p, pi);
    break;
  case 8:
    random_curves_with_8_torsion(a4, a6, tx, ty, ncurves, p, pi);
    break;
  case 9:
    random_curves_with_9_torsion(a4, a6, tx, ty, ncurves, p, pi);
    break;
  case 10:
    random_curves_with_10_torsion(a4, a6, tx, ty, ncurves, p, pi);
    break;
  /* case 11 is not missing, it is handled by random_curves_with_elliptic_X1() */
  case 12:
    random_curves_with_12_torsion(a4, a6, tx, ty, ncurves, p, pi);
    break;
  default:
    pari_err_BUG("random_curves_with_rational_X1");
  }
}


static void
random_curves_with_any_torsion(
  ulong *a4, ulong *a6, ulong *px, ulong *py,
  long ncurves, ulong p, ulong pi)
{
  pari_sp av = avma;
  ulong c_1728 = 1728 % p;
  long i;
  for (i = 0; i < ncurves; ++i) {
    GEN P;
    ulong j;
    do
      j = random_Fl(p);
    while (j == 0 || j == c_1728);

    Fl_ellj_to_a4a6(j, p, &a4[i], &a6[i]);

    P = random_Fle_pre(a4[i], a6[i], p, pi);
    px[i] = P[1];
    py[i] = P[2];
    avma = av;
  }
}

/* Assumes p < 2^62 or thereabouts. */
INLINE long
torsion_compatible_with_characteristic(long m, ulong p)
{
  ulong two_sqrt_p = usqrt(4*p);
  ulong lo = p + 1 - two_sqrt_p;
  ulong hi = p + 1 + two_sqrt_p;

  /* If ceil(lo/m) <= floor(hi/m) then there is a positive
   * integer n such that lo <= mn <= hi. */
  /* NB: Ceil(a/b) = (a + b - 1)/b, Floor(a/b) = a/b (using integer
   * truncation). */
  return (lo + m - 1)/m <= hi/m;
}


/*
 * Input: pointers a4, a6, t{x,y} where t{x,y} is allowed to be
 * zero, each (non-zero one) pointing to space for at least ncurves
 * elements; an integer m <= 50; a prime p > 3; a flag in {0, 1}.
 *
 * The flag indicates that we should generate curves faster at the
 * expense of not guaranteeing uniform randomness.  This only makes a
 * difference when m = 11, 14 and 15.
 *
 * Output: Put the coefficients of ncurves elliptic curves with
 * m-torsion into a4 and a6.  The actual number of *unique* curves
 * generated is *not* guaranteed to be ncurves, but will be close
 * whenever p is big relative to ncurves.  When non-zero, (torx[i],
 * tory[i]) will contain the m-torsion point on [a4[i], a6[i]].
 */
void
random_curves_with_m_torsion(
  ulong *a4, ulong *a6, ulong *tx, ulong *ty,
  long ncurves, long m, ulong p)
{
  ulong pi = get_Fl_red(p);

  if (ncurves == 0)
    return;

  if (m < 1 || m > LAST_X1_LEVEL
      || ! torsion_compatible_with_characteristic(m, p))
    pari_err_BUG("random_curves_with_m_torsion");
  else if (m == 1)
    random_curves_with_any_torsion(a4, a6, tx, ty, ncurves, p, pi);
  else if (m <= 10 || m == 12)
    random_curves_with_rational_X1(a4, a6, tx, ty, ncurves, m, p, pi);
  else if (m == 11 || m == 14 || m == 15)
    random_curves_with_elliptic_X1(a4, a6, tx, ty, ncurves, m, p, pi);
  else
    random_curves_with_general_X1(a4, a6, tx, ty, ncurves, m, p, pi);

  /* The likelihood of getting *any* zero discriminants is small
   * enough that we can check using this slightly roundabout and
   * expensive manner. */
  while (ncurves--) {
    ulong d = Fl_elldisc_pre(*a4, *a6, p, pi);
    if (d == 0)  /* should almost never be true */
      random_curves_with_m_torsion(a4, a6, tx, ty, 1L, m, p);
    ++a4; ++a6; ++tx; ++ty;
  }
}

#define vZ evalvarn(1) /* variable number for secondary variable */
static const long FLX_0[3] = { evaltyp(t_VECSMALL) | _evallg(2), vZ };
static const long FLX_1[3] = { evaltyp(t_VECSMALL) | _evallg(3), vZ, 1 };
static const long FLX_m1[3] = { evaltyp(t_VECSMALL) | _evallg(3), vZ, -1 };
static const long FLX_Z[4] = { evaltyp(t_VECSMALL) | _evallg(4), vZ, 0, 1 };
static const long FLX_mZ[4] = { evaltyp(t_VECSMALL) | _evallg(4), vZ, 0, -1 };

/*
 * X1 Curves database follows!
 */

/* x^2 + (z^3 + z^2 + 1)*x + (-z^2 - z) */
static const long X1_13_crv_0[5] = {
  evaltyp(t_VECSMALL) | _evallg(5), vZ, 0, -1, -1 }; /* -z^2 - z */
static const long X1_13_crv_1[6] = {
  evaltyp(t_VECSMALL) | _evallg(6), vZ, 1, 0, 1, 1 }; /* z^3 + z^2 + 1 */
static const long *X1_13_crv[5] = {
  (long *)(evaltyp(t_POL) | _evallg(5)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_13_crv_0, X1_13_crv_1, FLX_1
};
/* -z*x + 1 */
static const long *X1_13_r_n[4] = {
  (long *)(evaltyp(t_POL) | _evallg(4)), (long *)(evalvarn(0) | evalsigne(1)),
  FLX_1, FLX_mZ
};
/* 1 */
static const long *X1_13_r_d[3] = {
  (long *)(evaltyp(t_POL) | _evallg(3)), (long *)(evalvarn(0) | evalsigne(1)),
  FLX_1
};
/* -z*x */
static const long *X1_13_s_n[4] = {
  (long *)(evaltyp(t_POL) | _evallg(4)), (long *)(evalvarn(0) | evalsigne(1)),
  FLX_0, FLX_mZ
};
/* x + 1 */
static const long *X1_13_s_d[4] = {
  (long *)(evaltyp(t_POL) | _evallg(4)), (long *)(evalvarn(0) | evalsigne(1)),
  FLX_1, FLX_1
};
/* x^2 + (z^2 + z)*x + z */
static const long X1_14_crv_1[5] = {
  evaltyp(t_VECSMALL) | _evallg(5), vZ, 0, 1, 1 }; /* z^2 + z */
static const long *X1_14_crv[5] = {
  (long *)(evaltyp(t_POL) | _evallg(5)), (long *)(evalvarn(0) | evalsigne(1)),
  FLX_Z, X1_14_crv_1, FLX_1
};
/* -x - z */
static const long *X1_14_r_n[4] = {
  (long *)(evaltyp(t_POL) | _evallg(4)), (long *)(evalvarn(0) | evalsigne(1)),
  FLX_mZ, FLX_m1
};
/* x^2 + (z + 2)*x + (z + 1) */
static const long X1_14_r_d_0[4] = {
  evaltyp(t_VECSMALL) | _evallg(4), vZ, 1, 1 }; /* z + 1 */
static const long X1_14_r_d_1[4] = {
  evaltyp(t_VECSMALL) | _evallg(4), vZ, 2, 1 }; /* z + 2 */
static const long *X1_14_r_d[5] = {
  (long *)(evaltyp(t_POL) | _evallg(5)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_14_r_d_0, X1_14_r_d_1, FLX_1
};
/* (-z + 1) */
static const long X1_14_s_n_0[4] = {
  evaltyp(t_VECSMALL) | _evallg(4), vZ, 1, -1 }; /* -z + 1 */
static const long *X1_14_s_n[3] = {
  (long *)(evaltyp(t_POL) | _evallg(3)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_14_s_n_0
};
/* x + 1 */
static const long *X1_14_s_d[4] = {
  (long *)(evaltyp(t_POL) | _evallg(4)), (long *)(evalvarn(0) | evalsigne(1)),
  FLX_1, FLX_1
};
/* x^2 + (z^2 + z + 1)*x + z^2 */
static const long X1_15_crv_0[5] = {
  evaltyp(t_VECSMALL) | _evallg(5), vZ, 0, 0, 1 }; /* z^2 */
static const long X1_15_crv_1[5] = {
  evaltyp(t_VECSMALL) | _evallg(5), vZ, 1, 1, 1 }; /* z^2 + z + 1 */
static const long *X1_15_crv[5] = {
  (long *)(evaltyp(t_POL) | _evallg(5)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_15_crv_0, X1_15_crv_1, FLX_1
};
/* x^2 + z*x */
static const long *X1_15_r_n[5] = {
  (long *)(evaltyp(t_POL) | _evallg(5)), (long *)(evalvarn(0) | evalsigne(1)),
  FLX_0, FLX_Z, FLX_1
};
/* z^2*x + (z^3 + z^2) */
static const long X1_15_r_d_0[6] = {
  evaltyp(t_VECSMALL) | _evallg(6), vZ, 0, 0, 1, 1 }; /* z^3 + z^2 */
static const long X1_15_r_d_1[5] = {
  evaltyp(t_VECSMALL) | _evallg(5), vZ, 0, 0, 1 }; /* z^2 */
static const long *X1_15_r_d[4] = {
  (long *)(evaltyp(t_POL) | _evallg(4)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_15_r_d_0, X1_15_r_d_1
};
/* x */
static const long *X1_15_s_n[4] = {
  (long *)(evaltyp(t_POL) | _evallg(4)), (long *)(evalvarn(0) | evalsigne(1)),
  FLX_0, FLX_1
};
/* (z^2 + z) */
static const long X1_15_s_d_0[5] = {
  evaltyp(t_VECSMALL) | _evallg(5), vZ, 0, 1, 1 }; /* z^2 + z */
static const long *X1_15_s_d[3] = {
  (long *)(evaltyp(t_POL) | _evallg(3)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_15_s_d_0
};
/* x^2 + (z^3 + z^2 - z + 1)*x + z^2 */
static const long X1_16_crv_0[5] = {
  evaltyp(t_VECSMALL) | _evallg(5), vZ, 0, 0, 1 }; /* z^2 */
static const long X1_16_crv_1[6] = {
  evaltyp(t_VECSMALL) | _evallg(6), vZ, 1, -1, 1, 1 }; /* z^3 + z^2 - z + 1 */
static const long *X1_16_crv[5] = {
  (long *)(evaltyp(t_POL) | _evallg(5)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_16_crv_0, X1_16_crv_1, FLX_1
};
/* x^2 + (-z + 1)*x + z^2 */
static const long X1_16_r_n_0[5] = {
  evaltyp(t_VECSMALL) | _evallg(5), vZ, 0, 0, 1 }; /* z^2 */
static const long X1_16_r_n_1[4] = {
  evaltyp(t_VECSMALL) | _evallg(4), vZ, 1, -1 }; /* -z + 1 */
static const long *X1_16_r_n[5] = {
  (long *)(evaltyp(t_POL) | _evallg(5)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_16_r_n_0, X1_16_r_n_1, FLX_1
};
/* -x + (z^2 + z - 1) */
static const long X1_16_r_d_0[5] = {
  evaltyp(t_VECSMALL) | _evallg(5), vZ, -1, 1, 1 }; /* z^2 + z - 1 */
static const long *X1_16_r_d[4] = {
  (long *)(evaltyp(t_POL) | _evallg(4)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_16_r_d_0, FLX_m1
};
/* -x + z */
static const long *X1_16_s_n[4] = {
  (long *)(evaltyp(t_POL) | _evallg(4)), (long *)(evalvarn(0) | evalsigne(1)),
  FLX_Z, FLX_m1
};
/* (z + 1) */
static const long X1_16_s_d_0[4] = {
  evaltyp(t_VECSMALL) | _evallg(4), vZ, 1, 1 }; /* z + 1 */
static const long *X1_16_s_d[3] = {
  (long *)(evaltyp(t_POL) | _evallg(3)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_16_s_d_0
};
/* x^4 + (z^3 + z^2 - z + 2)*x^3 + (z^3 - 3*z + 1)*x^2 + (-z^4 - 2*z)*x + (z^3 + z^2) */
static const long X1_17_crv_0[6] = {
  evaltyp(t_VECSMALL) | _evallg(6), vZ, 0, 0, 1, 1 }; /* z^3 + z^2 */
static const long X1_17_crv_1[7] = {
  evaltyp(t_VECSMALL) | _evallg(7), vZ, 0, -2, 0, 0, -1 }; /* -z^4 - 2*z */
static const long X1_17_crv_2[6] = {
  evaltyp(t_VECSMALL) | _evallg(6), vZ, 1, -3, 0, 1 }; /* z^3 - 3*z + 1 */
static const long X1_17_crv_3[6] = {
  evaltyp(t_VECSMALL) | _evallg(6), vZ, 2, -1, 1, 1 }; /* z^3 + z^2 - z + 2 */
static const long *X1_17_crv[7] = {
  (long *)(evaltyp(t_POL) | _evallg(7)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_17_crv_0, X1_17_crv_1, X1_17_crv_2, X1_17_crv_3, FLX_1
};
/* -x + (z^2 + z) */
static const long X1_17_r_n_0[5] = {
  evaltyp(t_VECSMALL) | _evallg(5), vZ, 0, 1, 1 }; /* z^2 + z */
static const long *X1_17_r_n[4] = {
  (long *)(evaltyp(t_POL) | _evallg(4)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_17_r_n_0, FLX_m1
};
/* -x^2 + (z - 1)*x + (z^2 + z) */
static const long X1_17_r_d_0[5] = {
  evaltyp(t_VECSMALL) | _evallg(5), vZ, 0, 1, 1 }; /* z^2 + z */
static const long X1_17_r_d_1[4] = {
  evaltyp(t_VECSMALL) | _evallg(4), vZ, -1, 1 }; /* z - 1 */
static const long *X1_17_r_d[5] = {
  (long *)(evaltyp(t_POL) | _evallg(5)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_17_r_d_0, X1_17_r_d_1, FLX_m1
};
/* (z + 1) */
static const long X1_17_s_n_0[4] = {
  evaltyp(t_VECSMALL) | _evallg(4), vZ, 1, 1 }; /* z + 1 */
static const long *X1_17_s_n[3] = {
  (long *)(evaltyp(t_POL) | _evallg(3)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_17_s_n_0
};
/* x + (z + 1) */
static const long X1_17_s_d_0[4] = {
  evaltyp(t_VECSMALL) | _evallg(4), vZ, 1, 1 }; /* z + 1 */
static const long *X1_17_s_d[4] = {
  (long *)(evaltyp(t_POL) | _evallg(4)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_17_s_d_0, FLX_1
};
/* x^2 + (z^3 - 2*z^2 + 3*z + 1)*x + 2*z */
static const long X1_18_crv_0[4] = {
  evaltyp(t_VECSMALL) | _evallg(4), vZ, 0, 2 }; /* 2*z */
static const long X1_18_crv_1[6] = {
  evaltyp(t_VECSMALL) | _evallg(6), vZ, 1, 3, -2, 1 }; /* z^3 - 2*z^2 + 3*z + 1 */
static const long *X1_18_crv[5] = {
  (long *)(evaltyp(t_POL) | _evallg(5)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_18_crv_0, X1_18_crv_1, FLX_1
};
/* -z*x + (z^2 - 3*z + 1) */
static const long X1_18_r_n_0[5] = {
  evaltyp(t_VECSMALL) | _evallg(5), vZ, 1, -3, 1 }; /* z^2 - 3*z + 1 */
static const long *X1_18_r_n[4] = {
  (long *)(evaltyp(t_POL) | _evallg(4)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_18_r_n_0, FLX_mZ
};
/* (z^3 - 2*z^2 + z)*x + (z^2 - 2*z + 1) */
static const long X1_18_r_d_0[5] = {
  evaltyp(t_VECSMALL) | _evallg(5), vZ, 1, -2, 1 }; /* z^2 - 2*z + 1 */
static const long X1_18_r_d_1[6] = {
  evaltyp(t_VECSMALL) | _evallg(6), vZ, 0, 1, -2, 1 }; /* z^3 - 2*z^2 + z */
static const long *X1_18_r_d[4] = {
  (long *)(evaltyp(t_POL) | _evallg(4)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_18_r_d_0, X1_18_r_d_1
};
/* -x + (z^2 - 2*z) */
static const long X1_18_s_n_0[5] = {
  evaltyp(t_VECSMALL) | _evallg(5), vZ, 0, -2, 1 }; /* z^2 - 2*z */
static const long *X1_18_s_n[4] = {
  (long *)(evaltyp(t_POL) | _evallg(4)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_18_s_n_0, FLX_m1
};
/* -x^2 + (-z - 2)*x + (z^2 - 3*z) */
static const long X1_18_s_d_0[5] = {
  evaltyp(t_VECSMALL) | _evallg(5), vZ, 0, -3, 1 }; /* z^2 - 3*z */
static const long X1_18_s_d_1[4] = {
  evaltyp(t_VECSMALL) | _evallg(4), vZ, -2, -1 }; /* -z - 2 */
static const long *X1_18_s_d[5] = {
  (long *)(evaltyp(t_POL) | _evallg(5)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_18_s_d_0, X1_18_s_d_1, FLX_m1
};
/* x^5 + (-z^2 - 2)*x^4 + (-2*z^3 - 2*z^2 - 2*z + 1)*x^3 + (z^5 + 3*z^4 + 7*z^3 + 6*z^2 + 2*z)*x^2 + (-z^5 - 2*z^4 - 4*z^3 - 3*z^2)*x + (z^3 + z^2) */
static const long X1_19_crv_0[6] = {
  evaltyp(t_VECSMALL) | _evallg(6), vZ, 0, 0, 1, 1 }; /* z^3 + z^2 */
static const long X1_19_crv_1[8] = {
  evaltyp(t_VECSMALL) | _evallg(8), vZ, 0, 0, -3, -4, -2, -1 }; /* -z^5 - 2*z^4 - 4*z^3 - 3*z^2 */
static const long X1_19_crv_2[8] = {
  evaltyp(t_VECSMALL) | _evallg(8), vZ, 0, 2, 6, 7, 3, 1 }; /* z^5 + 3*z^4 + 7*z^3 + 6*z^2 + 2*z */
static const long X1_19_crv_3[6] = {
  evaltyp(t_VECSMALL) | _evallg(6), vZ, 1, -2, -2, -2 }; /* -2*z^3 - 2*z^2 - 2*z + 1 */
static const long X1_19_crv_4[5] = {
  evaltyp(t_VECSMALL) | _evallg(5), vZ, -2, 0, -1 }; /* -z^2 - 2 */
static const long *X1_19_crv[8] = {
  (long *)(evaltyp(t_POL) | _evallg(8)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_19_crv_0, X1_19_crv_1, X1_19_crv_2, X1_19_crv_3, X1_19_crv_4, FLX_1
};
/* z*x^2 + (z^2 - z)*x - z^2 */
static const long X1_19_r_n_0[5] = {
  evaltyp(t_VECSMALL) | _evallg(5), vZ, 0, 0, -1 }; /* -z^2 */
static const long X1_19_r_n_1[5] = {
  evaltyp(t_VECSMALL) | _evallg(5), vZ, 0, -1, 1 }; /* z^2 - z */
static const long *X1_19_r_n[5] = {
  (long *)(evaltyp(t_POL) | _evallg(5)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_19_r_n_0, X1_19_r_n_1, FLX_Z
};
/* (-z - 1)*x^2 + (-z^2 + 1)*x + (z^3 + 3*z^2 + 2*z) */
static const long X1_19_r_d_0[6] = {
  evaltyp(t_VECSMALL) | _evallg(6), vZ, 0, 2, 3, 1 }; /* z^3 + 3*z^2 + 2*z */
static const long X1_19_r_d_1[5] = {
  evaltyp(t_VECSMALL) | _evallg(5), vZ, 1, 0, -1 }; /* -z^2 + 1 */
static const long X1_19_r_d_2[4] = {
  evaltyp(t_VECSMALL) | _evallg(4), vZ, -1, -1 }; /* -z - 1 */
static const long *X1_19_r_d[5] = {
  (long *)(evaltyp(t_POL) | _evallg(5)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_19_r_d_0, X1_19_r_d_1, X1_19_r_d_2
};
/* z*x - z */
static const long *X1_19_s_n[4] = {
  (long *)(evaltyp(t_POL) | _evallg(4)), (long *)(evalvarn(0) | evalsigne(1)),
  FLX_mZ, FLX_Z
};
/* (-z - 1)*x + (z^2 + 2*z + 1) */
static const long X1_19_s_d_0[5] = {
  evaltyp(t_VECSMALL) | _evallg(5), vZ, 1, 2, 1 }; /* z^2 + 2*z + 1 */
static const long X1_19_s_d_1[4] = {
  evaltyp(t_VECSMALL) | _evallg(4), vZ, -1, -1 }; /* -z - 1 */
static const long *X1_19_s_d[4] = {
  (long *)(evaltyp(t_POL) | _evallg(4)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_19_s_d_0, X1_19_s_d_1
};
/* x^3 - z^3*x^2 - z^2*x + z */
static const long X1_20_crv_1[5] = {
  evaltyp(t_VECSMALL) | _evallg(5), vZ, 0, 0, -1 }; /* -z^2 */
static const long X1_20_crv_2[6] = {
  evaltyp(t_VECSMALL) | _evallg(6), vZ, 0, 0, 0, -1 }; /* -z^3 */
static const long *X1_20_crv[6] = {
  (long *)(evaltyp(t_POL) | _evallg(6)), (long *)(evalvarn(0) | evalsigne(1)),
  FLX_Z, X1_20_crv_1, X1_20_crv_2, FLX_1
};
/* -x + z */
static const long *X1_20_r_n[4] = {
  (long *)(evaltyp(t_POL) | _evallg(4)), (long *)(evalvarn(0) | evalsigne(1)),
  FLX_Z, FLX_m1
};
/* z*x - 1 */
static const long *X1_20_r_d[4] = {
  (long *)(evaltyp(t_POL) | _evallg(4)), (long *)(evalvarn(0) | evalsigne(1)),
  FLX_m1, FLX_Z
};
/* 4*z^3*x^3 + (-4*z^4 - 8*z^2)*x^2 + (8*z^3 + 4*z)*x - 4*z^2 */
static const long X1_20_s_n_0[5] = {
  evaltyp(t_VECSMALL) | _evallg(5), vZ, 0, 0, -4 }; /* -4*z^2 */
static const long X1_20_s_n_1[6] = {
  evaltyp(t_VECSMALL) | _evallg(6), vZ, 0, 4, 0, 8 }; /* 8*z^3 + 4*z */
static const long X1_20_s_n_2[7] = {
  evaltyp(t_VECSMALL) | _evallg(7), vZ, 0, 0, -8, 0, -4 }; /* -4*z^4 - 8*z^2 */
static const long X1_20_s_n_3[6] = {
  evaltyp(t_VECSMALL) | _evallg(6), vZ, 0, 0, 0, 4 }; /* 4*z^3 */
static const long *X1_20_s_n[6] = {
  (long *)(evaltyp(t_POL) | _evallg(6)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_20_s_n_0, X1_20_s_n_1, X1_20_s_n_2, X1_20_s_n_3
};
/* (z^4 + 4*z^2 - 1)*x^3 + (-10*z^3 - 2*z)*x^2 + (3*z^4 + 8*z^2 + 1)*x + (-2*z^3 - 2*z) */
static const long X1_20_s_d_0[6] = {
  evaltyp(t_VECSMALL) | _evallg(6), vZ, 0, -2, 0, -2 }; /* -2*z^3 - 2*z */
static const long X1_20_s_d_1[7] = {
  evaltyp(t_VECSMALL) | _evallg(7), vZ, 1, 0, 8, 0, 3 }; /* 3*z^4 + 8*z^2 + 1 */
static const long X1_20_s_d_2[6] = {
  evaltyp(t_VECSMALL) | _evallg(6), vZ, 0, -2, 0, -10 }; /* -10*z^3 - 2*z */
static const long X1_20_s_d_3[7] = {
  evaltyp(t_VECSMALL) | _evallg(7), vZ, -1, 0, 4, 0, 1 }; /* z^4 + 4*z^2 - 1 */
static const long *X1_20_s_d[6] = {
  (long *)(evaltyp(t_POL) | _evallg(6)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_20_s_d_0, X1_20_s_d_1, X1_20_s_d_2, X1_20_s_d_3
};
/* x^4 + (3*z^2 + 1)*x^3 + (z^5 + z^4 + 2*z^2 + 2*z)*x^2 + (2*z^4 + z^3 + z)*x + z^3 */
static const long X1_21_crv_0[6] = {
  evaltyp(t_VECSMALL) | _evallg(6), vZ, 0, 0, 0, 1 }; /* z^3 */
static const long X1_21_crv_1[7] = {
  evaltyp(t_VECSMALL) | _evallg(7), vZ, 0, 1, 0, 1, 2 }; /* 2*z^4 + z^3 + z */
static const long X1_21_crv_2[8] = {
  evaltyp(t_VECSMALL) | _evallg(8), vZ, 0, 2, 2, 0, 1, 1 }; /* z^5 + z^4 + 2*z^2 + 2*z */
static const long X1_21_crv_3[5] = {
  evaltyp(t_VECSMALL) | _evallg(5), vZ, 1, 0, 3 }; /* 3*z^2 + 1 */
static const long *X1_21_crv[7] = {
  (long *)(evaltyp(t_POL) | _evallg(7)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_21_crv_0, X1_21_crv_1, X1_21_crv_2, X1_21_crv_3, FLX_1
};
/* (z + 1)*x^3 + (z + 2)*x^2 + x */
static const long X1_21_r_n_2[4] = {
  evaltyp(t_VECSMALL) | _evallg(4), vZ, 2, 1 }; /* z + 2 */
static const long X1_21_r_n_3[4] = {
  evaltyp(t_VECSMALL) | _evallg(4), vZ, 1, 1 }; /* z + 1 */
static const long *X1_21_r_n[6] = {
  (long *)(evaltyp(t_POL) | _evallg(6)), (long *)(evalvarn(0) | evalsigne(1)),
  FLX_0, FLX_1, X1_21_r_n_2, X1_21_r_n_3
};
/* -z*x^3 + (z^2 - 1)*x^2 + 2*z*x + 1 */
static const long X1_21_r_d_1[4] = {
  evaltyp(t_VECSMALL) | _evallg(4), vZ, 0, 2 }; /* 2*z */
static const long X1_21_r_d_2[5] = {
  evaltyp(t_VECSMALL) | _evallg(5), vZ, -1, 0, 1 }; /* z^2 - 1 */
static const long *X1_21_r_d[6] = {
  (long *)(evaltyp(t_POL) | _evallg(6)), (long *)(evalvarn(0) | evalsigne(1)),
  FLX_1, X1_21_r_d_1, X1_21_r_d_2, FLX_mZ
};
/* x^2 + x */
static const long *X1_21_s_n[5] = {
  (long *)(evaltyp(t_POL) | _evallg(5)), (long *)(evalvarn(0) | evalsigne(1)),
  FLX_0, FLX_1, FLX_1
};
/* z*x + 1 */
static const long *X1_21_s_d[4] = {
  (long *)(evaltyp(t_POL) | _evallg(4)), (long *)(evalvarn(0) | evalsigne(1)),
  FLX_1, FLX_Z
};
/* x^4 + (z^3 + 2*z^2 + z + 2)*x^3 + (z^5 + z^4 + 2*z^3 + 2*z^2 + 1)*x^2 + (z^5 - z^4 - 2*z^3 - z^2 - z)*x + (-z^4 - z^3) */
static const long X1_22_crv_0[7] = {
  evaltyp(t_VECSMALL) | _evallg(7), vZ, 0, 0, 0, -1, -1 }; /* -z^4 - z^3 */
static const long X1_22_crv_1[8] = {
  evaltyp(t_VECSMALL) | _evallg(8), vZ, 0, -1, -1, -2, -1, 1 }; /* z^5 - z^4 - 2*z^3 - z^2 - z */
static const long X1_22_crv_2[8] = {
  evaltyp(t_VECSMALL) | _evallg(8), vZ, 1, 0, 2, 2, 1, 1 }; /* z^5 + z^4 + 2*z^3 + 2*z^2 + 1 */
static const long X1_22_crv_3[6] = {
  evaltyp(t_VECSMALL) | _evallg(6), vZ, 2, 1, 2, 1 }; /* z^3 + 2*z^2 + z + 2 */
static const long *X1_22_crv[7] = {
  (long *)(evaltyp(t_POL) | _evallg(7)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_22_crv_0, X1_22_crv_1, X1_22_crv_2, X1_22_crv_3, FLX_1
};
/* (z^2 + z + 1)*x + z^2 */
static const long X1_22_r_n_0[5] = {
  evaltyp(t_VECSMALL) | _evallg(5), vZ, 0, 0, 1 }; /* z^2 */
static const long X1_22_r_n_1[5] = {
  evaltyp(t_VECSMALL) | _evallg(5), vZ, 1, 1, 1 }; /* z^2 + z + 1 */
static const long *X1_22_r_n[4] = {
  (long *)(evaltyp(t_POL) | _evallg(4)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_22_r_n_0, X1_22_r_n_1
};
/* x + (z^3 + 2*z^2) */
static const long X1_22_r_d_0[6] = {
  evaltyp(t_VECSMALL) | _evallg(6), vZ, 0, 0, 2, 1 }; /* z^3 + 2*z^2 */
static const long *X1_22_r_d[4] = {
  (long *)(evaltyp(t_POL) | _evallg(4)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_22_r_d_0, FLX_1
};
/* (z + 1)*x */
static const long X1_22_s_n_1[4] = {
  evaltyp(t_VECSMALL) | _evallg(4), vZ, 1, 1 }; /* z + 1 */
static const long *X1_22_s_n[4] = {
  (long *)(evaltyp(t_POL) | _evallg(4)), (long *)(evalvarn(0) | evalsigne(1)),
  FLX_0, X1_22_s_n_1
};
/* x + z^2 */
static const long X1_22_s_d_0[5] = {
  evaltyp(t_VECSMALL) | _evallg(5), vZ, 0, 0, 1 }; /* z^2 */
static const long *X1_22_s_d[4] = {
  (long *)(evaltyp(t_POL) | _evallg(4)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_22_s_d_0, FLX_1
};
/* x^7 + (z^5 - z^4 + z^3 + 4*z^2 + 3)*x^6 + (z^7 + 3*z^5 + z^4 + 5*z^3 + 7*z^2 - 4*z + 3)*x^5 + (2*z^7 + 3*z^5 - z^4 - 2*z^3 - z^2 - 8*z + 1)*x^4 + (z^7 - 4*z^6 - 5*z^5 - 6*z^4 - 6*z^3 - 2*z^2 - 3*z)*x^3 + (-3*z^6 + 5*z^4 + 3*z^3 + 3*z^2 + 2*z)*x^2 + (3*z^5 + 4*z^4 + z)*x + (-z^4 - 2*z^3 - z^2) */
static const long X1_23_crv_0[7] = {
  evaltyp(t_VECSMALL) | _evallg(7), vZ, 0, 0, -1, -2, -1 }; /* -z^4 - 2*z^3 - z^2 */
static const long X1_23_crv_1[8] = {
  evaltyp(t_VECSMALL) | _evallg(8), vZ, 0, 1, 0, 0, 4, 3 }; /* 3*z^5 + 4*z^4 + z */
static const long X1_23_crv_2[9] = {
  evaltyp(t_VECSMALL) | _evallg(9), vZ, 0, 2, 3, 3, 5, 0, -3 }; /* -3*z^6 + 5*z^4 + 3*z^3 + 3*z^2 + 2*z */
static const long X1_23_crv_3[10] = {
  evaltyp(t_VECSMALL) | _evallg(10), vZ, 0, -3, -2, -6, -6, -5, -4, 1 }; /* z^7 - 4*z^6 - 5*z^5 - 6*z^4 - 6*z^3 - 2*z^2 - 3*z */
static const long X1_23_crv_4[10] = {
  evaltyp(t_VECSMALL) | _evallg(10), vZ, 1, -8, -1, -2, -1, 3, 0, 2 }; /* 2*z^7 + 3*z^5 - z^4 - 2*z^3 - z^2 - 8*z + 1 */
static const long X1_23_crv_5[10] = {
  evaltyp(t_VECSMALL) | _evallg(10), vZ, 3, -4, 7, 5, 1, 3, 0, 1 }; /* z^7 + 3*z^5 + z^4 + 5*z^3 + 7*z^2 - 4*z + 3 */
static const long X1_23_crv_6[8] = {
  evaltyp(t_VECSMALL) | _evallg(8), vZ, 3, 0, 4, 1, -1, 1 }; /* z^5 - z^4 + z^3 + 4*z^2 + 3 */
static const long *X1_23_crv[10] = {
  (long *)(evaltyp(t_POL) | _evallg(10)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_23_crv_0, X1_23_crv_1, X1_23_crv_2, X1_23_crv_3, X1_23_crv_4, X1_23_crv_5, X1_23_crv_6, FLX_1
};
/* x + (z^2 + z + 1) */
static const long X1_23_r_n_0[5] = {
  evaltyp(t_VECSMALL) | _evallg(5), vZ, 1, 1, 1 }; /* z^2 + z + 1 */
static const long *X1_23_r_n[4] = {
  (long *)(evaltyp(t_POL) | _evallg(4)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_23_r_n_0, FLX_1
};
/* -z*x + z^2 */
static const long X1_23_r_d_0[5] = {
  evaltyp(t_VECSMALL) | _evallg(5), vZ, 0, 0, 1 }; /* z^2 */
static const long *X1_23_r_d[4] = {
  (long *)(evaltyp(t_POL) | _evallg(4)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_23_r_d_0, FLX_mZ
};
/* x + (z + 1) */
static const long X1_23_s_n_0[4] = {
  evaltyp(t_VECSMALL) | _evallg(4), vZ, 1, 1 }; /* z + 1 */
static const long *X1_23_s_n[4] = {
  (long *)(evaltyp(t_POL) | _evallg(4)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_23_s_n_0, FLX_1
};
/* z */
static const long *X1_23_s_d[3] = {
  (long *)(evaltyp(t_POL) | _evallg(3)), (long *)(evalvarn(0) | evalsigne(1)),
  FLX_Z
};
/* (z^2 - 3)*x^4 + (z^5 + 2*z^4 + 2*z^3 + 2*z^2 - 3*z)*x^2 + (-z^4 - z^2) */
static const long X1_24_crv_0[7] = {
  evaltyp(t_VECSMALL) | _evallg(7), vZ, 0, 0, -1, 0, -1 }; /* -z^4 - z^2 */
static const long X1_24_crv_2[8] = {
  evaltyp(t_VECSMALL) | _evallg(8), vZ, 0, -3, 2, 2, 2, 1 }; /* z^5 + 2*z^4 + 2*z^3 + 2*z^2 - 3*z */
static const long X1_24_crv_4[5] = {
  evaltyp(t_VECSMALL) | _evallg(5), vZ, -3, 0, 1 }; /* z^2 - 3 */
static const long *X1_24_crv[7] = {
  (long *)(evaltyp(t_POL) | _evallg(7)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_24_crv_0, FLX_0, X1_24_crv_2, FLX_0, X1_24_crv_4
};
/* x */
static const long *X1_24_r_n[4] = {
  (long *)(evaltyp(t_POL) | _evallg(4)), (long *)(evalvarn(0) | evalsigne(1)),
  FLX_0, FLX_1
};
/* 1 */
static const long *X1_24_r_d[3] = {
  (long *)(evaltyp(t_POL) | _evallg(3)), (long *)(evalvarn(0) | evalsigne(1)),
  FLX_1
};
/* 4*x^3 + 4*z*x */
static const long X1_24_s_n_1[4] = {
  evaltyp(t_VECSMALL) | _evallg(4), vZ, 0, 4 }; /* 4*z */
static const long X1_24_s_n_3[3] = {
  evaltyp(t_VECSMALL) | _evallg(3), vZ, 4 }; /* 4 */
static const long *X1_24_s_n[6] = {
  (long *)(evaltyp(t_POL) | _evallg(6)), (long *)(evalvarn(0) | evalsigne(1)),
  FLX_0, X1_24_s_n_1, FLX_0, X1_24_s_n_3
};
/* (z - 2)*x^4 + (-4*z - 2)*x^2 - z */
static const long X1_24_s_d_2[4] = {
  evaltyp(t_VECSMALL) | _evallg(4), vZ, -2, -4 }; /* -4*z - 2 */
static const long X1_24_s_d_4[4] = {
  evaltyp(t_VECSMALL) | _evallg(4), vZ, -2, 1 }; /* z - 2 */
static const long *X1_24_s_d[7] = {
  (long *)(evaltyp(t_POL) | _evallg(7)), (long *)(evalvarn(0) | evalsigne(1)),
  FLX_mZ, FLX_0, X1_24_s_d_2, FLX_0, X1_24_s_d_4
};
/* z*u^5 + (z^4 - 2*z^3 - z^2 + 2*z + 1)*u^4 + (-2*z^6 + 2*z^4 - 4*z^3 - 2*z^2 + 2)*u^3 + (z^8 + z^7 - 2*z^6 + z^5 - z^4 - z^3 - 2*z^2 - z + 1)*u^2 + (z^8 + z^7 + 2*z^6 + z^5 - 2*z^4 + z^3 - z^2)*u + z^6 */
static const long X1_25_crv_0[9] = {
  evaltyp(t_VECSMALL) | _evallg(9), vZ, 0, 0, 0, 0, 0, 0, 1 }; /* z^6 */
static const long X1_25_crv_1[11] = {
  evaltyp(t_VECSMALL) | _evallg(11), vZ, 0, 0, -1, 1, -2, 1, 2, 1, 1 }; /* z^8 + z^7 + 2*z^6 + z^5 - 2*z^4 + z^3 - z^2 */
static const long X1_25_crv_2[11] = {
  evaltyp(t_VECSMALL) | _evallg(11), vZ, 1, -1, -2, -1, -1, 1, -2, 1, 1 }; /* z^8 + z^7 - 2*z^6 + z^5 - z^4 - z^3 - 2*z^2 - z + 1 */
static const long X1_25_crv_3[9] = {
  evaltyp(t_VECSMALL) | _evallg(9), vZ, 2, 0, -2, -4, 2, 0, -2 }; /* -2*z^6 + 2*z^4 - 4*z^3 - 2*z^2 + 2 */
static const long X1_25_crv_4[7] = {
  evaltyp(t_VECSMALL) | _evallg(7), vZ, 1, 2, -1, -2, 1 }; /* z^4 - 2*z^3 - z^2 + 2*z + 1 */
static const long *X1_25_crv[8] = {
  (long *)(evaltyp(t_POL) | _evallg(8)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_25_crv_0, X1_25_crv_1, X1_25_crv_2, X1_25_crv_3, X1_25_crv_4, FLX_Z
};
/* -z^2*u^6 + (2*z^4 - 2*z^2 - 2*z)*u^5 + (-z^6 + 2*z^5 + 5*z^4 + z^3 - 4*z - 1)*u^4 + (-2*z^7 - 3*z^6 + 4*z^5 + 4*z^4 + 5*z^3 - z - 2)*u^3 + (-z^8 - 4*z^7 - 2*z^6 - z^5 + 3*z^4 + 5*z^3 - z^2 + z - 1)*u^2 + (-z^8 - z^7 - 2*z^6 - 3*z^5 + 2*z^4 + z^3)*u - z^6 */
static const long X1_25_r_n_0[9] = {
  evaltyp(t_VECSMALL) | _evallg(9), vZ, 0, 0, 0, 0, 0, 0, -1 }; /* -z^6 */
static const long X1_25_r_n_1[11] = {
  evaltyp(t_VECSMALL) | _evallg(11), vZ, 0, 0, 0, 1, 2, -3, -2, -1, -1 }; /* -z^8 - z^7 - 2*z^6 - 3*z^5 + 2*z^4 + z^3 */
static const long X1_25_r_n_2[11] = {
  evaltyp(t_VECSMALL) | _evallg(11), vZ, -1, 1, -1, 5, 3, -1, -2, -4, -1 }; /* -z^8 - 4*z^7 - 2*z^6 - z^5 + 3*z^4 + 5*z^3 - z^2 + z - 1 */
static const long X1_25_r_n_3[10] = {
  evaltyp(t_VECSMALL) | _evallg(10), vZ, -2, -1, 0, 5, 4, 4, -3, -2 }; /* -2*z^7 - 3*z^6 + 4*z^5 + 4*z^4 + 5*z^3 - z - 2 */
static const long X1_25_r_n_4[9] = {
  evaltyp(t_VECSMALL) | _evallg(9), vZ, -1, -4, 0, 1, 5, 2, -1 }; /* -z^6 + 2*z^5 + 5*z^4 + z^3 - 4*z - 1 */
static const long X1_25_r_n_5[7] = {
  evaltyp(t_VECSMALL) | _evallg(7), vZ, 0, -2, -2, 0, 2 }; /* 2*z^4 - 2*z^2 - 2*z */
static const long X1_25_r_n_6[5] = {
  evaltyp(t_VECSMALL) | _evallg(5), vZ, 0, 0, -1 }; /* -z^2 */
static const long *X1_25_r_n[9] = {
  (long *)(evaltyp(t_POL) | _evallg(9)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_25_r_n_0, X1_25_r_n_1, X1_25_r_n_2, X1_25_r_n_3, X1_25_r_n_4, X1_25_r_n_5, X1_25_r_n_6
};
/* -z^2*u^6 + (2*z^4 + z^3 - 2*z^2 - 2*z)*u^5 + (-z^6 + 7*z^4 + 3*z^3 + z^2 - 4*z - 1)*u^4 + (-z^7 - 8*z^6 + z^5 + 7*z^4 + 7*z^3 + 2*z^2 - z - 2)*u^3 + (2*z^8 - 6*z^7 - 11*z^6 - 2*z^5 + 3*z^4 + 7*z^3 + z - 1)*u^2 + (3*z^9 + 3*z^8 - 6*z^7 - 6*z^6 - 3*z^5 + z^4 + 2*z^3)*u + (z^10 + 3*z^9 + z^8 - 2*z^7 - z^6) */
static const long X1_25_r_d_0[13] = {
  evaltyp(t_VECSMALL) | _evallg(13), vZ, 0, 0, 0, 0, 0, 0, -1, -2, 1, 3, 1 }; /* z^10 + 3*z^9 + z^8 - 2*z^7 - z^6 */
static const long X1_25_r_d_1[12] = {
  evaltyp(t_VECSMALL) | _evallg(12), vZ, 0, 0, 0, 2, 1, -3, -6, -6, 3, 3 }; /* 3*z^9 + 3*z^8 - 6*z^7 - 6*z^6 - 3*z^5 + z^4 + 2*z^3 */
static const long X1_25_r_d_2[11] = {
  evaltyp(t_VECSMALL) | _evallg(11), vZ, -1, 1, 0, 7, 3, -2, -11, -6, 2 }; /* 2*z^8 - 6*z^7 - 11*z^6 - 2*z^5 + 3*z^4 + 7*z^3 + z - 1 */
static const long X1_25_r_d_3[10] = {
  evaltyp(t_VECSMALL) | _evallg(10), vZ, -2, -1, 2, 7, 7, 1, -8, -1 }; /* -z^7 - 8*z^6 + z^5 + 7*z^4 + 7*z^3 + 2*z^2 - z - 2 */
static const long X1_25_r_d_4[9] = {
  evaltyp(t_VECSMALL) | _evallg(9), vZ, -1, -4, 1, 3, 7, 0, -1 }; /* -z^6 + 7*z^4 + 3*z^3 + z^2 - 4*z - 1 */
static const long X1_25_r_d_5[7] = {
  evaltyp(t_VECSMALL) | _evallg(7), vZ, 0, -2, -2, 1, 2 }; /* 2*z^4 + z^3 - 2*z^2 - 2*z */
static const long X1_25_r_d_6[5] = {
  evaltyp(t_VECSMALL) | _evallg(5), vZ, 0, 0, -1 }; /* -z^2 */
static const long *X1_25_r_d[9] = {
  (long *)(evaltyp(t_POL) | _evallg(9)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_25_r_d_0, X1_25_r_d_1, X1_25_r_d_2, X1_25_r_d_3, X1_25_r_d_4, X1_25_r_d_5, X1_25_r_d_6
};
/* -z*u^3 + (z^3 - z - 1)*u^2 + (z^4 + z^3 - z^2 + z - 1)*u + z^4 */
static const long X1_25_s_n_0[7] = {
  evaltyp(t_VECSMALL) | _evallg(7), vZ, 0, 0, 0, 0, 1 }; /* z^4 */
static const long X1_25_s_n_1[7] = {
  evaltyp(t_VECSMALL) | _evallg(7), vZ, -1, 1, -1, 1, 1 }; /* z^4 + z^3 - z^2 + z - 1 */
static const long X1_25_s_n_2[6] = {
  evaltyp(t_VECSMALL) | _evallg(6), vZ, -1, -1, 0, 1 }; /* z^3 - z - 1 */
static const long *X1_25_s_n[6] = {
  (long *)(evaltyp(t_POL) | _evallg(6)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_25_s_n_0, X1_25_s_n_1, X1_25_s_n_2, FLX_mZ
};
/* -z*u^3 + (z^3 + z^2 - z - 1)*u^2 + (2*z^3 + z - 1)*u + (-z^5 + z^3) */
static const long X1_25_s_d_0[8] = {
  evaltyp(t_VECSMALL) | _evallg(8), vZ, 0, 0, 0, 1, 0, -1 }; /* -z^5 + z^3 */
static const long X1_25_s_d_1[6] = {
  evaltyp(t_VECSMALL) | _evallg(6), vZ, -1, 1, 0, 2 }; /* 2*z^3 + z - 1 */
static const long X1_25_s_d_2[6] = {
  evaltyp(t_VECSMALL) | _evallg(6), vZ, -1, -1, 1, 1 }; /* z^3 + z^2 - z - 1 */
static const long *X1_25_s_d[6] = {
  (long *)(evaltyp(t_POL) | _evallg(6)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_25_s_d_0, X1_25_s_d_1, X1_25_s_d_2, FLX_mZ
};
/* x^6 + (3*z^2 + 4*z - 2)*x^5 + (3*z^4 + 10*z^3 - 9*z + 1)*x^4 + (z^6 + 7*z^5 + 8*z^4 - 14*z^3 - 11*z^2 + 6*z)*x^3 + (z^7 + 4*z^6 - z^5 - 13*z^4 + 2*z^3 + 10*z^2 - z)*x^2 + (-z^6 + 7*z^4 + 4*z^3 - 2*z^2)*x + (-z^4 - z^3) */
static const long X1_26_crv_0[7] = {
  evaltyp(t_VECSMALL) | _evallg(7), vZ, 0, 0, 0, -1, -1 }; /* -z^4 - z^3 */
static const long X1_26_crv_1[9] = {
  evaltyp(t_VECSMALL) | _evallg(9), vZ, 0, 0, -2, 4, 7, 0, -1 }; /* -z^6 + 7*z^4 + 4*z^3 - 2*z^2 */
static const long X1_26_crv_2[10] = {
  evaltyp(t_VECSMALL) | _evallg(10), vZ, 0, -1, 10, 2, -13, -1, 4, 1 }; /* z^7 + 4*z^6 - z^5 - 13*z^4 + 2*z^3 + 10*z^2 - z */
static const long X1_26_crv_3[9] = {
  evaltyp(t_VECSMALL) | _evallg(9), vZ, 0, 6, -11, -14, 8, 7, 1 }; /* z^6 + 7*z^5 + 8*z^4 - 14*z^3 - 11*z^2 + 6*z */
static const long X1_26_crv_4[7] = {
  evaltyp(t_VECSMALL) | _evallg(7), vZ, 1, -9, 0, 10, 3 }; /* 3*z^4 + 10*z^3 - 9*z + 1 */
static const long X1_26_crv_5[5] = {
  evaltyp(t_VECSMALL) | _evallg(5), vZ, -2, 4, 3 }; /* 3*z^2 + 4*z - 2 */
static const long *X1_26_crv[9] = {
  (long *)(evaltyp(t_POL) | _evallg(9)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_26_crv_0, X1_26_crv_1, X1_26_crv_2, X1_26_crv_3, X1_26_crv_4, X1_26_crv_5, FLX_1
};
/* z*x^2 + (z^3 + 3*z^2)*x - z^2 */
static const long X1_26_r_n_0[5] = {
  evaltyp(t_VECSMALL) | _evallg(5), vZ, 0, 0, -1 }; /* -z^2 */
static const long X1_26_r_n_1[6] = {
  evaltyp(t_VECSMALL) | _evallg(6), vZ, 0, 0, 3, 1 }; /* z^3 + 3*z^2 */
static const long *X1_26_r_n[5] = {
  (long *)(evaltyp(t_POL) | _evallg(5)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_26_r_n_0, X1_26_r_n_1, FLX_Z
};
/* (z + 1)*x^2 + (z^3 + 4*z^2 + 3*z)*x + (z^3 + z^2) */
static const long X1_26_r_d_0[6] = {
  evaltyp(t_VECSMALL) | _evallg(6), vZ, 0, 0, 1, 1 }; /* z^3 + z^2 */
static const long X1_26_r_d_1[6] = {
  evaltyp(t_VECSMALL) | _evallg(6), vZ, 0, 3, 4, 1 }; /* z^3 + 4*z^2 + 3*z */
static const long X1_26_r_d_2[4] = {
  evaltyp(t_VECSMALL) | _evallg(4), vZ, 1, 1 }; /* z + 1 */
static const long *X1_26_r_d[5] = {
  (long *)(evaltyp(t_POL) | _evallg(5)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_26_r_d_0, X1_26_r_d_1, X1_26_r_d_2
};
/* z*x - z */
static const long *X1_26_s_n[4] = {
  (long *)(evaltyp(t_POL) | _evallg(4)), (long *)(evalvarn(0) | evalsigne(1)),
  FLX_mZ, FLX_Z
};
/* (z + 1)*x */
static const long X1_26_s_d_1[4] = {
  evaltyp(t_VECSMALL) | _evallg(4), vZ, 1, 1 }; /* z + 1 */
static const long *X1_26_s_d[4] = {
  (long *)(evaltyp(t_POL) | _evallg(4)), (long *)(evalvarn(0) | evalsigne(1)),
  FLX_0, X1_26_s_d_1
};
/* (z^2 - 2*z + 1)*u^6 + (z^5 - 2*z^4 + z^3 + 2*z^2 - 4*z + 2)*u^5 + (-z^7 + 5*z^5 - 5*z^4 + 2*z^3 - 2*z^2 + 1)*u^4 + (z^8 - 4*z^7 - z^6 + 5*z^5 + 2*z^3 - 5*z^2 + 2*z)*u^3 + (3*z^8 - 4*z^7 - 2*z^6 - 2*z^5 + 3*z^4 + 2*z^3 - z^2 + z)*u^2 + (3*z^8 - 3*z^5)*u + (z^8 + z^7 + z^6) */
static const long X1_27_crv_0[11] = {
  evaltyp(t_VECSMALL) | _evallg(11), vZ, 0, 0, 0, 0, 0, 0, 1, 1, 1 }; /* z^8 + z^7 + z^6 */
static const long X1_27_crv_1[11] = {
  evaltyp(t_VECSMALL) | _evallg(11), vZ, 0, 0, 0, 0, 0, -3, 0, 0, 3 }; /* 3*z^8 - 3*z^5 */
static const long X1_27_crv_2[11] = {
  evaltyp(t_VECSMALL) | _evallg(11), vZ, 0, 1, -1, 2, 3, -2, -2, -4, 3 }; /* 3*z^8 - 4*z^7 - 2*z^6 - 2*z^5 + 3*z^4 + 2*z^3 - z^2 + z */
static const long X1_27_crv_3[11] = {
  evaltyp(t_VECSMALL) | _evallg(11), vZ, 0, 2, -5, 2, 0, 5, -1, -4, 1 }; /* z^8 - 4*z^7 - z^6 + 5*z^5 + 2*z^3 - 5*z^2 + 2*z */
static const long X1_27_crv_4[10] = {
  evaltyp(t_VECSMALL) | _evallg(10), vZ, 1, 0, -2, 2, -5, 5, 0, -1 }; /* -z^7 + 5*z^5 - 5*z^4 + 2*z^3 - 2*z^2 + 1 */
static const long X1_27_crv_5[8] = {
  evaltyp(t_VECSMALL) | _evallg(8), vZ, 2, -4, 2, 1, -2, 1 }; /* z^5 - 2*z^4 + z^3 + 2*z^2 - 4*z + 2 */
static const long X1_27_crv_6[5] = {
  evaltyp(t_VECSMALL) | _evallg(5), vZ, 1, -2, 1 }; /* z^2 - 2*z + 1 */
static const long *X1_27_crv[9] = {
  (long *)(evaltyp(t_POL) | _evallg(9)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_27_crv_0, X1_27_crv_1, X1_27_crv_2, X1_27_crv_3, X1_27_crv_4, X1_27_crv_5, X1_27_crv_6
};
/* (-z^4 + 2*z^2 - 2*z + 1)*u^4 + (z^5 - 4*z^4 - z^3 + 6*z^2 - 4*z + 2)*u^3 + (3*z^5 - 5*z^4 - 2*z^3 + 5*z^2 - z + 1)*u^2 + (3*z^5 - 2*z^4 - z^3 + z^2)*u + z^5 */
static const long X1_27_r_n_0[8] = {
  evaltyp(t_VECSMALL) | _evallg(8), vZ, 0, 0, 0, 0, 0, 1 }; /* z^5 */
static const long X1_27_r_n_1[8] = {
  evaltyp(t_VECSMALL) | _evallg(8), vZ, 0, 0, 1, -1, -2, 3 }; /* 3*z^5 - 2*z^4 - z^3 + z^2 */
static const long X1_27_r_n_2[8] = {
  evaltyp(t_VECSMALL) | _evallg(8), vZ, 1, -1, 5, -2, -5, 3 }; /* 3*z^5 - 5*z^4 - 2*z^3 + 5*z^2 - z + 1 */
static const long X1_27_r_n_3[8] = {
  evaltyp(t_VECSMALL) | _evallg(8), vZ, 2, -4, 6, -1, -4, 1 }; /* z^5 - 4*z^4 - z^3 + 6*z^2 - 4*z + 2 */
static const long X1_27_r_n_4[7] = {
  evaltyp(t_VECSMALL) | _evallg(7), vZ, 1, -2, 2, 0, -1 }; /* -z^4 + 2*z^2 - 2*z + 1 */
static const long *X1_27_r_n[7] = {
  (long *)(evaltyp(t_POL) | _evallg(7)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_27_r_n_0, X1_27_r_n_1, X1_27_r_n_2, X1_27_r_n_3, X1_27_r_n_4
};
/* (-z^3 + z^2 - z + 1)*u^4 + (z^5 - z^4 - 2*z^3 + z^2 - z + 2)*u^3 + (3*z^5 - 2*z^4 - z^3 - 2*z^2 + 2*z + 1)*u^2 + (3*z^5 - z^4 - 3*z^2 + z)*u + (z^5 - z^2) */
static const long X1_27_r_d_0[8] = {
  evaltyp(t_VECSMALL) | _evallg(8), vZ, 0, 0, -1, 0, 0, 1 }; /* z^5 - z^2 */
static const long X1_27_r_d_1[8] = {
  evaltyp(t_VECSMALL) | _evallg(8), vZ, 0, 1, -3, 0, -1, 3 }; /* 3*z^5 - z^4 - 3*z^2 + z */
static const long X1_27_r_d_2[8] = {
  evaltyp(t_VECSMALL) | _evallg(8), vZ, 1, 2, -2, -1, -2, 3 }; /* 3*z^5 - 2*z^4 - z^3 - 2*z^2 + 2*z + 1 */
static const long X1_27_r_d_3[8] = {
  evaltyp(t_VECSMALL) | _evallg(8), vZ, 2, -1, 1, -2, -1, 1 }; /* z^5 - z^4 - 2*z^3 + z^2 - z + 2 */
static const long X1_27_r_d_4[6] = {
  evaltyp(t_VECSMALL) | _evallg(6), vZ, 1, -1, 1, -1 }; /* -z^3 + z^2 - z + 1 */
static const long *X1_27_r_d[7] = {
  (long *)(evaltyp(t_POL) | _evallg(7)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_27_r_d_0, X1_27_r_d_1, X1_27_r_d_2, X1_27_r_d_3, X1_27_r_d_4
};
/* (z^3 - 2*z + 1)*u^3 + (-z^4 + 2*z^3 + z^2 - 4*z + 2)*u^2 + (-2*z^4 + z^3 + z^2 - z + 1)*u - z^4 */
static const long X1_27_s_n_0[7] = {
  evaltyp(t_VECSMALL) | _evallg(7), vZ, 0, 0, 0, 0, -1 }; /* -z^4 */
static const long X1_27_s_n_1[7] = {
  evaltyp(t_VECSMALL) | _evallg(7), vZ, 1, -1, 1, 1, -2 }; /* -2*z^4 + z^3 + z^2 - z + 1 */
static const long X1_27_s_n_2[7] = {
  evaltyp(t_VECSMALL) | _evallg(7), vZ, 2, -4, 1, 2, -1 }; /* -z^4 + 2*z^3 + z^2 - 4*z + 2 */
static const long X1_27_s_n_3[6] = {
  evaltyp(t_VECSMALL) | _evallg(6), vZ, 1, -2, 0, 1 }; /* z^3 - 2*z + 1 */
static const long *X1_27_s_n[6] = {
  (long *)(evaltyp(t_POL) | _evallg(6)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_27_s_n_0, X1_27_s_n_1, X1_27_s_n_2, X1_27_s_n_3
};
/* (-z + 1)*u^3 + (-z^4 - z + 2)*u^2 + (-2*z^4 + 2*z + 1)*u + (-z^4 + z) */
static const long X1_27_s_d_0[7] = {
  evaltyp(t_VECSMALL) | _evallg(7), vZ, 0, 1, 0, 0, -1 }; /* -z^4 + z */
static const long X1_27_s_d_1[7] = {
  evaltyp(t_VECSMALL) | _evallg(7), vZ, 1, 2, 0, 0, -2 }; /* -2*z^4 + 2*z + 1 */
static const long X1_27_s_d_2[7] = {
  evaltyp(t_VECSMALL) | _evallg(7), vZ, 2, -1, 0, 0, -1 }; /* -z^4 - z + 2 */
static const long X1_27_s_d_3[4] = {
  evaltyp(t_VECSMALL) | _evallg(4), vZ, 1, -1 }; /* -z + 1 */
static const long *X1_27_s_d[6] = {
  (long *)(evaltyp(t_POL) | _evallg(6)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_27_s_d_0, X1_27_s_d_1, X1_27_s_d_2, X1_27_s_d_3
};
/* (z^5 + 3*z^4 + 3*z^3 + z^2)*x^6 + (z^8 + 2*z^7 + z^6 + 11*z^4 + 22*z^3 + 11*z^2)*x^5 + (9*z^7 + 9*z^6 - 6*z^5 - 6*z^4 + 45*z^3 + 45*z^2)*x^4 + (-5*z^8 + 28*z^6 - 42*z^4 + 84*z^2 - 1)*x^3 + (-25*z^7 + 25*z^6 + 23*z^5 - 23*z^4 - 67*z^3 + 67*z^2 + 5*z - 5)*x^2 + (6*z^8 - 12*z^7 - 12*z^6 + 36*z^5 - 36*z^3 + 12*z^2 + 12*z - 6)*x + (-z^9 + 3*z^8 - 8*z^6 + 6*z^5 + 6*z^4 - 8*z^3 + 3*z - 1) */
static const long X1_28_crv_0[12] = {
  evaltyp(t_VECSMALL) | _evallg(12), vZ, -1, 3, 0, -8, 6, 6, -8, 0, 3, -1 }; /* -z^9 + 3*z^8 - 8*z^6 + 6*z^5 + 6*z^4 - 8*z^3 + 3*z - 1 */
static const long X1_28_crv_1[11] = {
  evaltyp(t_VECSMALL) | _evallg(11), vZ, -6, 12, 12, -36, 0, 36, -12, -12, 6 }; /* 6*z^8 - 12*z^7 - 12*z^6 + 36*z^5 - 36*z^3 + 12*z^2 + 12*z - 6 */
static const long X1_28_crv_2[10] = {
  evaltyp(t_VECSMALL) | _evallg(10), vZ, -5, 5, 67, -67, -23, 23, 25, -25 }; /* -25*z^7 + 25*z^6 + 23*z^5 - 23*z^4 - 67*z^3 + 67*z^2 + 5*z - 5 */
static const long X1_28_crv_3[11] = {
  evaltyp(t_VECSMALL) | _evallg(11), vZ, -1, 0, 84, 0, -42, 0, 28, 0, -5 }; /* -5*z^8 + 28*z^6 - 42*z^4 + 84*z^2 - 1 */
static const long X1_28_crv_4[10] = {
  evaltyp(t_VECSMALL) | _evallg(10), vZ, 0, 0, 45, 45, -6, -6, 9, 9 }; /* 9*z^7 + 9*z^6 - 6*z^5 - 6*z^4 + 45*z^3 + 45*z^2 */
static const long X1_28_crv_5[11] = {
  evaltyp(t_VECSMALL) | _evallg(11), vZ, 0, 0, 11, 22, 11, 0, 1, 2, 1 }; /* z^8 + 2*z^7 + z^6 + 11*z^4 + 22*z^3 + 11*z^2 */
static const long X1_28_crv_6[8] = {
  evaltyp(t_VECSMALL) | _evallg(8), vZ, 0, 0, 1, 3, 3, 1 }; /* z^5 + 3*z^4 + 3*z^3 + z^2 */
static const long *X1_28_crv[9] = {
  (long *)(evaltyp(t_POL) | _evallg(9)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_28_crv_0, X1_28_crv_1, X1_28_crv_2, X1_28_crv_3, X1_28_crv_4, X1_28_crv_5, X1_28_crv_6
};
/* (z + 1)*x + 2 */
static const long X1_28_r_n_0[3] = {
  evaltyp(t_VECSMALL) | _evallg(3), vZ, 2 }; /* 2 */
static const long X1_28_r_n_1[4] = {
  evaltyp(t_VECSMALL) | _evallg(4), vZ, 1, 1 }; /* z + 1 */
static const long *X1_28_r_n[4] = {
  (long *)(evaltyp(t_POL) | _evallg(4)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_28_r_n_0, X1_28_r_n_1
};
/* 2*z */
static const long X1_28_r_d_0[4] = {
  evaltyp(t_VECSMALL) | _evallg(4), vZ, 0, 2 }; /* 2*z */
static const long *X1_28_r_d[3] = {
  (long *)(evaltyp(t_POL) | _evallg(3)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_28_r_d_0
};
/* (-z - 1)*x - 2 */
static const long X1_28_s_n_0[3] = {
  evaltyp(t_VECSMALL) | _evallg(3), vZ, -2 }; /* -2 */
static const long X1_28_s_n_1[4] = {
  evaltyp(t_VECSMALL) | _evallg(4), vZ, -1, -1 }; /* -z - 1 */
static const long *X1_28_s_n[4] = {
  (long *)(evaltyp(t_POL) | _evallg(4)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_28_s_n_0, X1_28_s_n_1
};
/* 2 */
static const long X1_28_s_d_0[3] = {
  evaltyp(t_VECSMALL) | _evallg(3), vZ, 2 }; /* 2 */
static const long *X1_28_s_d[3] = {
  (long *)(evaltyp(t_POL) | _evallg(3)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_28_s_d_0
};
/* x^11 + (2*z^3 + 5*z^2 + 5*z - 3)*x^10 + (z^6 + 8*z^5 + 18*z^4 + 11*z^3 - 5*z^2 - 12*z + 3)*x^9 + (3*z^8 + 15*z^7 + 29*z^6 + 6*z^5 - 39*z^4 - 19*z^3 + 5*z^2 + 5*z - 1)*x^8 + (3*z^10 + 14*z^9 + 18*z^8 - 26*z^7 - 99*z^6 - 45*z^5 + 95*z^4 + 25*z^3 - 37*z^2 + 7*z)*x^7 + (z^12 + 5*z^11 - 44*z^9 - 106*z^8 - 40*z^7 + 197*z^6 + 190*z^5 - 140*z^4 - 93*z^3 + 59*z^2 - 6*z)*x^6 + (-2*z^12 - 16*z^11 - 37*z^10 + 9*z^9 + 184*z^8 + 256*z^7 - 99*z^6 - 346*z^5 + 20*z^4 + 130*z^3 - 32*z^2 + z)*x^5 + (z^12 + 15*z^11 + 65*z^10 + 99*z^9 - 55*z^8 - 320*z^7 - 165*z^6 + 223*z^5 + 100*z^4 - 66*z^3 + 5*z^2)*x^4 + (-4*z^11 - 36*z^10 - 108*z^9 - 98*z^8 + 110*z^7 + 191*z^6 - 15*z^5 - 64*z^4 + 10*z^3)*x^3 + (6*z^10 + 38*z^9 + 76*z^8 + 25*z^7 - 55*z^6 - 26*z^5 + 10*z^4)*x^2 + (-4*z^9 - 17*z^8 - 18*z^7 + 5*z^5)*x + (z^8 + 2*z^7 + z^6) */
static const long X1_29_crv_0[11] = {
  evaltyp(t_VECSMALL) | _evallg(11), vZ, 0, 0, 0, 0, 0, 0, 1, 2, 1 }; /* z^8 + 2*z^7 + z^6 */
static const long X1_29_crv_1[12] = {
  evaltyp(t_VECSMALL) | _evallg(12), vZ, 0, 0, 0, 0, 0, 5, 0, -18, -17, -4 }; /* -4*z^9 - 17*z^8 - 18*z^7 + 5*z^5 */
static const long X1_29_crv_2[13] = {
  evaltyp(t_VECSMALL) | _evallg(13), vZ, 0, 0, 0, 0, 10, -26, -55, 25, 76, 38, 6 }; /* 6*z^10 + 38*z^9 + 76*z^8 + 25*z^7 - 55*z^6 - 26*z^5 + 10*z^4 */
static const long X1_29_crv_3[14] = {
  evaltyp(t_VECSMALL) | _evallg(14), vZ, 0, 0, 0, 10, -64, -15, 191, 110, -98, -108, -36, -4 }; /* -4*z^11 - 36*z^10 - 108*z^9 - 98*z^8 + 110*z^7 + 191*z^6 - 15*z^5 - 64*z^4 + 10*z^3 */
static const long X1_29_crv_4[15] = {
  evaltyp(t_VECSMALL) | _evallg(15), vZ, 0, 0, 5, -66, 100, 223, -165, -320, -55, 99, 65, 15, 1 }; /* z^12 + 15*z^11 + 65*z^10 + 99*z^9 - 55*z^8 - 320*z^7 - 165*z^6 + 223*z^5 + 100*z^4 - 66*z^3 + 5*z^2 */
static const long X1_29_crv_5[15] = {
  evaltyp(t_VECSMALL) | _evallg(15), vZ, 0, 1, -32, 130, 20, -346, -99, 256, 184, 9, -37, -16, -2 }; /* -2*z^12 - 16*z^11 - 37*z^10 + 9*z^9 + 184*z^8 + 256*z^7 - 99*z^6 - 346*z^5 + 20*z^4 + 130*z^3 - 32*z^2 + z */
static const long X1_29_crv_6[15] = {
  evaltyp(t_VECSMALL) | _evallg(15), vZ, 0, -6, 59, -93, -140, 190, 197, -40, -106, -44, 0, 5, 1 }; /* z^12 + 5*z^11 - 44*z^9 - 106*z^8 - 40*z^7 + 197*z^6 + 190*z^5 - 140*z^4 - 93*z^3 + 59*z^2 - 6*z */
static const long X1_29_crv_7[13] = {
  evaltyp(t_VECSMALL) | _evallg(13), vZ, 0, 7, -37, 25, 95, -45, -99, -26, 18, 14, 3 }; /* 3*z^10 + 14*z^9 + 18*z^8 - 26*z^7 - 99*z^6 - 45*z^5 + 95*z^4 + 25*z^3 - 37*z^2 + 7*z */
static const long X1_29_crv_8[11] = {
  evaltyp(t_VECSMALL) | _evallg(11), vZ, -1, 5, 5, -19, -39, 6, 29, 15, 3 }; /* 3*z^8 + 15*z^7 + 29*z^6 + 6*z^5 - 39*z^4 - 19*z^3 + 5*z^2 + 5*z - 1 */
static const long X1_29_crv_9[9] = {
  evaltyp(t_VECSMALL) | _evallg(9), vZ, 3, -12, -5, 11, 18, 8, 1 }; /* z^6 + 8*z^5 + 18*z^4 + 11*z^3 - 5*z^2 - 12*z + 3 */
static const long X1_29_crv_10[6] = {
  evaltyp(t_VECSMALL) | _evallg(6), vZ, -3, 5, 5, 2 }; /* 2*z^3 + 5*z^2 + 5*z - 3 */
static const long *X1_29_crv[14] = {
  (long *)(evaltyp(t_POL) | _evallg(14)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_29_crv_0, X1_29_crv_1, X1_29_crv_2, X1_29_crv_3, X1_29_crv_4, X1_29_crv_5, X1_29_crv_6, X1_29_crv_7, X1_29_crv_8, X1_29_crv_9, X1_29_crv_10, FLX_1
};
/* -x + (-z^3 - z^2 - z) */
static const long X1_29_r_n_0[6] = {
  evaltyp(t_VECSMALL) | _evallg(6), vZ, 0, -1, -1, -1 }; /* -z^3 - z^2 - z */
static const long *X1_29_r_n[4] = {
  (long *)(evaltyp(t_POL) | _evallg(4)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_29_r_n_0, FLX_m1
};
/* (z^2 + z - 1)*x - z */
static const long X1_29_r_d_1[5] = {
  evaltyp(t_VECSMALL) | _evallg(5), vZ, -1, 1, 1 }; /* z^2 + z - 1 */
static const long *X1_29_r_d[4] = {
  (long *)(evaltyp(t_POL) | _evallg(4)), (long *)(evalvarn(0) | evalsigne(1)),
  FLX_mZ, X1_29_r_d_1
};
/* -z*x - z^2 */
static const long X1_29_s_n_0[5] = {
  evaltyp(t_VECSMALL) | _evallg(5), vZ, 0, 0, -1 }; /* -z^2 */
static const long *X1_29_s_n[4] = {
  (long *)(evaltyp(t_POL) | _evallg(4)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_29_s_n_0, FLX_mZ
};
/* (z - 1)*x - z */
static const long X1_29_s_d_1[4] = {
  evaltyp(t_VECSMALL) | _evallg(4), vZ, -1, 1 }; /* z - 1 */
static const long *X1_29_s_d[4] = {
  (long *)(evaltyp(t_POL) | _evallg(4)), (long *)(evalvarn(0) | evalsigne(1)),
  FLX_mZ, X1_29_s_d_1
};
/* x^6 + (z^6 - 5*z^5 + 6*z^4 + 3*z^3 - 6*z^2 + 7*z + 3)*x^5 + (z^7 - 3*z^6 - 13*z^5 + 44*z^4 - 18*z^3 + z^2 + 18*z + 3)*x^4 + (z^8 - 3*z^7 - 13*z^6 + 27*z^5 + 46*z^4 - 32*z^3 + 21*z^2 + 15*z + 1)*x^3 + (2*z^8 - 16*z^7 + 18*z^6 + 40*z^5 + 12*z^4 - 12*z^3 + 18*z^2 + 4*z)*x^2 + (-8*z^7 + 28*z^6 + 12*z^5 + 4*z^2)*x + 8*z^6 */
static const long X1_30_crv_0[9] = {
  evaltyp(t_VECSMALL) | _evallg(9), vZ, 0, 0, 0, 0, 0, 0, 8 }; /* 8*z^6 */
static const long X1_30_crv_1[10] = {
  evaltyp(t_VECSMALL) | _evallg(10), vZ, 0, 0, 4, 0, 0, 12, 28, -8 }; /* -8*z^7 + 28*z^6 + 12*z^5 + 4*z^2 */
static const long X1_30_crv_2[11] = {
  evaltyp(t_VECSMALL) | _evallg(11), vZ, 0, 4, 18, -12, 12, 40, 18, -16, 2 }; /* 2*z^8 - 16*z^7 + 18*z^6 + 40*z^5 + 12*z^4 - 12*z^3 + 18*z^2 + 4*z */
static const long X1_30_crv_3[11] = {
  evaltyp(t_VECSMALL) | _evallg(11), vZ, 1, 15, 21, -32, 46, 27, -13, -3, 1 }; /* z^8 - 3*z^7 - 13*z^6 + 27*z^5 + 46*z^4 - 32*z^3 + 21*z^2 + 15*z + 1 */
static const long X1_30_crv_4[10] = {
  evaltyp(t_VECSMALL) | _evallg(10), vZ, 3, 18, 1, -18, 44, -13, -3, 1 }; /* z^7 - 3*z^6 - 13*z^5 + 44*z^4 - 18*z^3 + z^2 + 18*z + 3 */
static const long X1_30_crv_5[9] = {
  evaltyp(t_VECSMALL) | _evallg(9), vZ, 3, 7, -6, 3, 6, -5, 1 }; /* z^6 - 5*z^5 + 6*z^4 + 3*z^3 - 6*z^2 + 7*z + 3 */
static const long *X1_30_crv[9] = {
  (long *)(evaltyp(t_POL) | _evallg(9)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_30_crv_0, X1_30_crv_1, X1_30_crv_2, X1_30_crv_3, X1_30_crv_4, X1_30_crv_5, FLX_1
};
/* x + 1 */
static const long *X1_30_r_n[4] = {
  (long *)(evaltyp(t_POL) | _evallg(4)), (long *)(evalvarn(0) | evalsigne(1)),
  FLX_1, FLX_1
};
/* 1 */
static const long *X1_30_r_d[3] = {
  (long *)(evaltyp(t_POL) | _evallg(3)), (long *)(evalvarn(0) | evalsigne(1)),
  FLX_1
};
/* 4*x^2 + (4*z + 4)*x + 4*z */
static const long X1_30_s_n_0[4] = {
  evaltyp(t_VECSMALL) | _evallg(4), vZ, 0, 4 }; /* 4*z */
static const long X1_30_s_n_1[4] = {
  evaltyp(t_VECSMALL) | _evallg(4), vZ, 4, 4 }; /* 4*z + 4 */
static const long X1_30_s_n_2[3] = {
  evaltyp(t_VECSMALL) | _evallg(3), vZ, 4 }; /* 4 */
static const long *X1_30_s_n[5] = {
  (long *)(evaltyp(t_POL) | _evallg(5)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_30_s_n_0, X1_30_s_n_1, X1_30_s_n_2
};
/* (z - 3)*x^3 - 6*x^2 + (-4*z - 4)*x - 4*z */
static const long X1_30_s_d_0[4] = {
  evaltyp(t_VECSMALL) | _evallg(4), vZ, 0, -4 }; /* -4*z */
static const long X1_30_s_d_1[4] = {
  evaltyp(t_VECSMALL) | _evallg(4), vZ, -4, -4 }; /* -4*z - 4 */
static const long X1_30_s_d_2[3] = {
  evaltyp(t_VECSMALL) | _evallg(3), vZ, -6 }; /* -6 */
static const long X1_30_s_d_3[4] = {
  evaltyp(t_VECSMALL) | _evallg(4), vZ, -3, 1 }; /* z - 3 */
static const long *X1_30_s_d[6] = {
  (long *)(evaltyp(t_POL) | _evallg(6)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_30_s_d_0, X1_30_s_d_1, X1_30_s_d_2, X1_30_s_d_3
};
/* u^12 + (z^10 - z^9 - 8*z^8 + 6*z^7 + 23*z^6 - 12*z^5 - 26*z^4 + 8*z^3 + 10*z^2 + 7*z - 3)*u^11 + (z^11 - 8*z^10 - 11*z^9 + 61*z^8 + 45*z^7 - 152*z^6 - 70*z^5 + 129*z^4 + 37*z^3 - 24*z + 3)*u^10 + (-8*z^11 + 17*z^10 + 105*z^9 - 93*z^8 - 387*z^7 + 145*z^6 + 453*z^5 - 57*z^4 - 91*z^3 - 73*z^2 + 31*z - 1)*u^9 + (-z^12 + 25*z^11 + 27*z^10 - 273*z^9 - 260*z^8 + 745*z^7 + 569*z^6 - 572*z^5 - 266*z^4 - 36*z^3 + 131*z^2 - 19*z)*u^8 + (5*z^12 - 32*z^11 - 162*z^10 + 193*z^9 + 911*z^8 - 147*z^7 - 1254*z^6 - 78*z^5 + 301*z^4 + 222*z^3 - 99*z^2 + 6*z)*u^7 + (-10*z^12 + 240*z^10 + 268*z^9 - 864*z^8 - 967*z^7 + 713*z^6 + 598*z^5 + 28*z^4 - 216*z^3 + 37*z^2 - z)*u^6 + (10*z^12 + 44*z^11 - 115*z^10 - 537*z^9 + 19*z^8 + 1033*z^7 + 242*z^6 - 351*z^5 - 200*z^4 + 91*z^3 - 6*z^2)*u^5 + (-5*z^12 - 47*z^11 - 52*z^10 + 293*z^9 + 448*z^8 - 266*z^7 - 390*z^6 - 17*z^5 + 112*z^4 - 15*z^3)*u^4 + (z^12 + 20*z^11 + 76*z^10 - z^9 - 247*z^8 - 119*z^7 + 103*z^6 + 68*z^5 - 20*z^4)*u^3 + (-3*z^11 - 27*z^10 - 49*z^9 + 25*z^8 + 67*z^7 + 13*z^6 - 15*z^5)*u^2 + (3*z^10 + 14*z^9 + 11*z^8 - 5*z^7 - 6*z^6)*u + (-z^9 - 2*z^8 - z^7) */
static const long X1_31_crv_0[12] = {
  evaltyp(t_VECSMALL) | _evallg(12), vZ, 0, 0, 0, 0, 0, 0, 0, -1, -2, -1 }; /* -z^9 - 2*z^8 - z^7 */
static const long X1_31_crv_1[13] = {
  evaltyp(t_VECSMALL) | _evallg(13), vZ, 0, 0, 0, 0, 0, 0, -6, -5, 11, 14, 3 }; /* 3*z^10 + 14*z^9 + 11*z^8 - 5*z^7 - 6*z^6 */
static const long X1_31_crv_2[14] = {
  evaltyp(t_VECSMALL) | _evallg(14), vZ, 0, 0, 0, 0, 0, -15, 13, 67, 25, -49, -27, -3 }; /* -3*z^11 - 27*z^10 - 49*z^9 + 25*z^8 + 67*z^7 + 13*z^6 - 15*z^5 */
static const long X1_31_crv_3[15] = {
  evaltyp(t_VECSMALL) | _evallg(15), vZ, 0, 0, 0, 0, -20, 68, 103, -119, -247, -1, 76, 20, 1 }; /* z^12 + 20*z^11 + 76*z^10 - z^9 - 247*z^8 - 119*z^7 + 103*z^6 + 68*z^5 - 20*z^4 */
static const long X1_31_crv_4[15] = {
  evaltyp(t_VECSMALL) | _evallg(15), vZ, 0, 0, 0, -15, 112, -17, -390, -266, 448, 293, -52, -47, -5 }; /* -5*z^12 - 47*z^11 - 52*z^10 + 293*z^9 + 448*z^8 - 266*z^7 - 390*z^6 - 17*z^5 + 112*z^4 - 15*z^3 */
static const long X1_31_crv_5[15] = {
  evaltyp(t_VECSMALL) | _evallg(15), vZ, 0, 0, -6, 91, -200, -351, 242, 1033, 19, -537, -115, 44, 10 }; /* 10*z^12 + 44*z^11 - 115*z^10 - 537*z^9 + 19*z^8 + 1033*z^7 + 242*z^6 - 351*z^5 - 200*z^4 + 91*z^3 - 6*z^2 */
static const long X1_31_crv_6[15] = {
  evaltyp(t_VECSMALL) | _evallg(15), vZ, 0, -1, 37, -216, 28, 598, 713, -967, -864, 268, 240, 0, -10 }; /* -10*z^12 + 240*z^10 + 268*z^9 - 864*z^8 - 967*z^7 + 713*z^6 + 598*z^5 + 28*z^4 - 216*z^3 + 37*z^2 - z */
static const long X1_31_crv_7[15] = {
  evaltyp(t_VECSMALL) | _evallg(15), vZ, 0, 6, -99, 222, 301, -78, -1254, -147, 911, 193, -162, -32, 5 }; /* 5*z^12 - 32*z^11 - 162*z^10 + 193*z^9 + 911*z^8 - 147*z^7 - 1254*z^6 - 78*z^5 + 301*z^4 + 222*z^3 - 99*z^2 + 6*z */
static const long X1_31_crv_8[15] = {
  evaltyp(t_VECSMALL) | _evallg(15), vZ, 0, -19, 131, -36, -266, -572, 569, 745, -260, -273, 27, 25, -1 }; /* -z^12 + 25*z^11 + 27*z^10 - 273*z^9 - 260*z^8 + 745*z^7 + 569*z^6 - 572*z^5 - 266*z^4 - 36*z^3 + 131*z^2 - 19*z */
static const long X1_31_crv_9[14] = {
  evaltyp(t_VECSMALL) | _evallg(14), vZ, -1, 31, -73, -91, -57, 453, 145, -387, -93, 105, 17, -8 }; /* -8*z^11 + 17*z^10 + 105*z^9 - 93*z^8 - 387*z^7 + 145*z^6 + 453*z^5 - 57*z^4 - 91*z^3 - 73*z^2 + 31*z - 1 */
static const long X1_31_crv_10[14] = {
  evaltyp(t_VECSMALL) | _evallg(14), vZ, 3, -24, 0, 37, 129, -70, -152, 45, 61, -11, -8, 1 }; /* z^11 - 8*z^10 - 11*z^9 + 61*z^8 + 45*z^7 - 152*z^6 - 70*z^5 + 129*z^4 + 37*z^3 - 24*z + 3 */
static const long X1_31_crv_11[13] = {
  evaltyp(t_VECSMALL) | _evallg(13), vZ, -3, 7, 10, 8, -26, -12, 23, 6, -8, -1, 1 }; /* z^10 - z^9 - 8*z^8 + 6*z^7 + 23*z^6 - 12*z^5 - 26*z^4 + 8*z^3 + 10*z^2 + 7*z - 3 */
static const long *X1_31_crv[15] = {
  (long *)(evaltyp(t_POL) | _evallg(15)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_31_crv_0, X1_31_crv_1, X1_31_crv_2, X1_31_crv_3, X1_31_crv_4, X1_31_crv_5, X1_31_crv_6, X1_31_crv_7, X1_31_crv_8, X1_31_crv_9, X1_31_crv_10, X1_31_crv_11, FLX_1
};
/* (-z^4 + 3*z^3 - 2*z^2 - z + 1)*u^7 + (-z^5 + 7*z^4 - 11*z^3 + 2*z^2 + 3*z)*u^6 + (5*z^5 - 18*z^4 + 12*z^3 + 3*z^2 - 1)*u^5 + (z^6 - 11*z^5 + 22*z^4 + z^3 - 6*z^2 - 4*z + 1)*u^4 + (-2*z^6 + 15*z^5 - 9*z^4 - 15*z^3 - 3*z^2 + 4*z)*u^3 + (3*z^6 - 11*z^5 - 10*z^4 + 4*z^3 + 6*z^2)*u^2 + (-3*z^6 + 6*z^4 + 4*z^3)*u + (z^6 + 2*z^5 + z^4) */
static const long X1_31_r_n_0[9] = {
  evaltyp(t_VECSMALL) | _evallg(9), vZ, 0, 0, 0, 0, 1, 2, 1 }; /* z^6 + 2*z^5 + z^4 */
static const long X1_31_r_n_1[9] = {
  evaltyp(t_VECSMALL) | _evallg(9), vZ, 0, 0, 0, 4, 6, 0, -3 }; /* -3*z^6 + 6*z^4 + 4*z^3 */
static const long X1_31_r_n_2[9] = {
  evaltyp(t_VECSMALL) | _evallg(9), vZ, 0, 0, 6, 4, -10, -11, 3 }; /* 3*z^6 - 11*z^5 - 10*z^4 + 4*z^3 + 6*z^2 */
static const long X1_31_r_n_3[9] = {
  evaltyp(t_VECSMALL) | _evallg(9), vZ, 0, 4, -3, -15, -9, 15, -2 }; /* -2*z^6 + 15*z^5 - 9*z^4 - 15*z^3 - 3*z^2 + 4*z */
static const long X1_31_r_n_4[9] = {
  evaltyp(t_VECSMALL) | _evallg(9), vZ, 1, -4, -6, 1, 22, -11, 1 }; /* z^6 - 11*z^5 + 22*z^4 + z^3 - 6*z^2 - 4*z + 1 */
static const long X1_31_r_n_5[8] = {
  evaltyp(t_VECSMALL) | _evallg(8), vZ, -1, 0, 3, 12, -18, 5 }; /* 5*z^5 - 18*z^4 + 12*z^3 + 3*z^2 - 1 */
static const long X1_31_r_n_6[8] = {
  evaltyp(t_VECSMALL) | _evallg(8), vZ, 0, 3, 2, -11, 7, -1 }; /* -z^5 + 7*z^4 - 11*z^3 + 2*z^2 + 3*z */
static const long X1_31_r_n_7[7] = {
  evaltyp(t_VECSMALL) | _evallg(7), vZ, 1, -1, -2, 3, -1 }; /* -z^4 + 3*z^3 - 2*z^2 - z + 1 */
static const long *X1_31_r_n[10] = {
  (long *)(evaltyp(t_POL) | _evallg(10)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_31_r_n_0, X1_31_r_n_1, X1_31_r_n_2, X1_31_r_n_3, X1_31_r_n_4, X1_31_r_n_5, X1_31_r_n_6, X1_31_r_n_7
};
/* (-z + 1)*u^6 + (-4*z^2 + 5*z - 1)*u^5 + (-z^6 - z^5 + 5*z^4 - z^3 + 6*z^2 - 7*z + 1)*u^4 + (3*z^6 + 10*z^5 - 6*z^4 - 8*z^3 - 10*z^2 + 5*z)*u^3 + (-z^6 - 14*z^5 - 10*z^4 + z^3 + 8*z^2)*u^2 + (-2*z^6 + 2*z^5 + 7*z^4 + 5*z^3)*u + (z^6 + 2*z^5 + z^4) */
static const long X1_31_r_d_0[9] = {
  evaltyp(t_VECSMALL) | _evallg(9), vZ, 0, 0, 0, 0, 1, 2, 1 }; /* z^6 + 2*z^5 + z^4 */
static const long X1_31_r_d_1[9] = {
  evaltyp(t_VECSMALL) | _evallg(9), vZ, 0, 0, 0, 5, 7, 2, -2 }; /* -2*z^6 + 2*z^5 + 7*z^4 + 5*z^3 */
static const long X1_31_r_d_2[9] = {
  evaltyp(t_VECSMALL) | _evallg(9), vZ, 0, 0, 8, 1, -10, -14, -1 }; /* -z^6 - 14*z^5 - 10*z^4 + z^3 + 8*z^2 */
static const long X1_31_r_d_3[9] = {
  evaltyp(t_VECSMALL) | _evallg(9), vZ, 0, 5, -10, -8, -6, 10, 3 }; /* 3*z^6 + 10*z^5 - 6*z^4 - 8*z^3 - 10*z^2 + 5*z */
static const long X1_31_r_d_4[9] = {
  evaltyp(t_VECSMALL) | _evallg(9), vZ, 1, -7, 6, -1, 5, -1, -1 }; /* -z^6 - z^5 + 5*z^4 - z^3 + 6*z^2 - 7*z + 1 */
static const long X1_31_r_d_5[5] = {
  evaltyp(t_VECSMALL) | _evallg(5), vZ, -1, 5, -4 }; /* -4*z^2 + 5*z - 1 */
static const long X1_31_r_d_6[4] = {
  evaltyp(t_VECSMALL) | _evallg(4), vZ, 1, -1 }; /* -z + 1 */
static const long *X1_31_r_d[9] = {
  (long *)(evaltyp(t_POL) | _evallg(9)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_31_r_d_0, X1_31_r_d_1, X1_31_r_d_2, X1_31_r_d_3, X1_31_r_d_4, X1_31_r_d_5, X1_31_r_d_6
};
/* (-z^3 + 3*z^2 - z - 2)*u^6 + (-z^4 + 7*z^3 - 8*z^2 - 3*z + 1)*u^5 + (5*z^4 - 15*z^3 + 2*z^2 + 5*z + 1)*u^4 + (z^5 - 11*z^4 + 9*z^3 + 9*z^2 - z - 1)*u^3 + (-3*z^5 + 8*z^4 + 6*z^3 - 4*z^2 - 2*z)*u^2 + (3*z^5 + z^4 - 4*z^3 - 2*z^2)*u + (-z^5 - 2*z^4 - z^3) */
static const long X1_31_s_n_0[8] = {
  evaltyp(t_VECSMALL) | _evallg(8), vZ, 0, 0, 0, -1, -2, -1 }; /* -z^5 - 2*z^4 - z^3 */
static const long X1_31_s_n_1[8] = {
  evaltyp(t_VECSMALL) | _evallg(8), vZ, 0, 0, -2, -4, 1, 3 }; /* 3*z^5 + z^4 - 4*z^3 - 2*z^2 */
static const long X1_31_s_n_2[8] = {
  evaltyp(t_VECSMALL) | _evallg(8), vZ, 0, -2, -4, 6, 8, -3 }; /* -3*z^5 + 8*z^4 + 6*z^3 - 4*z^2 - 2*z */
static const long X1_31_s_n_3[8] = {
  evaltyp(t_VECSMALL) | _evallg(8), vZ, -1, -1, 9, 9, -11, 1 }; /* z^5 - 11*z^4 + 9*z^3 + 9*z^2 - z - 1 */
static const long X1_31_s_n_4[7] = {
  evaltyp(t_VECSMALL) | _evallg(7), vZ, 1, 5, 2, -15, 5 }; /* 5*z^4 - 15*z^3 + 2*z^2 + 5*z + 1 */
static const long X1_31_s_n_5[7] = {
  evaltyp(t_VECSMALL) | _evallg(7), vZ, 1, -3, -8, 7, -1 }; /* -z^4 + 7*z^3 - 8*z^2 - 3*z + 1 */
static const long X1_31_s_n_6[6] = {
  evaltyp(t_VECSMALL) | _evallg(6), vZ, -2, -1, 3, -1 }; /* -z^3 + 3*z^2 - z - 2 */
static const long *X1_31_s_n[9] = {
  (long *)(evaltyp(t_POL) | _evallg(9)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_31_s_n_0, X1_31_s_n_1, X1_31_s_n_2, X1_31_s_n_3, X1_31_s_n_4, X1_31_s_n_5, X1_31_s_n_6
};
/* (z^2 - z - 1)*u^6 + (2*z^3 - 4*z^2 - z)*u^5 + (z^4 - 6*z^3 + 3*z^2 + z + 1)*u^4 + (-z^5 - 7*z^4 + 5*z^3 + 4*z^2 + 2*z - 1)*u^3 + (10*z^4 + 7*z^3 - z^2 - 3*z)*u^2 + (2*z^5 - z^4 - 5*z^3 - 3*z^2)*u + (-z^5 - 2*z^4 - z^3) */
static const long X1_31_s_d_0[8] = {
  evaltyp(t_VECSMALL) | _evallg(8), vZ, 0, 0, 0, -1, -2, -1 }; /* -z^5 - 2*z^4 - z^3 */
static const long X1_31_s_d_1[8] = {
  evaltyp(t_VECSMALL) | _evallg(8), vZ, 0, 0, -3, -5, -1, 2 }; /* 2*z^5 - z^4 - 5*z^3 - 3*z^2 */
static const long X1_31_s_d_2[7] = {
  evaltyp(t_VECSMALL) | _evallg(7), vZ, 0, -3, -1, 7, 10 }; /* 10*z^4 + 7*z^3 - z^2 - 3*z */
static const long X1_31_s_d_3[8] = {
  evaltyp(t_VECSMALL) | _evallg(8), vZ, -1, 2, 4, 5, -7, -1 }; /* -z^5 - 7*z^4 + 5*z^3 + 4*z^2 + 2*z - 1 */
static const long X1_31_s_d_4[7] = {
  evaltyp(t_VECSMALL) | _evallg(7), vZ, 1, 1, 3, -6, 1 }; /* z^4 - 6*z^3 + 3*z^2 + z + 1 */
static const long X1_31_s_d_5[6] = {
  evaltyp(t_VECSMALL) | _evallg(6), vZ, 0, -1, -4, 2 }; /* 2*z^3 - 4*z^2 - z */
static const long X1_31_s_d_6[5] = {
  evaltyp(t_VECSMALL) | _evallg(5), vZ, -1, -1, 1 }; /* z^2 - z - 1 */
static const long *X1_31_s_d[9] = {
  (long *)(evaltyp(t_POL) | _evallg(9)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_31_s_d_0, X1_31_s_d_1, X1_31_s_d_2, X1_31_s_d_3, X1_31_s_d_4, X1_31_s_d_5, X1_31_s_d_6
};
/* (z^8 - 4*z^7 + 6*z^6 - 4*z^5 + z^4)*x^8 + (16*z^8 - 48*z^7 + 48*z^6 - 16*z^5)*x^7 + (z^11 - 2*z^10 + z^9 + 104*z^8 - 208*z^7 + 96*z^6 + 16*z^5 - 8*z^4 - z^3 + 2*z^2 - z)*x^6 + (12*z^11 - 12*z^10 + 352*z^8 - 352*z^7 - 96*z^6 + 96*z^5 - 12*z^3 + 12*z^2)*x^5 + (54*z^11 - 6*z^9 + 664*z^8 - 432*z^6 + 24*z^4 - 54*z^3 + 6*z)*x^4 + (112*z^11 + 112*z^10 + 64*z^9 + 768*z^8 + 768*z^7 - 128*z^6 - 128*z^5 + 64*z^4 - 48*z^3 - 48*z^2)*x^3 + (106*z^11 + 212*z^10 + 198*z^9 + 600*z^8 + 1020*z^7 + 576*z^6 + 132*z^5 + 168*z^4 + 90*z^3 - 20*z^2 - 10*z)*x^2 + (40*z^11 + 120*z^10 + 144*z^9 + 240*z^8 + 480*z^7 + 480*z^6 + 240*z^5 + 144*z^4 + 120*z^3 + 40*z^2)*x + (-z^12 + 6*z^10 - 15*z^8 + 20*z^6 - 15*z^4 + 6*z^2 - 1) */
static const long X1_32_crv_0[15] = {
  evaltyp(t_VECSMALL) | _evallg(15), vZ, -1, 0, 6, 0, -15, 0, 20, 0, -15, 0, 6, 0, -1 }; /* -z^12 + 6*z^10 - 15*z^8 + 20*z^6 - 15*z^4 + 6*z^2 - 1 */
static const long X1_32_crv_1[14] = {
  evaltyp(t_VECSMALL) | _evallg(14), vZ, 0, 0, 40, 120, 144, 240, 480, 480, 240, 144, 120, 40 }; /* 40*z^11 + 120*z^10 + 144*z^9 + 240*z^8 + 480*z^7 + 480*z^6 + 240*z^5 + 144*z^4 + 120*z^3 + 40*z^2 */
static const long X1_32_crv_2[14] = {
  evaltyp(t_VECSMALL) | _evallg(14), vZ, 0, -10, -20, 90, 168, 132, 576, 1020, 600, 198, 212, 106 }; /* 106*z^11 + 212*z^10 + 198*z^9 + 600*z^8 + 1020*z^7 + 576*z^6 + 132*z^5 + 168*z^4 + 90*z^3 - 20*z^2 - 10*z */
static const long X1_32_crv_3[14] = {
  evaltyp(t_VECSMALL) | _evallg(14), vZ, 0, 0, -48, -48, 64, -128, -128, 768, 768, 64, 112, 112 }; /* 112*z^11 + 112*z^10 + 64*z^9 + 768*z^8 + 768*z^7 - 128*z^6 - 128*z^5 + 64*z^4 - 48*z^3 - 48*z^2 */
static const long X1_32_crv_4[14] = {
  evaltyp(t_VECSMALL) | _evallg(14), vZ, 0, 6, 0, -54, 24, 0, -432, 0, 664, -6, 0, 54 }; /* 54*z^11 - 6*z^9 + 664*z^8 - 432*z^6 + 24*z^4 - 54*z^3 + 6*z */
static const long X1_32_crv_5[14] = {
  evaltyp(t_VECSMALL) | _evallg(14), vZ, 0, 0, 12, -12, 0, 96, -96, -352, 352, 0, -12, 12 }; /* 12*z^11 - 12*z^10 + 352*z^8 - 352*z^7 - 96*z^6 + 96*z^5 - 12*z^3 + 12*z^2 */
static const long X1_32_crv_6[14] = {
  evaltyp(t_VECSMALL) | _evallg(14), vZ, 0, -1, 2, -1, -8, 16, 96, -208, 104, 1, -2, 1 }; /* z^11 - 2*z^10 + z^9 + 104*z^8 - 208*z^7 + 96*z^6 + 16*z^5 - 8*z^4 - z^3 + 2*z^2 - z */
static const long X1_32_crv_7[11] = {
  evaltyp(t_VECSMALL) | _evallg(11), vZ, 0, 0, 0, 0, 0, -16, 48, -48, 16 }; /* 16*z^8 - 48*z^7 + 48*z^6 - 16*z^5 */
static const long X1_32_crv_8[11] = {
  evaltyp(t_VECSMALL) | _evallg(11), vZ, 0, 0, 0, 0, 1, -4, 6, -4, 1 }; /* z^8 - 4*z^7 + 6*z^6 - 4*z^5 + z^4 */
static const long *X1_32_crv[11] = {
  (long *)(evaltyp(t_POL) | _evallg(11)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_32_crv_0, X1_32_crv_1, X1_32_crv_2, X1_32_crv_3, X1_32_crv_4, X1_32_crv_5, X1_32_crv_6, X1_32_crv_7, X1_32_crv_8
};
/* (z - 1)*x + 2*z */
static const long X1_32_r_n_0[4] = {
  evaltyp(t_VECSMALL) | _evallg(4), vZ, 0, 2 }; /* 2*z */
static const long X1_32_r_n_1[4] = {
  evaltyp(t_VECSMALL) | _evallg(4), vZ, -1, 1 }; /* z - 1 */
static const long *X1_32_r_n[4] = {
  (long *)(evaltyp(t_POL) | _evallg(4)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_32_r_n_0, X1_32_r_n_1
};
/* 2 */
static const long X1_32_r_d_0[3] = {
  evaltyp(t_VECSMALL) | _evallg(3), vZ, 2 }; /* 2 */
static const long *X1_32_r_d[3] = {
  (long *)(evaltyp(t_POL) | _evallg(3)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_32_r_d_0
};
/* (-z + 1)*x - 2*z */
static const long X1_32_s_n_0[4] = {
  evaltyp(t_VECSMALL) | _evallg(4), vZ, 0, -2 }; /* -2*z */
static const long X1_32_s_n_1[4] = {
  evaltyp(t_VECSMALL) | _evallg(4), vZ, 1, -1 }; /* -z + 1 */
static const long *X1_32_s_n[4] = {
  (long *)(evaltyp(t_POL) | _evallg(4)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_32_s_n_0, X1_32_s_n_1
};
/* 2*z */
static const long X1_32_s_d_0[4] = {
  evaltyp(t_VECSMALL) | _evallg(4), vZ, 0, 2 }; /* 2*z */
static const long *X1_32_s_d[3] = {
  (long *)(evaltyp(t_POL) | _evallg(3)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_32_s_d_0
};
/* z^8*x^10 + (-z^17 - 2*z^16 - 4*z^15 - 6*z^14 - 9*z^13 - 12*z^12 - 16*z^11 - 20*z^10 - 25*z^9 - 18*z^8)*x^9 + (-3*z^17 - 15*z^16 - 24*z^15 - 28*z^14 - 16*z^13 + 6*z^12 + 32*z^11 + 32*z^10 - 33*z^9 - 155*z^8 - 188*z^7 - 108*z^6 - 58*z^5 - 28*z^4 - 12*z^3 - 4*z^2 - z)*x^8 + (-6*z^17 - 48*z^16 - 144*z^15 - 226*z^14 - 225*z^13 - 39*z^12 + 402*z^11 + 1116*z^10 + 1854*z^9 + 2071*z^8 + 1536*z^7 + 852*z^6 + 476*z^5 + 249*z^4 + 114*z^3 + 40*z^2 + 9*z)*x^7 + (-10*z^17 - 110*z^16 - 520*z^15 - 1464*z^14 - 3006*z^13 - 5160*z^12 - 7660*z^11 - 9656*z^10 - 9778*z^9 - 7536*z^8 - 4500*z^7 - 2580*z^6 - 1696*z^5 - 1028*z^4 - 508*z^3 - 180*z^2 - 36*z)*x^6 + (z^20 + 10*z^19 + 60*z^18 + 255*z^17 + 795*z^16 + 1872*z^15 + 3576*z^14 + 6042*z^13 + 9198*z^12 + 11872*z^11 + 12028*z^10 + 8886*z^9 + 4847*z^8 + 3188*z^7 + 3762*z^6 + 3917*z^5 + 2801*z^4 + 1422*z^3 + 480*z^2 + 84*z)*x^5 + (10*z^17 + 60*z^16 + 120*z^15 - 64*z^14 - 690*z^13 - 1026*z^12 + 392*z^11 + 3456*z^10 + 4980*z^9 + 1576*z^8 - 5292*z^7 - 10032*z^6 - 9630*z^5 - 6174*z^4 - 2808*z^3 - 840*z^2 - 126*z)*x^4 + (6*z^17 + 54*z^16 + 192*z^15 + 254*z^14 - 419*z^13 - 2392*z^12 - 4432*z^11 - 3020*z^10 + 4499*z^9 + 15607*z^8 + 23336*z^7 + 22966*z^6 + 16391*z^5 + 8779*z^4 + 3458*z^3 + 896*z^2 + 112*z - 1)*x^3 + (3*z^17 + 36*z^16 + 192*z^15 + 572*z^14 + 884*z^13 - 150*z^12 - 4536*z^11 - 13080*z^10 - 23253*z^9 - 29900*z^8 - 29288*z^7 - 22380*z^6 - 13480*z^5 - 6328*z^4 - 2184*z^3 - 476*z^2 - 41*z + 3)*x^2 + (z^17 + 15*z^16 + 108*z^15 + 494*z^14 + 1605*z^13 + 3927*z^12 + 7490*z^11 + 11376*z^10 + 13938*z^9 + 13882*z^8 + 11292*z^7 + 7506*z^6 + 4025*z^5 + 1659*z^4 + 462*z^3 + 56*z^2 - 9*z - 3)*x + (z^8 + 8*z^7 + 28*z^6 + 56*z^5 + 70*z^4 + 56*z^3 + 28*z^2 + 8*z + 1) */
static const long X1_33_crv_0[11] = {
  evaltyp(t_VECSMALL) | _evallg(11), vZ, 1, 8, 28, 56, 70, 56, 28, 8, 1 }; /* z^8 + 8*z^7 + 28*z^6 + 56*z^5 + 70*z^4 + 56*z^3 + 28*z^2 + 8*z + 1 */
static const long X1_33_crv_1[20] = {
  evaltyp(t_VECSMALL) | _evallg(20), vZ, -3, -9, 56, 462, 1659, 4025, 7506, 11292, 13882, 13938, 11376, 7490, 3927, 1605, 494, 108, 15, 1 }; /* z^17 + 15*z^16 + 108*z^15 + 494*z^14 + 1605*z^13 + 3927*z^12 + 7490*z^11 + 11376*z^10 + 13938*z^9 + 13882*z^8 + 11292*z^7 + 7506*z^6 + 4025*z^5 + 1659*z^4 + 462*z^3 + 56*z^2 - 9*z - 3 */
static const long X1_33_crv_2[20] = {
  evaltyp(t_VECSMALL) | _evallg(20), vZ, 3, -41, -476, -2184, -6328, -13480, -22380, -29288, -29900, -23253, -13080, -4536, -150, 884, 572, 192, 36, 3 }; /* 3*z^17 + 36*z^16 + 192*z^15 + 572*z^14 + 884*z^13 - 150*z^12 - 4536*z^11 - 13080*z^10 - 23253*z^9 - 29900*z^8 - 29288*z^7 - 22380*z^6 - 13480*z^5 - 6328*z^4 - 2184*z^3 - 476*z^2 - 41*z + 3 */
static const long X1_33_crv_3[20] = {
  evaltyp(t_VECSMALL) | _evallg(20), vZ, -1, 112, 896, 3458, 8779, 16391, 22966, 23336, 15607, 4499, -3020, -4432, -2392, -419, 254, 192, 54, 6 }; /* 6*z^17 + 54*z^16 + 192*z^15 + 254*z^14 - 419*z^13 - 2392*z^12 - 4432*z^11 - 3020*z^10 + 4499*z^9 + 15607*z^8 + 23336*z^7 + 22966*z^6 + 16391*z^5 + 8779*z^4 + 3458*z^3 + 896*z^2 + 112*z - 1 */
static const long X1_33_crv_4[20] = {
  evaltyp(t_VECSMALL) | _evallg(20), vZ, 0, -126, -840, -2808, -6174, -9630, -10032, -5292, 1576, 4980, 3456, 392, -1026, -690, -64, 120, 60, 10 }; /* 10*z^17 + 60*z^16 + 120*z^15 - 64*z^14 - 690*z^13 - 1026*z^12 + 392*z^11 + 3456*z^10 + 4980*z^9 + 1576*z^8 - 5292*z^7 - 10032*z^6 - 9630*z^5 - 6174*z^4 - 2808*z^3 - 840*z^2 - 126*z */
static const long X1_33_crv_5[23] = {
  evaltyp(t_VECSMALL) | _evallg(23), vZ, 0, 84, 480, 1422, 2801, 3917, 3762, 3188, 4847, 8886, 12028, 11872, 9198, 6042, 3576, 1872, 795, 255, 60, 10, 1 }; /* z^20 + 10*z^19 + 60*z^18 + 255*z^17 + 795*z^16 + 1872*z^15 + 3576*z^14 + 6042*z^13 + 9198*z^12 + 11872*z^11 + 12028*z^10 + 8886*z^9 + 4847*z^8 + 3188*z^7 + 3762*z^6 + 3917*z^5 + 2801*z^4 + 1422*z^3 + 480*z^2 + 84*z */
static const long X1_33_crv_6[20] = {
  evaltyp(t_VECSMALL) | _evallg(20), vZ, 0, -36, -180, -508, -1028, -1696, -2580, -4500, -7536, -9778, -9656, -7660, -5160, -3006, -1464, -520, -110, -10 }; /* -10*z^17 - 110*z^16 - 520*z^15 - 1464*z^14 - 3006*z^13 - 5160*z^12 - 7660*z^11 - 9656*z^10 - 9778*z^9 - 7536*z^8 - 4500*z^7 - 2580*z^6 - 1696*z^5 - 1028*z^4 - 508*z^3 - 180*z^2 - 36*z */
static const long X1_33_crv_7[20] = {
  evaltyp(t_VECSMALL) | _evallg(20), vZ, 0, 9, 40, 114, 249, 476, 852, 1536, 2071, 1854, 1116, 402, -39, -225, -226, -144, -48, -6 }; /* -6*z^17 - 48*z^16 - 144*z^15 - 226*z^14 - 225*z^13 - 39*z^12 + 402*z^11 + 1116*z^10 + 1854*z^9 + 2071*z^8 + 1536*z^7 + 852*z^6 + 476*z^5 + 249*z^4 + 114*z^3 + 40*z^2 + 9*z */
static const long X1_33_crv_8[20] = {
  evaltyp(t_VECSMALL) | _evallg(20), vZ, 0, -1, -4, -12, -28, -58, -108, -188, -155, -33, 32, 32, 6, -16, -28, -24, -15, -3 }; /* -3*z^17 - 15*z^16 - 24*z^15 - 28*z^14 - 16*z^13 + 6*z^12 + 32*z^11 + 32*z^10 - 33*z^9 - 155*z^8 - 188*z^7 - 108*z^6 - 58*z^5 - 28*z^4 - 12*z^3 - 4*z^2 - z */
static const long X1_33_crv_9[20] = {
  evaltyp(t_VECSMALL) | _evallg(20), vZ, 0, 0, 0, 0, 0, 0, 0, 0, -18, -25, -20, -16, -12, -9, -6, -4, -2, -1 }; /* -z^17 - 2*z^16 - 4*z^15 - 6*z^14 - 9*z^13 - 12*z^12 - 16*z^11 - 20*z^10 - 25*z^9 - 18*z^8 */
static const long X1_33_crv_10[11] = {
  evaltyp(t_VECSMALL) | _evallg(11), vZ, 0, 0, 0, 0, 0, 0, 0, 0, 1 }; /* z^8 */
static const long *X1_33_crv[13] = {
  (long *)(evaltyp(t_POL) | _evallg(13)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_33_crv_0, X1_33_crv_1, X1_33_crv_2, X1_33_crv_3, X1_33_crv_4, X1_33_crv_5, X1_33_crv_6, X1_33_crv_7, X1_33_crv_8, X1_33_crv_9, X1_33_crv_10
};
/* (z + 1) */
static const long X1_33_r_n_0[4] = {
  evaltyp(t_VECSMALL) | _evallg(4), vZ, 1, 1 }; /* z + 1 */
static const long *X1_33_r_n[3] = {
  (long *)(evaltyp(t_POL) | _evallg(3)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_33_r_n_0
};
/* z */
static const long *X1_33_r_d[3] = {
  (long *)(evaltyp(t_POL) | _evallg(3)), (long *)(evalvarn(0) | evalsigne(1)),
  FLX_Z
};
/* 1 */
static const long *X1_33_s_n[3] = {
  (long *)(evaltyp(t_POL) | _evallg(3)), (long *)(evalvarn(0) | evalsigne(1)),
  FLX_1
};
/* (-z - 1)*x + (z + 1) */
static const long X1_33_s_d_0[4] = {
  evaltyp(t_VECSMALL) | _evallg(4), vZ, 1, 1 }; /* z + 1 */
static const long X1_33_s_d_1[4] = {
  evaltyp(t_VECSMALL) | _evallg(4), vZ, -1, -1 }; /* -z - 1 */
static const long *X1_33_s_d[4] = {
  (long *)(evaltyp(t_POL) | _evallg(4)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_33_s_d_0, X1_33_s_d_1
};
/* u^10 + (z^5 - z^2 - 4*z + 4)*u^9 + (8*z^5 - z^4 - 5*z^3 + z^2 - 12*z + 6)*u^8 + (5*z^7 - 2*z^6 + 16*z^5 - z^4 - 20*z^3 + 9*z^2 - 11*z + 4)*u^7 + (-z^8 + 24*z^7 + 2*z^6 + 7*z^5 - 36*z^3 + 8*z^2 + 1)*u^6 + (z^10 + z^9 - 7*z^8 + 40*z^7 + 26*z^6 + 2*z^5 + 8*z^4 - 29*z^3 - 3*z^2 + 5*z)*u^5 + (2*z^10 + 4*z^9 - 5*z^8 + 35*z^7 + 37*z^6 + 5*z^5 + 12*z^4 - 6*z^3 - 5*z^2 + 2*z)*u^4 + (z^10 + 4*z^9 + 7*z^8 + 28*z^7 + 29*z^6 + 7*z^5 + 5*z^4 + 3*z^3)*u^3 + (2*z^9 + 10*z^8 + 16*z^7 + 10*z^6 + 2*z^5 - z^4 + z^2)*u^2 + (z^9 + 5*z^8 + 5*z^7 - z^5 - z^4 - z^3)*u + (-z^7 - 2*z^6 - z^5) */
static const long X1_34_crv_0[10] = {
  evaltyp(t_VECSMALL) | _evallg(10), vZ, 0, 0, 0, 0, 0, -1, -2, -1 }; /* -z^7 - 2*z^6 - z^5 */
static const long X1_34_crv_1[12] = {
  evaltyp(t_VECSMALL) | _evallg(12), vZ, 0, 0, 0, -1, -1, -1, 0, 5, 5, 1 }; /* z^9 + 5*z^8 + 5*z^7 - z^5 - z^4 - z^3 */
static const long X1_34_crv_2[12] = {
  evaltyp(t_VECSMALL) | _evallg(12), vZ, 0, 0, 1, 0, -1, 2, 10, 16, 10, 2 }; /* 2*z^9 + 10*z^8 + 16*z^7 + 10*z^6 + 2*z^5 - z^4 + z^2 */
static const long X1_34_crv_3[13] = {
  evaltyp(t_VECSMALL) | _evallg(13), vZ, 0, 0, 0, 3, 5, 7, 29, 28, 7, 4, 1 }; /* z^10 + 4*z^9 + 7*z^8 + 28*z^7 + 29*z^6 + 7*z^5 + 5*z^4 + 3*z^3 */
static const long X1_34_crv_4[13] = {
  evaltyp(t_VECSMALL) | _evallg(13), vZ, 0, 2, -5, -6, 12, 5, 37, 35, -5, 4, 2 }; /* 2*z^10 + 4*z^9 - 5*z^8 + 35*z^7 + 37*z^6 + 5*z^5 + 12*z^4 - 6*z^3 - 5*z^2 + 2*z */
static const long X1_34_crv_5[13] = {
  evaltyp(t_VECSMALL) | _evallg(13), vZ, 0, 5, -3, -29, 8, 2, 26, 40, -7, 1, 1 }; /* z^10 + z^9 - 7*z^8 + 40*z^7 + 26*z^6 + 2*z^5 + 8*z^4 - 29*z^3 - 3*z^2 + 5*z */
static const long X1_34_crv_6[11] = {
  evaltyp(t_VECSMALL) | _evallg(11), vZ, 1, 0, 8, -36, 0, 7, 2, 24, -1 }; /* -z^8 + 24*z^7 + 2*z^6 + 7*z^5 - 36*z^3 + 8*z^2 + 1 */
static const long X1_34_crv_7[10] = {
  evaltyp(t_VECSMALL) | _evallg(10), vZ, 4, -11, 9, -20, -1, 16, -2, 5 }; /* 5*z^7 - 2*z^6 + 16*z^5 - z^4 - 20*z^3 + 9*z^2 - 11*z + 4 */
static const long X1_34_crv_8[8] = {
  evaltyp(t_VECSMALL) | _evallg(8), vZ, 6, -12, 1, -5, -1, 8 }; /* 8*z^5 - z^4 - 5*z^3 + z^2 - 12*z + 6 */
static const long X1_34_crv_9[8] = {
  evaltyp(t_VECSMALL) | _evallg(8), vZ, 4, -4, -1, 0, 0, 1 }; /* z^5 - z^2 - 4*z + 4 */
static const long *X1_34_crv[13] = {
  (long *)(evaltyp(t_POL) | _evallg(13)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_34_crv_0, X1_34_crv_1, X1_34_crv_2, X1_34_crv_3, X1_34_crv_4, X1_34_crv_5, X1_34_crv_6, X1_34_crv_7, X1_34_crv_8, X1_34_crv_9, FLX_1
};
/* u^8 + (-z^2 - 3*z + 3)*u^7 + (-z^3 + 3*z^2 - 5*z + 3)*u^6 + (-3*z^4 - 11*z^3 + 7*z^2 - 2*z + 1)*u^5 + (2*z^5 + 2*z^4 - 15*z^3 + z^2 - z)*u^4 + (-2*z^6 + 5*z^4 - 7*z^3 - 3*z^2 - 2*z)*u^3 + (z^7 + 2*z^4 - z)*u^2 + (z^5 + z^4 + z^3 + z^2)*u + (z^6 + 2*z^5 + z^4) */
static const long X1_34_r_n_0[9] = {
  evaltyp(t_VECSMALL) | _evallg(9), vZ, 0, 0, 0, 0, 1, 2, 1 }; /* z^6 + 2*z^5 + z^4 */
static const long X1_34_r_n_1[8] = {
  evaltyp(t_VECSMALL) | _evallg(8), vZ, 0, 0, 1, 1, 1, 1 }; /* z^5 + z^4 + z^3 + z^2 */
static const long X1_34_r_n_2[10] = {
  evaltyp(t_VECSMALL) | _evallg(10), vZ, 0, -1, 0, 0, 2, 0, 0, 1 }; /* z^7 + 2*z^4 - z */
static const long X1_34_r_n_3[9] = {
  evaltyp(t_VECSMALL) | _evallg(9), vZ, 0, -2, -3, -7, 5, 0, -2 }; /* -2*z^6 + 5*z^4 - 7*z^3 - 3*z^2 - 2*z */
static const long X1_34_r_n_4[8] = {
  evaltyp(t_VECSMALL) | _evallg(8), vZ, 0, -1, 1, -15, 2, 2 }; /* 2*z^5 + 2*z^4 - 15*z^3 + z^2 - z */
static const long X1_34_r_n_5[7] = {
  evaltyp(t_VECSMALL) | _evallg(7), vZ, 1, -2, 7, -11, -3 }; /* -3*z^4 - 11*z^3 + 7*z^2 - 2*z + 1 */
static const long X1_34_r_n_6[6] = {
  evaltyp(t_VECSMALL) | _evallg(6), vZ, 3, -5, 3, -1 }; /* -z^3 + 3*z^2 - 5*z + 3 */
static const long X1_34_r_n_7[5] = {
  evaltyp(t_VECSMALL) | _evallg(5), vZ, 3, -3, -1 }; /* -z^2 - 3*z + 3 */
static const long *X1_34_r_n[11] = {
  (long *)(evaltyp(t_POL) | _evallg(11)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_34_r_n_0, X1_34_r_n_1, X1_34_r_n_2, X1_34_r_n_3, X1_34_r_n_4, X1_34_r_n_5, X1_34_r_n_6, X1_34_r_n_7, FLX_1
};
/* (-z^3 + 1)*u^6 + (-z^4 - 4*z^3 + 2*z^2 + 3)*u^5 + (-2*z^5 - 2*z^4 - 4*z^3 + 2*z^2 - 3*z + 3)*u^4 + (-z^6 - 2*z^5 - 2*z^4 - 5*z^3 - 3*z^2 - 6*z + 1)*u^3 + (z^7 - z^5 - 2*z^4 - 2*z^3 - z^2 - 3*z)*u^2 + (2*z^5 + 3*z^4 + 3*z^3 + 2*z^2)*u + (z^6 + 2*z^5 + z^4) */
static const long X1_34_r_d_0[9] = {
  evaltyp(t_VECSMALL) | _evallg(9), vZ, 0, 0, 0, 0, 1, 2, 1 }; /* z^6 + 2*z^5 + z^4 */
static const long X1_34_r_d_1[8] = {
  evaltyp(t_VECSMALL) | _evallg(8), vZ, 0, 0, 2, 3, 3, 2 }; /* 2*z^5 + 3*z^4 + 3*z^3 + 2*z^2 */
static const long X1_34_r_d_2[10] = {
  evaltyp(t_VECSMALL) | _evallg(10), vZ, 0, -3, -1, -2, -2, -1, 0, 1 }; /* z^7 - z^5 - 2*z^4 - 2*z^3 - z^2 - 3*z */
static const long X1_34_r_d_3[9] = {
  evaltyp(t_VECSMALL) | _evallg(9), vZ, 1, -6, -3, -5, -2, -2, -1 }; /* -z^6 - 2*z^5 - 2*z^4 - 5*z^3 - 3*z^2 - 6*z + 1 */
static const long X1_34_r_d_4[8] = {
  evaltyp(t_VECSMALL) | _evallg(8), vZ, 3, -3, 2, -4, -2, -2 }; /* -2*z^5 - 2*z^4 - 4*z^3 + 2*z^2 - 3*z + 3 */
static const long X1_34_r_d_5[7] = {
  evaltyp(t_VECSMALL) | _evallg(7), vZ, 3, 0, 2, -4, -1 }; /* -z^4 - 4*z^3 + 2*z^2 + 3 */
static const long X1_34_r_d_6[6] = {
  evaltyp(t_VECSMALL) | _evallg(6), vZ, 1, 0, 0, -1 }; /* -z^3 + 1 */
static const long *X1_34_r_d[9] = {
  (long *)(evaltyp(t_POL) | _evallg(9)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_34_r_d_0, X1_34_r_d_1, X1_34_r_d_2, X1_34_r_d_3, X1_34_r_d_4, X1_34_r_d_5, X1_34_r_d_6
};
/* -u^7 + (z^2 + 3*z - 3)*u^6 + (z^3 - 2*z^2 + 5*z - 3)*u^5 + (3*z^4 + 10*z^3 - 4*z^2 + z - 1)*u^4 + (-2*z^5 + 2*z^4 + 14*z^3 - 2*z)*u^3 + (z^6 + z^4 + 6*z^3 + z^2 - z)*u^2 + (z^4 + z^3)*u + (z^5 + 2*z^4 + z^3) */
static const long X1_34_s_n_0[8] = {
  evaltyp(t_VECSMALL) | _evallg(8), vZ, 0, 0, 0, 1, 2, 1 }; /* z^5 + 2*z^4 + z^3 */
static const long X1_34_s_n_1[7] = {
  evaltyp(t_VECSMALL) | _evallg(7), vZ, 0, 0, 0, 1, 1 }; /* z^4 + z^3 */
static const long X1_34_s_n_2[9] = {
  evaltyp(t_VECSMALL) | _evallg(9), vZ, 0, -1, 1, 6, 1, 0, 1 }; /* z^6 + z^4 + 6*z^3 + z^2 - z */
static const long X1_34_s_n_3[8] = {
  evaltyp(t_VECSMALL) | _evallg(8), vZ, 0, -2, 0, 14, 2, -2 }; /* -2*z^5 + 2*z^4 + 14*z^3 - 2*z */
static const long X1_34_s_n_4[7] = {
  evaltyp(t_VECSMALL) | _evallg(7), vZ, -1, 1, -4, 10, 3 }; /* 3*z^4 + 10*z^3 - 4*z^2 + z - 1 */
static const long X1_34_s_n_5[6] = {
  evaltyp(t_VECSMALL) | _evallg(6), vZ, -3, 5, -2, 1 }; /* z^3 - 2*z^2 + 5*z - 3 */
static const long X1_34_s_n_6[5] = {
  evaltyp(t_VECSMALL) | _evallg(5), vZ, -3, 3, 1 }; /* z^2 + 3*z - 3 */
static const long *X1_34_s_n[10] = {
  (long *)(evaltyp(t_POL) | _evallg(10)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_34_s_n_0, X1_34_s_n_1, X1_34_s_n_2, X1_34_s_n_3, X1_34_s_n_4, X1_34_s_n_5, X1_34_s_n_6, FLX_m1
};
/* z*u^6 + (-z^2 + 3*z - 1)*u^5 + (4*z^3 - z^2 + z - 3)*u^4 + (-z^5 + 6*z^3 - z^2 - 2*z - 3)*u^3 + (z^6 + 3*z^3 + z^2 - 1)*u^2 + (2*z^4 + 3*z^3 + 2*z^2 + z)*u + (z^5 + 2*z^4 + z^3) */
static const long X1_34_s_d_0[8] = {
  evaltyp(t_VECSMALL) | _evallg(8), vZ, 0, 0, 0, 1, 2, 1 }; /* z^5 + 2*z^4 + z^3 */
static const long X1_34_s_d_1[7] = {
  evaltyp(t_VECSMALL) | _evallg(7), vZ, 0, 1, 2, 3, 2 }; /* 2*z^4 + 3*z^3 + 2*z^2 + z */
static const long X1_34_s_d_2[9] = {
  evaltyp(t_VECSMALL) | _evallg(9), vZ, -1, 0, 1, 3, 0, 0, 1 }; /* z^6 + 3*z^3 + z^2 - 1 */
static const long X1_34_s_d_3[8] = {
  evaltyp(t_VECSMALL) | _evallg(8), vZ, -3, -2, -1, 6, 0, -1 }; /* -z^5 + 6*z^3 - z^2 - 2*z - 3 */
static const long X1_34_s_d_4[6] = {
  evaltyp(t_VECSMALL) | _evallg(6), vZ, -3, 1, -1, 4 }; /* 4*z^3 - z^2 + z - 3 */
static const long X1_34_s_d_5[5] = {
  evaltyp(t_VECSMALL) | _evallg(5), vZ, -1, 3, -1 }; /* -z^2 + 3*z - 1 */
static const long *X1_34_s_d[9] = {
  (long *)(evaltyp(t_POL) | _evallg(9)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_34_s_d_0, X1_34_s_d_1, X1_34_s_d_2, X1_34_s_d_3, X1_34_s_d_4, X1_34_s_d_5, FLX_Z
};
/* z^3*u^12 + (-z^7 - 8*z^4 - 6*z^3 - z)*u^11 + (7*z^8 + 5*z^7 + 25*z^5 + 44*z^4 + 12*z^3 + 7*z^2 + 5*z)*u^10 + (-18*z^9 - 32*z^8 - 7*z^7 - 34*z^6 - 122*z^5 - 80*z^4 - 27*z^3 - 32*z^2 - 8*z + 1)*u^9 + (-z^11 + 19*z^10 + 72*z^9 + 41*z^8 + 3*z^7 + 141*z^6 + 193*z^5 + 71*z^4 + 75*z^3 + 47*z^2 - 2*z - 3)*u^8 + (4*z^12 + 4*z^11 - 59*z^10 - 79*z^9 + 44*z^8 + 5*z^7 - 178*z^6 - 100*z^5 - 72*z^4 - 99*z^3 - 9*z^2 + 17*z + 3)*u^7 + (-6*z^13 - 32*z^12 - 24*z^11 + 45*z^10 - 43*z^9 - 174*z^8 - 37*z^7 + 35*z^6 - z^5 + 90*z^4 + 34*z^3 - 35*z^2 - 15*z - 1)*u^6 + (4*z^14 + 33*z^13 + 80*z^12 + 42*z^11 + 9*z^10 + 145*z^9 + 183*z^8 + 73*z^7 + 60*z^6 - 27*z^5 - 52*z^4 + 32*z^3 + 27*z^2 + 3*z)*u^5 + (-z^15 - 14*z^14 - 57*z^13 - 72*z^12 - 6*z^10 - 100*z^9 - 84*z^8 - 47*z^7 - 3*z^6 + 50*z^5 - 6*z^4 - 27*z^3 + 2*z)*u^4 + (2*z^15 + 16*z^14 + 36*z^13 + 6*z^12 - 45*z^11 - 13*z^10 + 25*z^9 + 11*z^8 - 7*z^7 - 36*z^6 - 15*z^5 + 19*z^4 - 8*z^2 - z)*u^3 + (-z^15 - 6*z^14 - 3*z^13 + 21*z^12 + 26*z^11 + z^10 - 3*z^9 + 9*z^8 + 20*z^7 + 16*z^6 - 8*z^5 - 7*z^4 + 7*z^3 + 4*z^2)*u^2 + (-3*z^13 - 6*z^12 + z^11 + 7*z^10 + z^9 - 6*z^8 - 7*z^7 + z^6 + 7*z^5 + z^4 - 3*z^3 - z^2)*u + (-z^12 - 3*z^11 - 3*z^10 - z^9 - z^7 - 3*z^6 - 3*z^5 - z^4) */
static const long X1_35_crv_0[15] = {
  evaltyp(t_VECSMALL) | _evallg(15), vZ, 0, 0, 0, 0, -1, -3, -3, -1, 0, -1, -3, -3, -1 }; /* -z^12 - 3*z^11 - 3*z^10 - z^9 - z^7 - 3*z^6 - 3*z^5 - z^4 */
static const long X1_35_crv_1[16] = {
  evaltyp(t_VECSMALL) | _evallg(16), vZ, 0, 0, -1, -3, 1, 7, 1, -7, -6, 1, 7, 1, -6, -3 }; /* -3*z^13 - 6*z^12 + z^11 + 7*z^10 + z^9 - 6*z^8 - 7*z^7 + z^6 + 7*z^5 + z^4 - 3*z^3 - z^2 */
static const long X1_35_crv_2[18] = {
  evaltyp(t_VECSMALL) | _evallg(18), vZ, 0, 0, 4, 7, -7, -8, 16, 20, 9, -3, 1, 26, 21, -3, -6, -1 }; /* -z^15 - 6*z^14 - 3*z^13 + 21*z^12 + 26*z^11 + z^10 - 3*z^9 + 9*z^8 + 20*z^7 + 16*z^6 - 8*z^5 - 7*z^4 + 7*z^3 + 4*z^2 */
static const long X1_35_crv_3[18] = {
  evaltyp(t_VECSMALL) | _evallg(18), vZ, 0, -1, -8, 0, 19, -15, -36, -7, 11, 25, -13, -45, 6, 36, 16, 2 }; /* 2*z^15 + 16*z^14 + 36*z^13 + 6*z^12 - 45*z^11 - 13*z^10 + 25*z^9 + 11*z^8 - 7*z^7 - 36*z^6 - 15*z^5 + 19*z^4 - 8*z^2 - z */
static const long X1_35_crv_4[18] = {
  evaltyp(t_VECSMALL) | _evallg(18), vZ, 0, 2, 0, -27, -6, 50, -3, -47, -84, -100, -6, 0, -72, -57, -14, -1 }; /* -z^15 - 14*z^14 - 57*z^13 - 72*z^12 - 6*z^10 - 100*z^9 - 84*z^8 - 47*z^7 - 3*z^6 + 50*z^5 - 6*z^4 - 27*z^3 + 2*z */
static const long X1_35_crv_5[17] = {
  evaltyp(t_VECSMALL) | _evallg(17), vZ, 0, 3, 27, 32, -52, -27, 60, 73, 183, 145, 9, 42, 80, 33, 4 }; /* 4*z^14 + 33*z^13 + 80*z^12 + 42*z^11 + 9*z^10 + 145*z^9 + 183*z^8 + 73*z^7 + 60*z^6 - 27*z^5 - 52*z^4 + 32*z^3 + 27*z^2 + 3*z */
static const long X1_35_crv_6[16] = {
  evaltyp(t_VECSMALL) | _evallg(16), vZ, -1, -15, -35, 34, 90, -1, 35, -37, -174, -43, 45, -24, -32, -6 }; /* -6*z^13 - 32*z^12 - 24*z^11 + 45*z^10 - 43*z^9 - 174*z^8 - 37*z^7 + 35*z^6 - z^5 + 90*z^4 + 34*z^3 - 35*z^2 - 15*z - 1 */
static const long X1_35_crv_7[15] = {
  evaltyp(t_VECSMALL) | _evallg(15), vZ, 3, 17, -9, -99, -72, -100, -178, 5, 44, -79, -59, 4, 4 }; /* 4*z^12 + 4*z^11 - 59*z^10 - 79*z^9 + 44*z^8 + 5*z^7 - 178*z^6 - 100*z^5 - 72*z^4 - 99*z^3 - 9*z^2 + 17*z + 3 */
static const long X1_35_crv_8[14] = {
  evaltyp(t_VECSMALL) | _evallg(14), vZ, -3, -2, 47, 75, 71, 193, 141, 3, 41, 72, 19, -1 }; /* -z^11 + 19*z^10 + 72*z^9 + 41*z^8 + 3*z^7 + 141*z^6 + 193*z^5 + 71*z^4 + 75*z^3 + 47*z^2 - 2*z - 3 */
static const long X1_35_crv_9[12] = {
  evaltyp(t_VECSMALL) | _evallg(12), vZ, 1, -8, -32, -27, -80, -122, -34, -7, -32, -18 }; /* -18*z^9 - 32*z^8 - 7*z^7 - 34*z^6 - 122*z^5 - 80*z^4 - 27*z^3 - 32*z^2 - 8*z + 1 */
static const long X1_35_crv_10[11] = {
  evaltyp(t_VECSMALL) | _evallg(11), vZ, 0, 5, 7, 12, 44, 25, 0, 5, 7 }; /* 7*z^8 + 5*z^7 + 25*z^5 + 44*z^4 + 12*z^3 + 7*z^2 + 5*z */
static const long X1_35_crv_11[10] = {
  evaltyp(t_VECSMALL) | _evallg(10), vZ, 0, -1, 0, -6, -8, 0, 0, -1 }; /* -z^7 - 8*z^4 - 6*z^3 - z */
static const long X1_35_crv_12[6] = {
  evaltyp(t_VECSMALL) | _evallg(6), vZ, 0, 0, 0, 1 }; /* z^3 */
static const long *X1_35_crv[15] = {
  (long *)(evaltyp(t_POL) | _evallg(15)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_35_crv_0, X1_35_crv_1, X1_35_crv_2, X1_35_crv_3, X1_35_crv_4, X1_35_crv_5, X1_35_crv_6, X1_35_crv_7, X1_35_crv_8, X1_35_crv_9, X1_35_crv_10, X1_35_crv_11, X1_35_crv_12
};
/* -z^8*u^19 + (11*z^9 + 8*z^8 + 2*z^6)*u^18 + (-51*z^10 - 83*z^9 - 24*z^8 - 20*z^7 - 13*z^6 - z^4)*u^17 + (125*z^11 + 359*z^10 + 234*z^9 + 118*z^8 + 124*z^7 + 30*z^6 + 7*z^5 + 4*z^4)*u^16 + (-156*z^12 - 804*z^11 - 940*z^10 - 498*z^9 - 527*z^8 - 273*z^7 - 46*z^6 - 25*z^5 - 4*z^4 + 2*z^3 + z^2)*u^15 + (35*z^13 + 861*z^12 + 1909*z^11 + 1379*z^10 + 1322*z^9 + 1091*z^8 + 261*z^7 + 70*z^6 + 19*z^5 - 16*z^4 - 15*z^3 - 2*z^2)*u^14 + (174*z^14 + 19*z^13 - 1703*z^12 - 2223*z^11 - 2147*z^10 - 2523*z^9 - 972*z^8 - 162*z^7 - 62*z^6 + 61*z^5 + 79*z^4 + 21*z^3 - 2*z^2 - z - 1)*u^13 + (-232*z^15 - 1155*z^14 - 552*z^13 + 1490*z^12 + 2193*z^11 + 3700*z^10 + 2378*z^9 + 472*z^8 + 272*z^7 - 65*z^6 - 225*z^5 - 88*z^4 + 21*z^3 + 11*z^2 + 11*z + 2)*u^12 + (72*z^16 + 1175*z^15 + 2713*z^14 + 1080*z^13 - 944*z^12 - 3365*z^11 - 3864*z^10 - 1239*z^9 - 855*z^8 - 294*z^7 + 373*z^6 + 253*z^5 - 90*z^4 - 57*z^3 - 46*z^2 - 21*z - 1)*u^11 + (85*z^17 - 152*z^16 - 2096*z^15 - 2809*z^14 - 902*z^13 + 1269*z^12 + 3806*z^11 + 2152*z^10 + 1495*z^9 + 1142*z^8 - 339*z^7 - 614*z^6 + 111*z^5 + 181*z^4 + 84*z^3 + 81*z^2 + 11*z)*u^10 + (-85*z^18 - 520*z^17 - 149*z^16 + 1678*z^15 + 1797*z^14 + 1203*z^13 - 1299*z^12 - 2155*z^11 - 1471*z^10 - 1685*z^9 + 163*z^8 + 1172*z^7 + 249*z^6 - 319*z^5 - 62*z^4 - 132*z^3 - 43*z^2)*u^9 + (19*z^19 + 357*z^18 + 1085*z^17 + 381*z^16 - 1194*z^15 - 2243*z^14 - 1704*z^13 + 870*z^12 + 1000*z^11 + 1263*z^10 - 131*z^9 - 1589*z^8 - 952*z^7 + 278*z^6 + 36*z^5 + 65*z^4 + 75*z^3 - z^2 + 2*z)*u^8 + (7*z^20 - 40*z^19 - 522*z^18 - 898*z^17 + 184*z^16 + 1590*z^15 + 2413*z^14 + 396*z^13 - 950*z^12 - 708*z^11 + 188*z^10 + 1491*z^9 + 1264*z^8 - 100*z^7 - 187*z^6 + 53*z^5 - 73*z^4 + 12*z^3 - 9*z^2 - 2*z)*u^7 + (-3*z^21 - 34*z^20 - 2*z^19 + 314*z^18 + 201*z^17 - 523*z^16 - 1148*z^15 - 515*z^14 + 1090*z^13 + 767*z^12 - 67*z^11 - 980*z^10 - 905*z^9 + 43*z^8 + 463*z^7 - 23*z^6 + 39*z^5 - 27*z^4 + 2*z^3 + 11*z^2)*u^6 + (9*z^21 + 56*z^20 + 40*z^19 - 101*z^18 - 10*z^17 + 100*z^16 + 74*z^15 - 730*z^14 - 802*z^13 - 104*z^12 + 449*z^11 + 429*z^10 - 71*z^9 - 525*z^8 - 125*z^7 + 20*z^6 + 34*z^5 + 32*z^4 - 13*z^3)*u^5 + (-9*z^21 - 37*z^20 + 79*z^18 + 103*z^17 + 86*z^16 + 178*z^15 + 385*z^14 + 109*z^13 - 137*z^12 - 168*z^11 + 29*z^10 + 289*z^9 + 172*z^8 - 57*z^7 - 42*z^6 - 50*z^5 + 4*z^4 - z^3)*u^4 + (3*z^21 + 7*z^20 - 26*z^19 - 43*z^18 - 24*z^17 + 43*z^16 - 13*z^15 - 29*z^14 + 28*z^13 + 49*z^12 + 24*z^11 - 54*z^10 - 82*z^9 + 35*z^8 + 40*z^7 + 31*z^6 - 2*z^5 - 4*z^4 + z^3 - z^2)*u^3 + (z^20 + 9*z^19 - 4*z^18 - 30*z^17 - 44*z^16 - 5*z^15 - 6*z^13 - 25*z^12 - 17*z^11 + 9*z^10 - 5*z^9 - 19*z^8 - 11*z^7 + z^6 + 8*z^5 - z^4)*u^2 + (5*z^18 + 7*z^17 - 8*z^15 - 4*z^14 + 4*z^13 + 6*z^12 - 5*z^11 - 10*z^10 - 4*z^9 - z^8 - z^7 - 5*z^6 - 2*z^5)*u + (z^17 + 2*z^16 + z^15 - z^14 - 2*z^13 + 2*z^11 + z^10 - z^9 - 2*z^8 - z^7) */
static const long X1_35_r_n_0[20] = {
  evaltyp(t_VECSMALL) | _evallg(20), vZ, 0, 0, 0, 0, 0, 0, 0, -1, -2, -1, 1, 2, 0, -2, -1, 1, 2, 1 }; /* z^17 + 2*z^16 + z^15 - z^14 - 2*z^13 + 2*z^11 + z^10 - z^9 - 2*z^8 - z^7 */
static const long X1_35_r_n_1[21] = {
  evaltyp(t_VECSMALL) | _evallg(21), vZ, 0, 0, 0, 0, 0, -2, -5, -1, -1, -4, -10, -5, 6, 4, -4, -8, 0, 7, 5 }; /* 5*z^18 + 7*z^17 - 8*z^15 - 4*z^14 + 4*z^13 + 6*z^12 - 5*z^11 - 10*z^10 - 4*z^9 - z^8 - z^7 - 5*z^6 - 2*z^5 */
static const long X1_35_r_n_2[23] = {
  evaltyp(t_VECSMALL) | _evallg(23), vZ, 0, 0, 0, 0, -1, 8, 1, -11, -19, -5, 9, -17, -25, -6, 0, -5, -44, -30, -4, 9, 1 }; /* z^20 + 9*z^19 - 4*z^18 - 30*z^17 - 44*z^16 - 5*z^15 - 6*z^13 - 25*z^12 - 17*z^11 + 9*z^10 - 5*z^9 - 19*z^8 - 11*z^7 + z^6 + 8*z^5 - z^4 */
static const long X1_35_r_n_3[24] = {
  evaltyp(t_VECSMALL) | _evallg(24), vZ, 0, 0, -1, 1, -4, -2, 31, 40, 35, -82, -54, 24, 49, 28, -29, -13, 43, -24, -43, -26, 7, 3 }; /* 3*z^21 + 7*z^20 - 26*z^19 - 43*z^18 - 24*z^17 + 43*z^16 - 13*z^15 - 29*z^14 + 28*z^13 + 49*z^12 + 24*z^11 - 54*z^10 - 82*z^9 + 35*z^8 + 40*z^7 + 31*z^6 - 2*z^5 - 4*z^4 + z^3 - z^2 */
static const long X1_35_r_n_4[24] = {
  evaltyp(t_VECSMALL) | _evallg(24), vZ, 0, 0, 0, -1, 4, -50, -42, -57, 172, 289, 29, -168, -137, 109, 385, 178, 86, 103, 79, 0, -37, -9 }; /* -9*z^21 - 37*z^20 + 79*z^18 + 103*z^17 + 86*z^16 + 178*z^15 + 385*z^14 + 109*z^13 - 137*z^12 - 168*z^11 + 29*z^10 + 289*z^9 + 172*z^8 - 57*z^7 - 42*z^6 - 50*z^5 + 4*z^4 - z^3 */
static const long X1_35_r_n_5[24] = {
  evaltyp(t_VECSMALL) | _evallg(24), vZ, 0, 0, 0, -13, 32, 34, 20, -125, -525, -71, 429, 449, -104, -802, -730, 74, 100, -10, -101, 40, 56, 9 }; /* 9*z^21 + 56*z^20 + 40*z^19 - 101*z^18 - 10*z^17 + 100*z^16 + 74*z^15 - 730*z^14 - 802*z^13 - 104*z^12 + 449*z^11 + 429*z^10 - 71*z^9 - 525*z^8 - 125*z^7 + 20*z^6 + 34*z^5 + 32*z^4 - 13*z^3 */
static const long X1_35_r_n_6[24] = {
  evaltyp(t_VECSMALL) | _evallg(24), vZ, 0, 0, 11, 2, -27, 39, -23, 463, 43, -905, -980, -67, 767, 1090, -515, -1148, -523, 201, 314, -2, -34, -3 }; /* -3*z^21 - 34*z^20 - 2*z^19 + 314*z^18 + 201*z^17 - 523*z^16 - 1148*z^15 - 515*z^14 + 1090*z^13 + 767*z^12 - 67*z^11 - 980*z^10 - 905*z^9 + 43*z^8 + 463*z^7 - 23*z^6 + 39*z^5 - 27*z^4 + 2*z^3 + 11*z^2 */
static const long X1_35_r_n_7[23] = {
  evaltyp(t_VECSMALL) | _evallg(23), vZ, 0, -2, -9, 12, -73, 53, -187, -100, 1264, 1491, 188, -708, -950, 396, 2413, 1590, 184, -898, -522, -40, 7 }; /* 7*z^20 - 40*z^19 - 522*z^18 - 898*z^17 + 184*z^16 + 1590*z^15 + 2413*z^14 + 396*z^13 - 950*z^12 - 708*z^11 + 188*z^10 + 1491*z^9 + 1264*z^8 - 100*z^7 - 187*z^6 + 53*z^5 - 73*z^4 + 12*z^3 - 9*z^2 - 2*z */
static const long X1_35_r_n_8[22] = {
  evaltyp(t_VECSMALL) | _evallg(22), vZ, 0, 2, -1, 75, 65, 36, 278, -952, -1589, -131, 1263, 1000, 870, -1704, -2243, -1194, 381, 1085, 357, 19 }; /* 19*z^19 + 357*z^18 + 1085*z^17 + 381*z^16 - 1194*z^15 - 2243*z^14 - 1704*z^13 + 870*z^12 + 1000*z^11 + 1263*z^10 - 131*z^9 - 1589*z^8 - 952*z^7 + 278*z^6 + 36*z^5 + 65*z^4 + 75*z^3 - z^2 + 2*z */
static const long X1_35_r_n_9[21] = {
  evaltyp(t_VECSMALL) | _evallg(21), vZ, 0, 0, -43, -132, -62, -319, 249, 1172, 163, -1685, -1471, -2155, -1299, 1203, 1797, 1678, -149, -520, -85 }; /* -85*z^18 - 520*z^17 - 149*z^16 + 1678*z^15 + 1797*z^14 + 1203*z^13 - 1299*z^12 - 2155*z^11 - 1471*z^10 - 1685*z^9 + 163*z^8 + 1172*z^7 + 249*z^6 - 319*z^5 - 62*z^4 - 132*z^3 - 43*z^2 */
static const long X1_35_r_n_10[20] = {
  evaltyp(t_VECSMALL) | _evallg(20), vZ, 0, 11, 81, 84, 181, 111, -614, -339, 1142, 1495, 2152, 3806, 1269, -902, -2809, -2096, -152, 85 }; /* 85*z^17 - 152*z^16 - 2096*z^15 - 2809*z^14 - 902*z^13 + 1269*z^12 + 3806*z^11 + 2152*z^10 + 1495*z^9 + 1142*z^8 - 339*z^7 - 614*z^6 + 111*z^5 + 181*z^4 + 84*z^3 + 81*z^2 + 11*z */
static const long X1_35_r_n_11[19] = {
  evaltyp(t_VECSMALL) | _evallg(19), vZ, -1, -21, -46, -57, -90, 253, 373, -294, -855, -1239, -3864, -3365, -944, 1080, 2713, 1175, 72 }; /* 72*z^16 + 1175*z^15 + 2713*z^14 + 1080*z^13 - 944*z^12 - 3365*z^11 - 3864*z^10 - 1239*z^9 - 855*z^8 - 294*z^7 + 373*z^6 + 253*z^5 - 90*z^4 - 57*z^3 - 46*z^2 - 21*z - 1 */
static const long X1_35_r_n_12[18] = {
  evaltyp(t_VECSMALL) | _evallg(18), vZ, 2, 11, 11, 21, -88, -225, -65, 272, 472, 2378, 3700, 2193, 1490, -552, -1155, -232 }; /* -232*z^15 - 1155*z^14 - 552*z^13 + 1490*z^12 + 2193*z^11 + 3700*z^10 + 2378*z^9 + 472*z^8 + 272*z^7 - 65*z^6 - 225*z^5 - 88*z^4 + 21*z^3 + 11*z^2 + 11*z + 2 */
static const long X1_35_r_n_13[17] = {
  evaltyp(t_VECSMALL) | _evallg(17), vZ, -1, -1, -2, 21, 79, 61, -62, -162, -972, -2523, -2147, -2223, -1703, 19, 174 }; /* 174*z^14 + 19*z^13 - 1703*z^12 - 2223*z^11 - 2147*z^10 - 2523*z^9 - 972*z^8 - 162*z^7 - 62*z^6 + 61*z^5 + 79*z^4 + 21*z^3 - 2*z^2 - z - 1 */
static const long X1_35_r_n_14[16] = {
  evaltyp(t_VECSMALL) | _evallg(16), vZ, 0, 0, -2, -15, -16, 19, 70, 261, 1091, 1322, 1379, 1909, 861, 35 }; /* 35*z^13 + 861*z^12 + 1909*z^11 + 1379*z^10 + 1322*z^9 + 1091*z^8 + 261*z^7 + 70*z^6 + 19*z^5 - 16*z^4 - 15*z^3 - 2*z^2 */
static const long X1_35_r_n_15[15] = {
  evaltyp(t_VECSMALL) | _evallg(15), vZ, 0, 0, 1, 2, -4, -25, -46, -273, -527, -498, -940, -804, -156 }; /* -156*z^12 - 804*z^11 - 940*z^10 - 498*z^9 - 527*z^8 - 273*z^7 - 46*z^6 - 25*z^5 - 4*z^4 + 2*z^3 + z^2 */
static const long X1_35_r_n_16[14] = {
  evaltyp(t_VECSMALL) | _evallg(14), vZ, 0, 0, 0, 0, 4, 7, 30, 124, 118, 234, 359, 125 }; /* 125*z^11 + 359*z^10 + 234*z^9 + 118*z^8 + 124*z^7 + 30*z^6 + 7*z^5 + 4*z^4 */
static const long X1_35_r_n_17[13] = {
  evaltyp(t_VECSMALL) | _evallg(13), vZ, 0, 0, 0, 0, -1, 0, -13, -20, -24, -83, -51 }; /* -51*z^10 - 83*z^9 - 24*z^8 - 20*z^7 - 13*z^6 - z^4 */
static const long X1_35_r_n_18[12] = {
  evaltyp(t_VECSMALL) | _evallg(12), vZ, 0, 0, 0, 0, 0, 0, 2, 0, 8, 11 }; /* 11*z^9 + 8*z^8 + 2*z^6 */
static const long X1_35_r_n_19[11] = {
  evaltyp(t_VECSMALL) | _evallg(11), vZ, 0, 0, 0, 0, 0, 0, 0, 0, -1 }; /* -z^8 */
static const long *X1_35_r_n[22] = {
  (long *)(evaltyp(t_POL) | _evallg(22)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_35_r_n_0, X1_35_r_n_1, X1_35_r_n_2, X1_35_r_n_3, X1_35_r_n_4, X1_35_r_n_5, X1_35_r_n_6, X1_35_r_n_7, X1_35_r_n_8, X1_35_r_n_9, X1_35_r_n_10, X1_35_r_n_11, X1_35_r_n_12, X1_35_r_n_13, X1_35_r_n_14, X1_35_r_n_15, X1_35_r_n_16, X1_35_r_n_17, X1_35_r_n_18, X1_35_r_n_19
};
/* (-z^10 + z^7)*u^16 + (10*z^11 + 5*z^10 - 9*z^8 - 4*z^7 - 2*z^5 - z^4)*u^15 + (-40*z^12 - 47*z^11 - 8*z^10 + 32*z^9 + 35*z^8 + 4*z^7 + 19*z^6 + 17*z^5 + 4*z^4 + z^3 + 2*z^2)*u^14 + (-z^14 + 77*z^13 + 175*z^12 + 71*z^11 - 48*z^10 - 122*z^9 - 33*z^8 - 75*z^7 - 107*z^6 - 48*z^5 - 12*z^4 - 22*z^3 - 6*z^2 - 1)*u^13 + (7*z^15 - 50*z^14 - 307*z^13 - 248*z^12 - 21*z^11 + 193*z^10 + 109*z^9 + 149*z^8 + 348*z^7 + 235*z^6 + 71*z^5 + 95*z^4 + 63*z^3 + 3*z^2 + 9*z + 2)*u^12 + (-19*z^16 - 79*z^15 + 169*z^14 + 406*z^13 + 219*z^12 - 27*z^11 - 153*z^10 - 117*z^9 - 627*z^8 - 612*z^7 - 237*z^6 - 201*z^5 - 257*z^4 - 38*z^3 - 28*z^2 - 20*z - 1)*u^11 + (23*z^17 + 192*z^16 + 271*z^15 - 206*z^14 - 400*z^13 - 436*z^12 - 70*z^11 - 106*z^10 + 512*z^9 + 884*z^8 + 427*z^7 + 180*z^6 + 492*z^5 + 171*z^4 + 21*z^3 + 73*z^2 + 11*z)*u^10 + (-7*z^18 - 142*z^17 - 520*z^16 - 311*z^15 + 307*z^14 + 779*z^13 + 598*z^12 + 382*z^11 + 204*z^10 - 520*z^9 - 317*z^8 + 106*z^7 - 343*z^6 - 348*z^5 + 75*z^4 - 108*z^3 - 45*z^2)*u^9 + (-11*z^19 - 6*z^18 + 271*z^17 + 539*z^16 + 53*z^15 - 548*z^14 - 883*z^13 - 517*z^12 - 885*z^11 - 445*z^10 - 196*z^9 - 456*z^8 - 282*z^7 + 295*z^6 - 201*z^5 + 2*z^4 + 91*z^3 + 2*z)*u^8 + (11*z^20 + 75*z^19 + 84*z^18 - 240*z^17 - 307*z^16 - 33*z^15 + 466*z^14 + 459*z^13 + 840*z^12 + 1094*z^11 + 575*z^10 + 413*z^9 + 589*z^8 + 9*z^7 + 163*z^6 + 191*z^5 - 109*z^4 - z^3 - 10*z^2 - 2*z)*u^7 + (-3*z^21 - 45*z^20 - 158*z^19 - 94*z^18 + 231*z^17 + 363*z^16 + 171*z^15 - 237*z^14 - 385*z^13 - 810*z^12 - 341*z^11 + 132*z^10 - 60*z^9 - 109*z^8 + 43*z^7 - 218*z^6 + 86*z^5 + 11*z^4 + 11*z^3 + 12*z^2)*u^6 + (9*z^21 + 66*z^20 + 128*z^19 - 49*z^18 - 304*z^17 - 367*z^16 - 4*z^15 + 143*z^14 + 189*z^13 - 122*z^12 - 610*z^11 - 532*z^10 - 58*z^9 - 108*z^8 + 91*z^7 - 19*z^6 - 22*z^5 + 19*z^4 - 19*z^3)*u^5 + (-9*z^21 - 40*z^20 - 16*z^19 + 130*z^18 + 208*z^17 + 70*z^16 - 130*z^15 + 7*z^14 + 219*z^13 + 509*z^12 + 451*z^11 + 43*z^10 - 81*z^9 - 62*z^8 - 56*z^7 + 12*z^6 - 48*z^5 + 4*z^4)*u^4 + (3*z^21 + 7*z^20 - 27*z^19 - 58*z^18 - 16*z^17 + 104*z^16 + 68*z^15 - 67*z^14 - 162*z^13 - 115*z^12 + 88*z^11 + 186*z^10 + 80*z^9 + 36*z^8 - 18*z^7 + 18*z^6 + 6*z^5 - 3*z^4 - z^2)*u^3 + (z^20 + 9*z^19 - 4*z^18 - 36*z^17 - 51*z^16 + 2*z^15 + 26*z^14 + 8*z^13 - 60*z^12 - 85*z^11 - 24*z^10 + 28*z^9 + 38*z^8 + 19*z^7 + 4*z^5 - z^4 + z^3)*u^2 + (5*z^18 + 7*z^17 - z^16 - 10*z^15 - 4*z^14 + 9*z^13 + 14*z^12 - 3*z^11 - 19*z^10 - 17*z^9 - 7*z^8 + 3*z^7 + 2*z^6 + 2*z^5 + z^4)*u + (z^17 + 2*z^16 + z^15 - z^14 - 2*z^13 + 2*z^11 + z^10 - z^9 - 2*z^8 - z^7) */
static const long X1_35_r_d_0[20] = {
  evaltyp(t_VECSMALL) | _evallg(20), vZ, 0, 0, 0, 0, 0, 0, 0, -1, -2, -1, 1, 2, 0, -2, -1, 1, 2, 1 }; /* z^17 + 2*z^16 + z^15 - z^14 - 2*z^13 + 2*z^11 + z^10 - z^9 - 2*z^8 - z^7 */
static const long X1_35_r_d_1[21] = {
  evaltyp(t_VECSMALL) | _evallg(21), vZ, 0, 0, 0, 0, 1, 2, 2, 3, -7, -17, -19, -3, 14, 9, -4, -10, -1, 7, 5 }; /* 5*z^18 + 7*z^17 - z^16 - 10*z^15 - 4*z^14 + 9*z^13 + 14*z^12 - 3*z^11 - 19*z^10 - 17*z^9 - 7*z^8 + 3*z^7 + 2*z^6 + 2*z^5 + z^4 */
static const long X1_35_r_d_2[23] = {
  evaltyp(t_VECSMALL) | _evallg(23), vZ, 0, 0, 0, 1, -1, 4, 0, 19, 38, 28, -24, -85, -60, 8, 26, 2, -51, -36, -4, 9, 1 }; /* z^20 + 9*z^19 - 4*z^18 - 36*z^17 - 51*z^16 + 2*z^15 + 26*z^14 + 8*z^13 - 60*z^12 - 85*z^11 - 24*z^10 + 28*z^9 + 38*z^8 + 19*z^7 + 4*z^5 - z^4 + z^3 */
static const long X1_35_r_d_3[24] = {
  evaltyp(t_VECSMALL) | _evallg(24), vZ, 0, 0, -1, 0, -3, 6, 18, -18, 36, 80, 186, 88, -115, -162, -67, 68, 104, -16, -58, -27, 7, 3 }; /* 3*z^21 + 7*z^20 - 27*z^19 - 58*z^18 - 16*z^17 + 104*z^16 + 68*z^15 - 67*z^14 - 162*z^13 - 115*z^12 + 88*z^11 + 186*z^10 + 80*z^9 + 36*z^8 - 18*z^7 + 18*z^6 + 6*z^5 - 3*z^4 - z^2 */
static const long X1_35_r_d_4[24] = {
  evaltyp(t_VECSMALL) | _evallg(24), vZ, 0, 0, 0, 0, 4, -48, 12, -56, -62, -81, 43, 451, 509, 219, 7, -130, 70, 208, 130, -16, -40, -9 }; /* -9*z^21 - 40*z^20 - 16*z^19 + 130*z^18 + 208*z^17 + 70*z^16 - 130*z^15 + 7*z^14 + 219*z^13 + 509*z^12 + 451*z^11 + 43*z^10 - 81*z^9 - 62*z^8 - 56*z^7 + 12*z^6 - 48*z^5 + 4*z^4 */
static const long X1_35_r_d_5[24] = {
  evaltyp(t_VECSMALL) | _evallg(24), vZ, 0, 0, 0, -19, 19, -22, -19, 91, -108, -58, -532, -610, -122, 189, 143, -4, -367, -304, -49, 128, 66, 9 }; /* 9*z^21 + 66*z^20 + 128*z^19 - 49*z^18 - 304*z^17 - 367*z^16 - 4*z^15 + 143*z^14 + 189*z^13 - 122*z^12 - 610*z^11 - 532*z^10 - 58*z^9 - 108*z^8 + 91*z^7 - 19*z^6 - 22*z^5 + 19*z^4 - 19*z^3 */
static const long X1_35_r_d_6[24] = {
  evaltyp(t_VECSMALL) | _evallg(24), vZ, 0, 0, 12, 11, 11, 86, -218, 43, -109, -60, 132, -341, -810, -385, -237, 171, 363, 231, -94, -158, -45, -3 }; /* -3*z^21 - 45*z^20 - 158*z^19 - 94*z^18 + 231*z^17 + 363*z^16 + 171*z^15 - 237*z^14 - 385*z^13 - 810*z^12 - 341*z^11 + 132*z^10 - 60*z^9 - 109*z^8 + 43*z^7 - 218*z^6 + 86*z^5 + 11*z^4 + 11*z^3 + 12*z^2 */
static const long X1_35_r_d_7[23] = {
  evaltyp(t_VECSMALL) | _evallg(23), vZ, 0, -2, -10, -1, -109, 191, 163, 9, 589, 413, 575, 1094, 840, 459, 466, -33, -307, -240, 84, 75, 11 }; /* 11*z^20 + 75*z^19 + 84*z^18 - 240*z^17 - 307*z^16 - 33*z^15 + 466*z^14 + 459*z^13 + 840*z^12 + 1094*z^11 + 575*z^10 + 413*z^9 + 589*z^8 + 9*z^7 + 163*z^6 + 191*z^5 - 109*z^4 - z^3 - 10*z^2 - 2*z */
static const long X1_35_r_d_8[22] = {
  evaltyp(t_VECSMALL) | _evallg(22), vZ, 0, 2, 0, 91, 2, -201, 295, -282, -456, -196, -445, -885, -517, -883, -548, 53, 539, 271, -6, -11 }; /* -11*z^19 - 6*z^18 + 271*z^17 + 539*z^16 + 53*z^15 - 548*z^14 - 883*z^13 - 517*z^12 - 885*z^11 - 445*z^10 - 196*z^9 - 456*z^8 - 282*z^7 + 295*z^6 - 201*z^5 + 2*z^4 + 91*z^3 + 2*z */
static const long X1_35_r_d_9[21] = {
  evaltyp(t_VECSMALL) | _evallg(21), vZ, 0, 0, -45, -108, 75, -348, -343, 106, -317, -520, 204, 382, 598, 779, 307, -311, -520, -142, -7 }; /* -7*z^18 - 142*z^17 - 520*z^16 - 311*z^15 + 307*z^14 + 779*z^13 + 598*z^12 + 382*z^11 + 204*z^10 - 520*z^9 - 317*z^8 + 106*z^7 - 343*z^6 - 348*z^5 + 75*z^4 - 108*z^3 - 45*z^2 */
static const long X1_35_r_d_10[20] = {
  evaltyp(t_VECSMALL) | _evallg(20), vZ, 0, 11, 73, 21, 171, 492, 180, 427, 884, 512, -106, -70, -436, -400, -206, 271, 192, 23 }; /* 23*z^17 + 192*z^16 + 271*z^15 - 206*z^14 - 400*z^13 - 436*z^12 - 70*z^11 - 106*z^10 + 512*z^9 + 884*z^8 + 427*z^7 + 180*z^6 + 492*z^5 + 171*z^4 + 21*z^3 + 73*z^2 + 11*z */
static const long X1_35_r_d_11[19] = {
  evaltyp(t_VECSMALL) | _evallg(19), vZ, -1, -20, -28, -38, -257, -201, -237, -612, -627, -117, -153, -27, 219, 406, 169, -79, -19 }; /* -19*z^16 - 79*z^15 + 169*z^14 + 406*z^13 + 219*z^12 - 27*z^11 - 153*z^10 - 117*z^9 - 627*z^8 - 612*z^7 - 237*z^6 - 201*z^5 - 257*z^4 - 38*z^3 - 28*z^2 - 20*z - 1 */
static const long X1_35_r_d_12[18] = {
  evaltyp(t_VECSMALL) | _evallg(18), vZ, 2, 9, 3, 63, 95, 71, 235, 348, 149, 109, 193, -21, -248, -307, -50, 7 }; /* 7*z^15 - 50*z^14 - 307*z^13 - 248*z^12 - 21*z^11 + 193*z^10 + 109*z^9 + 149*z^8 + 348*z^7 + 235*z^6 + 71*z^5 + 95*z^4 + 63*z^3 + 3*z^2 + 9*z + 2 */
static const long X1_35_r_d_13[17] = {
  evaltyp(t_VECSMALL) | _evallg(17), vZ, -1, 0, -6, -22, -12, -48, -107, -75, -33, -122, -48, 71, 175, 77, -1 }; /* -z^14 + 77*z^13 + 175*z^12 + 71*z^11 - 48*z^10 - 122*z^9 - 33*z^8 - 75*z^7 - 107*z^6 - 48*z^5 - 12*z^4 - 22*z^3 - 6*z^2 - 1 */
static const long X1_35_r_d_14[15] = {
  evaltyp(t_VECSMALL) | _evallg(15), vZ, 0, 0, 2, 1, 4, 17, 19, 4, 35, 32, -8, -47, -40 }; /* -40*z^12 - 47*z^11 - 8*z^10 + 32*z^9 + 35*z^8 + 4*z^7 + 19*z^6 + 17*z^5 + 4*z^4 + z^3 + 2*z^2 */
static const long X1_35_r_d_15[14] = {
  evaltyp(t_VECSMALL) | _evallg(14), vZ, 0, 0, 0, 0, -1, -2, 0, -4, -9, 0, 5, 10 }; /* 10*z^11 + 5*z^10 - 9*z^8 - 4*z^7 - 2*z^5 - z^4 */
static const long X1_35_r_d_16[13] = {
  evaltyp(t_VECSMALL) | _evallg(13), vZ, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1 }; /* -z^10 + z^7 */
static const long *X1_35_r_d[19] = {
  (long *)(evaltyp(t_POL) | _evallg(19)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_35_r_d_0, X1_35_r_d_1, X1_35_r_d_2, X1_35_r_d_3, X1_35_r_d_4, X1_35_r_d_5, X1_35_r_d_6, X1_35_r_d_7, X1_35_r_d_8, X1_35_r_d_9, X1_35_r_d_10, X1_35_r_d_11, X1_35_r_d_12, X1_35_r_d_13, X1_35_r_d_14, X1_35_r_d_15, X1_35_r_d_16
};
/* z^4*u^10 + (-5*z^5 - 4*z^4 - z^2)*u^9 + (7*z^6 + 18*z^5 + 4*z^4 + 4*z^3 + 2*z^2)*u^8 + (3*z^7 - 22*z^6 - 16*z^5 - 5*z^4 - 6*z^3 + z + 1)*u^7 + (-14*z^8 - 10*z^7 + 17*z^6 + z^5 + 5*z^4 - 3*z^3 - 3*z^2 - 6*z - 1)*u^6 + (7*z^9 + 36*z^8 + 8*z^7 + 2*z^6 - z^5 + 5*z^4 + 3*z^3 + 10*z^2 + 6*z)*u^5 + (4*z^10 - 15*z^9 - 23*z^8 + 2*z^6 + 3*z^5 + z^4 - 3*z^3 - 9*z^2)*u^4 + (-3*z^11 - 9*z^10 + 8*z^9 - 2*z^8 - 4*z^7 - 9*z^6 - 5*z^5 - 6*z^4 + 6*z^3 - z^2)*u^3 + (6*z^11 + 5*z^10 + 3*z^8 + 4*z^7 + 3*z^6 + 5*z^5 - 3*z^4 + z^2 - z)*u^2 + (-3*z^11 + z^10 - z^8 - z^7 - 2*z^6 + z^4 - 2*z^3)*u + (-z^10 - z^5) */
static const long X1_35_s_n_0[13] = {
  evaltyp(t_VECSMALL) | _evallg(13), vZ, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1 }; /* -z^10 - z^5 */
static const long X1_35_s_n_1[14] = {
  evaltyp(t_VECSMALL) | _evallg(14), vZ, 0, 0, 0, -2, 1, 0, -2, -1, -1, 0, 1, -3 }; /* -3*z^11 + z^10 - z^8 - z^7 - 2*z^6 + z^4 - 2*z^3 */
static const long X1_35_s_n_2[14] = {
  evaltyp(t_VECSMALL) | _evallg(14), vZ, 0, -1, 1, 0, -3, 5, 3, 4, 3, 0, 5, 6 }; /* 6*z^11 + 5*z^10 + 3*z^8 + 4*z^7 + 3*z^6 + 5*z^5 - 3*z^4 + z^2 - z */
static const long X1_35_s_n_3[14] = {
  evaltyp(t_VECSMALL) | _evallg(14), vZ, 0, 0, -1, 6, -6, -5, -9, -4, -2, 8, -9, -3 }; /* -3*z^11 - 9*z^10 + 8*z^9 - 2*z^8 - 4*z^7 - 9*z^6 - 5*z^5 - 6*z^4 + 6*z^3 - z^2 */
static const long X1_35_s_n_4[13] = {
  evaltyp(t_VECSMALL) | _evallg(13), vZ, 0, 0, -9, -3, 1, 3, 2, 0, -23, -15, 4 }; /* 4*z^10 - 15*z^9 - 23*z^8 + 2*z^6 + 3*z^5 + z^4 - 3*z^3 - 9*z^2 */
static const long X1_35_s_n_5[12] = {
  evaltyp(t_VECSMALL) | _evallg(12), vZ, 0, 6, 10, 3, 5, -1, 2, 8, 36, 7 }; /* 7*z^9 + 36*z^8 + 8*z^7 + 2*z^6 - z^5 + 5*z^4 + 3*z^3 + 10*z^2 + 6*z */
static const long X1_35_s_n_6[11] = {
  evaltyp(t_VECSMALL) | _evallg(11), vZ, -1, -6, -3, -3, 5, 1, 17, -10, -14 }; /* -14*z^8 - 10*z^7 + 17*z^6 + z^5 + 5*z^4 - 3*z^3 - 3*z^2 - 6*z - 1 */
static const long X1_35_s_n_7[10] = {
  evaltyp(t_VECSMALL) | _evallg(10), vZ, 1, 1, 0, -6, -5, -16, -22, 3 }; /* 3*z^7 - 22*z^6 - 16*z^5 - 5*z^4 - 6*z^3 + z + 1 */
static const long X1_35_s_n_8[9] = {
  evaltyp(t_VECSMALL) | _evallg(9), vZ, 0, 0, 2, 4, 4, 18, 7 }; /* 7*z^6 + 18*z^5 + 4*z^4 + 4*z^3 + 2*z^2 */
static const long X1_35_s_n_9[8] = {
  evaltyp(t_VECSMALL) | _evallg(8), vZ, 0, 0, -1, 0, -4, -5 }; /* -5*z^5 - 4*z^4 - z^2 */
static const long X1_35_s_n_10[7] = {
  evaltyp(t_VECSMALL) | _evallg(7), vZ, 0, 0, 0, 0, 1 }; /* z^4 */
static const long *X1_35_s_n[13] = {
  (long *)(evaltyp(t_POL) | _evallg(13)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_35_s_n_0, X1_35_s_n_1, X1_35_s_n_2, X1_35_s_n_3, X1_35_s_n_4, X1_35_s_n_5, X1_35_s_n_6, X1_35_s_n_7, X1_35_s_n_8, X1_35_s_n_9, X1_35_s_n_10
};
/* z^5*u^9 + (-6*z^6 - 3*z^5 - z^3 - z^2)*u^8 + (13*z^7 + 16*z^6 + 2*z^5 + 5*z^4 + 8*z^3 + 2*z^2 + 1)*u^7 + (-10*z^8 - 31*z^7 - 9*z^6 - 10*z^5 - 22*z^4 - 13*z^3 + z^2 - 5*z - 1)*u^6 + (-3*z^9 + 21*z^8 + 16*z^7 + 10*z^6 + 30*z^5 + 28*z^4 - 3*z^3 + 6*z^2 + 6*z)*u^5 + (8*z^10 + 7*z^9 - 11*z^8 - 5*z^7 - 22*z^6 - 25*z^5 + 5*z^4 + 6*z^3 - 10*z^2)*u^4 + (-3*z^11 - 16*z^10 - 3*z^9 + z^8 + 7*z^7 + 6*z^6 - 8*z^5 - 20*z^4 + 5*z^3)*u^3 + (6*z^11 + 8*z^10 - z^9 + 3*z^7 + 7*z^6 + 16*z^5 + z^4 - 2*z^3 - z)*u^2 + (-3*z^11 + z^10 + z^9 - z^8 - 2*z^7 - 4*z^6 - z^5 + 3*z^4 + z^2)*u + (-z^10 - z^5) */
static const long X1_35_s_d_0[13] = {
  evaltyp(t_VECSMALL) | _evallg(13), vZ, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1 }; /* -z^10 - z^5 */
static const long X1_35_s_d_1[14] = {
  evaltyp(t_VECSMALL) | _evallg(14), vZ, 0, 0, 1, 0, 3, -1, -4, -2, -1, 1, 1, -3 }; /* -3*z^11 + z^10 + z^9 - z^8 - 2*z^7 - 4*z^6 - z^5 + 3*z^4 + z^2 */
static const long X1_35_s_d_2[14] = {
  evaltyp(t_VECSMALL) | _evallg(14), vZ, 0, -1, 0, -2, 1, 16, 7, 3, 0, -1, 8, 6 }; /* 6*z^11 + 8*z^10 - z^9 + 3*z^7 + 7*z^6 + 16*z^5 + z^4 - 2*z^3 - z */
static const long X1_35_s_d_3[14] = {
  evaltyp(t_VECSMALL) | _evallg(14), vZ, 0, 0, 0, 5, -20, -8, 6, 7, 1, -3, -16, -3 }; /* -3*z^11 - 16*z^10 - 3*z^9 + z^8 + 7*z^7 + 6*z^6 - 8*z^5 - 20*z^4 + 5*z^3 */
static const long X1_35_s_d_4[13] = {
  evaltyp(t_VECSMALL) | _evallg(13), vZ, 0, 0, -10, 6, 5, -25, -22, -5, -11, 7, 8 }; /* 8*z^10 + 7*z^9 - 11*z^8 - 5*z^7 - 22*z^6 - 25*z^5 + 5*z^4 + 6*z^3 - 10*z^2 */
static const long X1_35_s_d_5[12] = {
  evaltyp(t_VECSMALL) | _evallg(12), vZ, 0, 6, 6, -3, 28, 30, 10, 16, 21, -3 }; /* -3*z^9 + 21*z^8 + 16*z^7 + 10*z^6 + 30*z^5 + 28*z^4 - 3*z^3 + 6*z^2 + 6*z */
static const long X1_35_s_d_6[11] = {
  evaltyp(t_VECSMALL) | _evallg(11), vZ, -1, -5, 1, -13, -22, -10, -9, -31, -10 }; /* -10*z^8 - 31*z^7 - 9*z^6 - 10*z^5 - 22*z^4 - 13*z^3 + z^2 - 5*z - 1 */
static const long X1_35_s_d_7[10] = {
  evaltyp(t_VECSMALL) | _evallg(10), vZ, 1, 0, 2, 8, 5, 2, 16, 13 }; /* 13*z^7 + 16*z^6 + 2*z^5 + 5*z^4 + 8*z^3 + 2*z^2 + 1 */
static const long X1_35_s_d_8[9] = {
  evaltyp(t_VECSMALL) | _evallg(9), vZ, 0, 0, -1, -1, 0, -3, -6 }; /* -6*z^6 - 3*z^5 - z^3 - z^2 */
static const long X1_35_s_d_9[8] = {
  evaltyp(t_VECSMALL) | _evallg(8), vZ, 0, 0, 0, 0, 0, 1 }; /* z^5 */
static const long *X1_35_s_d[12] = {
  (long *)(evaltyp(t_POL) | _evallg(12)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_35_s_d_0, X1_35_s_d_1, X1_35_s_d_2, X1_35_s_d_3, X1_35_s_d_4, X1_35_s_d_5, X1_35_s_d_6, X1_35_s_d_7, X1_35_s_d_8, X1_35_s_d_9
};
/* (z^7 - 2*z^6 + 2*z^5 - z^4)*u^8 + (4*z^8 - 4*z^7 + 4*z^5 - 4*z^4)*u^7 + (6*z^9 + 2*z^8 - 10*z^7 + 10*z^6 + z^5 - 13*z^4 + 4*z^3 - z^2)*u^6 + (4*z^10 + 10*z^9 - 10*z^8 + 24*z^6 - 36*z^5 + 2*z^4 + 2*z^3 - 2*z^2)*u^5 + (z^11 + 8*z^10 + z^9 - 9*z^8 + 27*z^7 - 9*z^6 - 55*z^5 + 34*z^4 - 13*z^3)*u^4 + (2*z^11 + 4*z^10 - 4*z^9 + 8*z^8 + 26*z^7 - 54*z^6 - 24*z^5 + 50*z^4 - 38*z^3 + 12*z^2 - 2*z)*u^3 + (z^11 + 15*z^8 - 3*z^7 - 43*z^6 + 9*z^5 + 29*z^4 - 39*z^3 + 22*z^2 - 7*z + 1)*u^2 + (2*z^9 + 6*z^8 - 10*z^7 - 14*z^6 + 18*z^5 - 10*z^4 + 2*z^3)*u + (z^9 - 3*z^7 + z^6) */
static const long X1_36_crv_0[12] = {
  evaltyp(t_VECSMALL) | _evallg(12), vZ, 0, 0, 0, 0, 0, 0, 1, -3, 0, 1 }; /* z^9 - 3*z^7 + z^6 */
static const long X1_36_crv_1[12] = {
  evaltyp(t_VECSMALL) | _evallg(12), vZ, 0, 0, 0, 2, -10, 18, -14, -10, 6, 2 }; /* 2*z^9 + 6*z^8 - 10*z^7 - 14*z^6 + 18*z^5 - 10*z^4 + 2*z^3 */
static const long X1_36_crv_2[14] = {
  evaltyp(t_VECSMALL) | _evallg(14), vZ, 1, -7, 22, -39, 29, 9, -43, -3, 15, 0, 0, 1 }; /* z^11 + 15*z^8 - 3*z^7 - 43*z^6 + 9*z^5 + 29*z^4 - 39*z^3 + 22*z^2 - 7*z + 1 */
static const long X1_36_crv_3[14] = {
  evaltyp(t_VECSMALL) | _evallg(14), vZ, 0, -2, 12, -38, 50, -24, -54, 26, 8, -4, 4, 2 }; /* 2*z^11 + 4*z^10 - 4*z^9 + 8*z^8 + 26*z^7 - 54*z^6 - 24*z^5 + 50*z^4 - 38*z^3 + 12*z^2 - 2*z */
static const long X1_36_crv_4[14] = {
  evaltyp(t_VECSMALL) | _evallg(14), vZ, 0, 0, 0, -13, 34, -55, -9, 27, -9, 1, 8, 1 }; /* z^11 + 8*z^10 + z^9 - 9*z^8 + 27*z^7 - 9*z^6 - 55*z^5 + 34*z^4 - 13*z^3 */
static const long X1_36_crv_5[13] = {
  evaltyp(t_VECSMALL) | _evallg(13), vZ, 0, 0, -2, 2, 2, -36, 24, 0, -10, 10, 4 }; /* 4*z^10 + 10*z^9 - 10*z^8 + 24*z^6 - 36*z^5 + 2*z^4 + 2*z^3 - 2*z^2 */
static const long X1_36_crv_6[12] = {
  evaltyp(t_VECSMALL) | _evallg(12), vZ, 0, 0, -1, 4, -13, 1, 10, -10, 2, 6 }; /* 6*z^9 + 2*z^8 - 10*z^7 + 10*z^6 + z^5 - 13*z^4 + 4*z^3 - z^2 */
static const long X1_36_crv_7[11] = {
  evaltyp(t_VECSMALL) | _evallg(11), vZ, 0, 0, 0, 0, -4, 4, 0, -4, 4 }; /* 4*z^8 - 4*z^7 + 4*z^5 - 4*z^4 */
static const long X1_36_crv_8[10] = {
  evaltyp(t_VECSMALL) | _evallg(10), vZ, 0, 0, 0, 0, -1, 2, -2, 1 }; /* z^7 - 2*z^6 + 2*z^5 - z^4 */
static const long *X1_36_crv[11] = {
  (long *)(evaltyp(t_POL) | _evallg(11)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_36_crv_0, X1_36_crv_1, X1_36_crv_2, X1_36_crv_3, X1_36_crv_4, X1_36_crv_5, X1_36_crv_6, X1_36_crv_7, X1_36_crv_8
};
/* (z^3 - z)*u^4 + (4*z^4 - 4*z^2)*u^3 + (5*z^5 + z^4 - 6*z^3 - z^2 - 1)*u^2 + (2*z^6 + 2*z^5 - 4*z^4 - 2*z^3 - 2*z)*u + (z^6 - z^5 - 2*z^4 + 3*z^3 - 5*z^2 + 3*z - 1) */
static const long X1_36_r_n_0[9] = {
  evaltyp(t_VECSMALL) | _evallg(9), vZ, -1, 3, -5, 3, -2, -1, 1 }; /* z^6 - z^5 - 2*z^4 + 3*z^3 - 5*z^2 + 3*z - 1 */
static const long X1_36_r_n_1[9] = {
  evaltyp(t_VECSMALL) | _evallg(9), vZ, 0, -2, 0, -2, -4, 2, 2 }; /* 2*z^6 + 2*z^5 - 4*z^4 - 2*z^3 - 2*z */
static const long X1_36_r_n_2[8] = {
  evaltyp(t_VECSMALL) | _evallg(8), vZ, -1, 0, -1, -6, 1, 5 }; /* 5*z^5 + z^4 - 6*z^3 - z^2 - 1 */
static const long X1_36_r_n_3[7] = {
  evaltyp(t_VECSMALL) | _evallg(7), vZ, 0, 0, -4, 0, 4 }; /* 4*z^4 - 4*z^2 */
static const long X1_36_r_n_4[6] = {
  evaltyp(t_VECSMALL) | _evallg(6), vZ, 0, -1, 0, 1 }; /* z^3 - z */
static const long *X1_36_r_n[7] = {
  (long *)(evaltyp(t_POL) | _evallg(7)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_36_r_n_0, X1_36_r_n_1, X1_36_r_n_2, X1_36_r_n_3, X1_36_r_n_4
};
/* (z^3 - z)*u^4 + (6*z^4 - 2*z^3 - 4*z^2 + z)*u^3 + (7*z^5 + 3*z^4 - 12*z^3 + 3*z^2 + z - 1)*u^2 + (2*z^6 + 5*z^5 - 5*z^4 - 8*z^3 + 9*z^2 - 5*z + 1)*u + (z^6 - 3*z^4 + z^3) */
static const long X1_36_r_d_0[9] = {
  evaltyp(t_VECSMALL) | _evallg(9), vZ, 0, 0, 0, 1, -3, 0, 1 }; /* z^6 - 3*z^4 + z^3 */
static const long X1_36_r_d_1[9] = {
  evaltyp(t_VECSMALL) | _evallg(9), vZ, 1, -5, 9, -8, -5, 5, 2 }; /* 2*z^6 + 5*z^5 - 5*z^4 - 8*z^3 + 9*z^2 - 5*z + 1 */
static const long X1_36_r_d_2[8] = {
  evaltyp(t_VECSMALL) | _evallg(8), vZ, -1, 1, 3, -12, 3, 7 }; /* 7*z^5 + 3*z^4 - 12*z^3 + 3*z^2 + z - 1 */
static const long X1_36_r_d_3[7] = {
  evaltyp(t_VECSMALL) | _evallg(7), vZ, 0, 1, -4, -2, 6 }; /* 6*z^4 - 2*z^3 - 4*z^2 + z */
static const long X1_36_r_d_4[6] = {
  evaltyp(t_VECSMALL) | _evallg(6), vZ, 0, -1, 0, 1 }; /* z^3 - z */
static const long *X1_36_r_d[7] = {
  (long *)(evaltyp(t_POL) | _evallg(7)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_36_r_d_0, X1_36_r_d_1, X1_36_r_d_2, X1_36_r_d_3, X1_36_r_d_4
};
/* (z^3 - z)*u^4 + (2*z^4 + 2*z^3 - 4*z^2 - z)*u^3 + (z^5 + 3*z^4 - 2*z^3 - 6*z^2 - 1)*u^2 + (z^5 + z^4 - 4*z^3 - 5*z^2 + z - 1)*u + (-2*z^3 - 2*z^2 + 2*z - 1) */
static const long X1_36_s_n_0[6] = {
  evaltyp(t_VECSMALL) | _evallg(6), vZ, -1, 2, -2, -2 }; /* -2*z^3 - 2*z^2 + 2*z - 1 */
static const long X1_36_s_n_1[8] = {
  evaltyp(t_VECSMALL) | _evallg(8), vZ, -1, 1, -5, -4, 1, 1 }; /* z^5 + z^4 - 4*z^3 - 5*z^2 + z - 1 */
static const long X1_36_s_n_2[8] = {
  evaltyp(t_VECSMALL) | _evallg(8), vZ, -1, 0, -6, -2, 3, 1 }; /* z^5 + 3*z^4 - 2*z^3 - 6*z^2 - 1 */
static const long X1_36_s_n_3[7] = {
  evaltyp(t_VECSMALL) | _evallg(7), vZ, 0, -1, -4, 2, 2 }; /* 2*z^4 + 2*z^3 - 4*z^2 - z */
static const long X1_36_s_n_4[6] = {
  evaltyp(t_VECSMALL) | _evallg(6), vZ, 0, -1, 0, 1 }; /* z^3 - z */
static const long *X1_36_s_n[7] = {
  (long *)(evaltyp(t_POL) | _evallg(7)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_36_s_n_0, X1_36_s_n_1, X1_36_s_n_2, X1_36_s_n_3, X1_36_s_n_4
};
/* (z^3 - z)*u^4 + (4*z^4 - 4*z^2)*u^3 + (3*z^5 + 5*z^4 - 8*z^3 - 2*z^2 + z - 1)*u^2 + (4*z^5 - 10*z^3 + 4*z^2 - 2*z)*u + (z^5 - z^4 - 4*z^3 + 3*z^2 - z) */
static const long X1_36_s_d_0[8] = {
  evaltyp(t_VECSMALL) | _evallg(8), vZ, 0, -1, 3, -4, -1, 1 }; /* z^5 - z^4 - 4*z^3 + 3*z^2 - z */
static const long X1_36_s_d_1[8] = {
  evaltyp(t_VECSMALL) | _evallg(8), vZ, 0, -2, 4, -10, 0, 4 }; /* 4*z^5 - 10*z^3 + 4*z^2 - 2*z */
static const long X1_36_s_d_2[8] = {
  evaltyp(t_VECSMALL) | _evallg(8), vZ, -1, 1, -2, -8, 5, 3 }; /* 3*z^5 + 5*z^4 - 8*z^3 - 2*z^2 + z - 1 */
static const long X1_36_s_d_3[7] = {
  evaltyp(t_VECSMALL) | _evallg(7), vZ, 0, 0, -4, 0, 4 }; /* 4*z^4 - 4*z^2 */
static const long X1_36_s_d_4[6] = {
  evaltyp(t_VECSMALL) | _evallg(6), vZ, 0, -1, 0, 1 }; /* z^3 - z */
static const long *X1_36_s_d[7] = {
  (long *)(evaltyp(t_POL) | _evallg(7)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_36_s_d_0, X1_36_s_d_1, X1_36_s_d_2, X1_36_s_d_3, X1_36_s_d_4
};
/* (z^4 + 4*z^3 + 6*z^2 + 4*z + 1)*x^18 + (4*z^6 + 27*z^5 + 61*z^4 + 53*z^3 + 3*z^2 - 20*z - 8)*x^17 + (6*z^8 + 64*z^7 + 227*z^6 + 318*z^5 + 86*z^4 - 186*z^3 - 123*z^2 + 28*z + 28)*x^16 + (4*z^10 + 70*z^9 + 390*z^8 + 899*z^7 + 697*z^6 - 460*z^5 - 878*z^4 - 71*z^3 + 299*z^2 + 18*z - 56)*x^15 + (z^12 + 36*z^11 + 334*z^10 + 1256*z^9 + 1944*z^8 + 227*z^7 - 2560*z^6 - 1975*z^5 + 530*z^4 + 635*z^3 - 205*z^2 - 65*z + 70)*x^14 + (7*z^13 + 137*z^12 + 885*z^11 + 2414*z^10 + 2085*z^9 - 2931*z^8 - 6951*z^7 - 2982*z^6 + 2372*z^5 + 2034*z^4 + 306*z^3 + 38*z^2 - 50*z - 56)*x^13 + (21*z^14 + 294*z^13 + 1420*z^12 + 2579*z^11 - 870*z^10 - 9749*z^9 - 11481*z^8 + 664*z^7 + 10483*z^6 + 6962*z^5 - 527*z^4 - 2730*z^3 - 733*z^2 + 322*z + 28)*x^12 + (35*z^15 + 363*z^14 + 1210*z^13 + 414*z^12 - 6515*z^11 - 14529*z^10 - 6010*z^9 + 16913*z^8 + 23552*z^7 + 4413*z^6 - 13117*z^5 - 8675*z^4 + 2488*z^3 + 2270*z^2 - 494*z - 8)*x^11 + (26*z^16 + 184*z^15 + 129*z^14 - 2320*z^13 - 8129*z^12 - 7355*z^11 + 12096*z^10 + 31592*z^9 + 16424*z^8 - 20987*z^7 - 29776*z^6 - 1252*z^5 + 14573*z^4 + 1991*z^3 - 3145*z^2 + 412*z + 1)*x^10 + (-z^18 - 5*z^17 - 52*z^16 - 501*z^15 - 2023*z^14 - 2681*z^13 + 4715*z^12 + 19581*z^11 + 18001*z^10 - 14660*z^9 - 40593*z^8 - 16842*z^7 + 25005*z^6 + 20440*z^5 - 8210*z^4 - 5975*z^3 + 2525*z^2 - 210*z)*x^9 + (-z^19 - 10*z^18 - 52*z^17 - 172*z^16 - 162*z^15 + 1311*z^14 + 5622*z^13 + 7317*z^12 - 5435*z^11 - 25859*z^10 - 20839*z^9 + 16281*z^8 + 34475*z^7 + 2999*z^6 - 20366*z^5 - 2065*z^4 + 5725*z^3 - 1264*z^2 + 66*z)*x^8 + (3*z^18 + 32*z^17 + 180*z^16 + 595*z^15 + 789*z^14 - 1585*z^13 - 7639*z^12 - 9008*z^11 + 5183*z^10 + 22272*z^9 + 12561*z^8 - 16256*z^7 - 16253*z^6 + 7183*z^5 + 5741*z^4 - 3053*z^3 + 395*z^2 - 12*z)*x^7 + (-3*z^17 - 39*z^16 - 243*z^15 - 807*z^14 - 1079*z^13 + 1278*z^12 + 6267*z^11 + 6155*z^10 - 4834*z^9 - 13100*z^8 - 1905*z^7 + 9941*z^6 + 1372*z^5 - 3726*z^4 + 978*z^3 - 72*z^2 + z)*x^6 + (z^16 + 22*z^15 + 166*z^14 + 564*z^13 + 678*z^12 - 891*z^11 - 3469*z^10 - 2293*z^9 + 3656*z^8 + 4495*z^7 - 2053*z^6 - 2249*z^5 + 1275*z^4 - 180*z^3 + 6*z^2)*x^5 + (-5*z^14 - 60*z^13 - 210*z^12 - 180*z^11 + 555*z^10 + 1350*z^9 + 185*z^8 - 1655*z^7 - 400*z^6 + 910*z^5 - 240*z^4 + 15*z^3)*x^4 + (10*z^12 + 35*z^11 - 15*z^10 - 265*z^9 - 325*z^8 + 201*z^7 + 321*z^6 - 180*z^5 + 20*z^4)*x^3 + (26*z^9 + 77*z^8 + 30*z^7 - 72*z^6 + 15*z^5)*x^2 + (-z^9 - 7*z^8 - 12*z^7 + 6*z^6)*x + z^7 */
static const long X1_37_crv_0[10] = {
  evaltyp(t_VECSMALL) | _evallg(10), vZ, 0, 0, 0, 0, 0, 0, 0, 1 }; /* z^7 */
static const long X1_37_crv_1[12] = {
  evaltyp(t_VECSMALL) | _evallg(12), vZ, 0, 0, 0, 0, 0, 0, 6, -12, -7, -1 }; /* -z^9 - 7*z^8 - 12*z^7 + 6*z^6 */
static const long X1_37_crv_2[12] = {
  evaltyp(t_VECSMALL) | _evallg(12), vZ, 0, 0, 0, 0, 0, 15, -72, 30, 77, 26 }; /* 26*z^9 + 77*z^8 + 30*z^7 - 72*z^6 + 15*z^5 */
static const long X1_37_crv_3[15] = {
  evaltyp(t_VECSMALL) | _evallg(15), vZ, 0, 0, 0, 0, 20, -180, 321, 201, -325, -265, -15, 35, 10 }; /* 10*z^12 + 35*z^11 - 15*z^10 - 265*z^9 - 325*z^8 + 201*z^7 + 321*z^6 - 180*z^5 + 20*z^4 */
static const long X1_37_crv_4[17] = {
  evaltyp(t_VECSMALL) | _evallg(17), vZ, 0, 0, 0, 15, -240, 910, -400, -1655, 185, 1350, 555, -180, -210, -60, -5 }; /* -5*z^14 - 60*z^13 - 210*z^12 - 180*z^11 + 555*z^10 + 1350*z^9 + 185*z^8 - 1655*z^7 - 400*z^6 + 910*z^5 - 240*z^4 + 15*z^3 */
static const long X1_37_crv_5[19] = {
  evaltyp(t_VECSMALL) | _evallg(19), vZ, 0, 0, 6, -180, 1275, -2249, -2053, 4495, 3656, -2293, -3469, -891, 678, 564, 166, 22, 1 }; /* z^16 + 22*z^15 + 166*z^14 + 564*z^13 + 678*z^12 - 891*z^11 - 3469*z^10 - 2293*z^9 + 3656*z^8 + 4495*z^7 - 2053*z^6 - 2249*z^5 + 1275*z^4 - 180*z^3 + 6*z^2 */
static const long X1_37_crv_6[20] = {
  evaltyp(t_VECSMALL) | _evallg(20), vZ, 0, 1, -72, 978, -3726, 1372, 9941, -1905, -13100, -4834, 6155, 6267, 1278, -1079, -807, -243, -39, -3 }; /* -3*z^17 - 39*z^16 - 243*z^15 - 807*z^14 - 1079*z^13 + 1278*z^12 + 6267*z^11 + 6155*z^10 - 4834*z^9 - 13100*z^8 - 1905*z^7 + 9941*z^6 + 1372*z^5 - 3726*z^4 + 978*z^3 - 72*z^2 + z */
static const long X1_37_crv_7[21] = {
  evaltyp(t_VECSMALL) | _evallg(21), vZ, 0, -12, 395, -3053, 5741, 7183, -16253, -16256, 12561, 22272, 5183, -9008, -7639, -1585, 789, 595, 180, 32, 3 }; /* 3*z^18 + 32*z^17 + 180*z^16 + 595*z^15 + 789*z^14 - 1585*z^13 - 7639*z^12 - 9008*z^11 + 5183*z^10 + 22272*z^9 + 12561*z^8 - 16256*z^7 - 16253*z^6 + 7183*z^5 + 5741*z^4 - 3053*z^3 + 395*z^2 - 12*z */
static const long X1_37_crv_8[22] = {
  evaltyp(t_VECSMALL) | _evallg(22), vZ, 0, 66, -1264, 5725, -2065, -20366, 2999, 34475, 16281, -20839, -25859, -5435, 7317, 5622, 1311, -162, -172, -52, -10, -1 }; /* -z^19 - 10*z^18 - 52*z^17 - 172*z^16 - 162*z^15 + 1311*z^14 + 5622*z^13 + 7317*z^12 - 5435*z^11 - 25859*z^10 - 20839*z^9 + 16281*z^8 + 34475*z^7 + 2999*z^6 - 20366*z^5 - 2065*z^4 + 5725*z^3 - 1264*z^2 + 66*z */
static const long X1_37_crv_9[21] = {
  evaltyp(t_VECSMALL) | _evallg(21), vZ, 0, -210, 2525, -5975, -8210, 20440, 25005, -16842, -40593, -14660, 18001, 19581, 4715, -2681, -2023, -501, -52, -5, -1 }; /* -z^18 - 5*z^17 - 52*z^16 - 501*z^15 - 2023*z^14 - 2681*z^13 + 4715*z^12 + 19581*z^11 + 18001*z^10 - 14660*z^9 - 40593*z^8 - 16842*z^7 + 25005*z^6 + 20440*z^5 - 8210*z^4 - 5975*z^3 + 2525*z^2 - 210*z */
static const long X1_37_crv_10[19] = {
  evaltyp(t_VECSMALL) | _evallg(19), vZ, 1, 412, -3145, 1991, 14573, -1252, -29776, -20987, 16424, 31592, 12096, -7355, -8129, -2320, 129, 184, 26 }; /* 26*z^16 + 184*z^15 + 129*z^14 - 2320*z^13 - 8129*z^12 - 7355*z^11 + 12096*z^10 + 31592*z^9 + 16424*z^8 - 20987*z^7 - 29776*z^6 - 1252*z^5 + 14573*z^4 + 1991*z^3 - 3145*z^2 + 412*z + 1 */
static const long X1_37_crv_11[18] = {
  evaltyp(t_VECSMALL) | _evallg(18), vZ, -8, -494, 2270, 2488, -8675, -13117, 4413, 23552, 16913, -6010, -14529, -6515, 414, 1210, 363, 35 }; /* 35*z^15 + 363*z^14 + 1210*z^13 + 414*z^12 - 6515*z^11 - 14529*z^10 - 6010*z^9 + 16913*z^8 + 23552*z^7 + 4413*z^6 - 13117*z^5 - 8675*z^4 + 2488*z^3 + 2270*z^2 - 494*z - 8 */
static const long X1_37_crv_12[17] = {
  evaltyp(t_VECSMALL) | _evallg(17), vZ, 28, 322, -733, -2730, -527, 6962, 10483, 664, -11481, -9749, -870, 2579, 1420, 294, 21 }; /* 21*z^14 + 294*z^13 + 1420*z^12 + 2579*z^11 - 870*z^10 - 9749*z^9 - 11481*z^8 + 664*z^7 + 10483*z^6 + 6962*z^5 - 527*z^4 - 2730*z^3 - 733*z^2 + 322*z + 28 */
static const long X1_37_crv_13[16] = {
  evaltyp(t_VECSMALL) | _evallg(16), vZ, -56, -50, 38, 306, 2034, 2372, -2982, -6951, -2931, 2085, 2414, 885, 137, 7 }; /* 7*z^13 + 137*z^12 + 885*z^11 + 2414*z^10 + 2085*z^9 - 2931*z^8 - 6951*z^7 - 2982*z^6 + 2372*z^5 + 2034*z^4 + 306*z^3 + 38*z^2 - 50*z - 56 */
static const long X1_37_crv_14[15] = {
  evaltyp(t_VECSMALL) | _evallg(15), vZ, 70, -65, -205, 635, 530, -1975, -2560, 227, 1944, 1256, 334, 36, 1 }; /* z^12 + 36*z^11 + 334*z^10 + 1256*z^9 + 1944*z^8 + 227*z^7 - 2560*z^6 - 1975*z^5 + 530*z^4 + 635*z^3 - 205*z^2 - 65*z + 70 */
static const long X1_37_crv_15[13] = {
  evaltyp(t_VECSMALL) | _evallg(13), vZ, -56, 18, 299, -71, -878, -460, 697, 899, 390, 70, 4 }; /* 4*z^10 + 70*z^9 + 390*z^8 + 899*z^7 + 697*z^6 - 460*z^5 - 878*z^4 - 71*z^3 + 299*z^2 + 18*z - 56 */
static const long X1_37_crv_16[11] = {
  evaltyp(t_VECSMALL) | _evallg(11), vZ, 28, 28, -123, -186, 86, 318, 227, 64, 6 }; /* 6*z^8 + 64*z^7 + 227*z^6 + 318*z^5 + 86*z^4 - 186*z^3 - 123*z^2 + 28*z + 28 */
static const long X1_37_crv_17[9] = {
  evaltyp(t_VECSMALL) | _evallg(9), vZ, -8, -20, 3, 53, 61, 27, 4 }; /* 4*z^6 + 27*z^5 + 61*z^4 + 53*z^3 + 3*z^2 - 20*z - 8 */
static const long X1_37_crv_18[7] = {
  evaltyp(t_VECSMALL) | _evallg(7), vZ, 1, 4, 6, 4, 1 }; /* z^4 + 4*z^3 + 6*z^2 + 4*z + 1 */
static const long *X1_37_crv[21] = {
  (long *)(evaltyp(t_POL) | _evallg(21)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_37_crv_0, X1_37_crv_1, X1_37_crv_2, X1_37_crv_3, X1_37_crv_4, X1_37_crv_5, X1_37_crv_6, X1_37_crv_7, X1_37_crv_8, X1_37_crv_9, X1_37_crv_10, X1_37_crv_11, X1_37_crv_12, X1_37_crv_13, X1_37_crv_14, X1_37_crv_15, X1_37_crv_16, X1_37_crv_17, X1_37_crv_18
};
/* (z^2 + z + 1)*x - 1 */
static const long X1_37_r_n_1[5] = {
  evaltyp(t_VECSMALL) | _evallg(5), vZ, 1, 1, 1 }; /* z^2 + z + 1 */
static const long *X1_37_r_n[4] = {
  (long *)(evaltyp(t_POL) | _evallg(4)), (long *)(evalvarn(0) | evalsigne(1)),
  FLX_m1, X1_37_r_n_1
};
/* x + (z^2 + z - 1) */
static const long X1_37_r_d_0[5] = {
  evaltyp(t_VECSMALL) | _evallg(5), vZ, -1, 1, 1 }; /* z^2 + z - 1 */
static const long *X1_37_r_d[4] = {
  (long *)(evaltyp(t_POL) | _evallg(4)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_37_r_d_0, FLX_1
};
/* (z + 1)*x - 1 */
static const long X1_37_s_n_1[4] = {
  evaltyp(t_VECSMALL) | _evallg(4), vZ, 1, 1 }; /* z + 1 */
static const long *X1_37_s_n[4] = {
  (long *)(evaltyp(t_POL) | _evallg(4)), (long *)(evalvarn(0) | evalsigne(1)),
  FLX_m1, X1_37_s_n_1
};
/* x + (z - 1) */
static const long X1_37_s_d_0[4] = {
  evaltyp(t_VECSMALL) | _evallg(4), vZ, -1, 1 }; /* z - 1 */
static const long *X1_37_s_d[4] = {
  (long *)(evaltyp(t_POL) | _evallg(4)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_37_s_d_0, FLX_1
};
/* z^3*u^12 + (z^6 + 4*z^4 + 10*z^3 - z^2 + z)*u^11 + (4*z^7 + 10*z^6 + 2*z^5 + 39*z^4 + 41*z^3 - 5*z^2 + 7*z - 1)*u^10 + (z^9 + 4*z^8 + 38*z^7 + 32*z^6 + 26*z^5 + 167*z^4 + 88*z^3 - 10*z^2 + 17*z - 6)*u^9 + (4*z^10 + 3*z^9 + 39*z^8 + 141*z^7 + 28*z^6 + 144*z^5 + 396*z^4 + 94*z^3 - 18*z^2 + 12*z - 15)*u^8 + (6*z^11 + 14*z^10 + 173*z^8 + 234*z^7 - 44*z^6 + 421*z^5 + 545*z^4 - 4*z^3 - 50*z^2 - 17*z - 20)*u^7 + (4*z^12 + 25*z^11 - z^10 + 41*z^9 + 368*z^8 + 91*z^7 - 39*z^6 + 691*z^5 + 383*z^4 - 168*z^3 - 91*z^2 - 38*z - 15)*u^6 + (z^13 + 17*z^12 + 30*z^11 - 33*z^10 + 171*z^9 + 326*z^8 - 163*z^7 + 166*z^6 + 594*z^5 + 24*z^4 - 236*z^3 - 82*z^2 - 28*z - 6)*u^5 + (4*z^13 + 26*z^12 + 4*z^11 - 7*z^10 + 202*z^9 + 61*z^8 - 135*z^7 + 249*z^6 + 210*z^5 - 153*z^4 - 146*z^3 - 34*z^2 - 9*z - 1)*u^4 + (6*z^13 + 17*z^12 - 10*z^11 + 27*z^10 + 78*z^9 - 34*z^8 - 10*z^7 + 107*z^6 - 17*z^5 - 90*z^4 - 39*z^3 - 5*z^2 - z)*u^3 + (4*z^13 + 4*z^12 - 3*z^11 + 12*z^10 + 10*z^9 - 9*z^8 + 6*z^7 + 6*z^6 - 25*z^5 - 15*z^4 - 3*z^3)*u^2 + (z^13 + z^10 + z^9 - 3*z^7 - 3*z^6 - 3*z^5)*u - z^7 */
static const long X1_38_crv_0[10] = {
  evaltyp(t_VECSMALL) | _evallg(10), vZ, 0, 0, 0, 0, 0, 0, 0, -1 }; /* -z^7 */
static const long X1_38_crv_1[16] = {
  evaltyp(t_VECSMALL) | _evallg(16), vZ, 0, 0, 0, 0, 0, -3, -3, -3, 0, 1, 1, 0, 0, 1 }; /* z^13 + z^10 + z^9 - 3*z^7 - 3*z^6 - 3*z^5 */
static const long X1_38_crv_2[16] = {
  evaltyp(t_VECSMALL) | _evallg(16), vZ, 0, 0, 0, -3, -15, -25, 6, 6, -9, 10, 12, -3, 4, 4 }; /* 4*z^13 + 4*z^12 - 3*z^11 + 12*z^10 + 10*z^9 - 9*z^8 + 6*z^7 + 6*z^6 - 25*z^5 - 15*z^4 - 3*z^3 */
static const long X1_38_crv_3[16] = {
  evaltyp(t_VECSMALL) | _evallg(16), vZ, 0, -1, -5, -39, -90, -17, 107, -10, -34, 78, 27, -10, 17, 6 }; /* 6*z^13 + 17*z^12 - 10*z^11 + 27*z^10 + 78*z^9 - 34*z^8 - 10*z^7 + 107*z^6 - 17*z^5 - 90*z^4 - 39*z^3 - 5*z^2 - z */
static const long X1_38_crv_4[16] = {
  evaltyp(t_VECSMALL) | _evallg(16), vZ, -1, -9, -34, -146, -153, 210, 249, -135, 61, 202, -7, 4, 26, 4 }; /* 4*z^13 + 26*z^12 + 4*z^11 - 7*z^10 + 202*z^9 + 61*z^8 - 135*z^7 + 249*z^6 + 210*z^5 - 153*z^4 - 146*z^3 - 34*z^2 - 9*z - 1 */
static const long X1_38_crv_5[16] = {
  evaltyp(t_VECSMALL) | _evallg(16), vZ, -6, -28, -82, -236, 24, 594, 166, -163, 326, 171, -33, 30, 17, 1 }; /* z^13 + 17*z^12 + 30*z^11 - 33*z^10 + 171*z^9 + 326*z^8 - 163*z^7 + 166*z^6 + 594*z^5 + 24*z^4 - 236*z^3 - 82*z^2 - 28*z - 6 */
static const long X1_38_crv_6[15] = {
  evaltyp(t_VECSMALL) | _evallg(15), vZ, -15, -38, -91, -168, 383, 691, -39, 91, 368, 41, -1, 25, 4 }; /* 4*z^12 + 25*z^11 - z^10 + 41*z^9 + 368*z^8 + 91*z^7 - 39*z^6 + 691*z^5 + 383*z^4 - 168*z^3 - 91*z^2 - 38*z - 15 */
static const long X1_38_crv_7[14] = {
  evaltyp(t_VECSMALL) | _evallg(14), vZ, -20, -17, -50, -4, 545, 421, -44, 234, 173, 0, 14, 6 }; /* 6*z^11 + 14*z^10 + 173*z^8 + 234*z^7 - 44*z^6 + 421*z^5 + 545*z^4 - 4*z^3 - 50*z^2 - 17*z - 20 */
static const long X1_38_crv_8[13] = {
  evaltyp(t_VECSMALL) | _evallg(13), vZ, -15, 12, -18, 94, 396, 144, 28, 141, 39, 3, 4 }; /* 4*z^10 + 3*z^9 + 39*z^8 + 141*z^7 + 28*z^6 + 144*z^5 + 396*z^4 + 94*z^3 - 18*z^2 + 12*z - 15 */
static const long X1_38_crv_9[12] = {
  evaltyp(t_VECSMALL) | _evallg(12), vZ, -6, 17, -10, 88, 167, 26, 32, 38, 4, 1 }; /* z^9 + 4*z^8 + 38*z^7 + 32*z^6 + 26*z^5 + 167*z^4 + 88*z^3 - 10*z^2 + 17*z - 6 */
static const long X1_38_crv_10[10] = {
  evaltyp(t_VECSMALL) | _evallg(10), vZ, -1, 7, -5, 41, 39, 2, 10, 4 }; /* 4*z^7 + 10*z^6 + 2*z^5 + 39*z^4 + 41*z^3 - 5*z^2 + 7*z - 1 */
static const long X1_38_crv_11[9] = {
  evaltyp(t_VECSMALL) | _evallg(9), vZ, 0, 1, -1, 10, 4, 0, 1 }; /* z^6 + 4*z^4 + 10*z^3 - z^2 + z */
static const long X1_38_crv_12[6] = {
  evaltyp(t_VECSMALL) | _evallg(6), vZ, 0, 0, 0, 1 }; /* z^3 */
static const long *X1_38_crv[15] = {
  (long *)(evaltyp(t_POL) | _evallg(15)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_38_crv_0, X1_38_crv_1, X1_38_crv_2, X1_38_crv_3, X1_38_crv_4, X1_38_crv_5, X1_38_crv_6, X1_38_crv_7, X1_38_crv_8, X1_38_crv_9, X1_38_crv_10, X1_38_crv_11, X1_38_crv_12
};
/* (z^3 - z^2)*u^10 + (z^5 + 4*z^4 + 2*z^3 - 8*z^2 + 2*z)*u^9 + (6*z^6 + 10*z^5 + 14*z^4 - 13*z^3 - 17*z^2 + 9*z - 1)*u^8 + (15*z^7 + 25*z^6 + 22*z^5 + 10*z^4 - 45*z^3 - 11*z^2 + 13*z - 2)*u^7 + (21*z^8 + 46*z^7 + 21*z^6 + 33*z^5 - 20*z^4 - 63*z^3 + 5*z^2 + 12*z - 1)*u^6 + (17*z^9 + 58*z^8 + 14*z^7 + 25*z^6 + 39*z^5 - 67*z^4 - 42*z^3 + 21*z^2 + 10*z)*u^5 + (7*z^10 + 45*z^9 + 24*z^8 - 27*z^7 + 75*z^6 - 9*z^5 - 71*z^4 + 23*z^2 + 4*z)*u^4 + (z^11 + 17*z^10 + 30*z^9 - 32*z^8 + 9*z^7 + 68*z^6 - 49*z^5 - 32*z^4 + 17*z^3 + 8*z^2)*u^3 + (2*z^11 + 12*z^10 - 2*z^9 - 24*z^8 + 33*z^7 + 16*z^6 - 38*z^5 - z^4 + 6*z^3)*u^2 + (z^11 + 2*z^10 - 6*z^9 - z^8 + 13*z^7 - 6*z^6 - 9*z^5 + 2*z^4)*u + (-z^9 + z^8 + z^7 - 2*z^6) */
static const long X1_38_r_n_0[12] = {
  evaltyp(t_VECSMALL) | _evallg(12), vZ, 0, 0, 0, 0, 0, 0, -2, 1, 1, -1 }; /* -z^9 + z^8 + z^7 - 2*z^6 */
static const long X1_38_r_n_1[14] = {
  evaltyp(t_VECSMALL) | _evallg(14), vZ, 0, 0, 0, 0, 2, -9, -6, 13, -1, -6, 2, 1 }; /* z^11 + 2*z^10 - 6*z^9 - z^8 + 13*z^7 - 6*z^6 - 9*z^5 + 2*z^4 */
static const long X1_38_r_n_2[14] = {
  evaltyp(t_VECSMALL) | _evallg(14), vZ, 0, 0, 0, 6, -1, -38, 16, 33, -24, -2, 12, 2 }; /* 2*z^11 + 12*z^10 - 2*z^9 - 24*z^8 + 33*z^7 + 16*z^6 - 38*z^5 - z^4 + 6*z^3 */
static const long X1_38_r_n_3[14] = {
  evaltyp(t_VECSMALL) | _evallg(14), vZ, 0, 0, 8, 17, -32, -49, 68, 9, -32, 30, 17, 1 }; /* z^11 + 17*z^10 + 30*z^9 - 32*z^8 + 9*z^7 + 68*z^6 - 49*z^5 - 32*z^4 + 17*z^3 + 8*z^2 */
static const long X1_38_r_n_4[13] = {
  evaltyp(t_VECSMALL) | _evallg(13), vZ, 0, 4, 23, 0, -71, -9, 75, -27, 24, 45, 7 }; /* 7*z^10 + 45*z^9 + 24*z^8 - 27*z^7 + 75*z^6 - 9*z^5 - 71*z^4 + 23*z^2 + 4*z */
static const long X1_38_r_n_5[12] = {
  evaltyp(t_VECSMALL) | _evallg(12), vZ, 0, 10, 21, -42, -67, 39, 25, 14, 58, 17 }; /* 17*z^9 + 58*z^8 + 14*z^7 + 25*z^6 + 39*z^5 - 67*z^4 - 42*z^3 + 21*z^2 + 10*z */
static const long X1_38_r_n_6[11] = {
  evaltyp(t_VECSMALL) | _evallg(11), vZ, -1, 12, 5, -63, -20, 33, 21, 46, 21 }; /* 21*z^8 + 46*z^7 + 21*z^6 + 33*z^5 - 20*z^4 - 63*z^3 + 5*z^2 + 12*z - 1 */
static const long X1_38_r_n_7[10] = {
  evaltyp(t_VECSMALL) | _evallg(10), vZ, -2, 13, -11, -45, 10, 22, 25, 15 }; /* 15*z^7 + 25*z^6 + 22*z^5 + 10*z^4 - 45*z^3 - 11*z^2 + 13*z - 2 */
static const long X1_38_r_n_8[9] = {
  evaltyp(t_VECSMALL) | _evallg(9), vZ, -1, 9, -17, -13, 14, 10, 6 }; /* 6*z^6 + 10*z^5 + 14*z^4 - 13*z^3 - 17*z^2 + 9*z - 1 */
static const long X1_38_r_n_9[8] = {
  evaltyp(t_VECSMALL) | _evallg(8), vZ, 0, 2, -8, 2, 4, 1 }; /* z^5 + 4*z^4 + 2*z^3 - 8*z^2 + 2*z */
static const long X1_38_r_n_10[6] = {
  evaltyp(t_VECSMALL) | _evallg(6), vZ, 0, 0, -1, 1 }; /* z^3 - z^2 */
static const long *X1_38_r_n[13] = {
  (long *)(evaltyp(t_POL) | _evallg(13)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_38_r_n_0, X1_38_r_n_1, X1_38_r_n_2, X1_38_r_n_3, X1_38_r_n_4, X1_38_r_n_5, X1_38_r_n_6, X1_38_r_n_7, X1_38_r_n_8, X1_38_r_n_9, X1_38_r_n_10
};
/* (z^3 - z^2)*u^10 + (z^5 + 5*z^4 + z^3 - 8*z^2 + 2*z)*u^9 + (7*z^6 + 12*z^5 + 17*z^4 - 20*z^3 - 15*z^2 + 9*z - 1)*u^8 + (19*z^7 + 28*z^6 + 30*z^5 + 10*z^4 - 61*z^3 - 3*z^2 + 13*z - 2)*u^7 + (26*z^8 + 58*z^7 + 19*z^6 + 54*z^5 - 32*z^4 - 82*z^3 + 20*z^2 + 12*z - 1)*u^6 + (19*z^9 + 74*z^8 + 21*z^7 + 16*z^6 + 75*z^5 - 93*z^4 - 53*z^3 + 36*z^2 + 10*z)*u^5 + (7*z^10 + 51*z^9 + 43*z^8 - 41*z^7 + 72*z^6 + 35*z^5 - 106*z^4 - 2*z^3 + 31*z^2 + 4*z)*u^4 + (z^11 + 17*z^10 + 37*z^9 - 26*z^8 - 14*z^7 + 90*z^6 - 33*z^5 - 59*z^4 + 19*z^3 + 10*z^2)*u^3 + (2*z^11 + 12*z^10 + z^9 - 29*z^8 + 31*z^7 + 27*z^6 - 41*z^5 - 10*z^4 + 8*z^3)*u^2 + (z^11 + 2*z^10 - 6*z^9 - 2*z^8 + 14*z^7 - 5*z^6 - 11*z^5 + 2*z^4)*u + (-z^9 + z^8 + z^7 - 2*z^6) */
static const long X1_38_r_d_0[12] = {
  evaltyp(t_VECSMALL) | _evallg(12), vZ, 0, 0, 0, 0, 0, 0, -2, 1, 1, -1 }; /* -z^9 + z^8 + z^7 - 2*z^6 */
static const long X1_38_r_d_1[14] = {
  evaltyp(t_VECSMALL) | _evallg(14), vZ, 0, 0, 0, 0, 2, -11, -5, 14, -2, -6, 2, 1 }; /* z^11 + 2*z^10 - 6*z^9 - 2*z^8 + 14*z^7 - 5*z^6 - 11*z^5 + 2*z^4 */
static const long X1_38_r_d_2[14] = {
  evaltyp(t_VECSMALL) | _evallg(14), vZ, 0, 0, 0, 8, -10, -41, 27, 31, -29, 1, 12, 2 }; /* 2*z^11 + 12*z^10 + z^9 - 29*z^8 + 31*z^7 + 27*z^6 - 41*z^5 - 10*z^4 + 8*z^3 */
static const long X1_38_r_d_3[14] = {
  evaltyp(t_VECSMALL) | _evallg(14), vZ, 0, 0, 10, 19, -59, -33, 90, -14, -26, 37, 17, 1 }; /* z^11 + 17*z^10 + 37*z^9 - 26*z^8 - 14*z^7 + 90*z^6 - 33*z^5 - 59*z^4 + 19*z^3 + 10*z^2 */
static const long X1_38_r_d_4[13] = {
  evaltyp(t_VECSMALL) | _evallg(13), vZ, 0, 4, 31, -2, -106, 35, 72, -41, 43, 51, 7 }; /* 7*z^10 + 51*z^9 + 43*z^8 - 41*z^7 + 72*z^6 + 35*z^5 - 106*z^4 - 2*z^3 + 31*z^2 + 4*z */
static const long X1_38_r_d_5[12] = {
  evaltyp(t_VECSMALL) | _evallg(12), vZ, 0, 10, 36, -53, -93, 75, 16, 21, 74, 19 }; /* 19*z^9 + 74*z^8 + 21*z^7 + 16*z^6 + 75*z^5 - 93*z^4 - 53*z^3 + 36*z^2 + 10*z */
static const long X1_38_r_d_6[11] = {
  evaltyp(t_VECSMALL) | _evallg(11), vZ, -1, 12, 20, -82, -32, 54, 19, 58, 26 }; /* 26*z^8 + 58*z^7 + 19*z^6 + 54*z^5 - 32*z^4 - 82*z^3 + 20*z^2 + 12*z - 1 */
static const long X1_38_r_d_7[10] = {
  evaltyp(t_VECSMALL) | _evallg(10), vZ, -2, 13, -3, -61, 10, 30, 28, 19 }; /* 19*z^7 + 28*z^6 + 30*z^5 + 10*z^4 - 61*z^3 - 3*z^2 + 13*z - 2 */
static const long X1_38_r_d_8[9] = {
  evaltyp(t_VECSMALL) | _evallg(9), vZ, -1, 9, -15, -20, 17, 12, 7 }; /* 7*z^6 + 12*z^5 + 17*z^4 - 20*z^3 - 15*z^2 + 9*z - 1 */
static const long X1_38_r_d_9[8] = {
  evaltyp(t_VECSMALL) | _evallg(8), vZ, 0, 2, -8, 1, 5, 1 }; /* z^5 + 5*z^4 + z^3 - 8*z^2 + 2*z */
static const long X1_38_r_d_10[6] = {
  evaltyp(t_VECSMALL) | _evallg(6), vZ, 0, 0, -1, 1 }; /* z^3 - z^2 */
static const long *X1_38_r_d[13] = {
  (long *)(evaltyp(t_POL) | _evallg(13)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_38_r_d_0, X1_38_r_d_1, X1_38_r_d_2, X1_38_r_d_3, X1_38_r_d_4, X1_38_r_d_5, X1_38_r_d_6, X1_38_r_d_7, X1_38_r_d_8, X1_38_r_d_9, X1_38_r_d_10
};
/* (z^3 - z^2)*u^9 + (z^5 + 3*z^4 + 3*z^3 - 8*z^2 + 2*z)*u^8 + (5*z^6 + 7*z^5 + 12*z^4 - 6*z^3 - 19*z^2 + 9*z - 1)*u^7 + (10*z^7 + 20*z^6 + 11*z^5 + 17*z^4 - 31*z^3 - 19*z^2 + 13*z - 2)*u^6 + (12*z^8 + 31*z^7 + 15*z^6 + 12*z^5 + 8*z^4 - 52*z^3 - 10*z^2 + 12*z - 1)*u^5 + (10*z^9 + 30*z^8 + 9*z^7 + 13*z^6 + 15*z^5 - 22*z^4 - 46*z^3 + 6*z^2 + 10*z)*u^4 + (5*z^10 + 23*z^9 - 2*z^8 - 4*z^7 + 42*z^6 - 27*z^5 - 25*z^4 - 13*z^3 + 15*z^2 + 4*z)*u^3 + (z^11 + 11*z^10 + 4*z^9 - 24*z^8 + 35*z^7 + 2*z^6 - 30*z^5 - 3*z^4 + 7*z^3 + 6*z^2)*u^2 + (2*z^11 + 5*z^10 - 11*z^9 + 4*z^8 + 13*z^7 - 11*z^6 - 8*z^5 + 6*z^4 + 2*z^3)*u + (z^11 - z^10 - z^9 + 2*z^8 + z^7 - 4*z^6 + 2*z^5) */
static const long X1_38_s_n_0[14] = {
  evaltyp(t_VECSMALL) | _evallg(14), vZ, 0, 0, 0, 0, 0, 2, -4, 1, 2, -1, -1, 1 }; /* z^11 - z^10 - z^9 + 2*z^8 + z^7 - 4*z^6 + 2*z^5 */
static const long X1_38_s_n_1[14] = {
  evaltyp(t_VECSMALL) | _evallg(14), vZ, 0, 0, 0, 2, 6, -8, -11, 13, 4, -11, 5, 2 }; /* 2*z^11 + 5*z^10 - 11*z^9 + 4*z^8 + 13*z^7 - 11*z^6 - 8*z^5 + 6*z^4 + 2*z^3 */
static const long X1_38_s_n_2[14] = {
  evaltyp(t_VECSMALL) | _evallg(14), vZ, 0, 0, 6, 7, -3, -30, 2, 35, -24, 4, 11, 1 }; /* z^11 + 11*z^10 + 4*z^9 - 24*z^8 + 35*z^7 + 2*z^6 - 30*z^5 - 3*z^4 + 7*z^3 + 6*z^2 */
static const long X1_38_s_n_3[13] = {
  evaltyp(t_VECSMALL) | _evallg(13), vZ, 0, 4, 15, -13, -25, -27, 42, -4, -2, 23, 5 }; /* 5*z^10 + 23*z^9 - 2*z^8 - 4*z^7 + 42*z^6 - 27*z^5 - 25*z^4 - 13*z^3 + 15*z^2 + 4*z */
static const long X1_38_s_n_4[12] = {
  evaltyp(t_VECSMALL) | _evallg(12), vZ, 0, 10, 6, -46, -22, 15, 13, 9, 30, 10 }; /* 10*z^9 + 30*z^8 + 9*z^7 + 13*z^6 + 15*z^5 - 22*z^4 - 46*z^3 + 6*z^2 + 10*z */
static const long X1_38_s_n_5[11] = {
  evaltyp(t_VECSMALL) | _evallg(11), vZ, -1, 12, -10, -52, 8, 12, 15, 31, 12 }; /* 12*z^8 + 31*z^7 + 15*z^6 + 12*z^5 + 8*z^4 - 52*z^3 - 10*z^2 + 12*z - 1 */
static const long X1_38_s_n_6[10] = {
  evaltyp(t_VECSMALL) | _evallg(10), vZ, -2, 13, -19, -31, 17, 11, 20, 10 }; /* 10*z^7 + 20*z^6 + 11*z^5 + 17*z^4 - 31*z^3 - 19*z^2 + 13*z - 2 */
static const long X1_38_s_n_7[9] = {
  evaltyp(t_VECSMALL) | _evallg(9), vZ, -1, 9, -19, -6, 12, 7, 5 }; /* 5*z^6 + 7*z^5 + 12*z^4 - 6*z^3 - 19*z^2 + 9*z - 1 */
static const long X1_38_s_n_8[8] = {
  evaltyp(t_VECSMALL) | _evallg(8), vZ, 0, 2, -8, 3, 3, 1 }; /* z^5 + 3*z^4 + 3*z^3 - 8*z^2 + 2*z */
static const long X1_38_s_n_9[6] = {
  evaltyp(t_VECSMALL) | _evallg(6), vZ, 0, 0, -1, 1 }; /* z^3 - z^2 */
static const long *X1_38_s_n[12] = {
  (long *)(evaltyp(t_POL) | _evallg(12)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_38_s_n_0, X1_38_s_n_1, X1_38_s_n_2, X1_38_s_n_3, X1_38_s_n_4, X1_38_s_n_5, X1_38_s_n_6, X1_38_s_n_7, X1_38_s_n_8, X1_38_s_n_9
};
/* (z^3 - z^2)*u^9 + (z^5 + 4*z^4 + 2*z^3 - 8*z^2 + 2*z)*u^8 + (6*z^6 + 9*z^5 + 15*z^4 - 13*z^3 - 17*z^2 + 9*z - 1)*u^7 + (14*z^7 + 23*z^6 + 19*z^5 + 17*z^4 - 47*z^3 - 11*z^2 + 13*z - 2)*u^6 + (17*z^8 + 43*z^7 + 13*z^6 + 33*z^5 - 4*z^4 - 71*z^3 + 5*z^2 + 12*z - 1)*u^5 + (12*z^9 + 46*z^8 + 16*z^7 + 4*z^6 + 51*z^5 - 48*z^4 - 57*z^3 + 21*z^2 + 10*z)*u^4 + (5*z^10 + 29*z^9 + 17*z^8 - 18*z^7 + 39*z^6 + 17*z^5 - 60*z^4 - 15*z^3 + 23*z^2 + 4*z)*u^3 + (z^11 + 11*z^10 + 11*z^9 - 18*z^8 + 12*z^7 + 24*z^6 - 14*z^5 - 30*z^4 + 9*z^3 + 8*z^2)*u^2 + (2*z^11 + 5*z^10 - 8*z^9 - z^8 + 11*z^7 - 11*z^5 - 3*z^4 + 4*z^3)*u + (z^11 - z^10 - z^9 + z^8 + 2*z^7 - 3*z^6) */
static const long X1_38_s_d_0[14] = {
  evaltyp(t_VECSMALL) | _evallg(14), vZ, 0, 0, 0, 0, 0, 0, -3, 2, 1, -1, -1, 1 }; /* z^11 - z^10 - z^9 + z^8 + 2*z^7 - 3*z^6 */
static const long X1_38_s_d_1[14] = {
  evaltyp(t_VECSMALL) | _evallg(14), vZ, 0, 0, 0, 4, -3, -11, 0, 11, -1, -8, 5, 2 }; /* 2*z^11 + 5*z^10 - 8*z^9 - z^8 + 11*z^7 - 11*z^5 - 3*z^4 + 4*z^3 */
static const long X1_38_s_d_2[14] = {
  evaltyp(t_VECSMALL) | _evallg(14), vZ, 0, 0, 8, 9, -30, -14, 24, 12, -18, 11, 11, 1 }; /* z^11 + 11*z^10 + 11*z^9 - 18*z^8 + 12*z^7 + 24*z^6 - 14*z^5 - 30*z^4 + 9*z^3 + 8*z^2 */
static const long X1_38_s_d_3[13] = {
  evaltyp(t_VECSMALL) | _evallg(13), vZ, 0, 4, 23, -15, -60, 17, 39, -18, 17, 29, 5 }; /* 5*z^10 + 29*z^9 + 17*z^8 - 18*z^7 + 39*z^6 + 17*z^5 - 60*z^4 - 15*z^3 + 23*z^2 + 4*z */
static const long X1_38_s_d_4[12] = {
  evaltyp(t_VECSMALL) | _evallg(12), vZ, 0, 10, 21, -57, -48, 51, 4, 16, 46, 12 }; /* 12*z^9 + 46*z^8 + 16*z^7 + 4*z^6 + 51*z^5 - 48*z^4 - 57*z^3 + 21*z^2 + 10*z */
static const long X1_38_s_d_5[11] = {
  evaltyp(t_VECSMALL) | _evallg(11), vZ, -1, 12, 5, -71, -4, 33, 13, 43, 17 }; /* 17*z^8 + 43*z^7 + 13*z^6 + 33*z^5 - 4*z^4 - 71*z^3 + 5*z^2 + 12*z - 1 */
static const long X1_38_s_d_6[10] = {
  evaltyp(t_VECSMALL) | _evallg(10), vZ, -2, 13, -11, -47, 17, 19, 23, 14 }; /* 14*z^7 + 23*z^6 + 19*z^5 + 17*z^4 - 47*z^3 - 11*z^2 + 13*z - 2 */
static const long X1_38_s_d_7[9] = {
  evaltyp(t_VECSMALL) | _evallg(9), vZ, -1, 9, -17, -13, 15, 9, 6 }; /* 6*z^6 + 9*z^5 + 15*z^4 - 13*z^3 - 17*z^2 + 9*z - 1 */
static const long X1_38_s_d_8[8] = {
  evaltyp(t_VECSMALL) | _evallg(8), vZ, 0, 2, -8, 2, 4, 1 }; /* z^5 + 4*z^4 + 2*z^3 - 8*z^2 + 2*z */
static const long X1_38_s_d_9[6] = {
  evaltyp(t_VECSMALL) | _evallg(6), vZ, 0, 0, -1, 1 }; /* z^3 - z^2 */
static const long *X1_38_s_d[12] = {
  (long *)(evaltyp(t_POL) | _evallg(12)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_38_s_d_0, X1_38_s_d_1, X1_38_s_d_2, X1_38_s_d_3, X1_38_s_d_4, X1_38_s_d_5, X1_38_s_d_6, X1_38_s_d_7, X1_38_s_d_8, X1_38_s_d_9
};
/* z^12*x^14 + (-z^23 - 2*z^22 - 4*z^21 - 6*z^20 - 9*z^19 - 12*z^18 - 16*z^17 - 20*z^16 - 25*z^15 - 30*z^14 - 36*z^13 - 12*z^12)*x^13 + (-18*z^23 - 52*z^22 - 100*z^21 - 147*z^20 - 187*z^19 - 208*z^18 - 216*z^17 - 218*z^16 - 248*z^15 - 348*z^14 - 596*z^13 - 650*z^12 - 483*z^11 - 308*z^10 - 188*z^9 - 108*z^8 - 58*z^7 - 28*z^6 - 12*z^5 - 4*z^4 - z^3)*x^12 + (-153*z^23 - 594*z^22 - 1300*z^21 - 2055*z^20 - 2574*z^19 - 2556*z^18 - 1806*z^17 - 261*z^16 + 1845*z^15 + 3786*z^14 + 3780*z^13 + 2178*z^12 + 849*z^11 + 360*z^10 + 266*z^9 + 243*z^8 + 192*z^7 + 124*z^6 + 60*z^5 + 21*z^4 + 3*z^3)*x^11 + (-816*z^23 - 4080*z^22 - 10860*z^21 - 20535*z^20 - 31080*z^19 - 39972*z^18 - 44924*z^17 - 43894*z^16 - 34940*z^15 - 17560*z^14 + 268*z^13 + 8717*z^12 + 7806*z^11 + 3780*z^10 + 720*z^9 - 616*z^8 - 818*z^7 - 544*z^6 - 240*z^5 - 60*z^4 - 6*z^3)*x^10 + (z^28 + 10*z^27 + 60*z^26 + 270*z^25 + 1005*z^24 + 192*z^23 - 9736*z^22 - 38140*z^21 - 87840*z^20 - 151485*z^19 - 216012*z^18 - 269898*z^17 - 306131*z^16 - 316700*z^15 - 284760*z^14 - 207128*z^13 - 114251*z^12 - 43146*z^11 - 5820*z^10 + 6900*z^9 + 7806*z^8 + 5035*z^7 + 2314*z^6 + 720*z^5 + 130*z^4 + 10*z^3)*x^9 + (9*z^28 + 91*z^27 + 540*z^26 + 2400*z^25 + 8890*z^24 + 20526*z^23 + 21288*z^22 - 23112*z^21 - 140013*z^20 - 320022*z^19 - 516680*z^18 - 678672*z^17 - 787386*z^16 - 859748*z^15 - 893172*z^14 - 842244*z^13 - 686088*z^12 - 474318*z^11 - 280656*z^10 - 144524*z^9 - 65124*z^8 - 25122*z^7 - 7784*z^6 - 1740*z^5 - 240*z^4 - 15*z^3)*x^8 + (36*z^28 + 369*z^27 + 2164*z^26 + 9452*z^25 + 34678*z^24 + 96449*z^23 + 188602*z^22 + 245336*z^21 + 166136*z^20 - 94892*z^19 - 461620*z^18 - 768278*z^17 - 883369*z^16 - 829121*z^15 - 743626*z^14 - 706388*z^13 - 669214*z^12 - 565402*z^11 - 404852*z^10 - 245998*z^9 - 129905*z^8 - 61105*z^7 - 25634*z^6 - 9268*z^5 - 2744*z^4 - 637*z^3 - 112*z^2 - 14*z - 1)*x^7 + (84*z^28 + 876*z^27 + 5076*z^26 + 21640*z^25 + 77944*z^24 + 230394*z^23 + 528492*z^22 + 922068*z^21 + 1213200*z^20 + 1162575*z^19 + 693252*z^18 + 6228*z^17 - 521846*z^16 - 626120*z^15 - 375720*z^14 - 68172*z^13 + 79677*z^12 + 72513*z^11 + 20760*z^10 - 6456*z^9 - 7416*z^8 - 1916*z^7 + 496*z^6 + 480*z^5 + 135*z^4 + 15*z^3)*x^6 + (126*z^28 + 1344*z^27 + 7704*z^26 + 31770*z^25 + 110495*z^24 + 332211*z^23 + 826386*z^22 + 1650292*z^21 + 2628990*z^20 + 3341835*z^19 + 3353964*z^18 + 2539962*z^17 + 1236231*z^16 + 55910*z^15 - 540060*z^14 - 540912*z^13 - 271552*z^12 - 44343*z^11 + 39780*z^10 + 34350*z^9 + 11565*z^8 + 333*z^7 - 1366*z^6 - 600*z^5 - 120*z^4 - 10*z^3)*x^5 + (126*z^28 + 1386*z^27 + 7896*z^26 + 31200*z^25 + 101730*z^24 + 297098*z^23 + 765412*z^22 + 1667408*z^21 + 3004995*z^20 + 4469310*z^19 + 5505000*z^18 + 5608136*z^17 + 4657354*z^16 + 3031220*z^15 + 1391660*z^14 + 270580*z^13 - 204565*z^12 - 244602*z^11 - 134160*z^10 - 41460*z^9 - 2842*z^8 + 4030*z^7 + 2216*z^6 + 600*z^5 + 90*z^4 + 6*z^3)*x^4 + (84*z^28 + 966*z^27 + 5544*z^26 + 21000*z^25 + 61860*z^24 + 161856*z^23 + 398596*z^22 + 897424*z^21 + 1758603*z^20 + 2925262*z^19 + 4115740*z^18 + 4919796*z^17 + 5012510*z^16 + 4342211*z^15 + 3166854*z^14 + 1907052*z^13 + 913956*z^12 + 320100*z^11 + 58652*z^10 - 14782*z^9 - 17649*z^8 - 8090*z^7 - 2360*z^6 - 456*z^5 - 54*z^4 - 3*z^3)*x^3 + (36*z^28 + 443*z^27 + 2640*z^26 + 9912*z^25 + 26488*z^24 + 56208*z^23 + 108084*z^22 + 209364*z^21 + 405039*z^20 + 723204*z^19 + 1128252*z^18 + 1513356*z^17 + 1749258*z^16 + 1752384*z^15 + 1525872*z^14 + 1153404*z^13 + 753402*z^12 + 422268*z^11 + 201168*z^10 + 80432*z^9 + 26520*z^8 + 7032*z^7 + 1444*z^6 + 216*z^5 + 21*z^4 + z^3)*x^2 + (9*z^28 + 123*z^27 + 800*z^26 + 3220*z^25 + 8834*z^24 + 17206*z^23 + 23900*z^22 + 22600*z^21 + 11580*z^20 - 2916*z^19 - 12024*z^18 - 12470*z^17 - 7885*z^16 - 3335*z^15 - 930*z^14 - 156*z^13 - 12*z^12)*x + (z^28 + 16*z^27 + 120*z^26 + 560*z^25 + 1820*z^24 + 4368*z^23 + 8008*z^22 + 11440*z^21 + 12870*z^20 + 11440*z^19 + 8008*z^18 + 4368*z^17 + 1820*z^16 + 560*z^15 + 120*z^14 + 16*z^13 + z^12) */
static const long X1_39_crv_0[31] = {
  evaltyp(t_VECSMALL) | _evallg(31), vZ, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 16, 120, 560, 1820, 4368, 8008, 11440, 12870, 11440, 8008, 4368, 1820, 560, 120, 16, 1 }; /* z^28 + 16*z^27 + 120*z^26 + 560*z^25 + 1820*z^24 + 4368*z^23 + 8008*z^22 + 11440*z^21 + 12870*z^20 + 11440*z^19 + 8008*z^18 + 4368*z^17 + 1820*z^16 + 560*z^15 + 120*z^14 + 16*z^13 + z^12 */
static const long X1_39_crv_1[31] = {
  evaltyp(t_VECSMALL) | _evallg(31), vZ, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -12, -156, -930, -3335, -7885, -12470, -12024, -2916, 11580, 22600, 23900, 17206, 8834, 3220, 800, 123, 9 }; /* 9*z^28 + 123*z^27 + 800*z^26 + 3220*z^25 + 8834*z^24 + 17206*z^23 + 23900*z^22 + 22600*z^21 + 11580*z^20 - 2916*z^19 - 12024*z^18 - 12470*z^17 - 7885*z^16 - 3335*z^15 - 930*z^14 - 156*z^13 - 12*z^12 */
static const long X1_39_crv_2[31] = {
  evaltyp(t_VECSMALL) | _evallg(31), vZ, 0, 0, 0, 1, 21, 216, 1444, 7032, 26520, 80432, 201168, 422268, 753402, 1153404, 1525872, 1752384, 1749258, 1513356, 1128252, 723204, 405039, 209364, 108084, 56208, 26488, 9912, 2640, 443, 36 }; /* 36*z^28 + 443*z^27 + 2640*z^26 + 9912*z^25 + 26488*z^24 + 56208*z^23 + 108084*z^22 + 209364*z^21 + 405039*z^20 + 723204*z^19 + 1128252*z^18 + 1513356*z^17 + 1749258*z^16 + 1752384*z^15 + 1525872*z^14 + 1153404*z^13 + 753402*z^12 + 422268*z^11 + 201168*z^10 + 80432*z^9 + 26520*z^8 + 7032*z^7 + 1444*z^6 + 216*z^5 + 21*z^4 + z^3 */
static const long X1_39_crv_3[31] = {
  evaltyp(t_VECSMALL) | _evallg(31), vZ, 0, 0, 0, -3, -54, -456, -2360, -8090, -17649, -14782, 58652, 320100, 913956, 1907052, 3166854, 4342211, 5012510, 4919796, 4115740, 2925262, 1758603, 897424, 398596, 161856, 61860, 21000, 5544, 966, 84 }; /* 84*z^28 + 966*z^27 + 5544*z^26 + 21000*z^25 + 61860*z^24 + 161856*z^23 + 398596*z^22 + 897424*z^21 + 1758603*z^20 + 2925262*z^19 + 4115740*z^18 + 4919796*z^17 + 5012510*z^16 + 4342211*z^15 + 3166854*z^14 + 1907052*z^13 + 913956*z^12 + 320100*z^11 + 58652*z^10 - 14782*z^9 - 17649*z^8 - 8090*z^7 - 2360*z^6 - 456*z^5 - 54*z^4 - 3*z^3 */
static const long X1_39_crv_4[31] = {
  evaltyp(t_VECSMALL) | _evallg(31), vZ, 0, 0, 0, 6, 90, 600, 2216, 4030, -2842, -41460, -134160, -244602, -204565, 270580, 1391660, 3031220, 4657354, 5608136, 5505000, 4469310, 3004995, 1667408, 765412, 297098, 101730, 31200, 7896, 1386, 126 }; /* 126*z^28 + 1386*z^27 + 7896*z^26 + 31200*z^25 + 101730*z^24 + 297098*z^23 + 765412*z^22 + 1667408*z^21 + 3004995*z^20 + 4469310*z^19 + 5505000*z^18 + 5608136*z^17 + 4657354*z^16 + 3031220*z^15 + 1391660*z^14 + 270580*z^13 - 204565*z^12 - 244602*z^11 - 134160*z^10 - 41460*z^9 - 2842*z^8 + 4030*z^7 + 2216*z^6 + 600*z^5 + 90*z^4 + 6*z^3 */
static const long X1_39_crv_5[31] = {
  evaltyp(t_VECSMALL) | _evallg(31), vZ, 0, 0, 0, -10, -120, -600, -1366, 333, 11565, 34350, 39780, -44343, -271552, -540912, -540060, 55910, 1236231, 2539962, 3353964, 3341835, 2628990, 1650292, 826386, 332211, 110495, 31770, 7704, 1344, 126 }; /* 126*z^28 + 1344*z^27 + 7704*z^26 + 31770*z^25 + 110495*z^24 + 332211*z^23 + 826386*z^22 + 1650292*z^21 + 2628990*z^20 + 3341835*z^19 + 3353964*z^18 + 2539962*z^17 + 1236231*z^16 + 55910*z^15 - 540060*z^14 - 540912*z^13 - 271552*z^12 - 44343*z^11 + 39780*z^10 + 34350*z^9 + 11565*z^8 + 333*z^7 - 1366*z^6 - 600*z^5 - 120*z^4 - 10*z^3 */
static const long X1_39_crv_6[31] = {
  evaltyp(t_VECSMALL) | _evallg(31), vZ, 0, 0, 0, 15, 135, 480, 496, -1916, -7416, -6456, 20760, 72513, 79677, -68172, -375720, -626120, -521846, 6228, 693252, 1162575, 1213200, 922068, 528492, 230394, 77944, 21640, 5076, 876, 84 }; /* 84*z^28 + 876*z^27 + 5076*z^26 + 21640*z^25 + 77944*z^24 + 230394*z^23 + 528492*z^22 + 922068*z^21 + 1213200*z^20 + 1162575*z^19 + 693252*z^18 + 6228*z^17 - 521846*z^16 - 626120*z^15 - 375720*z^14 - 68172*z^13 + 79677*z^12 + 72513*z^11 + 20760*z^10 - 6456*z^9 - 7416*z^8 - 1916*z^7 + 496*z^6 + 480*z^5 + 135*z^4 + 15*z^3 */
static const long X1_39_crv_7[31] = {
  evaltyp(t_VECSMALL) | _evallg(31), vZ, -1, -14, -112, -637, -2744, -9268, -25634, -61105, -129905, -245998, -404852, -565402, -669214, -706388, -743626, -829121, -883369, -768278, -461620, -94892, 166136, 245336, 188602, 96449, 34678, 9452, 2164, 369, 36 }; /* 36*z^28 + 369*z^27 + 2164*z^26 + 9452*z^25 + 34678*z^24 + 96449*z^23 + 188602*z^22 + 245336*z^21 + 166136*z^20 - 94892*z^19 - 461620*z^18 - 768278*z^17 - 883369*z^16 - 829121*z^15 - 743626*z^14 - 706388*z^13 - 669214*z^12 - 565402*z^11 - 404852*z^10 - 245998*z^9 - 129905*z^8 - 61105*z^7 - 25634*z^6 - 9268*z^5 - 2744*z^4 - 637*z^3 - 112*z^2 - 14*z - 1 */
static const long X1_39_crv_8[31] = {
  evaltyp(t_VECSMALL) | _evallg(31), vZ, 0, 0, 0, -15, -240, -1740, -7784, -25122, -65124, -144524, -280656, -474318, -686088, -842244, -893172, -859748, -787386, -678672, -516680, -320022, -140013, -23112, 21288, 20526, 8890, 2400, 540, 91, 9 }; /* 9*z^28 + 91*z^27 + 540*z^26 + 2400*z^25 + 8890*z^24 + 20526*z^23 + 21288*z^22 - 23112*z^21 - 140013*z^20 - 320022*z^19 - 516680*z^18 - 678672*z^17 - 787386*z^16 - 859748*z^15 - 893172*z^14 - 842244*z^13 - 686088*z^12 - 474318*z^11 - 280656*z^10 - 144524*z^9 - 65124*z^8 - 25122*z^7 - 7784*z^6 - 1740*z^5 - 240*z^4 - 15*z^3 */
static const long X1_39_crv_9[31] = {
  evaltyp(t_VECSMALL) | _evallg(31), vZ, 0, 0, 0, 10, 130, 720, 2314, 5035, 7806, 6900, -5820, -43146, -114251, -207128, -284760, -316700, -306131, -269898, -216012, -151485, -87840, -38140, -9736, 192, 1005, 270, 60, 10, 1 }; /* z^28 + 10*z^27 + 60*z^26 + 270*z^25 + 1005*z^24 + 192*z^23 - 9736*z^22 - 38140*z^21 - 87840*z^20 - 151485*z^19 - 216012*z^18 - 269898*z^17 - 306131*z^16 - 316700*z^15 - 284760*z^14 - 207128*z^13 - 114251*z^12 - 43146*z^11 - 5820*z^10 + 6900*z^9 + 7806*z^8 + 5035*z^7 + 2314*z^6 + 720*z^5 + 130*z^4 + 10*z^3 */
static const long X1_39_crv_10[26] = {
  evaltyp(t_VECSMALL) | _evallg(26), vZ, 0, 0, 0, -6, -60, -240, -544, -818, -616, 720, 3780, 7806, 8717, 268, -17560, -34940, -43894, -44924, -39972, -31080, -20535, -10860, -4080, -816 }; /* -816*z^23 - 4080*z^22 - 10860*z^21 - 20535*z^20 - 31080*z^19 - 39972*z^18 - 44924*z^17 - 43894*z^16 - 34940*z^15 - 17560*z^14 + 268*z^13 + 8717*z^12 + 7806*z^11 + 3780*z^10 + 720*z^9 - 616*z^8 - 818*z^7 - 544*z^6 - 240*z^5 - 60*z^4 - 6*z^3 */
static const long X1_39_crv_11[26] = {
  evaltyp(t_VECSMALL) | _evallg(26), vZ, 0, 0, 0, 3, 21, 60, 124, 192, 243, 266, 360, 849, 2178, 3780, 3786, 1845, -261, -1806, -2556, -2574, -2055, -1300, -594, -153 }; /* -153*z^23 - 594*z^22 - 1300*z^21 - 2055*z^20 - 2574*z^19 - 2556*z^18 - 1806*z^17 - 261*z^16 + 1845*z^15 + 3786*z^14 + 3780*z^13 + 2178*z^12 + 849*z^11 + 360*z^10 + 266*z^9 + 243*z^8 + 192*z^7 + 124*z^6 + 60*z^5 + 21*z^4 + 3*z^3 */
static const long X1_39_crv_12[26] = {
  evaltyp(t_VECSMALL) | _evallg(26), vZ, 0, 0, 0, -1, -4, -12, -28, -58, -108, -188, -308, -483, -650, -596, -348, -248, -218, -216, -208, -187, -147, -100, -52, -18 }; /* -18*z^23 - 52*z^22 - 100*z^21 - 147*z^20 - 187*z^19 - 208*z^18 - 216*z^17 - 218*z^16 - 248*z^15 - 348*z^14 - 596*z^13 - 650*z^12 - 483*z^11 - 308*z^10 - 188*z^9 - 108*z^8 - 58*z^7 - 28*z^6 - 12*z^5 - 4*z^4 - z^3 */
static const long X1_39_crv_13[26] = {
  evaltyp(t_VECSMALL) | _evallg(26), vZ, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -12, -36, -30, -25, -20, -16, -12, -9, -6, -4, -2, -1 }; /* -z^23 - 2*z^22 - 4*z^21 - 6*z^20 - 9*z^19 - 12*z^18 - 16*z^17 - 20*z^16 - 25*z^15 - 30*z^14 - 36*z^13 - 12*z^12 */
static const long X1_39_crv_14[15] = {
  evaltyp(t_VECSMALL) | _evallg(15), vZ, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1 }; /* z^12 */
static const long *X1_39_crv[17] = {
  (long *)(evaltyp(t_POL) | _evallg(17)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_39_crv_0, X1_39_crv_1, X1_39_crv_2, X1_39_crv_3, X1_39_crv_4, X1_39_crv_5, X1_39_crv_6, X1_39_crv_7, X1_39_crv_8, X1_39_crv_9, X1_39_crv_10, X1_39_crv_11, X1_39_crv_12, X1_39_crv_13, X1_39_crv_14
};
/* -z */
static const long *X1_39_r_n[3] = {
  (long *)(evaltyp(t_POL) | _evallg(3)), (long *)(evalvarn(0) | evalsigne(1)),
  FLX_mZ
};
/* 1 */
static const long *X1_39_r_d[3] = {
  (long *)(evaltyp(t_POL) | _evallg(3)), (long *)(evalvarn(0) | evalsigne(1)),
  FLX_1
};
/* (z + 1)*x + (z + 1) */
static const long X1_39_s_n_0[4] = {
  evaltyp(t_VECSMALL) | _evallg(4), vZ, 1, 1 }; /* z + 1 */
static const long X1_39_s_n_1[4] = {
  evaltyp(t_VECSMALL) | _evallg(4), vZ, 1, 1 }; /* z + 1 */
static const long *X1_39_s_n[4] = {
  (long *)(evaltyp(t_POL) | _evallg(4)), (long *)(evalvarn(0) | evalsigne(1)),
  X1_39_s_n_0, X1_39_s_n_1
};
/* z */
static const long *X1_39_s_d[3] = {
  (long *)(evaltyp(t_POL) | _evallg(3)), (long *)(evalvarn(0) | evalsigne(1)),
  FLX_Z
};


static const X1_info X1_table[LAST_X1_LEVEL - FIRST_X1_LEVEL + 1] = {
  { (GEN)X1_13_crv, (GEN)X1_13_r_n, (GEN)X1_13_r_d, 0, (GEN)X1_13_s_n, (GEN)X1_13_s_d, 1, RS_MAP },
  { (GEN)X1_14_crv, (GEN)X1_14_r_n, (GEN)X1_14_r_d, 1, (GEN)X1_14_s_n, (GEN)X1_14_s_d, 0, RS_MAP },
  { (GEN)X1_15_crv, (GEN)X1_15_r_n, (GEN)X1_15_r_d, 1, (GEN)X1_15_s_n, (GEN)X1_15_s_d, 1, RS_MAP },
  { (GEN)X1_16_crv, (GEN)X1_16_r_n, (GEN)X1_16_r_d, 0, (GEN)X1_16_s_n, (GEN)X1_16_s_d, 0, RS_MAP },
  { (GEN)X1_17_crv, (GEN)X1_17_r_n, (GEN)X1_17_r_d, 0, (GEN)X1_17_s_n, (GEN)X1_17_s_d, 0, RS_MAP },
  { (GEN)X1_18_crv, (GEN)X1_18_r_n, (GEN)X1_18_r_d, 0, (GEN)X1_18_s_n, (GEN)X1_18_s_d, 0, RS_MAP },
  { (GEN)X1_19_crv, (GEN)X1_19_r_n, (GEN)X1_19_r_d, 1, (GEN)X1_19_s_n, (GEN)X1_19_s_d, 1, RS_MAP },
  { (GEN)X1_20_crv, (GEN)X1_20_r_n, (GEN)X1_20_r_d, 0, (GEN)X1_20_s_n, (GEN)X1_20_s_d, 0, TQ_MAP },
  { (GEN)X1_21_crv, (GEN)X1_21_r_n, (GEN)X1_21_r_d, 1, (GEN)X1_21_s_n, (GEN)X1_21_s_d, 1, RS_MAP },
  { (GEN)X1_22_crv, (GEN)X1_22_r_n, (GEN)X1_22_r_d, 0, (GEN)X1_22_s_n, (GEN)X1_22_s_d, 0, RS_MAP },
  { (GEN)X1_23_crv, (GEN)X1_23_r_n, (GEN)X1_23_r_d, 0, (GEN)X1_23_s_n, (GEN)X1_23_s_d, 0, RS_MAP },
  { (GEN)X1_24_crv, (GEN)X1_24_r_n, (GEN)X1_24_r_d, 0, (GEN)X1_24_s_n, (GEN)X1_24_s_d, 0, TQ_MAP },
  { (GEN)X1_25_crv, (GEN)X1_25_r_n, (GEN)X1_25_r_d, 0, (GEN)X1_25_s_n, (GEN)X1_25_s_d, 0, RS_MAP },
  { (GEN)X1_26_crv, (GEN)X1_26_r_n, (GEN)X1_26_r_d, 0, (GEN)X1_26_s_n, (GEN)X1_26_s_d, 0, RS_MAP },
  { (GEN)X1_27_crv, (GEN)X1_27_r_n, (GEN)X1_27_r_d, 0, (GEN)X1_27_s_n, (GEN)X1_27_s_d, 0, RS_MAP },
  { (GEN)X1_28_crv, (GEN)X1_28_r_n, (GEN)X1_28_r_d, 0, (GEN)X1_28_s_n, (GEN)X1_28_s_d, 0, QT_MAP },
  { (GEN)X1_29_crv, (GEN)X1_29_r_n, (GEN)X1_29_r_d, 0, (GEN)X1_29_s_n, (GEN)X1_29_s_d, 1, RS_MAP },
  { (GEN)X1_30_crv, (GEN)X1_30_r_n, (GEN)X1_30_r_d, 0, (GEN)X1_30_s_n, (GEN)X1_30_s_d, 0, TQ_MAP },
  { (GEN)X1_31_crv, (GEN)X1_31_r_n, (GEN)X1_31_r_d, 0, (GEN)X1_31_s_n, (GEN)X1_31_s_d, 0, RS_MAP },
  { (GEN)X1_32_crv, (GEN)X1_32_r_n, (GEN)X1_32_r_d, 0, (GEN)X1_32_s_n, (GEN)X1_32_s_d, 0, QT_MAP },
  { (GEN)X1_33_crv, (GEN)X1_33_r_n, (GEN)X1_33_r_d, 0, (GEN)X1_33_s_n, (GEN)X1_33_s_d, 0, T_MAP},
  { (GEN)X1_34_crv, (GEN)X1_34_r_n, (GEN)X1_34_r_d, 0, (GEN)X1_34_s_n, (GEN)X1_34_s_d, 0, RS_MAP },
  { (GEN)X1_35_crv, (GEN)X1_35_r_n, (GEN)X1_35_r_d, 0, (GEN)X1_35_s_n, (GEN)X1_35_s_d, 0, RS_MAP },
  { (GEN)X1_36_crv, (GEN)X1_36_r_n, (GEN)X1_36_r_d, 0, (GEN)X1_36_s_n, (GEN)X1_36_s_d, 0, RS_MAP },
  { (GEN)X1_37_crv, (GEN)X1_37_r_n, (GEN)X1_37_r_d, 0, (GEN)X1_37_s_n, (GEN)X1_37_s_d, 0, RS_MAP },
  { (GEN)X1_38_crv, (GEN)X1_38_r_n, (GEN)X1_38_r_d, 0, (GEN)X1_38_s_n, (GEN)X1_38_s_d, 0, RS_MAP },
  { (GEN)X1_39_crv, (GEN)X1_39_r_n, (GEN)X1_39_r_d, 0, (GEN)X1_39_s_n, (GEN)X1_39_s_d, 0, T_MAP }
};

INLINE const X1_info *
get_X1_info(ulong N)
{
  return &X1_table[N - FIRST_X1_LEVEL];
}
