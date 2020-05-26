/* Copyright (C) 2009  The PARI group.

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

/* Not so fast arithmetic with points over elliptic curves over Fp */

/***********************************************************************/
/**                                                                   **/
/**                              FpJ                                  **/
/**                                                                   **/
/***********************************************************************/

/* Arithmetic is implemented using Jacobian coordinates, representing
 * a projective point (x : y : z) on E by [z*x , z^2*y , z].  This is
 * probably not the fastest representation available for the given
 * problem, but they're easy to implement and up to 60% faster than
 * the school-book method used in FpE_mulu().
 */

/*
 * Cost: 1M + 8S + 1*a + 10add + 1*8 + 2*2 + 1*3.
 * Source: http://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian.html#doubling-dbl-2007-bl
 */

GEN
FpJ_dbl(GEN P, GEN a4, GEN p)
{
  GEN X1, Y1, Z1;
  GEN XX, YY, YYYY, ZZ, S, M, T, Q;

  if (signe(gel(P,3)) == 0)
    return gcopy(P);

  X1 = gel(P,1); Y1 = gel(P,2); Z1 = gel(P,3);

  XX = Fp_sqr(X1, p);
  YY = Fp_sqr(Y1, p);
  YYYY = Fp_sqr(YY, p);
  ZZ = Fp_sqr(Z1, p);
  S = Fp_mulu(Fp_sub(Fp_sqr(Fp_add(X1, YY, p), p),
                       Fp_add(XX, YYYY, p), p), 2, p);
  M = Fp_addmul(Fp_mulu(XX, 3, p), a4, Fp_sqr(ZZ, p),  p);
  T = Fp_sub(Fp_sqr(M, p), Fp_mulu(S, 2, p), p);
  Q = cgetg(4, t_VEC);
  gel(Q,1) = T;
  gel(Q,2) = Fp_sub(Fp_mul(M, Fp_sub(S, T, p), p),
                Fp_mulu(YYYY, 8, p), p);
  gel(Q,3) = Fp_sub(Fp_sqr(Fp_add(Y1, Z1, p), p),
                Fp_add(YY, ZZ, p), p);
  return Q;
}

/*
 * Cost: 11M + 5S + 9add + 4*2.
 * Source: http://www.hyperelliptic.org/EFD/g1p/auto-shortw-jacobian.html#addition-add-2007-bl
 */

GEN
FpJ_add(GEN P, GEN Q, GEN a4, GEN p)
{
  GEN X1, Y1, Z1, X2, Y2, Z2;
  GEN Z1Z1, Z2Z2, U1, U2, S1, S2, H, I, J, r, V, W, R;

  if (signe(gel(Q,3)) == 0) return gcopy(P);
  if (signe(gel(P,3)) == 0) return gcopy(Q);

  X1 = gel(P,1); Y1 = gel(P,2); Z1 = gel(P,3);
  X2 = gel(Q,1); Y2 = gel(Q,2); Z2 = gel(Q,3);

  Z1Z1 = Fp_sqr(Z1, p);
  Z2Z2 = Fp_sqr(Z2, p);
  U1 = Fp_mul(X1, Z2Z2, p);
  U2 = Fp_mul(X2, Z1Z1, p);
  S1 = mulii(Y1, Fp_mul(Z2, Z2Z2, p));
  S2 = mulii(Y2, Fp_mul(Z1, Z1Z1, p));
  H = Fp_sub(U2, U1, p);
  r = Fp_mulu(Fp_sub(S2, S1, p), 2, p);

  /* If points are equal we must double. */
  if (signe(H)== 0) {
    if (signe(r) == 0)
      /* Points are equal so double. */
      return FpJ_dbl(P, a4, p);
    else
      return mkvec3(gen_1, gen_1, gen_0);
  }
  I = Fp_sqr(Fp_mulu(H, 2, p), p);
  J = Fp_mul(H, I, p);
  V = Fp_mul(U1, I, p);
  W = Fp_sub(Fp_sqr(r, p), Fp_add(J, Fp_mulu(V, 2, p), p), p);
  R = cgetg(4, t_VEC);
  gel(R,1) = W;
  gel(R,2) = Fp_sub(mulii(r, subii(V, W)),
                    shifti(mulii(S1, J), 1), p);
  gel(R,3) = Fp_mul(Fp_sub(Fp_sqr(Fp_add(Z1, Z2, p), p),
                           Fp_add(Z1Z1, Z2Z2, p), p), H, p);
  return R;
}

GEN
FpJ_neg(GEN Q, GEN p)
{
  return mkvec3(icopy(gel(Q,1)), Fp_neg(gel(Q,2), p), icopy(gel(Q,3)));
}

GEN
FpE_to_FpJ(GEN P)
{ return ell_is_inf(P) ? mkvec3(gen_1, gen_1, gen_0):
                         mkvec3(icopy(gel(P,1)),icopy(gel(P,2)), gen_1);
}

GEN
FpJ_to_FpE(GEN P, GEN p)
{
  if (signe(gel(P,3)) == 0) return ellinf();
  else
  {
    GEN Z = Fp_inv(gel(P,3), p);
    GEN Z2 = Fp_sqr(Z, p), Z3 = Fp_mul(Z, Z2, p);
    retmkvec2(Fp_mul(gel(P,1), Z2, p), Fp_mul(gel(P,2), Z3, p));
  }
}

struct _FpE
{
  GEN a4,a6;
  GEN p;
};

static GEN
_FpJ_dbl(void *E, GEN P)
{
  struct _FpE *ell = (struct _FpE *) E;
  return FpJ_dbl(P, ell->a4, ell->p);
}

static GEN
_FpJ_add(void *E, GEN P, GEN Q)
{
  struct _FpE *ell=(struct _FpE *) E;
  return FpJ_add(P, Q, ell->a4, ell->p);
}

static GEN
_FpJ_mul(void *E, GEN P, GEN n)
{
  pari_sp av = avma;
  struct _FpE *e=(struct _FpE *) E;
  long s = signe(n);
  if (!s || ell_is_inf(P)) return ellinf();
  if (s<0) P = FpJ_neg(P, e->p);
  if (is_pm1(n)) return s>0? gcopy(P): P;
  return gerepilecopy(av, gen_pow(P, n, e, &_FpJ_dbl, &_FpJ_add));
}

GEN
FpJ_mul(GEN P, GEN n, GEN a4, GEN p)
{
  struct _FpE E;
  E.a4= a4; E.p = p;
  return _FpJ_mul(&E, P, n);
}

/***********************************************************************/
/**                                                                   **/
/**                              FpE                                  **/
/**                                                                   **/
/***********************************************************************/

/* These functions deal with point over elliptic curves over Fp defined
 * by an equation of the form y^2=x^3+a4*x+a6.
 * Most of the time a6 is omitted since it can be recovered from any point
 * on the curve.
 */

GEN
RgE_to_FpE(GEN x, GEN p)
{
  if (ell_is_inf(x)) return x;
  retmkvec2(Rg_to_Fp(gel(x,1),p),Rg_to_Fp(gel(x,2),p));
}

GEN
FpE_to_mod(GEN x, GEN p)
{
  if (ell_is_inf(x)) return x;
  retmkvec2(Fp_to_mod(gel(x,1),p),Fp_to_mod(gel(x,2),p));
}

GEN
FpE_changepoint(GEN x, GEN ch, GEN p)
{
  pari_sp av = avma;
  GEN p1,z,u,r,s,t,v,v2,v3;
  if (ell_is_inf(x)) return x;
  u = gel(ch,1); r = gel(ch,2);
  s = gel(ch,3); t = gel(ch,4);
  v = Fp_inv(u, p); v2 = Fp_sqr(v,p); v3 = Fp_mul(v,v2,p);
  p1 = Fp_sub(gel(x,1),r,p);
  z = cgetg(3,t_VEC);
  gel(z,1) = Fp_mul(v2, p1, p);
  gel(z,2) = Fp_mul(v3, Fp_sub(gel(x,2), Fp_add(Fp_mul(s,p1, p),t, p),p),p);
  return gerepileupto(av, z);
}

GEN
FpE_changepointinv(GEN x, GEN ch, GEN p)
{
  GEN u, r, s, t, X, Y, u2, u3, u2X, z;
  if (ell_is_inf(x)) return x;
  X = gel(x,1); Y = gel(x,2);
  u = gel(ch,1); r = gel(ch,2);
  s = gel(ch,3); t = gel(ch,4);
  u2 = Fp_sqr(u, p); u3 = Fp_mul(u,u2,p);
  u2X = Fp_mul(u2,X, p);
  z = cgetg(3, t_VEC);
  gel(z,1) = Fp_add(u2X,r,p);
  gel(z,2) = Fp_add(Fp_mul(u3,Y,p), Fp_add(Fp_mul(s,u2X,p), t, p), p);
  return z;
}

static GEN
nonsquare_Fp(GEN p)
{
  pari_sp av = avma;
  GEN a;
  do
  {
    avma = av;
    a = randomi(p);
  } while (kronecker(a, p) >= 0);
  return a;
}

void
Fp_elltwist(GEN a4, GEN a6, GEN p, GEN *pt_a4, GEN *pt_a6)
{
  GEN d = nonsquare_Fp(p), d2 = Fp_sqr(d, p), d3 = Fp_mul(d2, d, p);
  *pt_a4 = Fp_mul(a4, d2, p);
  *pt_a6 = Fp_mul(a6, d3, p);
}

static GEN
FpE_dbl_slope(GEN P, GEN a4, GEN p, GEN *slope)
{
  GEN x, y, Q;
  if (ell_is_inf(P) || !signe(gel(P,2))) return ellinf();
  x = gel(P,1); y = gel(P,2);
  *slope = Fp_div(Fp_add(Fp_mulu(Fp_sqr(x,p), 3, p), a4, p),
                  Fp_mulu(y, 2, p), p);
  Q = cgetg(3,t_VEC);
  gel(Q, 1) = Fp_sub(Fp_sqr(*slope, p), Fp_mulu(x, 2, p), p);
  gel(Q, 2) = Fp_sub(Fp_mul(*slope, Fp_sub(x, gel(Q, 1), p), p), y, p);
  return Q;
}

GEN
FpE_dbl(GEN P, GEN a4, GEN p)
{
  pari_sp av = avma;
  GEN slope;
  return gerepileupto(av, FpE_dbl_slope(P,a4,p,&slope));
}

static GEN
FpE_add_slope(GEN P, GEN Q, GEN a4, GEN p, GEN *slope)
{
  GEN Px, Py, Qx, Qy, R;
  if (ell_is_inf(P)) return Q;
  if (ell_is_inf(Q)) return P;
  Px = gel(P,1); Py = gel(P,2);
  Qx = gel(Q,1); Qy = gel(Q,2);
  if (equalii(Px, Qx))
  {
    if (equalii(Py, Qy))
      return FpE_dbl_slope(P, a4, p, slope);
    else
      return ellinf();
  }
  *slope = Fp_div(Fp_sub(Py, Qy, p), Fp_sub(Px, Qx, p), p);
  R = cgetg(3,t_VEC);
  gel(R, 1) = Fp_sub(Fp_sub(Fp_sqr(*slope, p), Px, p), Qx, p);
  gel(R, 2) = Fp_sub(Fp_mul(*slope, Fp_sub(Px, gel(R, 1), p), p), Py, p);
  return R;
}

GEN
FpE_add(GEN P, GEN Q, GEN a4, GEN p)
{
  pari_sp av = avma;
  GEN slope;
  return gerepileupto(av, FpE_add_slope(P,Q,a4,p,&slope));
}

static GEN
FpE_neg_i(GEN P, GEN p)
{
  if (ell_is_inf(P)) return P;
  return mkvec2(gel(P,1), Fp_neg(gel(P,2), p));
}

GEN
FpE_neg(GEN P, GEN p)
{
  if (ell_is_inf(P)) return ellinf();
  return mkvec2(gcopy(gel(P,1)), Fp_neg(gel(P,2), p));
}

GEN
FpE_sub(GEN P, GEN Q, GEN a4, GEN p)
{
  pari_sp av = avma;
  GEN slope;
  return gerepileupto(av, FpE_add_slope(P, FpE_neg_i(Q, p), a4, p, &slope));
}

static GEN
_FpE_dbl(void *E, GEN P)
{
  struct _FpE *ell = (struct _FpE *) E;
  return FpE_dbl(P, ell->a4, ell->p);
}

static GEN
_FpE_add(void *E, GEN P, GEN Q)
{
  struct _FpE *ell=(struct _FpE *) E;
  return FpE_add(P, Q, ell->a4, ell->p);
}

static GEN
_FpE_mul(void *E, GEN P, GEN n)
{
  pari_sp av = avma;
  struct _FpE *e=(struct _FpE *) E;
  long s = signe(n);
  GEN Q;
  if (!s || ell_is_inf(P)) return ellinf();
  if (s<0) P = FpE_neg(P, e->p);
  if (is_pm1(n)) return s>0? gcopy(P): P;
  if (equalis(n,2)) return _FpE_dbl(E, P);
  Q = gen_pow(FpE_to_FpJ(P), n, e, &_FpJ_dbl, &_FpJ_add);
  return gerepileupto(av, FpJ_to_FpE(Q, e->p));
}

GEN
FpE_mul(GEN P, GEN n, GEN a4, GEN p)
{
  struct _FpE E;
  E.a4 = a4; E.p = p;
  return _FpE_mul(&E, P, n);
}

/* Finds a random non-singular point on E */

GEN
random_FpE(GEN a4, GEN a6, GEN p)
{
  pari_sp ltop = avma;
  GEN x, x2, y, rhs;
  do
  {
    avma= ltop;
    x   = randomi(p); /*  x^3+a4*x+a6 = x*(x^2+a4)+a6  */
    x2  = Fp_sqr(x, p);
    rhs = Fp_add(Fp_mul(x, Fp_add(x2, a4, p), p), a6, p);
  } while ((!signe(rhs) && !signe(Fp_add(Fp_mulu(x2,3,p),a4,p)))
          || kronecker(rhs, p) < 0);
  y = Fp_sqrt(rhs, p);
  if (!y) pari_err_PRIME("random_FpE", p);
  return gerepilecopy(ltop, mkvec2(x, y));
}

static GEN
_FpE_rand(void *E)
{
  struct _FpE *e=(struct _FpE *) E;
  return random_FpE(e->a4, e->a6, e->p);
}

static const struct bb_group FpE_group={_FpE_add,_FpE_mul,_FpE_rand,hash_GEN,ZV_equal,ell_is_inf,NULL};

const struct bb_group *
get_FpE_group(void ** pt_E, GEN a4, GEN a6, GEN p)
{
  struct _FpE *e = (struct _FpE *) stack_malloc(sizeof(struct _FpE));
  e->a4 = a4; e->a6 = a6; e->p  = p;
  *pt_E = (void *) e;
  return &FpE_group;
}

GEN
FpE_order(GEN z, GEN o, GEN a4, GEN p)
{
  pari_sp av = avma;
  struct _FpE e;
  GEN r;
  if (lgefint(p) == 3)
  {
    ulong pp = p[2];
    r = Fle_order(ZV_to_Flv(z, pp), o, umodiu(a4,pp), pp);
  }
  else
  {
    e.a4 = a4;
    e.p = p;
    r = gen_order(z, o, (void*)&e, &FpE_group);
  }
  return gerepileuptoint(av, r);
}

GEN
FpE_log(GEN a, GEN b, GEN o, GEN a4, GEN p)
{
  pari_sp av = avma;
  struct _FpE e;
  GEN r;
  if (lgefint(p) == 3)
  {
    ulong pp = p[2];
    r = Fle_log(ZV_to_Flv(a,pp), ZV_to_Flv(b,pp), o, umodiu(a4,pp), pp);
  }
  else
  {
    e.a4 = a4;
    e.p = p;
    r = gen_PH_log(a, b, o, (void*)&e, &FpE_group);
  }
  return gerepileuptoint(av, r);
}

/***********************************************************************/
/**                                                                   **/
/**                            Pairings                               **/
/**                                                                   **/
/***********************************************************************/

/* Derived from APIP from and by Jerome Milan, 2012 */

static GEN
FpE_vert(GEN P, GEN Q, GEN a4, GEN p)
{
  if (ell_is_inf(P))
    return gen_1;
  if (!equalii(gel(Q, 1), gel(P, 1)))
    return Fp_sub(gel(Q, 1), gel(P, 1), p);
  if (signe(gel(P,2))!=0) return gen_1;
  return Fp_inv(Fp_add(Fp_mulu(Fp_sqr(gel(P,1),p), 3, p), a4, p), p);
}

static GEN
FpE_Miller_line(GEN R, GEN Q, GEN slope, GEN a4, GEN p)
{
  GEN x = gel(Q, 1), y = gel(Q, 2);
  GEN tmp1 = Fp_sub(x, gel(R, 1), p);
  GEN tmp2 = Fp_add(Fp_mul(tmp1, slope, p), gel(R,2), p);
  if (!equalii(y, tmp2))
    return Fp_sub(y, tmp2, p);
  if (signe(y) == 0)
    return gen_1;
  else
  {
    GEN s1, s2;
    GEN y2i = Fp_inv(Fp_mulu(y, 2, p), p);
    s1 = Fp_mul(Fp_add(Fp_mulu(Fp_sqr(x, p), 3, p), a4, p), y2i, p);
    if (!equalii(s1, slope))
      return Fp_sub(s1, slope, p);
    s2 = Fp_mul(Fp_sub(Fp_mulu(x, 3, p), Fp_sqr(s1, p), p), y2i, p);
    return signe(s2)!=0 ? s2: y2i;
  }
}

/* Computes the equation of the line tangent to R and returns its
   evaluation at the point Q. Also doubles the point R.
 */

static GEN
FpE_tangent_update(GEN R, GEN Q, GEN a4, GEN p, GEN *pt_R)
{
  if (ell_is_inf(R))
  {
    *pt_R = ellinf();
    return gen_1;
  }
  else if (signe(gel(R,2)) == 0)
  {
    *pt_R = ellinf();
    return FpE_vert(R, Q, a4, p);
  } else {
    GEN slope;
    *pt_R = FpE_dbl_slope(R, a4, p, &slope);
    return FpE_Miller_line(R, Q, slope, a4, p);
  }
}

/* Computes the equation of the line through R and P, and returns its
   evaluation at the point Q. Also adds P to the point R.
 */

static GEN
FpE_chord_update(GEN R, GEN P, GEN Q, GEN a4, GEN p, GEN *pt_R)
{
  if (ell_is_inf(R))
  {
    *pt_R = gcopy(P);
    return FpE_vert(P, Q, a4, p);
  }
  else if (ell_is_inf(P))
  {
    *pt_R = gcopy(R);
    return FpE_vert(R, Q, a4, p);
  }
  else if (equalii(gel(P, 1), gel(R, 1)))
  {
    if (equalii(gel(P, 2), gel(R, 2)))
      return FpE_tangent_update(R, Q, a4, p, pt_R);
    else {
      *pt_R = ellinf();
      return FpE_vert(R, Q, a4, p);
    }
  } else {
    GEN slope;
    *pt_R = FpE_add_slope(P, R, a4, p, &slope);
    return FpE_Miller_line(R, Q, slope, a4, p);
  }
}

/* Returns the Miller function f_{m, Q} evaluated at the point P using
   the standard Miller algorithm.
 */

struct _FpE_miller
{
  GEN p, a4, P;
};

static GEN
FpE_Miller_dbl(void* E, GEN d)
{
  struct _FpE_miller *m = (struct _FpE_miller *)E;
  GEN p = m->p, a4 = m->a4, P = m->P;
  GEN v, line;
  GEN num = Fp_sqr(gel(d,1), p);
  GEN denom = Fp_sqr(gel(d,2), p);
  GEN point = gel(d,3);
  line = FpE_tangent_update(point, P, a4, p, &point);
  num  = Fp_mul(num, line, p);
  v = FpE_vert(point, P, a4, p);
  denom = Fp_mul(denom, v, p);
  return mkvec3(num, denom, point);
}

static GEN
FpE_Miller_add(void* E, GEN va, GEN vb)
{
  struct _FpE_miller *m = (struct _FpE_miller *)E;
  GEN p = m->p, a4= m->a4, P = m->P;
  GEN v, line, point;
  GEN na = gel(va,1), da = gel(va,2), pa = gel(va,3);
  GEN nb = gel(vb,1), db = gel(vb,2), pb = gel(vb,3);
  GEN num   = Fp_mul(na, nb, p);
  GEN denom = Fp_mul(da, db, p);
  line = FpE_chord_update(pa, pb, P, a4, p, &point);
  num  = Fp_mul(num, line, p);
  v = FpE_vert(point, P, a4, p);
  denom = Fp_mul(denom, v, p);
  return mkvec3(num, denom, point);
}

static GEN
FpE_Miller(GEN Q, GEN P, GEN m, GEN a4, GEN p)
{
  pari_sp ltop = avma;
  struct _FpE_miller d;
  GEN v, num, denom;

  d.a4 = a4; d.p = p; d.P = P;
  v = gen_pow(mkvec3(gen_1,gen_1,Q), m, (void*)&d, FpE_Miller_dbl, FpE_Miller_add);
  num = gel(v,1); denom = gel(v,2);
  return gerepileupto(ltop, Fp_div(num, denom, p));
}

GEN
FpE_weilpairing(GEN P, GEN Q, GEN m, GEN a4, GEN p)
{
  pari_sp ltop = avma;
  GEN num, denom, result;
  if (ell_is_inf(P) || ell_is_inf(Q) || ZV_equal(P,Q))
    return gen_1;
  num    = FpE_Miller(P, Q, m, a4, p);
  denom  = FpE_Miller(Q, P, m, a4, p);
  result = Fp_div(num, denom, p);
  if (mpodd(m))
    result  = Fp_neg(result, p);
  return gerepileupto(ltop, result);
}

GEN
FpE_tatepairing(GEN P, GEN Q, GEN m, GEN a4, GEN p)
{
  if (ell_is_inf(P) || ell_is_inf(Q))
    return gen_1;
  return FpE_Miller(P, Q, m, a4, p);
}

/***********************************************************************/
/**                                                                   **/
/**                   CM by principal order                           **/
/**                                                                   **/
/***********************************************************************/

/* is jn/jd = J (mod p) */
static int
is_CMj(long J, GEN jn, GEN jd, GEN p)
{ return dvdii(subii(mulis(jd,J), jn), p); }
#ifndef LONG_IS_64BIT
/* is jn/jd = -(2^32 a + b) (mod p) */
static int
u2_is_CMj(ulong a, ulong b, GEN jn, GEN jd, GEN p)
{
  GEN mJ = uu32toi(a,b);
  return dvdii(addii(mulii(jd,mJ), jn), p);
}
#endif

static long
Fp_ellj_get_CM(GEN jn, GEN jd, GEN p)
{
#define CHECK(CM,J) if (is_CMj(J,jn,jd,p)) return CM;
  CHECK(-3,  0);
  CHECK(-4,  1728);
  CHECK(-7,  -3375);
  CHECK(-8,  8000);
  CHECK(-11, -32768);
  CHECK(-12, 54000);
  CHECK(-16, 287496);
  CHECK(-19, -884736);
  CHECK(-27, -12288000);
  CHECK(-28, 16581375);
  CHECK(-43, -884736000);
#ifdef LONG_IS_64BIT
  CHECK(-67, -147197952000L);
  CHECK(-163, -262537412640768000L);
#else
  if (u2_is_CMj(0x00000022UL,0x45ae8000UL,jn,jd,p)) return -67;
  if (u2_is_CMj(0x03a4b862UL,0xc4b40000UL,jn,jd,p)) return -163;
#endif
#undef CHECK
  return 0;
}

/***********************************************************************/
/**                                                                   **/
/**                            issupersingular                        **/
/**                                                                   **/
/***********************************************************************/

/* assume x reduced mod p, monic. Return one root, or NULL if irreducible */
static GEN
FqX_quad_root(GEN x, GEN T, GEN p)
{
  GEN b = gel(x,3), c = gel(x,2);
  GEN D = Fq_sub(Fq_sqr(b, T, p), Fq_mulu(c,4, T, p), T, p);
  GEN s = Fq_sqrt(D,T, p);
  if (!s) return NULL;
  return Fq_Fp_mul(Fq_sub(s, b, T, p), shifti(addiu(p, 1),-1),T, p);
}

/*
 * pol is the modular polynomial of level 2 modulo p.
 *
 * (T, p) defines the field FF_{p^2} in which j_prev and j live.
 */
static long
path_extends_to_floor(GEN j_prev, GEN j, GEN T, GEN p, GEN Phi2, ulong max_len)
{
  pari_sp ltop = avma;
  GEN Phi2_j;
  ulong mult, d;

  /* A path made its way to the floor if (i) its length was cut off
   * before reaching max_path_len, or (ii) it reached max_path_len but
   * only has one neighbour. */
  for (d = 1; d < max_len; ++d) {
    GEN j_next;

    Phi2_j = FqX_div_by_X_x(FqXY_evalx(Phi2, j, T, p), j_prev, T, p, NULL);
    j_next = FqX_quad_root(Phi2_j, T, p);
    if (!j_next)
    { /* j is on the floor */
      avma = ltop;
      return 1;
    }

    j_prev = j; j = j_next;
    if (gc_needed(ltop, 2))
      gerepileall(ltop, 2, &j, &j_prev);
  }

  /* Check that we didn't end up at the floor on the last step (j will
   * point to the last element in the path. */
  Phi2_j = FqX_div_by_X_x(FqXY_evalx(Phi2, j, T, p), j_prev, T, p, NULL);
  mult = FqX_nbroots(Phi2_j, T, p);
  avma = ltop;
  return mult == 0;
}

static int
jissupersingular(GEN j, GEN S, GEN p)
{
  long max_path_len = expi(p)+1;
  GEN Phi2 = FpXX_red(polmodular_ZXX(2,0,0,1), p);
  GEN Phi2_j = FqXY_evalx(Phi2, j, S, p);
  GEN roots = FpXQX_roots(Phi2_j, S, p);
  long nbroots = lg(roots)-1;
  int res = 1;

  /* Every node in a supersingular L-volcano has L + 1 neighbours. */
  /* Note: a multiple root only occur when j has CM by sqrt(-15). */
  if (nbroots==0 || (nbroots==1 && FqX_is_squarefree(Phi2_j, S, p)))
    res = 0;
  else {
    long i, l = lg(roots);
    for (i = 1; i < l; ++i) {
      if (path_extends_to_floor(j, gel(roots, i), S, p, Phi2, max_path_len)) {
        res = 0;
        break;
      }
    }
  }
  /* If none of the paths reached the floor, then the j-invariant is
   * supersingular. */
  return res;
}

int
Fp_elljissupersingular(GEN j, GEN p)
{
  pari_sp ltop = avma;
  long CM;
  if (abscmpiu(p, 5) <= 0) return signe(j) == 0; /* valid if p <= 5 */
  CM = Fp_ellj_get_CM(j, gen_1, p);
  if (CM < 0) return krosi(CM, p) < 0; /* valid if p > 3 */
  else
  {
    GEN S = init_Fq(p, 2, fetch_var());
    int res = jissupersingular(j, S, p);
    (void)delete_var(); avma = ltop; return res;
  }
}

/***********************************************************************/
/**                                                                   **/
/**                            Cardinal                               **/
/**                                                                   **/
/***********************************************************************/

/*assume a4,a6 reduced mod p odd */
static ulong
Fl_elltrace_naive(ulong a4, ulong a6, ulong p)
{
  ulong i, j;
  long a = 0;
  long d0, d1, d2, d3;
  GEN k = const_vecsmall(p, -1);
  k[1] = 0;
  for (i=1, j=1; i < p; i += 2, j = Fl_add(j, i, p))
    k[j+1] = 1;
  d0 = 6%p; d1 = d0; d2 = Fl_add(a4, 1, p); d3 = a6;
  for(i=0;; i++)
  {
    a -= k[1+d3];
    if (i==p-1) break;
    d3 = Fl_add(d3, d2, p);
    d2 = Fl_add(d2, d1, p);
    d1 = Fl_add(d1, d0, p);
  }
  return a;
}

/* z1 <-- z1 + z2, with precomputed inverse */
static void
FpE_add_ip(GEN z1, GEN z2, GEN a4, GEN p, GEN p2inv)
{
  GEN p1,x,x1,x2,y,y1,y2;

  x1 = gel(z1,1); y1 = gel(z1,2);
  x2 = gel(z2,1); y2 = gel(z2,2);
  if (x1 == x2)
    p1 = Fp_add(a4, mulii(x1,mului(3,x1)), p);
  else
    p1 = Fp_sub(y2,y1, p);

  p1 = Fp_mul(p1, p2inv, p);
  x = Fp_sub(sqri(p1), addii(x1,x2), p);
  y = Fp_sub(mulii(p1,subii(x1,x)), y1, p);
  affii(x, x1);
  affii(y, y1);
}

/* make sure *x has lgefint >= k */
static void
_fix(GEN x, long k)
{
  GEN y = (GEN)*x;
  if (lgefint(y) < k) { GEN p1 = cgeti(k); affii(y,p1); *x = (long)p1; }
}

/* Return the lift of a (mod b), which is closest to c */
static GEN
closest_lift(GEN a, GEN b, GEN c)
{
  return addii(a, mulii(b, diviiround(subii(c,a), b)));
}

static long
get_table_size(GEN pordmin, GEN B)
{
  pari_sp av = avma;
  GEN t = ceilr( sqrtr( divri(itor(pordmin, DEFAULTPREC), B) ) );
  if (is_bigint(t))
    pari_err_OVERFLOW("ellap [large prime: install the 'seadata' package]");
  avma = av;
  return itos(t) >> 1;
}

/* Find x such that kronecker(u = x^3+c4x+c6, p) is KRO.
 * Return point [x*u,u^2] on E (KRO=1) / E^twist (KRO=-1) */
static GEN
Fp_ellpoint(long KRO, ulong *px, GEN c4, GEN c6, GEN p)
{
  ulong x = *px;
  GEN u;
  for(;;)
  {
    x++; /* u = x^3 + c4 x + c6 */
    u = modii(addii(c6, mului(x, addii(c4, sqru(x)))), p);
    if (kronecker(u,p) == KRO) break;
  }
  *px = x;
  return mkvec2(modii(mului(x,u),p), Fp_sqr(u,p));
}
static GEN
Fl_ellpoint(long KRO, ulong *px, ulong c4, ulong c6, ulong p)
{
  ulong t, u, x = *px;
  for(;;)
  {
    if (++x >= p) pari_err_PRIME("ellap",utoi(p));
    t = Fl_add(c4, Fl_sqr(x,p), p);
    u = Fl_add(c6, Fl_mul(x, t, p), p);
    if (krouu(u,p) == KRO) break;
  }
  *px = x;
  return mkvecsmall2(Fl_mul(x,u,p), Fl_sqr(u,p));
}

static GEN ap_j1728(GEN a4,GEN p);
/* compute a_p using Shanks/Mestre + Montgomery's trick. Assume p > 457 */
static GEN
Fp_ellcard_Shanks(GEN c4, GEN c6, GEN p)
{
  pari_timer T;
  long *tx, *ty, *ti, pfinal, i, j, s, KRO, nb;
  ulong x;
  pari_sp av = avma, av2;
  GEN p1, P, mfh, h, F,f, fh,fg, pordmin, u, v, p1p, p2p, A, B, a4, pts;
  tx = NULL;
  ty = ti = NULL; /* gcc -Wall */

  if (!signe(c6)) {
    GEN ap = ap_j1728(c4, p);
    return gerepileuptoint(av, subii(addiu(p,1), ap));
  }

  if (DEBUGLEVEL >= 6) timer_start(&T);
  /* once #E(Fp) is know mod B >= pordmin, it is completely determined */
  pordmin = addiu(sqrti(gmul2n(p,4)), 1); /* ceil( 4sqrt(p) ) */
  p1p = addiu(p, 1);
  p2p = shifti(p1p, 1);
  x = 0; KRO = 0;
  /* how many 2-torsion points ? */
  switch(FpX_nbroots(mkpoln(4, gen_1, gen_0, c4, c6), p))
  {
    case 3:  A = gen_0; B = utoipos(4); break;
    case 1:  A = gen_0; B = gen_2; break;
    default: A = gen_1; B = gen_2; break; /* 0 */
  }
  for(;;)
  {
    h = closest_lift(A, B, p1p);
    if (!KRO) /* first time, initialize */
    {
      KRO = kronecker(c6,p);
      f = mkvec2(gen_0, Fp_sqr(c6,p));
    }
    else
    {
      KRO = -KRO;
      f = Fp_ellpoint(KRO, &x, c4,c6,p);
    }
    /* [ux, u^2] is on E_u: y^2 = x^3 + c4 u^2 x + c6 u^3
     * E_u isomorphic to E (resp. E') iff KRO = 1 (resp. -1)
     * #E(F_p) = p+1 - a_p, #E'(F_p) = p+1 + a_p
     *
     * #E_u(Fp) = A (mod B),  h is close to #E_u(Fp) */
    a4 = modii(mulii(c4, gel(f,2)), p); /* c4 for E_u */
    fh = FpE_mul(f, h, a4, p);
    if (ell_is_inf(fh)) goto FOUND;

    s = get_table_size(pordmin, B);
    /* look for h s.t f^h = 0 */
    if (!tx)
    { /* first time: initialize */
      tx = newblock(3*(s+1));
      ty = tx + (s+1);
      ti = ty + (s+1);
    }
    F = FpE_mul(f,B,a4,p);
    *tx = evaltyp(t_VECSMALL) | evallg(s+1);

    /* F = B.f */
    P = gcopy(fh);
    if (s < 3)
    { /* we're nearly done: naive search */
      GEN q1 = P, mF = FpE_neg(F, p); /* -F */
      for (i=1;; i++)
      {
        P = FpE_add(P,F,a4,p); /* h.f + i.F */
        if (ell_is_inf(P)) { h = addii(h, mului(i,B)); goto FOUND; }
        q1 = FpE_add(q1,mF,a4,p); /* h.f - i.F */
        if (ell_is_inf(q1)) { h = subii(h, mului(i,B)); goto FOUND; }
      }
    }
    /* Baby Step/Giant Step */
    nb = minss(128, s >> 1); /* > 0. Will do nb pts at a time: faster inverse */
    pts = cgetg(nb+1, t_VEC);
    j = lgefint(p);
    for (i=1; i<=nb; i++)
    { /* baby steps */
      gel(pts,i) = P; /* h.f + (i-1).F */
      _fix(P+1, j); tx[i] = mod2BIL(gel(P,1));
      _fix(P+2, j); ty[i] = mod2BIL(gel(P,2));
      P = FpE_add(P,F,a4,p); /* h.f + i.F */
      if (ell_is_inf(P)) { h = addii(h, mului(i,B)); goto FOUND; }
    }
    mfh = FpE_neg(fh, p);
    fg = FpE_add(P,mfh,a4,p); /* h.f + nb.F - h.f = nb.F */
    if (ell_is_inf(fg)) { h = mului(nb,B); goto FOUND; }
    u = cgetg(nb+1, t_VEC);
    av2 = avma; /* more baby steps, nb points at a time */
    while (i <= s)
    {
      long maxj;
      for (j=1; j<=nb; j++) /* adding nb.F (part 1) */
      {
        P = gel(pts,j); /* h.f + (i-nb-1+j-1).F */
        gel(u,j) = subii(gel(fg,1), gel(P,1));
        if (!signe(gel(u,j))) /* sum = 0 or doubling */
        {
          long k = i+j-2;
          if (equalii(gel(P,2),gel(fg,2))) k -= 2*nb; /* fg == P */
          h = addii(h, mulsi(k,B)); goto FOUND;
        }
      }
      v = FpV_inv(u, p);
      maxj = (i-1 + nb <= s)? nb: s % nb;
      for (j=1; j<=maxj; j++,i++) /* adding nb.F (part 2) */
      {
        P = gel(pts,j);
        FpE_add_ip(P,fg, a4,p, gel(v,j));
        tx[i] = mod2BIL(gel(P,1));
        ty[i] = mod2BIL(gel(P,2));
      }
      avma = av2;
    }
    P = FpE_add(gel(pts,j-1),mfh,a4,p); /* = (s-1).F */
    if (ell_is_inf(P)) { h = mului(s-1,B); goto FOUND; }
    if (DEBUGLEVEL >= 6)
      timer_printf(&T, "[Fp_ellcard_Shanks] baby steps, s = %ld",s);

    /* giant steps: fg = s.F */
    fg = FpE_add(P,F,a4,p);
    if (ell_is_inf(fg)) { h = mului(s,B); goto FOUND; }
    pfinal = mod2BIL(p); av2 = avma;
    /* Goal of the following: sort points by increasing x-coordinate hash.
     * Done in a complicated way to avoid allocating a large temp vector */
    p1 = vecsmall_indexsort(tx); /* = permutation sorting tx */
    for (i=1; i<=s; i++) ti[i] = tx[p1[i]];
    /* ti = tx sorted */
    for (i=1; i<=s; i++) { tx[i] = ti[i]; ti[i] = ty[p1[i]]; }
    /* tx is sorted. ti = ty sorted */
    for (i=1; i<=s; i++) { ty[i] = ti[i]; ti[i] = p1[i]; }
    /* ty is sorted. ti = permutation sorting tx */
    if (DEBUGLEVEL >= 6) timer_printf(&T, "[Fp_ellcard_Shanks] sorting");
    avma = av2;

    gaffect(fg, gel(pts,1));
    for (j=2; j<=nb; j++) /* pts[j] = j.fg = (s*j).F */
    {
      P = FpE_add(gel(pts,j-1),fg,a4,p);
      if (ell_is_inf(P)) { h = mulii(mulss(s,j), B); goto FOUND; }
      gaffect(P, gel(pts,j));
    }
    /* replace fg by nb.fg since we do nb points at a time */
    avma = av2;
    fg = gcopy(gel(pts,nb)); /* copy: we modify (temporarily) pts[nb] below */
    av2 = avma;

    for (i=1,j=1; ; i++)
    {
      GEN ftest = gel(pts,j);
      long m, l = 1, r = s+1;
      long k, k2, j2;

      avma = av2;
      k = mod2BIL(gel(ftest,1));
      while (l < r)
      {
        m = (l+r) >> 1;
        if (tx[m] < k) l = m+1; else r = m;
      }
      if (r <= s && tx[r] == k)
      {
        while (r && tx[r] == k) r--;
        k2 = mod2BIL(gel(ftest,2));
        for (r++; r <= s && tx[r] == k; r++)
          if (ty[r] == k2 || ty[r] == pfinal - k2)
          { /* [h+j2] f == +/- ftest (= [i.s] f)? */
            j2 = ti[r] - 1;
            if (DEBUGLEVEL >=6)
              timer_printf(&T, "[Fp_ellcard_Shanks] giant steps, i = %ld",i);
            P = FpE_add(FpE_mul(F,stoi(j2),a4,p),fh,a4,p);
            if (equalii(gel(P,1), gel(ftest,1)))
            {
              if (equalii(gel(P,2), gel(ftest,2))) i = -i;
              h = addii(h, mulii(addis(mulss(s,i), j2), B));
              goto FOUND;
            }
          }
      }
      if (++j > nb)
      { /* compute next nb points */
        long save = 0; /* gcc -Wall */;
        for (j=1; j<=nb; j++)
        {
          P = gel(pts,j);
          gel(u,j) = subii(gel(fg,1), gel(P,1));
          if (gel(u,j) == gen_0) /* occurs once: i = j = nb, P == fg */
          {
            gel(u,j) = shifti(gel(P,2),1);
            save = fg[1]; fg[1] = P[1];
          }
        }
        v = FpV_inv(u, p);
        for (j=1; j<=nb; j++)
          FpE_add_ip(gel(pts,j),fg,a4,p, gel(v,j));
        if (i == nb) { fg[1] = save; }
        j = 1;
      }
    }
FOUND: /* found a point of exponent h on E_u */
    h = FpE_order(f, h, a4, p);
    /* h | #E_u(Fp) = A (mod B) */
    A = Z_chinese_all(A, gen_0, B, h, &B);
    if (cmpii(B, pordmin) >= 0) break;
    /* not done: update A mod B for the _next_ curve, isomorphic to
     * the quadratic twist of this one */
    A = remii(subii(p2p,A), B); /* #E(Fp)+#E'(Fp) = 2p+2 */
  }
  if (tx) killblock(tx);
  h = closest_lift(A, B, p1p);
  return gerepileuptoint(av, KRO==1? h: subii(p2p,h));
}

typedef struct
{
  ulong x,y,i;
} multiple;

static int
compare_multiples(multiple *a, multiple *b) { return a->x > b->x? 1:a->x<b->x?-1:0; }

/* find x such that h := a + b x is closest to c and return h:
 * x = round((c-a) / b) = floor( (2(c-a) + b) / 2b )
 * Assume 0 <= a < b < c  and b + 2c < 2^BIL */
static ulong
uclosest_lift(ulong a, ulong b, ulong c)
{
  ulong x = (b + ((c-a) << 1)) / (b << 1);
  return a + b * x;
}

static long
Fle_dbl_inplace(GEN P, ulong a4, ulong p)
{
  ulong x, y, slope;
  if (!P[2]) return 1;
  x = P[1]; y = P[2];
  slope = Fl_div(Fl_add(Fl_triple(Fl_sqr(x,p), p), a4, p),
                 Fl_double(y, p), p);
  P[1] = Fl_sub(Fl_sqr(slope, p), Fl_double(x, p), p);
  P[2] = Fl_sub(Fl_mul(slope, Fl_sub(x, P[1], p), p), y, p);
  return 0;
}

static long
Fle_add_inplace(GEN P, GEN Q, ulong a4, ulong p)
{
  ulong Px, Py, Qx, Qy, slope;
  if (ell_is_inf(Q)) return 0;
  Px = P[1]; Py = P[2];
  Qx = Q[1]; Qy = Q[2];
  if (Px==Qx)
    return Py==Qy ? Fle_dbl_inplace(P, a4, p): 1;
  slope = Fl_div(Fl_sub(Py, Qy, p), Fl_sub(Px, Qx, p), p);
  P[1] = Fl_sub(Fl_sub(Fl_sqr(slope, p), Px, p), Qx, p);
  P[2] = Fl_sub(Fl_mul(slope, Fl_sub(Px, P[1], p), p), Py, p);
  return 0;
}

/* assume 99 < p < 2^(BIL-1) - 2^((BIL+1)/2) and e has good reduction at p.
 * Should use Barett reduction + multi-inverse. See Fp_ellcard_Shanks() */
static long
Fl_ellcard_Shanks(ulong c4, ulong c6, ulong p)
{
  GEN f, fh, fg, ftest, F;
  ulong i, l, r, s, h, x, cp4, p1p, p2p, pordmin,A,B;
  long KRO;
  pari_sp av = avma;
  multiple *table;

  if (!c6) {
    GEN ap = ap_j1728(utoi(c4), utoipos(p));
    avma = av; return p+1 - itos(ap);
  }

  pordmin = (ulong)(1 + 4*sqrt((double)p));
  p1p = p+1;
  p2p = p1p << 1;
  x = 0; KRO = 0;
  switch(Flx_nbroots(mkvecsmall5(0L, c6,c4,0L,1L), p))
  {
    case 3:  A = 0; B = 4; break;
    case 1:  A = 0; B = 2; break;
    default: A = 1; B = 2; break; /* 0 */
  }
  for(;;)
  { /* see comments in Fp_ellcard_Shanks */
    h = uclosest_lift(A, B, p1p);
    if (!KRO) /* first time, initialize */
    {
      KRO = krouu(c6,p); /* != 0 */
      f = mkvecsmall2(0, Fl_sqr(c6,p));
    }
    else
    {
      KRO = -KRO;
      f = Fl_ellpoint(KRO, &x, c4,c6,p);
    }
    cp4 = Fl_mul(c4, f[2], p);
    fh = Fle_mulu(f, h, cp4, p);
    if (ell_is_inf(fh)) goto FOUND;

    s = (ulong) (sqrt(((double)pordmin)/B) / 2);
    if (!s) s = 1;
    table = (multiple *) stack_malloc((s+1) * sizeof(multiple));
    F = Fle_mulu(f, B, cp4, p);
    for (i=0; i < s; i++)
    {
      table[i].x = fh[1];
      table[i].y = fh[2];
      table[i].i = i;
      if (Fle_add_inplace(fh, F, cp4, p)) { h += B*(i+1); goto FOUND; }
    }
    qsort(table,s,sizeof(multiple),(QSCOMP)compare_multiples);
    fg = Fle_mulu(F, s, cp4, p); ftest = zv_copy(fg);
    if (ell_is_inf(ftest)) {
      if (!uisprime(p)) pari_err_PRIME("ellap",utoi(p));
      pari_err_BUG("ellap (f^(i*s) = 1)");
    }
    for (i=1; ; i++)
    {
      l=0; r=s;
      while (l<r)
      {
        ulong m = (l+r) >> 1;
        if (table[m].x < uel(ftest,1)) l=m+1; else r=m;
      }
      if (r < s && table[r].x == uel(ftest,1)) break;
      if (Fle_add_inplace(ftest, fg, cp4, p))
        pari_err_PRIME("ellap",utoi(p));
    }
    h += table[r].i * B;
    if (table[r].y == uel(ftest,2))
      h -= s * i * B;
    else
      h += s * i * B;
FOUND:
    h = itou(Fle_order(f, utoipos(h), cp4, p));
    /* h | #E_u(Fp) = A (mod B) */
    {
      GEN C;
      A = itou( Z_chinese_all(gen_0, utoi(A), utoipos(h), utoipos(B), &C) );
      if (abscmpiu(C, pordmin) >= 0) { /* uclosest_lift could overflow */
        h = itou( closest_lift(utoi(A), C, utoipos(p1p)) );
        break;
      }
      B = itou(C);
    }
    A = (p2p - A) % B; avma = av;
  }
  avma = av; return KRO==1? h: p2p-h;
}

/** ellap from CM (original code contributed by Mark Watkins) **/

static GEN
ap_j0(GEN a6,GEN p)
{
  GEN a, b, e, d;
  if (umodiu(p,3) != 1) return gen_0;
  (void)cornacchia2(utoipos(27),p, &a,&b);
  if (umodiu(a, 3) == 1) a = negi(a);
  d = mulis(a6,-108);
  e = diviuexact(shifti(p,-1), 3); /* (p-1) / 6 */
  return centermod(mulii(a, Fp_pow(d, e, p)), p);
}
static GEN
ap_j1728(GEN a4,GEN p)
{
  GEN a, b, e;
  if (mod4(p) != 1) return gen_0;
  (void)cornacchia2(utoipos(4),p, &a,&b);
  if (Mod4(a)==0) a = b;
  if (Mod2(a)==1) a = shifti(a,1);
  if (Mod8(a)==6) a = negi(a);
  e = shifti(p,-2); /* (p-1) / 4 */
  return centermod(mulii(a, Fp_pow(a4, e, p)), p);
}
static GEN
ap_j8000(GEN a6, GEN p)
{
  GEN a, b;
  long r = mod8(p), s = 1;
  if (r != 1 && r != 3) return gen_0;
  (void)cornacchia2(utoipos(8),p, &a,&b);
  switch(Mod16(a)) {
    case 2: case 6:   if (Mod4(b)) s = -s;
      break;
    case 10: case 14: if (!Mod4(b)) s = -s;
      break;
  }
  if (kronecker(mulis(a6, 42), p) < 0) s = -s;
  return s > 0? a: negi(a);
}
static GEN
ap_j287496(GEN a6, GEN p)
{
  GEN a, b;
  long s = 1;
  if (mod4(p) != 1) return gen_0;
  (void)cornacchia2(utoipos(4),p, &a,&b);
  if (Mod4(a)==0) a = b;
  if (Mod2(a)==1) a = shifti(a,1);
  if (Mod8(a)==6) s = -s;
  if (krosi(2,p) < 0) s = -s;
  if (kronecker(mulis(a6, -14), p) < 0) s = -s;
  return s > 0? a: negi(a);
}
static GEN
ap_cm(int CM, long A6B, GEN a6, GEN p)
{
  GEN a, b;
  long s = 1;
  if (krosi(CM,p) < 0) return gen_0;
  (void)cornacchia2(utoipos(-CM),p, &a, &b);
  if ((CM&3) == 0) CM >>= 2;
  if ((krois(a, -CM) > 0) ^ (CM == -7)) s = -s;
  if (kronecker(mulis(a6,A6B), p) < 0) s = -s;
  return s > 0? a: negi(a);
}
static GEN
ec_ap_cm(int CM, GEN a4, GEN a6, GEN p)
{
  switch(CM)
  {
    case  -3: return ap_j0(a6, p);
    case  -4: return ap_j1728(a4, p);
    case  -8: return ap_j8000(a6, p);
    case -16: return ap_j287496(a6, p);
    case  -7: return ap_cm(CM, -2, a6, p);
    case -11: return ap_cm(CM, 21, a6, p);
    case -12: return ap_cm(CM, 22, a6, p);
    case -19: return ap_cm(CM, 1, a6, p);
    case -27: return ap_cm(CM, 253, a6, p);
    case -28: return ap_cm(-7, -114, a6, p); /* yes, -7 ! */
    case -43: return ap_cm(CM, 21, a6, p);
    case -67: return ap_cm(CM, 217, a6, p);
    case -163:return ap_cm(CM, 185801, a6, p);
    default: return NULL;
  }
}

static GEN
Fp_ellj_nodiv(GEN a4, GEN a6, GEN p)
{
  GEN a43 = Fp_mulu(Fp_powu(a4, 3, p), 4, p);
  GEN a62 = Fp_mulu(Fp_sqr(a6, p), 27, p);
  return mkvec2(Fp_mulu(a43, 1728, p), Fp_add(a43, a62, p));
}

GEN
Fp_ellj(GEN a4, GEN a6, GEN p)
{
  pari_sp av=avma;
  GEN z = Fp_ellj_nodiv(a4, a6, p);
  return gerepileuptoint(av,Fp_div(gel(z,1),gel(z,2),p));
}

static GEN /* Only compute a mod p, so assume p>=17 */
Fp_ellcard_CM(GEN a4, GEN a6, GEN p)
{
  pari_sp av = avma;
  GEN a;
  if (!signe(a4)) a = ap_j0(a6,p);
  else if (!signe(a6)) a = ap_j1728(a4,p);
  else
  {
    GEN j = Fp_ellj_nodiv(a4, a6, p);
    long CM = Fp_ellj_get_CM(gel(j,1), gel(j,2), p);
    if (!CM) { avma = av; return NULL; }
    a = ec_ap_cm(CM,a4,a6,p);
  }
  return gerepileuptoint(av, subii(addiu(p,1),a));
}

GEN
Fp_ellcard(GEN a4, GEN a6, GEN p)
{
  long lp = expi(p);
  ulong pp = p[2];
  if (lp < 11)
    return utoi(pp+1 - Fl_elltrace_naive(umodiu(a4,pp), umodiu(a6,pp), pp));
  { GEN a = Fp_ellcard_CM(a4,a6,p); if (a) return a; }
  if (lp >= 56)
    return Fp_ellcard_SEA(a4, a6, p, 0);
  if (lp <= BITS_IN_LONG-2)
    return utoi(Fl_ellcard_Shanks(umodiu(a4,pp), umodiu(a6,pp), pp));
  return Fp_ellcard_Shanks(a4, a6, p);
}

long
Fl_elltrace(ulong a4, ulong a6, ulong p)
{
  pari_sp av;
  long lp;
  GEN a;
  if (p < (1<<11)) return Fl_elltrace_naive(a4, a6, p);
  lp = expu(p);
  if (lp <= minss(56, BITS_IN_LONG-2)) return p+1-Fl_ellcard_Shanks(a4, a6, p);
  av = avma; a = subui(p+1, Fp_ellcard(utoi(a4), utoi(a6), utoipos(p)));
  avma = av; return itos(a);
}
long
Fl_elltrace_CM(long CM, ulong a4, ulong a6, ulong p)
{
  pari_sp av;
  GEN a;
  if (!CM) return Fl_elltrace(a4,a6,p);
  if (p < (1<<11)) return Fl_elltrace_naive(a4, a6, p);
  av = avma; a = ec_ap_cm(CM, utoi(a4), utoi(a6), utoipos(p));
  avma = av; return itos(a);
}

static GEN
_FpE_pairorder(void *E, GEN P, GEN Q, GEN m, GEN F)
{
  struct _FpE *e = (struct _FpE *) E;
  return  Fp_order(FpE_weilpairing(P,Q,m,e->a4,e->p), F, e->p);
}

GEN
Fp_ellgroup(GEN a4, GEN a6, GEN N, GEN p, GEN *pt_m)
{
  struct _FpE e;
  e.a4=a4; e.a6=a6; e.p=p;
  return gen_ellgroup(N, subiu(p,1), pt_m, (void*)&e, &FpE_group, _FpE_pairorder);
}

GEN
Fp_ellgens(GEN a4, GEN a6, GEN ch, GEN D, GEN m, GEN p)
{
  GEN P;
  pari_sp av = avma;
  struct _FpE e;
  e.a4=a4; e.a6=a6; e.p=p;
  switch(lg(D)-1)
  {
  case 1:
    P = gen_gener(gel(D,1), (void*)&e, &FpE_group);
    P = mkvec(FpE_changepoint(P, ch, p));
    break;
  default:
    P = gen_ellgens(gel(D,1), gel(D,2), m, (void*)&e, &FpE_group, _FpE_pairorder);
    gel(P,1) = FpE_changepoint(gel(P,1), ch, p);
    gel(P,2) = FpE_changepoint(gel(P,2), ch, p);
    break;
  }
  return gerepilecopy(av, P);
}

/* Not so fast arithmetic with points over elliptic curves over FpXQ */

/***********************************************************************/
/**                                                                   **/
/**                              FpXQE                                  **/
/**                                                                   **/
/***********************************************************************/

/* Theses functions deal with point over elliptic curves over FpXQ defined
 * by an equation of the form y^2=x^3+a4*x+a6.
 * Most of the time a6 is omitted since it can be recovered from any point
 * on the curve.
 */

GEN
RgE_to_FpXQE(GEN x, GEN T, GEN p)
{
  if (ell_is_inf(x)) return x;
  retmkvec2(Rg_to_FpXQ(gel(x,1),T,p),Rg_to_FpXQ(gel(x,2),T,p));
}

GEN
FpXQE_changepoint(GEN x, GEN ch, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN p1,z,u,r,s,t,v,v2,v3;
  if (ell_is_inf(x)) return x;
  u = gel(ch,1); r = gel(ch,2);
  s = gel(ch,3); t = gel(ch,4);
  v = FpXQ_inv(u, T, p); v2 = FpXQ_sqr(v, T, p); v3 = FpXQ_mul(v,v2, T, p);
  p1 = FpX_sub(gel(x,1),r, p);
  z = cgetg(3,t_VEC);
  gel(z,1) = FpXQ_mul(v2, p1, T, p);
  gel(z,2) = FpXQ_mul(v3, FpX_sub(gel(x,2), FpX_add(FpXQ_mul(s,p1, T, p),t, p), p), T, p);
  return gerepileupto(av, z);
}

GEN
FpXQE_changepointinv(GEN x, GEN ch, GEN T, GEN p)
{
  GEN u, r, s, t, X, Y, u2, u3, u2X, z;
  if (ell_is_inf(x)) return x;
  X = gel(x,1); Y = gel(x,2);
  u = gel(ch,1); r = gel(ch,2);
  s = gel(ch,3); t = gel(ch,4);
  u2 = FpXQ_sqr(u, T, p); u3 = FpXQ_mul(u,u2, T, p);
  u2X = FpXQ_mul(u2,X, T, p);
  z = cgetg(3, t_VEC);
  gel(z,1) = FpX_add(u2X,r, p);
  gel(z,2) = FpX_add(FpXQ_mul(u3,Y, T, p), FpX_add(FpXQ_mul(s,u2X, T, p), t, p), p);
  return z;
}

static GEN
nonsquare_FpXQ(GEN T, GEN p)
{
  pari_sp av = avma;
  long n = degpol(T), v = varn(T);
  GEN a;
  if (odd(n))
  {
    GEN z = cgetg(3, t_POL);
    z[1] = evalsigne(1) | evalvarn(v);
    gel(z,2) = nonsquare_Fp(p); return z;
  }
  do
  {
    avma = av;
    a = random_FpX(n, v, p);
  } while (FpXQ_issquare(a, T, p));
  return a;
}

void
FpXQ_elltwist(GEN a4, GEN a6, GEN T, GEN p, GEN *pt_a4, GEN *pt_a6)
{
  GEN d = nonsquare_FpXQ(T, p);
  GEN d2 = FpXQ_sqr(d, T, p), d3 = FpXQ_mul(d2, d, T, p);
  *pt_a4 = FpXQ_mul(a4, d2, T, p);
  *pt_a6 = FpXQ_mul(a6, d3, T, p);
}

static GEN
FpXQE_dbl_slope(GEN P, GEN a4, GEN T, GEN p, GEN *slope)
{
  GEN x, y, Q;
  if (ell_is_inf(P) || !signe(gel(P,2))) return ellinf();
  x = gel(P,1); y = gel(P,2);
  *slope = FpXQ_div(FpX_add(FpX_mulu(FpXQ_sqr(x, T, p), 3, p), a4, p),
                            FpX_mulu(y, 2, p), T, p);
  Q = cgetg(3,t_VEC);
  gel(Q, 1) = FpX_sub(FpXQ_sqr(*slope, T, p), FpX_mulu(x, 2, p), p);
  gel(Q, 2) = FpX_sub(FpXQ_mul(*slope, FpX_sub(x, gel(Q, 1), p), T, p), y, p);
  return Q;
}

GEN
FpXQE_dbl(GEN P, GEN a4, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN slope;
  return gerepileupto(av, FpXQE_dbl_slope(P,a4,T,p,&slope));
}

static GEN
FpXQE_add_slope(GEN P, GEN Q, GEN a4, GEN T, GEN p, GEN *slope)
{
  GEN Px, Py, Qx, Qy, R;
  if (ell_is_inf(P)) return Q;
  if (ell_is_inf(Q)) return P;
  Px = gel(P,1); Py = gel(P,2);
  Qx = gel(Q,1); Qy = gel(Q,2);
  if (ZX_equal(Px, Qx))
  {
    if (ZX_equal(Py, Qy))
      return FpXQE_dbl_slope(P, a4, T, p, slope);
    else
      return ellinf();
  }
  *slope = FpXQ_div(FpX_sub(Py, Qy, p), FpX_sub(Px, Qx, p), T, p);
  R = cgetg(3,t_VEC);
  gel(R, 1) = FpX_sub(FpX_sub(FpXQ_sqr(*slope, T, p), Px, p), Qx, p);
  gel(R, 2) = FpX_sub(FpXQ_mul(*slope, FpX_sub(Px, gel(R, 1), p), T, p), Py, p);
  return R;
}

GEN
FpXQE_add(GEN P, GEN Q, GEN a4, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN slope;
  return gerepileupto(av, FpXQE_add_slope(P,Q,a4,T,p,&slope));
}

static GEN
FpXQE_neg_i(GEN P, GEN p)
{
  if (ell_is_inf(P)) return P;
  return mkvec2(gel(P,1), FpX_neg(gel(P,2), p));
}

GEN
FpXQE_neg(GEN P, GEN T, GEN p)
{
  (void) T;
  if (ell_is_inf(P)) return ellinf();
  return mkvec2(gcopy(gel(P,1)), FpX_neg(gel(P,2), p));
}

GEN
FpXQE_sub(GEN P, GEN Q, GEN a4, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN slope;
  return gerepileupto(av, FpXQE_add_slope(P, FpXQE_neg_i(Q, p), a4, T, p, &slope));
}

struct _FpXQE
{
  GEN a4,a6;
  GEN T,p;
};

static GEN
_FpXQE_dbl(void *E, GEN P)
{
  struct _FpXQE *ell = (struct _FpXQE *) E;
  return FpXQE_dbl(P, ell->a4, ell->T, ell->p);
}

static GEN
_FpXQE_add(void *E, GEN P, GEN Q)
{
  struct _FpXQE *ell=(struct _FpXQE *) E;
  return FpXQE_add(P, Q, ell->a4, ell->T, ell->p);
}

static GEN
_FpXQE_mul(void *E, GEN P, GEN n)
{
  pari_sp av = avma;
  struct _FpXQE *e=(struct _FpXQE *) E;
  long s = signe(n);
  if (!s || ell_is_inf(P)) return ellinf();
  if (s<0) P = FpXQE_neg(P, e->T, e->p);
  if (is_pm1(n)) return s>0? gcopy(P): P;
  return gerepileupto(av, gen_pow(P, n, e, &_FpXQE_dbl, &_FpXQE_add));
}

GEN
FpXQE_mul(GEN P, GEN n, GEN a4, GEN T, GEN p)
{
  struct _FpXQE E;
  E.a4= a4; E.T = T; E.p = p;
  return _FpXQE_mul(&E, P, n);
}

/* Finds a random non-singular point on E */

GEN
random_FpXQE(GEN a4, GEN a6, GEN T, GEN p)
{
  pari_sp ltop = avma;
  GEN x, x2, y, rhs;
  long v = get_FpX_var(T), d = get_FpX_degree(T);
  do
  {
    avma= ltop;
    x   = random_FpX(d,v,p); /*  x^3+a4*x+a6 = x*(x^2+a4)+a6  */
    x2  = FpXQ_sqr(x, T, p);
    rhs = FpX_add(FpXQ_mul(x, FpX_add(x2, a4, p), T, p), a6, p);
  } while ((!signe(rhs) && !signe(FpX_add(FpX_mulu(x2,3,p), a4, p)))
          || !FpXQ_issquare(rhs, T, p));
  y = FpXQ_sqrt(rhs, T, p);
  if (!y) pari_err_PRIME("random_FpE", p);
  return gerepilecopy(ltop, mkvec2(x, y));
}

static GEN
_FpXQE_rand(void *E)
{
  struct _FpXQE *e=(struct _FpXQE *) E;
  return random_FpXQE(e->a4, e->a6, e->T, e->p);
}

static const struct bb_group FpXQE_group={_FpXQE_add,_FpXQE_mul,_FpXQE_rand,hash_GEN,ZXV_equal,ell_is_inf};

const struct bb_group *
get_FpXQE_group(void ** pt_E, GEN a4, GEN a6, GEN T, GEN p)
{
  struct _FpXQE *e = (struct _FpXQE *) stack_malloc(sizeof(struct _FpXQE));
  e->a4 = a4; e->a6 = a6; e->T = T; e->p = p;
  *pt_E = (void *) e;
  return &FpXQE_group;
}

GEN
FpXQE_order(GEN z, GEN o, GEN a4, GEN T, GEN p)
{
  pari_sp av = avma;
  struct _FpXQE e;
  e.a4=a4; e.T=T; e.p=p;
  return gerepileuptoint(av, gen_order(z, o, (void*)&e, &FpXQE_group));
}

GEN
FpXQE_log(GEN a, GEN b, GEN o, GEN a4, GEN T, GEN p)
{
  pari_sp av = avma;
  struct _FpXQE e;
  e.a4=a4; e.T=T; e.p=p;
  return gerepileuptoint(av, gen_PH_log(a, b, o, (void*)&e, &FpXQE_group));
}


/***********************************************************************/
/**                                                                   **/
/**                            Pairings                               **/
/**                                                                   **/
/***********************************************************************/

/* Derived from APIP from and by Jerome Milan, 2012 */

static GEN
FpXQE_vert(GEN P, GEN Q, GEN a4, GEN T, GEN p)
{
  long vT = get_FpX_var(T);
  if (ell_is_inf(P))
    return pol_1(get_FpX_var(T));
  if (!ZX_equal(gel(Q, 1), gel(P, 1)))
    return FpX_sub(gel(Q, 1), gel(P, 1), p);
  if (signe(gel(P,2))!=0) return pol_1(vT);
  return FpXQ_inv(FpX_add(FpX_mulu(FpXQ_sqr(gel(P,1), T, p), 3, p),
                  a4, p), T, p);
}

static GEN
FpXQE_Miller_line(GEN R, GEN Q, GEN slope, GEN a4, GEN T, GEN p)
{
  long vT = get_FpX_var(T);
  GEN x = gel(Q, 1), y = gel(Q, 2);
  GEN tmp1  = FpX_sub(x, gel(R, 1), p);
  GEN tmp2  = FpX_add(FpXQ_mul(tmp1, slope, T, p), gel(R, 2), p);
  if (!ZX_equal(y, tmp2))
    return FpX_sub(y, tmp2, p);
  if (signe(y) == 0)
    return pol_1(vT);
  else
  {
    GEN s1, s2;
    GEN y2i = FpXQ_inv(FpX_mulu(y, 2, p), T, p);
    s1 = FpXQ_mul(FpX_add(FpX_mulu(FpXQ_sqr(x, T, p), 3, p), a4, p), y2i, T, p);
    if (!ZX_equal(s1, slope))
      return FpX_sub(s1, slope, p);
    s2 = FpXQ_mul(FpX_sub(FpX_mulu(x, 3, p), FpXQ_sqr(s1, T, p), p), y2i, T, p);
    return signe(s2)!=0 ? s2: y2i;
  }
}

/* Computes the equation of the line tangent to R and returns its
   evaluation at the point Q. Also doubles the point R.
 */

static GEN
FpXQE_tangent_update(GEN R, GEN Q, GEN a4, GEN T, GEN p, GEN *pt_R)
{
  if (ell_is_inf(R))
  {
    *pt_R = ellinf();
    return pol_1(get_FpX_var(T));
  }
  else if (!signe(gel(R,2)))
  {
    *pt_R = ellinf();
    return FpXQE_vert(R, Q, a4, T, p);
  } else {
    GEN slope;
    *pt_R = FpXQE_dbl_slope(R, a4, T, p, &slope);
    return FpXQE_Miller_line(R, Q, slope, a4, T, p);
  }
}

/* Computes the equation of the line through R and P, and returns its
   evaluation at the point Q. Also adds P to the point R.
 */

static GEN
FpXQE_chord_update(GEN R, GEN P, GEN Q, GEN a4, GEN T, GEN p, GEN *pt_R)
{
  if (ell_is_inf(R))
  {
    *pt_R = gcopy(P);
    return FpXQE_vert(P, Q, a4, T, p);
  }
  else if (ell_is_inf(P))
  {
    *pt_R = gcopy(R);
    return FpXQE_vert(R, Q, a4, T, p);
  }
  else if (ZX_equal(gel(P, 1), gel(R, 1)))
  {
    if (ZX_equal(gel(P, 2), gel(R, 2)))
      return FpXQE_tangent_update(R, Q, a4, T, p, pt_R);
    else
    {
      *pt_R = ellinf();
      return FpXQE_vert(R, Q, a4, T, p);
    }
  } else {
    GEN slope;
    *pt_R = FpXQE_add_slope(P, R, a4, T, p, &slope);
    return FpXQE_Miller_line(R, Q, slope, a4, T, p);
  }
}

/* Returns the Miller function f_{m, Q} evaluated at the point P using
   the standard Miller algorithm.
 */

struct _FpXQE_miller
{
  GEN p;
  GEN T, a4, P;
};

static GEN
FpXQE_Miller_dbl(void* E, GEN d)
{
  struct _FpXQE_miller *m = (struct _FpXQE_miller *)E;
  GEN p  = m->p;
  GEN T = m->T, a4 = m->a4, P = m->P;
  GEN v, line;
  GEN num = FpXQ_sqr(gel(d,1), T, p);
  GEN denom = FpXQ_sqr(gel(d,2), T, p);
  GEN point = gel(d,3);
  line = FpXQE_tangent_update(point, P, a4, T, p, &point);
  num  = FpXQ_mul(num, line, T, p);
  v = FpXQE_vert(point, P, a4, T, p);
  denom = FpXQ_mul(denom, v, T, p);
  return mkvec3(num, denom, point);
}

static GEN
FpXQE_Miller_add(void* E, GEN va, GEN vb)
{
  struct _FpXQE_miller *m = (struct _FpXQE_miller *)E;
  GEN p = m->p;
  GEN T = m->T, a4 = m->a4, P = m->P;
  GEN v, line, point;
  GEN na = gel(va,1), da = gel(va,2), pa = gel(va,3);
  GEN nb = gel(vb,1), db = gel(vb,2), pb = gel(vb,3);
  GEN num   = FpXQ_mul(na, nb, T, p);
  GEN denom = FpXQ_mul(da, db, T, p);
  line = FpXQE_chord_update(pa, pb, P, a4, T, p, &point);
  num  = FpXQ_mul(num, line, T, p);
  v = FpXQE_vert(point, P, a4, T, p);
  denom = FpXQ_mul(denom, v, T, p);
  return mkvec3(num, denom, point);
}

static GEN
FpXQE_Miller(GEN Q, GEN P, GEN m, GEN a4, GEN T, GEN p)
{
  pari_sp ltop = avma;
  struct _FpXQE_miller d;
  GEN v, num, denom, g1;

  d.a4 = a4; d.T = T; d.p = p; d.P = P;
  g1 = pol_1(get_FpX_var(T));
  v = gen_pow(mkvec3(g1,g1,Q), m, (void*)&d, FpXQE_Miller_dbl, FpXQE_Miller_add);
  num = gel(v,1); denom = gel(v,2);
  return gerepileupto(ltop, FpXQ_div(num, denom, T, p));
}

GEN
FpXQE_weilpairing(GEN P, GEN Q, GEN m, GEN a4, GEN T, GEN p)
{
  pari_sp ltop = avma;
  GEN num, denom, result;
  if (ell_is_inf(P) || ell_is_inf(Q) || ZXV_equal(P,Q))
    return pol_1(get_FpX_var(T));
  num    = FpXQE_Miller(P, Q, m, a4, T, p);
  denom  = FpXQE_Miller(Q, P, m, a4, T, p);
  result = FpXQ_div(num, denom, T, p);
  if (mpodd(m))
    result  = FpX_neg(result, p);
  return gerepileupto(ltop, result);
}

GEN
FpXQE_tatepairing(GEN P, GEN Q, GEN m, GEN a4, GEN T, GEN p)
{
  if (ell_is_inf(P) || ell_is_inf(Q))
    return pol_1(get_FpX_var(T));
  return FpXQE_Miller(P, Q, m, a4, T, p);
}

/***********************************************************************/
/**                                                                   **/
/**                           issupersingular                         **/
/**                                                                   **/
/***********************************************************************/

GEN
FpXQ_ellj(GEN a4, GEN a6, GEN T, GEN p)
{
  if (absequaliu(p,3)) return pol_0(get_FpX_var(T));
  else
  {
    pari_sp av=avma;
    GEN a43 = FpXQ_mul(a4,FpXQ_sqr(a4,T,p),T,p);
    GEN a62 = FpXQ_sqr(a6,T,p);
    GEN num = FpX_mulu(a43,6912,p);
    GEN den = FpX_add(FpX_mulu(a43,4,p),FpX_mulu(a62,27,p),p);
    return gerepileuptoleaf(av, FpXQ_div(num, den, T, p));
  }
}

int
FpXQ_elljissupersingular(GEN j, GEN T, GEN p)
{
  pari_sp ltop = avma;

  /* All supersingular j-invariants are in FF_{p^2}, so we first check
   * whether j is in FF_{p^2}.  If d is odd, then FF_{p^2} is not a
   * subfield of FF_{p^d} so the j-invariants are all in FF_p.  Hence
   * the j-invariants are in FF_{p^{2 - e}}. */
  ulong d = get_FpX_degree(T);
  GEN S;
  int res;

  if (degpol(j) <= 0) return Fp_elljissupersingular(constant_coeff(j), p);
  if (abscmpiu(p, 5) <= 0) return 0; /* j != 0*/

  /* Set S so that FF_p[T]/(S) is isomorphic to FF_{p^2}: */
  if (d == 2)
    S = T;
  else { /* d > 2 */
    /* We construct FF_{p^2} = FF_p[t]/((T - j)(T - j^p)) which
     * injects into FF_{p^d} via the map T |--> j. */
    GEN j_pow_p = FpXQ_pow(j, p, T, p);
    GEN j_sum = FpX_add(j, j_pow_p, p), j_prod;
    long var = varn(T);
    if (degpol(j_sum) > 0) { avma = ltop; return 0; /* j not in Fp^2 */ }
    j_prod = FpXQ_mul(j, j_pow_p, T, p);
    if (degpol(j_prod) > 0 ) { avma = ltop; return 0; /* j not in Fp^2 */ }
    j_sum = constant_coeff(j_sum); j_prod = constant_coeff(j_prod);
    S = mkpoln(3, gen_1, Fp_neg(j_sum, p), j_prod);
    setvarn(S, var);
    j = pol_x(var);
  }
  res = jissupersingular(j, S, p);
  avma = ltop;
  return res;
}

/***********************************************************************/
/**                                                                   **/
/**                           Point counting                          **/
/**                                                                   **/
/***********************************************************************/

GEN
elltrace_extension(GEN t, long n, GEN q)
{
  pari_sp av = avma;
  GEN v = RgX_to_RgC(RgXQ_powu(pol_x(0), n, mkpoln(3,gen_1,negi(t),q)),2);
  GEN te = addii(shifti(gel(v,1),1), mulii(t,gel(v,2)));
  return gerepileuptoint(av, te);
}

GEN
Fp_ffellcard(GEN a4, GEN a6, GEN q, long n, GEN p)
{
  pari_sp av = avma;
  GEN ap = subii(addiu(p, 1), Fp_ellcard(a4, a6, p));
  GEN te = elltrace_extension(ap, n, p);
  return gerepileuptoint(av, subii(addiu(q, 1), te));
}

static GEN
FpXQ_ellcardj(GEN a4, GEN a6, GEN j, GEN T, GEN q, GEN p, long n)
{
  GEN q1 = addiu(q,1);
  if (signe(j)==0)
  {
    GEN W, w, t, N;
    if (umodiu(q,6)!=1) return q1;
    N = Fp_ffellcard(gen_0,gen_1,q,n,p);
    t = subii(q1, N);
    W = FpXQ_pow(a6,diviuexact(shifti(q,-1), 3),T,p);
    if (degpol(W)>0) /*p=5 mod 6*/
      return ZX_equal1(FpXQ_powu(W,3,T,p)) ? addii(q1,shifti(t,-1)):
                                             subii(q1,shifti(t,-1));
    w = modii(gel(W,2),p);
    if (equali1(w))  return N;
    if (equalii(w,subiu(p,1))) return addii(q1,t);
    else /*p=1 mod 6*/
    {
      GEN u = shifti(t,-1), v = sqrtint(diviuexact(subii(q,sqri(u)),3));
      GEN a = addii(u,v), b = shifti(v,1);
      if (equali1(Fp_powu(w,3,p)))
      {
        if (dvdii(addmulii(a, w, b), p))
          return subii(q1,subii(shifti(b,1),a));
        else
          return addii(q1,addii(a,b));
      }
      else
      {
        if (dvdii(submulii(a, w, b), p))
          return subii(q1,subii(a,shifti(b,1)));
        else
          return subii(q1,addii(a,b));
      }
    }
  } else if (equalii(j,modsi(1728,p)))
  {
    GEN w, W, N, t;
    if (mod4(q)==3) return q1;
    W = FpXQ_pow(a4,shifti(q,-2),T,p);
    if (degpol(W)>0) return q1; /*p=3 mod 4*/
    w = modii(gel(W,2),p);
    N = Fp_ffellcard(gen_1,gen_0,q,n,p);
    if (equali1(w)) return N;
    t = subii(q1, N);
    if (equalii(w,subiu(p,1))) return addii(q1,t);
    else /*p=1 mod 4*/
    {
      GEN u = shifti(t,-1), v = sqrtint(subii(q,sqri(u)));
      if (dvdii(addmulii(u, w, v), p))
        return subii(q1,shifti(v,1));
      else
        return addii(q1,shifti(v,1));
    }
  } else
  {
    GEN g = Fp_div(j, Fp_sub(utoi(1728), j, p), p);
    GEN l = FpXQ_div(FpX_mulu(a6,3,p),FpX_mulu(a4,2,p),T,p);
    GEN N = Fp_ffellcard(Fp_mulu(g,3,p),Fp_mulu(g,2,p),q,n,p);
    if (FpXQ_issquare(l,T,p)) return N;
    return subii(shifti(q1,1),N);
  }
}

GEN
FpXQ_ellcard(GEN a4, GEN a6, GEN T, GEN p)
{
  pari_sp av = avma;
  long n = get_FpX_degree(T);
  GEN q = powiu(p, n), r, J;
  if (degpol(a4)<=0 && degpol(a6)<=0)
    r = Fp_ffellcard(constant_coeff(a4),constant_coeff(a6),q,n,p);
  else if (lgefint(p)==3)
  {
    ulong pp = p[2];
    r =  Flxq_ellcard(ZX_to_Flx(a4,pp),ZX_to_Flx(a6,pp),ZX_to_Flx(T,pp),pp);
  }
  else if (degpol(J=FpXQ_ellj(a4,a6,T,p))<=0)
    r = FpXQ_ellcardj(a4,a6,constant_coeff(J),T,q,p,n);
  else
    r = Fq_ellcard_SEA(a4, a6, q, T, p, 0);
  return gerepileuptoint(av, r);
}

static GEN
_FpXQE_pairorder(void *E, GEN P, GEN Q, GEN m, GEN F)
{
  struct _FpXQE *e = (struct _FpXQE *) E;
  return  FpXQ_order(FpXQE_weilpairing(P,Q,m,e->a4,e->T,e->p), F, e->T, e->p);
}

GEN
FpXQ_ellgroup(GEN a4, GEN a6, GEN N, GEN T, GEN p, GEN *pt_m)
{
  struct _FpXQE e;
  GEN q = powiu(p, get_FpX_degree(T));
  e.a4=a4; e.a6=a6; e.T=T; e.p=p;
  return gen_ellgroup(N, subiu(q,1), pt_m, (void*)&e, &FpXQE_group, _FpXQE_pairorder);
}

GEN
FpXQ_ellgens(GEN a4, GEN a6, GEN ch, GEN D, GEN m, GEN T, GEN p)
{
  GEN P;
  pari_sp av = avma;
  struct _FpXQE e;
  e.a4=a4; e.a6=a6; e.T=T; e.p=p;
  switch(lg(D)-1)
  {
  case 1:
    P = gen_gener(gel(D,1), (void*)&e, &FpXQE_group);
    P = mkvec(FpXQE_changepoint(P, ch, T, p));
    break;
  default:
    P = gen_ellgens(gel(D,1), gel(D,2), m, (void*)&e, &FpXQE_group, _FpXQE_pairorder);
    gel(P,1) = FpXQE_changepoint(gel(P,1), ch, T, p);
    gel(P,2) = FpXQE_changepoint(gel(P,2), ch, T, p);
    break;
  }
  return gerepilecopy(av, P);
}


