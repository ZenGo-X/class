/* Copyright (C) 2012  The PARI group.

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

/* Not so fast arithmetic with points over elliptic curves over Fq,
small characteristic. */

/***********************************************************************/
/**                                                                   **/
/**                              FlxqE                                **/
/**                                                                   **/
/***********************************************************************/

/* Theses functions deal with point over elliptic curves over Fq defined
 * by an equation of the form y^2=x^3+a4*x+a6.
 * Most of the time a6 is omitted since it can be recovered from any point
 * on the curve.
 */

GEN
RgE_to_FlxqE(GEN x, GEN T, ulong p)
{
  if (ell_is_inf(x)) return x;
  retmkvec2(Rg_to_Flxq(gel(x,1),T,p),Rg_to_Flxq(gel(x,2),T,p));
}

GEN
FlxqE_changepoint(GEN x, GEN ch, GEN T, ulong p)
{
  pari_sp av = avma;
  GEN p1,z,u,r,s,t,v,v2,v3;
  if (ell_is_inf(x)) return x;
  u = gel(ch,1); r = gel(ch,2);
  s = gel(ch,3); t = gel(ch,4);
  v = Flxq_inv(u, T, p); v2 = Flxq_sqr(v, T, p); v3 = Flxq_mul(v,v2, T, p);
  p1 = Flx_sub(gel(x,1),r, p);
  z = cgetg(3,t_VEC);
  gel(z,1) = Flxq_mul(v2, p1, T, p);
  gel(z,2) = Flxq_mul(v3, Flx_sub(gel(x,2), Flx_add(Flxq_mul(s, p1, T, p),t, p), p), T, p);
  return gerepileupto(av, z);
}

GEN
FlxqE_changepointinv(GEN x, GEN ch, GEN T, ulong p)
{
  GEN u, r, s, t, X, Y, u2, u3, u2X, z;
  if (ell_is_inf(x)) return x;
  X = gel(x,1); Y = gel(x,2);
  u = gel(ch,1); r = gel(ch,2);
  s = gel(ch,3); t = gel(ch,4);
  u2 = Flxq_sqr(u, T, p); u3 = Flxq_mul(u,u2, T, p);
  u2X = Flxq_mul(u2,X, T, p);
  z = cgetg(3, t_VEC);
  gel(z,1) = Flx_add(u2X,r, p);
  gel(z,2) = Flx_add(Flxq_mul(u3,Y, T, p), Flx_add(Flxq_mul(s,u2X, T, p), t, p), p);
  return z;
}

static ulong
nonsquare_Fl(ulong p)
{
  ulong a;
  do
    a = random_Fl(p);
  while (krouu(a, p) >= 0);
  return a;
}

static GEN
nonsquare_Flxq(GEN T, ulong p)
{
  pari_sp av = avma;
  long n = degpol(T), vs = T[1];
  GEN a;
  if (odd(n))
    return mkvecsmall2(vs, nonsquare_Fl(p));
  do
  {
    avma = av;
    a = random_Flx(n, vs, p);
  } while (Flxq_issquare(a, T, p));
  return a;
}

void
Flxq_elltwist(GEN a, GEN a6, GEN T, ulong p, GEN *pt_a, GEN *pt_a6)
{
  GEN d = nonsquare_Flxq(T, p);
  GEN d2 = Flxq_sqr(d, T, p), d3 = Flxq_mul(d2, d, T, p);
  if (typ(a)==t_VECSMALL)
  {
    *pt_a  = Flxq_mul(a,  d2, T, p);
    *pt_a6 = Flxq_mul(a6, d3, T, p);
  } else
  {
    *pt_a  = mkvec(Flxq_mul(gel(a,1), d, T, p));
    *pt_a6 = Flxq_mul(a6, d3, T, p);
  }
}

static GEN
FlxqE_dbl_slope(GEN P, GEN a4, GEN T, ulong p, GEN *slope)
{
  GEN x, y, Q;
  if (ell_is_inf(P) || !lgpol(gel(P,2))) return ellinf();
  x = gel(P,1); y = gel(P,2);
  if (p==3UL)
    *slope = typ(a4)==t_VEC ? Flxq_div(Flxq_mul(x, gel(a4, 1), T, p), y, T, p)
                            : Flxq_div(a4, Flx_neg(y, p), T, p);
  else
  {
    GEN sx = Flx_add(Flx_triple(Flxq_sqr(x, T, p), p), a4, p);
    *slope = Flxq_div(sx, Flx_double(y, p), T, p);
  }
  Q = cgetg(3,t_VEC);
  gel(Q, 1) = Flx_sub(Flxq_sqr(*slope, T, p), Flx_double(x, p), p);
  if (typ(a4)==t_VEC) gel(Q, 1) = Flx_sub(gel(Q, 1), gel(a4, 1), p);
  gel(Q, 2) = Flx_sub(Flxq_mul(*slope, Flx_sub(x, gel(Q, 1), p), T, p), y, p);
  return Q;
}

GEN
FlxqE_dbl(GEN P, GEN a4, GEN T, ulong p)
{
  pari_sp av = avma;
  GEN slope;
  return gerepileupto(av, FlxqE_dbl_slope(P,a4, T, p,&slope));
}

static GEN
FlxqE_add_slope(GEN P, GEN Q, GEN a4, GEN T, ulong p, GEN *slope)
{
  GEN Px, Py, Qx, Qy, R;
  if (ell_is_inf(P)) return Q;
  if (ell_is_inf(Q)) return P;
  Px = gel(P,1); Py = gel(P,2);
  Qx = gel(Q,1); Qy = gel(Q,2);
  if (Flx_equal(Px, Qx))
  {
    if (Flx_equal(Py, Qy))
      return FlxqE_dbl_slope(P, a4, T, p, slope);
    else
      return ellinf();
  }
  *slope = Flxq_div(Flx_sub(Py, Qy, p), Flx_sub(Px, Qx, p), T, p);
  R = cgetg(3,t_VEC);
  gel(R, 1) = Flx_sub(Flx_sub(Flxq_sqr(*slope, T, p), Px, p), Qx, p);
  if (typ(a4)==t_VEC) gel(R, 1) = Flx_sub(gel(R, 1),gel(a4, 1), p);
  gel(R, 2) = Flx_sub(Flxq_mul(*slope, Flx_sub(Px, gel(R, 1), p), T, p), Py, p);
  return R;
}

GEN
FlxqE_add(GEN P, GEN Q, GEN a4, GEN T, ulong p)
{
  pari_sp av = avma;
  GEN slope;
  return gerepileupto(av, FlxqE_add_slope(P,Q,a4, T, p,&slope));
}

static GEN
FlxqE_neg_i(GEN P, ulong p)
{
  if (ell_is_inf(P)) return P;
  return mkvec2(gel(P,1), Flx_neg(gel(P,2), p));
}

GEN
FlxqE_neg(GEN P, GEN T, ulong p)
{
  (void) T;
  if (ell_is_inf(P)) return ellinf();
  return mkvec2(gcopy(gel(P,1)), Flx_neg(gel(P,2), p));
}

GEN
FlxqE_sub(GEN P, GEN Q, GEN a4, GEN T, ulong p)
{
  pari_sp av = avma;
  GEN slope;
  return gerepileupto(av, FlxqE_add_slope(P, FlxqE_neg_i(Q, p), a4, T, p, &slope));
}

struct _FlxqE
{
  GEN a4, a6;
  GEN T;
  ulong p;
};

static GEN
_FlxqE_dbl(void *E, GEN P)
{
  struct _FlxqE *ell = (struct _FlxqE *) E;
  return FlxqE_dbl(P, ell->a4, ell->T, ell->p);
}

static GEN
_FlxqE_add(void *E, GEN P, GEN Q)
{
  struct _FlxqE *ell=(struct _FlxqE *) E;
  return FlxqE_add(P, Q, ell->a4, ell->T, ell->p);
}

static GEN
_FlxqE_mul(void *E, GEN P, GEN n)
{
  pari_sp av = avma;
  struct _FlxqE *e=(struct _FlxqE *) E;
  long s = signe(n);
  if (!s || ell_is_inf(P)) return ellinf();
  if (s<0) P = FlxqE_neg(P, e->T, e->p);
  if (is_pm1(n)) return s>0? gcopy(P): P;
  return gerepileupto(av, gen_pow(P, n, e, &_FlxqE_dbl, &_FlxqE_add));
}

GEN
FlxqE_mul(GEN P, GEN n, GEN a4, GEN T, ulong p)
{
  struct _FlxqE E;
  E.a4= a4; E.T = T; E.p = p;
  return _FlxqE_mul(&E, P, n);
}

/* 3*x^2+2*a2*x = -a2*x, and a2!=0 */

/* Finds a random non-singular point on E */
static GEN
random_F3xqE(GEN a2, GEN a6, GEN T)
{
  pari_sp ltop = avma;
  GEN x, y, rhs;
  const ulong p=3;
  do
  {
    avma= ltop;
    x   = random_Flx(get_Flx_degree(T),get_Flx_var(T),p);
    rhs = Flx_add(Flxq_mul(Flxq_sqr(x, T, p), Flx_add(x, a2, p), T, p), a6, p);
  } while ((!lgpol(rhs) && !lgpol(x)) || !Flxq_issquare(rhs, T, p));
  y = Flxq_sqrt(rhs, T, p);
  if (!y) pari_err_PRIME("random_F3xqE", T);
  return gerepilecopy(ltop, mkvec2(x, y));
}

/* Finds a random non-singular point on E */
GEN
random_FlxqE(GEN a4, GEN a6, GEN T, ulong p)
{
  pari_sp ltop = avma;
  GEN x, x2, y, rhs;
  if (typ(a4)==t_VEC)
    return random_F3xqE(gel(a4,1), a6, T);
  do
  {
    avma= ltop;
    x   = random_Flx(get_Flx_degree(T),get_Flx_var(T),p);
    x2  = Flxq_sqr(x, T, p); /*  x^3+a4*x+a6 = x*(x^2+a4)+a6  */
    rhs = Flx_add(Flxq_mul(x, Flx_add(x2, a4, p), T, p), a6, p);
  } while ((!lgpol(rhs) && !lgpol(Flx_add(Flx_triple(x2, p), a4, p)))
          || !Flxq_issquare(rhs, T, p));
  y = Flxq_sqrt(rhs, T, p);
  if (!y) pari_err_PRIME("random_FlxqE", T);
  return gerepilecopy(ltop, mkvec2(x, y));
}

static GEN
_FlxqE_rand(void *E)
{
  struct _FlxqE *ell=(struct _FlxqE *) E;
  return random_FlxqE(ell->a4, ell->a6, ell->T, ell->p);
}

static const struct bb_group FlxqE_group={_FlxqE_add,_FlxqE_mul,_FlxqE_rand,hash_GEN,zvV_equal,ell_is_inf, NULL};

const struct bb_group *
get_FlxqE_group(void ** pt_E, GEN a4, GEN a6, GEN T, ulong p)
{
  struct _FlxqE *e = (struct _FlxqE *) stack_malloc(sizeof(struct _FlxqE));
  e->a4 = a4; e->a6 = a6; e->T = Flx_get_red(T, p); e->p = p;
  *pt_E = (void *) e;
  return &FlxqE_group;
}

GEN
FlxqE_order(GEN z, GEN o, GEN a4, GEN T, ulong p)
{
  pari_sp av = avma;
  struct _FlxqE e;
  e.a4=a4; e.T=T; e.p=p;
  return gerepileuptoint(av, gen_order(z, o, (void*)&e, &FlxqE_group));
}

GEN
FlxqE_log(GEN a, GEN b, GEN o, GEN a4, GEN T, ulong p)
{
  pari_sp av = avma;
  struct _FlxqE e;
  e.a4=a4; e.T=T; e.p=p;
  return gerepileuptoint(av, gen_PH_log(a, b, o, (void*)&e, &FlxqE_group));
}

/***********************************************************************/
/**                                                                   **/
/**                            Pairings                               **/
/**                                                                   **/
/***********************************************************************/

/* Derived from APIP from and by Jerome Milan, 2012 */

static GEN
FlxqE_vert(GEN P, GEN Q, GEN a4, GEN T, ulong p)
{
  long vT = get_Flx_var(T);
  GEN df;
  if (ell_is_inf(P))
    return pol1_Flx(vT);
  if (!Flx_equal(gel(Q, 1), gel(P, 1)))
    return Flx_sub(gel(Q, 1), gel(P, 1), p);
  if (lgpol(gel(P,2))!=0) return pol1_Flx(vT);
  df = typ(a4)==t_VEC ? Flxq_mul(gel(P,1), Flx_mulu(gel(a4, 1), 2, p), T, p)
                      : a4;
  return Flxq_inv(Flx_add(Flx_mulu(Flxq_sqr(gel(P,1), T, p), 3, p),
                          df, p), T, p);
}

static GEN
FlxqE_Miller_line(GEN R, GEN Q, GEN slope, GEN a4, GEN T, ulong p)
{
  long vT = get_Flx_var(T);
  GEN x = gel(Q, 1), y = gel(Q, 2);
  GEN tmp1 = Flx_sub(x, gel(R, 1), p);
  GEN tmp2 = Flx_add(Flxq_mul(tmp1, slope, T, p), gel(R, 2), p);
  if (!Flx_equal(y, tmp2))
    return Flx_sub(y, tmp2, p);
  if (lgpol(y) == 0)
    return pol1_Flx(vT);
  else
  {
    GEN s1, s2, a2 = typ(a4)==t_VEC ? gel(a4,1): NULL;
    GEN y2i = Flxq_inv(Flx_mulu(y, 2, p), T, p);
    GEN df = a2 ? Flxq_mul(x, Flx_mulu(a2, 2, p), T, p): a4;
    GEN x3, ddf;
    s1 = Flxq_mul(Flx_add(Flx_mulu(Flxq_sqr(x, T, p), 3, p), df, p), y2i, T, p);
    if (!Flx_equal(s1, slope))
      return Flx_sub(s1, slope, p);
    x3 = Flx_mulu(x, 3, p);
    ddf = a2 ? Flx_add(x3, a2, p): x3;
    s2 = Flxq_mul(Flx_sub(ddf, Flxq_sqr(s1, T, p), p), y2i, T, p);
    return lgpol(s2)!=0 ? s2: y2i;
  }
}

/* Computes the equation of the line tangent to R and returns its
   evaluation at the point Q. Also doubles the point R.
 */

static GEN
FlxqE_tangent_update(GEN R, GEN Q, GEN a4, GEN T, ulong p, GEN *pt_R)
{
  if (ell_is_inf(R))
  {
    *pt_R = ellinf();
    return pol1_Flx(get_Flx_var(T));
  }
  else if (!lgpol(gel(R,2)))
  {
    *pt_R = ellinf();
    return FlxqE_vert(R, Q, a4, T, p);
  } else {
    GEN slope;
    *pt_R = FlxqE_dbl_slope(R, a4, T, p, &slope);
    return FlxqE_Miller_line(R, Q, slope, a4, T, p);
  }
}

/* Computes the equation of the line through R and P, and returns its
   evaluation at the point Q. Also adds P to the point R.
 */

static GEN
FlxqE_chord_update(GEN R, GEN P, GEN Q, GEN a4, GEN T, ulong p, GEN *pt_R)
{
  if (ell_is_inf(R))
  {
    *pt_R = gcopy(P);
    return FlxqE_vert(P, Q, a4, T, p);
  }
  else if (ell_is_inf(P))
  {
    *pt_R = gcopy(R);
    return FlxqE_vert(R, Q, a4, T, p);
  }
  else if (Flx_equal(gel(P, 1), gel(R, 1)))
  {
    if (Flx_equal(gel(P, 2), gel(R, 2)))
      return FlxqE_tangent_update(R, Q, a4, T, p, pt_R);
    else
    {
      *pt_R = ellinf();
      return FlxqE_vert(R, Q, a4, T, p);
    }
  } else {
    GEN slope;
    *pt_R = FlxqE_add_slope(P, R, a4, T, p, &slope);
    return FlxqE_Miller_line(R, Q, slope, a4, T, p);
  }
}

/* Returns the Miller function f_{m, Q} evaluated at the point P using
   the standard Miller algorithm.
 */

struct _FlxqE_miller
{
  ulong p;
  GEN T, a4, P;
};

static GEN
FlxqE_Miller_dbl(void* E, GEN d)
{
  struct _FlxqE_miller *m = (struct _FlxqE_miller *)E;
  ulong p  = m->p;
  GEN T = m->T, a4 = m->a4, P = m->P;
  GEN v, line;
  GEN num = Flxq_sqr(gel(d,1), T, p);
  GEN denom = Flxq_sqr(gel(d,2), T, p);
  GEN point = gel(d,3);
  line = FlxqE_tangent_update(point, P, a4, T, p, &point);
  num  = Flxq_mul(num, line, T, p);
  v = FlxqE_vert(point, P, a4, T, p);
  denom = Flxq_mul(denom, v, T, p);
  return mkvec3(num, denom, point);
}

static GEN
FlxqE_Miller_add(void* E, GEN va, GEN vb)
{
  struct _FlxqE_miller *m = (struct _FlxqE_miller *)E;
  ulong p = m->p;
  GEN T = m->T, a4 = m->a4, P = m->P;
  GEN v, line, point;
  GEN na = gel(va,1), da = gel(va,2), pa = gel(va,3);
  GEN nb = gel(vb,1), db = gel(vb,2), pb = gel(vb,3);
  GEN num   = Flxq_mul(na, nb, T, p);
  GEN denom = Flxq_mul(da, db, T, p);
  line = FlxqE_chord_update(pa, pb, P, a4, T, p, &point);
  num  = Flxq_mul(num, line, T, p);
  v = FlxqE_vert(point, P, a4, T, p);
  denom = Flxq_mul(denom, v, T, p);
  return mkvec3(num, denom, point);
}

static GEN
FlxqE_Miller(GEN Q, GEN P, GEN m, GEN a4, GEN T, ulong p)
{
  pari_sp ltop = avma;
  struct _FlxqE_miller d;
  GEN v, num, denom, g1;

  d.a4 = a4; d.T = T; d.p = p; d.P = P;
  g1 = pol1_Flx(get_Flx_var(T));
  v = gen_pow(mkvec3(g1,g1,Q), m, (void*)&d, FlxqE_Miller_dbl, FlxqE_Miller_add);
  num = gel(v,1); denom = gel(v,2);
  return gerepileupto(ltop, Flxq_div(num, denom, T, p));
}

GEN
FlxqE_weilpairing(GEN P, GEN Q, GEN m, GEN a4, GEN T, ulong p)
{
  pari_sp ltop = avma;
  GEN num, denom, result;
  if (ell_is_inf(P) || ell_is_inf(Q) || Flx_equal(P,Q))
    return pol1_Flx(get_Flx_var(T));
  num    = FlxqE_Miller(P, Q, m, a4, T, p);
  denom  = FlxqE_Miller(Q, P, m, a4, T, p);
  result = Flxq_div(num, denom, T, p);
  if (mpodd(m))
    result  = Flx_neg(result, p);
  return gerepileupto(ltop, result);
}

GEN
FlxqE_tatepairing(GEN P, GEN Q, GEN m, GEN a4, GEN T, ulong p)
{
  if (ell_is_inf(P) || ell_is_inf(Q))
    return pol1_Flx(get_Flx_var(T));
  return FlxqE_Miller(P, Q, m, a4, T, p);
}

static GEN
_FlxqE_pairorder(void *E, GEN P, GEN Q, GEN m, GEN F)
{
  struct _FlxqE *e = (struct _FlxqE *) E;
  return  Flxq_order(FlxqE_weilpairing(P,Q,m,e->a4,e->T,e->p), F, e->T, e->p);
}

GEN
Flxq_ellgroup(GEN a4, GEN a6, GEN N, GEN T, ulong p, GEN *pt_m)
{
  struct _FlxqE e;
  GEN q = powuu(p, get_Flx_degree(T));
  e.a4=a4; e.a6=a6; e.T=T; e.p=p;
  return gen_ellgroup(N, subiu(q,1), pt_m, (void*)&e, &FlxqE_group, _FlxqE_pairorder);
}

GEN
Flxq_ellgens(GEN a4, GEN a6, GEN ch, GEN D, GEN m, GEN T, ulong p)
{
  GEN P;
  pari_sp av = avma;
  struct _FlxqE e;
  e.a4=a4; e.a6=a6; e.T=T; e.p=p;
  switch(lg(D)-1)
  {
  case 0:
    return cgetg(1,t_VEC);
  case 1:
    P = gen_gener(gel(D,1), (void*)&e, &FlxqE_group);
    P = mkvec(FlxqE_changepoint(P, ch, T, p));
    break;
  default:
    P = gen_ellgens(gel(D,1), gel(D,2), m, (void*)&e, &FlxqE_group, _FlxqE_pairorder);
    gel(P,1) = FlxqE_changepoint(gel(P,1), ch, T, p);
    gel(P,2) = FlxqE_changepoint(gel(P,2), ch, T, p);
    break;
  }
  return gerepilecopy(av, P);
}
/***********************************************************************/
/**                                                                   **/
/**                          Point counting                           **/
/**                                                                   **/
/***********************************************************************/

static GEN _can_invl(void *E, GEN V) {(void) E; return V; }

static GEN _can_lin(void *E, GEN F, GEN V, GEN q)
{
  GEN v = RgX_splitting(V, 3);
  (void) E;
  return FpX_sub(V,ZXV_dotproduct(v, F), q);
}

static GEN
_can_iter(void *E, GEN f, GEN q)
{
  GEN h = RgX_splitting(f,3);
  GEN h1s = ZX_sqr(gel(h,1)), h2s = ZX_sqr(gel(h,2)), h3s = ZX_sqr(gel(h,3));
  GEN h12 = ZX_mul(gel(h,1), gel(h,2));
  GEN h13 = ZX_mul(gel(h,1), gel(h,3));
  GEN h23 = ZX_mul(gel(h,2), gel(h,3));
  GEN h1c = ZX_mul(gel(h,1), h1s);
  GEN h3c = ZX_mul(gel(h,3), h3s);
  GEN th = ZX_mul(ZX_sub(h2s,ZX_mulu(h13,3)),gel(h,2));
  GEN y = FpX_sub(f,ZX_add(RgX_shift_shallow(h3c,2),ZX_add(RgX_shift_shallow(th,1),h1c)),q);
  (void) E;
  return mkvecn(7,y,h1s,h2s,h3s,h12,h13,h23);
}

static GEN
_can_invd(void *E, GEN V, GEN v, GEN qM, long M)
{
  GEN h1s=gel(v,2), h2s=gel(v,3), h3s=gel(v,4);
  GEN h12=gel(v,5), h13=gel(v,6), h23=gel(v,7);
  GEN F = mkvec3(ZX_sub(h1s,RgX_shift_shallow(h23,1)),RgX_shift_shallow(ZX_sub(h2s,h13),1),
                 ZX_sub(RgX_shift_shallow(h3s,2),RgX_shift_shallow(h12,1)));
  (void)E;
  return gen_ZpX_Dixon(ZXV_Z_mul(F, utoi(3)), V, qM, utoi(3), M, NULL,
                                                 _can_lin, _can_invl);
}

static GEN
F3x_canonlift(GEN P, long n)
{ return gen_ZpX_Newton(Flx_to_ZX(P),utoi(3), n, NULL, _can_iter, _can_invd); }

static GEN _can5_invl(void *E, GEN V) {(void) E; return V; }

static GEN _can5_lin(void *E, GEN F, GEN V, GEN q)
{
  ulong p = *(ulong*)E;
  GEN v = RgX_splitting(V, p);
  return FpX_sub(V,ZXV_dotproduct(v, F), q);
}

/* P(X,t) -> P(X*t^n,t) mod (t^p-1) */
static GEN
_shift(GEN P, long n, ulong p, long v)
{
  long i, l=lg(P);
  GEN r = cgetg(l,t_POL); r[1] = P[1];
  for(i=2;i<l;i++)
  {
    long s = n*(i-2)%p;
    GEN ci = gel(P,i);
    if (typ(ci)==t_INT)
      gel(r,i) = monomial(ci, s, v);
    else
      gel(r,i) = RgX_rotate_shallow(ci, s, p);
  }
  return FpXX_renormalize(r, l);
}

struct _can_mul
{
  GEN T, q;
  ulong p;
};

static GEN
_can5_mul(void *E, GEN A, GEN B)
{
  struct _can_mul *d = (struct _can_mul *)E;
  GEN a = gel(A,1), b = gel(B,1);
  long n = itos(gel(A,2));
  GEN bn = _shift(b, n, d->p, get_FpX_var(d->T));
  GEN c = FpXQX_mul(a, bn, d->T, d->q);
  return mkvec2(c, addii(gel(A,2), gel(B,2)));
}

static GEN
_can5_sqr(void *E, GEN A)
{
  return _can5_mul(E,A,A);
}

static GEN
_can5_iter(void *E, GEN f, GEN q)
{
  pari_sp av = avma;
  struct _can_mul D;
  ulong p = *(ulong*)E;
  long i, vT = fetch_var();
  GEN N, P, d, V, fs;
  D.q = q; D.T = ZX_Z_sub(pol_xn(p,vT),gen_1);
  D.p = p;
  fs = mkvec2(_shift(f, 1, p, vT), gen_1);
  N = gel(gen_powu(fs,p-1,(void*)&D,_can5_sqr,_can5_mul),1);
  N = simplify_shallow(FpXQX_red(N,polcyclo(p,vT),q));
  P = FpX_mul(N,f,q);
  P = RgX_deflate(P, p);
  d = RgX_splitting(N, p);
  V = cgetg(p+1,t_VEC);
  gel(V,1) = ZX_mulu(gel(d,1), p);
  for(i=2; i<= (long)p; i++)
    gel(V,i) = ZX_mulu(RgX_shift_shallow(gel(d,p+2-i), 1), p);
  (void)delete_var(); return gerepilecopy(av, mkvec2(ZX_sub(f,P),V));
}

static GEN
_can5_invd(void *E, GEN H, GEN v, GEN qM, long M)
{
  ulong p = *(long*)E;
  return gen_ZpX_Dixon(gel(v,2), H, qM, utoi(p), M, E, _can5_lin, _can5_invl);
}

static GEN
Flx_canonlift(GEN P, long n, ulong p)
{
  return p==3 ? F3x_canonlift(P,n):
         gen_ZpX_Newton(Flx_to_ZX(P),utoi(p), n, &p, _can5_iter, _can5_invd);
}

/* assume a and n  are coprime */
static GEN
RgX_circular_shallow(GEN P, long a, long n)
{
  long i, l = lgpol(P);
  GEN Q = cgetg(2+n,t_POL);
  Q[1] = P[1];
  for(i=0; i<l; i++)
    gel(Q,2+(i*a)%n) = gel(P,2+i);
  for(   ; i<n; i++)
    gel(Q,2+(i*a)%n) = gen_0;
  return normalizepol_lg(Q,2+n);
}

static GEN
ZpXQ_frob_cyc(GEN x, GEN T, GEN q, ulong p)
{
  long n = get_FpX_degree(T);
  return FpX_rem(RgX_circular_shallow(x,p,n+1), T, q);
}

static GEN
ZpXQ_frob(GEN x, GEN Xm, GEN T, GEN q, ulong p)
{
  if (lg(Xm)==1)
    return ZpXQ_frob_cyc(x, T, q, p);
  else
  {
    long n = get_FpX_degree(T);
    GEN V = RgX_blocks(RgX_inflate(x, p), n, p);
    GEN W = ZXV_dotproduct(V, Xm);
    return FpX_rem(W, T, q);
  }
}

struct _lift_lin
{
  ulong p;
  GEN sqx, Tp;
  GEN ai, Xm;
};

static GEN _lift_invl(void *E, GEN x)
{
  struct _lift_lin *d = (struct _lift_lin *) E;
  GEN T = d->Tp;
  ulong p = d->p;
  GEN xai = Flxq_mul(ZX_to_Flx(x, p), d->ai, T, p);
  return Flx_to_ZX(Flxq_lroot_fast(xai, d->sqx, T, p));
}

static GEN _lift_lin(void *E, GEN F, GEN x2, GEN q)
{
  struct _lift_lin *d = (struct _lift_lin *) E;
  pari_sp av = avma;
  GEN T = gel(F,3), Xm = gel(F,4);
  GEN y2  = ZpXQ_frob(x2, Xm, T, q, d->p);
  GEN lin = FpX_add(ZX_mul(gel(F,1), y2), ZX_mul(gel(F,2), x2), q);
  return gerepileupto(av, FpX_rem(lin, T, q));
}

static GEN
FpM_FpXV_bilinear(GEN P, GEN X, GEN Y, GEN p)
{
   pari_sp av = avma;
   GEN s =  ZX_mul(FpXV_FpC_mul(X,gel(P,1),p),gel(Y,1));
   long i, l = lg(P);
   for(i=2; i<l; i++)
     s = ZX_add(s, ZX_mul(FpXV_FpC_mul(X,gel(P,i),p),gel(Y,i)));
   return gerepileupto(av, FpX_red(s, p));
}

static GEN
FpM_FpXQV_bilinear(GEN P, GEN X, GEN Y, GEN T, GEN p)
{
  return FpX_rem(FpM_FpXV_bilinear(P,X,Y,p),T,p);
}

static GEN
FpXC_powderiv(GEN M, GEN p)
{
  long i, l;
  long v = varn(gel(M,2));
  GEN m = cgetg_copy(M, &l);
  gel(m,1) = pol_0(v);
  gel(m,2) = pol_1(v);
  for(i=2; i<l-1; i++)
    gel(m,i+1) = FpX_Fp_mul(gel(M,i),utoi(i), p);
  return m;
}

struct _lift_iso
{
  GEN phi;
  GEN Xm,T;
  GEN sqx, Tp;
  ulong p;
};

static GEN
_lift_iter(void *E, GEN x2, GEN q)
{
  struct _lift_iso *d = (struct _lift_iso *) E;
  ulong p = d->p;
  long n = lg(d->phi)-2;
  GEN TN = FpXT_red(d->T, q), XN = FpXV_red(d->Xm, q);
  GEN y2 = ZpXQ_frob(x2, XN, TN, q, p);
  GEN xp = FpXQ_powers(x2, n, TN, q);
  GEN yp = FpXQ_powers(y2, n, TN, q);
  GEN V  = FpM_FpXQV_bilinear(d->phi,xp,yp,TN,q);
  return mkvec3(V,xp,yp);
}

static GEN
_lift_invd(void *E, GEN V, GEN v, GEN qM, long M)
{
  struct _lift_iso *d = (struct _lift_iso *) E;
  struct _lift_lin e;
  ulong p = d->p;
  GEN TM = FpXT_red(d->T, qM), XM = FpXV_red(d->Xm, qM);
  GEN xp = FpXV_red(gel(v,2), qM);
  GEN yp = FpXV_red(gel(v,3), qM);
  GEN Dx = FpM_FpXQV_bilinear(d->phi, FpXC_powderiv(xp, qM), yp, TM, qM);
  GEN Dy = FpM_FpXQV_bilinear(d->phi, xp, FpXC_powderiv(yp, qM), TM, qM);
  GEN F = mkvec4(Dy, Dx, TM, XM);
  e.ai = Flxq_inv(ZX_to_Flx(Dy,p),d->Tp,p);
  e.sqx = d->sqx; e.Tp = d->Tp; e.p=p; e.Xm = XM;
  return gen_ZpX_Dixon(F,V,qM,utoi(p),M,(void*) &e, _lift_lin, _lift_invl);
}

static GEN
lift_isogeny(GEN phi, GEN x0, long n, GEN Xm, GEN T, GEN sqx, GEN Tp, ulong p)
{
  struct _lift_iso d;
  d.phi=phi;
  d.Xm=Xm; d.T=T;
  d.sqx=sqx; d.Tp=Tp; d.p=p;
  return gen_ZpX_Newton(x0, utoi(p), n,(void*)&d, _lift_iter, _lift_invd);
}

static GEN
getc2(GEN act, GEN X, GEN T, GEN q, ulong p, long N)
{
  GEN A1 = RgV_to_RgX(gel(act,1),0), A2 =  RgV_to_RgX(gel(act,2),0);
  long n = brent_kung_optpow(maxss(degpol(A1),degpol(A2)),2,1);
  GEN xp = FpXQ_powers(X,n,T,q);
  GEN P  = FpX_FpXQV_eval(A1, xp, T, q);
  GEN Q  = FpX_FpXQV_eval(A2, xp, T, q);
  return ZpXQ_div(P, Q, T, q, utoi(p), N);
}

struct _ZpXQ_norm
{
  long n;
  GEN T, p;
};

static GEN
ZpXQ_norm_mul(void *E, GEN x, GEN y)
{
  struct _ZpXQ_norm *D = (struct _ZpXQ_norm*)E;
  GEN P = gel(x,1), Q = gel(y,1);
  long a = mael(x,2,1), b = mael(y,2,1);
  retmkvec2(FpXQ_mul(P,ZpXQ_frob_cyc(Q, D->T, D->p, a), D->T, D->p),
            mkvecsmall((a*b)%D->n));
}

static GEN
ZpXQ_norm_sqr(void *E, GEN x)
{
  return ZpXQ_norm_mul(E, x, x);
}

/* Assume T = Phi_(n) and n prime */
GEN
ZpXQ_norm_pcyc(GEN x, GEN T, GEN q, GEN p)
{
  GEN z;
  struct _ZpXQ_norm D;
  long d = get_FpX_degree(T);
  D.T = T; D.p = q; D.n = d+1;
  if (d==1) return ZX_copy(x);
  z = mkvec2(x,mkvecsmall(p[2]));
  z = gen_powu(z,d,(void*)&D,ZpXQ_norm_sqr,ZpXQ_norm_mul);
  return gmael(z,1,2);
}

/* Assume T = Phi_(n) and n prime */
static GEN
ZpXQ_sqrtnorm_pcyc(GEN x, GEN T, GEN q, GEN p, long e)
{
  GEN z = ZpXQ_norm_pcyc(x, T, q, p);
  return Zp_sqrtlift(z,Fp_sqrt(z,p),p,e);
}

/* Assume a = 1 [p], return the square root of the norm */
static GEN
ZpXQ_sqrtnorm(GEN a, GEN T, GEN q, GEN p, long e)
{
  GEN s = Fp_div(FpXQ_trace(ZpXQ_log(a, T, p, e), T, q), gen_2, q);
  return modii(gel(Qp_exp(cvtop(s, p, e-1)),4), q);
}

struct _teich_lin
{
  ulong p;
  GEN sqx, Tp;
  long m;
};

static GEN
_teich_invl(void *E, GEN x)
{
  struct _teich_lin *d = (struct _teich_lin *) E;
  ulong p = d->p;
  GEN T = d->Tp;
  return Flx_to_ZX(Flxq_lroot_fast(ZX_to_Flx(x, p), d->sqx, T, p));
}

static GEN
_teich_lin(void *E, GEN F, GEN x2, GEN q)
{
  struct _teich_lin *d = (struct _teich_lin *) E;
  pari_sp av = avma;
  GEN T = gel(F,2), Xm = gel(F,3);
  GEN y2  = ZpXQ_frob(x2, Xm, T, q, d->p);
  GEN lin = FpX_sub(y2, ZX_mulu(ZX_mul(gel(F,1), x2), d->p), q);
  return gerepileupto(av, FpX_rem(lin, T, q));
}

struct _teich_iso
{
  GEN Xm, T;
  GEN sqx, Tp;
  ulong p;
};

static GEN
_teich_iter(void *E, GEN x2, GEN q)
{
  struct _teich_iso *d = (struct _teich_iso *) E;
  ulong p = d->p;
  GEN TN = FpXT_red(d->T, q), XN = FpXV_red(d->Xm, q);
  GEN y2 = ZpXQ_frob(x2, XN, TN, q, d->p);
  GEN x1 = FpXQ_powu(x2, p-1, TN, q);
  GEN xp = FpXQ_mul(x2, x1, TN, q);
  GEN V = FpX_sub(y2,xp,q);
  return mkvec2(V,x1);
}

static GEN
_teich_invd(void *E, GEN V, GEN v, GEN qM, long M)
{
  struct _teich_iso *d = (struct _teich_iso *) E;
  struct _teich_lin e;
  ulong p = d->p;
  GEN TM = FpXT_red(d->T, qM), XM = FpXV_red(d->Xm, qM);
  GEN x1 = FpX_red(gel(v,2), qM);
  GEN F = mkvec3(x1, TM, XM);
  e.sqx = d->sqx; e.Tp = d->Tp; e.p=p;
  return gen_ZpX_Dixon(F,V,qM,utoi(p),M,(void*) &e, _teich_lin, _teich_invl);
}

static GEN
Teichmuller_lift(GEN x, GEN Xm, GEN T, GEN sqx, GEN Tp, ulong p, long N)
{
  struct _teich_iso d;
  d.Xm = Xm; d.T = T; d.sqx = sqx; d.Tp = Tp; d.p = p;
  return gen_ZpX_Newton(x,utoi(p), N,(void*)&d, _teich_iter, _teich_invd);
}

static GEN
get_norm(GEN a4, GEN a6, GEN T, ulong p, long N)
{
  long sv=T[1];
  GEN a;
  if (p==3) a = gel(a4,1);
  else
  {
    GEN P = mkpoln(4, pol1_Flx(sv), pol0_Flx(sv), a4, a6);
    a = gel(FlxqX_powu(P,p>>1,T,p),2+p-1);
  }
  return Zp_sqrtnlift(gen_1,subss(p,1),utoi(Flxq_norm(a,T,p)),utoi(p), N);
}

static GEN
fill_pols(long n, const long *v, long m, const long *vn,
          const long *vd, GEN *act)
{
  long i, j;
  long d = upowuu(n,12/(n-1));
  GEN N, D, M = zeromatcopy(n+1,n+1);
  gmael(M,1,n+1) = gen_1;
  for(i=2;i<=n+1;i++)
    for(j=i-1;j<=n;j++)
      gmael(M,i,j) = mulis(powuu(d,i-2),v[j-i+1]);
  N = cgetg(m+1,t_COL);
  D = cgetg(m+1,t_COL);
  for(i=1;i<=m;i++)
  {
    gel(N,i) = stoi(*vn++);
    gel(D,i) = stoi(*vd++);
  }
  *act = mkmat2(N,D);
  return M;
}

/*
  These polynomials were extracted from the ECHIDNA databases
  available at <http://echidna.maths.usyd.edu.au/echidna/>
  and computed by David R. Kohel.
  Return the matrix of the modular polynomial, set act to the parametrization,
  and set dj to the opposite of the supersingular j-invariant.
*/
static GEN
get_Kohel_polynomials(ulong p, GEN *act, long *dj)
{
  const long mat3[] = {-1,-36,-270};
  const long num3[] = {1,-483,-21141,-59049};
  const long den3[] = {1,261, 4347, -6561};
  const long mat5[] = {-1,-30,-315,-1300,-1575};
  const long num5[] = {-1,490,20620,158750,78125};
  const long den5[] = {-1,-254,-4124,-12250,3125};
  const long mat7[] = {-1,-28,-322,-1904,-5915,-8624,-4018};
  const long num7[] = {1,-485,-24058,-343833,-2021642,-4353013,-823543};
  const long den7[] = {1,259,5894,49119,168406,166355,-16807};
  const long mat13[]= {-1,-26,-325,-2548,-13832,-54340,-157118,-333580,-509366,
                       -534820,-354536,-124852,-15145};
  const long num13[]= {1,-487,-24056,-391463,-3396483,-18047328,-61622301,
                       -133245853,-168395656,-95422301,-4826809};
  const long den13[]= {1,257,5896,60649,364629,1388256,3396483,5089019,4065464,
                       1069939,-28561};
  switch(p)
  {
  case 3:
    *dj = 0;
    return fill_pols(3,mat3,4,num3,den3,act);
  case 5:
    *dj = 0;
    return fill_pols(5,mat5,5,num5,den5,act);
  case 7:
    *dj = 1;
    return fill_pols(7,mat7,7,num7,den7,act);
  case 13:
    *dj = 8;
    return fill_pols(13,mat13,11,num13,den13,act);
  }
  *dj=0; *act = NULL; return NULL; /* LCOV_EXCL_LINE */
}

long
zx_is_pcyc(GEN T)
{
  long i, n = degpol(T);
  if (!uisprime(n+1))
    return 0;
  for (i=0; i<=n; i++)
    if (T[i+2]!=1UL)
      return 0;
  return 1;
}

static GEN
Flxq_ellcard_Kohel(GEN a4, GEN a6, GEN T, ulong p)
{
  pari_sp av = avma, av2;
  pari_timer ti;
  long n = get_Flx_degree(T), N = (n+4)/2, dj;
  GEN q = powuu(p, N);
  GEN T2, Xm, s1, c2, t, lr;
  GEN S1, sqx;
  GEN Nc2, Np;
  GEN act, phi = get_Kohel_polynomials(p, &act, &dj);
  long ispcyc = zx_is_pcyc(get_Flx_mod(T));
  timer_start(&ti);
  if (!ispcyc)
  {
    T2 = Flx_canonlift(get_Flx_mod(T),N,p);
    if (DEBUGLEVEL) timer_printf(&ti,"Teich");
  } else
    T2 = Flx_to_ZX(get_Flx_mod(T));
  T2 = FpX_get_red(T2, q); T = ZXT_to_FlxT(T2, p);
  av2 = avma;
  if (DEBUGLEVEL) timer_printf(&ti,"Barrett");
  if (!ispcyc)
  {
    Xm = FpXQ_powers(pol_xn(n,get_FpX_var(T2)),p-1,T2,q);
    if (DEBUGLEVEL) timer_printf(&ti,"Xm");
  } else
    Xm = cgetg(1,t_VEC);
  s1 = Flxq_inv(Flx_Fl_add(Flxq_ellj(a4,a6,T,p),dj, p),T,p);
  lr = Flxq_lroot(polx_Flx(get_Flx_var(T)), T, p);
  sqx = Flxq_powers(lr, p-1, T, p);
  S1 = lift_isogeny(phi, Flx_to_ZX(s1), N, Xm, T2, sqx, T ,p);
  if (DEBUGLEVEL) timer_printf(&ti,"Lift isogeny");
  c2 = getc2(act, S1, T2, q, p, N);
  if (DEBUGLEVEL) timer_printf(&ti,"c^2");
  if (p>3 && !ispcyc)
  {
    GEN c2p = Flx_to_ZX(Flxq_inv(ZX_to_Flx(c2,p),T,p));
    GEN tc2 = Teichmuller_lift(c2p,Xm, T2,sqx,T,p,N);
    if (DEBUGLEVEL) timer_printf(&ti,"Teichmuller/Fq");
    c2 = FpX_rem(FpX_mul(tc2,c2,q),T2,q);
  }
  c2 = gerepileupto(av2, c2);
  if (DEBUGLEVEL) timer_printf(&ti,"tc2");
  Nc2 = (ispcyc? ZpXQ_sqrtnorm_pcyc: ZpXQ_sqrtnorm)(c2, T2, q, utoi(p), N);
  if (DEBUGLEVEL) timer_printf(&ti,"Norm");
  Np = get_norm(a4,a6,T,p,N);
  if (p>3 && ispcyc)
  {
    GEN Ncpi =  utoi(Fl_inv(umodiu(Nc2,p), p));
    GEN tNc2 = Zp_sqrtnlift(gen_1, subss(p,1), Ncpi, utoi(p),N);
    if (DEBUGLEVEL) timer_printf(&ti,"Teichmuller/Fp");
    Nc2 = Fp_mul(Nc2,tNc2,q);
  }
  t = Fp_center_i(Fp_mul(Nc2,Np,q),q,shifti(q,-1));
  return gerepileupto(av, subii(addiu(powuu(p,n),1),t));
}

static void
liftcurve(GEN J, GEN T, GEN q, ulong p, long N, GEN *A4, GEN *A6)
{
  pari_sp av = avma;
  GEN r = ZpXQ_inv(Z_ZX_sub(utoi(1728),J),T,utoi(p),N);
  GEN g = FpXQ_mul(J,r,T,q);
  *A4 = FpX_mulu(g,3,q);
  *A6 = FpX_mulu(g,2,q);
  gerepileall(av,2,A4,A6);
}

static GEN
getc5(GEN H, GEN A40, GEN A60, GEN A41, GEN A61, GEN T, GEN q, ulong p, long N)
{
  long d = lg(H)-1;
  GEN s1 = gel(H,d-1), s2 = gel(H,d-2), s3 = d<5 ? pol_0(varn(T)): gel(H,d-3);
  GEN s12 = FpXQ_sqr(s1,T,q);
  GEN h2 = ZX_sub(ZX_shifti(s2,1),s12); /*2*s2-s1^2*/
  GEN h3 = ZX_sub(FpXQ_mul(ZX_add(h2,s2),s1,T,q),ZX_mulu(s3,3));
                                        /*3*s2*s1-s1^3-3s3*/
  GEN alpha= ZX_sub(ZX_mulu(h2,30), ZX_mulu(A40,5*p-6)); /* 30*h2+A40*(6-5*p)*/
  GEN beta = ZX_sub(ZX_sub(ZX_mulu(FpXQ_mul(A40,s1,T,q),42),ZX_mulu(A60,14*p-15)),
                    ZX_mulu(h3,70)); /* 42*A40*s1-A60*(14*p-15)-70*h3 */
  GEN u2 = FpXQ_mul(FpXQ_mul(A41,beta,T,q),
                    ZpXQ_inv(FpXQ_mul(A61,alpha,T,q),T,utoi(p),N),T,q);
  return u2;
}

static GEN
ZpXQX_liftrootmod_vald(GEN f, GEN H, long v, GEN T, GEN p, long e)
{
  pari_sp av = avma, av2;
  GEN pv = p, q, qv, W, df, Tq, fr, dfr;
  ulong mask;
  pari_timer ti;
  if (e <= v+1) return H;
  df = RgX_deriv(f);
  if (v) { pv = powiu(p,v); qv = mulii(pv,p); df = ZXX_Z_divexact(df, pv); }
  else qv = p;
  mask = quadratic_prec_mask(e-v);
  Tq = FpXT_red(T, qv); dfr = FpXQX_red(df, Tq, p);
  if (DEBUGLEVEL) timer_start(&ti);
  W = FpXQXQ_inv(FpXQX_rem(dfr, H, Tq, p), H, Tq, p); /* 1/f'(a) mod (T,p) */
  if (DEBUGLEVEL) timer_printf(&ti,"FpXQXQ_inv");
  q = p; av2 = avma;
  for (;;)
  {
    GEN u, fa, qv, q2v, Tq2, fadH;
    GEN H2 = H, q2 = q;
    q = sqri(q);
    if (mask & 1) q = diviiexact(q,p);
    mask >>= 1;
    if (v) { qv = mulii(q, pv); q2v = mulii(q2, pv); }
    else { qv = q; q2v = q2; }
    Tq2 = FpXT_red(T, q2v); Tq = FpXT_red(T, qv);
    fr = FpXQX_red(f, Tq, qv);
    fa = FpXQX_rem(fr, H, Tq, qv);
    fa = ZXX_Z_divexact(fa, q2v);
    fadH = FpXQXQ_mul(RgX_deriv(H),fa,H,Tq2,q2);
    H = FpXX_add(H, gmul(FpXQXQ_mul(W, fadH, H, Tq2, q2v), q2), qv);
    if (mask == 1) return gerepileupto(av, H);
    dfr = FpXQX_rem(FpXQX_red(df, Tq, q),H,Tq,q);
    u = ZXX_Z_divexact(ZXX_Z_add_shallow(FpXQXQ_mul(W,dfr,H,Tq,q),gen_m1),q2);
    W = gsub(W,gmul(FpXQXQ_mul(u,W,H2,Tq2,q2),q2));
    if (gc_needed(av2,2))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"ZpXQX_liftroot, e = %ld", e);
      gerepileall(av2, 3, &H, &W, &q);
    }
  }
}

static GEN
get_H1(GEN A41, GEN A61, GEN T2, ulong p)
{
  GEN q = utoi(p), T = FpXT_red(T2,q);
  GEN pol = FpXQ_elldivpol(FpX_red(A41,q),FpX_red(A61,q),p,T,q);
  return FpXQX_normalize(RgX_deflate(pol,p),T,q);
}

static GEN
Flxq_ellcard_Harley(GEN a4, GEN a6, GEN T, ulong p)
{
  pari_sp av = avma, av2;
  pari_timer ti;
  long n = get_Flx_degree(T), N = (n+5)/2;
  GEN q = powuu(p, N);
  GEN T2, j, t;
  GEN J1,A40,A41,A60,A61, sqx,Xm;
  GEN pol, h1, H;
  GEN c2, tc2, c2p, Nc2, Np;
  long ispcyc = zx_is_pcyc(get_Flx_mod(T));
  timer_start(&ti);
  if (!ispcyc)
  {
    T2 = Flx_canonlift(get_Flx_mod(T),N,p);
    if (DEBUGLEVEL) timer_printf(&ti,"Teich");
  } else
    T2 = Flx_to_ZX(get_Flx_mod(T));
  T2 = FpX_get_red(T2, q); T = ZXT_to_FlxT(T2, p);
  av2 = avma;
  if (DEBUGLEVEL) timer_printf(&ti,"Barrett");
  if (!ispcyc)
  {
    Xm = FpXQ_powers(pol_xn(n,get_FpX_var(T2)),p-1,T2,q);
    if (DEBUGLEVEL) timer_printf(&ti,"Xm");
  } else
    Xm = cgetg(1,t_VEC);
  if (DEBUGLEVEL) timer_printf(&ti,"Xm");
  j = Flxq_ellj(a4,a6,T,p);
  sqx = Flxq_powers(Flxq_lroot(polx_Flx(T[1]), T, p), p-1, T, p);
  J1 = lift_isogeny(polmodular_ZM(p, 0), Flx_to_ZX(j), N, Xm, T2,sqx,T,p);
  if (DEBUGLEVEL) timer_printf(&ti,"Lift isogeny");
  liftcurve(J1,T2,q,p,N,&A41,&A61);
  A40 = ZpXQ_frob(A41, Xm, T2, q, p);
  A60 = ZpXQ_frob(A61, Xm, T2, q, p);
  if (DEBUGLEVEL) timer_printf(&ti,"liftcurve");
  pol = FpXQ_elldivpol(A40,A60,p,T2,q);
  if (DEBUGLEVEL) timer_printf(&ti,"p-division");
  h1 = get_H1(A41,A61,T2,p);
  H = ZpXQX_liftrootmod_vald(pol,h1,1,T2,utoi(p),N);
  q = diviuexact(q,p); N--;
  if (DEBUGLEVEL) timer_printf(&ti,"kernel");
  c2 = getc5(H,A40,A60,A41,A61,T2,q,p,N);
  if (DEBUGLEVEL) timer_printf(&ti,"c^2");
  if (!ispcyc)
  {
    c2p = Flx_to_ZX(Flxq_inv(ZX_to_Flx(c2,p),T,p));
    tc2 = Teichmuller_lift(c2p,Xm, T2,sqx,T,p,N);
    if (DEBUGLEVEL) timer_printf(&ti,"teichmuller");
    c2 = FpX_rem(FpX_mul(tc2,c2,q),T2,q);
  }
  c2 = gerepileupto(av2, c2);
  q = powuu(p, N);
  Nc2 = (ispcyc? ZpXQ_sqrtnorm_pcyc: ZpXQ_sqrtnorm)(c2, T2, q, utoi(p), N);
  if (DEBUGLEVEL) timer_printf(&ti,"Norm");
  Np = get_norm(a4,a6,T,p,N);
  if (ispcyc)
  {
    GEN Ncpi = utoi(Fl_inv(umodiu(Nc2,p), p));
    GEN tNc2 = Zp_sqrtnlift(gen_1, subss(p,1), Ncpi, utoi(p), N);
    if (DEBUGLEVEL) timer_printf(&ti,"Teichmuller/Fp");
    Nc2 = Fp_mul(Nc2,tNc2,q);
  }
  t = Fp_center_i(Fp_mul(Nc2,Np,q),q,shifti(q,-1));
  return gerepileupto(av, subii(addiu(powuu(p,n),1),t));
}

/***************************************************************************/
/*                                                                         */
/*                          Shanks Mestre                                  */
/*                                                                         */
/***************************************************************************/

/* Return the lift of a (mod b), which is closest to h */
static GEN
closest_lift(GEN a, GEN b, GEN h)
{
  return addii(a, mulii(b, diviiround(subii(h,a), b)));
}

static GEN
FlxqE_find_order(GEN f, GEN h, GEN bound, GEN B, GEN a4, GEN T, ulong p)
{
  pari_sp av = avma, av1;
  pari_timer Ti;
  long s = itos( gceil(gsqrt(gdiv(bound,B),DEFAULTPREC)) ) >> 1;
  GEN tx, ti;
  GEN fh = FlxqE_mul(f, h, a4, T, p);
  GEN F, P = fh, fg;
  long i;
  if (DEBUGLEVEL >= 6) timer_start(&Ti);
  if (ell_is_inf(fh)) return h;
  F = FlxqE_mul(f, B, a4, T, p);
  if (s < 3)
  { /* we're nearly done: naive search */
    GEN Q = P;
    for (i=1;; i++)
    {
      P = FlxqE_add(P, F, a4, T, p); /* h.f + i.F */
      if (ell_is_inf(P)) return gerepileupto(av, addii(h, mului(i,B)));
      Q = FlxqE_sub(Q, F, a4, T, p); /* h.f - i.F */
      if (ell_is_inf(Q)) return gerepileupto(av, subii(h, mului(i,B)));
    }
  }
  tx = cgetg(s+1,t_VECSMALL);
  /* Baby Step/Giant Step */
  av1 = avma;
  for (i=1; i<=s; i++)
  { /* baby steps */
    tx[i] = hash_GEN(gel(P, 1));
    P = FlxqE_add(P, F, a4, T, p); /* h.f + i.F */
    if (ell_is_inf(P)) return gerepileupto(av, addii(h, mului(i,B)));
    if (gc_needed(av1,3))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"[Flxq_ellcard] baby steps, i=%ld",i);
      P = gerepileupto(av1,P);
    }
  }
  if (DEBUGLEVEL >= 6) timer_printf(&Ti, "[Flxq_ellcard] baby steps, s = %ld",s);
  /* giant steps: fg = s.F */
  fg = gerepileupto(av1, FlxqE_sub(P, fh, a4, T, p));
  if (ell_is_inf(fg)) return gerepileupto(av,mului(s,B));
  ti = vecsmall_indexsort(tx); /* = permutation sorting tx */
  tx = perm_mul(tx,ti);
  if (DEBUGLEVEL >= 6) timer_printf(&Ti, "[Flxq_ellcard] sorting");
  av1 = avma;
  for (P=fg, i=1; ; i++)
  {
    long k = hash_GEN(gel(P,1));
    long r = zv_search(tx, k);
    if (r)
    {
      while (r && tx[r] == k) r--;
      for (r++; r <= s && tx[r] == k; r++)
      {
        long j = ti[r]-1;
        GEN Q = FlxqE_add(FlxqE_mul(F, stoi(j), a4, T, p), fh, a4, T, p);
        if (DEBUGLEVEL >= 6)
          timer_printf(&Ti, "[Flxq_ellcard] giant steps, i = %ld",i);
        if (Flx_equal(gel(P,1), gel(Q,1)))
        {
          if (Flx_equal(gel(P,2), gel(Q,2))) i = -i;
          return gerepileupto(av,addii(h, mulii(addis(mulss(s,i), j), B)));
        }
      }
    }
    P = FlxqE_add(P,fg,a4,T,p);
    if (gc_needed(av1,3))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"[Flxq_ellcard] giants steps, i=%ld",i);
      P = gerepileupto(av1,P);
    }
  }
}

static void
Flx_next(GEN t, ulong p)
{
  long i;
  for(i=2;;i++)
    if (uel(t,i)==p-1)
      t[i]=0;
    else
    {
      t[i]++;
      break;
    }
}

static void
Flx_renormalize_ip(GEN x, long lx)
{
  long i;
  for (i = lx-1; i>=2; i--)
    if (x[i]) break;
  setlg(x, i+1);
}

static ulong
F3xq_ellcard_naive(GEN a2, GEN a6, GEN T)
{
  pari_sp av = avma;
  long i, d = get_Flx_degree(T), lx = d+2;
  long q = upowuu(3, d), a;
  GEN x = zero_zv(lx); x[1] = get_Flx_var(T);
  for(a=1, i=0; i<q; i++)
  {
    GEN rhs;
    Flx_renormalize_ip(x, lx);
    rhs = Flx_add(Flxq_mul(Flxq_sqr(x, T, 3), Flx_add(x, a2, 3), T, 3), a6, 3);
    if (!lgpol(rhs)) a++; else if (Flxq_issquare(rhs, T, 3)) a+=2;
    Flx_next(x, 3);
  }
  avma = av;
  return a;
}

static ulong
Flxq_ellcard_naive(GEN a4, GEN a6, GEN T, ulong p)
{
  pari_sp av = avma;
  long i, d = get_Flx_degree(T), lx = d+2;
  long q = upowuu(p, d), a;
  GEN x = zero_zv(lx); x[1] = get_Flx_var(T);
  for(a=1, i=0; i<q; i++)
  {
    GEN x2, rhs;
    Flx_renormalize_ip(x, lx);
    x2  = Flxq_sqr(x, T, p);
    rhs = Flx_add(Flxq_mul(x, Flx_add(x2, a4, p), T, p), a6, p);
    if (!lgpol(rhs)) a++; else if (Flxq_issquare(rhs,T,p)) a+=2;
    Flx_next(x,p);
  }
  avma = av;
  return a;
}

/* assume T irreducible mod p, m = (q-1)/(p-1) */
static int
Flxq_kronecker(GEN x, GEN m, GEN T, ulong p)
{
  pari_sp av;
  ulong z;
  if (lgpol(x) == 0) return 0;
  av = avma;
  z = Flxq_pow(x, m, T, p)[2];
  avma = av; return krouu(z, p);
}

/* Find x such that kronecker(u = x^3+a4x+a6, p) is KRO.
 * Return point [x*u,u^2] on E (KRO=1) / E^twist (KRO=-1) */
static GEN
Flxq_ellpoint(long KRO, GEN a4, GEN a6, GEN m, long n, long vn, GEN T, ulong p)
{
  for(;;)
  {
    GEN x = random_Flx(n,vn,p);
    GEN u = Flx_add(a6, Flxq_mul(Flx_add(a4, Flxq_sqr(x,T,p), p), x, T,p), p);
    if (Flxq_kronecker(u, m,T,p) == KRO)
      return mkvec2(Flxq_mul(u,x, T,p), Flxq_sqr(u, T,p));
  }
}

static GEN
Flxq_ellcard_Shanks(GEN a4, GEN a6, GEN q, GEN T, ulong p)
{
  pari_sp av = avma;
  long vn = get_Flx_var(T), n = get_Flx_degree(T), KRO = -1;
  GEN h,f, ta4, A, B, m;
  GEN q1p = addiu(q,1), q2p = shifti(q1p, 1);
  GEN bound = addiu(sqrti(gmul2n(q,4)), 1); /* ceil( 4sqrt(q) ) */
  /* once #E(Flxq) is know mod B >= bound, it is completely determined */
  /* how many 2-torsion points ? */
  switch(FlxqX_nbroots(mkpoln(4, pol1_Flx(vn), pol0_Flx(vn), a4, a6), T, p))
  {
  case 3:  A = gen_0; B = utoipos(4); break;
  case 1:  A = gen_0; B = gen_2; break;
  default: A = gen_1; B = gen_2; break; /* 0 */
  }
  m = diviuexact(subiu(powuu(p,n), 1), p-1);
  for(;;)
  {
    h = closest_lift(A, B, q1p);
    /* [ux, u^2] is on E_u: y^2 = x^3 + c4 u^2 x + c6 u^3
     * E_u isomorphic to E (resp. E') iff KRO = 1 (resp. -1)
     * #E(F_p) = p+1 - a_p, #E'(F_p) = p+1 + a_p
     *
     * #E_u(Flxq) = A (mod B),  h is close to #E_u(Flxq) */
    KRO = -KRO;
    f = Flxq_ellpoint(KRO, a4,a6, m,n,vn, T,p);

    ta4 = Flxq_mul(a4, gel(f,2), T, p); /* a4 for E_u */
    h = FlxqE_find_order(f, h, bound, B, ta4,T,p);
    h = FlxqE_order(f, h, ta4, T, p);
    /* h | #E_u(Flxq) = A (mod B) */
    A = Z_chinese_all(A, gen_0, B, h, &B);
    if (cmpii(B, bound) >= 0) break;
    /* not done, update A mod B for the _next_ curve, isomorphic to
     * the quadratic twist of this one */
    A = remii(subii(q2p,A), B); /* #E(Fq)+#E'(Fq) = 2q+2 */
  }
  h = closest_lift(A, B, q1p);
  return gerepileuptoint(av, KRO == 1? h: subii(q2p,h));
}

static GEN
F3xq_ellcard(GEN a2, GEN a6, GEN T)
{
  long n = get_Flx_degree(T);
  if (n <= 2)
    return utoi(F3xq_ellcard_naive(a2, a6, T));
  else
  {
    GEN q1 = addiu(powuu(3, get_Flx_degree(T)), 1), t;
    GEN a = Flxq_div(a6,Flxq_powu(a2,3,T,3),T,3);
    if (Flx_equal1(Flxq_powu(a, 8, T, 3)))
    {
      GEN P = Flxq_minpoly(a,T,3);
      long dP = degpol(P); /* dP <= 2 */
      ulong q = upowuu(3,dP);
      GEN A2 = pol1_Flx(P[1]), A6 = Flx_rem(polx_Flx(P[1]), P, 3);
      long tP = q + 1 - F3xq_ellcard_naive(A2, A6, P);
      t = elltrace_extension(stoi(tP), n/dP, utoi(q));
      if (umodiu(t, 3)!=1) t = negi(t);
      return Flx_equal1(a2) || Flxq_issquare(a2,T,3) ? subii(q1,t): addii(q1,t);
    }
    else return Flxq_ellcard_Kohel(mkvec(a2), a6, T, 3);
  }
}

static GEN
Flxq_ellcard_Satoh(GEN a4, GEN a6, GEN j, GEN T, ulong p)
{
  long n = get_Flx_degree(T);
  if (n <= 2)
    return utoi(Flxq_ellcard_naive(a4, a6, T, p));
  else
  {
    GEN jp = Flxq_powu(j, p, T, p);
    GEN s = Flx_add(j, jp, p);
    if (degpol(s) <= 0)
    { /* it is assumed j not in F_p */
      GEN m = Flxq_mul(j, jp, T, p);
      if (degpol(m) <= 0)
      {
        GEN q = sqru(p);
        GEN q1 = addiu(powuu(p, get_Flx_degree(T)), 1);
        GEN sk = Flx_Fl_add(Flx_neg(j, p), 1728%p, p);
        GEN sA4 = Flx_triple(Flxq_mul(sk, j, T, p), p);
        GEN u = Flxq_div(a4, sA4, T, p);
        ulong ns = lgpol(s) ? Fl_neg(s[2], p): 0UL;
        GEN P = mkvecsmall4(T[1], m[2], ns, 1L);
        GEN A4, A6, t, tP;
        Flxq_ellj_to_a4a6(polx_Flx(T[1]), P, p, &A4, &A6);
        tP = addis(q, 1 - Flxq_ellcard_naive(A4, A6, P, p));
        t = elltrace_extension(tP, n>>1, q);
        return Flxq_is2npower(u, 2, T, p) ? subii(q1,t): addii(q1,t);
      }
    }
    if (p<=7 || p==13 ) return Flxq_ellcard_Kohel(a4, a6, T, p);
    else return Flxq_ellcard_Harley(a4, a6, T, p);
  }
}

static GEN
Flxq_ellcard_Kedlaya(GEN a4, GEN a6, GEN T, ulong p)
{
  pari_sp av = avma;
  GEN H = mkpoln(4, gen_1, gen_0, Flx_to_ZX(a4), Flx_to_ZX(a6));
  GEN Tp = Flx_to_ZX(get_Flx_mod(T));
  long n = degpol(Tp), e = ((p < 16 ? n+1: n)>>1)+1;
  GEN M = ZlXQX_hyperellpadicfrobenius(H, Tp, p, e);
  GEN N = ZpXQM_prodFrobenius(M, Tp, utoi(p), e);
  GEN q = powuu(p, e);
  GEN tp = Fq_add(gcoeff(N,1,1), gcoeff(N,2,2), Tp, q);
  GEN t = Fp_center_i(typ(tp)==t_INT ? tp: leading_coeff(tp), q, shifti(q,-1));
  return gerepileupto(av, subii(addiu(powuu(p, n), 1), t));
}

GEN
Flxq_ellj(GEN a4, GEN a6, GEN T, ulong p)
{
  pari_sp av=avma;
  if (p==3)
  {
    GEN J;
    if (typ(a4)!=t_VEC) return pol0_Flx(get_Flx_var(T));
    J = Flxq_div(Flxq_powu(gel(a4,1),3, T, p),Flx_neg(a6,p), T, p);
    return gerepileuptoleaf(av, J);
  }
  else
  {
    pari_sp av=avma;
    GEN a43 = Flxq_mul(a4,Flxq_sqr(a4,T,p),T,p);
    GEN a62 = Flxq_sqr(a6,T,p);
    GEN num = Flx_mulu(a43,6912,p);
    GEN den = Flx_add(Flx_mulu(a43,4,p),Flx_mulu(a62,27,p),p);
    return gerepileuptoleaf(av, Flxq_div(num, den, T, p));
  }
}

void
Flxq_ellj_to_a4a6(GEN j, GEN T, ulong p, GEN *pt_a4, GEN *pt_a6)
{
  ulong zagier = 1728 % p;
  if (lgpol(j)==0)
    { *pt_a4 = pol0_Flx(T[1]); *pt_a6 =pol1_Flx(T[1]); }
  else if (lgpol(j)==1 && uel(j,2) == zagier)
    { *pt_a4 = pol1_Flx(T[1]); *pt_a6 =pol0_Flx(T[1]); }
  else
  {
    GEN k = Flx_Fl_add(Flx_neg(j, p), zagier, p);
    GEN kj = Flxq_mul(k, j, T, p);
    GEN k2j = Flxq_mul(kj, k, T, p);
    *pt_a4 = Flx_triple(kj, p);
    *pt_a6 = Flx_double(k2j, p);
  }
}

static GEN
F3xq_ellcardj(GEN a4, GEN a6, GEN T, GEN q, long n)
{
  const ulong p = 3;
  ulong t;
  GEN q1 = addiu(q,1);
  GEN na4 = Flx_neg(a4,p), ra4;
  if (!Flxq_issquare(na4,T,p))
    return q1;
  ra4 = Flxq_sqrt(na4,T,p);
  t = Flxq_trace(Flxq_div(a6,Flxq_mul(na4,ra4,T,p),T,p),T,p);
  if (n%2==1)
  {
    GEN q3;
    if (t==0) return q1;
    q3 = powuu(p,(n+1)>>1);
    return (t==1)^(n%4==1) ? subii(q1,q3): addii(q1,q3);
  }
  else
  {
    GEN q22, q2 = powuu(p,n>>1);
    GEN W = Flxq_pow(a4,shifti(q,-2),T,p);
    long s = (W[2]==1)^(n%4==2);
    if (t!=0) return s ? addii(q1,q2): subii(q1, q2);
    q22 = shifti(q2,1);
    return s ? subii(q1,q22):  addii(q1, q22);
  }
}

static GEN
Flxq_ellcardj(GEN a4, GEN a6, ulong j, GEN T, GEN q, ulong p, long n)
{
  GEN q1 = addiu(q,1);
  if (j==0)
  {
    ulong w;
    GEN W, t, N;
    if (umodiu(q,6)!=1) return q1;
    N = Fp_ffellcard(gen_0,gen_1,q,n,utoi(p));
    t = subii(q1, N);
    W = Flxq_pow(a6,diviuexact(shifti(q,-1), 3),T,p);
    if (degpol(W)>0) /*p=5 mod 6*/
      return Flx_equal1(Flxq_powu(W,3,T,p)) ? addii(q1,shifti(t,-1)):
                                              subii(q1,shifti(t,-1));
    w = W[2];
    if (w==1)   return N;
    if (w==p-1) return addii(q1,t);
    else /*p=1 mod 6*/
    {
      GEN u = shifti(t,-1), v = sqrtint(diviuexact(subii(q,sqri(u)),3));
      GEN a = addii(u,v), b = shifti(v,1);
      if (Fl_powu(w,3,p)==1)
      {
        if (Fl_add(umodiu(a,p),Fl_mul(w,umodiu(b,p),p),p)==0)
          return subii(q1,subii(shifti(b,1),a));
        else
          return addii(q1,addii(a,b));
      }
      else
      {
        if (Fl_sub(umodiu(a,p),Fl_mul(w,umodiu(b,p),p),p)==0)
          return subii(q1,subii(a,shifti(b,1)));
        else
          return subii(q1,addii(a,b));
      }
    }
  } else if (j==1728%p)
  {
    ulong w;
    GEN W, N, t;
    if (mod4(q)==3) return q1;
    W = Flxq_pow(a4,shifti(q,-2),T,p);
    if (degpol(W)>0) return q1; /*p=3 mod 4*/
    w = W[2];
    N = Fp_ffellcard(gen_1,gen_0,q,n,utoi(p));
    if(w==1) return N;
    t = subii(q1, N);
    if(w==p-1) return addii(q1, t);
    else /*p=1 mod 4*/
    {
      GEN u = shifti(t,-1), v = sqrtint(subii(q,sqri(u)));
      if (Fl_add(umodiu(u,p),Fl_mul(w,umodiu(v,p),p),p)==0)
        return subii(q1,shifti(v,1));
      else
        return addii(q1,shifti(v,1));
    }
  } else
  {
    ulong g = Fl_div(j, Fl_sub(1728%p, j, p), p);
    GEN l = Flxq_div(Flx_triple(a6,p),Flx_double(a4,p),T,p);
    GEN N = Fp_ffellcard(utoi(Fl_triple(g,p)),utoi(Fl_double(g,p)),q,n,utoi(p));
    if (Flxq_issquare(l,T,p)) return N;
    return subii(shifti(q1,1),N);
  }
}

GEN
Flxq_ellcard(GEN a4, GEN a6, GEN T, ulong p)
{
  pari_sp av = avma;
  long n = get_Flx_degree(T);
  GEN J, r, q = powuu(p,  n);
  if (typ(a4)==t_VEC)
    r = F3xq_ellcard(gel(a4,1), a6, T);
  else if (p==3)
    r = F3xq_ellcardj(a4, a6, T, q, n);
  else if (degpol(a4)<=0 && degpol(a6)<=0)
    r = Fp_ffellcard(utoi(Flx_eval(a4,0,p)),utoi(Flx_eval(a6,0,p)),q,n,utoi(p));
  else if (degpol(J=Flxq_ellj(a4,a6,T,p))<=0)
    r = Flxq_ellcardj(a4,a6,lgpol(J)?J[2]:0,T,q,p,n);
  else if (p <= 7)
    r = Flxq_ellcard_Satoh(a4, a6, J, T, p);
  else if (cmpis(q,100)<0)
    r = utoi(Flxq_ellcard_naive(a4, a6, T, p));
  else if (p == 13 || (7*p <= (ulong)10*n && (BITS_IN_LONG==64 || p <= 103)))
    r = Flxq_ellcard_Satoh(a4, a6, J, T, p);
  else if (p <= (ulong)2*n)
    r = Flxq_ellcard_Kedlaya(a4, a6, T, p);
  else if (expi(q)<=62)
    r = Flxq_ellcard_Shanks(a4, a6, q, T, p);
  else
    r = Fq_ellcard_SEA(Flx_to_ZX(a4),Flx_to_ZX(a6),q,Flx_to_ZX(T),utoi(p),0);
  return gerepileuptoint(av, r);
}
