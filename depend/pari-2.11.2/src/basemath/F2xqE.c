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

/* Not so fast arithmetic with points over elliptic curves over F_2^n */

/***********************************************************************/
/**                                                                   **/
/**                              F2xqE                                **/
/**                                                                   **/
/***********************************************************************/

/* Theses functions deal with point over elliptic curves over F_2^n defined
 * by an equation of the form:
 ** y^2+x*y=x^3+a_2*x^2+a_6 if the curve is ordinary.
 ** y^2+a_3*y=x^3+a_4*x+a_6 if the curve is supersingular.
 * Most of the time a6 is omitted since it can be recovered from any point
 * on the curve.
 * For supersingular curves, the parameter a2 is replaced by [a3,a4,a3^-1].
 */

GEN
RgE_to_F2xqE(GEN x, GEN T)
{
  if (ell_is_inf(x)) return x;
  retmkvec2(Rg_to_F2xq(gel(x,1),T),Rg_to_F2xq(gel(x,2),T));
}

GEN
F2xqE_changepoint(GEN x, GEN ch, GEN T)
{
  pari_sp av = avma;
  GEN p1,z,u,r,s,t,v,v2,v3;
  if (ell_is_inf(x)) return x;
  u = gel(ch,1); r = gel(ch,2);
  s = gel(ch,3); t = gel(ch,4);
  v = F2xq_inv(u, T); v2 = F2xq_sqr(v, T); v3 = F2xq_mul(v,v2, T);
  p1 = F2x_add(gel(x,1),r);
  z = cgetg(3,t_VEC);
  gel(z,1) = F2xq_mul(v2, p1, T);
  gel(z,2) = F2xq_mul(v3, F2x_add(gel(x,2), F2x_add(F2xq_mul(s, p1, T),t)), T);
  return gerepileupto(av, z);
}

GEN
F2xqE_changepointinv(GEN x, GEN ch, GEN T)
{
  GEN u, r, s, t, X, Y, u2, u3, u2X, z;
  if (ell_is_inf(x)) return x;
  X = gel(x,1); Y = gel(x,2);
  u = gel(ch,1); r = gel(ch,2);
  s = gel(ch,3); t = gel(ch,4);
  u2 = F2xq_sqr(u, T); u3 = F2xq_mul(u,u2, T);
  u2X = F2xq_mul(u2,X, T);
  z = cgetg(3, t_VEC);
  gel(z,1) = F2x_add(u2X,r);
  gel(z,2) = F2x_add(F2xq_mul(u3,Y, T), F2x_add(F2xq_mul(s,u2X, T), t));
  return z;
}

static GEN
nonzerotrace_F2xq(GEN T)
{
  pari_sp av = avma;
  long n = F2x_degree(T), vs = T[1];
  GEN a;
  if (odd(n))
    return pol1_F2x(vs);
  do
  {
    avma = av;
    a = random_F2x(n, vs);
  } while (F2xq_trace(a, T)==0);
  return a;
}

void
F2xq_elltwist(GEN a, GEN a6, GEN T, GEN *pt_a, GEN *pt_a6)
{
  pari_sp av = avma;
  GEN n = nonzerotrace_F2xq(T);
  if (typ(a)==t_VECSMALL)
  {
    *pt_a = gerepileuptoleaf(av, F2x_add(n, a));
    *pt_a6 = vecsmall_copy(a6);
  } else
  {
    GEN a6t = F2x_add(a6, F2xq_mul(n, F2xq_sqr(gel(a,1), T), T));
    *pt_a6 = gerepileuptoleaf(av, a6t);
    *pt_a = vecsmall_copy(a);
  }
}

static GEN
F2xqE_dbl_slope(GEN P, GEN a, GEN T, GEN *slope)
{
  GEN x, y, Q;
  if (ell_is_inf(P)) return ellinf();
  x = gel(P,1); y = gel(P,2);
  if (typ(a)==t_VECSMALL)
  {
    GEN a2 = a;
    if (!lgpol(gel(P,1))) return ellinf();
    *slope = F2x_add(x, F2xq_div(y, x, T));
    Q = cgetg(3,t_VEC);
    gel(Q, 1) = F2x_add(F2xq_sqr(*slope, T), F2x_add(*slope, a2));
    gel(Q, 2) = F2x_add(F2xq_mul(*slope, F2x_add(x, gel(Q, 1)), T), F2x_add(y, gel(Q, 1)));
  }
  else
  {
    GEN a3 = gel(a,1), a4 = gel(a,2), a3i = gel(a,3);
    *slope = F2xq_mul(F2x_add(a4, F2xq_sqr(x, T)), a3i, T);
    Q = cgetg(3,t_VEC);
    gel(Q, 1) = F2xq_sqr(*slope, T);
    gel(Q, 2) = F2x_add(F2xq_mul(*slope, F2x_add(x, gel(Q, 1)), T), F2x_add(y, a3));
  }
  return Q;
}

GEN
F2xqE_dbl(GEN P, GEN a, GEN T)
{
  pari_sp av = avma;
  GEN slope;
  return gerepileupto(av, F2xqE_dbl_slope(P, a, T,&slope));
}

static GEN
F2xqE_add_slope(GEN P, GEN Q, GEN a, GEN T, GEN *slope)
{
  GEN Px, Py, Qx, Qy, R;
  if (ell_is_inf(P)) return Q;
  if (ell_is_inf(Q)) return P;
  Px = gel(P,1); Py = gel(P,2);
  Qx = gel(Q,1); Qy = gel(Q,2);
  if (F2x_equal(Px, Qx))
  {
    if (F2x_equal(Py, Qy))
      return F2xqE_dbl_slope(P, a, T, slope);
    else
      return ellinf();
  }
  *slope = F2xq_div(F2x_add(Py, Qy), F2x_add(Px, Qx), T);
  R = cgetg(3,t_VEC);
  if (typ(a)==t_VECSMALL)
  {
    GEN a2 = a;
    gel(R, 1) = F2x_add(F2x_add(F2x_add(F2x_add(F2xq_sqr(*slope, T), *slope), Px), Qx), a2);
    gel(R, 2) = F2x_add(F2xq_mul(*slope, F2x_add(Px, gel(R, 1)), T), F2x_add(Py, gel(R, 1)));
  }
  else
  {
    GEN a3 = gel(a,1);
    gel(R, 1) = F2x_add(F2x_add(F2xq_sqr(*slope, T), Px), Qx);
    gel(R, 2) = F2x_add(F2xq_mul(*slope, F2x_add(Px, gel(R, 1)), T), F2x_add(Py, a3));
  }
  return R;
}

GEN
F2xqE_add(GEN P, GEN Q, GEN a, GEN T)
{
  pari_sp av = avma;
  GEN slope;
  return gerepileupto(av, F2xqE_add_slope(P, Q, a, T, &slope));
}

static GEN
F2xqE_neg_i(GEN P, GEN a)
{
  GEN LHS;
  if (ell_is_inf(P)) return P;
  LHS = typ(a)==t_VECSMALL ? gel(P,1): gel(a,1);
  return mkvec2(gel(P,1), F2x_add(LHS, gel(P,2)));
}

GEN
F2xqE_neg(GEN P, GEN a, GEN T)
{
  GEN LHS;
  (void) T;
  if (ell_is_inf(P)) return ellinf();
  LHS = typ(a)==t_VECSMALL ? gel(P,1): gel(a,1);
  return mkvec2(gcopy(gel(P,1)), F2x_add(LHS, gel(P,2)));
}

GEN
F2xqE_sub(GEN P, GEN Q, GEN a2, GEN T)
{
  pari_sp av = avma;
  GEN slope;
  return gerepileupto(av, F2xqE_add_slope(P, F2xqE_neg_i(Q, a2), a2, T, &slope));
}

struct _F2xqE
{
  GEN a2, a6;
  GEN T;
};

static GEN
_F2xqE_dbl(void *E, GEN P)
{
  struct _F2xqE *ell = (struct _F2xqE *) E;
  return F2xqE_dbl(P, ell->a2, ell->T);
}

static GEN
_F2xqE_add(void *E, GEN P, GEN Q)
{
  struct _F2xqE *ell=(struct _F2xqE *) E;
  return F2xqE_add(P, Q, ell->a2, ell->T);
}

static GEN
_F2xqE_mul(void *E, GEN P, GEN n)
{
  pari_sp av = avma;
  struct _F2xqE *e=(struct _F2xqE *) E;
  long s = signe(n);
  if (!s || ell_is_inf(P)) return ellinf();
  if (s<0) P = F2xqE_neg(P, e->a2, e->T);
  if (is_pm1(n)) return s>0? gcopy(P): P;
  return gerepileupto(av, gen_pow(P, n, e, &_F2xqE_dbl, &_F2xqE_add));
}

GEN
F2xqE_mul(GEN P, GEN n, GEN a2, GEN T)
{
  struct _F2xqE E;
  E.a2 = a2; E.T = T;
  return _F2xqE_mul(&E, P, n);
}

/* Finds a random non-singular point on E */
GEN
random_F2xqE(GEN a, GEN a6, GEN T)
{
  pari_sp ltop = avma;
  GEN x, y, rhs, u;
  do
  {
    avma= ltop;
    x   = random_F2x(F2x_degree(T),T[1]);
    if (typ(a) == t_VECSMALL)
    {
      GEN a2 = a, x2;
      if (!lgpol(x))
        { avma=ltop; retmkvec2(pol0_Flx(T[1]), F2xq_sqrt(a6,T)); }
      u = x; x2  = F2xq_sqr(x, T);
      rhs = F2x_add(F2xq_mul(x2,F2x_add(x,a2),T),a6);
      rhs = F2xq_div(rhs,x2,T);
    }
    else
    {
      GEN a3 = gel(a,1), a4 = gel(a,2), a3i = gel(a,3), u2i;
      u = a3; u2i = F2xq_sqr(a3i,T);
      rhs = F2x_add(F2xq_mul(x,F2x_add(F2xq_sqr(x,T),a4),T),a6);
      rhs = F2xq_mul(rhs,u2i,T);
    }
  } while (F2xq_trace(rhs,T));
  y = F2xq_mul(F2xq_Artin_Schreier(rhs, T), u, T);
  return gerepilecopy(ltop, mkvec2(x, y));
}

static GEN
_F2xqE_rand(void *E)
{
  struct _F2xqE *ell=(struct _F2xqE *) E;
  return random_F2xqE(ell->a2, ell->a6, ell->T);
}

static const struct bb_group F2xqE_group={_F2xqE_add,_F2xqE_mul,_F2xqE_rand,hash_GEN,zvV_equal,ell_is_inf, NULL};

const struct bb_group *
get_F2xqE_group(void ** pt_E, GEN a2, GEN a6, GEN T)
{
  struct _F2xqE *e = (struct _F2xqE *) stack_malloc(sizeof(struct _F2xqE));
  e->a2 = a2; e->a6 = a6; e->T = T;
  *pt_E = (void *) e;
  return &F2xqE_group;
}

GEN
F2xqE_order(GEN z, GEN o, GEN a2, GEN T)
{
  pari_sp av = avma;
  struct _F2xqE e;
  e.a2=a2; e.T=T;
  return gerepileuptoint(av, gen_order(z, o, (void*)&e, &F2xqE_group));
}

GEN
F2xqE_log(GEN a, GEN b, GEN o, GEN a2, GEN T)
{
  pari_sp av = avma;
  struct _F2xqE e;
  e.a2=a2; e.T=T;
  return gerepileuptoint(av, gen_PH_log(a, b, o, (void*)&e, &F2xqE_group));
}

/***********************************************************************/
/**                                                                   **/
/**                            Pairings                               **/
/**                                                                   **/
/***********************************************************************/

/* Derived from APIP from and by Jerome Milan, 2012 */

static long
is_2_torsion(GEN Q, GEN a)
{
  return (typ(a)==t_VEC || lgpol(gel(Q, 1))) ? 0: 1;
}

static GEN
F2xqE_vert(GEN P, GEN Q, GEN a, GEN T)
{
  long vT = T[1];
  if (ell_is_inf(P))
    return pol1_F2x(T[1]);
  if (!F2x_equal(gel(Q, 1), gel(P, 1)))
    return F2x_add(gel(Q, 1), gel(P, 1));
  if (is_2_torsion(Q, a))
    return F2xq_inv(gel(Q,2), T);
  return pol1_F2x(vT);
}

static GEN
F2xqE_Miller_line(GEN R, GEN Q, GEN slope, GEN a, GEN T)
{
  long vT = T[1];
  GEN x = gel(Q, 1), y = gel(Q, 2);
  GEN tmp1 = F2x_add(x, gel(R, 1));
  GEN tmp2 = F2x_add(F2xq_mul(tmp1, slope, T), gel(R, 2));
  GEN s1, s2, ix;
  if (!F2x_equal(y, tmp2))
    return F2x_add(y, tmp2);
  if (is_2_torsion(Q, a)) return pol1_F2x(vT);
  if (typ(a)==t_VEC)
  {
    GEN a4 = gel(a,2), a3i = gel(a,3);
    s1 = F2xq_mul(F2x_add(a4, F2xq_sqr(x, T)), a3i, T);
    if (!F2x_equal(s1, slope))
      return F2x_add(s1, slope);
    s2 = F2xq_mul(F2x_add(x, F2xq_sqr(s1, T)), a3i, T);
    if (lgpol(s2)) return s2;
    return zv_copy(a3i);
  } else
  {
    GEN a2 = a ;
    ix = F2xq_inv(x, T);
    s1 = F2x_add(x, F2xq_mul(y, ix, T));
    if (!F2x_equal(s1, slope))
      return F2x_add(s1, slope);
    s2 =F2x_add(a2, F2x_add(F2xq_sqr(s1,T), s1));
    if (!F2x_equal(s2, x))
      return  F2x_add(pol1_F2x(vT), F2xq_mul(s2, ix, T));
    return ix;
  }
}

/* Computes the equation of the line tangent to R and returns its
   evaluation at the point Q. Also doubles the point R.
 */

static GEN
F2xqE_tangent_update(GEN R, GEN Q, GEN a2, GEN T, GEN *pt_R)
{
  if (ell_is_inf(R))
  {
    *pt_R = ellinf();
    return pol1_F2x(T[1]);
  }
  else if (is_2_torsion(R, a2))
  {
    *pt_R = ellinf();
    return F2xqE_vert(R, Q, a2, T);
  } else {
    GEN slope;
    *pt_R = F2xqE_dbl_slope(R, a2, T, &slope);
    return F2xqE_Miller_line(R, Q, slope, a2, T);
  }
}

/* Computes the equation of the line through R and P, and returns its
   evaluation at the point Q. Also adds P to the point R.
 */

static GEN
F2xqE_chord_update(GEN R, GEN P, GEN Q, GEN a2, GEN T, GEN *pt_R)
{
  if (ell_is_inf(R))
  {
    *pt_R = gcopy(P);
    return F2xqE_vert(P, Q, a2, T);
  }
  else if (ell_is_inf(P))
  {
    *pt_R = gcopy(R);
    return F2xqE_vert(R, Q, a2, T);
  }
  else if (F2x_equal(gel(P, 1), gel(R, 1)))
  {
    if (F2x_equal(gel(P, 2), gel(R, 2)))
      return F2xqE_tangent_update(R, Q, a2, T, pt_R);
    else
    {
      *pt_R = ellinf();
      return F2xqE_vert(R, Q, a2, T);
    }
  } else {
    GEN slope;
    *pt_R = F2xqE_add_slope(P, R, a2, T, &slope);
    return F2xqE_Miller_line(R, Q, slope, a2, T);
  }
}

/* Returns the Miller function f_{m, Q} evaluated at the point P using
   the standard Miller algorithm.
 */

struct _F2xqE_miller
{
  GEN T, a2, P;
};

static GEN
F2xqE_Miller_dbl(void* E, GEN d)
{
  struct _F2xqE_miller *m = (struct _F2xqE_miller *)E;
  GEN T = m->T, a2 = m->a2, P = m->P;
  GEN v, line;
  GEN num = F2xq_sqr(gel(d,1), T);
  GEN denom = F2xq_sqr(gel(d,2), T);
  GEN point = gel(d,3);
  line = F2xqE_tangent_update(point, P, a2, T, &point);
  num  = F2xq_mul(num, line, T);
  v = F2xqE_vert(point, P, a2, T);
  denom = F2xq_mul(denom, v, T);
  return mkvec3(num, denom, point);
}

static GEN
F2xqE_Miller_add(void* E, GEN va, GEN vb)
{
  struct _F2xqE_miller *m = (struct _F2xqE_miller *)E;
  GEN T = m->T, a2 = m->a2, P = m->P;
  GEN v, line, point;
  GEN na = gel(va,1), da = gel(va,2), pa = gel(va,3);
  GEN nb = gel(vb,1), db = gel(vb,2), pb = gel(vb,3);
  GEN num   = F2xq_mul(na, nb, T);
  GEN denom = F2xq_mul(da, db, T);
  line = F2xqE_chord_update(pa, pb, P, a2, T, &point);
  num  = F2xq_mul(num, line, T);
  v = F2xqE_vert(point, P, a2, T);
  denom = F2xq_mul(denom, v, T);
  return mkvec3(num, denom, point);
}

static GEN
F2xqE_Miller(GEN Q, GEN P, GEN m, GEN a2, GEN T)
{
  pari_sp ltop = avma;
  struct _F2xqE_miller d;
  GEN v, num, denom, g1;

  d.a2 = a2; d.T = T; d.P = P;
  g1 = pol1_F2x(T[1]);
  v = gen_pow(mkvec3(g1,g1,Q), m, (void*)&d, F2xqE_Miller_dbl, F2xqE_Miller_add);
  num = gel(v,1); denom = gel(v,2);
  return gerepileupto(ltop, F2xq_div(num, denom, T));
}

GEN
F2xqE_weilpairing(GEN P, GEN Q, GEN m, GEN a2, GEN T)
{
  pari_sp ltop = avma;
  GEN num, denom, result;
  if (ell_is_inf(P) || ell_is_inf(Q) || F2x_equal(P,Q))
    return pol1_F2x(T[1]);
  num    = F2xqE_Miller(P, Q, m, a2, T);
  denom  = F2xqE_Miller(Q, P, m, a2, T);
  result = F2xq_div(num, denom, T);
  return gerepileupto(ltop, result);
}

GEN
F2xqE_tatepairing(GEN P, GEN Q, GEN m, GEN a2, GEN T)
{
  if (ell_is_inf(P) || ell_is_inf(Q))
    return pol1_F2x(T[1]);
  return F2xqE_Miller(P, Q, m, a2, T);
}

/***********************************************************************/
/**                                                                   **/
/**                          Point counting                           **/
/**                                                                   **/
/***********************************************************************/

static GEN
Z2x_rshift(GEN y, long x)
{
  GEN z;
  long i, l;
  if (!x) return pol0_Flx(y[1]);
  z = cgetg_copy(y, &l); z[1] = y[1];
  for(i=2; i<l; i++) z[i] = y[i]>>x;
  return Flx_renormalize(z, l);
}

/* Solve the linear equation approximation in the Newton algorithm */

static GEN
gen_Z2x_Dixon(GEN F, GEN V, long N, void *E, GEN lin(void *E, GEN F, GEN d, long N), GEN invl(void *E, GEN d))
{
  pari_sp av = avma;
  long N2, M;
  GEN VN2, V2, VM, bil;
  ulong q = 1UL<<N;
  if (N == 1) return invl(E, V);
  V = Flx_red(V, q);
  N2 = (N + 1)>>1; M = N - N2;
  F = FlxT_red(F, q);
  VN2 = gen_Z2x_Dixon(F, V, N2, E, lin, invl);
  bil = lin(E, F, VN2, N);
  V2 = Z2x_rshift(Flx_sub(V, bil, q), N2);
  VM = gen_Z2x_Dixon(F, V2, M, E, lin, invl);
  return gerepileupto(av, Flx_add(VN2, Flx_Fl_mul(VM, 1UL<<N2, q), q));
}

/* Solve F(X) = V mod 2^N
   F(Xn) = V [mod 2^n]
   Vm = (V-F(Xn))/(2^n)
   F(Xm) = Vm
   X = Xn + 2^n*Xm
*/

static GEN
gen_Z2X_Dixon(GEN F, GEN V, long N, void *E,
                     GEN lin(void *E, GEN F, GEN d, long N),
                     GEN lins(void *E, GEN F, GEN d, long N),
                     GEN invls(void *E, GEN d))
{
  pari_sp av = avma;
  long n, m;
  GEN Xn, Xm, FXn, Vm;
  if (N<BITS_IN_LONG)
  {
    ulong q = 1UL<<N;
    return Flx_to_ZX(gen_Z2x_Dixon(ZXT_to_FlxT(F,q), ZX_to_Flx(V,q),N,E,lins,invls));
  }
  V = ZX_remi2n(V, N);
  n = (N + 1)>>1; m = N - n;
  F = ZXT_remi2n(F, N);
  Xn = gen_Z2X_Dixon(F, V, n, E, lin, lins, invls);
  FXn = lin(E, F, Xn, N);
  Vm = ZX_shifti(ZX_sub(V, FXn), -n);
  Xm = gen_Z2X_Dixon(F, Vm, m, E, lin, lins, invls);
  return gerepileupto(av, ZX_remi2n(ZX_add(Xn, ZX_shifti(Xm, n)), N));
}

/* H -> H mod 2*/

static GEN _can_invls(void *E, GEN V) {(void) E; return V; }

/* H -> H-(f0*H0-f1*H1) */

static GEN _can_lin(void *E, GEN F, GEN V, long N)
{
  pari_sp av=avma;
  GEN d0, d1, z;
  (void) E;
  RgX_even_odd(V, &d0, &d1);
  z =  ZX_sub(V, ZX_sub(ZX_mul(gel(F,1), d0), ZX_mul(gel(F,2), d1)));
  return gerepileupto(av, ZX_remi2n(z, N));
}

static GEN _can_lins(void *E, GEN F, GEN V, long N)
{
  GEN D=Flx_splitting(V, 2), z;
  ulong q = 1UL<<N;
  (void) E;
  z = Flx_sub(Flx_mul(gel(F,1), gel(D,1), q), Flx_mul(gel(F,2), gel(D,2), q), q);
  return Flx_sub(V, z, q);
}

/* P -> P-(P0^2-X*P1^2) */

static GEN
_can_iter(void *E, GEN f2, GEN q)
{
  GEN f0, f1, z;
  (void) E;
  RgX_even_odd(f2, &f0, &f1);
  z = ZX_add(ZX_sub(f2, FpX_sqr(f0, q)), RgX_shift_shallow(FpX_sqr(f1, q), 1));
  return mkvec3(z,f0,f1);
}

/* H -> H-(2*P0*H0-2*X*P1*H1) */

static GEN
_can_invd(void *E, GEN V, GEN v, GEN q, long M)
{
  GEN F;
  (void)E; (void)q;
  F = mkvec2(ZX_shifti(gel(v,2),1), ZX_shifti(RgX_shift_shallow(gel(v,3),1),1));
  return gen_Z2X_Dixon(F, V, M, NULL, _can_lin, _can_lins, _can_invls);
}

/* Lift P to Q such that Q(x^2)=Q(x)*Q(-x) mod 2^n
   if Q = Q0(X^2)+X*Q1(X^2), solve Q(x^2) = Q0^2-X*Q1^2
*/
static GEN
F2x_canonlift(GEN P, long n)
{ return gen_ZpX_Newton(F2x_to_ZX(P),gen_2, n, NULL, _can_iter, _can_invd); }

static GEN
Z2XQ_frob(GEN x, GEN T, GEN q)
{
  return FpX_rem(RgX_inflate(x, 2), T, q);
}

static GEN
Z2xq_frob(GEN x, GEN T, ulong q)
{
  return Flx_rem(Flx_inflate(x, 2), T, q);
}

struct _frob_lift
{
  GEN T, sqx;
};

/* H -> S^-1(H) mod 2 */

static GEN _frob_invls(void *E, GEN V)
{
  struct _frob_lift *F = (struct _frob_lift*) E;
  GEN sqx = F->sqx;
  return F2x_to_Flx(F2xq_sqrt_fast(Flx_to_F2x(V), gel(sqx,1), gel(sqx,2)));
}

/* H -> f1*S(H) + f2*H */

static GEN _frob_lin(void *E, GEN F, GEN x2, long N)
{
  GEN T = gel(F,3);
  GEN q = int2n(N);
  GEN y2  = Z2XQ_frob(x2, T, q);
  GEN lin = ZX_add(ZX_mul(gel(F,1), y2), ZX_mul(gel(F,2), x2));
  (void) E;
  return FpX_rem(ZX_remi2n(lin, N), T, q);
}

static GEN _frob_lins(void *E, GEN F, GEN x2, long N)
{
  GEN T = gel(F,3);
  ulong q = 1UL<<N;
  GEN y2  = Z2xq_frob(x2, T, q);
  GEN lin = Flx_add(Flx_mul(gel(F,1), y2,q), Flx_mul(gel(F,2), x2,q),q);
  (void) E;
  return Flx_rem(lin, T, q);
}

/* X -> P(X,S(X)) */

static GEN
_lift_iter(void *E, GEN x2, GEN q)
{
  struct _frob_lift *F = (struct _frob_lift*) E;
  long N = expi(q);
  GEN TN = ZXT_remi2n(F->T, N);
  GEN y2 = Z2XQ_frob(x2, TN, q);
  GEN x2y2 = FpX_rem(ZX_remi2n(ZX_mul(x2, y2), N), TN, q);
  GEN s = ZX_add(ZX_add(x2, ZX_shifti(y2, 1)), ZX_shifti(x2y2, 3));
  GEN V = ZX_add(ZX_add(ZX_sqr(s), y2), ZX_shifti(x2y2, 2));
  return mkvec4(FpX_rem(ZX_remi2n(V, N), TN, q),x2,y2,s);
}

/* H -> Dx*H+Dy*S(H) */

static GEN
_lift_invd(void *E, GEN V, GEN v, GEN qM, long M)
{
  struct _frob_lift *F = (struct _frob_lift*) E;
  GEN TM = ZXT_remi2n(F->T, M);
  GEN x2 = gel(v,2), y2 = gel(v,3), s = gel(v,4), r;
  GEN Dx = ZX_add(ZX_mul(ZX_Z_add(ZX_shifti(y2, 4), gen_2), s),
                         ZX_shifti(y2, 2));
  GEN Dy = ZX_add(ZX_Z_add(ZX_mul(ZX_Z_add(ZX_shifti(x2, 4), utoi(4)), s),
                           gen_1), ZX_shifti(x2, 2));
  Dx = FpX_rem(ZX_remi2n(Dx, M), TM, qM);
  Dy = FpX_rem(ZX_remi2n(Dy, M), TM, qM);
  r = mkvec3(Dy, Dx, TM);
  return gen_Z2X_Dixon(r, V, M, E, _frob_lin, _frob_lins, _frob_invls);
}

/*
  Let P(X,Y)=(X+2*Y+8*X*Y)^2+Y+4*X*Y
  Solve   P(x,S(x))=0 [mod 2^n,T]
  assuming  x = x0    [mod 2,T]

  we set s = X+2*Y+8*X*Y, P = s^2+Y+4*X*Y
  Dx = dP/dx = (16*s+4)*x+(4*s+1)
  Dy = dP/dy = (16*y+2)*s+4*y
*/

static GEN
solve_AGM_eqn(GEN x0, long n, GEN T, GEN sqx)
{
  struct _frob_lift F;
  F.T=T; F.sqx=sqx;
  return gen_ZpX_Newton(x0, gen_2, n, &F, _lift_iter, _lift_invd);
}

static GEN
Z2XQ_invnorm_pcyc(GEN a, GEN T, long e)
{
  GEN q = int2n(e);
  GEN z = ZpXQ_norm_pcyc(a, T, q, gen_2);
  return Fp_inv(z, q);
}

/* Assume a = 1 [4] */
static GEN
Z2XQ_invnorm(GEN a, GEN T, long e)
{
  pari_timer ti;
  GEN pe = int2n(e), s;
  if (degpol(a)==0)
    return Fp_inv(Fp_powu(gel(a,2), get_FpX_degree(T), pe), pe);
  if (DEBUGLEVEL>=3) timer_start(&ti);
  s = ZpXQ_log(a, T, gen_2, e);
  if (DEBUGLEVEL>=3) timer_printf(&ti,"Z2XQ_log");
  s = Fp_neg(FpXQ_trace(s, T, pe), pe);
  if (DEBUGLEVEL>=3) timer_printf(&ti,"FpXQ_trace");
  s = modii(gel(Qp_exp(cvtop(s, gen_2, e-2)),4),pe);
  if (DEBUGLEVEL>=3) timer_printf(&ti,"Qp_exp");
  return s;
}

/* Assume a2==0, so 4|E(F_p): if t^4 = a6 then (t,t^2) is of order 4
   8|E(F_p) <=> trace(a6)==0
 */

static GEN
F2xq_elltrace_Harley(GEN a6, GEN T2)
{
  pari_sp ltop = avma;
  pari_timer ti;
  GEN T, sqx;
  GEN x, x2, t;
  long n = F2x_degree(T2), N = ((n + 1)>>1) + 2;
  long ispcyc;
  if (n==1) return gen_m1;
  if (n==2) return F2x_degree(a6) ? gen_1 : stoi(-3);
  if (n==3) return F2x_degree(a6) ? (F2xq_trace(a6,T2) ?  stoi(-3): gen_1)
                                  : stoi(5);
  timer_start(&ti);
  sqx = mkvec2(F2xq_sqrt(polx_F2x(T2[1]),T2), T2);
  if (DEBUGLEVEL>1) timer_printf(&ti,"Sqrtx");
  ispcyc = zx_is_pcyc(F2x_to_Flx(T2));
  T = ispcyc? F2x_to_ZX(T2): F2x_canonlift(T2, N-2);
  if (DEBUGLEVEL>1) timer_printf(&ti,"Teich");
  T = FpX_get_red(T, int2n(N));
  if (DEBUGLEVEL>1) timer_printf(&ti,"Barrett");
  x = solve_AGM_eqn(F2x_to_ZX(a6), N-2, T, sqx);
  if (DEBUGLEVEL>1) timer_printf(&ti,"Lift");
  x2 = ZX_Z_add_shallow(ZX_shifti(x,2), gen_1);
  t = (ispcyc? Z2XQ_invnorm_pcyc: Z2XQ_invnorm)(x2, T, N);
  if (DEBUGLEVEL>1) timer_printf(&ti,"Norm");
  if (cmpii(sqri(t), int2n(n + 2)) > 0)
    t = subii(t, int2n(N));
  return gerepileuptoint(ltop, t);
}

static GEN
get_v(GEN u, GEN a, GEN T)
{
  GEN a4 = gel(a,2), a3i = gel(a,3);
  GEN ui2 = F2xq_mul(u, a3i, T), ui4 = F2xq_sqr(ui2, T);
  return F2xq_mul(a4, ui4, T);
}

static GEN
get_r(GEN w, GEN u, GEN T)
{
  return F2xq_sqr(F2xq_mul(F2xq_Artin_Schreier(w, T), u, T), T);
}

static GEN
F2xq_elltracej(GEN a, GEN a6, GEN T, GEN q, long n)
{
  GEN a3 = gel(a,1), a4 = gel(a,2), a3i = gel(a,3);
  GEN r, pi, rhs;
  long t, s, m = n >> 1;
  if (odd(n))
  {
    GEN u, v, w;
    u = F2xq_pow(a3,diviuexact(subiu(shifti(q,1), 1), 3),T);
    v = get_v(u, a, T);
    if (F2xq_trace(v, T)==0) return gen_0;
    w = F2xq_Artin_Schreier(F2x_1_add(v), T);
    if (F2xq_trace(w, T)) w = F2x_1_add(w);
    r = get_r(w, u, T);
    pi = int2n(m+1);
    s = (((m+3)&3L) <= 1) ? -1: 1;
  }
  else
  {
    if (F2x_degree(F2xq_pow(a3,diviuexact(subiu(q, 1), 3),T))==0)
    {
      GEN u, v, w;
      u = F2xq_sqrtn(a3, utoi(3), T, NULL);
      v = get_v(u, a, T);
      if (F2xq_trace(v, T)==1) return gen_0;
      w = F2xq_Artin_Schreier(v, T);
      if (F2xq_trace(w, T)==1) return gen_0;
      r = get_r(w, u, T);
      pi = int2n(m+1);
      s = odd(m+1) ? -1: 1;
    }
    else
    {
      long sv = T[1];
      GEN P = mkpoln(5, pol1_F2x(sv), pol0_F2x(sv), pol0_F2x(sv), a3, a4);
      r = F2xq_sqr(gel(F2xqX_roots(P,T), 1), T);
      pi = int2n(m);
      s = odd(m) ? -1: 1;
    }
  }
  rhs = F2x_add(F2xq_mul(F2x_add(F2xq_sqr(r, T), a4), r, T), a6);
  t = F2xq_trace(F2xq_mul(rhs, F2xq_sqr(a3i, T), T), T);
  return (t==0)^(s==1)? pi: negi(pi);
}

GEN
F2xq_ellcard(GEN a, GEN a6, GEN T)
{
  pari_sp av = avma;
  long n = F2x_degree(T);
  GEN c;
  if (typ(a)==t_VECSMALL)
  {
    GEN t = F2xq_elltrace_Harley(a6, T);
    c = addii(int2u(n), F2xq_trace(a,T) ? addui(1,t): subui(1,t));
  } else if (n==1)
  {
    long a4i = lgpol(gel(a,2)), a6i = lgpol(a6);
    return utoi(a4i? (a6i? 1: 5): 3);
  }
  else
  {
    GEN q = int2u(n);
    c = subii(addiu(q,1), F2xq_elltracej(a, a6, T, q, n));
  }
  return gerepileuptoint(av, c);
}

/***********************************************************************/
/**                                                                   **/
/**                          Group structure                          **/
/**                                                                   **/
/***********************************************************************/

static GEN
_F2xqE_pairorder(void *E, GEN P, GEN Q, GEN m, GEN F)
{
  struct _F2xqE *e = (struct _F2xqE *) E;
  return  F2xq_order(F2xqE_weilpairing(P,Q,m,e->a2,e->T), F, e->T);
}

GEN
F2xq_ellgroup(GEN a2, GEN a6, GEN N, GEN T, GEN *pt_m)
{
  struct _F2xqE e;
  GEN q = int2u(F2x_degree(T));
  e.a2=a2; e.a6=a6; e.T=T;
  return gen_ellgroup(N, subiu(q,1), pt_m, (void*)&e, &F2xqE_group,
                                                      _F2xqE_pairorder);
}

GEN
F2xq_ellgens(GEN a2, GEN a6, GEN ch, GEN D, GEN m, GEN T)
{
  GEN P;
  pari_sp av = avma;
  struct _F2xqE e;
  e.a2=a2; e.a6=a6; e.T=T;
  switch(lg(D)-1)
  {
  case 0:
    return cgetg(1,t_VEC);
  case 1:
    P = gen_gener(gel(D,1), (void*)&e, &F2xqE_group);
    P = mkvec(F2xqE_changepoint(P, ch, T));
    break;
  default:
    P = gen_ellgens(gel(D,1), gel(D,2), m, (void*)&e, &F2xqE_group,
                                                      _F2xqE_pairorder);
    gel(P,1) = F2xqE_changepoint(gel(P,1), ch, T);
    gel(P,2) = F2xqE_changepoint(gel(P,2), ch, T);
    break;
  }
  return gerepilecopy(av, P);
}
