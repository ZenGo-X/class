/* Copyright (C) 2015  The PARI group.

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

/* This file is a C version by Bill Allombert of a GP script by
   Fernando Rodriguez-Villegas */

/* ---------------  GP code  --------------------------------------- */
/* http://www.ma.utexas.edu/users/villegas/cnt/jacobians.gp */
/* */
/* Description: Compute long Weierstrass equation for genus 1 curve */
/* given by a plane curve */
/* */
/* Original Author:     Fernando Rodriguez-Villegas  */
/*                      villegas@math.utexas.edu */
/*                      University of Texas at Austin */
/* */
/* Created:             Tue Jun  7 2005 */
/* */
/*----------------------------------------------------------------- */

/* The mathematic behind this is described in
On the Jacobians of plane cubics,
Artin, Michael and Rodriguez-Villegas, Fernando and Tate, John,
Advances in Mathematics, 198, 2005, 1, 366--382
DOI: 10.1016/j.aim.2005.06.004
URL: http://dx.doi.org/10.1016/j.aim.2005.06.004
PDF: http://www.sciencedirect.com/science/article/pii/S0001870805001775
*/

/* Input: coefficients of a cubic  */
/*t0*y^3+(s1+s0*x)*y^2 +(r2+r1*x+r0*x^2)*y+(q3+q2*x+q1*x^2+q0*x^3)=0*/

static GEN
jac_cubic(GEN t0, GEN s0, GEN s1, GEN r0, GEN r1, GEN r2, GEN q0, GEN q1, GEN q2, GEN q3)
{
  GEN p1 = cgetg(6, t_VEC);
  gel(p1, 1) = gcopy(r1);
  gel(p1, 2) = gneg(gadd(gadd(gmul(s0, q2), gmul(s1, q1)), gmul(r0, r2)));
  gel(p1, 3) = gadd(gmul(gsub(gmul(gmulsg(9, t0), q0), gmul(s0, r0)), q3), gadd(gmul(gsub(gmul(gneg(t0), q1), gmul(s1, r0)), q2), gsub(gmul(gmul(gneg(s0), r2), q1), gmul(gmul(s1, r2), q0))));
  gel(p1, 4) = gadd(gmul(gadd(gmul(gadd(gmul(gmulsg(-3, t0), r0), gsqr(s0)), q1), gadd(gmul(gmul(gmulsg(-3, s1), s0), q0), gmul(s1, gsqr(r0)))), q3), gadd(gadd(gmul(gmul(t0, r0), gsqr(q2)), gmul(gadd(gmul(gmul(s1, s0), q1), gadd(gmul(gadd(gmul(gmulsg(-3, t0), r2), gsqr(s1)), q0), gmul(gmul(s0, r0), r2))), q2)), gadd(gadd(gmul(gmul(t0, r2), gsqr(q1)), gmul(gmul(gmul(s1, r0), r2), q1)), gmul(gmul(s0, gsqr(r2)), q0))));
  gel(p1, 5) = gadd(gadd(gmul(gsub(gadd(gmul(gmulsg(-27, gsqr(t0)), gsqr(q0)), gmul(gsub(gmul(gmul(gmulsg(9, t0), s0), r0), gpowgs(s0, 3)), q0)), gmul(t0, gpowgs(r0, 3))), gsqr(q3)), gmul(gadd(gmul(gadd(gmul(gsub(gmul(gmulsg(9, gsqr(t0)), q0), gmul(gmul(t0, s0), r0)), q1), gadd(gmul(gadd(gmul(gmul(gmulsg(-3, t0), s0), r1), gadd(gmul(gmul(gmulsg(3, t0), s1), r0), gmul(gmulsg(2, s1), gsqr(s0)))), q0), gsub(gmul(gmul(t0, gsqr(r0)), r1), gmul(gmul(s1, s0), gsqr(r0))))), q2), gadd(gadd(gadd(gmul(gneg(gsqr(t0)), gpowgs(q1, 3)), gmul(gadd(gmul(gmul(t0, s0), r1), gsub(gmul(gmul(gmulsg(2, t0), s1), r0), gmul(s1, gsqr(s0)))), gsqr(q1))), gmul(gadd(gmul(gadd(gmul(gmul(gmulsg(3, t0), s0), r2), gadd(gmul(gmul(gmulsg(-3, t0), s1), r1), gmul(gmulsg(2, gsqr(s1)), s0))), q0), gadd(gmul(gsub(gmul(gmulsg(2, t0), gsqr(r0)), gmul(gsqr(s0), r0)), r2), gsub(gadd(gmul(gmul(gneg(t0), r0), gsqr(r1)), gmul(gmul(gmul(s1, s0), r0), r1)), gmul(gsqr(s1), gsqr(r0))))), q1)), gadd(gmul(gsub(gmul(gmul(gmulsg(9, t0), s1), r2), gpowgs(s1, 3)), gsqr(q0)), gmul(gadd(gmul(gsub(gmul(gadd(gmul(gmulsg(-3, t0), r0), gsqr(s0)), r1), gmul(gmul(s1, s0), r0)), r2), gadd(gsub(gmul(t0, gpowgs(r1, 3)), gmul(gmul(s1, s0), gsqr(r1))), gmul(gmul(gsqr(s1), r0), r1))), q0)))), q3)), gadd(gadd(gadd(gmul(gmul(gneg(gsqr(t0)), q0), gpowgs(q2, 3)), gmul(gadd(gmul(gmul(gmul(gneg(t0), s1), r0), q1), gsub(gmul(gadd(gmul(gmul(gmulsg(2, t0), s0), r2), gsub(gmul(gmul(t0, s1), r1), gmul(gsqr(s1), s0))), q0), gmul(gmul(t0, gsqr(r0)), r2))), gsqr(q2))), gmul(gadd(gadd(gmul(gmul(gmul(gneg(t0), s0), r2), gsqr(q1)), gmul(gadd(gmul(gmul(gmul(gneg(t0), s1), r2), q0), gmul(gsub(gmul(gmul(t0, r0), r1), gmul(gmul(s1, s0), r0)), r2)), q1)), gmul(gadd(gmul(gsub(gmul(gmulsg(2, t0), r0), gsqr(s0)), gsqr(r2)), gmul(gsub(gadd(gmul(gneg(t0), gsqr(r1)), gmul(gmul(s1, s0), r1)), gmul(gsqr(s1), r0)), r2)), q0)), q2)), gsub(gadd(gmul(gmul(gmul(gneg(t0), r0), gsqr(r2)), gsqr(q1)), gmul(gmul(gmul(gsub(gmul(t0, r1), gmul(s1, s0)), gsqr(r2)), q0), q1)), gmul(gmul(t0, gpowgs(r2, 3)), gsqr(q0)))));
  return p1;
}

/* Input: coefficients of an equation */
/* t0*y^2+(s0*x^2+s1*x+s2)*y+(r0*x^4+r1*x^3+r2*x^2+r3*x+r4)=0 */

static GEN
jac_quart(GEN t0, GEN s0, GEN s1, GEN s2, GEN r0, GEN r1, GEN r2, GEN r3, GEN r4)
{
  GEN p1 = cgetg(6, t_VEC);
  gel(p1, 1) = gcopy(s1);
  gel(p1, 2) = gsub(gmul(gneg(t0), r2), gmul(s0, s2));
  gel(p1, 3) = gsub(gmul(gmul(gneg(t0), s2), r1), gmul(gmul(t0, s0), r3));
  gel(p1, 4) = gadd(gadd(gadd(gmul(gneg(gsub(gmul(gmulsg(4, gsqr(t0)), r4), gmul(t0, gsqr(s2)))), r0), gmul(gmul(gsqr(t0), r1), r3)), gmul(gmul(gmul(t0, s0), s2), r2)), gmul(gmul(t0, gsqr(s0)), r4));
  gel(p1, 5) = gsub(gsub(gsub(gmul(gneg(gadd(gsub(gadd(gmul(gneg(gsub(gmul(gmulsg(4, gpowgs(t0, 3)), r4), gmul(gsqr(t0), gsqr(s2)))), r2), gmul(gpowgs(t0, 3), gsqr(r3))), gmul(gmul(gmul(gsqr(t0), s1), s2), r3)), gmul(gmul(gsqr(t0), gsqr(s1)), r4))), r0), gmul(gmul(gpowgs(t0, 3), gsqr(r1)), r4)), gmul(gsub(gmul(gmul(gmul(gsqr(t0), s0), s2), r3), gmul(gmul(gmul(gsqr(t0), s0), s1), r4)), r1)), gmul(gmul(gmul(gsqr(t0), gsqr(s0)), r2), r4));
  return p1;
}

/* Input: coefficients of an equation */
/* (t0*x^2+t1*x+t2)*y^2+(r0*x^2+r1*x+r2)*y+(s0*x^2+s1*x+s2)=0 */

static GEN
jac_biquadr(GEN t0, GEN t1, GEN t2, GEN r0, GEN r1, GEN r2,
                                    GEN s0, GEN s1, GEN s2)
{
  GEN p1 = cgetg(6, t_VEC);
  gel(p1, 1) = gcopy(r1);
  gel(p1, 2) = gneg(gadd(gadd(gadd(gmul(s2, t0), gmul(t2, s0)), gmul(t1, s1)), gmul(r2, r0)));
  gel(p1, 3) = gadd(gmul(gmul(gneg(r2), s1), t0), gadd(gmul(gmul(gneg(t1), r2), s0), gsub(gmul(gmul(gneg(t2), r0), s1), gmul(gmul(t1, r0), s2))));
  gel(p1, 4) = gadd(gmul(gadd(gmul(gadd(gmul(gmulsg(-4, t2), s2), gsqr(r2)), s0), gadd(gadd(gmul(t2, gsqr(s1)), gmul(gmul(t1, s2), s1)), gmul(gmul(r2, r0), s2))), t0), gadd(gmul(gadd(gmul(gmul(t2, t1), s1), gadd(gmul(gsqr(t1), s2), gmul(gmul(t2, r2), r0))), s0), gadd(gmul(gmul(gmul(t1, r2), r0), s1), gmul(gmul(t2, gsqr(r0)), s2))));
  gel(p1, 5) = gadd(gadd(gmul(gsub(gmul(gsub(gmul(gmulsg(4, t2), gsqr(s2)), gmul(gsqr(r2), s2)), s0), gmul(gmul(t2, s2), gsqr(s1))), gsqr(t0)), gmul(gadd(gadd(gmul(gsub(gmul(gmulsg(4, gsqr(t2)), s2), gmul(t2, gsqr(r2))), gsqr(s0)), gmul(gadd(gadd(gmul(gneg(gsqr(t2)), gsqr(s1)), gmul(gsub(gmul(gmul(t2, r2), r1), gmul(t1, gsqr(r2))), s1)), gadd(gmul(gneg(gsqr(t1)), gsqr(s2)), gmul(gadd(gmul(gneg(t2), gsqr(r1)), gmul(gmul(t1, r2), r1)), s2))), s0)), gsub(gadd(gmul(gmul(gmul(gneg(t2), r2), r0), gsqr(s1)), gmul(gmul(gmul(gsub(gmul(t2, r1), gmul(t1, r2)), r0), s2), s1)), gmul(gmul(t2, gsqr(r0)), gsqr(s2)))), t0)), gsub(gadd(gmul(gmul(gmul(gneg(t2), gsqr(t1)), s2), gsqr(s0)), gmul(gadd(gmul(gmul(gmul(gmul(gneg(t2), t1), r2), r0), s1), gmul(gadd(gmul(gneg(gsqr(t2)), gsqr(r0)), gmul(gsub(gmul(gmul(t2, t1), r1), gmul(gsqr(t1), r2)), r0)), s2)), s0)), gmul(gmul(gmul(gmul(t2, t1), gsqr(r0)), s2), s1)));
  return p1;
}


INLINE long
dg(GEN P, long v)
{
  if (typ(P)!=t_POL || varn(P)!=v || !signe(P))
    return -1;
  return degpol(P);
}

INLINE GEN
co(GEN P, long i, long v)
{
  if (typ(P)!=t_POL || varn(P)!=v)
    return i==0 ? P: gen_0;
  if (i>degpol(P)) return gen_0;
  return gel(P, i+2);
}

GEN
ellfromeqn(GEN P)
{
  pari_sp av = avma;
  long vx, vy, dx, dy, dm;
  GEN r = gen_0;
  if (typ(P)!=t_POL) pari_err_TYPE("ellfromeqn",P);
  vx = varn(P); vy = gvar2(P);
  if (vy==NO_VARIABLE) pari_err_TYPE("ellfromeqn",P);
  dx = poldegree(P, vx);
  dy = poldegree(P, vy);
  dm = maxss(dx, dy);
  if (dm == 2)
  {
    GEN p_0 = co(P, 0, vx), p_1 = co(P, 1, vx), p_2 = co(P, 2, vx);
    r = jac_biquadr(co(p_2, 2, vy), co(p_2, 1, vy), co(p_2, 0, vy),
                    co(p_1, 2, vy), co(p_1, 1, vy), co(p_1, 0, vy),
                    co(p_0, 2, vy), co(p_0, 1, vy), co(p_0, 0, vy));
  }
  else if (dm == 3)
  {
    GEN p_0 = co(P, 0, vx), p_1 = co(P, 1, vx),
        p_2 = co(P, 2, vx), p_3 = co(P, 3, vx);
    if (dg(p_3, vy) > 0 || dg(p_2, vy) > 1 || dg(p_1, vy) > 2)
      r = gen_0; /* genus > 1 */
    else
      r = jac_cubic( co(p_3, 0, vy),
        co(p_2, 1, vy), co(p_2, 0, vy),
        co(p_1, 2, vy), co(p_1, 1, vy), co(p_1, 0, vy),
        co(p_0, 3, vy), co(p_0, 2, vy), co(p_0, 1, vy), co(p_0, 0, vy));
  }
  else if (dm == 4 && dx == 2)
  {
    GEN p_0 = co(P, 0, vx), p_1 = co(P, 1, vx), p_2 = co(P, 2, vx);
    if (dg(p_2, vy) > 0 || dg(p_1, vy) > 2)
      r = gen_0; /* genus > 1 */
    else
      r = jac_quart( co(p_2, 0, vy),
        co(p_1, 2, vy), co(p_1, 1, vy), co(p_1, 0, vy),
        co(p_0, 4, vy), co(p_0, 3, vy), co(p_0, 2, vy), co(p_0, 1, vy),
                                                        co(p_0, 0, vy));
  }
  else if (dm == 4 && dx == 4)
  {
    GEN p_0 = co(P, 0, vx), p_1 = co(P, 1, vx), p_2 = co(P, 2, vx),
        p_3 = co(P, 3, vx), p_4 = co(P, 4, vx);
    if (dg(p_4, vy) > 0 || dg(p_3, vy) > 0
     || dg(p_2, vy) > 1 || dg(p_1, vy) > 1 || dg(p_0, vy) > 2)
      r = gen_0; /* genus > 1 */
    else
      r = jac_quart(co(p_0, 2, vy),
                    co(p_2, 1, vy), co(p_1, 1, vy), co(p_0, 1, vy),
                    co(p_4, 0, vy), co(p_3, 0, vy), co(p_2, 0, vy),
                                    co(p_1, 0, vy), co(p_0, 0, vy));
  }
  if (r==gen_0)
    pari_err_DOMAIN("ellfromeqn", "genus", "!=", gen_1,P);
  return gerepileupto(av, r);
}
