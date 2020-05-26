/* Copyright (C) 2000  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA. */
#include "pari.h"
#include "paripriv.h"

/********************************************************************/
/**                                                                **/
/**                       IGUSA INVARIANTS                         **/
/**                       (GP2C-generated)                         **/
/**                                                                **/
/********************************************************************/
/*
j2(a0,a1,a2,a3,a4,a5,a6) = (-120*a0*a6+20*a1*a5-8*a2*a4+3*a3^2) / 4;
*/
static GEN
igusaj2(GEN a0, GEN a1, GEN a2, GEN a3, GEN a4, GEN a5, GEN a6)
{
  pari_sp av = avma;
  return gerepileupto(av, gmul2n(gadd(gsub(gadd(gmul(gmulsg(-120, a0), a6), gmul(gmulsg(20, a1), a5)), gmul(gmulsg(8, a2), a4)), gmulsg(3, gsqr(a3))), -2));
}

/*
j4(a0,a1,a2,a3,a4,a5,a6) = (240*(a0*a3*a4*a5+a1*a2*a3*a6)-400*(a0*a2*a5^2+a1^2*a4*a6)-64*(a0*a4^3+a2^3*a6)+16*(a1*a3*a4^2+a2^2*a3*a5)-672*a0*a3^2*a6+240*a1^2*a5^2-112*a1*a2*a4*a5-8*a1*a3^2*a5+16*a2^2*a4^2-16*a2*a3^2*a4+3*a3^4+2640*a0^2*a6^2-880*a0*a1*a5*a6+1312*a0*a2*a4*a6) / 2^7
*/
static GEN
igusaj4(GEN a0, GEN a1, GEN a2, GEN a3, GEN a4, GEN a5, GEN a6)
{
  pari_sp av = avma;
  return gerepileupto(av,
gmul2n(gadd(gsub(gadd(gadd(gsub(gadd(gsub(gsub(gadd(gsub(gadd(gsub(gsub(gmulsg(240,
gadd(gmul(gmul(gmul(a0, a3), a4), a5), gmul(gmul(gmul(a1, a2), a3), a6))),
gmulsg(400, gadd(gmul(gmul(a0, a2), gsqr(a5)), gmul(gmul(gsqr(a1), a4), a6)))),
gmulsg(64, gadd(gmul(a0, gpowgs(a4, 3)), gmul(gpowgs(a2, 3), a6)))), gmulsg(16,
gadd(gmul(gmul(a1, a3), gsqr(a4)), gmul(gmul(gsqr(a2), a3), a5)))),
gmul(gmul(gmulsg(672, a0), gsqr(a3)), a6)), gmul(gmulsg(240, gsqr(a1)),
gsqr(a5))), gmul(gmul(gmul(gmulsg(112, a1), a2), a4), a5)), gmul(gmul(gmulsg(8,
a1), gsqr(a3)), a5)), gmul(gmulsg(16, gsqr(a2)), gsqr(a4))),
gmul(gmul(gmulsg(16, a2), gsqr(a3)), a4)), gmulsg(3, gpowgs(a3, 4))),
gmul(gmulsg(2640, gsqr(a0)), gsqr(a6))), gmul(gmul(gmul(gmulsg(880, a0), a1),
a5), a6)), gmul(gmul(gmul(gmulsg(1312, a0), a2), a4), a6)), -7));
}

/*
j6(a0,a1,a2,a3,a4,a5,a6) = (1600*(a0^2*a4^2*a5^2+a1^2*a2^2*a6^2)+1600*(a0*a1*a2*a5^3+a1^3*a4*a5*a6)+640*(a0*a1*a3*a4*a5^2+a1^2*a2*a3*a5*a6)-4000*(a0^2*a3*a5^3+a1^3*a3*a6^2)-384*(a0*a1*a4^3*a5+a1*a2^3*a5*a6)-640*(a0*a2^2*a4*a5^2+a1^2*a2*a4^2*a6)+80*(a0*a2*a3^2*a5^2+a1^2*a3^2*a4*a6)+192*(a0*a2*a3*a4^2*a5+a1*a2^2*a3*a4*a6)-48*(a0*a3^3*a4*a5+a1*a2*a3^3*a6)-224*(a1^2*a3*a4^2*a5+a1*a2^2*a3*a5^2)+64*(a1^2*a4^4+a2^4*a5^2)-64*(a1*a2*a3*a4^3+a2^3*a3*a4*a5)+16*(a1*a3^3*a4^2+a2^2*a3^3*a5)-4096*(a0^2*a4^3*a6+a0*a2^3*a6^2)+6400*(a0^2*a2*a5^2*a6+a0*a1^2*a4*a6^2)+10560*(a0^2*a3*a4*a5*a6+a0*a1*a2*a3*a6^2)+2624*(a0*a1*a3*a4^2*a6+a0*a2^2*a3*a5*a6)-4432*a0*a1*a3^2*a5*a6-8*a2*a3^4*a4+a3^6-320*a1^3*a5^3+64*a1^2*a2*a4*a5^2+176*a1^2*a3^2*a5^2+128*a1*a2^2*a4^2*a5+112*a1*a2*a3^2*a4*a5-28*a1*a3^4*a5+16*a2^2*a3^2*a4^2+5120*a0^3*a6^3-2544*a0^2*a3^2*a6^2+312*a0*a3^4*a6-14336*a0^2*a2*a4*a6^2+1024*a0*a2^2*a4^2*a6-2560*a0^2*a1*a5*a6^2-2240*a0*a1^2*a5^2*a6-6528*a0*a1*a2*a4*a5*a6-1568*a0*a2*a3^2*a4*a6) / 2^10
*/
static GEN
igusaj6(GEN a0, GEN a1, GEN a2, GEN a3, GEN a4, GEN a5, GEN a6)
{
  pari_sp av = avma;
  return gerepileupto(av,
gmul2n(gsub(gsub(gsub(gsub(gadd(gsub(gadd(gsub(gadd(gadd(gsub(gadd(gadd(gadd(gadd(gsub(gadd(gsub(gsub(gadd(gadd(gadd(gsub(gadd(gsub(gadd(gsub(gsub(gadd(gadd(gsub(gsub(gsub(gadd(gadd(gmulsg(1600,
gadd(gmul(gmul(gsqr(a0), gsqr(a4)), gsqr(a5)), gmul(gmul(gsqr(a1), gsqr(a2)),
gsqr(a6)))), gmulsg(1600, gadd(gmul(gmul(gmul(a0, a1), a2), gpowgs(a5, 3)),
gmul(gmul(gmul(gpowgs(a1, 3), a4), a5), a6)))), gmulsg(640,
gadd(gmul(gmul(gmul(gmul(a0, a1), a3), a4), gsqr(a5)),
gmul(gmul(gmul(gmul(gsqr(a1), a2), a3), a5), a6)))), gmulsg(4000,
gadd(gmul(gmul(gsqr(a0), a3), gpowgs(a5, 3)), gmul(gmul(gpowgs(a1, 3), a3),
gsqr(a6))))), gmulsg(384, gadd(gmul(gmul(gmul(a0, a1), gpowgs(a4, 3)), a5),
gmul(gmul(gmul(a1, gpowgs(a2, 3)), a5), a6)))), gmulsg(640,
gadd(gmul(gmul(gmul(a0, gsqr(a2)), a4), gsqr(a5)), gmul(gmul(gmul(gsqr(a1),
a2), gsqr(a4)), a6)))), gmulsg(80, gadd(gmul(gmul(gmul(a0, a2), gsqr(a3)),
gsqr(a5)), gmul(gmul(gmul(gsqr(a1), gsqr(a3)), a4), a6)))), gmulsg(192,
gadd(gmul(gmul(gmul(gmul(a0, a2), a3), gsqr(a4)), a5), gmul(gmul(gmul(gmul(a1,
gsqr(a2)), a3), a4), a6)))), gmulsg(48, gadd(gmul(gmul(gmul(a0, gpowgs(a3, 3)),
a4), a5), gmul(gmul(gmul(a1, a2), gpowgs(a3, 3)), a6)))), gmulsg(224,
gadd(gmul(gmul(gmul(gsqr(a1), a3), gsqr(a4)), a5), gmul(gmul(gmul(a1,
gsqr(a2)), a3), gsqr(a5))))), gmulsg(64, gadd(gmul(gsqr(a1), gpowgs(a4, 4)),
gmul(gpowgs(a2, 4), gsqr(a5))))), gmulsg(64, gadd(gmul(gmul(gmul(a1, a2), a3),
gpowgs(a4, 3)), gmul(gmul(gmul(gpowgs(a2, 3), a3), a4), a5)))), gmulsg(16,
gadd(gmul(gmul(a1, gpowgs(a3, 3)), gsqr(a4)), gmul(gmul(gsqr(a2), gpowgs(a3,
3)), a5)))), gmulsg(4096, gadd(gmul(gmul(gsqr(a0), gpowgs(a4, 3)), a6),
gmul(gmul(a0, gpowgs(a2, 3)), gsqr(a6))))), gmulsg(6400,
gadd(gmul(gmul(gmul(gsqr(a0), a2), gsqr(a5)), a6), gmul(gmul(gmul(a0,
gsqr(a1)), a4), gsqr(a6))))), gmulsg(10560, gadd(gmul(gmul(gmul(gmul(gsqr(a0),
a3), a4), a5), a6), gmul(gmul(gmul(gmul(a0, a1), a2), a3), gsqr(a6))))),
gmulsg(2624, gadd(gmul(gmul(gmul(gmul(a0, a1), a3), gsqr(a4)), a6),
gmul(gmul(gmul(gmul(a0, gsqr(a2)), a3), a5), a6)))),
gmul(gmul(gmul(gmul(gmulsg(4432, a0), a1), gsqr(a3)), a5), a6)),
gmul(gmul(gmulsg(8, a2), gpowgs(a3, 4)), a4)), gpowgs(a3, 6)), gmul(gmulsg(320,
gpowgs(a1, 3)), gpowgs(a5, 3))), gmul(gmul(gmul(gmulsg(64, gsqr(a1)), a2), a4),
gsqr(a5))), gmul(gmul(gmulsg(176, gsqr(a1)), gsqr(a3)), gsqr(a5))),
gmul(gmul(gmul(gmulsg(128, a1), gsqr(a2)), gsqr(a4)), a5)),
gmul(gmul(gmul(gmul(gmulsg(112, a1), a2), gsqr(a3)), a4), a5)),
gmul(gmul(gmulsg(28, a1), gpowgs(a3, 4)), a5)), gmul(gmul(gmulsg(16, gsqr(a2)),
gsqr(a3)), gsqr(a4))), gmul(gmulsg(5120, gpowgs(a0, 3)), gpowgs(a6, 3))),
gmul(gmul(gmulsg(2544, gsqr(a0)), gsqr(a3)), gsqr(a6))), gmul(gmul(gmulsg(312,
a0), gpowgs(a3, 4)), a6)), gmul(gmul(gmul(gmulsg(14336, gsqr(a0)), a2), a4),
gsqr(a6))), gmul(gmul(gmul(gmulsg(1024, a0), gsqr(a2)), gsqr(a4)), a6)),
gmul(gmul(gmul(gmulsg(2560, gsqr(a0)), a1), a5), gsqr(a6))),
gmul(gmul(gmul(gmulsg(2240, a0), gsqr(a1)), gsqr(a5)), a6)),
gmul(gmul(gmul(gmul(gmul(gmulsg(6528, a0), a1), a2), a4), a5), a6)),
gmul(gmul(gmul(gmul(gmulsg(1568, a0), a2), gsqr(a3)), a4), a6)), -10));
}

/********************************************************************/
/**                                                                **/
/**   A REDUCTION ALGORITHM "A LA TATE" FOR CURVES OF GENUS 2      **/
/**                                                                **/
/********************************************************************/
/* Based on genus2reduction-0.3, http://www.math.u-bordeaux.fr/~liu/G2R/
 * by Qing Liu <liu@math.u-bordeaux.fr>
 * and Henri Cohen <cohen@math.u-bordeaux.fr>

 * Qing Liu: Modeles minimaux des courbes de genre deux
 * J. fuer die Reine und Angew. Math., 453 (1994), 137-164.
 * http://www.math.u-bordeaux.fr/~liu/articles/modregE.ps */

/* some auxiliary polynomials, gp2c-generated */

/*
apol2(a0,a1,a2) = -5*a1^2+12*a0*a2;
*/
static GEN
apol2(GEN a0, GEN a1, GEN a2)
{
  return gadd(gmulsg(-5, gsqr(a1)), gmul(gmulsg(12, a0), a2));
}

/*
apol3(a0,a1,a2,a3) = 5*a1^3+9*a0*(-2*a1*a2+3*a0*a3);
*/
static GEN
apol3(GEN a0, GEN a1, GEN a2, GEN a3)
{
  return gadd(gmulsg(5, gpowgs(a1, 3)), gmul(gmulsg(9, a0), gadd(gmul(gmulsg(-2, a1), a2), gmul(gmulsg(3, a0), a3))));
}

/*
apol5(a0,a1,a2,a3,a4,a5) = a1^5+3*a0*(-2*a1^3*a2+9*a0*a1^2*a3-36*a0^2*a1*a4+108*a0^3*a5);
*/
static GEN
apol5(GEN a0, GEN a1, GEN a2, GEN a3, GEN a4, GEN a5)
{
  return gadd(gpowgs(a1, 5), gmul(gmulsg(3, a0), gadd(gsub(gadd(gmul(gmulsg(-2, gpowgs(a1, 3)), a2), gmul(gmul(gmulsg(9, a0), gsqr(a1)), a3)), gmul(gmul(gmulsg(36, gsqr(a0)), a1), a4)), gmul(gmulsg(108, gpowgs(a0, 3)), a5))));
}

/*
bpol2(a0,a1,a2,a3,a4) = 2*a2^2-5*a1*a3+10*a0*a4;
*/
static GEN
bpol2(GEN a0, GEN a1, GEN a2, GEN a3, GEN a4)
{
  return gadd(gsub(gmulsg(2, gsqr(a2)), gmul(gmulsg(5, a1), a3)), gmul(gmulsg(10, a0), a4));
}

static const long VERYBIG = (1L<<20);
static long
myval(GEN x, GEN p) { return signe(x)? Z_pval(x,p): VERYBIG; }
static long
my3val(GEN x) { return signe(x)? Z_lval(x,3): VERYBIG; }
/* b in Z[i], return v_3(b) */
static long
myval_zi(GEN b) { return minss(my3val(real_i(b)), my3val(imag_i(b))); }
/* b in Z[i, Y]/(Y^2-3), return v_Y(b) */
static long
myval_zi2(GEN b)
{
  long v0, v1;
  b = lift_shallow(b);
  v0 = myval_zi(RgX_coeff(b,0));
  v1 = myval_zi(RgX_coeff(b,1));
  return minss(2*v0, 2*v1+1);
}

/* min(a,b,c) */
static long
min3(long a, long b, long c)
{
  long m = a;
  if (b < m) m = b;
  if (c < m) m = c;
  return m;
}

/* Vector of p-adic factors (over Q_p) to accuracy r of pol. */
static GEN
padicfactors(GEN pol, GEN p, long r) { return gel(factorpadic(pol,p,r),1); }

/* x(1/t)*t^6, deg x <= 6 */
static GEN
RgX_recip6(GEN x)
{
  long lx = lg(x), i, j;
  GEN y = cgetg(9, t_POL);
  y[1] = x[1];
  for (i=8,j=2; j < lx; i--,j++) gel(y,i) = gel(x,j);
  for (       ; j <  9; i--,j++) gel(y,i) = gen_0;
  return normalizepol_lg(y, 9);
}
/* extract coefficients of a polynomial a0 X^6 + ... + a6, of degree <= 6 */
static void
RgX_to_06(GEN q, GEN *a0, GEN *a1, GEN *a2, GEN *a3, GEN *a4, GEN *a5, GEN *a6)
{
  *a0 = gen_0;
  *a1 = gen_0;
  *a2 = gen_0;
  *a3 = gen_0;
  *a4 = gen_0;
  *a5 = gen_0;
  *a6 = gen_0;
  switch(degpol(q))
  {
    case 6: *a0 = gel(q,8); /*fall through*/
    case 5: *a1 = gel(q,7); /*fall through*/
    case 4: *a2 = gel(q,6); /*fall through*/
    case 3: *a3 = gel(q,5); /*fall through*/
    case 2: *a4 = gel(q,4); /*fall through*/
    case 1: *a5 = gel(q,3); /*fall through*/
    case 0: *a6 = gel(q,2); /*fall through*/
  }
}
/* extract coefficients a0,...a3 of a polynomial a0 X^6 + ... + a6 */
static void
RgX_to_03(GEN q, GEN *a0, GEN *a1, GEN *a2, GEN *a3)
{
  *a0 = gen_0;
  *a1 = gen_0;
  *a2 = gen_0;
  *a3 = gen_0;
  switch(degpol(q))
  {
    case 6: *a0 = gel(q,8); /*fall through*/
    case 5: *a1 = gel(q,7); /*fall through*/
    case 4: *a2 = gel(q,6); /*fall through*/
    case 3: *a3 = gel(q,5); /*fall through*/
  }
}

/* deg(H mod p) = 3, return v_p( disc(correspondig p-adic factor) ) */
static long
discpart(GEN H, GEN p, long prec)
{
  GEN list, prod, dis;
  long i, j;

  if (degpol(FpX_red(H,p)) != 3)
    pari_err_BUG("discpart [must not reach]"); /* LCOV_EXCL_LINE */
  list = padicfactors(H,p,prec);
  prod = pol_1(varn(H));
  for(i = 1; i < lg(list); i++)
  {
    GEN t = gel(list,i);
    for(j = 3; j < lg(t); j++) /* include if non-constant mod p */
      if (!valp(gel(t,j))) { prod = RgX_mul(prod,t); break; }
  }
  if (degpol(prod) != 3) pari_err_BUG("discpart [prod degree]");
  dis = RgX_disc(prod);
  return gequal0(dis)? prec+1: valp(dis);
}

/* B = b0 X^6 + ... + b6 a ZX, 0 <= j <= 3.
 * Let theta_j(H) := min { v_p(b_i) / (i - j), j < i <= 6 } >= 0.
 * Return 60 theta \in Z */
static long
theta_j(GEN B, GEN p, long j)
{
  long i, t = 60*myval(RgX_coeff(B,5-j), p);
  for(i = 2+j; i <= 6; i++)
    t = minss(t, myval(RgX_coeff(B,6-i), p) * (60 / (i-j)));
  return t;
}
/* compute 6 * theta_3 for B in Z[i][X], p = 3 */
static long
theta_3_zi(GEN B)
{
  long v2 = myval_zi(RgX_coeff(B,2));
  long v1 = myval_zi(RgX_coeff(B,1));
  long v0 = myval_zi(RgX_coeff(B,0));
  return min3(6*v2, 3*v1, 2*v0);
}
/* compute 6 * theta_3 for B in (Z[i,Y]/(Y^2-3))[X], p = 3 */
static long
theta_3_zi2(GEN B)
{
  long v2 = myval_zi2(RgX_coeff(B,2));
  long v1 = myval_zi2(RgX_coeff(B,1));
  long v0 = myval_zi2(RgX_coeff(B,0));
  return min3(6*v2, 3*v1, 2*v0);
}

/* Set maxord to the maximal multiplicity of a factor. If there is at least
 * a triple root (=> maxord >= 3) return it, else return NULL */
static GEN
factmz(GEN Q, GEN p, long *maxord)
{
  GEN z = FpX_factor_squarefree(Q, p);
  long m = lg(z)-1; /* maximal multiplicity */
  *maxord = m;
  return (m >= 3)? FpX_oneroot(gel(z,m), p): NULL;
}

/* H integral ZX of degree 5 or 6, p > 2. Modify until
 *   y^2 = p^alpha H is minimal over Z_p, alpha = 0,1
 * Return [H,lambda,60*theta,alpha,quad,beta], where
 *   - quad = 1 if H has a root of order 3 in F_p^2 \ F_p, 0 otherwise
 *   - 0 <= lambda <= 3, index of a coefficient with valuation 0
 *   - theta = theta_j(H(x + r), p, lambda), 60*theta in Z, where r is a root
 *   of H mod p
 *   - beta >= -1 s.t. H = p^n H0(r + p^beta * X) for some n, r in Z, where
 *   H0 is the initial H or polrecip(H) */
static GEN
polymini(GEN H, GEN p)
{
  GEN a0, a1, a2, a3, Hp, rac;
  long t60, alpha, lambda, maxord, quad = 0, beta = 0;

  alpha = ZX_pvalrem(H, p, &H) & 1;
  RgX_to_03(H, &a0,&a1,&a2,&a3);
  if (dvdii(a0,p) && dvdii(a1,p) && dvdii(a2,p) && dvdii(a3,p))
  {
    H = RgX_recip6(H);
    RgX_to_03(H, &a0,&a1,&a2,&a3);
  }
  if (!dvdii(a3,p)) lambda = 3;
  else if (!dvdii(a2,p)) lambda = 2;
  else if (!dvdii(a1,p)) lambda = 1;
  else lambda = 0;

  for(;;)
  { /* lambda <= 3, t60 = 60*theta */
    long e;
    t60 = theta_j(H,p,lambda); e = t60 / 60;
    if (e)
    {
      GEN pe = powiu(p,e);
      /* H <- H(p^e X) / p^(e(6-lambda)) */
      H = ZX_Z_divexact(ZX_unscale_div(H,pe), powiu(pe,5-lambda));
      alpha = (alpha + lambda*e)&1;
      beta += e;
      t60 -= 60*e;
    }
    /* 0 <= t < 60 */
    Hp = FpX_red(H, p);
    if (t60) break;

    rac = factmz(Hp,p, &maxord);
    if (maxord <= 2)
    {
      if (degpol(Hp) <= 3) break;
      goto end;
    }
    else
    { /* maxord >= 3 */
      if (!rac) { quad = 1; goto end; }
      if (signe(rac)) H = ZX_translate(H, rac);
      lambda = 6-maxord;
    }
  }

  if (lambda <= 2)
  {
    if (myval(RgX_coeff(H,2),p) > 1-alpha &&
        myval(RgX_coeff(H,1),p) > 2-alpha &&
        myval(RgX_coeff(H,0),p) > 3-alpha)
    {
      H = ZX_unscale(H, p);
      if (alpha) H = ZX_Z_mul(H, p);
      return polymini(H, p);
    }
  }
  else if (lambda == 3 && alpha == 1)
  {
    if (degpol(Hp) == 3)
    {
      if (myval(RgX_coeff(H,6),p) >= 3 &&
          myval(RgX_coeff(H,5),p) >= 2)
      { /* too close to root [Kodaira symbol for y^2 = p^alpha*H not
           implemented when alpha = 1]: go back one step */
        H = ZX_rescale(H, p); /* H(x/p)p^(deg H) */
        H = ZX_Z_divexact(H, powiu(p, degpol(H)-3)); /* H(x/p)p^3 */
        t60 += 60; alpha = 0; beta--;
      }
    }
    else if (degpol(Hp) == 6 && t60)
    {
      rac = factmz(RgX_mulXn(Hp, -3), p, &maxord);
      if (maxord == 3)
      {
        GEN T = ZX_unscale(ZX_translate(H,rac),p); /* H(rac + px) */
        if (ZX_pval(T,p)>= 3)
        {
          H = RgX_Rg_div(T, powiu(p,3));
          alpha = 0; beta++;
          t60 = theta_j(H,p,3);
          if (!t60)
          {
            Hp = FpX_red(H, p);
            if (!signe(FpX_disc(Hp,p)))
            {
              rac = FpX_oneroot(Hp, p);
              t60 = theta_j(ZX_translate(H,rac),p,3);
            }
          }
        }
      }
    }
  }
end:
  return mkvec2(H, mkvecsmall5(lambda,t60,alpha,quad,beta));
}

/* a in Q[i], return a^3 mod 3 */
static GEN
zi_pow3mod(GEN a)
{
  GEN x, y;
  if (typ(a) != t_COMPLEX) return gmodgs(a,3);
  x = gmodgs(gel(a,1), 3);
  y = gmodgs(gel(a,2), 3);
  return mkcomplex(x, negi(y));
}
static GEN
polymini_zi(GEN pol) /* polynome minimal dans Z[i] */
{
  GEN polh, rac, a0, a1, a2, a3, a4, a5, a6, p = utoipos(3);
  long alpha, beta = 0, t6;

  alpha = ZX_pval(pol,p) & 1;
  polh = alpha? RgX_Rg_div(pol, p): pol;
  rac = mkcomplex(Fp_div(RgX_coeff(polh,3), RgX_coeff(polh,6), p), gen_1);
  for(;;)
  {
    long e;
    polh = RgX_translate(polh, rac);
    t6 = theta_3_zi(polh); e = t6 / 6;
    if (e)
    {
      GEN pe = powiu(p,e);
      polh = RgX_Rg_div(RgX_unscale(polh,pe), powiu(pe,3));
      alpha = (alpha+e)&1;
      t6 -= e * 6; beta += e;
    }
    RgX_to_06(polh, &a0,&a1,&a2,&a3,&a4,&a5,&a6);
    if (t6 || !myval_zi(a4) || !myval_zi(a5)) break;
    rac = zi_pow3mod(gdiv(a6, gneg(a3)));
  }
  if (alpha && myval_zi(a0) >= 3 && myval_zi(a1) >= 2 && myval_zi(a2) >= 1)
  {
    t6 += 6; beta--; alpha = 0;
  }
  if (alpha && beta >= 1) pari_err_BUG("quadratic");
  return mkvecsmall3(t6, alpha, beta);
}

/* pol is a ZX, minimal polynomial over Z_3[i,Y]/(Y^2-3) */
static GEN
polymini_zi2(GEN pol)
{
  long alpha, beta, t6;
  GEN a0, a1, a2, a3, a4, a5, a6;
  GEN polh, rac, y = pol_x(fetch_var()), p = utoipos(3);

  if (ZX_pval(pol,p)) pari_err_BUG("polymini_zi2 [polynomial not minimal]");
  y = mkpolmod(y, gsubgs(gsqr(y), 3)); /* mod(y,y^2-3) */
  polh = gdivgs(RgX_unscale(pol, y),27); /* H(y*x) / 27 */
  if (myval_zi2(RgX_coeff(polh,4)) <= 0 ||
      myval_zi2(RgX_coeff(polh,2)) <= 0)
  {
    (void)delete_var();
    return mkvecsmall2(0,0);
  }

  if (myval_zi2(gsub(RgX_coeff(polh,6), RgX_coeff(polh,0))) > 0)
    rac = gen_I();
  else
    rac = gen_1;
  alpha = 0;
  beta  = 0;
  for(;;)
  {
    long e;
    polh = RgX_translate(polh, rac);
    t6 = theta_3_zi2(polh); e = t6 / 6;
    if (e)
    {
      GEN pent = gpowgs(y, e);
      polh = RgX_Rg_div(RgX_unscale(polh, pent), gpowgs(pent,3));
      alpha = (alpha+e)&1;
      t6 -= 6*e; beta += e;
    }
    RgX_to_06(polh, &a0,&a1,&a2,&a3,&a4,&a5,&a6);
    if (t6 || !myval_zi2(a4) || !myval_zi2(a5)) break;
    a3 = liftpol_shallow(a3); if (typ(a3)==t_POL) a3 = RgX_coeff(a3,0);
    a6 = liftpol_shallow(a6); if (typ(a6)==t_POL) a6 = RgX_coeff(a6,0);
    rac = zi_pow3mod(gdiv(a6,gneg(a3)));
  }
  if (alpha)
  {
    if (myval_zi2(a0) < 3 || myval_zi2(a1) < 2 || myval_zi2(a2) < 1)
      pari_err_BUG("polymini_zi2 [alpha]");
    t6 += 6; beta--;
  }
  (void)delete_var();
  if (odd(beta)) pari_err_BUG("quartic [type over Z[i] must be [K-K-(2*m)]]");
  return mkvecsmall2(t6, beta);
}


struct igusa {
  GEN j2, i4, j4, j6, j8, j10, i12;
  GEN a0, A2, A3, A5, B2;
};
struct igusa_p {
  long eps, tt, r1, r2, tame;
  GEN p, stable, val, neron;
  const char *type;
};

/* initialize Ip */
static void
stable_reduction(struct igusa *I, struct igusa_p *Ip, GEN p)
{
  static const long d[9] = { 0,60,30,30,20,15,12,10 }; /* 120 / deg(X) */
  GEN j2 = I->j2, i4 = I->i4, j4 = I->j4, j6 = I->j6, j8 = I->j8;
  GEN val, J, v, Ieps, j10 = I->j10, i12 = I->i12;
  long s, r1, r2, r3, r4, i, eps;

  Ip->tame = 0;
  Ip->neron = NULL;
  Ip->type = NULL;
  Ip->p = p;
  Ip->val = val = cgetg(9, t_VECSMALL);
  val[1] = myval(j2,p);
  val[2] = myval(j4,p);
  val[3] = myval(i4,p);
  val[4] = myval(j6,p);
  val[5] = myval(j8,p);
  val[6] = myval(j10,p);
  val[7] = myval(i12,p);
  switch(itos_or_0(p))
  {
    case 2:  eps = 4; val[8] = val[5]; Ieps = j8; break;
    case 3:  eps = 3; val[8] = val[4]; Ieps = j6; break;
    default: eps = 1; val[8] = val[1]; Ieps = gdivgs(j2,12); break;
  }

  v = cgetg(8,t_VECSMALL);
  for(i = 1; i <= 7; i++) v[i] = val[i] * d[i];
  s = vecsmall_min(v);
  Ip->eps  = eps;

  r1 = 3*eps*val[3];
  r3 = eps*val[6] + val[8];
  r2 = eps*val[7];
  r4 = min3(r1, r2, r3);

  /* s = max(v_p(X) / deg(X)) */
  J = cgetg(1, t_VEC);
  if (s == v[6])
    Ip->tt = 1;
  else if (s == v[7])
  {
    J = mkvec( Fp_to_mod(gmod(gdiv(gpowgs(i4,3),i12), p), p) );
    Ip->tt = 2;
  }
  else if (s == v[3])
    Ip->tt = (val[2] == val[3] || 2*val[4] == 3*val[3])? 3: 4;
  else if (r3 == r4)
  {
    GEN a,b, P, sj, pj, t = gmul(gpowgs(j10,eps),Ieps);
    sj = gaddsg(1728, gdiv(gpowgs(i12,eps), t));
    pj = gdiv(gpowgs(i4,3*eps), t);
    a = gmod(sj, p);
    b = gmod(pj, p);
    P = mkpoln(3, gen_1, Fp_neg(a,p), b, 0); /* X^2 - SX + P: roots j1,j2 */
    J = FpX_roots(P, p);
    switch(lg(J)-1)
    {
      case 0:
        P = FpX_to_mod(P, p);
        a = FpX_to_mod(pol_x(0), p);
        b = FpX_to_mod(deg1pol_shallow(b, gen_m1,0), p);
        J = mkvec2(mkpolmod(a,P), mkpolmod(b,P)); break;
      case 1:
        a = Fp_to_mod(gel(J,1), p);
        J = mkvec2(a, a); break;
      case 2:
        settyp(J, t_VEC);
        J = FpV_to_mod(J, p); break;
    }
    Ip->tt = 5;
  }
  else if (r2 == r4)
  {
    J = mkvec( Fp_to_mod(gmod(gdiv(gpowgs(i4,3),i12), p), p) );
    Ip->tt = 6;
  }
  else
    Ip->tt = 7; /* r1 == r4 */
  Ip->stable = mkvec2(stoi(Ip->tt), J);
}

struct red {
  const char *t, *pages;
  double tnum;
  GEN g;
};

/* destroy v */
static GEN
zv_snf(GEN v)
{
  long i, l = lg(v);
  for (i = 1; i < l; i++)
  {
    long j, a = v[i];
    for (j = i+1; j < l; j++)
    {
      long b = v[j], d = ugcd(a,b);
      v[i] = a = a*(b/d);
      v[j] = d;
    }
  }
  for (i = l-1; i > 0; i--)
    if (v[i] != 1) { setlg(v, i+1); break; }
  return zv_to_ZV(v);
}

static GEN
cyclic(long n)
{ return (n <= 1)? cgetg(1, t_VECSMALL): mkvecsmall(n); }
static GEN
dicyclic(long a, long b)
{
  long d;
  if (!a) a = 1;
  if (!b) b = 1;
  if (a < b) lswap(a,b);
  d = ugcd(a,b);
  if (d == 1) return cyclic(a*b);
  return mkvecsmall2(a*b/d, d);
}
/* Z/2xZ/2, resp Z/4 for n even, resp. odd */
static GEN
groupH(long n) { return odd(n)? cyclic(4): dicyclic(2,2); }

static long
get_red(struct red *S, struct igusa_p *Ip, GEN polh, GEN p, long alpha, long r)
{
  GEN val = Ip->val;
  long indice;
  switch(r)
  {
    case 0:
      indice = FpX_is_squarefree(FpX_red(polh,p), p)
               ? 0
               : val[6] - val[7] + val[8]/Ip->eps;
      S->t = stack_sprintf("I{%ld}", indice);
      S->tnum = 1;
      S->pages = "159-177";
      S->g = cyclic(indice);
      return indice ? indice: 1;
    case 6:
      if (alpha == 0) /* H(px) /p^3 */
        polh = ZX_Z_divexact(ZX_unscale_div(polh,p), sqri(p));
      indice = FpX_is_squarefree(FpX_red(polh,p), p)
               ? 0
               : val[6] - val[7] + val[8]/Ip->eps;
      S->t = stack_sprintf("I*{%ld}", indice);
      S->tnum = 1.5;
      S->pages = "159-177";
      S->g = groupH(indice);
      return indice + 5;
    case 3:
      S->t = "III";
      S->tnum = 3;
      S->pages = "161-177";
      S->g = cyclic(2);
      return 2;
    case 9:
      S->t = "III*";
      S->tnum = 3.5;
      S->pages = "162-177";
      S->g = cyclic(2);
      return 8;
    case 2:
      S->t = "II";
      S->tnum = 2;
      S->pages = "159-174";
      S->g = cyclic(1);
      return 1;
    case 8:
      S->t = "IV*";
      S->tnum = 4.5;
      S->pages = "160-175";
      S->g = cyclic(3);
      return 7;
    case 4:
      S->t = "IV";
      S->tnum = 4;
      S->pages = "160-174";
      S->g = cyclic(3);
      return 3;
    case 10:
      S->t = "II*";
      S->tnum = 2.5;
      S->pages = "160-174";
      S->g = cyclic(1);
      return 9;
    default: pari_err_BUG("get_red [type]");
      S->t = "";
      S->tnum = 0;
      S->pages = ""; /* gcc -Wall */
      S->g = NULL;
      return -1; /*LCOV_EXCL_LINE*/
  }
}

/* reduce a/b; assume b > 0 */
static void
ssQ_red(long a, long b, long *n, long *d)
{
  long g = ugcd(labs(a), b);
  if (g > 1) { a /= g; b /= g; }
  *n = a; *d = b;
}
/* denom(a/b); assume b > 0 */
static long
ssQ_denom(long a, long b)
{
  long g = ugcd(labs(a), b);
  return g == 1? b: b / g;
}
/* n = lcm(d, denom(a/b)); r = (a/b * n mod n); assume b > 0 and d > 0 */
static void
get_nr(long d, long a, long b, long *n, long *r)
{
  long c, A, B;
  ssQ_red(a, b, &A,&B);
  c = d / ugcd(d, B);
  *n = B * c;
  *r = smodss(A * c, *n);
}
/* n = lcm(denom(a/b), denom(c/d)); r = (a/b * n mod n); q = (c/d * n mod n);
 * assume b > 0 and d > 0 */
static void
get_nrq(long a, long b, long c, long d, long *n, long *r, long *q)
{
  long g, A, B, C, D;
  ssQ_red(a, b, &A,&B);
  ssQ_red(c, d, &C,&D);
  g = ugcd(B,D);
  *n = B * (D/g);
  *r = smodss(A * (D/g), *n);
  *q = smodss(C * (B/g), *n);
}

/* Ip->tt = 1 */
static long
tame_1(struct igusa *I, struct igusa_p *Ip)
{
  GEN p = Ip->p, val = Ip->val;
  long condp = -1, va0, va5, r, n;
  va0 = myval(I->a0,p);
  va5 = myval(I->A5,p);
  if (!gequal0(I->A5) && 20*va0+val[6] > 6*va5)
    get_nr(ssQ_denom(5*val[6]-6*va5, 40), val[6]-2*va5, 20, &n,&r);
  else
    get_nr(ssQ_denom(5*va0-val[6], 10), 10*va0-val[6], 30, &n,&r);
  switch(n)
  {
    case 1:
      condp = 0;
      Ip->type = "[I{0-0-0}] page 155";
      Ip->neron = cyclic(1); break;
    case 2:
      switch(r)
      {
        case 0:
          condp = 4;
          Ip->type = "[I*{0-0-0}] page 155";
          Ip->neron = mkvecsmall4(2,2,2,2); break;
        case 1:
          condp = 2;
          Ip->type = "[II] page 155";
          Ip->neron = cyclic(1); break;
        default: pari_err_BUG("tame_1 [bug1]");
      }
      break;
    case 4:
      condp = 4;
      Ip->type = "[VI] page 156";
      Ip->neron = dicyclic(2,2); break;
    default: pari_err_BUG("tame_1 [bug8]");
  }
  return condp;
}

/* (4.2) */
static long
tame_234_init(struct igusa *I, struct igusa_p *Ip, long *n, long *q, long *r)
{
  long va0, va5, vb2, v12 = -1, flc = 1;
  GEN p = Ip->p;
  switch(Ip->tt)
  {
    case 2: v12 = myval(I->i12,  Ip->p); break;
    case 3: v12 = 3*myval(I->i4, Ip->p); break;
    case 4: v12 = 6*myval(I->j2, Ip->p); break;
  }
  va0 = myval(I->a0,p);
  va5 = myval(I->A5,p);
  vb2 = myval(I->B2,p);
  if (9*vb2 >= 6*va0+v12 && 36*va5 >= 120*va0+5*v12)
  {
    get_nrq(12*va0-v12,36, 6*va0-v12,12, n, r, q);
  }
  else if (120*va0+5*v12 > 36*va5 && 60*vb2 >= 12*va5+5*v12)
  {
    ssQ_red(36*va5-25*v12,240, q,n);
    *r = smodss(-2* *q, *n);
  }
  else /* 6*va0+v12 > 9*vb2 && 12*va5+5*v12 > 60*vb2 */
  {
    get_nrq(v12-6*vb2,12, v12-9*vb2,12, n,r,q);
    flc = 0;
  }
  return flc;
}

/* Ip->tt = 2 */
static long
tame_2(struct igusa *I, struct igusa_p *Ip)
{
  long condp = -1, d, n, q, r;
  GEN val = Ip->val;
  (void)tame_234_init(I, Ip, &n, &q, &r);
  d = n * (6*val[6]-5*val[7]) / 6;
  switch(n)
  {
    case 1: condp = 1;
      Ip->type = stack_sprintf("[I{%ld-0-0}] page 170", d);
      Ip->neron = cyclic(d); break;
    case 2:
      switch(r)
      {
        case 0: condp = 4;
          Ip->type = stack_sprintf("[I*{%ld-0-0}] page 171",d/2);
          Ip->neron = shallowconcat(dicyclic(2,2),groupH(d/2)); break;
        case 1:
          switch(q)
          {
            case 0: condp = 2;
              Ip->type = stack_sprintf("[II*{%ld-0}] page 172",d/2);
              Ip->neron = cyclic(1); break;
            case 1: condp = 3;
              Ip->type = stack_sprintf("[II{%ld-0}] page 171",d/2);
              Ip->neron = cyclic(2*d); break;
            default: pari_err_BUG("tame2 [bug10]");
          }
          break;
        default: pari_err_BUG("tame2 [bug11]");
      }
      break;
    case 3: condp = 3;
      Ip->neron = cyclic(d);
      switch(r)
      {
        case 1:
          Ip->type = stack_sprintf("[II{%ld}-IV] page 175", (d-2)/3);
          break;
        case 2:
          Ip->type = stack_sprintf("[II{%ld}-IV*] page 175", (d-1)/3);
          break;
        default: pari_err_BUG("tame2 [bug12]");
      }
      break;
    case 4:
      switch(r)
      {
        case 1:
          switch(q)
          {
            case 1: condp = 3;
              Ip->type = stack_sprintf("[II{%ld}-III] page 177",(d-2)/4);
              Ip->neron = cyclic(d/2); break;
            case 3: condp = 4;
              Ip->type = stack_sprintf("[II*{%ld}-III*] page 178",(d-2)/4);
              Ip->neron = cyclic(8); break;
            default: pari_err_BUG("tame2 [bug13]");
          }
          break;
        case 3:
          switch(q)
          {
            case 1: condp = 4;
              Ip->type = stack_sprintf("[II*{%ld}-III] page 178",(d-2)/4);
              Ip->neron = cyclic(8); break;
            case 3: condp = 3;
              Ip->type = stack_sprintf("[II{%ld}-III*] page 178",(d-2)/4);
              Ip->neron = cyclic(d/2); break;
            default: pari_err_BUG("tame2 [bug14]");
          }
          break;
        default: pari_err_BUG("tame2 [bug15]");
      }
      break;
    case 6:
      switch(r)
      {
        case 2: condp = 4;
          Ip->type = stack_sprintf("[II*-II*{%ld}] page 176", (d-4)/6);
          Ip->neron = groupH((d+2)/6); break;
        case 4: condp = 4;
          Ip->type = stack_sprintf("[II-II*{%ld}] page 176", (d-2)/6);
          Ip->neron = groupH((d+4)/6); break;
        default: pari_err_BUG("tame2 [bug16]");
      }
      break;
    default: pari_err_BUG("tame2 [bug17]");
  }
  return condp;
}

/* Ip->tt = 3 */
static long
tame_3(struct igusa *I, struct igusa_p *Ip)
{
  long condp = -1, n, q, r, va5, d1, d2;
  long flc = tame_234_init(I, Ip, &n, &q, &r);
  GEN val = Ip->val;

  va5 = 2*val[6]-5*val[3];
  d1 = minss(n * (val[7]-3*val[3]), n * va5 / 4);
  d2 = n * va5 / 2 - d1;
  switch(n)
  {
    case 1: condp = 2;
      Ip->type = stack_sprintf("[I{%ld-%ld-0}] page 179", d1,d2);
      Ip->neron = dicyclic(d1,d2); break;
    case 2:
      switch(r)
      {
        case 0: condp = 4;
          Ip->type = stack_sprintf("[I*{%ld-%ld-0}] page 180", d1/2,d2/2);
          Ip->neron = shallowconcat(groupH(d1/2),groupH(d2/2)); break;
        case 1: condp = 3;
          if (flc)
          {
            Ip->type = stack_sprintf("[2I{%ld}-0] page 181", d1);
            Ip->neron = cyclic(d1);
          }
          else
          { /* FIXME: "or" same with d1<->d2 */
            Ip->type = stack_sprintf("[II{%ld-%ld}] page 182",d1/2,d2/2);
            Ip->neron = ((d1*d2-4)&7)? cyclic(2*d1): dicyclic(d1,2);
          }
          break;
        default: pari_err_BUG("tame3 [bug20]");
      }
      break;
    case 4: condp = 4;
      Ip->type = stack_sprintf("[III{%ld}] page 182", d1/2);
      Ip->neron = groupH(d1/2); break;
    default: pari_err_BUG("tame3 [bug21]");
  }
  return condp;
}

/* Ip->tt = 4 */
static long
tame_4(struct igusa *I, struct igusa_p *Ip)
{
  long condp = -1, d1,d2,d3, f1,f2, g, h, n, q, r, vl,vn,vm, e1,e2,e3;
  GEN val = Ip->val;
  (void)tame_234_init(I, Ip, &n, &q, &r);
  vl = val[6]-5*val[1];
  vn = val[7]-6*val[1];
  vm = val[2]-2*val[1]; /* all >= 0 */
  e1 = min3(2*vl, 3*vn, 6*vm);
  e2 = minss(6*vl - e1, 12*vn - 2*e1); /* >= 0 */
  e3 = 12*vl - (2*e1+e2); /* >= 0 */
  d1 = e1*n / 6;
  d2 = e2*n / 12;
  d3 = e3*n / 12;
  g = d1*d2 + d1*d3 + d2*d3;
  h = ugcd(ugcd(d1,d2),d3);
  switch(n)
  {
    case 1: condp = 2;
      Ip->type = stack_sprintf("[I{%ld-%ld-%ld}] page 182",d1,d2,d3);
      Ip->neron = dicyclic(h,g/h); break;
    case 2:
      switch(r)
      {
        case 0: condp = 4;
          Ip->type = stack_sprintf("[I*{%ld-%ld-%ld}] page 183",d1/2,d2/2,d3/2);
          Ip->neron = shallowconcat(groupH(g/4), groupH(2-((h&2)>>1))); break;
        case 1:
          if      (d1 == d2 || d1 == d3) f2 = d1;
          else if (d2 == d3) f2 = d2;
          else {
            pari_err_BUG("tame4 [bug23]");
            return -1; /*LCOV_EXCL_LINE*/
          }
          f1 = d1+d2+d3-2*f2;
          switch(q)
          {
            case 0: condp = 3;
              Ip->type = stack_sprintf("[II*{%ld-%ld}] page 184", f1/2,f2);
              Ip->neron = cyclic(f2); break;
            case 1: condp = 3;
              Ip->type = stack_sprintf("[II{%ld-%ld}] page 183", f1/2,f2);
              Ip->neron = cyclic(2*f1+f2); break;
            default: pari_err_BUG("tame4 [bug24]");
          }
          break;
        default: pari_err_BUG("tame4 [bug25]");
      }
      break;
    case 3: condp = 4;
      Ip->type = stack_sprintf("[III{%ld}] page 184",d1);
      Ip->neron = (d1%3)? cyclic(9): dicyclic(3,3); break;
    case 6: condp = 4;
      Ip->type = stack_sprintf("[III*{%ld}] page 184",d1/2);
      Ip->neron = cyclic(1); break;
    default: pari_err_BUG("tame4 [bug26]");
  }
  return condp;
}

/* p = 3 */
static void
tame_567_init_3(struct igusa_p *Ip, long dk,
                long *pd, long *pn, long *pdm, long *pr)
{
  long n = 1 + Ip->r1/6;
  *pd = n * dk / 36; /* / (12*Ip->eps) */
  *pn = n;
  *pr = -1; /* unused */
  *pdm = 0;
}

/* (4.3) */
static void
tame_567_init(struct igusa *I, struct igusa_p *Ip, long dk,
              long *pd, long *pn, long *pdm, long *pr)
{
  long ndk, ddk;
  GEN p = Ip->p, val = Ip->val;

  if (equaliu(p,3)) { tame_567_init_3(Ip, dk, pd, pn, pdm, pr); return; }
  /* assume p > 3, Ip->eps = 1 */
  ssQ_red(dk, 12, &ndk, &ddk);
  if (! odd(val[8]))
  {
    long va0 = myval(I->a0,p), va2 = myval(I->A2,p), va3 = myval(I->A3,p);
    long va5 = myval(I->A5,p), vb2 = myval(I->B2,p);
    long v1 = 2*va3-4*va0-val[1],   v2 = 6*va5-20*va0-5*val[1];
    long v3 = 3*vb2-2*va0-2*val[1], v4 = 10*vb2-2*va5-5*val[1];
    if (v3 >= 0 && v2 >= 0 && v1 >= 0)
    {
      if (v1==0 || v2==0) get_nr(ddk, va0+val[1], 6,pn,pr); /* Prop 4.3.1 (a) */
      else
      { /* Prop 4.3.1 (d) */
        long v5 = myval(subii(mulii(I->A2,I->A3),mului(3,I->A5)),p);
        if (gequal0(I->A2)) pari_err_BUG("tame567 [bug27]");
        get_nr(ddk, 12*va0 + min3(dk, 6*va3-9*va2, 4*v5 - 10*va2), 24, pn,pr);
      }
    }
    else if (v2 < 0 && v4 >= 0)
      get_nr(ddk, 2*va5+val[1], 8, pn,pr); /* Prop 4.3.1 (b) */
    else /* (v3 < 0 && v4 < 0) */
      get_nr(ddk, vb2, 4, pn,pr); /* Prop 4.3.1 (c) */
    *pd = (*pn/ddk) * ndk;
  }
  else
  {
    *pr = ndk;
    *pn = 2*ddk;
    *pd = 2*ndk;
  }
  *pdm = smodss(*pd, *pn);
}

static long
tame_5(struct igusa *I, struct igusa_p *Ip)
{
  long condp = -1, d, n, dm, r, dk;
  GEN val = Ip->val;

  dk = Ip->eps*val[6]-5*val[8];
  tame_567_init(I, Ip, dk, &d, &n, &dm, &r);
  if (! odd(val[8]))
  {
    switch(n)
    {
      case 1: condp = 0;
        Ip->type = stack_sprintf("[I{0}-I{0}-%ld] page 158", d);
        Ip->neron = cyclic(1); break;
      case 2:
        switch(dm)
        {
          case 0: condp = 4;
            Ip->type = stack_sprintf("[I*{0}-I*{0}-%ld] page 158",(d-2)/2);
            Ip->neron = mkvecsmall4(2,2,2,2); break;
          case 1: condp = 2;
            Ip->type = stack_sprintf("[I{0}-I*{0}-%ld] page 159",(d-1)/2);
            Ip->neron = dicyclic(2,2); break;
        }
        break;
      case 3:
        switch(dm)
        {
          case 0: condp = 4;
            Ip->type = stack_sprintf("[IV-IV*-%ld] page 165",(d-3)/3);
            Ip->neron = dicyclic(3,3); break;
          case 1:
            switch(r)
            {
              case 0: case 1: condp = 2;
                Ip->type = stack_sprintf("[I{0}-IV-%ld] page 160",(d-1)/3);
                Ip->neron = cyclic(3); break;
              case 2: condp = 4;
                Ip->type = stack_sprintf("[IV*-IV*-%ld] page 166",(d-4)/3);
                Ip->neron = dicyclic(3,3); break;
            }
            break;
          case 2:
            switch(r)
            {
              case 0: case 2: condp = 2;
                Ip->type = stack_sprintf("[I{0}-IV*-%ld] page 160",(d-2)/3);
                Ip->neron = cyclic(3); break;
              case 1: condp = 4;
                Ip->type = stack_sprintf("[IV-IV-%ld] page 165",(d-2)/3);
                Ip->neron = dicyclic(3,3); break;
            }
            break;
        }
        break;
      case 4:
        switch(dm)
        {
          case 0: condp = 4;
            Ip->type = stack_sprintf("[III-III*-%ld] page 169",(d-4)/4);
            Ip->neron = dicyclic(2,2); break;
          case 1:
            switch(r)
            {
              case 0: case 1: condp = 2;
                Ip->type = stack_sprintf("[I{0}-III-%ld] page 161",(d-1)/4);
                Ip->neron = cyclic(2); break;
              case 2: case 3: condp = 4;
                Ip->type = stack_sprintf("[I*{0}-III*-%ld] page 162",(d-5)/4);
                Ip->neron = mkvecsmall3(2,2,2); break;
            }
            break;
          case 2: condp = 4;
            Ip->neron = dicyclic(2,2);
            switch(r)
            {
              case 1:
                Ip->type = stack_sprintf("[III-III-%ld] page 169",(d-2)/4);
                break;
              case 3:
                Ip->type = stack_sprintf("[III*-III*-%ld] page 169",(d-6)/4);
                break;
              default: pari_err_BUG("tame5 [bug29]");
            }
            break;
          case 3:
            switch(r)
            {
              case 0: case 3: condp = 2;
                Ip->type = stack_sprintf("[I{0}-III*-%ld] page 162",(d-3)/4);
                Ip->neron = cyclic(2); break;
              case 1: case 2: condp = 4;
                Ip->type = stack_sprintf("[I*{0}-III-%ld] page 162",(d-3)/4);
                Ip->neron = mkvecsmall3(2,2,2); break;
            }
            break;
        }
        break;
      case 6:
        switch(dm)
        {
          case 0: condp = 4;
            Ip->type = stack_sprintf("[II-II*-%ld] page 163",(d-6)/6);
            Ip->neron = cyclic(1); break;
          case 1:
            switch(r)
            {
              case 0: case 1: condp = 2;
                Ip->type = stack_sprintf("[I{0}-II-%ld] page 159",(d-1)/6);
                Ip->neron = cyclic(1); break;
              case 2: case 5: condp = 4;
                Ip->type = stack_sprintf("[II*-IV-%ld] page 164",(d-7)/6);
                Ip->neron = cyclic(3); break;
              case 3: case 4: condp = 4;
                Ip->type = stack_sprintf("[I*{0}-IV*-%ld] page 161",(d-7)/6);
                Ip->neron = mkvecsmall2(6,2); break;
            }
            break;
          case 2:
            switch(r)
            {
              case 1: condp = 4;
                Ip->type = stack_sprintf("[II-II-%ld] page 163",(d-2)/6);
                Ip->neron = cyclic(1); break;
              case 3: case 5: condp = 4;
                Ip->type = stack_sprintf("[I*{0}-II*-%ld] page 160",(d-8)/6);
                Ip->neron = dicyclic(2,2); break;
              default: pari_err_BUG("tame5 [bug30]");
            }
            break;
          case 3:
            Ip->neron = cyclic(3);
            switch(r)
            {
              case 1: case 2: condp = 4;
                Ip->type = stack_sprintf("[II-IV-%ld] page 164",(d-3)/6);
                break;
              case 4: case 5: condp = 4;
                Ip->type = stack_sprintf("[II*-IV*-%ld] page 164",(d-9)/6);
                break;
              default: pari_err_BUG("tame5 [bug31]");
            }
            break;
          case 4:
            switch(r)
            {
              case 1: case 3: condp = 4;
                Ip->type = stack_sprintf("[I*{0}-II-%ld] page 160",(d-4)/6);
                Ip->neron = dicyclic(2,2); break;
              case 5: condp = 4;
                Ip->type = stack_sprintf("[II*-II*-%ld] page 163",(d-10)/6);
                Ip->neron = cyclic(1); break;
              default: pari_err_BUG("tame5 [bug32]");
            }
            break;
          case 5:
            switch(r)
            {
              case 0: case 5: condp = 2;
                Ip->type = stack_sprintf("[I{0}-II*-%ld] page 160",(d-5)/6);
                Ip->neron = cyclic(1); break;
              case 1: case 4: condp = 4;
                Ip->type = stack_sprintf("[II-IV*-%ld] page 164",(d-5)/6);
                Ip->neron = cyclic(3); break;
              case 2: case 3: condp = 4;
                Ip->type = stack_sprintf("[I*{0}-IV-%ld] page 161",(d-5)/6);
                Ip->neron = mkvecsmall2(6,2); break;
            }
            break;
          default: pari_err_BUG("tame5 [bug33]");
        }
        break;
      case 12:
        condp = 4;
        switch(dm)
        {
          case 1:
            switch(r)
            {
              case 3: case 10:
                Ip->type = stack_sprintf("[II*-III-%ld] page 166",(d-13)/12);
                Ip->neron = cyclic(2); break;
              case 4: case 9:
                Ip->type = stack_sprintf("[III*-IV-%ld] page 167",(d-13)/12);
                Ip->neron = cyclic(6); break;
              default: pari_err_BUG("tame5 [bug34]");
            }
            break;
          case 5:
            switch(r)
            {
              case 2: case 3:
                Ip->type = stack_sprintf("[II-III-%ld] page 166",(d-5)/12);
                Ip->neron = cyclic(2); break;
              case 8: case 9:
                Ip->type = stack_sprintf("[III*-IV*-%ld] page 168",(d-17)/12);
                Ip->neron = cyclic(6); break;
              default: pari_err_BUG("tame5 [bug35]");
            }
            break;
          case 7:
            switch(r)
            {
              case 3: case 4:
                Ip->type = stack_sprintf("[III-IV-%ld] page 167",(d-7)/12);
                Ip->neron = cyclic(6); break;
              case 9: case 10:
                Ip->type = stack_sprintf("[II*-III*-%ld] page 167",(d-19)/12);
                Ip->neron = cyclic(2); break;
              default: pari_err_BUG("tame5 [bug36]");
            }
            break;
          case 11:
            switch(r)
            {
              case 3: case 8:
                Ip->type = stack_sprintf("[III-IV*-%ld] page 168",(d-11)/12);
                Ip->neron = cyclic(6); break;
              case 2: case 9:
                Ip->type = stack_sprintf("[II-III*-%ld] page 166",(d-11)/12);
                Ip->neron = cyclic(2); break;
              default: pari_err_BUG("tame5 [bug37]");
            }
            break;
          default: pari_err_BUG("tame5 [bug38]");
        }
        break;
      default: pari_err_BUG("tame5 [bug39]");
    }
  }
  else
  {
    r %= (n >> 1);
    switch(n)
    {
      case 2: condp = 2;
        Ip->type = stack_sprintf("[2I{0}-%ld] page 159",(d/2));
        Ip->neron = cyclic(1); break;
      case 4: condp = 4;
        Ip->type = stack_sprintf("[2I*{0}-%ld] page 159",(d/2-1)/2);
        Ip->neron = dicyclic(2,2); break;
      case 6: condp = 4;
        Ip->neron = cyclic(3);
        switch(r)
          {
          case 1:
            Ip->type = stack_sprintf("[2IV-%ld] page 165",(d/2-1)/3);
            break;
          case 2:
            Ip->type = stack_sprintf("[2IV*-%ld] page 165",(d/2-2)/3);
            break;
          default: pari_err_BUG("tame5 [bug40]");
          }
        break;
      case 8: condp = 4;
        Ip->neron = cyclic(2);
        switch(r)
        {
          case 1:
            Ip->type = stack_sprintf("[2III-%ld] page 168",(d/2-1)/4);
            break;
          case 3:
            Ip->type = stack_sprintf("[2III*-%ld] page 168",(d/2-3)/4);
            break;
          default: pari_err_BUG("tame5 [bug41]");
        }
        break;
      case 12: condp = 4;
        Ip->neron = cyclic(1);
        switch(r)
        {
          case 1:
            Ip->type = stack_sprintf("[2II-%ld] page 162",(d/2-1)/6);
            break;
          case 5:
            Ip->type = stack_sprintf("[2II*-%ld] page 163",(d/2-5)/6);
            break;
          default: pari_err_BUG("tame5 [bug42]");
        }
        break;
      default: pari_err_BUG("tame5 [bug43]");
    }
  }
  return condp;
}

static long
tame_6(struct igusa *I, struct igusa_p *Ip)
{
  long condp = -1, d, d1, n, dm, r, dk;
  GEN val = Ip->val;

  dk = Ip->eps*val[7]-6*val[8];
  tame_567_init(I, Ip, dk, &d, &n, &dm, &r);
  d1 = n * (Ip->eps*(val[6]-val[7])+val[8]) / Ip->eps;
  switch(n)
  {
    case 1: condp = 1;
      Ip->type = stack_sprintf("[I{0}-I{%ld}-%ld] page 170",d1,d);
      Ip->neron = cyclic(d1); break;
    case 2:
      switch(dm)
      {
        case 0: condp = 4;
          Ip->type=stack_sprintf("[I*{0}-I*{%ld}-%ld] page 171", d1/2,(d-2)/2);
          Ip->neron = shallowconcat(groupH(d1/2), dicyclic(2,2)); break;
        case 1: return -1;
        default: pari_err_BUG("tame6 [bug44]");
      }
      break;
    case 3: condp = 3;
      Ip->neron = dicyclic(3,d1/3);
      switch(dm)
      {
        case 1:
          Ip->type = stack_sprintf("[I{%ld}-IV-%ld] page 173",d1/3,(d-1)/3);
          break;
        case 2:
          Ip->type = stack_sprintf("[I{%ld}-IV*-%ld] page 173",d1/3,(d-2)/3);
          break;
        default: pari_err_BUG("tame6 [bug45]");
      }
      break;
    case 4:
      switch(dm)
      {
        case 1:
          switch(r)
          {
            case 0: case 1: condp = 3;
              Ip->type=stack_sprintf("[I{%ld}-III-%ld] page 176",d1/4,(d-1)/4);
              Ip->neron = dicyclic(2,d1/4); break;
            case 2: case 3: condp = 4;
              Ip->type=stack_sprintf("[I*{%ld}-III*-%ld] page 177",d1/4,(d-5)/4);
              Ip->neron = shallowconcat(groupH(d1/4), cyclic(2)); break;
            default: pari_err_BUG("tame6 [bug46]");
          }
          break;
        case 3:
          switch(r)
          {
            case 0: case 3: condp = 3;
              Ip->type=stack_sprintf("[I{%ld}-III*-%ld] page 176",d1/4,(d-3)/4);
              Ip->neron = dicyclic(2,d1/4); break;
            case 1: case 2: condp = 4;
              Ip->type=stack_sprintf("[I*{%ld}-III-%ld] page 177",d1/4,(d-3)/4);
              Ip->neron = shallowconcat(groupH(d1/4), cyclic(2)); break;
            default: pari_err_BUG("tame6 [bug47]");
          }
          break;
        default: pari_err_BUG("tame6 [bug48]");
      }
      break;
    case 6:
      switch(dm)
      {
        case 1:
          switch(r)
          {
            case 0: case 1: condp = 3;
              Ip->type = stack_sprintf("[I{%ld}-II-%ld] page 172",d1/6,(d-1)/6);
              Ip->neron = cyclic(d1/6); break;
            case 3: case 4: condp = 4;
              Ip->type=stack_sprintf("[I*{%ld}-IV*-%ld] page 174",d1/6,(d-7)/6);
              Ip->neron = shallowconcat(groupH(d1/6), cyclic(3)); break;
            default: pari_err_BUG("tame6 [bug49]");
          }
          break;
        case 2: condp = 4;
          Ip->type = stack_sprintf("[I*{%ld}-II*-%ld] page 174",d1/6,(d-8)/6);
          Ip->neron = groupH(d1/6); break;
        case 4: condp = 4;
          Ip->type = stack_sprintf("[I*{%ld}-II-%ld] page 173",d1/6,(d-4)/6);
          Ip->neron = groupH(d1/6); break;
        case 5:
          switch(r)
          {
            case 0: case 5: condp = 3;
              Ip->type=stack_sprintf("[I{%ld}-II*-%ld] page 172",d1/6,(d-5)/6);
              Ip->neron = cyclic(d1/6); break;
            case 2: case 3: condp = 4;
              Ip->type=stack_sprintf("[I*{%ld}-IV-%ld] page 174",d1/6,(d-5)/6);
              Ip->neron = shallowconcat(groupH(d1/6), cyclic(3)); break;
            default: pari_err_BUG("tame6 [bug50]");
          }
          break;
        default: pari_err_BUG("tame6 [bug51]");
      }
      break;
    default: pari_err_BUG("tame6 [bug52]");
  }
  return condp;
}

static long
tame_7(struct igusa *I, struct igusa_p *Ip)
{
  long condp = -1, d, D, d1, d2, n, dm, r, dk;
  GEN val = Ip->val;

  dk = 3*(Ip->eps*val[3]-2*val[8]);
  tame_567_init(I, Ip, dk, &d, &n, &dm, &r);
  D = n * (Ip->eps*(val[6]-3*val[3])+val[8]) / Ip->eps;
  d1 = minss(n * (val[7]-3*val[3]), D/2);
  d2 = D - d1;
  /* d1 <= d2 */
  switch(n)
  {
    case 1: condp = 2;
      Ip->type = stack_sprintf("[I{%ld}-I{%ld}-%ld] page 179",d1,d2,d);
      Ip->neron = dicyclic(d1,d2); break;
    case 2:
      if (odd(val[8]))
      {
        condp = 3;
        Ip->type = stack_sprintf("[2I{%ld}-%ld] page 181",d1,d/2);
        Ip->neron = cyclic(d1);
      }
      else if (dm == 0)
      {
        condp = 4;
        Ip->type = stack_sprintf("[I*{%ld}-I*{%ld}-%ld] page 180", d1/2,d2/2,(d-2)/2);
        Ip->neron = shallowconcat(groupH(d1/2),groupH(d2/2));
      }
      else
      {
        GEN H;
        if (d1 != d2) return -1;
        condp = 3; H = groupH(d1/2);
        Ip->type = stack_sprintf("[I{%ld}-I*{%ld}-%ld] page 180", d1/2,d1/2,(d-1)/2);
        Ip->neron = shallowconcat(H, H);
      }
      break;
    case 4: condp = 4;
      Ip->type = stack_sprintf("[2I*{%ld}-%ld] page 181",d1/2,(d-2)/4);
      Ip->neron = groupH(d1/2); break;
    default: pari_err_BUG("tame7 [bug55]");
  }
  return condp;
}

static long labelm3(GEN polh, long t60, long alpha, long Dmin, struct igusa *I, struct igusa_p *Ip);
static long
tame(GEN polh, long t60, long alpha, long Dmin, struct igusa *I, struct igusa_p *Ip)
{
  long d;
  Ip->tame = 1;
  switch(Ip->tt)
  {
    case 1: return tame_1(I,Ip);
    case 2: return tame_2(I,Ip);
    case 3: return tame_3(I,Ip);
    case 4: return tame_4(I,Ip);
    case 5: return tame_5(I,Ip);
    case 6: d = tame_6(I,Ip); break;
    default:d = tame_7(I,Ip); break;
  }
  if (d < 0) d = labelm3(polh,t60,alpha,Dmin,I,Ip); /* => tt=6 or 7 */
  return d;
}

/* maxc = maximum conductor valuation at p */
static long
get_maxc(GEN p)
{
  switch (itos_or_0(p))
  {
    case 2:  return 20; break;
    case 3:  return 10; break;
    case 5:  return 9; break;
    default: return 4; break; /* p > 5 */
  }
}

/* p = 3 */
static long
quartic(GEN polh, long alpha, long Dmin, struct igusa_p *Ip)
{
  GEN val = Ip->val, p = Ip->p;
  GEN polf = polymini_zi2(ZX_Z_mul(polh, powiu(p, alpha)));
  long condp = -1, d, R, r1, beta;
  r1 = polf[1];
  beta = polf[2];
  R = beta/2;
  switch(Ip->tt)
  {
    case 1: case 5: d = 0;break;
    case 3: d = val[6] - 5*val[3]/2;break;
    case 7: d = val[6] - 3*val[3] + val[8]/Ip->eps;break;
    default: pari_err_BUG("quartic [type choices]");
             d = 0; /*LCOV_EXCL_LINE*/
  }
  switch(r1)
  {
    case 0:
      if (d)
      {
        condp = 3;
        Ip->type = stack_sprintf("[2I{%ld}-%ld] page 181",d,R);
        Ip->neron = cyclic(d);
      }
      else
      {
        condp = 2;
        Ip->neron = cyclic(1);
        if (R) Ip->type = stack_sprintf("[2I{0}-%ld] page 159",R);
        else   Ip->type = "[II] page 155";
      }
      break;
    case 6: condp = 4;
      Ip->type = stack_sprintf("[2I*{%ld}-%ld] pages 159, 181",d,R);
      Ip->neron = dicyclic(2,2); break;
    case 3: condp = 4;
      Ip->type = stack_sprintf("[2III-%ld] page 168",R);
      Ip->neron = cyclic(2); break;
    case 9: condp = 4;
      Ip->type = stack_sprintf("[2III*-%ld] page 168",R);
      Ip->neron = cyclic(2); break;
    case 2: condp = Dmin-12*R-13;
      Ip->type = stack_sprintf("[2II-%ld] page 162",R);
      Ip->neron = cyclic(1); break;
    case 8: condp = Dmin-12*R-19;
      Ip->type = stack_sprintf("[2IV*-%ld] page 165",R);
      Ip->neron = cyclic(3); break;
    case 4: condp = Dmin-12*R-15;
      Ip->type = stack_sprintf("[2IV-%ld] page 165",R);
      Ip->neron = cyclic(3); break;
    case 10: condp = Dmin-12*R-21;
      Ip->type = stack_sprintf("[2II*-%ld] page 163",R);
      Ip->neron = cyclic(1); break;
    default: pari_err_BUG("quartic [type1]");
  }
  if (condp > get_maxc(p) || condp < 0) pari_err_BUG("quartic [conductor]");
  return condp;
}

static long
litredtp(long alpha, long alpha1, long t60, long t60_1, GEN polh, GEN polh1,
         long Dmin, long R, struct igusa *I, struct igusa_p *Ip)
{
  GEN val = Ip->val, p = Ip->p;
  long condp = -1, indice, d;

  if ((Ip->r1 == 0||Ip->r1 == 6) && (Ip->r2 == 0||Ip->r2 == 6))
  { /* (r1,r2) = (0,0), (0,6), (6,0) or (6,6) */
    if (Ip->tt == 5)
    {
      switch(Ip->r1 + Ip->r2)
      {
      case 0: /* (0,0) */
        condp = 0;
        Ip->type = stack_sprintf("[I{0}-I{0}-%ld] page 158",R);
        Ip->neron = cyclic(1); break;
      case 6: /* (0,6) or (6,0) */
        condp = 2;
        Ip->type = stack_sprintf("[I{0}-I*{0}-%ld] page 159",R);
        Ip->neron = dicyclic(2,2); break;
      case 12: /* (6,6) */
        condp = 4;
        Ip->type = stack_sprintf("[I*{0}-I*{0}-%ld] page 158",R);
        Ip->neron = mkvecsmall4(2,2,2,2); break;
      }
      return condp;
    }
    if (Ip->r1 == Ip->r2) return tame(polh, t60, alpha, Dmin, I, Ip);
    if (Ip->tt == 6)
    {
      d = val[6] - val[7] + val[8]/Ip->eps;
      if (Ip->r1 && alpha1 == 0) /* H(px) / p^3 */
        polh1 = ZX_Z_divexact(ZX_unscale_div(polh1,p), sqri(p));
      if (FpX_is_squarefree(FpX_red(polh1,p),p))
      { indice = 0; condp = 3-Ip->r2/6; }
      else
      { indice = d; condp = 3-Ip->r1/6; }
    }
    else
    { /* Ip->tt == 7 */
      long d1;
      d = val[6] - 3*val[3] + val[8]/Ip->eps;
      if (t60_1 == 60) /* H(px) / p^3 */
        polh1 = ZX_Z_divexact(ZX_unscale_div(polh1,p), sqri(p));
      d1 = minss(val[7]-3*val[3],d/2);
      if (d == 2*d1) indice = d1;
      else
      {
        indice = discpart(polh1,p,d1+1);
        if (indice>= d1+1) indice = d-d1; else indice = d1;
      }
      condp = 3;
    }
    if (Ip->r1) indice = d - indice; /* (r1,r2) = (6,0) */
    Ip->neron = shallowconcat(cyclic(indice),groupH(d-indice));
    Ip->type = stack_sprintf("[I{%ld}-I*{%ld}-%ld] page %ld",
                             indice,d-indice,R, (Ip->tt==6)? 170L: 180L);
    return condp;
  }
  if (Ip->tt == 7) pari_err_BUG("litredtp [switch ri]");
  {
    struct red __S1, __S2, *S1 = &__S1, *S2 = &__S2;
    long f1 = get_red(S1, Ip, polh1, p, alpha1, Ip->r1);
    long f2 = get_red(S2, Ip, polh,  p, alpha,  Ip->r2);
    /* reorder to normalize representation */
    if (S1->tnum > S2->tnum || (S1->tnum == S2->tnum && f1 > f2))
    { struct red *S = S1; S1 = S2; S2 = S; }
    Ip->type = stack_sprintf("[%s-%s-%ld] pages %s", S1->t,S2->t, R, S1->pages);
    Ip->neron = shallowconcat(S1->g, S2->g);
    condp = Dmin - (f1 + f2) + ((R >= 0)? 2-12*R: 4);
  }
  if (condp > get_maxc(p)) pari_err_BUG("litredtp [conductor]");
  return condp;
}

static long
labelm3(GEN h1, long t60_1, long alpha1, long Dmin, struct igusa *I, struct igusa_p *Ip)
{
  GEN h, pm, vs, val = Ip->val, p = Ip->p;
  long alpha, t60, lambda, beta, R;

  pm = polymini(ZX_Z_mul(RgX_recip6(h1), powiu(p,alpha1)), p);
  h  = gel(pm,1); vs = gel(pm,2);
  lambda= vs[1];
  t60   = vs[2];
  alpha = vs[3];
  beta  = vs[5];
  if (lambda != 3) pari_err_BUG("labelm3 [lambda != 3]");
  R = beta-(alpha1+alpha);
  if (odd(R)) pari_err_BUG("labelm3 [R odd]");
  R /= 2;
  if (R <= -2) pari_err_BUG("labelm3 [R <= -2]");
  if (val[8] % (2*Ip->eps)) pari_err_BUG("labelm3 [val(eps2)]");
  if (R >= 0 && (alpha+alpha1) >= 1) pari_err_BUG("labelm3 [minimal equation]");
  Ip->r1 = t60_1 / 10 + 6*alpha1;
  Ip->r2 = t60 / 10 + 6*alpha;
  return litredtp(alpha, alpha1, t60, t60_1, h, h1, Dmin, R, I, Ip);
}

/* p = 3 */
static long
quadratic(GEN polh, long alpha, long Dmin, struct igusa *I, struct igusa_p *Ip)
{
  long alpha1 = alpha, beta, t6, R;
  GEN vs = polymini_zi(ZX_Z_mul(polh, powiu(Ip->p,alpha)));
  t6 = vs[1];
  alpha = vs[2];
  beta  = vs[3];
  R = beta-alpha;
  if (R >= 0 && alpha1)
  {
    Dmin -= 10;
    if (DEBUGLEVEL)
      err_printf("(Care: minimal discriminant over Z[i] smaller than over Z)\n");
  }
  Ip->r2 = Ip->r1 = t6 + 6*alpha;
  return litredtp(alpha, alpha, t6*10, t6*10, polh, polh, Dmin, R, I, Ip);
}

static long
genus2localred(struct igusa *I, struct igusa_p *Ip, GEN p, GEN polmini)
{
  GEN val, vs, polh, list, c1, c2, c3, c4, c5, c6, prod;
  long i, vb5, vb6, d, Dmin, alpha, lambda, t60;
  long condp = -1, indice, vc6, mm, nb, dism;

  stable_reduction(I, Ip, p);
  val = Ip->val; Dmin = val[6];
  if (Dmin == 0)
  {
    Ip->tame = 1;
    Ip->type = "[I{0-0-0}] page 155";
    Ip->neron = cyclic(1); return 0;
  }
  if (Dmin == 1)
  {
    Ip->type = "[I{1-0-0}] page 170";
    Ip->neron = cyclic(1); return 1;
  }
  if (Dmin == 2) switch(Ip->tt)
  {
    case 2:
      Ip->type = "[I{2-0-0}] page 170";
      Ip->neron = cyclic(2); return 1;
    case 3:
      Ip->type = "[I{1-1-0}] page 179";
      Ip->neron = cyclic(1); return 2;
    case 5:
      if (cmpis(p,3) <= 0) pari_err_BUG("genus2localred [tt 1]");
      Ip->type = "[I{0}-II-0] page 159";
      Ip->neron = cyclic(1); return 2;
    default: pari_err_BUG("genus2localred [tt 2]");
  }
  if (absequaliu(p,2)) return -1;
  polh = gel(polmini,1); vs = gel(polmini,2);
  lambda = vs[1];
  t60    = vs[2];
  alpha  = vs[3];
  if (vs[4]) return equaliu(p,3)? quadratic(polh, alpha, Dmin, I, Ip):
                                  tame(polh, t60, alpha, Dmin, I, Ip);
  if (!t60 && lambda<= 2)
  {
    if (Ip->tt >= 5) pari_err_BUG("genus2localred [tt 3]");
    return tame(polh, t60, alpha, Dmin, I, Ip);
  }
  if (Dmin == 3)
  {
    switch(Ip->tt)
    {
      case 2: return tame(polh, t60, alpha, Dmin, I, Ip);
      case 3: Ip->type = "[I{2-1-0}] page 179"; Ip->neron = cyclic(2); return 2;
      case 4: Ip->type = "[I{1-1-1}] page 182"; Ip->neron = cyclic(3); return 2;
      case 5:
        if (equaliu(p,3) && t60 != 30)
          return labelm3(polh,t60,alpha,Dmin,I,Ip);
        Ip->type = "[I{0}-III-0] page 161"; Ip->neron = cyclic(2); return 2;
      case 6:
        if (equaliu(p,3)) pari_err_BUG("genus2localred [conductor]");
        Ip->type = "[I{1}-II-0] page 172"; Ip->neron = cyclic(1); return 3;
    }
    pari_err_BUG("genus2localred [switch tt 4]");
    return -1; /* LCOV_EXCL_LINE */
  }
  switch(lambda)
  {
    case 0:
      switch(t60+alpha)
      {
        case 10:
          condp = Dmin-1;
          Ip->type = "[V] page 156";
          Ip->neron = cyclic(3); break;
        case 11:
          condp = Dmin-11;
          Ip->type = "[V*] page 156";
          Ip->neron = cyclic(3); break;
        case 12:
          condp = Dmin-2;
          Ip->type = "[IX-2] page 157";
          Ip->neron = cyclic(5); break;
        case 13:
          condp = Dmin-12;
          Ip->type = "[VIII-4] page 157";
          Ip->neron = cyclic(1); break;
        case 24:
          condp = Dmin-8;
          Ip->type = "[IX-4] page 158";
          Ip->neron = cyclic(5);
          break;
        case 15: case 16:
          if (Ip->tt>= 5) pari_err_BUG("genus2localred [tt 6]");
          return tame(polh, t60, alpha, Dmin, I, Ip);
        case 20: case 21:
          {
            GEN b0, b1, b2, b3, b4, b5, b6, b02, b03, b04, b05;
            RgX_to_06(polh, &b0,&b1,&b2,&b3,&b4,&b5,&b6);
            vb5 = myval(b5,p);
            vb6 = myval(b6,p);
            if (vb6 >= 3)
            {
              if (vb5 < 2) pari_err_BUG("genus2localred [red1]");
              if (vb5 >= 3)
              {
                condp = Dmin-8;
                Ip->type = "[II*-IV-(-1)] page 164";
                Ip->neron = cyclic(3);
              }
              else
              {
                condp = Dmin-7;
                Ip->type = "[IV-III*-(-1)] page 167";
                Ip->neron = cyclic(6);
              }
              break;
            }
            if (dvdii(b0,p)) pari_err_BUG("genus2localred [b0]");
            b02 = gsqr(b0);
            b03 = gmul(b02, b0);
            b04 = gmul(b03, b0);
            b05 = gmul(b04, b0);
            c1 = gmul2n(b1,-1);
            c2 = gmul2n(gsub(gmul(b0,b2), gsqr(c1)),-1);
            c3 = gmul2n(gsub(gmul(b02,b3), gmul2n(gmul(c1,c2),1)),-1);
            c4 = gsub(gmul(b03,b4), gadd(gmul2n(gmul(c1,c3),1),gsqr(c2)));
            c5 = gsub(gmul(b04,b5), gmul2n(gmul(c2,c3),1));
            c6 = gsub(gmul(b05,b6), gsqr(c3));
            /* b0^5*H(x/b0) = (x^3+c1*x^2+c2*x+c3)^2+c4*x^2+c5*x+c6 */
            vc6 = myval(c6,p);
            if (vc6 == 2)
            {
              if (alpha)
              {
                condp = Dmin-16;
                Ip->type = "[IV] page 155";
                Ip->neron = cyclic(1);
              }
              else
              {
                condp = Dmin-6;
                Ip->type = "[III] page 155";
                Ip->neron = dicyclic(3,3);
              }
            }
            else
            {
              if (myval(c3,p) > 1) pari_err_BUG("genus2localred [c3]");
              mm = min3(3*myval(c4,p)-4, 3*myval(c5,p)-5, 3*vc6-6);
              if (alpha)
              {
                condp = Dmin-mm-16;
                Ip->type = stack_sprintf("[III*{%ld}] page 184", mm);
                Ip->neron = cyclic(1);
              }
              else
              {
                condp = Dmin-mm-6;
                Ip->type = stack_sprintf("[III{%ld}] page 184", mm);
                Ip->neron = (mm%3)? cyclic(9): dicyclic(3,3);
              }
            }
          }
          break;
        case 30:
          return equaliu(p,3)? quartic(polh, alpha, Dmin, Ip)
                             : tame(polh, t60, alpha, Dmin, I, Ip);
        default: pari_err_BUG("genus2localred [red2]");
      }
      break;
    case 1:
      switch(t60+alpha)
      {
        case 12:
          condp = Dmin;
          Ip->type = "[VIII-1] page 156";
          Ip->neron = cyclic(1); break;
        case 13:
          condp = Dmin-10;
          Ip->type = "[IX-3] page 157";
          Ip->neron = cyclic(5); break;
        case 24:
          condp = Dmin-4;
          Ip->type = "[IX-1] page 157";
          Ip->neron = cyclic(5); break;
        case 25:
          condp = Dmin-14;
          Ip->type = "[VIII-3] page 157";
          Ip->neron = cyclic(1); break;
        case 36:
          condp = Dmin-8;
          Ip->type = "[VIII-2] page 157";
          Ip->neron = cyclic(1); break;
        case 15:
          condp = Dmin-1;
          Ip->type = "[VII] page 156";
          Ip->neron = cyclic(2); break;
        case 16:
          condp = Dmin-11;
          Ip->type = "[VII*] page 156";
          Ip->neron = cyclic(2); break;
        case 20:
          if (cmpis(p,3))
          {
            d = 6*val[6]-5*val[7]-2;
            if (d%6) pari_err_BUG("genus2localred [index]");
            dism = (d/6);
          }
          else
          {
            list = padicfactors(polh,p,Dmin-5);
            nb = lg(list);
            prod = pol_1(varn(polh));
            for(i = 1;i<nb;i++)
            {
              GEN c = gel(list,i);
              if (valp(gel(c,2)) && degpol(c)<= 2) prod = RgX_mul(prod,c);
            }
            if (degpol(prod) > 2) pari_err_BUG("genus2localred [padicfactors]");
            dism = valp(RgX_disc(prod)) - 1;
          }
          condp = Dmin-dism-3;
          Ip->type = stack_sprintf("[II-II*{%ld}] page 176", dism);
          Ip->neron = groupH(dism+1); break;
        case 21:
          vb6 = myval(RgX_coeff(polh,0),p);
          if (vb6<2) pari_err_BUG("genus2localred [red3]");
          condp = Dmin-14;
          Ip->type = "[IV*-II{0}] page 175";
          Ip->neron = cyclic(1); break;
        case 30:
          vb5 = myval(RgX_coeff(polh,1),p);
          if (vb5 == 2)
          {
            if (Ip->tt >= 5) pari_err_BUG("genus2localred [tt 6]");
            return tame(polh, t60, alpha, Dmin, I, Ip);
          }
          condp = Dmin-7;
          Ip->type = "[II*-III-(-1)] page 167";
          Ip->neron = cyclic(2); break;
      }
      break;
    case 2:
      if (ugcd(t60, 60) == 15) /* denom(theta) = 4 */
      {
        if (Ip->tt>4) pari_err_BUG("genus2localred [tt 5]");
        return tame(polh, t60, alpha, Dmin, I, Ip);
      }
      if (!equaliu(p,3) && ugcd(t60, 60) == 20) /* denom(theta) = 3 */
        return tame(polh, t60, alpha, Dmin, I, Ip);
      list = padicfactors(polh,p,Dmin-10*alpha);
      nb = lg(list); prod = pol_1(varn(polh));
      for(i = 1;i<nb;i++)
      {
        GEN c = gel(list,i);
        if (!valp(gel(c,2))) prod = RgX_mul(prod,c);
      }
      switch(degpol(prod))
      {
        GEN e0, e1, e2;
        case 0:
          dism = 0; break;
        case 1:
          e1 = gel(prod,3);
          dism = 2*valp(e1); break;
        case 2:
          e0 = gel(prod,2);
          e1 = gel(prod,3);
          e2 = gel(prod,4);
          dism = valp(gsub(gsqr(e1),gmul2n(gmul(e0,e2),2))); break;
        default:
          pari_err_BUG("genus2localred [padicfactors 2]");
          dism = 0;
      }
      switch(t60/5+alpha-4)
      {
        case 0:
          condp = Dmin-dism-1;
          Ip->type = stack_sprintf("[IV-II{%ld}] page 175", dism);
          Ip->neron = cyclic(3*dism+2); break;
        case 1:
          condp = Dmin-dism-10;
          Ip->type = stack_sprintf("[II*-II*{%ld}] page 176",dism);
          Ip->neron = groupH(dism+1); break;
        case 2: case 3:
          if (myval(RgX_coeff(polh,0),p) == 2)
          {
            if (Ip->tt>4) pari_err_BUG("genus2localred [tt 5]");
            return tame(polh, t60, alpha, Dmin, I, Ip);
          }
          dism++;
          indice = val[6]-(5*val[3]/2)-dism;
          condp = Dmin-dism-indice-2;
          Ip->type = stack_sprintf("[II{%ld-%ld}] page 182", dism,indice);
          Ip->neron = both_odd(dism,indice)? dicyclic(2,2*dism): cyclic(4*dism);
          break;
        case 4:
          condp = Dmin-dism-5;
          Ip->type = stack_sprintf("[IV*-II{%ld}] page 175",dism+1);
          Ip->neron = cyclic(3*dism+4); break;
      }
      break;
    case 3:
      if (!equaliu(p,3) || Ip->tt <= 4)
        return tame(polh, t60, alpha, Dmin, I, Ip);
      return labelm3(polh,t60,alpha,Dmin,I,Ip); /* p = 3 */
    default: pari_err_BUG("genus2localred [switch lambda]");
  }
  if (condp < 2 || condp > get_maxc(p))
    pari_err_BUG("genus2localred [conductor]");
  return condp;
}

static long
chk_pol(GEN P) {
  switch(typ(P))
  {
    case t_INT: break;
    case t_POL: RgX_check_ZX(P,"genus2red"); return varn(P); break;
    default: pari_err_TYPE("genus2red", P);
  }
  return -1;
}

/* P,Q are ZX, study Y^2 + Q(X) Y = P(X) */
GEN
genus2red(GEN PQ, GEN p)
{
  pari_sp av = avma;
  struct igusa I;
  GEN P, Q, D;
  GEN j22, j42, j2j6, a0,a1,a2,a3,a4,a5,a6, V,polr,facto,factp, vecmini, cond;
  long i, l, dd, vP,vQ;

  PQ = Q_remove_denom(PQ, &D);
  if (typ(PQ) == t_VEC && lg(PQ) == 3)
  {
    P = gel(PQ,1);
    Q = gel(PQ,2);
  }
  else
  {
    P = PQ;
    Q = gen_0;
  }

  vP = chk_pol(P);
  vQ = chk_pol(Q);
  if (vP < 0)
  {
    if (vQ < 0) pari_err_TYPE("genus2red",mkvec2(P,Q));
    P = scalarpol(P,vQ);
  }
  else if (vQ < 0) Q = scalarpol(Q,vP);
  if (p && typ(p) != t_INT) pari_err_TYPE("genus2red", p);
  if (D) P = ZX_Z_mul(P,D);

  polr = ZX_add(ZX_sqr(Q), gmul2n(P,2)); /* ZX */
  switch(degpol(polr))
  {
    case 5: case 6: break;
    default: pari_err_DOMAIN("genus2red","genus","!=", gen_2,mkvec2(P,Q));
  }

  RgX_to_03(polr, &a0,&a1,&a2,&a3);
  I.j10 = !signe(a0)? mulii(sqri(a1), ZX_disc(polr)): ZX_disc(polr);
  if (!signe(I.j10))
    pari_err_DOMAIN("genus2red","genus","<",gen_2,mkvec2(P,Q));
  I.j10 = gmul2n(I.j10, -12); /* t_INT */

  if (p == NULL)
  {
    facto = absZ_factor(I.j10);
    factp = gel(facto,1);
  }
  else
  {
    factp = mkcol(p);
    facto = mkmat2(factp, mkcol(gen_1));
  }
  l = lg(factp);
  vecmini = cgetg(l, t_COL);
  for(i = 1; i<l; i++)
  {
    GEN l = gel(factp,i), pm;
    if (i == 1 && absequaliu(l, 2)) { gel(vecmini,1) = gen_0; continue; }
    gel(vecmini,i) = pm = polymini(polr, l);
    polr = ZX_Q_mul(gel(pm,1), powiu(l, gel(pm,2)[3]));
  }
  RgX_to_06(polr, &a0,&a1,&a2,&a3,&a4,&a5,&a6);
  I.j10 = !signe(a0)? mulii(sqri(a1), ZX_disc(polr)): ZX_disc(polr);
  I.j10 = gmul2n(I.j10,-12);

  I.a0 = a0;
  I.A2 = apol2(a0,a1,a2);
  I.A3 = apol3(a0,a1,a2,a3);
  I.A5 = apol5(a0,a1,a2,a3,a4,a5);
  I.B2 = bpol2(a0,a1,a2,a3,a4);

  I.j2 = igusaj2(a0,a1,a2,a3,a4,a5,a6);
  I.j4 = igusaj4(a0,a1,a2,a3,a4,a5,a6);
  I.i4 = gsub(gsqr(I.j2), gmulsg(24,I.j4));
  I.j6 = igusaj6(a0,a1,a2,a3,a4,a5,a6);
  j42 = gsqr(I.j4);
  j22 = gsqr(I.j2);
  j2j6 = gmul(I.j2,I.j6);
  I.j8 = gmul2n(gsub(j2j6,j42), -2);
  I.i12= gmul2n(gsub(gadd(gmul(j22,j42),gmulsg(36,gmul(j2j6,I.j4))),
                     gadd(gadd(gmulsg(32,gmul(j42,I.j4)),gmul(j2j6,j22)),gmulsg(108,gsqr(I.j6)))),-2);

  for(i = 1; i < l; i++)
    gcoeff(facto,i,2) = stoi(Q_pval(I.j10, gel(factp,i)));
  dd = ZX_pval(polr,gen_2) & (~1); /* = 2 floor(val/2) */
  polr = gmul2n(polr, -dd);

  V = cgetg(l, t_VEC);
  for (i = 1; i < l; i++)
  {
    GEN q = gel(factp,i), red, N = NULL;
    struct igusa_p Ip;
    long f = genus2localred(&I, &Ip, q, gel(vecmini,i));
    gcoeff(facto,i,2) = stoi(f);
    if (Ip.tame) Ip.type = stack_strcat("(tame) ", Ip.type);
    if (f >= 0)
      N = zv_snf(Ip.neron);
    if (DEBUGLEVEL)
    {
      if (!p) err_printf("p = %Ps\n", q);
      err_printf("(potential) stable reduction: %Ps\n", Ip.stable);
      if (f >= 0) {
        err_printf("reduction at p: %s, %Ps", Ip.type, N);
        err_printf(", f = %ld\n", f);
      }
    }
    red = f >= 0? mkvec2(strtoGENstr(Ip.type), N): cgetg(1, t_VEC);
    gel(V, i) = mkvec3(q, Ip.stable, red);
  }
  if (p) V = gel(V,1);
  cond = factorback(facto);
  /* remove denominator 2 coming from f = -1 in genuslocalred(, p = 2) */
  if (typ(cond) != t_INT) cond = gel(cond,1);
  return gerepilecopy(av, mkvec4(cond, facto, polr, V));
}
