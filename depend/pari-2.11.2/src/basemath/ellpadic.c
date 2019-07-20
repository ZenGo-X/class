/* Copyright (C) 2011  The PARI group.

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

static GEN
precp_fix(GEN h, long v)
{ return (precp(h) > v)? cvtop(h,gel(h,2),v): h; }

/* TATE CURVE */

/* a1, b1 are t_PADICs, a1/b1 = 1 (mod p) if p odd, (mod 2^4) otherwise.
 * Let (A_n, B_n) be defined by A_1 = a1/p^v, B_1 = b1/p^v, v=v(a1)=v(a2);
 *   A_{n+1} = (A_n + B_n + 2 B_{n+1}) / 4
 *   B_{n+1} = B_n sqrt(A_n / B_n) = square root of A_n B_n congruent to B_n
 *   R_n = p^v( A_n - B_n ) = r_{n+1}
 * Return [An,Bn,Rn]. N.B. lim An = M2(a1,b1) = M(sqrt(a1),sqrt(b1))^2 */
GEN
Qp_agm2_sequence(GEN a1, GEN b1)
{
  GEN bp, pmod, p = gel(a1,2), q = gel(a1,3), An, Bn, Rn;
  long pp = precp(a1), v = valp(a1), i;
  int pis2 = absequaliu(p,2);
  a1 = gel(a1,4);
  b1 = gel(b1,4);
  if (pis2)
    pmod = utoipos(8);
  else
    pmod = p;
  bp = modii(b1, pmod);
  An = cgetg(pp+1, t_VEC); /* overestimate: rather log_2(pp) */
  Bn = cgetg(pp+1, t_VEC);
  Rn = cgetg(pp+1, t_VEC);
  for(i = 1;; i++)
  {
    GEN a = a1, b = b1, r;
    long vr;
    gel(An, i) = a;
    gel(Bn, i) = b;
    r = subii(a,b);
    if (!signe(r)) break;
    vr = Z_pvalrem(r,p,&r);
    if (vr >= pp) break;
    r = cvtop(r, p, pp - vr); setvalp(r, vr+v);
    gel(Rn, i) = r;

    b1 = Zp_sqrt(Fp_mul(a,b,q), p, pp);
    if (!b1) pari_err_PREC("p-adic AGM");
    if (!equalii(modii(b1,pmod), bp)) b1 = Fp_neg(b1, q);
    /* a1 = (a+b+2sqrt(ab))/4 */
    if (pis2)
    {
      b1 = remi2n(b1, pp-1);
      a1 = shifti(addii(addii(a,b), shifti(b1,1)),-2);
      a1 = remi2n(a1, pp-2);
      pp -= 2;
    }
    else
      a1 = modii(Fp_halve(addii(Fp_halve(addii(a,b),q), b1), q), q);
  }
  setlg(An,i+1);
  setlg(Bn,i+1);
  setlg(Rn,i); return mkvec4(An, Bn, Rn, stoi(v));
}
void
Qp_descending_Landen(GEN AB, GEN *ptx, GEN *pty)
{
  GEN R = gel(AB,3);
  long i, n = lg(R)-1;
  GEN x = *ptx;
  if (isintzero(x))
  {
    i = 2;
    x = gmul2n(gel(R,1),-2);
    if (pty)
    {
      GEN A = gel(AB,1);
      if (n == 1)
        *pty = gmul(x, Qp_sqrt(gadd(x,gel(A,2))));
      else
        *pty = Qp_sqrt(gmul(gmul(x, gadd(x,gel(A,2))), gadd(x,gel(R,2))));
      if (!*pty) pari_err_PREC("Qp_descending_Landen");
    }
  }
  else
    i = 1;
  for (; i <= n; i++)
  {
    GEN r = gel(R,i), t;
    if (gequal0(x)) pari_err_PREC("Qp_descending_Landen");
    t = Qp_sqrt(gaddsg(1, gdiv(r,x))); /* = 1 (mod p) */
    if (!t) pari_err_PREC("Qp_descending_Landen");
    if (i == n)
    {
      GEN p = gel(r,2);
      long v, vx = valp(x), vr = valp(r);
      if (vx >= vr) pari_err_PREC("Qp_descending_Landen");
      /* last loop, take into account loss of accuracy from multiplication
       * by \prod_{j > n} sqrt(1+r_j/x_j); since vx < vr, j = n+1 is enough */
      v = 2*vr - vx;
      /* |r_{n+1}| <= |(r_n)^2 / 8| + 1 bit for sqrt loss */
      if (absequaliu(p,2)) v -= 4;
      /* tail is 1 + O(p^v) */
      if (v < precp(x)) x = cvtop(x,p,v);
    }
    /* x_{n+1} = x_n  ((1 + sqrt(1 + r_n/x_n)) / 2)^2 */
    x = gmul(x, gsqr(gmul2n(gaddsg(1,t),-1)));
    /* y_{n+1} = y_n / (1 - (r_n/4x_{n+1})^2) */
    if (pty) *pty = gdiv(*pty, gsubsg(1, gsqr(gdiv(r,gmul2n(x,2)))));
  }
  *ptx = x;
}
void
Qp_ascending_Landen(GEN AB, GEN *ptx, GEN *pty)
{
  GEN A = gel(AB,1), R = gel(AB,3), x = *ptx, p, r;
  long n = lg(R)-1, va = itos(gel(AB,4)), v, i;

  r = gel(R,n);
  v = 2*valp(r) + va;
  if (typ(x) == t_PADIC)
    v -= 2*valp(x);
  else
    v -= valp(gnorm(x)); /* v(x) = v(Nx) / (e*f), here ef = 2 */
  p = gel(r,2);
  if (absequaliu(p,2)) v -= 3; /* |r_{n+1}| <= |(r_n)^2 / 8| */
  /* v = v(A[n+1] R[n+1] / x_{n+1}^2) */
  if (v <= 0) pari_err_PREC("Qp_ascending_Landen");
  /* v > 0 => v = v(x_oo) = ... = v(x_{n+1}) */
  x = gsub(x, gmul2n(r,-1));
  if (padicprec_relative(x) > v) x = gcvtop(x, p, v);
  /* x = x_n */
  for (i = n; i > 1; i--)
  {
    GEN ar = gmul(gel(A,i),gel(R,i)), xp;
    setvalp(ar, valp(ar)+va); /* A_i = A[i] * p^va */
    /* x_{i-1} = x_i + a_i r_i / x_i - r_{i-1}/2 */
    xp = gsub(gadd(x, gdiv(ar, x)), gmul2n(gel(R,i-1),-1));
    /* y_{i-1} = y_i (1 - a_i r_i / x^2) */
    if (pty) *pty = gmul(*pty, gsubsg(1, gdiv(ar,gsqr(x))));
    x = xp;
  }
  *ptx = x;
}

/* Let T = 4x^3 + b2 x^2 + 2b4 x + b6, where T has a unique p-adic root 'a'.
 * Return a lift of a to padic accuracy prec. We have
 * 216 T = 864 X^3 - 18 c4X - c6, where X = x + b2/12 */
static GEN
doellQp_root(GEN E, long prec)
{
  GEN c4=ell_get_c4(E), c6=ell_get_c6(E), j=ell_get_j(E), p=ellQp_get_p(E);
  GEN c6p, T, a;
  long alpha;
  int pis2 = absequaliu(p, 2);
  if (Q_pval(j, p) >= 0) pari_err_DOMAIN(".root", "v_p(j)", ">=", gen_0, j);
  /* v(j) < 0 => v(c4^3) = v(c6^2) = 2 alpha */
  alpha = Q_pvalrem(ell_get_c4(E), p, &c4) >> 1;
  if (alpha) (void)Q_pvalrem(ell_get_c6(E), p, &c6);
  /* Renormalized so that v(c4) = v(c6) = 0; multiply by p^alpha at the end */
  if (prec < 4 && pis2) prec = 4;
  c6p = modii(c6,p);
  if (pis2)
  { /* Use 432T(X/4) = 27X^3 - 9c4 X - 2c6 to have integral root; a=0 mod 2 */
    T = mkpoln(4, utoipos(27), gen_0, mulis(c4,-9), mulis(c6, -2));
    /* v_2(root a) = 1, i.e. will lose one bit of accuracy: prec+1 */
    a = ZpX_liftroot(T, gen_0, p, prec+1);
    alpha -= 2;
  }
  else if (absequaliu(p, 3))
  { /* Use 216T(X/3) = 32X^3 - 6c4 X - c6 to have integral root; a=-c6 mod 3 */
    a = Fp_neg(c6p, p);
    T = mkpoln(4, utoipos(32), gen_0, mulis(c4, -6), negi(c6));
    a = ZX_Zp_root(T, a, p, prec);
    switch(lg(a)-1)
    {
      case 1: /* single root */
        a = gel(a,1); break;
      case 3: /* three roots, e.g. "15a1", choose the right one */
      {
        GEN a1 = gel(a,1), a2 = gel(a,2), a3 = gel(a,3);
        long v1 = Z_lval(subii(a2, a3), 3);
        long v2 = Z_lval(subii(a1, a3), 3);
        long v3 = Z_lval(subii(a1, a2), 3);
        if      (v1 == v2) a = a3;
        else if (v1 == v3) a = a2;
        else a = a1;
      }
      break;
    }
    alpha--;
  }
  else
  { /* p != 2,3: T = 4(x-a)(x-b)^2 = 4x^3 - 3a^2 x - a^3 when b = -a/2
     * (so that the trace coefficient vanishes) => a = c6/6c4 (mod p)*/
    GEN c4p = modii(c4,p);
    a = Fp_div(c6p, Fp_mulu(c4p, 6, p), p);
    T = mkpoln(4, utoipos(864), gen_0, mulis(c4, -18), negi(c6));
    a = ZpX_liftroot(T, a, p, prec);
  }
  a = cvtop(a, p, prec);
  if (alpha) setvalp(a, valp(a)+alpha);
  return gsub(a, gdivgs(ell_get_b2(E), 12));
}
GEN
ellQp_root(GEN E, long prec)
{ return obj_checkbuild_padicprec(E, Qp_ROOT, &doellQp_root, prec); }

/* compute a,b such that E1: y^2 = x(x-a)(x+a-b) ~ E */
static void
doellQp_ab(GEN E, GEN *pta, GEN *ptb, long prec)
{
  GEN b2 = ell_get_b2(E), b4 = ell_get_b4(E), e1 = ellQp_root(E, prec);
  GEN w, u, t = gadd(gdivgs(b2,4), gmulsg(3,e1)), p = ellQp_get_p(E);
  w = Qp_sqrt(gmul2n(gadd(b4,gmul(e1,gadd(b2,gmulsg(6,e1)))),1));
  u = gadd(t,w);
  /* Decide between w and -w: we want v(a-b) > v(b) */
  if (absequaliu(p,2))
  { if (valp(u)-1 <= valp(w)) w = gneg_i(w); }
  else
  { if (valp(u) <= valp(w)) w = gneg_i(w); }

  /* w^2 = 2b4 + 2b2 e1 + 12 e1^2 = 4(e1-e2)(e1-e3) */
  *pta = gmul2n(gsub(w,t),-2);
  *ptb = gmul2n(w,-1);
}

static GEN
doellQp_Tate(GEN E, long prec0)
{
  GEN p = ellQp_get_p(E), j = ell_get_j(E);
  GEN L, u, u2, q, x1, a, b, d, s, t, AB, A, M2;
  long v, n, pp, prec = prec0+3;
  int split = -1; /* unknown */
  int pis2 = equaliu(p,2);

  if (Q_pval(j, p) >= 0) pari_err_DOMAIN(".tate", "v_p(j)", ">=", gen_0, j);
START:
  doellQp_ab(E, &a, &b, prec);
  d = gsub(a,b);
  v = prec0 - precp(d);
  if (v > 0) { prec += v; goto START; }
  AB = Qp_agm2_sequence(a,b);
  A = gel(AB,1);
  n = lg(A)-1; /* AGM iterations */
  pp = minss(precp(a),precp(b));
  M2 = cvtop(gel(A,n), p, pis2? pp-2*n: pp);
  setvalp(M2, valp(a));
  u2 = ginv(gmul2n(M2, 2));
  if (split < 0) split = issquare(u2);
  x1 = gen_0;
  Qp_descending_Landen(AB,&x1,NULL);

  t = gaddsg(1, ginv(gmul2n(gmul(u2,x1),1)));
  s = Qp_sqrt(gsubgs(gsqr(t), 1));
  q = gadd(t,s);
  if (gequal0(q)) q = gsub(t,s);
  v = prec0 - precp(q);
  if (split)
  { /* we want log q at precision prec0 */
    GEN q0 = leafcopy(q); setvalp(q0, 0);
    v +=  valp(gsubgs(q0,1));
  }
  if (v > 0) { prec += v; goto START; }
  if (valp(q) < 0) q = ginv(q);
  if (split)
  {
    u = Qp_sqrt(u2);
    L = gdivgs(Qp_log(q), valp(q));
  }
  else
  {
    GEN T = mkpoln(3, gen_1, gen_0, gneg(u2));
    u = mkpolmod(pol_x(0), T);
    L = gen_1;
  }
  return mkvecn(6, u2, u, q, mkvec2(a, b), L, AB);
}
static long
Tate_prec(GEN T) { return padicprec_relative(gel(T,3)); }
GEN
ellQp_Tate_uniformization(GEN E, long prec)
{ return obj_checkbuild_prec(E,Qp_TATE,&doellQp_Tate, &Tate_prec,prec); }
GEN
ellQp_u(GEN E, long prec)
{ GEN T = ellQp_Tate_uniformization(E, prec); return gel(T,2); }
GEN
ellQp_u2(GEN E, long prec)
{ GEN T = ellQp_Tate_uniformization(E, prec); return gel(T,1); }
GEN
ellQp_q(GEN E, long prec)
{ GEN T = ellQp_Tate_uniformization(E, prec); return gel(T,3); }
GEN
ellQp_ab(GEN E, long prec)
{ GEN T = ellQp_Tate_uniformization(E, prec); return gel(T,4); }
GEN
ellQp_L(GEN E, long prec)
{ GEN T = ellQp_Tate_uniformization(E, prec); return gel(T,5); }
GEN
ellQp_AGM(GEN E, long prec)
{ GEN T = ellQp_Tate_uniformization(E, prec); return gel(T,6); }

/* FORMAL GROUP */

/* t to w := -1/y */
GEN
ellformalw(GEN e, long n, long v)
{
  pari_sp av = avma, av2;
  GEN a1,a2,a3,a4,a6, a63;
  GEN w = cgetg(3, t_SER), t, U, V, W, U2;
  ulong mask, nold = 1;
  if (v < 0) v = 0;
  if (n <= 0) pari_err_DOMAIN("ellformalw","precision","<=",gen_0,stoi(n));
  mask = quadratic_prec_mask(n);
  t = pol_x(v);
  checkell(e);
  a1 = ell_get_a1(e); a2 = ell_get_a2(e); a3 = ell_get_a3(e);
  a4 = ell_get_a4(e); a6 = ell_get_a6(e); a63 = gmulgs(a6,3);
  w[1] = evalsigne(1)|evalvarn(v)|evalvalp(3);
  gel(w,2) = gen_1; /* t^3 + O(t^4) */
  /* use Newton iteration, doubling accuracy at each step
   *
   *            w^3 a6 + w^2(a4 t + a3) + w (a2 t^2 + a1 t - 1) + t^3
   * w  <-  w - -----------------------------------------------------
   *              w^2 (3a6) + w (2a4 t + 2a3) + (a2 t^2 + a1 t - 1)
   *
   *              w^3 a6 + w^2 U + w V + W
   *      =: w -  -----------------------
   *                w^2 (3a6) + 2w U + V
   */
  U = gadd(gmul(a4,t), a3);
  U2 = gmul2n(U,1);
  V = gsubgs(gadd(gmul(a2,gsqr(t)), gmul(a1,t)), 1);
  W = gpowgs(t,3);
  av2 = avma;
  while (mask > 1)
  { /* nold correct terms in w */
    ulong i, nnew = nold << 1;
    GEN num, den, wnew, w2, w3;
    if (mask & 1) nnew--;
    mask >>= 1;
    wnew = cgetg(nnew+2, t_SER);
    wnew[1] = w[1];
    for (i = 2; i < nold+2; i++) gel(wnew,i) = gel(w,i);
    for (     ; i < nnew+2; i++) gel(wnew,i) = gen_0;
    w = wnew;
    w2 = gsqr(w); w3 = gmul(w2,w);
    num = gadd(gmul(a6,w3), gadd(gmul(U,w2), gadd(gmul(V,w), W)));
    den = gadd(gmul(a63,w2), gadd(gmul(w,U2), V));

    w = gerepileupto(av2, gsub(w, gdiv(num, den)));
    nold = nnew;
  }
  return gerepilecopy(av, w);
}

static GEN
ellformalpoint_i(GEN w, GEN wi)
{ return mkvec2(gmul(pol_x(varn(w)),wi), gneg(wi)); }

/* t to [x,y] */
GEN
ellformalpoint(GEN e, long n, long v)
{
  pari_sp av = avma;
  GEN w = ellformalw(e, n, v), wi = ser_inv(w);
  return gerepilecopy(av, ellformalpoint_i(w, wi));
}

static GEN
ellformaldifferential_i(GEN e, GEN w, GEN wi, GEN *px)
{
  GEN x, w1;
  if (gequal0(ell_get_a1(e)) && gequal0(ell_get_a3(e)))
  { /* dx/2y = dx * -w/2, avoid division */
    x = gmul(pol_x(varn(w)), wi);
    w1 = gmul(derivser(x), gneg(gmul2n(w,-1)));
  }
  else
  {
    GEN P = ellformalpoint_i(w, wi);
    x = gel(P,1);
    w1 = gdiv(derivser(x), ec_dmFdy_evalQ(e, P));
  }
  *px = x; return w1;
}
/* t to [ dx / (2y + a1 x + a3), x * ... ]*/
GEN
ellformaldifferential(GEN e, long n, long v)
{
  pari_sp av = avma;
  GEN w = ellformalw(e, n, v), wi = ser_inv(w), x;
  GEN w1 = ellformaldifferential_i(e, w, wi, &x);
  return gerepilecopy(av, mkvec2(w1,gmul(x,w1)));
}

/* t to z, dz = w1 dt */
GEN
ellformallog(GEN e, long n, long v)
{
  pari_sp av = avma;
  GEN w = ellformalw(e, n, v), wi = ser_inv(w), x;
  GEN w1 = ellformaldifferential_i(e, w, wi, &x);
  return gerepileupto(av, integser(w1));
}
/* z to t */
GEN
ellformalexp(GEN e, long n, long v)
{
  pari_sp av = avma;
  return gerepileupto(av, serreverse(ellformallog(e,n,v)));
}
/* [log_p (sigma(t) / t), log_E t], as power series, d (log_E t) := w1 dt;
 * As a fonction of z: odd, = e.b2/12 * z + O(z^3).
 *   sigma(z) = ellsigma(e) exp(e.b2/24*z^2)
 * log_p(sigma(t)/t)=log(subst(sigma(z), x, ellformallog(e))/x) */
static GEN
ellformallogsigma_t(GEN e, long n)
{
  pari_sp av = avma;
  GEN w = ellformalw(e, n, 0), wi = ser_inv(w), t = pol_x(0);
  GEN x, s = ellformaldifferential_i(e, w, wi, &x);
  GEN f = gmul(s, gadd(integser(gmul(x,s)), gmul2n(ell_get_a1(e),-1)));
  return gerepilecopy(av, mkvec2(integser( gsub(ginv(gneg(t)), f) ),
                                 integser(s)));
}

/* P-ADIC HEIGHTS */

/* m >= 0, T = b6^2, g4 = b6^2 - b4 b8, return g_m(xP) mod N, in Mazur-Tate's
 * notation (Duke 1991)*/
static GEN
rellg(hashtable *H, GEN m, GEN T, GEN g4, GEN b8, GEN N)
{
  hashentry *h;
  GEN n, z, np2, np1, nm2, nm1, fp2, fp1, fm2, fm1, f;
  ulong m4;
  if (abscmpiu(m, 4) <= 0) switch(itou(m))
  {
    case 0: return gen_0;
    case 1: return gen_1;
    case 2: return subiu(N,1);
    case 3: return b8;
    case 4: return g4;
  }
  if ((h = hash_search(H, (void*)m))) return (GEN)h->val;
  m4 = mod4(m);
  n = shifti(m, -1); f   = rellg(H,n,T,g4,b8,N);
  np2 = addiu(n, 2); fp2 = rellg(H,np2,T,g4,b8,N);
  np1 = addiu(n, 1); fp1 = rellg(H,np1,T,g4,b8,N);
  nm2 = subiu(n, 2); fm2 = rellg(H,nm2,T,g4,b8,N);
  nm1 = subiu(n, 1); fm1 = rellg(H,nm1,T,g4,b8,N);
  if (odd(m4))
  {
    GEN t1 = Fp_mul(fp2, Fp_powu(f,3,N), N);
    GEN t2 = Fp_mul(fm1, Fp_powu(fp1,3,N), N);
    if (mpodd(n)) t2 = Fp_mul(T,t2,N); else t1 = Fp_mul(T,t1,N);
    z = Fp_sub(t1, t2, N);
  }
  else
  {
    GEN t1 = Fp_mul(fm2, Fp_sqr(fp1,N), N);
    GEN t2 = Fp_mul(fp2, Fp_sqr(fm1,N), N);
    z = Fp_mul(f, Fp_sub(t1, t2, N), N);
  }
  hash_insert(H, (void*)m, (void*)z);
  return z;
}

static GEN
addii3(GEN x, GEN y, GEN z) { return addii(x,addii(y,z)); }
static GEN
addii4(GEN x, GEN y, GEN z, GEN t) { return addii(x,addii3(y,z,t)); }
static GEN
addii5(GEN x, GEN y, GEN z, GEN t, GEN u) { return addii(x,addii4(y,z,t,u)); }

/* xP = [n,d] (corr. to n/d, coprime), such that the reduction of the point
 * P = [xP,yP] is non singular at all places. Return x([m] P) mod N as
 * [num,den] (coprime) */
static GEN
xmP(GEN e, GEN xP, GEN m, GEN N)
{
  pari_sp av = avma;
  ulong k = expi(m);
  hashtable *H = hash_create((5+k)*k, (ulong(*)(void*))&hash_GEN,
                                      (int(*)(void*,void*))&gidentical, 1);
  GEN b2 = ell_get_b2(e), b4 = ell_get_b4(e), n = gel(xP,1), d = gel(xP,2);
  GEN b6 = ell_get_b6(e), b8 = ell_get_b8(e);
  GEN B4, B6, B8, T, g4;
  GEN d2 = Fp_sqr(d,N), d3 = Fp_mul(d2,d,N), d4 = Fp_sqr(d2,N);
  GEN n2 = Fp_sqr(n,N), n3 = Fp_mul(n2,n,N), n4 = Fp_sqr(n2,N);
  GEN nd = Fp_mul(n,d,N), n2d2 = Fp_sqr(nd,N);
  GEN b2nd = Fp_mul(b2,nd, N), b2n2d = Fp_mul(b2nd,n,N);
  GEN b6d3 = Fp_mul(b6,d3,N), g,gp1,gm1, C,D;
  B8 = addii5(muliu(n4,3), mulii(b2n2d,n), mulii(muliu(b4,3), n2d2),
              mulii(muliu(b6d3,3), n), mulii(b8,d4));
  B6 = addii4(muliu(n3,4), mulii(b2nd,n),
              shifti(mulii(b4,Fp_mul(n,d2,N)), 1), b6d3);
  B4 = addii3(muliu(n2,6), b2nd,  mulii(b4,d2));
  B4 = modii(B4,N);
  B6 = modii(B6,N);
  B8 = modii(B8,N);
  g4 = Fp_sub(sqri(B6), mulii(B4,B8), N);
  T = Fp_sqr(B6,N);

  g = rellg(H, m, T,g4,B8, N);
  gp1 = rellg(H, addiu(m,1), T,g4,B8, N);
  gm1 = rellg(H, subiu(m,1), T,g4,B8, N);
  C = Fp_sqr(g, N);
  D = Fp_mul(gp1,gm1, N);
  if (mpodd(m))
  {
    n = Fp_sub(mulii(C,n), mulii(D,B6), N);
    d = Fp_mul(C,d, N);
  }
  else
  {
    n = Fp_sub(Fp_mul(Fp_mul(B6,C,N), n, N), D, N);
    d = Fp_mul(Fp_mul(C,d,N), B6, N);
  }
  return gerepilecopy(av, mkvec2(n,d));
}
/* given [n,d2], x = n/d2 (coprime, d2 = d^2), p | den,
 * return t = -x/y + O(p^v) */
static GEN
tfromx(GEN e, GEN x, GEN p, long v, GEN N, GEN *pd)
{
  GEN n = gel(x,1), d2 = gel(x,2), d;
  GEN a1, a3, b2, b4, b6, B, C, d4, d6, Y;
  if (!signe(n)) { *pd = gen_1; return zeropadic(p, v); }
  a1 = ell_get_a1(e);
  b2 = ell_get_b2(e);
  a3 = ell_get_a3(e);
  b4 = ell_get_b4(e);
  b6 = ell_get_b6(e);
  d = Qp_sqrt(cvtop(d2, p, v - Z_pval(d2,p)));
  if (!d) pari_err_BUG("ellpadicheight");
  /* Solve Y^2 = 4n^3 + b2 n^2 d2+ 2b4 n d2^2 + b6 d2^3,
   * Y = 2y + a1 n d + a3 d^3 */
  d4 = Fp_sqr(d2, N);
  d6 = Fp_mul(d4, d2, N);
  B = gmul(d, Fp_add(mulii(a1,n), mulii(a3,d2), N));
  C = mkpoln(4, utoipos(4), Fp_mul(b2, d2, N),
                Fp_mul(shifti(b4,1), d4, N),
                Fp_mul(b6,d6,N));
  C = FpX_eval(C, n, N);
  if (!signe(C))
    Y = zeropadic(p, v >> 1);
  else
    Y = Qp_sqrt(cvtop(C, p, v - Z_pval(C,p)));
  if (!Y) pari_err_BUG("ellpadicheight");
  *pd = d;
  return gdiv(gmulgs(gmul(n,d), -2), gsub(Y,B));
}

/* return minimal i s.t. -v_p(j+1) - log_p(j-1) + (j+1)*t >= v for all j>=i */
static long
logsigma_prec(GEN p, long v, long t)
{
  double log2p = dbllog2(p);
  long j, i = ceil((v - t) / (t - 2*M_LN2/(3*log2p)) + 0.01);
  if (absequaliu(p,2) && i < 5) i = 5;
  /* guaranteed to work, now optimize */
  for (j = i-1; j >= 2; j--)
  {
    if (- u_pval(j+1,p) - log2(j-1)/log2p + (j+1)*t + 0.01 < v) break;
    i = j;
  }
  if (j == 1)
  {
    if (- absequaliu(p,2) + 2*t + 0.01 >= v) i = 1;
  }
  return i;
}
/* return minimal i s.t. -v_p(j+1) + (j+1)*t >= v for all j>=i */
static long
log_prec(GEN p, long v, long t)
{
  double log2p = dbllog2(p);
  long j, i = ceil(v / (t - M_LN2/(2*log2p)) + 0.01);
  /* guaranteed to work, now optimize */
  for (j = i-1; j >= 1; j--)
  {
    if (- u_pval(j+1,p) + (j+1)*t + 0.01 < v) break;
    i = j;
  }
  return i;
}

/* P = rational point of exact denominator d. Is Q singular on E(Fp) ? */
static int
FpE_issingular(GEN E, GEN P, GEN d, GEN p)
{
  pari_sp av = avma;
  GEN t, x, y, a1, a2, a3, a4;
  if (ell_is_inf(E) || dvdii(d,p)) return 0; /* 0_E is smooth */
  P = Q_muli_to_int(P,d);
  x = gel(P,1);
  y = gel(P,2);
  a1 = ell_get_a1(E);
  a3 = ell_get_a3(E);
  t = addii(shifti(y,1), addii(mulii(a1,x), mulii(a3,d)));
  if (!dvdii(t,p)) { avma = av; return 0; }
  a2 = ell_get_a2(E);
  a4 = ell_get_a4(E);
  d = Fp_inv(d, p);
  x = Fp_mul(x,d,p);
  y = Fp_mul(y,d,p);
  t = subii(mulii(a1,y), addii(a4, mulii(x, addii(gmul2n(a2,1), muliu(x,3)))));
  avma = av; return dvdii(t,p);
}
/* E/Q, P on E(Q). Let g > 0 minimal such that the image of R = [g]P in a
 * minimal model is everywhere non-singular; return [R,g] */
GEN
ellnonsingularmultiple(GEN e, GEN P)
{
  pari_sp av = avma;
  GEN ch, E = ellanal_globalred(e, &ch), NP, L, S, d, g = gen_1;
  long i, l;
  checkellpt(P);
  if (ell_is_inf(P)) retmkvec2(gcopy(P), gen_1);
  if (E != e) P = ellchangepoint(P, ch);
  S = obj_check(E, Q_GLOBALRED);
  NP = gmael(S,3,1);
  L = gel(S,4);
  l = lg(NP);
  d = Q_denom(P);
  for (i = 1; i < l; i++)
  {
    GEN G = gel(L,i), p = gel(NP,i);/* prime of bad reduction */
    long kod;
    if (!FpE_issingular(E, P, d, p)) continue;
    kod = itos(gel(G,2)); /* Kodaira type */
    if (kod >= 5) /* I_nu */
    {
      long nu = kod - 4;
      long n = minss(Q_pval(ec_dmFdy_evalQ(E,P), p), nu/2);
      nu /= ugcd(nu, n);
      g = muliu(g, nu);
      P = ellmul(E, P, utoipos(nu)); d = Q_denom(P);
    } else if (kod <= -5) /* I^*_nu */
    { /* either 2 or 4 */
      long nu = - kod - 4;
      P = elladd(E, P,P); d = Q_denom(P);
      g = shifti(g,1);
      if (odd(nu) && FpE_issingular(E, P, d, p))
      { /* it's 4 */
        P = elladd(E, P,P); d = Q_denom(P);
        g = shifti(g,1);
      }
    } else {
      GEN c = gel(G, 4); /* Tamagawa number at p */
      if (absequaliu(c, 4)) c = gen_2;
      P = ellmul(E, P, c); d = Q_denom(P);
      g = mulii(g, c);
    }
  }
  if (E != e) P = ellchangepointinv(P, ch);
  return gerepilecopy(av, mkvec2(P,g));
}

GEN
ellpadicheight(GEN e, GEN p, long v0, GEN P)
{
  pari_sp av = avma;
  GEN N, H, h, t, ch, g, E, x, D, ls, lt, S, a,b;
  long v, vd;
  int is2;
  checkellpt(P);
  if (v0<=0) pari_err_DOMAIN("ellpadicheight","precision","<=",gen_0,stoi(v0));
  checkell_Q(e);
  if (typ(p) != t_INT) pari_err_TYPE("ellpadicheight",p);
  if (cmpiu(p,2) < 0) pari_err_PRIME("ellpadicheight",p);
  if (ellorder_Q(e,P)) return mkvec2(gen_0,gen_0);
  E = ellanal_globalred(e, &ch);
  if (E != e) P = ellchangepoint(P, ch);
  S = ellnonsingularmultiple(E, P);
  P = gel(S,1);
  g = gel(S,2);
  v = v0 + 2*Z_pval(g, p);
  is2 = absequaliu(p,2); if (is2) v += 2;
  x = Q_remove_denom(gel(P,1), &b);
  x = mkvec2(x, b? b: gen_1);
  vd = Z_pval(gel(x,2), p);
  if (!vd)
  { /* P not in kernel of reduction mod p */
    GEN d, m, X, Pp, Ep = ellinit(E, mkintmod(gen_0,p), 0);
    long w = v+2;
    Pp = RgV_to_FpV(P, p);
    if (lg(Ep) != 1)
      m = ellorder(Ep, Pp, NULL);
    else
    { /* E has bad reduction at p */
      m = ellcard(E, p);
      if (equalii(m, p)) pari_err_TYPE("ellpadicheight: additive reduction", E);
    }
    g = mulii(g,m);
    for(;;)
    {
      N = powiu(p, w);
      X = xmP(E, x, m, N);
      d = gel(X,2);
      if (!signe(d)) w <<= 1;
      else
      {
        vd = Z_pval(d, p);
        if (w >= v+2*vd + is2) break;
        w = v+2*vd + is2;
      }
    }
    x = X;
  }
  /* we will want t mod p^(v+vd) because of t/D in H later, and
   * we lose p^vd in tfromx because of sqrt(d) (p^(vd+1) if p=2)*/
  v += 2*vd + is2;
  N = powiu(p,v);
  t = tfromx(E, x, p, v, N, &D); /* D^2=denom(x)=x[2] */
  S = ellformallogsigma_t(E, logsigma_prec(p, v-vd, valp(t)) + 1);
  ls = ser2rfrac_i(gel(S,1)); /* log_p (sigma(T)/T) */
  lt = ser2rfrac_i(gel(S,2)); /* log_E (T) */
  /* evaluate our formal power series at t */
  H = gadd(poleval(ls, t), glog(gdiv(t, D), 0));
  h = gsqr(poleval(lt, t));
  g = sqri(g);
  a = gdiv(gmulgs(H,-2), g);
  b = gdiv(gneg(h), g);
  if (E != e)
  {
    GEN u = gel(ch,1), r = gel(ch,2);
    a = gdiv(gadd(a, gmul(r,b)), u);
    b = gmul(u,b);
  }
  H = mkvec2(a,b);
  gel(H,1) = precp_fix(gel(H,1),v0);
  gel(H,2) = precp_fix(gel(H,2),v0);
  return gerepilecopy(av, H);
}

GEN
ellpadiclog(GEN E, GEN p, long n, GEN P)
{
  pari_sp av = avma;
  long vt;
  GEN t, x, y, L;
  checkellpt(P);
  if (ell_is_inf(P)) return gen_0;
  x = gel(P,1);
  y = gel(P,2); t = gneg(gdiv(x,y));
  vt = gvaluation(t, p); /* can be a t_INT, t_FRAC or t_PADIC */
  if (vt <= 0)
    pari_err_DOMAIN("ellpadiclog","P","not in the kernel of reduction at",p,P);
  L = ser2rfrac_i(ellformallog(E, log_prec(p, n, vt) + 1, 0));
  return gerepileupto(av, poleval(L, cvtop(t, p, n)));
}

/* E/Qp has multiplicative reduction, Tate curve */
static GEN
ellpadics2_tate(GEN Ep, long n)
{
  pari_sp av;
  GEN u2 = ellQp_u2(Ep, n), q = ellQp_q(Ep, n), pn = gel(q,3);
  GEN qm, s, b2 = ell_get_b2(Ep), v = vecfactoru_i(1, n);
  long m;
  qm = Fp_powers(padic_to_Fp(q, pn), n, pn);
  s = gel(qm, 2); av = avma;
  for (m = 2; m <= n; m++) /* sum sigma(m) q^m */
  {
    s = addii(s, mulii(gel(qm,m+1), usumdiv_fact(gel(v,m))));
    if ((m & 31) == 0) s = gerepileuptoint(av, s);
  }
  s = subui(1, muliu(s,24));
  s = gdivgs(gsub(b2, gdiv(s,u2)), 12);
  return precp_fix(s,n);
}

GEN
ellpadicfrobenius(GEN E, ulong p, long n)
{
  checkell(E);
  if (p < 2) pari_err_DOMAIN("ellpadicfrobenius","p", "<", gen_2, utoi(p));
  switch(ell_get_type(E))
  {
    case t_ELL_Q: break;
    case t_ELL_Qp: if (equaliu(ellQp_get_p(E), p)) break;
    default: pari_err_TYPE("ellpadicfrobenius",utoi(p));
  }
  return hyperellpadicfrobenius(ec_bmodel(E), p, n);
}

/* s2 = (b_2-E_2)/12 */
GEN
ellpadics2(GEN E, GEN p, long n)
{
  pari_sp av = avma;
  GEN l, F, a,b,d, ap;
  ulong pp;
  if (typ(p) != t_INT) pari_err_TYPE("ellpadics2",p);
  if (cmpis(p,2) < 0) pari_err_PRIME("ellpadics2",p);
  checkell(E);
  if (Q_pval(ell_get_j(E), p) < 0)
  {
    GEN Ep;
    if (ell_get_type(E) == t_ELL_Qp) Ep = E;
    else Ep = ellinit(E, zeropadic(p,n), 0);
    l = ellpadics2_tate(Ep, n);
    if (Ep != E) obj_free(Ep);
    return gerepilecopy(av, l);
  }
  pp = itou(p);
  F = ellpadicfrobenius(E, pp, n);
  a = gcoeff(F,1,1);
  b = gcoeff(F,1,2);
  d = gcoeff(F,2,2); ap = gadd(a,d);
  if (valp(ap) > 0) pari_err_DOMAIN("ellpadics2","E","is supersingular at",p,E);
  if (pp == 2 || (pp <= 13 && n == 1)) /* 2sqrt(p) > p/2: ambiguity */
    ap = ellap(E,p);
  else
  { /* either 2sqrt(p) < p/2 or n > 1 and 2sqrt(p) < p^2/2 (since p!=2) */
    GEN q = pp <= 13? utoipos(pp * pp): p;
    ap = padic_to_Fp(ap, q);
    ap = Fp_center_i(ap, q, shifti(q,-1));
  }
  l = mspadic_unit_eigenvalue(ap, 2, p, n);
  return gerepileupto(av, gdiv(b, gsub(l, a))); /* slope of eigenvector */
}

/* symbol and modular symbol space attached to E to later compute
 * ellpadicL(E,p,, s,,D) */
static GEN
ellpadicL_symbol(GEN E, GEN p, GEN s, GEN D)
{
  GEN s1, s2, ap;
  long sign;
  checkell(E);
  if (ell_get_type(E) != t_ELL_Q) pari_err_TYPE("ellpadicL",E);
  ap = ellap(E,p);
  if (D && typ(D) != t_INT) pari_err_TYPE("ellpadicL",D);
  if (D && !Z_isfundamental(D))
    pari_err_DOMAIN("ellpadicL", "isfundamental(D)", "=", gen_0, D);
  if (!D) D = gen_1;
  if (Z_pval(ellQ_get_N(E), p) >= 2)
    pari_err_IMPL("additive reduction in ellpadicL");
  mspadic_parse_chi(s, &s1,&s2);
  sign = signe(D); if (mpodd(s2)) sign = -sign;
  return shallowconcat(msfromell(E, sign), mkvec4(ap, p, s, D));
}
/* W an ellpadicL_symbol, initialize for ellpadicL(E,p,n,s,,D) */
static GEN
ellpadicL_init(GEN W, long n)
{
  GEN Wp, den, M = gel(W,1), xpm = gel(W,2), ap = gel(W,3), s = gel(W,5);
  long p = itos(gel(W,4)), D = itos(gel(W,6));

  xpm = Q_remove_denom(xpm,&den); if (!den) den = gen_1;
  n += Z_lval(den,p);
  Wp = mspadicinit(M, p, n, Z_lval(ap,p));
  return mkvec3(mspadicmoments(Wp,xpm,D), den, s);
}
/* v from ellpadicL_init, compute ellpadicL(E,p,n,s,r,D) */
static GEN
ellpadic_i(GEN v, long r)
{
  GEN oms = gel(v,1), den = gel(v,2), s = gel(v,3);
  return gdiv(mspadicL(oms,s,r), den);
}
GEN
ellpadicL(GEN E, GEN p, long n, GEN s, long r, GEN D)
{
  pari_sp av = avma;
  GEN W, v;
  if (r < 0) pari_err_DOMAIN("ellpadicL","r","<",gen_0,stoi(r));
  if (n <= 0) pari_err_DOMAIN("ellpadicL","precision","<=",gen_0,stoi(n));
  W = ellpadicL_symbol(E, p, s, D);
  v = ellpadicL_init(W, n);
  return gerepileupto(av, ellpadic_i(v, r));
}

static long
torsion_order(GEN E) { GEN T = elltors(E); return itos(gel(T,1)); }

/* E given by a minimal model; D != 0. Compare Euler factor of L(E,(D/.),1)
 * with L(E^D,1). Return
 *   \prod_{p|D} (p-a_p(E)+eps_{E}(p)) / p,
 * where eps(p) = 0 if p | N_E and 1 otherwise */
static GEN
get_Euler(GEN E, GEN D)
{
  GEN a = gen_1, b = gen_1, P = gel(absZ_factor(D), 1);
  long i, l = lg(P);
  for (i = 1; i < l; i++)
  {
    GEN p = gel(P,i);
    a = mulii(a, ellcard(E, p));
    b = mulii(b, p);
  }
  return Qdivii(a, b);
}
GEN
ellpadicbsd(GEN E, GEN p, long n, GEN D)
{
  const long MAXR = 30;
  pari_sp av = avma;
  GEN W, ED, tam, ND, C, apD, U = NULL;/*-Wall*/
  long r, vN;
  checkell(E);
  if (D && isint1(D)) D = NULL;
  W = ellpadicL_symbol(E, p, gen_0, D);
  ED = D? ellinit(elltwist(E,D), gen_1, 0): E;
  ED = ellanal_globalred_all(ED, NULL, &ND, &tam);
  vN = Z_pval(ND, p); /* additive reduction ? */
  if (vN >= 2) pari_err_DOMAIN("ellpadicbsd","v_p(N(E_D))",">",gen_1,stoi(vN));
  if (n < 5) n = 5;
  for(;; n <<= 1)
  {
    GEN v = ellpadicL_init(W, n);
    for (r = 0; r < MAXR; r++)
    {
      U = ellpadic_i(v, r);
      if (!gequal0(U)) break;
    }
    if (r < MAXR) break;
  }
  apD = ellap(ED, p);
  if (typ(U) == t_COL)
  { /* p | a_p(E_D), frobenius on E_D */
    GEN F = mkmat22(gen_0, negi(p), gen_1, apD);
    U = RgM_RgC_mul(gpowgs(gsubsg(1, gdiv(F,p)), -2), U);
    settyp(U, t_VEC);
  }
  else if (dvdii(ND,p))
  {
    if (equalim1(apD)) /* divide by 1-1/a_p */
      U = gdivgs(U, 2);
    else
    { /* ap = 1 */
      GEN EDp = ellinit(ED, zeropadic(p,n), 0);
      U = gdiv(U, ellQp_L(EDp,n));
      obj_free(EDp);
    }
  }
  else
  {
    GEN a = mspadic_unit_eigenvalue(apD, 2, p, n);
    U = gmul(U, gpowgs(gsubsg(1, ginv(a)), -2));
  }
  C = mulii(tam, mpfact(r));
  if (D) C = gmul(C, get_Euler(ED, D));
  C = gdiv(sqru(torsion_order(ED)), C);
  if (D) obj_free(ED);
  return gerepilecopy(av, mkvec2(utoi(r), gmul(U, C)));
}

GEN
ellpadicregulator(GEN E, GEN p, long n, GEN S)
{
  pari_sp av = avma;
  GEN FG = ellpadicheightmatrix(E,p,n,S); /* forbids additive reduction */
  /* [F,G]: height in basis [omega, eta] */
  GEN R, F = gel(FG,1), G = gel(FG,2), ap = ellap(E,p);
  if (dvdii(ap, p))
  { /* supersingular */
    GEN f = ellpadicfrobenius(E, itou(p), n);
    GEN x = gcoeff(f,1,1), y = gcoeff(f,2,1);
    /* [A,B]: regulator height in basis [omega, eta] */
    GEN A = det(F), B = det(gadd(F,G)), C;
    C = gdiv(gsub(B,A), y);
    /* R: regulator height in basis [omega, F.omega] */
    R = mkvec2(gsub(A, gmul(x,C)), C);
  }
  else
  {
    GEN s2;
    if (equali1(ap) && dvdii(ell_get_disc(E),p))
    { /* split multiplicative reduction */
      GEN Ep = ellinit(E, zeropadic(p,n), 0);
      GEN q = ellQp_q(Ep,n), u2 = ellQp_u2(Ep,n);
      s2 = ellpadics2_tate(Ep, n);
      s2 = gsub(s2, ginv(gmul(Qp_log(q), u2))); /*extended MW group contrib*/
      obj_free(Ep);
    }
    else
      s2 = ellpadics2(E,p,n);
    R = det( RgM_sub(F, RgM_Rg_mul(G,s2)) );
  }
  return gerepilecopy(av, R);
}
