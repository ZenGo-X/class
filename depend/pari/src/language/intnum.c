/* Copyright (C) 2000  The PARI group.

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

static const long EXTRAPREC =
#ifdef LONG_IS_64BIT
  1;
#else
  2;
#endif

static GEN
intlin(void *E, GEN (*eval)(void*, GEN), GEN a, GEN b, GEN tab, long prec);

/********************************************************************/
/**                NUMERICAL INTEGRATION (Romberg)                 **/
/********************************************************************/
typedef struct {
  void *E;
  GEN (*f)(void *E, GEN);
} invfun;

/* 1/x^2 f(1/x) */
static GEN
_invf(void *E, GEN x)
{
  invfun *S = (invfun*)E;
  GEN y = ginv(x);
  return gmul(S->f(S->E, y), gsqr(y));
}

/* h and s are arrays of the same length L > D. The h[i] are (decreasing)
 * step sizes, s[i] is the computed Riemann sum for step size h[i].
 * Interpolate the last D+1 values so that s ~ polynomial in h of degree D.
 * Guess that limit_{h->0} = s(0) */
static GEN
interp(GEN h, GEN s, long L, long bit, long D)
{
  pari_sp av = avma;
  long e1,e2;
  GEN dss, ss = polint_i(h + L-D,s + L-D, gen_0, D+1, &dss);

  e1 = gexpo(ss);
  e2 = gexpo(dss);
  if (DEBUGLEVEL>2)
  {
    err_printf("romb: iteration %ld, guess: %Ps\n", L,ss);
    err_printf("romb: relative error < 2^-%ld [target %ld bits]\n",e1-e2,bit);
  }
  if (e1-e2 <= bit && (L <= 10 || e1 >= -bit)) { avma = av; return NULL; }
  return cxtoreal(ss);
}

static GEN
qrom3(void *E, GEN (*eval)(void *, GEN), GEN a, GEN b, long bit)
{
  const long JMAX = 25, KLOC = 4;
  GEN ss,s,h,p1,p2,qlint,del,x,sum;
  long j, j1, it, sig, prec = nbits2prec(bit);

  a = gtofp(a,prec);
  b = gtofp(b,prec);
  qlint = subrr(b,a); sig = signe(qlint);
  if (!sig) return gen_0;
  if (sig < 0) { setabssign(qlint); swap(a,b); }

  s = new_chunk(JMAX+KLOC-1);
  h = new_chunk(JMAX+KLOC-1);
  gel(h,0) = real_1(prec);

  p1 = eval(E, a); if (p1 == a) p1 = rcopy(p1);
  p2 = eval(E, b);
  gel(s,0) = gmul2n(gmul(qlint,gadd(p1,p2)),-1);
  for (it=1,j=1; j<JMAX; j++, it<<=1) /* it = 2^(j-1) */
  {
    pari_sp av, av2;
    gel(h,j) = real2n(-2*j, prec); /* 2^(-2j) */
    av = avma; del = divru(qlint,it);
    x = addrr(a, shiftr(del,-1));
    av2 = avma;
    for (sum = gen_0, j1 = 1; j1 <= it; j1++, x = addrr(x,del))
    {
      sum = gadd(sum, eval(E, x));
      if ((j1 & 0x1ff) == 0) gerepileall(av2, 2, &sum,&x);
    }
    sum = gmul(sum,del);
    gel(s,j) = gerepileupto(av, gmul2n(gadd(gel(s,j-1), sum), -1));
    if (j >= KLOC && (ss = interp(h, s, j, bit-j-6, KLOC)))
      return gmulsg(sig,ss);
  }
  pari_err_IMPL("intnumromb recovery [too many iterations]");
  return NULL; /* LCOV_EXCL_LINE */
}

static GEN
qrom2(void *E, GEN (*eval)(void *, GEN), GEN a, GEN b, long bit)
{
  const long JMAX = 16, KLOC = 4;
  GEN ss,s,h,p1,qlint,del,ddel,x,sum;
  long j, j1, it, sig, prec = nbits2prec(bit);

  a = gtofp(a, prec);
  b = gtofp(b, prec);
  qlint = subrr(b,a); sig = signe(qlint);
  if (!sig)  return gen_0;
  if (sig < 0) { setabssign(qlint); swap(a,b); }

  s = new_chunk(JMAX+KLOC-1);
  h = new_chunk(JMAX+KLOC-1);
  gel(h,0) = real_1(prec);

  p1 = shiftr(addrr(a,b),-1);
  gel(s,0) = gmul(qlint, eval(E, p1));
  for (it=1, j=1; j<JMAX; j++, it*=3) /* it = 3^(j-1) */
  {
    pari_sp av, av2;
    gel(h,j) = divru(gel(h,j-1), 9); /* 3^(-2j) */
    av = avma; del = divru(qlint,3*it); ddel = shiftr(del,1);
    x = addrr(a, shiftr(del,-1));
    av2 = avma;
    for (sum = gen_0, j1 = 1; j1 <= it; j1++)
    {
      sum = gadd(sum, eval(E, x)); x = addrr(x,ddel);
      sum = gadd(sum, eval(E, x)); x = addrr(x,del);
      if ((j1 & 0x1ff) == 0) gerepileall(av2, 2, &sum,&x);
    }
    sum = gmul(sum,del); p1 = gdivgs(gel(s,j-1),3);
    gel(s,j) = gerepileupto(av, gadd(p1,sum));
    if (j >= KLOC && (ss = interp(h, s, j, bit-(3*j/2)+3, KLOC)))
      return gmulsg(sig, ss);
  }
  pari_err_IMPL("intnumromb recovery [too many iterations]");
  return NULL; /* LCOV_EXCL_LINE */
}

/* integrate after change of variables x --> 1/x */
static GEN
qromi(void *E, GEN (*eval)(void*, GEN), GEN a, GEN b, long bit)
{
  GEN A = ginv(b), B = ginv(a);
  invfun S;
  S.f = eval;
  S.E = E; return qrom2(&S, &_invf, A, B, bit);
}

/* a < b, assume b "small" (< 100 say) */
static GEN
rom_bsmall(void *E, GEN (*eval)(void*, GEN), GEN a, GEN b, long bit)
{
  if (gcmpgs(a,-100) >= 0) return qrom2(E,eval,a,b,bit);
  if (gcmpgs(b, -1) < 0)   return qromi(E,eval,a,b,bit); /* a<-100, b<-1 */
  /* a<-100, b>=-1, split at -1 */
  return gadd(qromi(E,eval,a,gen_m1,bit),
              qrom2(E,eval,gen_m1,b,bit));
}

static GEN
rombint(void *E, GEN (*eval)(void*, GEN), GEN a, GEN b, long bit)
{
  long l = gcmp(b,a);
  GEN z;

  if (!l) return gen_0;
  if (l < 0) swap(a,b);
  if (gcmpgs(b,100) >= 0)
  {
    if (gcmpgs(a,1) >= 0)
      z = qromi(E,eval,a,b,bit);
    else /* split at 1 */
      z = gadd(rom_bsmall(E,eval,a,gen_1,bit), qromi(E,eval,gen_1,b,bit));
  }
  else
    z = rom_bsmall(E,eval,a,b,bit);
  if (l < 0) z = gneg(z);
  return z;
}

GEN
intnumromb_bitprec(void *E, GEN (*f)(void *, GEN), GEN a,GEN b, long fl, long B)
{
  pari_sp av = avma;
  GEN z;
  switch(fl)
  {
    case 0: z = qrom3  (E, f, a, b, B); break;
    case 1: z = rombint(E, f, a, b, B); break;
    case 2: z = qromi  (E, f, a, b, B); break;
    case 3: z = qrom2  (E, f, a, b, B); break;
    default: pari_err_FLAG("intnumromb"); return NULL; /* LCOV_EXCL_LINE */
  }
  return gerepileupto(av, z);
}
GEN
intnumromb(void *E, GEN (*f)(void *, GEN), GEN a, GEN b, long flag, long prec)
{ return intnumromb_bitprec(E,f,a,b,flag,prec2nbits(prec));}
GEN
intnumromb0_bitprec(GEN a, GEN b, GEN code, long flag, long bit)
{ EXPR_WRAP(code, intnumromb_bitprec(EXPR_ARG, a, b, flag, bit)); }

/********************************************************************/
/**             NUMERICAL INTEGRATION (Gauss-Legendre)             **/
/********************************************************************/
GEN
intnumgaussinit(long n, long prec)
{
  pari_sp ltop = avma;
  GEN L, dp1, p1, p2, R, W;
  long prec0 = prec + EXTRAPRECWORD;
  long bitprec = prec2nbits(prec), i, d1;
  if (n <= 0) n = (long)(bitprec*0.2258);
  if (odd(n)) n++;
  if (n == 2) n = 4;
  /* n even >= 4, p1 is even */
  prec = nbits2prec(3*bitprec/2 + 32);
  L = pollegendre(n, 0); /* L_n = p1(x^2) */
  p1 = Q_remove_denom(RgX_deflate(L, 2), &dp1);
  d1 = vali(dp1);
  p2 = ZX_deriv(p1); /* L_n' = 2x p2(x^2) / 2^d1 */
  R = ZX_Uspensky(p1, gen_0, 1, 3*bitprec/2 + 32); /* positive roots of p1 */
  n >>= 1;
  W = cgetg(n+1, t_VEC);
  for (i = 1; i <= n; ++i)
  {
    GEN t, r2 = gel(R,i);
    if (typ(r2) != t_REAL) r2 = gtofp(r2, prec);
    gel(R,i) = sqrtr_abs(r2); /* positive root of L_n */
    /* 2 / (L'(r)^2(1-r^2)) =  2^(2d1 - 1) / (1-r2)r2 (p2(r2))^2 */
    t = mulrr(subrr(r2, sqrr(r2)), sqrr(poleval(p2, r2)));
    shiftr_inplace(t,1-2*d1);
    gel(W,i) = invr(t);
  }
  R = gprec_wtrunc(R,prec0);
  W = gprec_wtrunc(W,prec0);
  return gerepilecopy(ltop, mkvec2(R,W));
}

GEN
intnumgauss(void *E, GEN (*eval)(void*, GEN), GEN a, GEN b, GEN tab, long prec)
{
  pari_sp ltop = avma;
  GEN R, W, bma, bpa, S;
  long n, i, prec2 = prec + EXTRAPREC;
  if (!tab)
    tab = intnumgaussinit(0,prec);
  else if (typ(tab) != t_INT)
  {
    if (typ(tab) != t_VEC || lg(tab) != 3)
      pari_err_TYPE("intnumgauss",tab);
  }
  else
    tab = intnumgaussinit(itos(tab),prec);

  R = gel(tab,1); n = lg(R)-1;
  W = gel(tab,2);
  a = gprec_w(a, prec2);
  b = gprec_w(b, prec2);
  bma = gmul2n(gsub(b,a), -1); /* (b-a)/2 */
  bpa = gadd(bma, a); /* (b+a)/2 */
  S = gen_0;
  for (i = 1; i <= n; ++i)
  {
    GEN r = gel(R,i);
    GEN P = eval(E, gadd(bpa, gmul(bma, r)));
    GEN M = eval(E, gsub(bpa, gmul(bma, r)));
    S = gadd(S, gmul(gel(W,i), gadd(P,M)));
    S = gprec_wensure(S, prec2);
  }
  return gerepilecopy(ltop, gprec_wtrunc(gmul(bma,S), prec));
}

GEN
intnumgauss0(GEN a, GEN b, GEN code, GEN tab, long prec)
{ EXPR_WRAP(code, intnumgauss(EXPR_ARG, a, b, tab, prec)); }

/********************************************************************/
/**                DOUBLE EXPONENTIAL INTEGRATION                  **/
/********************************************************************/

typedef struct _intdata {
  long eps;  /* bit accuracy of current precision */
  long l; /* table lengths */
  GEN tabx0; /* abscissa phi(0) for t = 0 */
  GEN tabw0; /* weight phi'(0) for t = 0 */
  GEN tabxp; /* table of abscissas phi(kh) for k > 0 */
  GEN tabwp; /* table of weights phi'(kh) for k > 0 */
  GEN tabxm; /* table of abscissas phi(kh) for k < 0, possibly empty */
  GEN tabwm; /* table of weights phi'(kh) for k < 0, possibly empty */
  GEN h; /* integration step */
} intdata;

static const long LGTAB = 8;
#define TABh(v) gel(v,1)
#define TABx0(v) gel(v,2)
#define TABw0(v) gel(v,3)
#define TABxp(v) gel(v,4)
#define TABwp(v) gel(v,5)
#define TABxm(v) gel(v,6)
#define TABwm(v) gel(v,7)

static int
isinR(GEN z) { return is_real_t(typ(z)); }
static int
isinC(GEN z)
{ return (typ(z) == t_COMPLEX)? isinR(gel(z,1)) && isinR(gel(z,2)): isinR(z); }

static int
checktabsimp(GEN tab)
{
  long L, LN, LW;
  if (!tab || typ(tab) != t_VEC) return 0;
  if (lg(tab) != LGTAB) return 0;
  if (typ(TABxp(tab)) != t_VEC) return 0;
  if (typ(TABwp(tab)) != t_VEC) return 0;
  if (typ(TABxm(tab)) != t_VEC) return 0;
  if (typ(TABwm(tab)) != t_VEC) return 0;
  L = lg(TABxp(tab)); if (lg(TABwp(tab)) != L) return 0;
  LN = lg(TABxm(tab)); if (LN != 1 && LN != L) return 0;
  LW = lg(TABwm(tab)); if (LW != 1 && LW != L) return 0;
  return 1;
}

static int
checktabdoub(GEN tab)
{
  long L;
  if (typ(tab) != t_VEC) return 0;
  if (lg(tab) != LGTAB) return 0;
  L = lg(TABxp(tab));
  if (lg(TABwp(tab)) != L) return 0;
  if (lg(TABxm(tab)) != L) return 0;
  if (lg(TABwm(tab)) != L) return 0;
  return 1;
}

static int
checktab(GEN tab)
{
  if (typ(tab) != t_VEC) return 0;
  if (lg(tab) != 3) return checktabsimp(tab);
  return checktabsimp(gel(tab,1))
      && checktabsimp(gel(tab,2));
}

/* the TUNE parameter is heuristic */
static void
intinit_start(intdata *D, long m, double TUNE, long prec)
{
  long l, n, bitprec = prec2nbits(prec);
  double d = bitprec*LOG10_2;
  GEN h, nh, pi = mppi(prec);

  n = (long)ceil(d*log(d) / TUNE); /* heuristic */
  /* nh ~ log(2npi/log(n)) */
  nh = logr_abs(divrr(mulur(2*n, pi), logr_abs(utor(n,prec))));
  h = divru(nh, n);
  if (m > 0) { h = gmul2n(h,-m); n <<= m; }
  D->h = h;
  D->eps = bitprec;
  D->l = l = n+1;
  D->tabxp = cgetg(l, t_VEC);
  D->tabwp = cgetg(l, t_VEC);
  D->tabxm = cgetg(l, t_VEC);
  D->tabwm = cgetg(l, t_VEC);
}

static GEN
intinit_end(intdata *D, long pnt, long mnt)
{
  GEN v = cgetg(LGTAB, t_VEC);
  if (pnt < 0) pari_err_DOMAIN("intnuminit","table length","<",gen_0,stoi(pnt));
  TABx0(v) = D->tabx0;
  TABw0(v) = D->tabw0;
  TABh(v) = D->h;
  TABxp(v) = D->tabxp; setlg(D->tabxp, pnt+1);
  TABwp(v) = D->tabwp; setlg(D->tabwp, pnt+1);
  TABxm(v) = D->tabxm; setlg(D->tabxm, mnt+1);
  TABwm(v) = D->tabwm; setlg(D->tabwm, mnt+1); return v;
}

/* divide by 2 in place */
static GEN
divr2_ip(GEN x) { shiftr_inplace(x, -1); return x; }

/* phi(t)=tanh((Pi/2)sinh(t)): from -1 to 1, hence also from a to b compact
 * interval */
static GEN
inittanhsinh(long m, long prec)
{
  GEN et, ex, pi = mppi(prec);
  long k, nt = -1;
  intdata D;

  intinit_start(&D, m, 1.86, prec);
  D.tabx0 = real_0(prec);
  D.tabw0 = Pi2n(-1,prec);
  et = ex = mpexp(D.h);
  for (k = 1; k < D.l; k++)
  {
    GEN xp, wp, ct, st, z;
    pari_sp av;
    gel(D.tabxp,k) = cgetr(prec);
    gel(D.tabwp,k) = cgetr(prec); av = avma;
    ct = divr2_ip(addrr(et, invr(et))); /* ch(kh) */
    st = subrr(et, ct); /* sh(kh) */
    z = invr( addrs(mpexp(mulrr(pi, st)), 1) );
    shiftr_inplace(z, 1);
    xp = subsr(1, z);
    wp = divr2_ip(mulrr(mulrr(pi,ct), mulrr(z, subsr(2, z))));
    if (expo(wp) < -D.eps) { nt = k-1; break; }
    affrr(xp, gel(D.tabxp,k));
    if (absrnz_equal1(gel(D.tabxp,k))) { nt = k-1; break; }
    affrr(wp, gel(D.tabwp,k)); et = gerepileuptoleaf(av, mulrr(et, ex));
  }
  return intinit_end(&D, nt, 0);
}

/* phi(t)=sinh(sinh(t)): from -oo to oo, slowly decreasing, at least
 * as 1/x^2. */
static GEN
initsinhsinh(long m, long prec)
{
  pari_sp av;
  GEN et, ct, st, ex;
  long k, nt = -1;
  intdata D;

  intinit_start(&D, m, 0.666, prec);
  D.tabx0 = real_0(prec);
  D.tabw0 = real_1(prec);
  et = ex = mpexp(D.h);
  for (k = 1; k < D.l; k++)
  {
    GEN xp, wp, ext, exu;
    gel(D.tabxp,k) = cgetr(prec);
    gel(D.tabwp,k) = cgetr(prec); av = avma;
    ct = divr2_ip(addrr(et, invr(et)));
    st = subrr(et, ct);
    ext = mpexp(st);
    exu = invr(ext);
    xp = divr2_ip(subrr(ext, exu));
    wp = divr2_ip(mulrr(ct, addrr(ext, exu)));
    if (expo(wp) - 2*expo(xp) < -D.eps) { nt = k-1; break; }
    affrr(xp, gel(D.tabxp,k));
    affrr(wp, gel(D.tabwp,k)); et = gerepileuptoleaf(av, mulrr(et, ex));
  }
  return intinit_end(&D, nt, 0);
}

/* phi(t)=2sinh(t): from -oo to oo, exponentially decreasing as exp(-x) */
static GEN
initsinh(long m, long prec)
{
  pari_sp av;
  GEN et, ex, eti, xp, wp;
  long k, nt = -1;
  intdata D;

  intinit_start(&D, m, 1.0, prec);
  D.tabx0 = real_0(prec);
  D.tabw0 = real2n(1, prec);
  et = ex = mpexp(D.h);
  for (k = 1; k < D.l; k++)
  {
    gel(D.tabxp,k) = cgetr(prec);
    gel(D.tabwp,k) = cgetr(prec); av = avma;
    eti = invr(et);
    xp = subrr(et, eti);
    wp = addrr(et, eti);
    if (cmprs(xp, (long)(M_LN2*(expo(wp)+D.eps) + 1)) > 0) { nt = k-1; break; }
    affrr(xp, gel(D.tabxp,k));
    affrr(wp, gel(D.tabwp,k)); et = gerepileuptoleaf(av, mulrr(et, ex));
  }
  return intinit_end(&D, nt, 0);
}

/* phi(t)=exp(2sinh(t)): from 0 to oo, slowly decreasing at least as 1/x^2 */
static GEN
initexpsinh(long m, long prec)
{
  GEN et, ex;
  long k, nt = -1;
  intdata D;

  intinit_start(&D, m, 1.05, prec);
  D.tabx0 = real_1(prec);
  D.tabw0 = real2n(1, prec);
  ex = mpexp(D.h);
  et = real_1(prec);
  for (k = 1; k < D.l; k++)
  {
    GEN t, eti, xp;
    et = mulrr(et, ex);
    eti = invr(et); t = addrr(et, eti);
    xp = mpexp(subrr(et, eti));
    gel(D.tabxp,k) = xp;
    gel(D.tabwp,k) = mulrr(xp, t);
    gel(D.tabxm,k) = invr(xp);
    gel(D.tabwm,k) = mulrr(gel(D.tabxm,k), t);
    if (expo(gel(D.tabxm,k)) < -D.eps) { nt = k-1; break; }
  }
  return intinit_end(&D, nt, nt);
}

/* phi(t)=exp(t-exp(-t)) : from 0 to +oo, exponentially decreasing. */
static GEN
initexpexp(long m, long prec)
{
  pari_sp av;
  GEN et, ex;
  long k, nt = -1;
  intdata D;

  intinit_start(&D, m, 1.76, prec);
  D.tabx0 = mpexp(real_m1(prec));
  D.tabw0 = gmul2n(D.tabx0, 1);
  et = ex = mpexp(negr(D.h));
  for (k = 1; k < D.l; k++)
  {
    GEN xp, xm, wp, wm, eti, kh;
    gel(D.tabxp,k) = cgetr(prec);
    gel(D.tabwp,k) = cgetr(prec);
    gel(D.tabxm,k) = cgetr(prec);
    gel(D.tabwm,k) = cgetr(prec); av = avma;
    eti = invr(et); kh = mulur(k,D.h);
    xp = mpexp(subrr(kh, et));
    xm = mpexp(negr(addrr(kh, eti)));
    wp = mulrr(xp, addsr(1, et));
    wm = mulrr(xm, addsr(1, eti));
    if (expo(xm) < -D.eps && cmprs(xp, (long)(M_LN2*(expo(wp)+D.eps) + 1)) > 0) { nt = k-1; break; }
    affrr(xp, gel(D.tabxp,k));
    affrr(wp, gel(D.tabwp,k));
    affrr(xm, gel(D.tabxm,k));
    affrr(wm, gel(D.tabwm,k)); et = gerepileuptoleaf(av, mulrr(et, ex));
  }
  return intinit_end(&D, nt, nt);
}

/* phi(t)=(Pi/h)*t/(1-exp(-sinh(t))) from 0 to oo, sine oscillation */
static GEN
initnumsine(long m, long prec)
{
  pari_sp av;
  GEN invh, et, eti, ex, pi = mppi(prec);
  long exh, k, nt = -1;
  intdata D;

  intinit_start(&D, m, 0.666, prec);
  invh = invr(D.h);
  D.tabx0 = mulrr(pi, invh);
  D.tabw0 = gmul2n(D.tabx0,-1);
  exh = expo(invh); /*  expo(1/h) */
  et = ex = mpexp(D.h);
  for (k = 1; k < D.l; k++)
  {
    GEN xp,xm, wp,wm, ct,st, extp,extp1,extp2, extm,extm1,extm2, kct, kpi;
    gel(D.tabxp,k) = cgetr(prec);
    gel(D.tabwp,k) = cgetr(prec);
    gel(D.tabxm,k) = cgetr(prec);
    gel(D.tabwm,k) = cgetr(prec); av = avma;
    eti = invr(et); /* exp(-kh) */
    ct = divr2_ip(addrr(et, eti)); /* ch(kh) */
    st = divr2_ip(subrr(et, eti)); /* sh(kh) */
    extp = mpexp(st);  extp1 = subsr(1, extp);
    extp2 = invr(extp1); /* 1/(1-exp(sh(kh))) */
    extm = invr(extp); extm1 = subsr(1, extm);
    extm2 = invr(extm1);/* 1/(1-exp(sh(-kh))) */
    kpi = mulur(k, pi);
    kct = mulur(k, ct);
    extm1 = mulrr(extm1, invh);
    extp1 = mulrr(extp1, invh);
    xp = mulrr(kpi, extm2); /* phi(kh) */
    wp = mulrr(subrr(extm1, mulrr(kct, extm)), mulrr(pi, sqrr(extm2)));
    xm = mulrr(negr(kpi), extp2); /* phi(-kh) */
    wm = mulrr(addrr(extp1, mulrr(kct, extp)), mulrr(pi, sqrr(extp2)));
    if (expo(wm) < -D.eps && expo(extm) + exh + expu(10 * k) < -D.eps) { nt = k-1; break; }
    affrr(xp, gel(D.tabxp,k));
    affrr(wp, gel(D.tabwp,k));
    affrr(xm, gel(D.tabxm,k));
    affrr(wm, gel(D.tabwm,k)); et = gerepileuptoleaf(av, mulrr(et, ex));
  }
  return intinit_end(&D, nt, nt);
}

/* End of initialization functions. These functions can be executed once
 * and for all for a given accuracy and type of integral ([a,b], [a,oo[ or
 * ]-oo,a], ]-oo,oo[) */

/* The numbers below can be changed, but NOT the ordering */
enum {
  f_REG     = 0, /* regular function */
  f_SER     = 1, /* power series */
  f_SINGSER = 2, /* algebraic singularity, power series endpoint */
  f_SING    = 3, /* algebraic singularity */
  f_YSLOW   = 4, /* oo, slowly decreasing, at least x^(-2)  */
  f_YVSLO   = 5, /* oo, very slowly decreasing, worse than x^(-2) */
  f_YFAST   = 6, /* oo, exponentially decreasing */
  f_YOSCS   = 7, /* oo, sine oscillating */
  f_YOSCC   = 8  /* oo, cosine oscillating */
};
/* is finite ? */
static int
is_fin_f(long c) { return c == f_REG || c == f_SER || c == f_SING; }
/* is oscillatory ? */
static int
is_osc(long c) { long a = labs(c); return a == f_YOSCC|| a == f_YOSCS; }

/* All inner functions such as intn, etc... must be called with a
 * valid 'tab' table. The wrapper intnum provides a higher level interface */

/* compute \int_a^b f(t)dt with [a,b] compact and f nonsingular. */
static GEN
intn(void *E, GEN (*eval)(void*, GEN), GEN a, GEN b, GEN tab)
{
  GEN tabx0, tabw0, tabxp, tabwp;
  GEN bpa, bma, bmb, S;
  long i, prec;
  pari_sp ltop = avma, av;

  if (!checktabsimp(tab)) pari_err_TYPE("intnum",tab);
  tabx0 = TABx0(tab); tabw0 = TABw0(tab); prec = gprecision(tabw0);
  tabxp = TABxp(tab); tabwp = TABwp(tab);
  bpa = gmul2n(gadd(b, a), -1); /* (b+a)/2 */
  bma = gsub(bpa, a); /* (b-a)/2 */
  av = avma;
  bmb = gmul(bma, tabx0); /* (b-a)/2 phi(0) */
  /* phi'(0) f( (b+a)/2 + (b-a)/2 * phi(0) ) */
  S = gmul(tabw0, eval(E, gadd(bpa, bmb)));
  for (i = lg(tabxp)-1; i > 0; i--)
  {
    GEN SP, SM;
    bmb = gmul(bma, gel(tabxp,i));
    SP = eval(E, gsub(bpa, bmb));
    SM = eval(E, gadd(bpa, bmb));
    S = gadd(S, gmul(gel(tabwp,i), gadd(SP, SM)));
    if ((i & 0x7f) == 1) S = gerepileupto(av, S);
    S = gprec_wensure(S, prec);
  }
  return gerepileupto(ltop, gmul(S, gmul(bma, TABh(tab))));
}

/* compute \int_a^b f(t)dt with [a,b] compact, possible singularity with
 * exponent a[2] at lower extremity, b regular. Use tanh(sinh(t)). */
static GEN
intnsing(void *E, GEN (*eval)(void*, GEN), GEN a, GEN b, GEN tab)
{
  GEN tabx0, tabw0, tabxp, tabwp, ea, ba, S;
  long i, prec;
  pari_sp ltop = avma, av;

  if (!checktabsimp(tab)) pari_err_TYPE("intnum",tab);
  tabx0 = TABx0(tab); tabw0 = TABw0(tab); prec = gprecision(tabw0);
  tabxp = TABxp(tab); tabwp = TABwp(tab);
  ea = ginv(gaddsg(1, gel(a,2)));
  a = gel(a,1);
  ba = gdiv(gsub(b, a), gpow(gen_2, ea, prec));
  av = avma;
  S = gmul(gmul(tabw0, ba), eval(E, gadd(gmul(ba, addsr(1, tabx0)), a)));
  for (i = lg(tabxp)-1; i > 0; i--)
  {
    GEN p = addsr(1, gel(tabxp,i));
    GEN m = subsr(1, gel(tabxp,i));
    GEN bp = gmul(ba, gpow(p, ea, prec));
    GEN bm = gmul(ba, gpow(m, ea, prec));
    GEN SP = gmul(gdiv(bp, p), eval(E, gadd(bp, a)));
    GEN SM = gmul(gdiv(bm, m), eval(E, gadd(bm, a)));
    S = gadd(S, gmul(gel(tabwp,i), gadd(SP, SM)));
    if ((i & 0x7f) == 1) S = gerepileupto(av, S);
    S = gprec_wensure(S, prec);
  }
  return gerepileupto(ltop, gmul(gmul(S, TABh(tab)), ea));
}

static GEN id(GEN x) { return x; }

/* compute  \int_a^oo f(t)dt if si>0 or \int_{-oo}^a f(t)dt if si<0$.
 * Use exp(2sinh(t)) for slowly decreasing functions, exp(1+t-exp(-t)) for
 * exponentially decreasing functions, and (pi/h)t/(1-exp(-sinh(t))) for
 * oscillating functions. */
static GEN
intninfpm(void *E, GEN (*eval)(void*, GEN), GEN a, long sb, GEN tab)
{
  GEN tabx0, tabw0, tabxp, tabwp, tabxm, tabwm;
  GEN S;
  long L, i, prec;
  pari_sp av = avma;

  if (!checktabdoub(tab)) pari_err_TYPE("intnum",tab);
  tabx0 = TABx0(tab); tabw0 = TABw0(tab); prec = gprecision(tabw0);
  tabxp = TABxp(tab); tabwp = TABwp(tab); L = lg(tabxp);
  tabxm = TABxm(tab); tabwm = TABwm(tab);
  if (gequal0(a))
  {
    GEN (*NEG)(GEN) = sb > 0? id: gneg;
    S = gmul(tabw0, eval(E, NEG(tabx0)));
    for (i = 1; i < L; i++)
    {
      GEN SP = eval(E, NEG(gel(tabxp,i)));
      GEN SM = eval(E, NEG(gel(tabxm,i)));
      S = gadd(S, gadd(gmul(gel(tabwp,i), SP), gmul(gel(tabwm,i), SM)));
      if ((i & 0x7f) == 1) S = gerepileupto(av, S);
      S = gprec_wensure(S, prec);
    }
  }
  else if (gexpo(a) <= 0 || is_osc(sb))
  { /* a small */
    GEN (*ADD)(GEN,GEN) = sb > 0? gadd: gsub;
    S = gmul(tabw0, eval(E, ADD(a, tabx0)));
    for (i = 1; i < L; i++)
    {
      GEN SP = eval(E, ADD(a, gel(tabxp,i)));
      GEN SM = eval(E, ADD(a, gel(tabxm,i)));
      S = gadd(S, gadd(gmul(gel(tabwp,i), SP), gmul(gel(tabwm,i), SM)));
      if ((i & 0x7f) == 1) S = gerepileupto(av, S);
      S = gprec_wensure(S, prec);
    }
  }
  else
  { /* a large, |a|*\int_sgn(a)^{oo} f(|a|*x)dx (sb > 0)*/
    GEN (*ADD)(long,GEN) = sb > 0? addsr: subsr;
    long sa = gsigne(a);
    GEN A = sa > 0? a: gneg(a);
    pari_sp av2 = avma;
    S = gmul(tabw0, eval(E, gmul(A, ADD(sa, tabx0))));
    for (i = 1; i < L; i++)
    {
      GEN SP = eval(E, gmul(A, ADD(sa, gel(tabxp,i))));
      GEN SM = eval(E, gmul(A, ADD(sa, gel(tabxm,i))));
      S = gadd(S, gadd(gmul(gel(tabwp,i), SP), gmul(gel(tabwm,i), SM)));
      if ((i & 0x7f) == 1) S = gerepileupto(av2, S);
      S = gprec_wensure(S, prec);
    }
    S = gmul(S,A);
  }
  return gerepileupto(av, gmul(S, TABh(tab)));
}

/* Compute  \int_{-oo}^oo f(t)dt
 * use sinh(sinh(t)) for slowly decreasing functions and sinh(t) for
 * exponentially decreasing functions.
 * HACK: in case TABwm(tab) contains something, assume function to be integrated
 * satisfies f(-x) = conj(f(x)).
 */
static GEN
intninfinf(void *E, GEN (*eval)(void*, GEN), GEN tab)
{
  GEN tabx0, tabw0, tabxp, tabwp, tabwm;
  GEN S;
  long L, i, prec, spf;
  pari_sp ltop = avma;

  if (!checktabsimp(tab)) pari_err_TYPE("intnum",tab);
  tabx0 = TABx0(tab); tabw0 = TABw0(tab); prec = gprecision(tabw0);
  tabxp = TABxp(tab); tabwp = TABwp(tab); L = lg(tabxp);
  tabwm = TABwm(tab);
  spf = (lg(tabwm) == lg(tabwp));
  S = gmul(tabw0, eval(E, tabx0));
  if (spf) S = gmul2n(real_i(S), -1);
  for (i = L-1; i > 0; i--)
  {
    GEN SP = eval(E, gel(tabxp,i));
    if (spf)
      S = gadd(S, real_i(gmul(gel(tabwp,i), SP)));
    else
    {
      GEN SM = eval(E, negr(gel(tabxp,i)));
      S = gadd(S, gmul(gel(tabwp,i), gadd(SP,SM)));
    }
    if ((i & 0x7f) == 1) S = gerepileupto(ltop, S);
    S = gprec_wensure(S, prec);
  }
  if (spf) S = gmul2n(S,1);
  return gerepileupto(ltop, gmul(S, TABh(tab)));
}

/* general num integration routine int_a^b f(t)dt, where a and b are as follows:
 - a scalar : the scalar, no singularity worse than logarithmic at a.
 - [a, e] : the scalar a, singularity exponent -1 < e <= 0.
 - +oo: slowly decreasing function (at least O(t^-2))
 - [[+oo], a], a nonnegative real : +oo, function behaving like exp(-a|t|)
 - [[+oo], e], e < -1 : +oo, function behaving like t^e
 - [[+oo], a*I], a > 0 real : +oo, function behaving like cos(at)
 - [[+oo], a*I], a < 0 real : +oo, function behaving like sin(at)
 and similarly at -oo */
static GEN
f_getycplx(GEN a, long prec)
{
  long s;
  GEN tmp, a2R, a2I;

  if (lg(a) == 2 || gequal0(gel(a,2))) return gen_1;
  a2R = real_i(gel(a,2));
  a2I = imag_i(gel(a,2));
  s = gsigne(a2I); if (s < 0) a2I = gneg(a2I);
  tmp = s ? ginv(a2I) : ginv(a2R);
  if (gprecision(tmp) < prec) tmp = gprec_w(tmp, prec);
  return tmp;
}

static void
err_code(GEN a, const char *name)
{
  char *s = stack_sprintf("intnum [incorrect %s]", name);
  pari_err_TYPE(s, a);
}

/* a = [[+/-oo], alpha]*/
static long
code_aux(GEN a, const char *name)
{
  GEN re, im, alpha = gel(a,2);
  long s;
  if (!isinC(alpha)) err_code(a, name);
  re = real_i(alpha);
  im = imag_i(alpha);
  s = gsigne(im);
  if (s)
  {
    if (!gequal0(re)) err_code(a, name);
    return s > 0 ? f_YOSCC : f_YOSCS;
  }
  if (gequal0(re) || gcmpgs(re, -2)<=0) return f_YSLOW;
  if (gsigne(re) > 0) return f_YFAST;
  if (gcmpgs(re, -1) >= 0) err_code(a, name);
  return f_YVSLO;
}

static long
transcode(GEN a, const char *name)
{
  GEN a1, a2;
  switch(typ(a))
  {
    case t_VEC: break;
    case t_INFINITY:
      return inf_get_sign(a) == 1 ? f_YSLOW: -f_YSLOW;
    case t_SER: case t_POL: case t_RFRAC:
      return f_SER;
    default: if (!isinC(a)) err_code(a,name);
      return f_REG;
  }
  switch(lg(a))
  {
    case 2: return gsigne(gel(a,1)) > 0 ? f_YSLOW : -f_YSLOW;
    case 3: break;
    default: err_code(a,name);
  }
  a1 = gel(a,1);
  a2 = gel(a,2);
  switch(typ(a1))
  {
    case t_VEC:
      if (lg(a1) != 2) err_code(a,name);
      return gsigne(gel(a1,1)) * code_aux(a, name);
    case t_INFINITY:
      return inf_get_sign(a1) * code_aux(a, name);
    case t_SER: case t_POL: case t_RFRAC:
      if (!isinR(a2)) err_code(a,name);
      if (gcmpgs(a2, -1) <= 0)
        pari_err_IMPL("intnum with diverging non constant limit");
      return gsigne(a2) < 0 ? f_SINGSER : f_SER;
    default:
      if (!isinC(a1) || !isinR(a2) || gcmpgs(a2, -1) <= 0) err_code(a,name);
      return gsigne(a2) < 0 ? f_SING : f_REG;
  }
}

/* computes the necessary tabs, knowing a, b and m */
static GEN
homtab(GEN tab, GEN k)
{
  GEN z;
  if (gequal0(k) || gequal(k, gen_1)) return tab;
  if (gsigne(k) < 0) k = gneg(k);
  z = cgetg(LGTAB, t_VEC);
  TABx0(z) = gmul(TABx0(tab), k);
  TABw0(z) = gmul(TABw0(tab), k);
  TABxp(z) = gmul(TABxp(tab), k);
  TABwp(z) = gmul(TABwp(tab), k);
  TABxm(z) = gmul(TABxm(tab), k);
  TABwm(z) = gmul(TABwm(tab), k);
  TABh(z) = rcopy(TABh(tab)); return z;
}

static GEN
expvec(GEN v, GEN ea, long prec)
{
  long lv = lg(v), i;
  GEN z = cgetg(lv, t_VEC);
  for (i = 1; i < lv; i++) gel(z,i) = gpow(gel(v,i),ea,prec);
  return z;
}

static GEN
expscalpr(GEN vnew, GEN xold, GEN wold, GEN ea)
{
  pari_sp av = avma;
  return gerepileupto(av, gdiv(gmul(gmul(vnew, wold), ea), xold));
}
static GEN
expvecpr(GEN vnew, GEN xold, GEN wold, GEN ea)
{
  long lv = lg(vnew), i;
  GEN z = cgetg(lv, t_VEC);
  for (i = 1; i < lv; i++)
    gel(z,i) = expscalpr(gel(vnew,i), gel(xold,i), gel(wold,i), ea);
  return z;
}

/* here k < -1 */
static GEN
exptab(GEN tab, GEN k, long prec)
{
  GEN v, ea;

  if (gcmpgs(k, -2) <= 0) return tab;
  ea = ginv(gsubsg(-1, k));
  v = cgetg(LGTAB, t_VEC);
  TABx0(v) = gpow(TABx0(tab), ea, prec);
  TABw0(v) = expscalpr(TABx0(v), TABx0(tab), TABw0(tab), ea);
  TABxp(v) = expvec(TABxp(tab), ea, prec);
  TABwp(v) = expvecpr(TABxp(v), TABxp(tab), TABwp(tab), ea);
  TABxm(v) = expvec(TABxm(tab), ea, prec);
  TABwm(v) = expvecpr(TABxm(v), TABxm(tab), TABwm(tab), ea);
  TABh(v) = rcopy(TABh(tab));
  return v;
}

static GEN
init_fin(GEN b, long codeb, long m, long l, long prec)
{
  switch(labs(codeb))
  {
    case f_REG:
    case f_SING:  return inittanhsinh(m,l);
    case f_YSLOW: return initexpsinh(m,l);
    case f_YVSLO: return exptab(initexpsinh(m,l), gel(b,2), prec);
    case f_YFAST: return homtab(initexpexp(m,l), f_getycplx(b,l));
    /* f_YOSCS, f_YOSCC */
    default: return homtab(initnumsine(m,l),f_getycplx(b,l));
  }
}

static GEN
intnuminit_i(GEN a, GEN b, long m, long prec)
{
  long codea, codeb, l;
  GEN T, kma, kmb, tmp;

  if (m > 30) pari_err_OVERFLOW("intnuminit [m]");
  if (m < 0) pari_err_DOMAIN("intnuminit", "m", "<", gen_0, stoi(m));
  l = prec+EXTRAPREC;
  codea = transcode(a, "a"); if (codea == f_SER) codea = f_REG;
  codeb = transcode(b, "b"); if (codeb == f_SER) codeb = f_REG;
  if (codea == f_SINGSER || codeb == f_SINGSER)
    pari_err_IMPL("intnuminit with singularity at non constant limit");
  if (labs(codea) > labs(codeb)) { swap(a, b); lswap(codea, codeb); }
  if (codea == f_REG)
  {
    T = init_fin(b, codeb, m,l,prec);
    switch(labs(codeb))
    {
      case f_YOSCS: if (gequal0(a)) break;
      case f_YOSCC: T = mkvec2(inittanhsinh(m,l), T);
    }
    return T;
  }
  if (codea == f_SING)
  {
    T = init_fin(b,codeb, m,l,prec);
    T = mkvec2(labs(codeb) == f_SING? T: inittanhsinh(m,l), T);
    return T;
  }
  /* now a and b are infinite */
  if (codea * codeb > 0) return gen_0;
  kma = f_getycplx(a,l); codea = labs(codea);
  kmb = f_getycplx(b,l); codeb = labs(codeb);
  if (codea == f_YSLOW && codeb == f_YSLOW) return initsinhsinh(m, l);
  if (codea == f_YFAST && codeb == f_YFAST && gequal(kma, kmb))
    return homtab(initsinh(m,l), kmb);
  T = cgetg(3, t_VEC);
  switch (codea)
  {
    case f_YSLOW:
    case f_YVSLO:
      tmp = initexpsinh(m,l);
      gel(T,1) = codea == f_YSLOW? tmp: exptab(tmp, gel(a,2), prec);
      switch (codeb)
      {
        case f_YVSLO: gel(T,2) = exptab(tmp, gel(b,2), prec); return T;
        case f_YFAST: gel(T,2) = homtab(initexpexp(m,l), kmb); return T;
        /* YOSC[CS] */
        default: gel(T,2) = homtab(initnumsine(m,l), kmb); return T;
      }
      break;
    case f_YFAST:
      tmp = initexpexp(m, l);
      gel(T,1) = homtab(tmp, kma);
      switch (codeb)
      {
        case f_YFAST: gel(T,2) = homtab(tmp, kmb); return T;
        /* YOSC[CS] */
        default: gel(T,2) = homtab(initnumsine(m, l), kmb); return T;
      }
    default: /* YOSC[CS] */
      tmp = initnumsine(m, l);
      gel(T,1) = homtab(tmp,kma);
      if (codea == f_YOSCC && codeb == f_YOSCC && !gequal(kma, kmb))
        gel(T,2) = mkvec2(inittanhsinh(m,l), homtab(tmp,kmb));
      else
        gel(T,2) = homtab(tmp,kmb);
      return T;
  }
}
GEN
intnuminit(GEN a, GEN b, long m, long prec)
{
  pari_sp av = avma;
  return gerepilecopy(av, intnuminit_i(a,b,m,prec));
}

static GEN
intnuminit0(GEN a, GEN b, GEN tab, long prec)
{
  long m;
  if (!tab) m = 0;
  else if (typ(tab) != t_INT)
  {
    if (!checktab(tab)) pari_err_TYPE("intnuminit0",tab);
    return tab;
  }
  else
    m = itos(tab);
  return intnuminit(a, b, m, prec);
}

/* Assigns the values of the function weighted by w[k] at quadrature points x[k]
 * [replacing the weights]. Return the index of the last non-zero coeff */
static long
weight(void *E, GEN (*eval)(void *, GEN), GEN x, GEN w)
{
  long k, l = lg(x);
  for (k = 1; k < l; k++) gel(w,k) = gmul(gel(w,k), eval(E, gel(x,k)));
  k--; while (k >= 1) if (!gequal0(gel(w,k--))) break;
  return k;
}
/* compute the necessary tabs, weights multiplied by f(t) */
static GEN
intfuncinit_i(void *E, GEN (*eval)(void*, GEN), GEN tab)
{
  GEN tabxp = TABxp(tab), tabwp = TABwp(tab);
  GEN tabxm = TABxm(tab), tabwm = TABwm(tab);
  long L, L0 = lg(tabxp);

  TABw0(tab) = gmul(TABw0(tab), eval(E, TABx0(tab)));
  if (lg(tabxm) == 1)
  {
    TABxm(tab) = tabxm = gneg(tabxp);
    TABwm(tab) = tabwm = leafcopy(tabwp);
  }
  /* update wp and wm in place */
  L = minss(weight(E, eval, tabxp, tabwp), weight(E, eval, tabxm, tabwm));
  if (L < L0)
  { /* catch up functions whose growth at oo was not adequately described */
    setlg(tabxp, L+1);
    setlg(tabwp, L+1);
    if (lg(tabxm) > 1) { setlg(tabxm, L+1); setlg(tabwm, L+1); }
  }
  return tab;
}

GEN
intfuncinit(void *E, GEN (*eval)(void*, GEN), GEN a, GEN b, long m, long prec)
{
  pari_sp av = avma;
  GEN tab = intnuminit_i(a, b, m, prec);

  if (lg(tab) == 3)
    pari_err_IMPL("intfuncinit with hard endpoint behavior");
  if (is_fin_f(transcode(a,"intfuncinit")) ||
      is_fin_f(transcode(b,"intfuncinit")))
    pari_err_IMPL("intfuncinit with finite endpoints");
  return gerepilecopy(av, intfuncinit_i(E, eval, tab));
}

static GEN
intnum_i(void *E, GEN (*eval)(void*, GEN), GEN a, GEN b, GEN tab, long prec)
{
  GEN S = gen_0, res1, res2, kma, kmb;
  long sb, sgns = 1, codea = transcode(a, "a"), codeb = transcode(b, "b");

  if (codea == f_REG && typ(a) == t_VEC) a = gel(a,1);
  if (codeb == f_REG && typ(b) == t_VEC) b = gel(b,1);
  if (codea == f_REG && codeb == f_REG) return intn(E, eval, a, b, tab);
  if (codea == f_SER || codeb == f_SER) return intlin(E, eval, a, b, tab, prec);
  if (labs(codea) > labs(codeb)) { swap(a,b); lswap(codea,codeb); sgns = -1; }
  /* now labs(codea) <= labs(codeb) */
  if (codeb == f_SING)
  {
    if (codea == f_REG)
      S = intnsing(E, eval, b, a, tab), sgns = -sgns;
    else
    {
      GEN c = gmul2n(gadd(gel(a,1), gel(b,1)), -1);
      res1 = intnsing(E, eval, a, c, gel(tab,1));
      res2 = intnsing(E, eval, b, c, gel(tab,2));
      S = gsub(res1, res2);
    }
    return (sgns < 0) ? gneg(S) : S;
  }
  /* now b is infinite */
  sb = codeb > 0 ? 1 : -1;
  codeb = labs(codeb);
  if (codea == f_REG && codeb != f_YOSCC
      && (codeb != f_YOSCS || gequal0(a)))
  {
    S = intninfpm(E, eval, a, sb*codeb, tab);
    return sgns*sb < 0 ? gneg(S) : S;
  }
  if (is_fin_f(codea))
  { /* either codea == f_SING  or codea == f_REG and codeb = f_YOSCC
     * or (codeb == f_YOSCS and !gequal0(a)) */
    GEN c = real_i(codea == f_SING? gel(a,1): a);
    switch(codeb)
    {
      case f_YOSCC: case f_YOSCS:
      {
        GEN pi2p = gmul(Pi2n(1,prec), f_getycplx(b, prec));
        GEN pis2p = gmul2n(pi2p, -2);
        if (codeb == f_YOSCC) c = gadd(c, pis2p);
        c = gdiv(c, pi2p);
        c = sb > 0? addiu(gceil(c), 1): subiu(gfloor(c), 1);
        c = gmul(pi2p, c);
        if (codeb == f_YOSCC) c = gsub(c, pis2p);
        break;
      }
      default:
        c = sb > 0? addiu(gceil(c), 1): subiu(gfloor(c), 1);
        break;
    }
    res1 = codea==f_SING? intnsing(E, eval, a, c, gel(tab,1))
                        : intn    (E, eval, a, c, gel(tab,1));
    res2 = intninfpm(E, eval, c, sb*codeb, gel(tab,2));
    if (sb < 0) res2 = gneg(res2);
    res1 = gadd(res1, res2);
    return sgns < 0 ? gneg(res1) : res1;
  }
  /* now a and b are infinite */
  if (codea * sb > 0)
  {
    if (codea > 0) pari_warn(warner, "integral from oo to oo");
    if (codea < 0) pari_warn(warner, "integral from -oo to -oo");
    return gen_0;
  }
  if (sb < 0) sgns = -sgns;
  codea = labs(codea);
  kma = f_getycplx(a, prec);
  kmb = f_getycplx(b, prec);
  if ((codea == f_YSLOW && codeb == f_YSLOW)
   || (codea == f_YFAST && codeb == f_YFAST && gequal(kma, kmb)))
    S = intninfinf(E, eval, tab);
  else
  {
    GEN pis2 = Pi2n(-1, prec);
    GEN ca = (codea == f_YOSCC)? gmul(pis2, kma): gen_0;
    GEN cb = (codeb == f_YOSCC)? gmul(pis2, kmb): gen_0;
    GEN c = codea == f_YOSCC ? ca : cb; /*signe(a)=-sb*/
    GEN SP, SN = intninfpm(E, eval, c, -sb*codea, gel(tab,1));
    if (codea != f_YOSCC)
      SP = intninfpm(E, eval, cb, sb*codeb, gel(tab,2));
    /* codea = codeb = f_YOSCC */
    else if (gequal(kma, kmb))
      SP = intninfpm(E, eval, cb, sb*codeb, gel(tab,2));
    else
    {
      tab = gel(tab,2);
      SP = intninfpm(E, eval, cb, sb*codeb, gel(tab,2));
      SP = gadd(SP, intn(E, eval, ca, cb, gel(tab,1)));
    }
    S = gadd(SN, SP);
  }
  if (sgns < 0) S = gneg(S);
  return S;
}

GEN
intnum(void *E, GEN (*eval)(void*, GEN), GEN a, GEN b, GEN tab, long prec)
{
  pari_sp ltop = avma;
  long l = prec+EXTRAPREC;
  GEN na = NULL, nb = NULL, S;

  if (transcode(a,"a") == f_SINGSER) {
    long v = gvar(gel(a,1));
    if (v != NO_VARIABLE) {
      na = cgetg(3,t_VEC);
      gel(na,1) = polcoeff0(gel(a,1),0,v);
      gel(na,2) = gel(a,2);
    }
    a = gel(a,1);
  }
  if (transcode(b,"b") == f_SINGSER) {
    long v = gvar(gel(b,1));
    if (v != NO_VARIABLE) {
      nb = cgetg(3,t_VEC);
      gel(nb,1) = polcoeff0(gel(b,1),0,v);
      gel(nb,2) = gel(b,2);
    }
    b = gel(b,1);
  }
  if (na || nb) {
    if (tab && typ(tab) != t_INT)
      pari_err_IMPL("non integer tab argument");
    S = intnum(E, eval, na ? na : a, nb ? nb : b, tab, prec);
    if (na) S = gsub(S, intnum(E, eval, na, a, tab, prec));
    if (nb) S = gsub(S, intnum(E, eval, b, nb, tab, prec));
    return gerepilecopy(ltop, S);
  }
  tab = intnuminit0(a, b, tab, prec);
  S = intnum_i(E, eval, gprec_w(a, l), gprec_w(b, l), tab, prec);
  return gerepilecopy(ltop, gprec_wtrunc(S, prec));
}

typedef struct auxint_s {
  GEN a, R, mult;
  GEN (*f)(void*, GEN);
  GEN (*w)(GEN, long);
  long prec;
  void *E;
} auxint_t;

static GEN
auxcirc(void *E, GEN t)
{
  auxint_t *D = (auxint_t*) E;
  GEN s, c, z;
  mpsincos(mulrr(t, D->mult), &s, &c); z = mkcomplex(c,s);
  return gmul(z, D->f(D->E, gadd(D->a, gmul(D->R, z))));
}

GEN
intcirc(void *E, GEN (*eval)(void*, GEN), GEN a, GEN R, GEN tab, long prec)
{
  auxint_t D;
  GEN z;

  D.a = a;
  D.R = R;
  D.mult = mppi(prec);
  D.f = eval;
  D.E = E;
  z = intnum(&D, &auxcirc, real_m1(prec), real_1(prec), tab, prec);
  return gmul2n(gmul(R, z), -1);
}

static GEN
auxlin(void *E, GEN t)
{
  auxint_t *D = (auxint_t*) E;
  return D->f(D->E, gadd(D->a, gmul(D->mult, t)));
}

static GEN
intlin(void *E, GEN (*eval)(void*, GEN), GEN a, GEN b, GEN tab, long prec)
{
  auxint_t D;
  GEN z;

  if (typ(a) == t_VEC) a = gel(a,1);
  if (typ(b) == t_VEC) b = gel(b,1);
  z = toser_i(a); if (z) a = z;
  z = toser_i(b); if (z) b = z;
  D.a = a;
  D.mult = gsub(b,a);
  D.f = eval;
  D.E = E;
  z = intnum(&D, &auxlin, real_0(prec), real_1(prec), tab, prec);
  return gmul(D.mult, z);
}

GEN
intnum0(GEN a, GEN b, GEN code, GEN tab, long prec)
{ EXPR_WRAP(code, intnum(EXPR_ARG, a, b, tab, prec)); }
GEN
intcirc0(GEN a, GEN R, GEN code, GEN tab, long prec)
{ EXPR_WRAP(code, intcirc(EXPR_ARG, a, R, tab, prec)); }
GEN
intfuncinit0(GEN a, GEN b, GEN code, long m, long prec)
{ EXPR_WRAP(code, intfuncinit(EXPR_ARG, a, b, m, prec)); }

#if 0
/* Two variable integration */

typedef struct auxf_s {
  GEN x;
  GEN (*f)(void *, GEN, GEN);
  void *E;
} auxf_t;

typedef struct indi_s {
  GEN (*c)(void*, GEN);
  GEN (*d)(void*, GEN);
  GEN (*f)(void *, GEN, GEN);
  void *Ec;
  void *Ed;
  void *Ef;
  GEN tabintern;
  long prec;
} indi_t;

static GEN
auxf(GEN y, void *E)
{
  auxf_t *D = (auxf_t*) E;
  return D->f(D->E, D->x, y);
}

static GEN
intnumdoubintern(GEN x, void *E)
{
  indi_t *D = (indi_t*) E;
  GEN c = D->c(x, D->Ec), d = D->d(x, D->Ed);
  auxf_t A;

  A.x = x;
  A.f = D->f;
  A.E = D->Ef;
  return intnum(&A, &auxf, c, d, D->tabintern, D->prec);
}

GEN
intnumdoub(void *Ef, GEN (*evalf)(void *, GEN, GEN), void *Ec, GEN (*evalc)(void*, GEN), void *Ed, GEN (*evald)(void*, GEN), GEN a, GEN b, GEN tabext, GEN tabint, long prec)
{
  indi_t E;

  E.c = evalc;
  E.d = evald;
  E.f = evalf;
  E.Ec = Ec;
  E.Ed = Ed;
  E.Ef = Ef;
  E.prec = prec;
  if (typ(tabint) == t_INT)
  {
    GEN C = evalc(a, Ec), D = evald(a, Ed);
    if (typ(C) != t_VEC && typ(D) != t_VEC) { C = gen_0; D = gen_1; }
    E.tabintern = intnuminit0(C, D, tabint, prec);
  }
  else E.tabintern = tabint;
  return intnum(&E, &intnumdoubintern, a, b, tabext, prec);
}

GEN
intnumdoub0(GEN a, GEN b, int nc, int nd, int nf, GEN tabext, GEN tabint, long prec)
{
  GEN z;
  push_lex(NULL);
  push_lex(NULL);
  z = intnumdoub(chf, &gp_eval2, chc, &gp_eval, chd, &gp_eval, a, b, tabext, tabint, prec);
  pop_lex(1); pop_lex(1); return z;
}
#endif


/* The quotient-difference algorithm. Given a vector M, convert the series
 * S = \sum_{n >= 0} M[n+1]z^n into a continued fraction.
 * Compute the c[n] such that
 * S = c[1] / (1 + c[2]z / (1+c[3]z/(1+...c[lim]z))),
 * Compute A[n] and B[n] such that
 * S = M[1]/ (1+A[1]*z+B[1]*z^2 / (1+A[2]*z+B[2]*z^2/ (1+...1/(1+A[lim\2]*z)))),
 * Assume lim <= #M.
 * Does not work for certain M. */

/* Given a continued fraction CF output by the quodif program,
convert it into an Euler continued fraction A(n), B(n), where
$1/(1+c[2]z/(1+c[3]z/(1+..c[lim]z)))
=1/(1+A[1]*z+B[1]*z^2/(1+A[2]*z+B[2]*z^2/(1+...1/(1+A[lim\2]*z)))). */
static GEN
contfrac_Euler(GEN CF)
{
  long lima, limb, i, lim = lg(CF)-1;
  GEN A, B;
  lima = lim/2;
  limb = (lim - 1)/2;
  A = cgetg(lima+1, t_VEC);
  B = cgetg(limb+1, t_VEC);
  gel (A, 1) = gel(CF, 2);
  for (i=2; i <= lima; ++i) gel(A,i) = gadd(gel(CF, 2*i), gel(CF, 2*i-1));
  for (i=1; i <= limb; ++i) gel(B,i) = gneg(gmul(gel(CF, 2*i+1), gel(CF, 2*i)));
  return mkvec2(A, B);
}

static GEN
contfracinit_i(GEN M, long lim)
{
  pari_sp av;
  GEN e, q, c;
  long lim2;
  long j, k;
  e = zerovec(lim);
  c = zerovec(lim+1); gel(c, 1) = gel(M, 1);
  q = cgetg(lim+1, t_VEC);
  for (k = 1; k <= lim; ++k) gel(q, k) = gdiv(gel(M, k+1), gel(M, k));
  lim2 = lim/2; av = avma;
  for (j = 1; j <= lim2; ++j)
  {
    long l = lim - 2*j;
    gel(c, 2*j) = gneg(gel(q, 1));
    for (k = 0; k <= l; ++k)
      gel(e, k+1) = gsub(gadd(gel(e, k+2), gel(q, k+2)), gel(q, k+1));
    for (k = 0; k < l; ++k)
      gel(q, k+1) = gdiv(gmul(gel(q, k+2), gel(e, k+2)), gel(e, k+1));
    gel(c, 2*j+1) = gneg(gel(e, 1));
    if (gc_needed(av, 3))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"contfracinit, %ld/%ld",j,lim2);
      gerepileall(av, 3, &e, &c, &q);
    }
  }
  if (odd(lim)) gel(c, lim+1) = gneg(gel(q, 1));
  return c;
}

GEN
contfracinit(GEN M, long lim)
{
  pari_sp ltop = avma;
  GEN c;
  switch(typ(M))
  {
    case t_RFRAC:
      if (lim < 0) pari_err_TYPE("contfracinit",M);
      M = gadd(M, zeroser(gvar(M), lim + 2)); /*fall through*/
    case t_SER: M = gtovec(M); break;
    case t_POL: M = gtovecrev(M); break;
    case t_VEC: case t_COL: break;
    default: pari_err_TYPE("contfracinit", M);
  }
  if (lim < 0)
    lim = lg(M)-2;
  else if (lg(M)-1 <= lim)
    pari_err_COMPONENT("contfracinit", "<", stoi(lg(M)-1), stoi(lim));
  if (lim < 0) retmkvec2(cgetg(1,t_VEC),cgetg(1,t_VEC));
  c = contfracinit_i(M, lim);
  return gerepilecopy(ltop, contfrac_Euler(c));
}

/* Evaluate at 1/tinv the nlim first terms of the continued fraction output by
 * contfracinit. */
/* Not stack clean */
GEN
contfraceval_inv(GEN CF, GEN tinv, long nlim)
{
  pari_sp btop;
  long j;
  GEN S = gen_0, S1, S2, A, B;
  if (typ(CF) != t_VEC || lg(CF) != 3) pari_err_TYPE("contfraceval", CF);
  A = gel(CF, 1); if (typ(A) != t_VEC) pari_err_TYPE("contfraceval", CF);
  B = gel(CF, 2); if (typ(B) != t_VEC) pari_err_TYPE("contfraceval", CF);
  if (nlim < 0)
    nlim = lg(A)-1;
  else if (lg(A) <= nlim)
    pari_err_COMPONENT("contfraceval", ">", stoi(lg(A)-1), stoi(nlim));
  if (lg(B)+1 <= nlim)
    pari_err_COMPONENT("contfraceval", ">", stoi(lg(B)), stoi(nlim));
  btop = avma;
  if (nlim <= 1) return lg(A)==1? gen_0: gdiv(tinv, gadd(gel(A, 1), tinv));
  switch(nlim % 3)
  {
    case 2:
      S = gdiv(gel(B, nlim-1), gadd(gel(A, nlim), tinv));
      nlim--; break;

    case 0:
      S1 = gadd(gel(A, nlim), tinv);
      S2 = gadd(gmul(gadd(gel(A, nlim-1), tinv), S1), gel(B, nlim-1));
      S = gdiv(gmul(gel(B, nlim-2), S1), S2);
      nlim -= 2; break;
  }
  /* nlim = 1 (mod 3) */
  for (j = nlim; j >= 4; j -= 3)
  {
    GEN S3;
    S1 = gadd(gadd(gel(A, j), tinv), S);
    S2 = gadd(gmul(gadd(gel(A, j-1), tinv), S1), gel(B, j-1));
    S3 = gadd(gmul(gadd(gel(A, j-2), tinv), S2), gmul(gel(B, j-2), S1));
    S = gdiv(gmul(gel(B, j-3), S2), S3);
    if (gc_needed(btop, 3)) S = gerepilecopy(btop, S);
  }
  return gdiv(tinv, gadd(gadd(gel(A, 1), tinv), S));
}

GEN
contfraceval(GEN CF, GEN t, long nlim)
{
  pari_sp ltop = avma;
  return gerepileupto(ltop, contfraceval_inv(CF, ginv(t), nlim));
}

/* MONIEN SUMMATION */

/* basic Newton, find x ~ z such that Q(x) = 0 */
static GEN
monrefine(GEN Q, GEN QP, GEN z, long prec)
{
  pari_sp av = avma;
  GEN pr = poleval(Q, z);
  for(;;)
  {
    GEN prnew;
    z = gsub(z, gdiv(pr, poleval(QP, z)));
    prnew = poleval(Q, z);
    if (gcmp(gabs(prnew, prec), gabs(pr, prec)) >= 0) break;
    pr = prnew;
  }
  z = gprec_w(z, 2*prec-2);
  z = gsub(z, gdiv(poleval(Q, z), poleval(QP, z)));
  return gerepileupto(av, z);
}

static GEN
RX_realroots(GEN x, long prec)
{ return realroots(gprec_wtrunc(x,prec), NULL, prec); }

/* (real) roots of Q, assuming QP = Q' and that half the roots are close to
 * k+1, ..., k+m, m = deg(Q)/2-1. N.B. All roots are real and >= 1 */
static GEN
monroots(GEN Q, GEN QP, long k, long prec)
{
  long j, n = degpol(Q), m = n/2 - 1;
  GEN v2, v1 = cgetg(m+1, t_VEC);
  for (j = 1; j <= m; ++j) gel(v1, j) = monrefine(Q, QP, stoi(k+j), prec);
  Q = gdivent(Q, roots_to_pol(v1, varn(Q)));
  v2 = RX_realroots(Q, prec); settyp(v2, t_VEC);
  return shallowconcat(v1, v2);
}

static void
Pade(GEN M, GEN *pP, GEN *pQ)
{
  pari_sp av = avma;
  long n = lg(M)-2, i;
  GEN v = contfracinit_i(M, n), P = pol_0(0), Q = pol_1(0);
  /* evaluate continued fraction => Pade approximants */
  for (i = n-1; i >= 1; i--)
  { /* S = P/Q: S -> v[i]*x / (1+S) */
    GEN R = RgX_shift_shallow(RgX_Rg_mul(Q,gel(v,i)), 1);
    Q = RgX_add(P,Q); P = R;
    if (gc_needed(av, 3))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"Pade, %ld/%ld",i,n-1);
      gerepileall(av, 3, &P, &Q, &v);
    }
  }
  /* S -> 1+S */
  *pP = RgX_add(P,Q);
  *pQ = Q;
}

static GEN
veczetaprime(GEN a, GEN b, long N, long prec)
{
  long newprec, fpr = prec2nbits(prec), pr = (long)ceil(fpr * 1.5);
  long l = nbits2prec(pr), e = fpr / 2;
  GEN eps, A, B;
  newprec = nbits2prec(pr + BITS_IN_LONG);
  a = gprec_w(a, newprec);
  b = gprec_w(b, newprec);
  eps = real2n(-e, l);
  A = veczeta(a, gsub(b, eps), N, newprec);
  B = veczeta(a, gadd(b, eps), N, newprec);
  return gmul2n(RgV_sub(B, A), e-1);
}

struct mon_w {
  GEN w, a, b;
  long n, j, prec;
};

/* w(x) / x^(a*(j+k)+b), k >= 1; w a t_CLOSURE or t_INT [encodes log(x)^w] */
static GEN
wrapmonw(void* E, GEN x)
{
  struct mon_w *W = (struct mon_w*)E;
  long k, j = W->j, n = W->n, prec = W->prec, l = 2*n+4-j;
  GEN wx = typ(W->w) == t_CLOSURE? closure_callgen1prec(W->w, x, prec)
                                 : powgi(glog(x, prec), W->w);
  GEN v = cgetg(l, t_VEC);
  GEN xa = gpow(x, gneg(W->a), prec), w = gmul(wx, gpowgs(xa, j));
  w = gdiv(w, gpow(x,W->b,prec));
  for (k = 1; k < l; k++) { gel(v,k) = w; w = gmul(w, xa); }
  return v;
}
/* w(x) / x^(a*j+b) */
static GEN
wrapmonw2(void* E, GEN x)
{
  struct mon_w *W = (struct mon_w*)E;
  GEN wnx = closure_callgen1prec(W->w, x, W->prec);
  return gdiv(wnx, gpow(x, gadd(gmulgs(W->a, W->j), W->b), W->prec));
}
static GEN
M_from_wrapmon(struct mon_w *S, GEN wfast, GEN n0)
{
  long j, N = 2*S->n+2;
  GEN M = cgetg(N+1, t_VEC), faj = gsub(wfast, S->b);
  for (j = 1; j <= N; j++)
  {
    faj = gsub(faj, S->a);
    if (gcmpgs(faj, -2) <= 0)
    {
      S->j = j; setlg(M,j);
      M = shallowconcat(M, sumnum((void*)S, wrapmonw, n0, NULL, S->prec));
      break;
    }
    S->j = j;
    gel(M,j) = sumnum((void*)S, wrapmonw2, mkvec2(n0,faj), NULL, S->prec);
  }
  return M;
}

static void
checkmonroots(GEN vr, long n)
{
  if (lg(vr) != n+1)
    pari_err_IMPL("recovery when missing roots in sumnummonieninit");
}

static GEN
sumnummonieninit_i(GEN a, GEN b, GEN w, GEN n0, long prec)
{
  GEN c, M, P, Q, Qp, vr, vabs, vwt, ga = gadd(a, b);
  double bit = 2*prec2nbits(prec) / gtodouble(ga), D = bit*M_LN2;
  double da = maxdd(1., gtodouble(a));
  long n = (long)ceil(D / (da*(log(D)-1)));
  long j, prec2, prec0 = prec + EXTRAPRECWORD;
  double bit0 = ceil((2*n+1)*LOG2_10);
  int neg = 1;
  struct mon_w S;

  /* 2.05 is heuristic; with 2.03, sumnummonien(n=1,1/n^2) loses
   * 19 decimals at \p1500 */
  prec = nbits2prec(maxdd(2.05*da*bit, bit0));
  prec2 = nbits2prec(maxdd(1.3*da*bit, bit0));
  S.w = w;
  S.a = a = gprec_w(a, 2*prec-2);
  S.b = b = gprec_w(b, 2*prec-2);
  S.n = n;
  S.j = 1;
  S.prec = prec;
  if (typ(w) == t_INT)
  { /* f(n) ~ \sum_{i > 0} f_i log(n)^k / n^(a*i + b); a > 0, a+b > 1 */
    long k = itos(w);
    if (k == 0)
      M = veczeta(a, ga, 2*n+2, prec);
    else if (k == 1)
      M = veczetaprime(a, ga, 2*n+2, prec);
    else
      M = M_from_wrapmon(&S, gen_0, gen_1);
    if (odd(k)) neg = 0;
  }
  else
  {
    GEN wfast = gen_0;
    if (typ(w) == t_VEC) { wfast = gel(w,2); w = gel(w,1); }
    M = M_from_wrapmon(&S, wfast, n0);
  }
  /* M[j] = sum(n >= n0, w(n) / n^(a*j+b) */
  Pade(M, &P,&Q);
  Qp = RgX_deriv(Q);
  if (gequal1(a)) a = NULL;
  if (!a && typ(w) == t_INT)
  {
    vabs = vr = monroots(Q, Qp, signe(w)? 1: 0, prec2);
    checkmonroots(vr, n);
    c = b;
  }
  else
  {
    vr = RX_realroots(Q, prec2); settyp(vr, t_VEC);
    checkmonroots(vr, n);
    if (!a) { vabs = vr; c = b; }
    else
    {
      GEN ai = ginv(a);
      vabs = cgetg(n+1, t_VEC);
      for (j = 1; j <= n; j++) gel(vabs,j) = gpow(gel(vr,j), ai, prec2);
      c = gdiv(b,a);
    }
  }

  vwt = cgetg(n+1, t_VEC);
  c = gsubgs(c,1); if (gequal0(c)) c = NULL;
  for (j = 1; j <= n; j++)
  {
    GEN r = gel(vr,j), t = gdiv(poleval(P,r), poleval(Qp,r));
    if (c) t = gmul(t, gpow(r, c, prec));
    gel(vwt,j) = neg? gneg(t): t;
  }
  if (typ(w) == t_INT && !equali1(n0))
  {
    GEN h = subiu(n0,1);
    for (j = 1; j <= n; j++) gel(vabs,j) = gadd(gel(vabs,j), h);
  }
  return mkvec3(gprec_wtrunc(vabs,prec0), gprec_wtrunc(vwt,prec0), n0);
}

GEN
sumnummonieninit(GEN asymp, GEN w, GEN n0, long prec)
{
  pari_sp av = avma;
  const char *fun = "sumnummonieninit";
  GEN a, b;
  if (!n0) n0 = gen_1; else if (typ(n0) != t_INT) pari_err_TYPE(fun, n0);
  if (!asymp) a = b = gen_1;
  else
  {
    if (typ(asymp) == t_VEC)
    {
      if (lg(asymp) != 3) pari_err_TYPE(fun, asymp);
      a = gel(asymp,1);
      b = gel(asymp,2);
    }
    else
    {
      a = gen_1;
      b = asymp;
    }
    if (gsigne(a) <= 0) pari_err_DOMAIN(fun, "a", "<=", gen_0, a);
    if (gcmpgs(gadd(a,b), 1) <= 0)
      pari_err_DOMAIN(fun, "a+b", "<=", gen_1, mkvec2(a,b));
  }
  if (!w) w = gen_0;
  else switch(typ(w))
  {
    case t_INT:
      if (signe(w) < 0) pari_err_IMPL("log power < 0 in sumnummonieninit");
    case t_CLOSURE: break;
    case t_VEC:
      if (lg(w) == 3 && typ(gel(w,1)) == t_CLOSURE) break;
    default: pari_err_TYPE(fun, w);
  }
  return gerepilecopy(av, sumnummonieninit_i(a, b, w, n0, prec));
}

GEN
sumnummonien(void *E, GEN (*eval)(void*,GEN), GEN n0, GEN tab, long prec)
{
  pari_sp av = avma;
  GEN vabs, vwt, S;
  long l, i;
  if (typ(n0) != t_INT) pari_err_TYPE("sumnummonien", n0);
  if (!tab)
    tab = sumnummonieninit_i(gen_1, gen_1, gen_0, n0, prec);
  else
  {
    if (lg(tab) != 4 || typ(tab) != t_VEC) pari_err_TYPE("sumnummonien", tab);
    if (!equalii(n0, gel(tab,3)))
      pari_err(e_MISC, "incompatible initial value %Ps != %Ps", gel(tab,3),n0);
  }
  vabs= gel(tab,1); l = lg(vabs);
  vwt = gel(tab,2);
  if (typ(vabs) != t_VEC || typ(vwt) != t_VEC || lg(vwt) != l)
    pari_err_TYPE("sumnummonien", tab);
  S = gen_0;
  for (i = 1; i < l; i++)
  {
    S = gadd(S, gmul(gel(vwt,i), eval(E, gel(vabs,i))));
    S = gprec_wensure(S, prec);
  }
  return gerepilecopy(av, gprec_w(S, prec));
}

static GEN
get_oo(GEN fast) { return mkvec2(mkoo(), fast); }

GEN
sumnuminit(GEN fast, long prec)
{
  pari_sp av;
  GEN s, v, d, C, res = cgetg(6, t_VEC);
  long bitprec = prec2nbits(prec), N, k, k2, m;
  double w;

  gel(res, 1) = d = mkfrac(gen_1, utoipos(4)); /* 1/4 */
  av = avma;
  w = gtodouble(glambertW(ginv(d), LOWDEFAULTPREC));
  N = (long)ceil(M_LN2*bitprec/(w*(1+w))+5);
  k = (long)ceil(N*w); if (k&1) k--;

  prec += EXTRAPRECWORD;
  k2 = k/2;
  s = RgX_to_ser(monomial(real_1(prec),1,0), k+3);
  s = gmul2n(gasinh(s, prec), 2); /* asinh(x)/d, d = 1/4 */
  gel(s, 2) = utoipos(4);
  s = gsub(ser_inv(gexpm1(s,prec)), ser_inv(s));
  C = matpascal(k-1);
  v = cgetg(k2+1, t_VEC);
  for (m = 1; m <= k2; m++)
  {
    pari_sp av = avma;
    GEN S = real_0(prec);
    long j;
    for (j = m; j <= k2; j++)
    { /* s[X^(2j-1)] * binomial(2*j-1, j-m) */
      GEN t = gmul(gel(s,2*j+1), gcoeff(C, 2*j,j-m+1));
      t = gmul2n(t, 1-2*j);
      S = odd(j)? gsub(S,t): gadd(S,t);
    }
    if (odd(m)) S = gneg(S);
    gel(v,m) = gerepileupto(av, S);
  }
  v = RgC_gtofp(v,prec); settyp(v, t_VEC);
  gel(res, 4) = gerepileupto(av, v);
  gel(res, 2) = utoi(N);
  gel(res, 3) = utoi(k);
  if (!fast) fast = get_oo(gen_0);
  gel(res, 5) = intnuminit(gel(res,2), fast, 0, prec - EXTRAPRECWORD);
  return res;
}

static int
checksumtab(GEN T)
{
  if (typ(T) != t_VEC || lg(T) != 6) return 0;
  return typ(gel(T,2))==t_INT && typ(gel(T,3))==t_INT && typ(gel(T,4))==t_VEC;
}
GEN
sumnum(void *E, GEN (*eval)(void*, GEN), GEN a, GEN tab, long prec)
{
  pari_sp av = avma, av2;
  GEN v, tabint, S, d, fast;
  long as, N, k, m, prec2;
  if (!a) { a = gen_1; fast = get_oo(gen_0); }
  else switch(typ(a))
  {
  case t_VEC:
    if (lg(a) != 3) pari_err_TYPE("sumnum", a);
    fast = get_oo(gel(a,2));
    a = gel(a,1); break;
  default:
    fast = get_oo(gen_0);
  }
  if (typ(a) != t_INT) pari_err_TYPE("sumnum", a);
  if (!tab) tab = sumnuminit(fast, prec);
  else if (!checksumtab(tab)) pari_err_TYPE("sumnum",tab);
  as = itos(a);
  d = gel(tab,1);
  N = maxss(as, itos(gel(tab,2)));
  k = itos(gel(tab,3));
  v = gel(tab,4);
  tabint = gel(tab,5);
  prec2 = prec+EXTRAPRECWORD;
  av2 = avma;
  S = gmul(eval(E, stoi(N)), real2n(-1,prec2));
  for (m = as; m < N; m++)
  {
    S = gadd(S, eval(E, stoi(m)));
    if (gc_needed(av, 2))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"sumnum [1], %ld/%ld",m,N);
      S = gerepileupto(av2, S);
    }
    S = gprec_wensure(S, prec2);
  }
  for (m = 1; m <= k/2; m++)
  {
    GEN t = gmulsg(2*m-1, d);
    GEN s = gsub(eval(E, gsubsg(N,t)), eval(E, gaddsg(N,t)));
    S = gadd(S, gmul(gel(v,m), s));
    if (gc_needed(av2, 2))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"sumnum [2], %ld/%ld",m,k/2);
      S = gerepileupto(av2, S);
    }
    S = gprec_wensure(S, prec2);
  }
  S = gadd(S, intnum(E, eval,stoi(N), fast, tabint, prec2));
  return gerepilecopy(av, gprec_w(S, prec));
}

GEN
sumnummonien0(GEN a, GEN code, GEN tab, long prec)
{ EXPR_WRAP(code, sumnummonien(EXPR_ARG, a, tab, prec)); }
GEN
sumnum0(GEN a, GEN code, GEN tab, long prec)
{ EXPR_WRAP(code, sumnum(EXPR_ARG, a, tab, prec)); }

/* Abel-Plana summation */

static GEN
intnumgauexpinit(long prec)
{
  pari_sp ltop = avma;
  GEN V, N, E, P, Q, R, vabs, vwt;
  long l, n, k, j, prec2, prec0 = prec + EXTRAPRECWORD, bit = prec2nbits(prec);

  n = (long)ceil(bit*0.226);
  n |= 1; /* make n odd */
  prec = nbits2prec(1.5*bit + 32);
  prec2 = maxss(prec0, nbits2prec(1.15*bit + 32));
  V = cgetg(n + 4, t_VEC);
  for (k = 1; k <= n + 3; ++k)
    gel(V, k) = gtofp(gdivgs(bernfrac(2*k), odd(k)? 2*k: -2*k), prec);
  Pade(V, &P, &Q);
  N = RgX_recip(gsub(P, Q));
  E = RgX_recip(Q);
  R = gdivgs(gdiv(N, RgX_deriv(E)), 2);
  vabs = RX_realroots(E,prec2);
  l = lg(vabs); settyp(vabs, t_VEC);
  vwt = cgetg(l, t_VEC);
  for (j = 1; j < l; ++j)
  {
    GEN a = gel(vabs,j);
    gel(vwt, j) = gprec_wtrunc(poleval(R, a), prec0);
    gel(vabs, j) = gprec_wtrunc(sqrtr_abs(a), prec0);
  }
  return gerepilecopy(ltop, mkvec2(vabs, vwt));
}

/* Compute \int_{-oo}^oo w(x)f(x) dx, where w(x)=x/(exp(2pi x)-1)
 * for x>0 and w(-x)=w(x). For Abel-Plana (sumnumap). */
static GEN
intnumgauexp(void *E, GEN (*eval)(void*,GEN), GEN gN, GEN tab, long prec)
{
  pari_sp av = avma;
  GEN U = mkcomplex(gN, NULL), V = mkcomplex(gN, NULL), S = gen_0;
  GEN vabs = gel(tab, 1), vwt = gel(tab, 2);
  long l = lg(vabs), i;
  if (lg(vwt) != l || typ(vabs) != t_VEC || typ(vwt) != t_VEC)
    pari_err_TYPE("sumnumap", tab);
  for (i = 1; i < l; i++)
  { /* I * (w_i/a_i) * (f(N + I*a_i) - f(N - I*a_i)) */
    GEN x = gel(vabs,i), w = gel(vwt,i), t;
    gel(U,2) = x;
    gel(V,2) = gneg(x);
    t = mulcxI(gsub(eval(E,U), eval(E,V)));
    S = gadd(S, gmul(gdiv(w,x), cxtoreal(t)));
    S = gprec_wensure(S, prec);
  }
  return gerepilecopy(av, gprec_w(S, prec));
}

GEN
sumnumapinit(GEN fast, long prec)
{
  if (!fast) fast = mkoo();
  retmkvec2(intnumgauexpinit(prec), intnuminit(gen_1, fast, 0, prec));
}

typedef struct {
  GEN (*f)(void *E, GEN);
  void *E;
  long N;
} expfn;

/* f(Nx) */
static GEN
_exfn(void *E, GEN x)
{
  expfn *S = (expfn*)E;
  return S->f(S->E, gmulsg(S->N, x));
}

GEN
sumnumap(void *E, GEN (*eval)(void*,GEN), GEN a, GEN tab, long prec)
{
  pari_sp av = avma;
  expfn T;
  GEN S, fast, gN;
  long as, m, N;
  if (!a) { a = gen_1; fast = get_oo(gen_0); }
  else switch(typ(a))
  {
    case t_VEC:
      if (lg(a) != 3) pari_err_TYPE("sumnumap", a);
      fast = get_oo(gel(a,2));
      a = gel(a,1); break;
    default:
      fast = get_oo(gen_0);
  }
  if (typ(a) != t_INT) pari_err_TYPE("sumnumap", a);
  if (!tab) tab = sumnumapinit(fast, prec);
  else if (typ(tab) != t_VEC || lg(tab) != 3) pari_err_TYPE("sumnumap",tab);
  as = itos(a);
  T.N = N = maxss(as + 1, (long)ceil(prec2nbits(prec)*0.327));
  T.E = E;
  T.f = eval;
  gN = stoi(N);
  S = gtofp(gmul2n(eval(E, gN), -1), prec);
  for (m = as; m < N; ++m)
  {
    S = gadd(S, eval(E, stoi(m)));
    S = gprec_wensure(S, prec);
  }
  S = gadd(S, gmulsg(N, intnum(&T, &_exfn, gen_1, fast, gel(tab, 2), prec)));
  S = gadd(S, intnumgauexp(E, eval, gN, gel(tab, 1), prec));
  return gerepileupto(av, S);
}

GEN
sumnumap0(GEN a, GEN code, GEN tab, long prec)
{ EXPR_WRAP(code, sumnumap(EXPR_ARG, a, tab, prec)); }


/* max (1, |zeros|), P a t_POL or scalar */
static GEN
polmax(GEN P)
{
  GEN r;
  if (typ(P) != t_POL || degpol(P) <= 0) return gen_1;
  r = polrootsbound(P, NULL);
  if (gcmpgs(r, 1) <= 0) return gen_1;
  return r;
}

/* max (1, |poles|), F a t_POL or t_RFRAC or scalar */
static GEN
ratpolemax(GEN F)
{
  if (typ(F) == t_POL) return gen_1;
  return polmax(gel(F, 2));
}
/* max (1, |poles|, |zeros|), sets *p = max(1, |poles|)) */
static GEN
ratpolemax2(GEN F, GEN *p)
{
  GEN t;
  if (typ(F) == t_POL) { if (p) *p = gen_1; return polmax(F); }
  t = polmax(gel(F,2)); if (p) *p = t;
  return gmax_shallow(t, polmax(gel(F,1)));
}

static GEN
sercoeff(GEN x, long n)
{
  long N = n - valp(x);
  return (N < 0)? gen_0: gel(x,N+2);
}

/* Compute the integral from N to infinity of a rational function F, deg(F) < -1
 * We must have N > 2 * r, r = max(1, |poles F|). */
static GEN
intnumainfrat(GEN F, long N, double r, long prec)
{
  long B = prec2nbits(prec), v, k, lim;
  GEN S, ser;
  pari_sp av = avma;

  lim = (long)ceil(B/log2(N/r)) + 1;
  ser = gmul(F, real_1(prec + EXTRAPREC));
  ser = rfracrecip_to_ser_absolute(ser, lim);
  v = valp(ser);
  S = gdivgs(sercoeff(ser,lim+1), lim*N);
  /* goes down to 2, but coeffs are 0 in degree < v */
  for (k = lim; k >= v; k--) /* S <- (S + coeff(ser,k)/(k-1)) / N */
    S = gdivgs(gadd(S, gdivgs(sercoeff(ser,k), k-1)), N);
  if (v-2) S = gdiv(S, powuu(N, v-2));
  return gerepilecopy(av, gprec_w(S, prec));
}

static GEN
rfrac_eval0(GEN R)
{
  GEN N, n, D = gel(R,2), d = constant_coeff(D);
  if (gcmp0(d)) return NULL;
  N = gel(R,1);
  n = typ(N)==t_POL? constant_coeff(N): N;
  return gdiv(n, d);
}
static GEN
rfrac_eval(GEN R, GEN a)
{
  GEN D = gel(R,2), d = poleval(D,a);
  return gcmp0(d)? NULL: gdiv(poleval(gel(R,1),a), d);
}
/* R = \sum_i vR[i], eval at a omitting poles */
static GEN
RFRAC_eval(GEN R, GEN vR, GEN a)
{
  GEN S = rfrac_eval(R,a);
  if (!S && vR)
  {
    long i, l = lg(vR);
    for (i = 1; i < l; i++)
    {
      GEN z = rfrac_eval(gel(vR,i), a);
      if (z) S = S? gadd(S,z): z;
    }
  }
  return S;
}
static GEN
add_RFRAC_eval(GEN S, GEN R, GEN vR, GEN a)
{
  GEN z = RFRAC_eval(R, vR, a);
  return z? gadd(S, z): S;
}
static GEN
add_sumrfrac(GEN S, GEN R, GEN vR, long b)
{
  long m;
  for (m = b; m >= 1; m--) S = add_RFRAC_eval(S,R,vR,utoipos(m));
  return S;
}
static void
get_kN(long r, long B, long *pk, long *pN)
{
  long k = maxss(50, (long)ceil(0.241*B));
  GEN z;
  if (k&1L) k++;
  *pk = k;
  z = sqrtnr_abs(gmul2n(gtofp(bernfrac(k), LOWDEFAULTPREC), B), k);
  *pN = maxss(2*r, r + 1 + itos(gceil(z)));
}
/* F a t_RFRAC, F0 = F(0) or NULL [pole], vF a vector of t_RFRAC summing to F
 * or NULL [F atomic] */
static GEN
sumnumrat_i(GEN F, GEN F0, GEN vF, long prec)
{
  long B = prec2nbits(prec), vx, j, k, N;
  GEN S, S1, S2, intf, _1;
  double r;
  if (poldegree(F, -1) > -2) pari_err(e_MISC, "sum diverges in sumnumrat");
  vx = varn(gel(F,2));
  r = gtodouble(ratpolemax(F));
  get_kN((long)ceil(r), B, &k,&N);
  intf = intnumainfrat(F, N, r, prec);
  /* N > ratpolemax(F) is not a pole */
  _1 = real_1(prec);
  S1 = gmul2n(gmul(_1, gsubst(F, vx, utoipos(N))), -1);
  S1 = add_sumrfrac(S1, F, vF, N-1);
  if (F0) S1 = gadd(S1, F0);
  S = gmul(_1, gsubst(F, vx, gaddgs(pol_x(vx), N)));
  S = rfrac_to_ser(S, k + 2);
  S2 = gen_0;
  for (j = 2; j <= k; j += 2)
    S2 = gadd(S2, gmul(gdivgs(bernfrac(j),j), sercoeff(S, j-1)));
  return gadd(intf, gsub(S1, S2));
}
/* sum_{n >= a} F(n) */
GEN
sumnumrat(GEN F, GEN a, long prec)
{
  pari_sp av = avma;
  long vx;
  GEN vF, F0;

  switch(typ(F))
  {
    case t_RFRAC: break;
    case t_INT: case t_REAL: case t_COMPLEX: case t_POL:
      if (gequal0(F)) return real_0(prec);
    default: pari_err_TYPE("sumnumrat",F);
  }
  vx = varn(gel(F,2));
  switch(typ(a))
  {
    case t_INT:
      if (signe(a)) F = gsubst(F, vx, deg1pol_shallow(gen_1,a,vx));
      F0 = rfrac_eval0(F);
      vF = NULL;
      break;
    case t_INFINITY:
      if (inf_get_sign(a) == -1)
      { /* F(x) + F(-x). Could divide degree by 2, as G(x^2): pb with poles */
        GEN F2 = gsubst(F, vx, RgX_neg(pol_x(vx)));
        vF = mkvec2(F,F2);
        F = gadd(F, F2);
        if (gequal0(F)) { avma = av; return real_0(prec); }
        F0 = rfrac_eval0(gel(vF,1));
        break;
      }
    default:
      pari_err_TYPE("sumnumrat",a);
      return NULL; /* LCOV_EXCL_LINE */
  }
  return gerepileupto(av, sumnumrat_i(F, F0, vF, prec));
}
static GEN
_mpmul(GEN x, GEN y)
{
  if (!x) return y;
  return y? mpmul(x, y): x;
}

/* prod_{n >= a} F(n) */
GEN
prodnumrat(GEN F, long a, long prec)
{
  pari_sp ltop = avma;
  long B = prec2nbits(prec), j, k, m, N, vx;
  GEN S, S1, S2, intf, G, F1 = gsubgs(F,1);
  double r;

  switch(typ(F1))
  {
    case t_RFRAC: break;
    case t_INT: case t_REAL: case t_COMPLEX: case t_POL:
      if (gequal0(F1)) return real_1(prec);
    default: pari_err_TYPE("prodnumrat",F);
  }
  if (poldegree(F1,-1) > -2) pari_err(e_MISC, "product diverges in prodnumrat");
  vx = varn(gel(F,2));
  if (a) F = gsubst(F, vx, gaddgs(pol_x(vx), a));
  r = gtodouble(ratpolemax2(F, NULL));
  get_kN((long)ceil(r), B, &k,&N);
  G = gdiv(deriv(F, vx), F);
  intf = intnumainfrat(gmul(pol_x(vx),G), N, r, prec);
  intf = gneg(gadd(intf, gmulsg(N, glog(gsubst(F, vx, stoi(N)), prec))));
  S = gmul(real_1(prec), gsubst(G, vx, gaddgs(pol_x(vx), N)));
  S = rfrac_to_ser(S, k + 2);
  S1 = gsqrt(gsubst(F, vx, utoipos(N)), prec);
  for (m = 0; m < N; m++) S1 = gmul(S1, gsubst(F, vx, utoi(m)));
  S2 = gen_0;
  for (j = 2; j <= k; j += 2)
    S2 = gadd(S2, gmul(gdivgs(bernfrac(j),j*(j-1)), sercoeff(S, j-2)));
  return gerepileupto(ltop, gmul(S1, gexp(gsub(intf, S2), prec)));
}

static GEN
sdmob(GEN ser, long n)
{
  GEN D = divisorsu(n), S = gen_0;
  long i, l = lg(D);
  for (i = 1; i < l; ++i)
  {
    long d = D[i], mob = moebiusu(d);
    if (mob) S = gadd(S, gdivgs(sercoeff(ser, n/d), mob*d));
  }
  return S;
}
static GEN
logzetan(GEN s, GEN P, long prec)
{
  GEN negs = gneg(s), Z = gzeta(gprec_w(s,prec), prec);
  long i, l = lg(P);
  for (i = 1; i < l; i++) Z = gmul(Z, gsubsg(1, gpow(gel(P,i), negs, prec)));
  return glog(Z, prec);
}
static GEN
sumlogzeta(GEN ser, GEN s, long N, long vF, long lim, long prec)
{
  GEN z = gen_0, P = primes_interval(gen_2, utoipos(N));
  long n;
  for (n = lim; n >= vF; n--)
  {
    GEN t = sdmob(ser, n);
    if (!gequal0(t))
    {
      long e = gexpo(t), prec2 = e <= 0? prec: prec + nbits2prec(e);
      z = gadd(z, gmul(logzetan(gmulsg(n,s), P, prec2), t));
      z = gprec_w(z, prec);
    }
  }
  return z;
}

/* sum_{p prime, p >= a} F(p^s), F rational function */
GEN
sumeulerrat(GEN F, GEN s, long a, long prec)
{
  pari_sp av = avma;
  forprime_t T;
  GEN r, ser, res, rsg;
  double rs, RS;
  long B = prec2nbits(prec), vx, vF, p, N, lim;

  switch(typ(F))
  {
    case t_RFRAC: break;
    case t_INT: case t_REAL: case t_COMPLEX: case t_POL:
      if (gequal0(F)) return real_0(prec);
    default: pari_err_TYPE("sumeulerrat",F);
  }
  if (!s) s = gen_1;
  if (a < 2) a = 2;
  vx = varn(gel(F,2));
  vF = -poldegree(F, -1);
  rsg = real_i(s);
  rs = gtodouble(rsg);
  r = ratpolemax(F);
  RS = maxdd(1./vF, dbllog2(r) / log2((double)a));
  if (rs <= RS)
    pari_err_DOMAIN("sumeulerrat", "real(s)", "<=",  dbltor(RS), dbltor(rs));
  N = maxss(maxss(30, a), (long)ceil(2*gtodouble(r)));
  lim = (long)ceil(B / dbllog2(gdiv(gpow(stoi(N), rsg, LOWDEFAULTPREC), r)))+1;
  ser = gmul(real_1(prec + EXTRAPREC), F);
  ser = rfracrecip_to_ser_absolute(ser, lim);
  res = sumlogzeta(ser, s, N, vF, lim, prec);
  u_forprime_init(&T, a, N);
  while ( (p = u_forprime_next(&T)) )
    res = gadd(res, gsubst(F, vx, gpow(utoipos(p), s, prec)));
  return gerepilecopy(av, gprec_w(res, prec));
}

/* prod_{p prime, p >= a} F(p^s), F rational function */
GEN
prodeulerrat(GEN F, GEN s, long a, long prec)
{
  pari_sp ltop = avma;
  forprime_t T;
  GEN F1, r, r1, ser, res, rsg;
  double rs, RS;
  long B = prec2nbits(prec), vx = gvar(F), vF, p, N, lim;

  F1 = gsubgs(F, 1);
  switch(typ(F))
  {
    case t_RFRAC: break;
    case t_INT: case t_REAL: case t_COMPLEX: case t_POL:
      if (gequal0(F1)) return real_1(prec);
    default: pari_err_TYPE("prodeulerrat",F);
  }
  if (!s) s = gen_1;
  vF = -poldegree(F1, -1);
  rsg = real_i(s);
  rs = gtodouble(rsg);
  r = ratpolemax2(F, &r1);
  RS = maxdd(1./vF, dbllog2(r1) / log2((double)a));
  if (rs <= RS)
    pari_err_DOMAIN("prodeulerrat", "real(s)", "<=",  dbltor(RS), dbltor(rs));
  N = maxss(maxss(30, a), (long)ceil(2*gtodouble(r)));
  lim = (long)ceil(B / dbllog2(gdiv(gpow(stoi(N), rsg, LOWDEFAULTPREC), r)))+1;
  ser = gmul(real_1(prec + EXTRAPREC), F1);
  ser = gaddsg(1, rfracrecip_to_ser_absolute(ser, lim));
  ser = glog(ser, 0);
  res = sumlogzeta(ser, s, N, vF, lim, prec);
  res = gexp(res, prec);
  u_forprime_init(&T, a, N);
  while ( (p = u_forprime_next(&T)) )
    res = gmul(res, gsubst(F, vx, gpow(utoipos(p), s, prec)));
  return gerepilecopy(ltop, gprec_w(res, prec));
}

/* Compute $\sum_{n\ge a}c(n)$ using Lagrange extrapolation.
Assume that the $N$-th remainder term of the series has a
regular asymptotic expansion in integral powers of $1/N$. */
static GEN
sumnumlagrange1init(GEN c1, long flag, long prec)
{
  pari_sp av = avma;
  GEN V, W, T;
  double c1d;
  long B = prec2nbits(prec), prec2;
  ulong n, N;
  c1d = c1 ? gtodouble(c1) : 0.332;
  N = (ulong)ceil(c1d*B); if ((N&1L) == 0) N++;
  prec2 = nbits2prec(B+(long)ceil(1.8444*N) + 16);
  W = vecbinome(N);
  T = vecpowuu(N, N);
  V = cgetg(N+1, t_VEC); gel(V,N) = gel(T,N);
  for (n = N-1; n >= 1; n--)
  {
    pari_sp av = avma;
    GEN t = mulii(gel(W, n+1), gel(T,n));
    if (!odd(n)) togglesign_safe(&t);
    if (flag) t = addii(gel(V, n+1), t);
    gel(V, n) = gerepileuptoint(av, t);
  }
  V = gdiv(RgV_gtofp(V, prec2), mpfact(N));
  return gerepilecopy(av, mkvec4(gen_1, stoi(prec2), gen_1, V));
}

static GEN
sumnumlagrange2init(GEN c1, long flag, long prec)
{
  pari_sp av = avma;
  GEN V, W, T, told;
  double c1d = c1 ? gtodouble(c1) : 0.228;
  long B = prec2nbits(prec), prec2;
  ulong n, N;

  N = (ulong)ceil(c1d*B); if ((N&1L) == 0) N++;
  prec2 = nbits2prec(B+(long)ceil(1.18696*N) + 16);
  W = vecbinome(2*N);
  T = vecpowuu(N, 2*N);
  V = cgetg(N+1, t_VEC); gel(V, N) = told = gel(T,N);
  for (n = N-1; n >= 1; n--)
  {
    GEN tnew = mulii(gel(W, N-n+1), gel(T,n));
    if (!odd(n)) togglesign_safe(&tnew);
    told = addii(told, tnew);
    if (flag) told = addii(gel(V, n+1), told);
    gel(V, n) = told; told = tnew;
  }
  V = gdiv(RgV_gtofp(V, prec2), mpfact(2*N));
  return gerepilecopy(av, mkvec4(gen_2, stoi(prec2), gen_1, V));
}

/* Used only for al = 2, 1, 1/2, 1/3, 1/4. */
static GEN
sumnumlagrangeinit_i(GEN al, GEN c1, long flag, long prec)
{
  pari_sp av = avma;
  GEN V, W;
  double c1d = 0.0, c2;
  long B = prec2nbits(prec), B1, prec2, dal;
  ulong j, n, N;

  if (typ(al) == t_INT)
  {
    switch(itos_or_0(al))
    {
      case 1: return sumnumlagrange1init(c1, flag, prec);
      case 2: return sumnumlagrange2init(c1, flag, prec);
      default: pari_err_IMPL("sumnumlagrange for this alpha");
    }
  }
  if (typ(al) != t_FRAC) pari_err_TYPE("sumnumlagrangeinit",al);
  dal = itos_or_0(gel(al,2));
  if (dal > 4 || !equali1(gel(al,1)))
    pari_err_IMPL("sumnumlagrange for this alpha");
  switch(dal)
  {
    case 2: c2 = 2.6441; c1d = 0.62; break;
    case 3: c2 = 3.1578; c1d = 1.18; break;
    case 4: c2 = 3.5364; c1d = 3.00; break;
    default: return NULL; /* LCOV_EXCL_LINE */
  }
  if (c1)
  {
    c1d = gtodouble(c1);
    if (c1d <= 0)
      pari_err_DOMAIN("sumnumlagrangeinit", "c1", "<=", gen_0, c1);
  }
  N = (ulong)ceil(c1d*B); if ((N&1L) == 0) N++;
  B1 = B + (long)ceil(c2*N) + 16;
  prec2 = nbits2prec(B1);
  V = vecpowug(N, al, prec2);
  W = cgetg(N+1, t_VEC);
  for (n = 1; n <= N; ++n)
  {
    pari_sp av2 = avma;
    GEN t = NULL, vn = gel(V, n);
    for (j = 1; j <= N; j++)
      if (j != n) t = _mpmul(t, mpsub(vn, gel(V, j)));
    gel(W, n) = gerepileuptoleaf(av2, mpdiv(gpowgs(vn, N-1), t));
  }
  if (flag)
    for (n = N-1; n >= 1; n--) gel(W, n) = gadd(gel(W, n+1), gel(W, n));
  return gerepilecopy(av, mkvec4(al, stoi(prec2), gen_1, W));
}

GEN
sumnumlagrangeinit(GEN al, GEN c1, long prec)
{
  pari_sp ltop = avma;
  GEN V, W, S, be;
  long n, prec2, fl, N;

  if (!al) return sumnumlagrange1init(c1, 1, prec);
  if (typ(al) != t_VEC) al = mkvec2(gen_1, al);
  else if (lg(al) != 3) pari_err_TYPE("sumnumlagrangeinit",al);
  be = gel(al,2);
  al = gel(al,1);
  if (gequal0(be)) return sumnumlagrangeinit_i(al, c1, 1, prec);
  V = sumnumlagrangeinit_i(al, c1, 0, prec);
  switch(typ(be))
  {
    case t_CLOSURE: fl = 1; break;
    case t_INT: case t_FRAC: case t_REAL: fl = 0; break;
    default: pari_err_TYPE("sumnumlagrangeinit", be);
             return NULL; /* LCOV_EXCL_LINE */
  }
  prec2 = itos(gel(V, 2));
  W = gel(V, 4);
  N = lg(W) - 1;
  S = gen_0; V = cgetg(N+1, t_VEC);
  for (n = N; n >= 1; n--)
  {
    GEN tmp, gn = stoi(n);
    tmp = fl ? closure_callgen1prec(be, gn, prec2) : gpow(gn, gneg(be), prec2);
    tmp = gdiv(gel(W, n), tmp);
    S = gadd(S, tmp);
    gel(V, n) = (n == N)? tmp: gadd(gel(V, n+1), tmp);
  }
  return gerepilecopy(ltop, mkvec4(al, stoi(prec2), S, V));
}

/* - sum_{n=1}^{as-1} f(n) */
static GEN
sumaux(void *E, GEN (*eval)(void*,GEN,long), long as, long prec)
{
  GEN S = gen_0;
  long n;
  if (as > 1)
  {
    for (n = 1; n < as; ++n)
    {
      S = gadd(S, eval(E, stoi(n), prec));
      S = gprec_wensure(S, prec);
    }
    S = gneg(S);
  }
  else
    for (n = as; n <= 0; ++n)
    {
      S = gadd(S, eval(E, stoi(n), prec));
      S = gprec_wensure(S, prec);
    }
  return S;
}

GEN
sumnumlagrange(void *E, GEN (*eval)(void*,GEN,long), GEN a, GEN tab, long prec)
{
  pari_sp av = avma;
  GEN s, S, al, V;
  long as, prec2;
  ulong n, l;

  if (typ(a) != t_INT) pari_err_TYPE("sumnumlagrange", a);
  if (!tab) tab = sumnumlagrangeinit(NULL, tab, prec);
  else if (lg(tab) != 5 || typ(gel(tab,2)) != t_INT || typ(gel(tab,4)) != t_VEC)
    pari_err_TYPE("sumnumlagrange", tab);

  as = itos(a);
  al = gel(tab, 1);
  prec2 = itos(gel(tab, 2));
  S = gel(tab, 3);
  V = gel(tab, 4);
  l = lg(V);
  if (gequal(al, gen_2))
  {
    s = sumaux(E, eval, as, prec2);
    as = 1;
  }
  else
    s = gen_0;
  for (n = 1; n < l; n++)
  {
    s = gadd(s, gmul(gel(V, n), eval(E, stoi(n+as-1), prec2)));
    s = gprec_wensure(s, prec);
  }
  if (!gequal1(S)) s = gdiv(s,S);
  return gerepilecopy(av, gprec_w(s, prec));
}

GEN
sumnumlagrange0(GEN a, GEN code, GEN tab, long prec)
{ EXPR_WRAP(code, sumnumlagrange(EXPR_ARGPREC, a, tab, prec)); }
