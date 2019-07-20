/* Copyright (C) 2000  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/*******************************************************************/
/*                    THE APRCL PRIMALITY TEST                     */
/*******************************************************************/
#include "pari.h"
#include "paripriv.h"

typedef struct Red {
/* global data */
  GEN N; /* prime we are certifying */
  GEN N2; /* floor(N/2) */
/* global data for flexible window */
  long k, lv;
  ulong mask;
/* reduction data */
  long n;
  GEN C; /* polcyclo(n) */
  GEN (*red)(GEN x, struct Red*);
} Red;

#define cache_aall(C)  (gel((C),1))
#define cache_tall(C)  (gel((C),2))
#define cache_cyc(C)  (gel((C),3))
#define cache_E(C)  (gel((C),4))
#define cache_eta(C)  (gel((C),5))
#define cache_matvite(C)  (gel((C),6))
#define cache_matinvvite(C)  (gel((C),7))
#define cache_avite(C)  (gel((C),8))
#define cache_pkvite(C)  (gel((C),9))

static GEN
makepoldeg1(GEN c, GEN d)
{
  GEN z;
  if (signe(c)) {
    z = cgetg(4,t_POL); z[1] = evalsigne(1);
    gel(z,2) = d; gel(z,3) = c;
  } else if (signe(d)) {
    z = cgetg(3,t_POL); z[1] = evalsigne(1);
    gel(z,2) = d;
  } else {
    z = cgetg(2,t_POL); z[1] = evalsigne(0);
  }
  return z;
}

/* T mod polcyclo(p), assume deg(T) < 2p */
static GEN
red_cyclop(GEN T, long p)
{
  long i, d;
  GEN y, z;

  d = degpol(T) - p; /* < p */
  if (d <= -2) return T;

  /* reduce mod (x^p - 1) */
  y = ZX_mod_Xnm1(T, p);
  z = y+2;

  /* reduce mod x^(p-1) + ... + 1 */
  d = p-1;
  if (degpol(y) == d)
    for (i=0; i<d; i++) gel(z,i) = subii(gel(z,i), gel(z,d));
  return normalizepol_lg(y, d+2);
}

/* x t_VECSMALL, as red_cyclo2n_ip */
static GEN
u_red_cyclo2n_ip(GEN x, long n)
{
  long i, pow2 = 1L<<(n-1);
  GEN z;

  for (i = lg(x)-1; i>pow2; i--) x[i-pow2] -= x[i];
  for (; i>0; i--)
    if (x[i]) break;
  i += 2;
  z = cgetg(i, t_POL); z[1] = evalsigne(1);
  for (i--; i>=2; i--) gel(z,i) = stoi(x[i-1]);
  return z;
}
/* x t_POL, n > 0. Return x mod polcyclo(2^n) = (x^(2^(n-1)) + 1). IN PLACE */
static GEN
red_cyclo2n_ip(GEN x, long n)
{
  long i, pow2 = 1L<<(n-1);
  for (i = lg(x)-1; i>pow2+1; i--)
    if (signe(gel(x,i))) gel(x,i-pow2) = subii(gel(x,i-pow2), gel(x,i));
  return normalizepol_lg(x, i+1);
}
static GEN
red_cyclo2n(GEN x, long n) { return red_cyclo2n_ip(leafcopy(x), n); }

/* x a non-zero VECSMALL */
static GEN
smallpolrev(GEN x)
{
  long i,j, lx = lg(x);
  GEN y;

  while (lx-- && x[lx]==0) /* empty */;
  i = lx+2; y = cgetg(i,t_POL);
  y[1] = evalsigne(1);
  for (j=2; j<i; j++) gel(y,j) = stoi(x[j-1]);
  return y;
}

/* x polynomial in t_VECSMALL form, T t_POL return x mod T */
static GEN
u_red(GEN x, GEN T) {
  return RgX_rem(smallpolrev(x), T);
}

/* special case R->C = polcyclo(2^n) */
static GEN
_red_cyclo2n(GEN x, Red *R) {
  return centermod_i(red_cyclo2n(x, R->n), R->N, R->N2);
}
/* special case R->C = polcyclo(p) */
static GEN
_red_cyclop(GEN x, Red *R) {
  return centermod_i(red_cyclop(x, R->n), R->N, R->N2);
}
static GEN
_red(GEN x, Red *R) {
  return centermod_i(grem(x, R->C), R->N, R->N2);
}
static GEN
_redsimple(GEN x, Red *R) { return centermodii(x, R->N, R->N2); }

static GEN
sqrmod(GEN x, Red *R) {
  return R->red(gsqr(x), R);
}

static GEN
sqrconst(GEN pol, Red *R)
{
  GEN z = cgetg(3,t_POL);
  gel(z,2) = centermodii(sqri(gel(pol,2)), R->N, R->N2);
  z[1] = pol[1]; return z;
}

/* pol^2 mod (x^2+x+1, N) */
static GEN
sqrmod3(GEN pol, Red *R)
{
  GEN a,b,bma,A,B;
  long lv = lg(pol);

  if (lv==2) return pol;
  if (lv==3) return sqrconst(pol, R);
  a = gel(pol,3);
  b = gel(pol,2); bma = subii(b,a);
  A = centermodii(mulii(a,addii(b,bma)), R->N, R->N2);
  B = centermodii(mulii(bma,addii(a,b)), R->N, R->N2);
  return makepoldeg1(A,B);
}

/* pol^2 mod (x^2+1,N) */
static GEN
sqrmod4(GEN pol, Red *R)
{
  GEN a,b,A,B;
  long lv = lg(pol);

  if (lv==2) return pol;
  if (lv==3) return sqrconst(pol, R);
  a = gel(pol,3);
  b = gel(pol,2);
  A = centermodii(mulii(a, shifti(b,1)), R->N, R->N2);
  B = centermodii(mulii(subii(b,a),addii(b,a)), R->N, R->N2);
  return makepoldeg1(A,B);
}

/* pol^2 mod (polcyclo(5),N) */
static GEN
sqrmod5(GEN pol, Red *R)
{
  GEN c2,b,c,d,A,B,C,D;
  long lv = lg(pol);

  if (lv==2) return pol;
  if (lv==3) return sqrconst(pol, R);
  c = gel(pol,3); c2 = shifti(c,1);
  d = gel(pol,2);
  if (lv==4)
  {
    A = sqri(d);
    B = mulii(c2, d);
    C = sqri(c);
    A = centermodii(A, R->N, R->N2);
    B = centermodii(B, R->N, R->N2);
    C = centermodii(C, R->N, R->N2); return mkpoln(3,A,B,C);
  }
  b = gel(pol,4);
  if (lv==5)
  {
    A = mulii(b, subii(c2,b));
    B = addii(sqri(c), mulii(b, subii(shifti(d,1),b)));
    C = subii(mulii(c2,d), sqri(b));
    D = mulii(subii(d,b), addii(d,b));
  }
  else
  { /* lv == 6 */
    GEN a = gel(pol,5), a2 = shifti(a,1);
    /* 2a(d - c) + b(2c - b) */
    A = addii(mulii(a2, subii(d,c)), mulii(b, subii(c2,b)));
    /* c(c - 2a) + b(2d - b) */
    B = addii(mulii(c, subii(c,a2)), mulii(b, subii(shifti(d,1),b)));
    /* (a-b)(a+b) + 2c(d - a) */
    C = addii(mulii(subii(a,b),addii(a,b)), mulii(c2,subii(d,a)));
    /* 2a(b - c) + (d-b)(d+b) */
    D = addii(mulii(a2, subii(b,c)), mulii(subii(d,b), addii(d,b)));
  }
  A = centermodii(A, R->N, R->N2);
  B = centermodii(B, R->N, R->N2);
  C = centermodii(C, R->N, R->N2);
  D = centermodii(D, R->N, R->N2); return mkpoln(4,A,B,C,D);
}

static GEN
_mul(GEN x, GEN y, Red *R) { return R->red(gmul(x,y), R); }

/* jac^floor(N/pk) mod (N, polcyclo(pk)), flexible window */
static GEN
_powpolmod(GEN C, GEN jac, Red *R, GEN (*_sqr)(GEN, Red *))
{
  const GEN taba = cache_aall(C);
  const GEN tabt = cache_tall(C);
  const long efin = lg(taba)-1, lv = R->lv;
  GEN L, res = jac, pol2 = _sqr(res, R);
  long f;
  pari_sp av0 = avma, av;

  L = cgetg(lv+1, t_VEC); gel(L,1) = res;
  for (f=2; f<=lv; f++) gel(L,f) = _mul(gel(L,f-1), pol2, R);
  av = avma;
  for (f = efin; f >= 1; f--)
  {
    GEN t = gel(L, taba[f]);
    long tf = tabt[f];
    res = (f==efin)? t: _mul(t, res, R);
    while (tf--) {
      res = _sqr(res, R);
      if (gc_needed(av,1)) {
        res = gerepilecopy(av, res);
        if(DEBUGMEM>1) pari_warn(warnmem,"powpolmod: f = %ld",f);
      }
    }
  }
  return gerepilecopy(av0, res);
}

static GEN
_powpolmodsimple(GEN C, Red *R, GEN jac)
{
  pari_sp av = avma;
  GEN w = ZM_ZX_mul(cache_matvite(C), jac);
  long j, ph = lg(w);

  R->red = &_redsimple;
  for (j=1; j<ph; j++)
    gel(w,j) = _powpolmod(C, centermodii(gel(w,j), R->N, R->N2), R, &sqrmod);
  w = centermod_i( gmul(cache_matinvvite(C), w), R->N, R->N2 );
  w = gerepileupto(av, w);
  return RgV_to_RgX(w, 0);
}

static GEN
powpolmod(GEN C, Red *R, long p, long k, GEN jac)
{
  GEN (*_sqr)(GEN, Red *);

  if (!isintzero(cache_matvite(C))) return _powpolmodsimple(C, R, jac);
  if (p == 2) /* p = 2 */
  {
    if (k == 2) _sqr = &sqrmod4;
    else        _sqr = &sqrmod;
    R->n = k;
    R->red = &_red_cyclo2n;
  } else if (k == 1)
  {
    if      (p == 3) _sqr = &sqrmod3;
    else if (p == 5) _sqr = &sqrmod5;
    else             _sqr = &sqrmod;
    R->n = p;
    R->red = &_red_cyclop;
  } else {
    R->red = &_red; _sqr = &sqrmod;
  }
  return _powpolmod(C, jac, R, _sqr);
}

/* Return e(t) = \prod_{p-1 | t} p^{1+v_p(t)}}
 * faet contains the odd prime divisors of e(t) */
static GEN
compute_e(ulong t, GEN *faet)
{
  GEN L, P, D = divisorsu(t);
  long l = lg(D);
  ulong k;

  P = vecsmalltrunc_init(l);
  L = vecsmalltrunc_init(l);
  for (k=l-1; k>1; k--) /* k != 1: avoid d = 1 */
  {
    ulong d = D[k];
    if (uisprime(++d))
    { /* we want q = 1 (mod p) prime, not too large */
#ifdef LONG_IS_64BIT
      if (d > 5000000000UL) return gen_0;
#endif
      vecsmalltrunc_append(P, d);
      vecsmalltrunc_append(L, upowuu(d, 1 + u_lval(t,d)));
    }
  }
  if (faet) *faet = P;
  return shifti(zv_prod_Z(L), 2 + u_lval(t,2));
}

/* Table obtained by the following script:

install(compute_e, "LD&"); \\ remove 'static' first
table(first = 6, step = 6, MAXT = 6983776800)=
{
  emax = 0;
  forstep(t = first, MAXT, step,
    e = compute_e(t);
    if (e > 1.9*emax, emax = e;
      printf("  if (C < %7.2f) return %8d;\n", 2*log(e)/log(2) - 1e-2, t)
    );
  );
}
table(,, 147026880);
table(147026880,5040, 6983776800);
*/

/* assume C < 20003.8 */
static ulong
compute_t_small(double C)
{
  if (C <   17.94) return        6;
  if (C <   31.99) return       12;
  if (C <   33.99) return       24;
  if (C <   54.07) return       36;
  if (C <   65.32) return       60;
  if (C <   68.45) return       72;
  if (C <   70.78) return      108;
  if (C <   78.04) return      120;
  if (C <  102.41) return      180;
  if (C <  127.50) return      360;
  if (C <  136.68) return      420;
  if (C <  153.44) return      540;
  if (C <  165.67) return      840;
  if (C <  169.18) return     1008;
  if (C <  178.53) return     1080;
  if (C <  192.69) return     1200;
  if (C <  206.35) return     1260;
  if (C <  211.96) return     1620;
  if (C <  222.10) return     1680;
  if (C <  225.12) return     2016;
  if (C <  244.20) return     2160;
  if (C <  270.31) return     2520;
  if (C <  279.52) return     3360;
  if (C <  293.64) return     3780;
  if (C <  346.70) return     5040;
  if (C <  348.73) return     6480;
  if (C <  383.37) return     7560;
  if (C <  396.71) return     8400;
  if (C <  426.08) return    10080;
  if (C <  458.38) return    12600;
  if (C <  527.20) return    15120;
  if (C <  595.43) return    25200;
  if (C <  636.34) return    30240;
  if (C <  672.58) return    42840;
  if (C <  684.96) return    45360;
  if (C <  708.84) return    55440;
  if (C <  771.37) return    60480;
  if (C <  775.93) return    75600;
  if (C <  859.69) return    85680;
  if (C <  893.24) return   100800;
  if (C <  912.35) return   110880;
  if (C <  966.22) return   128520;
  if (C < 1009.18) return   131040;
  if (C < 1042.04) return   166320;
  if (C < 1124.98) return   196560;
  if (C < 1251.09) return   257040;
  if (C < 1375.13) return   332640;
  if (C < 1431.11) return   393120;
  if (C < 1483.46) return   514080;
  if (C < 1546.46) return   655200;
  if (C < 1585.94) return   665280;
  if (C < 1661.44) return   786240;
  if (C < 1667.67) return   831600;
  if (C < 1677.07) return   917280;
  if (C < 1728.17) return   982800;
  if (C < 1747.57) return  1081080;
  if (C < 1773.76) return  1179360;
  if (C < 1810.81) return  1285200;
  if (C < 1924.66) return  1310400;
  if (C < 2001.27) return  1441440;
  if (C < 2096.51) return  1663200;
  if (C < 2166.02) return  1965600;
  if (C < 2321.86) return  2162160;
  if (C < 2368.45) return  2751840;
  if (C < 2377.39) return  2827440;
  if (C < 2514.97) return  3326400;
  if (C < 2588.72) return  3341520;
  if (C < 2636.84) return  3603600;
  if (C < 2667.46) return  3931200;
  if (C < 3028.92) return  4324320;
  if (C < 3045.76) return  5654880;
  if (C < 3080.78) return  6652800;
  if (C < 3121.88) return  6683040;
  if (C < 3283.38) return  7207200;
  if (C < 3514.94) return  8648640;
  if (C < 3725.71) return 10810800;
  if (C < 3817.49) return 12972960;
  if (C < 3976.57) return 14414400;
  if (C < 3980.72) return 18378360;
  if (C < 4761.70) return 21621600;
  if (C < 5067.62) return 36756720;
  if (C < 5657.30) return 43243200;
  if (C < 5959.24) return 64864800;
  if (C < 6423.60) return 73513440;
  if (C < 6497.01) return 86486400;
  if (C < 6529.89) return 113097600;
  if (C < 6899.19) return 122522400;
  if (C < 7094.26) return 129729600;
  if (C < 7494.60) return 147026880;
  if (C < 7606.21) return 172972800;
  if (C < 7785.10) return 183783600;
  if (C < 7803.68) return 216216000;
  if (C < 8024.18) return 220540320;
  if (C < 8278.12) return 245044800;
  if (C < 8316.48) return 273873600;
  if (C < 8544.02) return 294053760;
  if (C < 8634.14) return 302702400;
  if (C < 9977.69) return 367567200;
  if (C < 10053.06) return 514594080;
  if (C < 10184.29) return 551350800;
  if (C < 11798.33) return 735134400;
  if (C < 11812.60) return 821620800;
  if (C < 11935.31) return 1029188160;
  if (C < 12017.99) return 1074427200;
  if (C < 12723.99) return 1102701600;
  if (C < 13702.71) return 1470268800;
  if (C < 13748.76) return 1643241600;
  if (C < 13977.37) return 2058376320;
  if (C < 14096.03) return 2148854400UL;
  if (C < 15082.25) return 2205403200UL;
  if (C < 15344.18) return 2572970400UL;
  if (C < 15718.37) return 2940537600UL;
  if (C < 15868.65) return 3491888400UL;
  if (C < 15919.88) return 3675672000UL;
  if (C < 16217.23) return 4108104000UL;
#ifdef LONG_IS_64BIT
  if (C < 17510.32) return 4410806400UL;
  if (C < 18312.87) return 5145940800UL;
  return 6983776800UL;
#else
  pari_err_IMPL("APRCL for large numbers on 32bit arch");
  return 0;
#endif
}

/* return t such that e(t) > sqrt(N), set *faet = odd prime divisors of e(t) */
static ulong
compute_t(GEN N, GEN *e, GEN *faet)
{ /* 2^e b <= N < 2^e (b+1), where b >= 2^52. Approximating log_2 N by
   * log2(gtodouble(N)) ~ e+log2(b), the error is less than log(1+1/b) < 1e-15*/
  double C = dbllog2(N) + 1e-10; /* > log_2 N at least for N < 2^(2^21) */
  ulong t;
  /* Return "smallest" t such that f(t) >= C, which implies e(t) > sqrt(N) */
  /* For N < 2^20003.8 ~ 5.5 10^6021 */
  if (C < 20003.8)
  {
    t = compute_t_small(C);
    *e = compute_e(t, faet);
  }
  else
  {
#ifdef LONG_IS_64BIT
    GEN B = sqrti(N);
    for (t = 6983776800UL+5040UL;; t+=5040)
    {
      pari_sp av = avma;
      *e = compute_e(t, faet);
      if (cmpii(*e, B) > 0) break;
      avma = av;
    }
#else
    *e = NULL; /* LCOV_EXCL_LINE */
    t = 0; /* LCOV_EXCL_LINE */
#endif
  }
  return t;
}

/* T[i] = discrete log of i in (Z/q)^*, q odd prime
 * To save on memory, compute half the table: T[q-x] = T[x] + (q-1)/2 */
static GEN
computetabdl(ulong q)
{
  ulong g, a, i, qs2 = q>>1; /* (q-1)/2 */
  GEN T = cgetg(qs2+2,t_VECSMALL);

  g = pgener_Fl(q); a = 1;
  for (i=1; i < qs2; i++) /* g^((q-1)/2) = -1 */
  {
    a = Fl_mul(g,a,q);
    if (a > qs2) T[q-a] = i+qs2; else T[a] = i;
  }
  T[qs2+1] = T[qs2] + qs2;
  T[1] = 0; return T;
}

/* Return T: T[x] = dl of x(1-x) */
static GEN
compute_g(ulong q)
{
  const ulong qs2 = q>>1; /* (q-1)/2 */
  ulong x, a;
  GEN T = computetabdl(q); /* updated in place to save on memory */
  a = 0; /* dl[1] */
  for (x=2; x<=qs2+1; x++)
  { /* a = dl(x) */
    ulong b = T[x]; /* = dl(x) */
    T[x] = b + a + qs2; /* dl(x) + dl(x-1) + dl(-1) */
    a = b;
  }
  return T;
}

/* p odd prime */
static GEN
get_jac(GEN C, ulong q, long pk, GEN tabg)
{
  ulong x, qs2 = q>>1; /* (q-1)/2 */
  GEN vpk = zero_zv(pk);

  for (x=2; x<=qs2; x++) vpk[ tabg[x]%pk + 1 ] += 2;
  vpk[ tabg[x]%pk + 1 ]++; /* x = (q+1)/2 */
  return u_red(vpk, cache_cyc(C));
}

/* p = 2 */
static GEN
get_jac2(GEN N, ulong q, long k, GEN *j2q, GEN *j3q)
{
  GEN jpq, vpk, T = computetabdl(q);
  ulong x, pk, i, qs2;

  /* could store T[x+1] + T[x] + qs2 (cf compute_g).
   * Recompute instead, saving half the memory. */
  pk = 1UL << k;;
  vpk = zero_zv(pk);

  qs2 = q>>1; /* (q-1)/2 */

  for (x=2; x<=qs2; x++) vpk[ (T[x]+T[x-1]+qs2)%pk + 1 ] += 2;
  vpk[ (T[x]+T[x-1]+qs2)%pk + 1 ]++;
  jpq = u_red_cyclo2n_ip(vpk, k);

  if (k == 2) return jpq;

  if (mod8(N) >= 5)
  {
    GEN v8 = cgetg(9,t_VECSMALL);
    for (x=1; x<=8; x++) v8[x] = 0;
    for (x=2; x<=qs2; x++) v8[ ((3*T[x]+T[x-1]+qs2)&7) + 1 ]++;
    for (   ; x<=q-1; x++) v8[ ((3*T[q-x]+T[q-x+1]-3*qs2)&7) + 1 ]++;
    *j2q = RgX_inflate(ZX_sqr(u_red_cyclo2n_ip(v8,3)), pk>>3);
    *j2q = red_cyclo2n_ip(*j2q, k);
  }
  for (i=1; i<=pk; i++) vpk[i] = 0;
  for (x=2; x<=qs2; x++) vpk[ (2*T[x]+T[x-1]+qs2)%pk + 1 ]++;
  for (   ; x<=q-1; x++) vpk[ (2*T[q-x]+T[q-x+1]-2*qs2)%pk + 1 ]++;
  *j3q = ZX_mul(jpq, u_red_cyclo2n_ip(vpk,k));
  *j3q = red_cyclo2n_ip(*j3q, k);
  return jpq;
}

/* N = 1 mod p^k, return an elt of order p^k in (Z/N)^* */
static GEN
finda(GEN Cp, GEN N, long pk, long p)
{
  GEN a, pv;
  if (Cp && !isintzero(cache_avite(Cp))) {
    a  = cache_avite(Cp);
    pv = cache_pkvite(Cp);
  }
  else
  {
    GEN ph, b, q;
    ulong u = 2;
    long v = Z_lvalrem(subiu(N,1), p, &q);
    ph = powuu(p, v-1); pv = muliu(ph, p); /* N - 1 = p^v q */
    if (p > 2)
    {
      for (;;u++)
      {
        a = Fp_pow(utoipos(u), q, N);
        b = Fp_pow(a, ph, N);
        if (!gequal1(b)) break;
      }
    }
    else
    {
      while (krosi(u,N) >= 0) u++;
      a = Fp_pow(utoipos(u), q, N);
      b = Fp_pow(a, ph, N);
    }
    /* checking b^p = 1 mod N done economically in caller */
    b = gcdii(subiu(b,1), N);
    if (!gequal1(b)) return NULL;

    if (Cp) {
      cache_avite(Cp)  = a; /* a has order p^v */
      cache_pkvite(Cp) = pv;
    }
  }
  return Fp_pow(a, divis(pv, pk), N);
}

/* return 0: N not a prime, 1: no problem so far */
static long
filltabs(GEN C, GEN Cp, Red *R, long p, long pk, long ltab)
{
  pari_sp av;
  long i, j;
  long e;
  GEN tabt, taba, m;

  cache_cyc(C) = polcyclo(pk,0);

  if (p > 2)
  {
    long LE = pk - pk/p + 1;
    GEN E = cgetg(LE, t_VECSMALL), eta = cgetg(pk+1,t_VEC);
    for (i=1,j=0; i<pk; i++)
      if (i%p) E[++j] = i;
    cache_E(C) = E;

    for (i=1; i<=pk; i++)
    {
      GEN z = FpX_rem(pol_xn(i-1, 0), cache_cyc(C), R->N);
      gel(eta,i) = FpX_center_i(z, R->N, R->N2);
    }
    cache_eta(C) = eta;
  }
  else if (pk >= 8)
  {
    long LE = (pk>>2) + 1;
    GEN E = cgetg(LE, t_VECSMALL);
    for (i=1,j=0; i<pk; i++)
      if ((i%8)==1 || (i%8)==3) E[++j] = i;
    cache_E(C) = E;
  }

  if (pk > 2 && umodiu(R->N,pk) == 1)
  {
    GEN vpa, p1, p2, p3, a2 = NULL, a = finda(Cp, R->N, pk, p);
    long jj, ph;

    if (!a) return 0;
    ph = pk - pk/p;
    vpa = cgetg(ph+1,t_COL); gel(vpa,1) = a;
    if (pk > p) a2 = centermodii(sqri(a), R->N, R->N2);
    jj = 1;
    for (i=2; i<pk; i++) /* vpa = { a^i, (i,p) = 1 } */
      if (i%p) {
        GEN z = mulii((i%p==1) ? a2 : a, gel(vpa,jj));
        gel(vpa,++jj) = centermodii(z , R->N, R->N2);
      }
    if (!gequal1( centermodii( mulii(a, gel(vpa,ph)), R->N, R->N2) )) return 0;
    p1 = cgetg(ph+1,t_MAT);
    p2 = cgetg(ph+1,t_COL); gel(p1,1) = p2;
    for (i=1; i<=ph; i++) gel(p2,i) = gen_1;
    j = 2; gel(p1,j) = vpa; p3 = vpa;
    for (j++; j <= ph; j++)
    {
      p2 = cgetg(ph+1,t_COL); gel(p1,j) = p2;
      for (i=1; i<=ph; i++)
        gel(p2,i) = centermodii(mulii(gel(vpa,i),gel(p3,i)), R->N, R->N2);
      p3 = p2;
    }
    cache_matvite(C) = p1;
    cache_matinvvite(C) = FpM_inv(p1, R->N);
  }

  tabt = cgetg(ltab+1, t_VECSMALL);
  taba = cgetg(ltab+1, t_VECSMALL);
  av = avma; m = divis(R->N, pk);
  for (e=1; e<=ltab && signe(m); e++)
  {
    long s = vali(m); m = shifti(m,-s);
    tabt[e] = e==1? s: s + R->k;
    taba[e] = signe(m)? ((mod2BIL(m) & R->mask)+1)>>1: 0;
    m = shifti(m, -R->k);
  }
  setlg(taba, e); cache_aall(C) = taba;
  setlg(tabt, e); cache_tall(C) = tabt;
  avma = av; return 1;
}

static GEN
calcglobs(Red *R, ulong t, long *plpC, long *pltab, GEN *pP)
{
  GEN fat, P, E, PE;
  long lv, i, k, b;
  GEN pC;

  b = expi(R->N)+1;
  k = 3; while (((k+1)*(k+2) << (k-1)) < b) k++;
  *pltab = (b/k)+2;
  R->k  = k;
  R->lv = 1L << (k-1);
  R->mask = (1UL << k) - 1;

  fat = factoru_pow(t);
  P = gel(fat,1);
  E = gel(fat,2);
  PE= gel(fat,3);
  *plpC = lv = vecsmall_max(PE); /* max(p^e, p^e | t) */
  pC = zerovec(lv);
  gel(pC,1) = zerovec(9); /* to be used as temp in step5() */
  for (i = 2; i <= lv; i++) gel(pC,i) = gen_0;
  for (i=1; i<lg(P); i++)
  {
    long pk, p = P[i], e = E[i];
    pk = p;
    for (k=1; k<=e; k++, pk*=p)
    {
      gel(pC,pk) = zerovec(9);
      if (!filltabs(gel(pC,pk), gel(pC,p), R, p,pk, *pltab)) return NULL;
    }
  }
  *pP = P; return pC;
}

/* sig_a^{-1}(z) for z in Q(zeta_pk) and sig_a: zeta -> zeta^a. Assume
 * a reduced mod pk := p^k*/
static GEN
aut(long pk, GEN z, long a)
{
  GEN v;
  long b, i, dz = degpol(z);
  if (a == 1 || dz < 0) return z;
  v = cgetg(pk+2,t_POL);
  v[1] = evalvarn(0);
  b = 0;
  gel(v,2) = gel(z,2); /* i = 0 */
  for (i = 1; i < pk; i++)
  {
    b += a; if (b > pk) b -= pk; /* b = (a*i) % pk */
    gel(v,i+2) = b > dz? gen_0: gel(z,b+2);
  }
  return normalizepol_lg(v, pk+2);
}

/* z^v for v in Z[G], represented by couples [sig_x^{-1},x] */
static GEN
autvec_TH(long pk, GEN z, GEN v, GEN C)
{
  long i, lv = lg(v);
  GEN s = pol_1(varn(C));
  for (i=1; i<lv; i++)
  {
    long y = v[i];
    if (y) s = RgXQ_mul(s, RgXQ_powu(aut(pk,z, y), y, C), C);
  }
  return s;
}

static GEN
autvec_AL(long pk, GEN z, GEN v, Red *R)
{
  const long r = umodiu(R->N, pk);
  GEN s = pol_1(varn(R->C));
  long i, lv = lg(v);
  for (i=1; i<lv; i++)
  {
    long y = (r*v[i]) / pk;
    if (y) s = RgXQ_mul(s, RgXQ_powu(aut(pk,z, v[i]), y, R->C), R->C);
  }
  return s;
}

/* 0 <= i < pk, such that x^i = z mod polcyclo(pk),  -1 if no such i exist */
static long
look_eta(GEN eta, long pk, GEN z)
{
  long i;
  for (i=1; i<=pk; i++)
    if (ZX_equal(z, gel(eta,i))) return i-1;
  return -1;
}
/* same pk = 2^k */
static long
look_eta2(long k, GEN z)
{
  long d, s;
  if (typ(z) != t_POL) d = 0; /* t_INT */
  else
  {
    if (!RgX_is_monomial(z)) return -1;
    d = degpol(z);
    z = gel(z,d+2); /* leading term */
  }
  s = signe(z);
  if (!s || !is_pm1(z)) return -1;
  return (s > 0)? d: d + (1L<<(k-1));
}

static long
step4a(GEN C, Red *R, ulong q, long p, long k, GEN tabg)
{
  const long pk = upowuu(p,k);
  long ind;
  GEN jpq, s1, s2, s3;

  if (!tabg) tabg = compute_g(q);
  jpq = get_jac(C, q, pk, tabg);
  s1 = autvec_TH(pk, jpq, cache_E(C), cache_cyc(C));
  s2 = powpolmod(C,R, p,k, s1);
  s3 = autvec_AL(pk, jpq, cache_E(C), R);
  s3 = _red(gmul(s3,s2), R);

  ind = look_eta(cache_eta(C), pk, s3);
  if (ind < 0) return -1;
  return (ind%p) != 0;
}

/* x == -1 mod N ? */
static long
is_m1(GEN x, GEN N)
{
  return equalii(addiu(x,1), N);
}

/* p=2, k>=3 */
static long
step4b(GEN C, Red *R, ulong q, long k)
{
  const long pk = 1L << k;
  long ind;
  GEN s1, s2, s3, j2q = NULL, j3q = NULL;

  (void)get_jac2(R->N,q,k, &j2q,&j3q);

  s1 = autvec_TH(pk, j3q, cache_E(C), cache_cyc(C));
  s2 = powpolmod(C,R, 2,k, s1);
  s3 = autvec_AL(pk, j3q, cache_E(C), R);
  s3 = _red(gmul(s3,s2), R);
  if (j2q) s3 = _red(gmul(j2q, s3), R);

  ind = look_eta2(k, s3);
  if (ind < 0) return -1;
  if ((ind&1)==0) return 0;
  s3 = Fp_pow(utoipos(q), R->N2, R->N);
  return is_m1(s3, R->N);
}

/* p=2, k=2 */
static long
step4c(GEN C, Red *R, ulong q)
{
  long ind;
  GEN s0,s1,s3, jpq = get_jac2(R->N,q,2, NULL,NULL);

  s0 = sqrmod4(jpq, R);
  s1 = gmulsg(q,s0);
  s3 = powpolmod(C,R, 2,2, s1);
  if (mod4(R->N) == 3) s3 = _red(gmul(s0,s3), R);

  ind = look_eta2(2, s3);
  if (ind < 0) return -1;
  if ((ind&1)==0) return 0;
  s3 = Fp_pow(utoipos(q), R->N2, R->N);
  return is_m1(s3, R->N);
}

/* p=2, k=1 */
static long
step4d(Red *R, ulong q)
{
  GEN s1 = Fp_pow(utoipos(q), R->N2, R->N);
  if (is_pm1(s1)) return 0;
  if (is_m1(s1, R->N)) return (mod4(R->N) == 1);
  return -1;
}

static GEN
_res(long a, long b) { return b? mkvec2s(a, b): mkvecs(a); }

/* return 1 [OK so far] or <= 0 [not a prime] */
static GEN
step5(GEN pC, Red *R, long p, GEN et, ulong ltab, long lpC)
{
  pari_sp av;
  ulong q;
  long pk, k, fl = -1;
  GEN C, Cp;
  forprime_t T;

  (void)u_forprime_arith_init(&T, 3, ULONG_MAX, 1,p);
  while( (q = u_forprime_next(&T)) )
  { /* q = 1 (mod p) */
    if (umodiu(et,q) == 0) continue;
    if (umodiu(R->N,q) == 0) return _res(1,p);
    k = u_lval(q-1, p);
    pk = upowuu(p,k);
    if (pk <= lpC && !isintzero(gel(pC,pk))) {
      C = gel(pC,pk);
      Cp = gel(pC,p);
    } else {
      C = gel(pC,1);
      Cp = NULL;
      cache_matvite(C) = gen_0; /* re-init */
    }

    av = avma;
    if (!filltabs(C, Cp, R, p, pk, ltab)) return _res(1,0);
    R->C = cache_cyc(C);
    if (p >= 3)      fl = step4a(C,R, q,p,k, NULL);
    else if (k >= 3) fl = step4b(C,R, q,k);
    else if (k == 2) fl = step4c(C,R, q);
    else             fl = step4d(R, q);
    if (fl == -1) return _res(q,p);
    if (fl == 1) return NULL; /*OK*/
    avma = av;
  }
  pari_err_BUG("aprcl test fails! This is highly improbable");
  return NULL;
}

GEN
aprcl_step6_worker(GEN r, long t, GEN N, GEN N1, GEN et)
{
  long i;
  pari_sp av = avma;
  for (i=1; i<=t; i++)
  {
    r = remii(mulii(r,N1), et);
    if (equali1(r)) break;
    if (dvdii(N,r) && !equalii(r,N)) return mkvec2(r, gen_0);
    if ((i & 0x1f) == 0) r = gerepileuptoint(av, r);
  }
  return gen_0;
}

static GEN
step6(GEN N, ulong t, GEN et)
{
  GEN r, rk, N1 = remii(N, et);
  ulong k = 10000;
  ulong i;
  GEN worker, res = NULL;
  long pending = 0;
  struct pari_mt pt;
  pari_sp btop;
  worker = strtoclosure("_aprcl_step6_worker", 3, N, N1, et);
  r = gen_1;
  rk = Fp_powu(N1, k, et);
  mt_queue_start_lim(&pt, worker, (t-1+k-1)/k);
  btop = avma;
  for (i=1; (i<t && !res) || pending; i+=k)
  {
    GEN done;
    mt_queue_submit(&pt, i, (i<t && !res) ? mkvec2(r, utoi(minss(k,t-i))): NULL);
    done = mt_queue_get(&pt, NULL, &pending);
    if (done && !isintzero(done)) res = done;
    r = Fp_mul(r, rk, et);
    if (gc_needed(btop, 2))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"APRCL: i = %ld",i);
      r = gerepileupto(btop, r);
    }
  }
  mt_queue_end(&pt);
  if (res) return res;
  return gen_1;
}

GEN
aprcl_step4_worker(ulong q, GEN pC, GEN N, GEN v)
{
  pari_sp av1 = avma, av2 = avma;
  long j, k;
  Red R;
  GEN faq = factoru_pow(q-1), tabg = compute_g(q);
  GEN P = gel(faq,1), E = gel(faq,2), PE = gel(faq,3);
  long lfaq = lg(P);
  GEN flags = cgetg(lfaq, t_VECSMALL);
  R.N = N;
  R.N2= shifti(N, -1);
  R.k = v[1]; R.lv = v[2]; R.mask = uel(v,3); R.n = v[4];
  av2 = avma;
  for (j=1, k=1; j<lfaq; j++, avma = av2)
  {
    long p = P[j], e = E[j], pe = PE[j], fl;
    GEN C = gel(pC,pe);
    R.C = cache_cyc(C);
    if (p >= 3)      fl = step4a(C,&R, q,p,e, tabg);
    else if (e >= 3) fl = step4b(C,&R, q,e);
    else if (e == 2) fl = step4c(C,&R, q);
    else             fl = step4d(&R, q);
    if (fl == -1) return _res(q,p);
    if (fl == 1)  flags[k++] = p;
  }
  setlg(flags, k);
  return gerepileuptoleaf(av1, flags);
}

static GEN
aprcl(GEN N)
{
  GEN et, fat, flaglp, faet = NULL; /*-Wall*/
  long i, j, l, ltab, lfat, lpC;
  ulong t;
  Red R;
  GEN pC;
  GEN worker, res = NULL;
  long pending = 0, workid;
  struct pari_mt pt;

  if (typ(N) != t_INT) pari_err_TYPE("aprcl",N);
  if (cmpis(N,12) <= 0)
    switch(itos(N))
    {
      case 2: case 3: case 5: case 7: case 11: return gen_1;
      default: return _res(0,0);
    }
  if (Z_issquare(N)) return _res(0,0);
  t = compute_t(N, &et, &faet);
  if (DEBUGLEVEL) err_printf("Starting APRCL with t = %ld\n",t);
  if (cmpii(sqri(et),N) < 0) pari_err_BUG("aprcl: e(t) too small");
  if (!equali1(gcdii(N,mului(t,et)))) return _res(1,0);

  R.N = N;
  R.N2= shifti(N, -1);
  pC = calcglobs(&R, t, &lpC, &ltab, &fat);
  if (!pC) return _res(1,0);
  lfat = lg(fat);
  flaglp = cgetg(lfat, t_VECSMALL);
  flaglp[1] = 0;
  for (i=2; i<lfat; i++)
  {
    ulong p = fat[i];
    flaglp[i] = absequaliu(Fp_powu(N, p-1, sqru(p)), 1);
  }
  vecsmall_sort(faet);
  l = lg(faet);
  worker = strtoclosure("_aprcl_step4_worker", 3,
                        pC, N, mkvecsmall4(R.k, R.lv, R.mask, R.n));
  if (DEBUGLEVEL>2) err_printf("Step4: %ld q-values\n", l-1);
  mt_queue_start_lim(&pt, worker, l-1);
  for (i=l-1; (i>0 && !res) || pending; i--)
  {
    GEN done;
    ulong q = i>0 ? faet[i]: 0;
    mt_queue_submit(&pt, q, q>0? mkvec(utoi(q)): NULL);
    done = mt_queue_get(&pt, &workid, &pending);
    if (done)
    {
      long lf = lg(done);
      if (typ(done) == t_VEC) res = done;
      for (j=1; j<lf; j++) flaglp[ zv_search(fat, done[j]) ] = 0;
      if (DEBUGLEVEL>2) err_printf("testing Jacobi sums for q = %ld...OK\n", workid);
    }
  }
  mt_queue_end(&pt);
  if (res) return res;
  if (DEBUGLEVEL>2) err_printf("Step5: testing conditions lp\n");
  for (i=2; i<lfat; i++) /*skip fat[1] = 2*/
  {
    pari_sp av = avma;
    long p = fat[i];
    GEN r;
    if (flaglp[i] && (r = step5(pC, &R, p, et, ltab, lpC))) return r;
    avma = av;
  }
  if (DEBUGLEVEL>2)
    err_printf("Step6: testing potential divisors\n");
  return step6(N, t, et);
}

long
isprimeAPRCL(GEN N)
{
  pari_sp av = avma;
  GEN res = aprcl(N);
  avma = av; return (typ(res) == t_INT);
}

/*******************************************************************/
/*              DIVISORS IN RESIDUE CLASSES (LENSTRA)              */
/*******************************************************************/
/* This would allow to replace e(t) > N^(1/2) by e(t) > N^(1/3), but step6
 * becomes so expensive that, at least up to 6000 bits, this is useless
 * in this application. */
static void
set_add(hashtable *H, void *d)
{
  ulong h = H->hash(d);
  if (!hash_search2(H, d, h)) hash_insert2(H, d, NULL, h);
}
static GEN
GEN_hash_keys(hashtable *H)
{ GEN v = hash_keys(H); settyp(v, t_VEC); return ZV_sort(v); }
static void
add(hashtable *H, GEN t1, GEN t2, GEN a, GEN b, GEN r, GEN s)
{
  GEN ra, qa = dvmdii(t1, a, &ra);
  if (!signe(ra) && dvdii(t2, b) && equalii(modii(qa, s), r))
    set_add(H, (void*)qa);
}
/* T^2 - B*T + C has integer roots ? */
static void
check_t(hashtable *H, GEN B, GEN C4, GEN a, GEN b, GEN r, GEN s)
{
  GEN d, t1, t2, D = subii(sqri(B), C4);
  if (!Z_issquareall(D, &d)) return;
  t1 = shifti(addii(B, d), -1); /* >= 0 */
  t2 = subii(B, t1);
  add(H, t1,t2, a,b,r,s);
  if (signe(t2) >= 0) add(H, t2,t1, a,b,r,s);
}
/* N > s > r >= 0, (r,s) = 1 */
GEN
divisorslenstra(GEN N, GEN r, GEN s)
{
  pari_sp av = avma;
  GEN u, Ns2, rp, a0, a1, b0, b1, c0, c1, s2;
  hashtable *H = hash_create(11, (ulong(*)(void*))&hash_GEN,
                                 (int(*)(void*,void*))&equalii, 1);
  long j;
  if (typ(N) != t_INT) pari_err_TYPE("divisorslenstra", N);
  if (typ(r) != t_INT) pari_err_TYPE("divisorslenstra", r);
  if (typ(s) != t_INT) pari_err_TYPE("divisorslenstra", s);
  u = Fp_inv(r, s);
  rp = Fp_mul(u, N, s); /* r' */
  s2 = sqri(s);
  a0 = s;
  b0 = gen_0;
  c0 = gen_0;
  if (dvdii(N, r)) set_add(H, (void*)r); /* case i = 0 */
  a1 = Fp_mul(u, rp, s); if (!signe(a1)) a1 = s; /* 0 < a1 <= s */
  b1 = gen_1;
  c1 = Fp_mul(u, diviiexact(subii(N,mulii(r,rp)), s), s);
  Ns2 = divii(N, s2);
  j = 1;
  for (;;)
  {
    GEN Cs, q, c, ab = mulii(a1,b1);
    long i, lC;
    if (j == 0) /* i even, a1 >= 0 */
    {
      if (!signe(c1)) Cs = mkvec(gen_0);
      else
      {
        GEN cs = mulii(c1, s);
        Cs = mkvec2(subii(cs,s2), cs);
      }
    }
    else
    { /* i odd, a1 > 0 */
      GEN X = shifti(ab,1);
      c = c1;
      /* smallest c >= 2ab, c = c1 (mod s) */
      if (cmpii(c, X) < 0)
      {
        GEN rX, qX = dvmdii(subii(X,c), s, &rX);
        if (signe(rX)) qX = addiu(qX,1); /* ceil((X-c)/s) */
        c = addii(c, mulii(s, qX));
      }
      Cs = (cmpii(c, addii(Ns2,ab)) <= 0)? mkvec(mulii(c,s)): cgetg(1,t_VEC);
    }
    lC = lg(Cs);
    if (signe(a1))
    {
      GEN abN4 = shifti(mulii(ab, N), 2);
      GEN B = addii(mulii(a1,r), mulii(b1,rp));
      for (i = 1; i < lC; i++)
        check_t(H, addii(B, gel(Cs,i)), abN4, a1, b1, r, s);
    }
    else
    { /* a1 = 0, last batch */
      for (i = 1; i < lC; i++)
      {
        GEN ry, ys = dvmdii(gel(Cs,i), b1, &ry);
        if (!signe(ry))
        {
          GEN d = addii(ys, rp);
          if (signe(d) > 0)
          {
            d = dvmdii(N, d, &ry);
            if (!signe(ry)) set_add(H, (void*)d);
          }
        }
      }
      break; /* DONE */
    }
    j = 1-j;
    q = dvmdii(a0, a1, &c);
    if (j == 1 && !signe(c)) { q = subiu(q,1); c = a1; }
    a0 = a1; a1 = c;
    if (equali1(q)) /* frequent */
    {
      c = subii(b0, b1); b0 = b1; b1 = c;
      c = Fp_sub(c0, c1, s); c0 = c1; c1 = c;
    }
    else
    {
      c = subii(b0, mulii(q,b1)); b0 = b1; b1 = c;
      c = modii(subii(c0, mulii(q,c1)), s); c0 = c1; c1 = c;
    }
  }
  return gerepileupto(av, GEN_hash_keys(H));
}
