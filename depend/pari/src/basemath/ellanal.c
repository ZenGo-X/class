/* Copyright (C) 2010  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/********************************************************************/
/**                                                                **/
/**                  L functions of elliptic curves                **/
/**                                                                **/
/********************************************************************/
#include "pari.h"
#include "paripriv.h"

struct baby_giant
{
  GEN baby, giant, sum;
  GEN bnd, rbnd;
};

/* Generic Buhler-Gross algorithm */

struct bg_data
{
  GEN E, N; /* ell, conductor */
  GEN bnd; /* t_INT; will need all an for n <= bnd */
  ulong rootbnd; /* sqrt(bnd) */
  GEN an; /* t_VECSMALL: cache of an, n <= rootbnd */
  GEN p;  /* t_VECSMALL: primes <= rootbnd */
};

typedef void bg_fun(void*el, GEN n, GEN a);

/* a = a_n, where p = bg->pp[i] divides n, and lasta = a_{n/p}.
 * Call fun(E, N, a_N), for all N, n | N, P^+(N) <= p, a_N != 0,
 * i.e. assumes that fun accumulates a_N * w(N) */

static void
gen_BG_add(void *E, bg_fun *fun, struct bg_data *bg, GEN n, long i, GEN a, GEN lasta)
{
  pari_sp av = avma;
  long j;
  ulong nn = itou_or_0(n);
  if (nn && nn <= bg->rootbnd) bg->an[nn] = itos(a);

  if (signe(a))
  {
    fun(E, n, a);
    j = 1;
  }
  else
    j = i;
  for(; j <= i; j++)
  {
    ulong p = bg->p[j];
    GEN nexta, pn = mului(p, n);
    if (cmpii(pn, bg->bnd) > 0) return;
    nexta = mulis(a, bg->an[p]);
    if (i == j && umodiu(bg->N, p)) nexta = subii(nexta, mului(p, lasta));
    gen_BG_add(E, fun, bg, pn, j, nexta, a);
    avma = av;
  }
}

static void
gen_BG_init(struct bg_data *bg, GEN E, GEN N, GEN bnd)
{
  bg->E = E;
  bg->N = N;
  bg->bnd = bnd;
  bg->rootbnd = itou(sqrtint(bnd));
  bg->p = primes_upto_zv(bg->rootbnd);
  bg->an = ellanQ_zv(E, bg->rootbnd);
}

static void
gen_BG_rec(void *E, bg_fun *fun, struct bg_data *bg)
{
  long i, j, lp = lg(bg->p)-1;
  GEN bndov2 = shifti(bg->bnd, -1);
  pari_sp av = avma, av2;
  GEN p;
  forprime_t S;
  (void)forprime_init(&S, utoipos(bg->p[lp]+1), bg->bnd);
  av2 = avma;
  if (DEBUGLEVEL)
    err_printf("1st stage, using recursion for p <= %ld\n", bg->p[lp]);
  for (i = 1; i <= lp; i++)
  {
    ulong pp = bg->p[i];
    long ap = bg->an[pp];
    gen_BG_add(E, fun, bg, utoipos(pp), i, stoi(ap), gen_1);
    avma = av2;
  }
  if (DEBUGLEVEL) err_printf("2nd stage, looping for p <= %Ps\n", bndov2);
  while ( (p = forprime_next(&S)) )
  {
    long jmax;
    GEN ap = ellap(bg->E, p);
    pari_sp av3 = avma;
    if (!signe(ap)) continue;

    jmax = itou( divii(bg->bnd, p) ); /* 2 <= jmax <= el->rootbound */
    fun(E, p, ap);
    for (j = 2;  j <= jmax; j++)
    {
      long aj = bg->an[j];
      GEN a, n;
      if (!aj) continue;
      a = mulis(ap, aj);
      n = muliu(p, j);
      fun(E, n, a);
      avma = av3;
    }
    avma = av2;
    if (abscmpii(p, bndov2) >= 0) break;
  }
  if (DEBUGLEVEL) err_printf("3nd stage, looping for p <= %Ps\n", bg->bnd);
  while ( (p = forprime_next(&S)) )
  {
    GEN ap = ellap(bg->E, p);
    if (!signe(ap)) continue;
    fun(E, p, ap);
    avma = av2;
  }
  avma = av;
}

/******************************************************************
 *
 * L functions of elliptic curves
 * Pascal Molin (molin.maths@gmail.com) 2014
 *
 ******************************************************************/

struct lcritical
{
  GEN h;    /* real */
  long cprec; /* computation prec */
  long L; /* number of points */
  GEN  K; /* length of series */
  long real;
};

static double
logboundG0(long e, double aY)
{
  double cla, loggam;
  cla = 1 + 1/sqrt(aY);
  if (e) cla = ( cla + 1/(2*aY) ) / (2*sqrt(aY));
  loggam = (e) ? M_LN2-aY : -aY + log( log( 1+1/aY) );
  return log(cla) + loggam;
}

static void
param_points(GEN N, double Y, double tmax, long bprec, long *cprec, long *L,
             GEN *K, double *h)
{
  double D, a, aY, X, logM;
  long d = 2, w = 1;
  tmax *= d;
  D = bprec * M_LN2 + M_PI/4*tmax + 2;
  *cprec = nbits2prec(ceil(D / M_LN2) + 5);
  a = 2 * M_PI / sqrt(gtodouble(N));
  aY = a * cos(M_PI/2*Y);
  logM = 2*M_LN2 + logboundG0(w+1, aY) + tmax * Y * M_PI/2;
  *h = ( 2 * M_PI * M_PI / 2 * Y ) / ( D + logM );
  X = log( D / a);
  *L = ceil( X / *h);
  *K = ceil_safe(dbltor( D / a ));
}

static GEN
vecF2_lk(GEN E, GEN K, GEN rbnd, GEN Q, GEN sleh, long prec)
{
  pari_sp av = avma, av2;
  long l, L  = lg(K)-1;
  GEN a = ellanQ_zv(E, itos(gel(K,1)));
  GEN S = cgetg(L+1, t_VEC);
  for (l = 1; l <= L; l++)
    gel(S,l) = cgetr(prec);
  av2 = avma;
  for (l = 1; l <= L; ++l)
  {
    GEN e1, Sl;
    long aB, b, A, B;
    GEN z, zB;
    pari_sp av3;
    long Kl = itou(gel(K,l));
    /* FIXME: could reduce prec here (useful for large prec) */
    e1 = gel(Q, l);
    Sl = real_0(prec);;
    /* baby-step giant step */
    A = rbnd[l]; B = A;
    z = powersr(e1, B); zB = gel(z, B+1);
    av3 = avma;
    for (aB = A*B; aB >= 0; aB -= B)
    {
      GEN s = real_0(prec); /* could change also prec here */
      for (b = B; b > 0; --b)
      {
        long k = aB+b;
        if (k <= Kl && a[k]) s = addrr(s, mulsr(a[k], gel(z, b+1)));
        if (gc_needed(av3, 1))
          gerepileall(av3, 2, &s, &Sl);
      }
      Sl = addrr(mulrr(Sl, zB), s);
    }
    affrr(mulrr(Sl, gel(sleh,l)), gel(S, l)); /* to avoid copying all S */
    avma = av2;
  }
  return gerepilecopy(av, S);
}

/* Return C, C[i][j] = Q[j]^i, i = 1..nb */
static void
baby_init(struct baby_giant *bb, GEN Q, GEN bnd, GEN rbnd, long prec)
{
  long i, j, l = lg(Q);
  GEN R, C, r0;
  C = cgetg(l,t_VEC);
  for (i = 1; i < l; ++i)
    gel(C, i) = powersr(gel(Q, i), rbnd[i]);
  R = cgetg(l,t_VEC);
  r0 = real_0(prec);
  for (i = 1; i < l; ++i)
  {
    gel(R, i) = cgetg(rbnd[i]+1, t_VEC);
    gmael(R, i, 1) = cgetr(prec);
    affrr(gmael(C, i, 2),gmael(R, i, 1));
    for (j = 2; j <= rbnd[i]; j++)
    {
      gmael(R, i, j) = cgetr(prec);
      affrr(r0, gmael(R, i, j));
    }
  }
  bb->baby = C; bb->giant = R;
  bb->bnd = bnd; bb->rbnd = rbnd;
}

static long
baby_size(GEN rbnd, long Ks, long prec)
{
  long i, s, m, l = lg(rbnd);
  for (s = 0, i = 1; i < l; ++i)
    s += rbnd[i];
  m = 2*s*prec + 3*l + s;
  if (DEBUGLEVEL)
    err_printf("ellL1: BG_add: %ld words, ellan: %ld words\n", m, Ks);
  return m;
}

static void
ellL1_add(void *E, GEN n, GEN a)
{
  pari_sp av = avma;
  struct baby_giant *bb = (struct baby_giant*) E;
  long j, l = lg(bb->giant);
  for (j = 1; j < l; j++)
    if (cmpii(n, gel(bb->bnd,j)) <= 0)
    {
      ulong r, q = uabsdiviu_rem(n, bb->rbnd[j], &r);
      GEN giant = gel(bb->giant, j), baby = gel(bb->baby, j);
      affrr(addrr(gel(giant, q+1), mulri(gel(baby, r+1), a)), gel(giant, q+1));
      avma = av;
    } else break;
}

static GEN
vecF2_lk_bsgs(GEN E, GEN bnd, GEN rbnd, GEN Q, GEN sleh, GEN N, long prec)
{
  pari_sp av = avma;
  struct bg_data bg;
  struct baby_giant bb;
  long k, L = lg(bnd)-1;
  GEN S;
  baby_init(&bb, Q, bnd, rbnd, prec);
  gen_BG_init(&bg, E, N, gel(bnd,1));
  gen_BG_rec((void*) &bb, ellL1_add, &bg);
  S = cgetg(L+1, t_VEC);
  for (k = 1; k <= L; ++k)
  {
    pari_sp av2 = avma;
    long j, g = rbnd[k];
    GEN giant = gmael(bb.baby, k, g+1);
    GEN Sl = real_0(prec);
    for (j = g; j >=1; j--)
      Sl = addrr(mulrr(Sl, giant), gmael(bb.giant,k,j));
    gel(S, k) = gerepileupto(av2, mulrr(gel(sleh,k), Sl));
  }
  return gerepileupto(av, S);
}

static GEN
vecF(struct lcritical *C, GEN E)
{
  pari_sp av = avma, av2;
  long prec = C->cprec, Ks = itos_or_0(C->K), l, L = C->L;
  GEN N = ellQ_get_N(E);
  GEN PiN = shiftr(divrr(mppi(prec), gsqrt(N, prec)), 1);
  GEN eh = mpexp(C->h), elh = powersr(eh, L-1), sleh = elh;
  GEN Q, bnd, rbnd, vec;
  rbnd = cgetg(L+1, t_VECSMALL);
  av2 = avma;
  bnd = cgetg(L+1, t_VEC);
  Q  = cgetg(L+1, t_VEC);
  for (l = 1; l <= L; ++l)
  {
    gel(bnd,l) = l==1 ? C->K: ceil_safe(divir(C->K, gel(elh, l)));
    rbnd[l] = itou(sqrtint(gel(bnd,l)))+1;
    gel(Q, l) = mpexp(mulrr(negr(PiN), gel(elh, l)));
  }
  gerepileall(av2, 2, &bnd, &Q);
  if (Ks && baby_size(rbnd, Ks, prec) > (Ks>>1))
    vec = vecF2_lk(E, bnd, rbnd, Q, sleh, prec);
  else
    vec = vecF2_lk_bsgs(E, bnd, rbnd, Q, sleh, N, prec);
  return gerepileupto(av, vec);
}

/* ************************************************************************
 *
 * Compute Lambda function by Fourier inversion
 *
 */

static GEN
glambda(GEN t, GEN vec, GEN h, long real, long prec)
{
  GEN ehs, elhs;
  GEN r;
  long L = lg(vec)-1, l;
  /* assume vec is a grid */
  ehs = gexp(gmul(gen_I(),gmul(h, t)), prec);
  elhs = (real == 1) ? gen_1 : mkcomplex(gen_0, gen_m1);
  r = gmul2n(real_i(gmul(real_i(gel(vec, 1)), elhs)), -1);
  /* FIXME: summing backward may be more stable */
  for (l = 2; l <= L; ++l)
  {
    elhs = gmul(elhs, ehs);
    r = gadd(r, real_i(gmul(gel(vec, l), elhs)));
  }
  return gmul(mulsr(4, h), r);
}

static GEN
Lpoints(struct lcritical *C, GEN e, GEN tmax, long bprec)
{
  double h = 0, Y = .97;
  GEN N = ellQ_get_N(e);
  param_points(N, Y, gtodouble(tmax), bprec, &C->cprec, &C->L, &C->K, &h);
  C->real = ellrootno_global(e);
  C->h = rtor(dbltor(h), C->cprec);
  return vecF(C, e);
}

static GEN
Llambda(GEN vec, struct lcritical *C, GEN t, long prec)
{
  GEN lambda = glambda(gprec_w(t, C->cprec), vec, C->h, C->real, C->cprec);
  return gprec_w(lambda, prec);
}

/* 2*(2*Pi)^(-s)*gamma(s)*N^(s/2); */
static GEN
ellgammafactor(GEN N, GEN s, long prec)
{
  GEN c = gpow(divrr(gsqrt(N,prec), Pi2n(1,prec)), s, prec);
  return gmul(gmul2n(c,1), ggamma(s, prec));
}

static GEN
ellL1_eval(GEN e, GEN vec, struct lcritical *C, GEN t, long prec)
{
  GEN g = ellgammafactor(ellQ_get_N(e), gaddgs(gmul(gen_I(),t), 1), prec);
  return gdiv(Llambda(vec, C, t, prec), g);
}

static GEN
ellL1_der(GEN e, GEN vec, struct lcritical *C, GEN t, long der, long prec)
{
  GEN r = polcoeff0(ellL1_eval(e, vec, C, t, prec), der, 0);
  r = gmul(r,powIs(C->real == 1 ? -der: 1-der));
  return gmul(real_i(r), mpfact(der));
}

GEN
ellL1_bitprec(GEN E, long r, long bitprec)
{
  pari_sp av = avma;
  struct lcritical C;
  long prec = nbits2prec(bitprec);
  GEN e, vec, t;
  if (r < 0)
    pari_err_DOMAIN("ellL1", "derivative order", "<", gen_0, stoi(r));
  e = ellanal_globalred(E, NULL);
  if (r == 0 && ellrootno_global(e) < 0) { avma = av; return gen_0; }
  vec = Lpoints(&C, e, gen_0, bitprec);
  t = r ? scalarser(gen_1, 0, r):  zeroser(0, 0);
  setvalp(t, 1);
  return gerepileupto(av, ellL1_der(e, vec, &C, t, r, prec));
}

GEN
ellL1(GEN E, long r, long prec) { return ellL1_bitprec(E, r, prec2nbits(prec)); }

GEN
ellanalyticrank_bitprec(GEN E, GEN eps, long bitprec)
{
  pari_sp av = avma, av2;
  long prec = nbits2prec(bitprec);
  struct lcritical C;
  pari_timer ti;
  GEN e, vec;
  long rk;
  if (DEBUGLEVEL) timer_start(&ti);
  if (!eps)
    eps = real2n(-bitprec/2+1, DEFAULTPREC);
  else
    if (typ(eps) != t_REAL) {
      eps = gtofp(eps, DEFAULTPREC);
      if (typ(eps) != t_REAL) pari_err_TYPE("ellanalyticrank", eps);
    }
  e = ellanal_globalred(E, NULL);
  vec = Lpoints(&C, e, gen_0, bitprec);
  if (DEBUGLEVEL) timer_printf(&ti, "init L");
  av2 = avma;
  for (rk = C.real>0 ? 0: 1;  ; rk += 2)
  {
    GEN Lrk;
    GEN t = rk ? scalarser(gen_1, 0, rk):  zeroser(0, 0);
    setvalp(t, 1);
    Lrk = ellL1_der(e, vec, &C, t, rk, prec);
    if (DEBUGLEVEL) timer_printf(&ti, "L^(%ld)=%Ps", rk, Lrk);
    if (abscmprr(Lrk, eps) > 0)
      return gerepilecopy(av, mkvec2(stoi(rk), Lrk));
    avma = av2;
  }
}

GEN
ellanalyticrank(GEN E, GEN eps, long prec)
{
  return ellanalyticrank_bitprec(E, eps, prec2nbits(prec));
}

/*        Heegner point computation

   This section is a C version by Bill Allombert of a GP script by
   Christophe Delaunay which was based on a GP script by John Cremona.
   Reference: Henri Cohen's book GTM 239.
*/

static void
heegner_L1_bg(void*E, GEN n, GEN a)
{
  struct baby_giant *bb = (struct baby_giant*) E;
  long j, l = lg(bb->giant);
  for (j = 1; j < l; j++)
    if (cmpii(n, gel(bb->bnd,j)) <= 0)
    {
      ulong r, q = uabsdiviu_rem(n, bb->rbnd[j], &r);
      GEN giant = gel(bb->giant, j), baby = gel(bb->baby, j);
      gaffect(gadd(gel(giant, q+1), gdiv(gmul(gel(baby, r+1), a), n)), gel(giant, q+1));
    }
}

static void
heegner_L1(void*E, GEN n, GEN a)
{
  struct baby_giant *bb = (struct baby_giant*) E;
  long j, l = lg(bb->giant);
  for (j = 1; j < l; j++)
    if (cmpii(n, gel(bb->bnd,j)) <= 0)
    {
      ulong r, q = uabsdiviu_rem(n, bb->rbnd[j], &r);
      GEN giant = gel(bb->giant, j), baby = gel(bb->baby, j);
      GEN ex = mulreal(gel(baby, r+1), gel(giant, q+1));
      affrr(addrr(gel(bb->sum, j), divri(mulri(ex, a), n)), gel(bb->sum, j));
    }
}
/* Return C, C[i][j] = Q[j]^i, i = 1..nb */
static void
baby_init2(struct baby_giant *bb, GEN Q, GEN bnd, GEN rbnd, long prec)
{
  long i, j, l = lg(Q);
  GEN R, C, r0;
  C = cgetg(l,t_VEC);
  for (i = 1; i < l; ++i)
    gel(C, i) = gpowers(gel(Q, i), rbnd[i]);
  R = cgetg(l,t_VEC);
  r0 = mkcomplex(real_0(prec),real_0(prec));
  for (i = 1; i < l; ++i)
  {
    gel(R, i) = cgetg(rbnd[i]+1, t_VEC);
    gmael(R, i, 1) = cgetc(prec);
    gaffect(gmael(C, i, 2),gmael(R, i, 1));
    for (j = 2; j <= rbnd[i]; j++)
    {
      gmael(R, i, j) = cgetc(prec);
      gaffect(r0, gmael(R, i, j));
    }
  }
  bb->baby = C; bb->giant = R;
  bb->bnd = bnd; bb->rbnd = rbnd;
}

/* Return C, C[i][j] = Q[j]^i, i = 1..nb */
static void
baby_init3(struct baby_giant *bb, GEN Q, GEN bnd, GEN rbnd, long prec)
{
  long i, l = lg(Q);
  GEN R, C, S;
  C = cgetg(l,t_VEC);
  for (i = 1; i < l; ++i)
    gel(C, i) = gpowers(gel(Q, i), rbnd[i]);
  R = cgetg(l,t_VEC);
  for (i = 1; i < l; ++i)
    gel(R, i) = gpowers(gmael(C, i, 1+rbnd[i]), rbnd[i]);
  S = cgetg(l,t_VEC);
  for (i = 1; i < l; ++i)
  {
    gel(S, i) = cgetr(prec);
    affrr(real_i(gmael(C, i, 2)), gel(S, i));
  }
  bb->baby = C; bb->giant = R; bb->sum = S;
  bb->bnd = bnd; bb->rbnd = rbnd;
}

/* ymin a t_REAL */
static GEN
heegner_psi(GEN E, GEN N, GEN points, long bitprec)
{
  pari_sp av = avma, av2;
  struct baby_giant bb;
  struct bg_data bg;
  long k, L = lg(points)-1, prec = nbits2prec(bitprec)+EXTRAPRECWORD;
  GEN  Q, pi2 = Pi2n(1, prec), bnd, rbnd;
  long l;
  GEN B = divrr(mulur(bitprec,mplog2(DEFAULTPREC)), pi2);
  GEN bndmax;
  rbnd = cgetg(L+1, t_VECSMALL);
  av2 = avma;
  bnd = cgetg(L+1, t_VEC);
  Q  = cgetg(L+1, t_VEC);
  for (l = 1; l <= L; ++l)
  {
    gel(bnd,l) = ceil_safe(divrr(B,imag_i(gel(points, l))));
    rbnd[l] = itou(sqrtint(gel(bnd,l)))+1;
    gel(Q, l) = expIxy(pi2, gel(points, l), prec);
  }
  gerepileall(av2, 2, &bnd, &Q);
  bndmax = gel(bnd,vecindexmax(bnd));
  gen_BG_init(&bg, E, N, bndmax);
  if (bitprec >= 1900)
  {
    GEN S;
    baby_init2(&bb, Q, bnd, rbnd, prec);
    gen_BG_rec((void*)&bb, heegner_L1_bg, &bg);
    S = cgetg(L+1, t_VEC);
    for (k = 1; k <= L; ++k)
    {
      pari_sp av2 = avma;
      long j, g = rbnd[k];
      GEN giant = gmael(bb.baby, k, g+1);
      GEN Sl = real_0(prec);
      for (j = g; j >=1; j--)
        Sl = gadd(gmul(Sl, giant), gmael(bb.giant,k,j));
      gel(S, k) = gerepileupto(av2, real_i(Sl));
    }
    return gerepileupto(av, S);
  }
  else
  {
    baby_init3(&bb, Q, bnd, rbnd, prec);
    gen_BG_rec((void*)&bb, heegner_L1, &bg);
    return gerepilecopy(av, bb.sum);
  }
}

/*Returns lambda_bad list for one prime p, nv = localred(E, p) */
static GEN
lambda1(GEN E, GEN nv, GEN p, long prec)
{
  pari_sp av;
  GEN res, lp;
  long kod = itos(gel(nv, 2));
  if (kod==2 || kod ==-2) return cgetg(1,t_VEC);
  av = avma; lp = glog(p, prec);
  if (kod > 4)
  {
    long n = Z_pval(ell_get_disc(E), p);
    long j, m = kod - 4, nl = 1 + (m >> 1L);
    res = cgetg(nl, t_VEC);
    for (j = 1; j < nl; j++)
      gel(res, j) = gmul(lp, gsubgs(gdivgs(sqru(j), n), j)); /* j^2/n - j */
  }
  else if (kod < -4)
    res = mkvec2(negr(lp), shiftr(mulrs(lp, kod), -2));
  else
  {
    const long lam[] = {8,9,0,6,0,0,0,3,4};
    long m = -lam[kod+4];
    res = mkvec(divru(mulrs(lp, m), 6));
  }
  return gerepilecopy(av, res);
}

static GEN
lambdalist(GEN E, long prec)
{
  pari_sp ltop = avma;
  GEN glob = ellglobalred(E), plist = gmael(glob,4,1), L = gel(glob,5);
  GEN res, v, D = ell_get_disc(E);
  long i, j, k, l, m, n, np = lg(plist), lr = 1;
  v = cgetg(np, t_VEC);
  for (j = 1, i = 1 ; j < np; ++j)
  {
    GEN p = gel(plist, j);
    if (dvdii(D, sqri(p)))
    {
      GEN la = lambda1(E, gel(L,j), p, prec);
      gel(v, i++) = la;
      lr *= lg(la);
    }
  }
  np = i;
  res = cgetg(lr+1, t_VEC);
  gel(res, 1) = gen_0; n = 1; m = 1;
  for (j = 1; j < np; ++j)
  {
    GEN w = gel(v, j);
    long lw = lg(w);
    for (k = 1; k <= n; k++)
    {
      GEN t = gel(res, k);
      for (l = 1, m = n; l < lw; l++, m+=n)
        gel(res, k + m) = mpadd(t, gel(w, l));
    }
    n = m;
  }
  return gerepilecopy(ltop, res);
}

/* P a t_INT or t_FRAC, return its logarithmic height */
static GEN
heightQ(GEN P, long prec)
{
  long s;
  if (typ(P) == t_FRAC)
  {
    GEN a = gel(P,1), b = gel(P,2);
    P = abscmpii(a,b) > 0 ? a: b;
  }
  s = signe(P);
  if (!s) return real_0(prec);
  if (s < 0) P = negi(P);
  return glog(P, prec);
}

/* t a t_INT or t_FRAC, returns max(1, log |t|), returns a t_REAL */
static GEN
logplusQ(GEN t, long prec)
{
  if (typ(t) == t_INT)
  {
    if (!signe(t)) return real_1(prec);
    if (signe(t) < 0) t = negi(t);
  }
  else
  {
    GEN a = gel(t,1), b = gel(t,2);
    if (abscmpii(a, b) < 0) return real_1(prec);
    if (signe(a) < 0) t = gneg(t);
  }
  return glog(t, prec);
}

/* See GTM239, p532, Th 8.1.18
 * Return M such that h_naive <= M */
static GEN
hnaive_max(GEN ell, GEN ht)
{
  const long prec = LOWDEFAULTPREC; /* minimal accuracy */
  GEN b2     = ell_get_b2(ell), j = ell_get_j(ell);
  GEN logd   = glog(absi_shallow(ell_get_disc(ell)), prec);
  GEN logj   = logplusQ(j, prec);
  GEN hj     = heightQ(j, prec);
  GEN logb2p = signe(b2)? addrr(logplusQ(gdivgs(b2, 12),prec), mplog2(prec))
                        : real_1(prec);
  GEN mu     = addrr(divru(addrr(logd, logj),6), logb2p);
  return addrs(addrr(addrr(ht, divru(hj,12)), mu), 2);
}

static GEN
qfb_root(GEN Q, GEN vDi)
{
  GEN a2 = shifti(gel(Q, 1),1), b = gel(Q, 2);
  return mkcomplex(gdiv(negi(b),a2),divri(vDi,a2));
}

static GEN
qimag2(GEN Q)
{
  pari_sp av = avma;
  GEN z = gdiv(negi(qfb_disc(Q)), shifti(sqri(gel(Q, 1)),2));
  return gerepileupto(av, z);
}

/***************************************************/
/*Routines for increasing the imaginary parts using*/
/*Atkin-Lehner operators                           */
/***************************************************/

static GEN
qfb_mult(GEN Q, GEN M)
{
  GEN A = gel(Q, 1) , B = gel(Q, 2) , C = gel(Q, 3);
  GEN a = gcoeff(M, 1, 1), b = gcoeff(M, 1, 2);
  GEN c = gcoeff(M, 2, 1), d = gcoeff(M, 2, 2);
  GEN W1 = addii(addii(mulii(sqri(a), A), mulii(mulii(c, a), B)), mulii(sqri(c), C));
  GEN W2 = addii(addii(mulii(mulii(shifti(b,1), a), A),
                       mulii(addii(mulii(d, a), mulii(c, b)), B)),
                 mulii(mulii(shifti(d,1), c), C));
  GEN W3 = addii(addii(mulii(sqri(b), A), mulii(mulii(d, b), B)), mulii(sqri(d), C));
  GEN D = gcdii(W1, gcdii(W2, W3));
  if (!equali1(D)) {
    W1 = diviiexact(W1,D);
    W2 = diviiexact(W2,D);
    W3 = diviiexact(W3,D);
  }
  return qfi(W1, W2, W3);
}

#ifdef DEBUG
static void
best_point_old(GEN Q, GEN NQ, GEN f, GEN *u, GEN *v)
{
  long n, k;
  GEN U, c, d;
  GEN A = gel(f, 1);
  GEN B = gel(f, 2);
  GEN C = gel(f, 3);
  GEN q = qfi(mulii(NQ, C), negi(B), diviiexact(A, NQ));
  redimagsl2(q, &U);
  *u = c = gcoeff(U, 1, 1);
  *v = d = gcoeff(U, 2, 1);
  if (equali1(gcdii(mulii(*u, NQ), mulii(*v, Q))))
    return;
  for (n = 1; ; n++)
  {
    for (k = -n; k<=n; k++)
    {
      *u = addis(c, k); *v = addiu(d, n);
      if (equali1(ggcd(mulii(*u, NQ), mulii(*v, Q))))
        return;
      *v= subiu(d, n);
      if (equali1(ggcd(mulii(*u, NQ), mulii(*v, Q))))
        return;
      *u = addiu(c, n); *v = addis(d, k);
      if (equali1(ggcd(mulii(*u, NQ), mulii(*v, Q))))
        return;
      *u = subiu(c, n);
      if (equali1(ggcd(mulii(*u, NQ), mulii(*v, Q))))
        return;
    }
  }
}
/* q(x,y) = ax^2 + bxy + cy^2 */
static GEN
qfb_eval(GEN q, GEN x, GEN y)
{
  GEN a = gel(q,1), b = gel(q,2), c = gel(q,3);
  GEN x2 = sqri(x), y2 = sqri(y), xy = mulii(x,y);
  return addii(addii(mulii(a, x2), mulii(b,xy)), mulii(c, y2));
}
#endif

static long
nexti(long i) { return i>0 ? -i : 1-i; }

/* q0 + i q1 + i^2 q2 */
static GEN
qfmin_eval(GEN q0, GEN q1, GEN q2, long i)
{ return addii(mulis(addii(mulis(q2, i), q1), i), q0); }

/* assume a > 0, return gcd(a,b,c) */
static ulong
gcduii(ulong a, GEN b, GEN c)
{
  a = ugcdiu(b, a);
  return a == 1? 1: ugcdiu(c, a);
}

static void
best_point(GEN Q, GEN NQ, GEN f, GEN *pu, GEN *pv)
{
  GEN a = mulii(NQ, gel(f,3)), b = negi(gel(f,2)), c = diviiexact(gel(f,1), NQ);
  GEN D = absi_shallow( qfb_disc(f) );
  GEN U, qr = redimagsl2(qfi(a,b,c), &U);
  GEN A = gel(qr,1), B = gel(qr,2), A2 = shifti(A,1), AA4 = sqri(A2);
  GEN V, best;
  long y;

  /* 4A qr(x,y) = (2A x + By)^2 + D y^2
   * Write x = x0(y) + i, where x0 is an integer minimum
   * (the smallest in case of tie) of x-> qr(x,y), for given y.
   * 4A qr(x,y) = ((2A x0 + By)^2 + Dy^2) + 4A i (2A x0 + By) + 4A^2 i^2
   *            = q0(y) + q1(y) i + q2 i^2
   * Loop through (x,y), y>0 by (roughly) increasing values of qr(x,y) */

  /* We must test whether [X,Y]~ := U * [x,y]~ satisfy (X NQ, Y Q) = 1
   * This is equivalent to (X,Y) = 1 (note that (X,Y) = (x,y)), and
   * (X, Q) = (Y, NQ) = 1.
   * We have U * [x0+i, y]~ = U * [x0,y]~ + i U[,1] =: V0 + i U[,1] */

  /* try [1,0]~ = first minimum */
  V = gel(U,1); /* U *[1,0]~ */
  *pu = gel(V,1);
  *pv = gel(V,2);
  if (is_pm1(gcdii(*pu, Q)) && is_pm1(gcdii(*pv, NQ))) return;

  /* try [0,1]~ = second minimum */
  V = gel(U,2); /* U *[0,1]~ */
  *pu = gel(V,1);
  *pv = gel(V,2);
  if (is_pm1(gcdii(*pu, Q)) && is_pm1(gcdii(*pv, NQ))) return;

  /* (X,Y) = (1, \pm1) always works. Try to do better now */
  best = subii(addii(a, c), absi_shallow(b));
  *pu = gen_1;
  *pv = signe(b) < 0? gen_1: gen_m1;

  for (y = 1;; y++)
  {
    GEN Dy2, r, By, x0, q0, q1, V0;
    long i;
    if (y > 1)
    {
      if (gcduii(y, gcoeff(U,1,1),  Q) != 1) continue;
      if (gcduii(y, gcoeff(U,2,1), NQ) != 1) continue;
    }
    Dy2 = mulii(D, sqru(y));
    if (cmpii(Dy2, best) >= 0) break; /* we won't improve. STOP */
    By = muliu(B,y), x0 = truedvmdii(negi(By), A2, &r);
    if (cmpii(r, A) >= 0) { x0 = subiu(x0,1); r = subii(r, A2); }
    /* (2A x + By)^2 + Dy^2, minimal at x = x0. Assume A2 > 0 */
    /* r = 2A x0 + By */
    q0 = addii(sqri(r), Dy2); /* minimal value for this y, at x0 */
    if (cmpii(q0, best) >= 0) continue; /* we won't improve for this y */
    q1 = shifti(mulii(A2, r), 1);

    V0 = ZM_ZC_mul(U, mkcol2(x0, utoipos(y)));
    for (i = 0;; i = nexti(i))
    {
      pari_sp av2 = avma;
      GEN x, N = qfmin_eval(q0, q1, AA4, i);
      if (cmpii(N , best) >= 0) break;
      x = addis(x0, i);
      if (ugcdiu(x, y) == 1)
      {
        GEN u, v;
        V = ZC_add(V0, ZC_z_mul(gel(U,1), i)); /* [X, Y] */
        u = gel(V,1);
        v = gel(V,2);
        if (is_pm1(gcdii(u, Q)) && is_pm1(gcdii(v, NQ)))
        {
          *pu = u;
          *pv = v;
          best = N; break;
        }
      }
      avma = av2;
    }
  }
#ifdef DEBUG
  {
    GEN oldu, oldv, F = qfi(a,b,c);
    best_point_old(Q, NQ, f, &oldu, &oldv);
    if (!equalii(oldu, *pu) || !equalii(oldv, *pv))
    {
      if (!equali1(gcdii(mulii(*pu, NQ), mulii(*pv, Q))))
        pari_err_BUG("best_point (gcd)");
      if (cmpii(qfb_eval(F, *pu,*pv), qfb_eval(F, oldu, oldv)) > 0)
      {
        pari_warn(warner, "%Ps,%Ps,%Ps, %Ps > %Ps",
                          Q,NQ,f, mkvec2(*pu,*pv), mkvec2(oldu,oldv));
        pari_err_BUG("best_point (too large)");
      }
    }
  }
#endif
}

static GEN
best_lift(GEN N, GEN Q, GEN NQ, GEN f)
{
  GEN a,b,c,d,M;
  best_point(Q, NQ, f, &c, &d);
  (void)bezout(mulii(d, Q), mulii(NQ, c), &a, &b);
  M = mkmat2( mkcol2(mulii(d, Q), mulii(negi(N), c)),
              mkcol2(b, mulii(a, Q)));
  return qfb_mult(f, M);
}

static GEN
lift_points(GEN N, GEN listQ, GEN f, GEN *pt, GEN *pQ)
{
  pari_sp av = avma;
  GEN yf = gen_0, tf = NULL, Qf = NULL;
  long k, l = lg(listQ);
  for (k = 1; k < l; ++k)
  {
    GEN c = gel(listQ, k), Q = gel(c,1), NQ = gel(c,2);
    GEN t = best_lift(N, Q, NQ, f), y = qimag2(t);
    if (gcmp(y, yf) > 0) { yf = y; Qf = Q; tf = t; }
  }
  gerepileall(av, 3, &tf, &Qf, &yf);
  *pt = tf; *pQ = Qf; return yf;
}

/***************************/
/*         Twists          */
/***************************/

static GEN
ltwist1(GEN E, GEN d, long bitprec)
{
  pari_sp av = avma;
  GEN Ed = ellinit(elltwist(E, d), NULL, DEFAULTPREC);
  GEN z = ellL1_bitprec(Ed, 0, bitprec);
  obj_free(Ed); return gerepileuptoleaf(av, z);
}

/* Return O_re*c(E)/(4*O_vol*|E_t|^2) */

static GEN
heegner_indexmult(GEN om, long t, GEN tam, long prec)
{
  pari_sp av = avma;
  GEN Ovr = gabs(imag_i(gel(om, 2)), prec); /* O_vol/O_re, t_REAL */
  return gerepileupto(av, divru(divir(tam, Ovr), 4*t*t));
}


/* omega(gcd(D, N)), given faN = factor(N) */
static long
omega_N_D(GEN faN, ulong D)
{
  GEN P = gel(faN, 1);
  long i, l = lg(P), w = 0;
  for (i = 1; i < l; i++)
    if (dvdui(D, gel(P,i))) w++;
  return w;
}

static GEN
heegner_indexmultD(GEN faN, GEN a, long D, GEN sqrtD)
{
  pari_sp av = avma;
  GEN c;
  long w;
  switch(D)
  {
    case -3: w = 9; break;
    case -4: w = 4; break;
    default: w = 1;
  }
  c = shifti(stoi(w), omega_N_D(faN,-D)); /* (w(D)/2)^2 * 2^omega(gcd(D,N)) */
  return gerepileupto(av, mulri(mulrr(a, sqrtD), c));
}

static GEN
heegner_try_point(GEN E, GEN lambdas, GEN ht, GEN z, long prec)
{
  long l = lg(lambdas);
  long i, eps;
  GEN P = real_i(pointell(E, z, prec)), x = gel(P,1);
  GEN rh = subrr(ht, shiftr(ellheightoo(E, P, prec),1));
  for (i = 1; i < l; ++i)
  {
    GEN logd = shiftr(gsub(rh, gel(lambdas, i)), -1);
    GEN d, approxd = gexp(logd, prec);
    if (DEBUGLEVEL > 2)
      err_printf("Trying lambda number %ld, logd=%Ps, approxd=%Ps\n", i, logd, approxd);
    d = grndtoi(approxd, &eps);
    if (signe(d) > 0 && eps<-10)
    {
      GEN X, ylist, d2 = sqri(d), approxn = mulir(d2, x);
      if (DEBUGLEVEL > 2) err_printf("approxn=%Ps  eps=%ld\n", approxn,eps);
      X = gdiv(ground(approxn), d2);
      ylist = ellordinate(E, X, prec);
      if (lg(ylist) > 1)
      {
        GEN P = mkvec2(X, gel(ylist, 1));
        GEN hp = ghell(E,P,prec);
        if (cmprr(hp, shiftr(ht,1)) < 0 && cmprr(hp, shiftr(ht,-1)) > 0)
          return P;
        if (DEBUGLEVEL)
          err_printf("found non-Heegner point %Ps\n", P);
      }
    }
  }
  return NULL;
}

static GEN
heegner_find_point(GEN e, GEN om, GEN ht, GEN z1, long k, long prec)
{
  GEN lambdas = lambdalist(e, prec);
  pari_sp av = avma;
  long m;
  GEN Ore = gel(om, 1), Oim = gel(om, 2);
  if (DEBUGLEVEL)
    err_printf("%ld*%ld multipliers to test\n",k,lg(lambdas)-1);
  for (m = 0; m < k; m++)
  {
    GEN P, z2 = divru(addrr(z1, mulsr(m, Ore)), k);
    if (DEBUGLEVEL > 2)
      err_printf("Trying multiplier %ld\n",m);
    P = heegner_try_point(e, lambdas, ht, z2, prec);
    if (P) return P;
    if (signe(ell_get_disc(e)) > 0)
    {
      z2 = gadd(z2, gmul2n(Oim, -1));
      P = heegner_try_point(e, lambdas, ht, z2, prec);
      if (P) return P;
    }
    avma = av;
  }
  pari_err_BUG("ellheegner, point not found");
  return NULL; /* LCOV_EXCL_LINE */
}

/* N > 1, fa = factor(N), return factor(4*N) */
static GEN
fa_shift2(GEN fa)
{
  GEN P = gel(fa,1), E = gel(fa,2);
  if (absequaliu(gcoeff(fa,1,1), 2))
  {
    E = shallowcopy(E);
    gel(E,1) = addiu(gel(E,1), 2);
  }
  else
  {
    P = shallowconcat(gen_2, P);
    E = shallowconcat(gen_2, E);
  }
  return mkmat2(P, E);
}

/* P = prime divisors of N(E). Return the product of primes p in P, a_p != -1
 * HACK: restrict to small primes since large ones won't divide our C-long
 * discriminants */
static GEN
get_bad(GEN E, GEN P)
{
  long k, l = lg(P), ibad = 1;
  GEN B = cgetg(l, t_VECSMALL);
  for (k = 1; k < l; k++)
  {
    GEN p = gel(P,k);
    long pp = itos_or_0(p);
    if (!pp) break;
    if (! equalim1(ellap(E,p))) B[ibad++] = pp;
  }
  setlg(B, ibad); return ibad == 1? NULL: zv_prod_Z(B);
}

/* list of pairs [Q,N/Q], where Q | N and gcd(Q,N/Q) = 1 */
static GEN
find_div(GEN N, GEN faN)
{
  GEN listQ = divisors(faN);
  long j, k, l = lg(listQ);

  gel(listQ, 1) = mkvec2(gen_1, N);
  for (j = k = 2; k < l; ++k)
  {
    GEN Q = gel(listQ, k), NQ = diviiexact(N, Q);
    if (is_pm1(gcdii(Q,NQ))) gel(listQ, j++) = mkvec2(Q,NQ);
  }
  setlg(listQ, j); return listQ;
}

static long
testDisc(GEN bad, long d) { return !bad || ugcdiu(bad, -d) == 1; }
/* bad = product of bad primes. Return the NDISC largest fundamental
 * discriminants D < d such that (D,bad) = 1 and d is a square mod 4N */
static GEN
listDisc(GEN fa4N, GEN bad, long d)
{
  const long NDISC = 10;
  GEN v = cgetg(NDISC+1, t_VECSMALL);
  pari_sp av = avma;
  long j = 1;
  for(;;)
  {
    d -= odd(d)? 1: 3;
    if (testDisc(bad,d) && unegisfundamental(-d) && Zn_issquare(stoi(d), fa4N))
    {
      v[j++] = d;
      if (j > NDISC) break;
    }
    avma = av;
  }
  avma = av; return v;
}
/* L = vector of [q1,q2] or [q1,q2,q2']
 * cd = (b^2 - D)/(4N) */
static void
listfill(GEN N, GEN b, GEN c, GEN d, GEN L, long *s)
{
  long k, l = lg(L);
  GEN add, frm2, a = mulii(d, N), V = mkqfi(a,b,c), frm = redimag(V);
  for (k = 1; k < l; ++k)
  { /* Lk = [v,frm] or [v,frm,frm2] */
    GEN Lk = gel(L,k);
    long i;
    for (i = 2; i < lg(Lk); i++) /* 1 or 2 elements */
      if (gequal(frm, gel(Lk,i)))
      {
        GEN v = gel(Lk, 1);
        if (cmpii(a, gel(v,1)) < 0) gel(Lk,1) = V;
        return;
      }
  }
  frm2 = redimag( mkqfi(d, negi(b), mulii(c,N)) );
  add = gequal(frm, frm2)? mkvec2(V,frm): mkvec3(V,frm,frm2);
  vectrunc_append(L, add);
  *s += lg(add) - 2;
}
/* faN4 = factor(4*N) */
static GEN
listheegner(GEN N, GEN faN4, GEN listQ, GEN D)
{
  pari_sp av = avma;
  const long kmin = 30;
  long h = itos(gel(quadclassunit0(D, 0, NULL, DEFAULTPREC), 1));
  GEN ymin, b = Zn_sqrt(D, faN4), L = vectrunc_init(h+1);
  long l, k, s = 0;
  for (k = 0; k < kmin || s < h; k++)
  {
    GEN bk = addii(b, mulsi(2*k, N));
    GEN C = diviiexact(shifti(subii(sqri(bk), D), -2), N);
    GEN div = divisors(C);
    long i, l = lg(div);
    for (i = 1; i < l; i++)
    {
      GEN d = gel(div, i), c = gel(div, l-i); /* cd = C */
      listfill(N, bk, c, d, L, &s);
    }
  }
  l = lg(L); ymin = NULL;
  for (k = 1; k < l; k++)
  {
    GEN t, Q, Lk = gel(L,k), f = gel(Lk,1);
    GEN y = lift_points(N, listQ, f, &t, &Q);
    gel(L, k) = mkvec3(t, stoi(lg(Lk) - 2), Q);
    if (!ymin || gcmp(y, ymin) < 0) ymin = y;
  }
  if (DEBUGLEVEL > 1)
    err_printf("Disc %Ps : N*ymin = %Pg\n", D,
                           gmul(gsqrt(ymin, DEFAULTPREC),N));
  return gerepilecopy(av, mkvec3(ymin, L, D));
}

/* Q | N, P = prime divisors of N, R[i] = local epsilon-factor at P[i].
 * Return \prod_{p | Q} R[i] */
static long
rootno(GEN Q, GEN P, GEN R)
{
  long s = 1, i, l = lg(P);
  for (i = 1; i < l; i++)
    if (dvdii(Q, gel(P,i))) s *= R[i];
  return s;
}

static void
heegner_find_disc(GEN *points, GEN *coefs, long *pind, GEN E,
                  GEN indmult, long prec)
{
  long d = 0;
  GEN faN4, bad, N, faN, listQ, listR;

  ellQ_get_Nfa(E, &N, &faN);
  faN4 = fa_shift2(faN);
  listQ = find_div(N, faN);
  bad = get_bad(E, gel(faN, 1));
  listR = gel(obj_check(E, Q_ROOTNO), 2);
  for(;;)
  {
    pari_sp av = avma;
    GEN list, listD = listDisc(faN4, bad, d);
    long k, l = lg(listD);
    list = cgetg(l, t_VEC);
    for (k = 1; k < l; ++k)
      gel(list, k) = listheegner(N, faN4, listQ, stoi(listD[k]));
    list = vecsort0(list, gen_1, 0);
    for (k = l-1; k > 0; --k)
    {
      long bprec = 8;
      GEN Lk = gel(list,k), D = gel(Lk,3);
      GEN sqrtD = sqrtr_abs(itor(D, prec)); /* sqrt(|D|) */
      GEN indmultD = heegner_indexmultD(faN, indmult, itos(D), sqrtD);
      do
      {
        GEN mulf, indr;
        pari_timer ti;
        if (DEBUGLEVEL) timer_start(&ti);
        mulf = ltwist1(E, D, bprec+expo(indmultD));
        if (DEBUGLEVEL) timer_printf(&ti,"ellL1twist");
        indr = mulrr(indmultD, mulf);
        if (DEBUGLEVEL) err_printf("Disc = %Ps, Index^2 = %Ps\n", D, indr);
        if (signe(indr)>0 && expo(indr) >= -1) /* indr >=.5 */
        {
          long e, i, l;
          GEN pts, cfs, L, indi = grndtoi(sqrtr_abs(indr), &e);
          if (e > expi(indi)-7)
          {
            bprec++;
            pari_warn(warnprec, "ellL1",bprec);
            continue;
          }
          *pind = itos(indi);
          L = gel(Lk, 2); l = lg(L);
          pts = cgetg(l, t_VEC);
          cfs = cgetg(l, t_VECSMALL);
          for (i = 1; i < l; ++i)
          {
            GEN P = gel(L,i), z = gel(P,2), Q = gel(P,3); /* [1 or 2, Q] */
            long c;
            gel(pts, i) = qfb_root(gel(P,1), sqrtD);
            c = rootno(Q, gel(faN,1), listR);
            if (!equali1(z)) c *= 2;
            cfs[i] = c;
          }
          if (DEBUGLEVEL)
            err_printf("N = %Ps, ymin*N = %Ps\n",N,
                       gmul(gsqrt(gel(Lk, 1), prec),N));
          *coefs = cfs; *points = pts; return;
        }
      } while(0);
    }
    d = listD[l-1]; avma = av;
  }
}

GEN
ellanal_globalred_all(GEN e, GEN *cb, GEN *N, GEN *tam)
{
  GEN E = ellanal_globalred(e, cb), red = obj_check(E, Q_GLOBALRED);
  *N = gel(red, 1);
  *tam = gel(red,2);
  if (signe(ell_get_disc(E))>0) *tam = shifti(*tam,1);
  return E;
}

GEN
ellheegner(GEN E)
{
  pari_sp av = avma;
  GEN z, P, ht, points, coefs, s, om, indmult;
  long ind, lint, k, l, wtor, etor;
  long bitprec = 16, prec = nbits2prec(bitprec)+1;
  pari_timer ti;
  GEN N, cb, tam, torsion;

  E = ellanal_globalred_all(E, &cb, &N, &tam);
  if (ellrootno_global(E) == 1)
    pari_err_DOMAIN("ellheegner", "(analytic rank)%2","=",gen_0,E);
  torsion = elltors(E);
  wtor = itos( gel(torsion,1) ); /* #E(Q)_tor */
  etor = wtor > 1? itou(gmael(torsion, 2, 1)): 1; /* exponent of E(Q)_tor */
  while (1)
  {
    GEN hnaive, l1;
    long bitneeded;
    if (DEBUGLEVEL) timer_start(&ti);
    l1 = ellL1_bitprec(E, 1, bitprec);
    if (DEBUGLEVEL) timer_printf(&ti,"ellL1");
    if (expo(l1) < 1 - bitprec/2)
      pari_err_DOMAIN("ellheegner", "analytic rank",">",gen_1,E);
    om = ellR_omega(E,prec);
    ht = divrr(mulru(l1, wtor * wtor), mulri(gel(om,1), tam));
    if (DEBUGLEVEL) err_printf("Expected height=%Ps\n", ht);
    hnaive = hnaive_max(E, ht);
    if (DEBUGLEVEL) err_printf("Naive height <= %Ps\n", hnaive);
    bitneeded = itos(gceil(divrr(hnaive, mplog2(prec)))) + 10;
    if (DEBUGLEVEL) err_printf("precision = %ld\n", bitneeded);
    if (bitprec>=bitneeded) break;
    bitprec = bitneeded;
    prec = nbits2prec(bitprec)+1;
  }
  indmult = heegner_indexmult(om, wtor, tam, prec);
  heegner_find_disc(&points, &coefs, &ind, E, indmult, prec);
  if (DEBUGLEVEL) timer_start(&ti);
  s = heegner_psi(E, N, points, bitprec);
  if (DEBUGLEVEL) timer_printf(&ti,"heegner_psi");
  l = lg(points);
  z = mulsr(coefs[1], gel(s, 1));
  for (k = 2; k < l; ++k) z = addrr(z, mulsr(coefs[k], gel(s, k)));
  if (DEBUGLEVEL) err_printf("z=%Ps\n", z);
  z = gsub(z, gmul(gel(om,1), ground(gdiv(z, gel(om,1)))));
  lint = wtor > 1 ? ugcd(ind, etor): 1;
  P = heegner_find_point(E, om, ht, gmulsg(2*lint, z), lint*2*ind, prec);
  if (DEBUGLEVEL) timer_printf(&ti,"heegner_find_point");
  if (cb) P = ellchangepointinv(P, cb);
  return gerepilecopy(av, P);
}

/* Modular degree */

static GEN
ellisobound(GEN e)
{
  GEN M = gel(ellisomat(e,0,1),2);
  return vecmax(gel(M,1));
}
/* 4Pi^2 / E.area */
static GEN
getA(GEN E, long prec) { return mpdiv(sqrr(Pi2n(1,prec)), ellR_area(E, prec)); }

/* Modular degree of elliptic curve e over Q, assuming Manin constant = 1
 * (otherwise multiply by square of Manin constant). */
GEN
ellmoddegree(GEN E)
{
  pari_sp av = avma;
  GEN N, tam, mc2, d;
  long b;
  E = ellanal_globalred_all(E, NULL, &N, &tam);
  mc2 = sqri(ellisobound(E));
  b = expi(mulii(N, mc2)) + maxss(0, expo(getA(E, LOWDEFAULTPREC))) + 16;
  for(;;)
  {
    long prec = nbits2prec(b), e, s;
    GEN deg = mulri(mulrr(lfunellmfpeters(E, b), getA(E, prec)), mc2);
    d = grndtoi(deg, &e);
    if (DEBUGLEVEL) err_printf("ellmoddegree: %Ps, bit=%ld, err=%ld\n",deg,b,e);
    s = expo(deg);
    if (e <= -8 && s <= b-8) return gerepileupto(av, gdiv(d,mc2));
    b = maxss(s, b+e) + 16;
  }
}
