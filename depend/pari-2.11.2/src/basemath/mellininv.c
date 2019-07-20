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

/*******************************************************************/
/*               Computation of inverse Mellin                     */
/*               transforms of gamma products.                     */
/*******************************************************************/
#ifndef M_E
#define M_E 2.7182818284590452354
#endif

/* rough approximation to W0(a > -1/e), < 1% relative error */
double
dbllambertW0(double a)
{
  if (a < -0.2583)
  {
    const double c2 = -1./3, c3 = 11./72, c4 = -43./540, c5 = 769./17280;
    double p = sqrt(2*(M_E*a+1));
    if (a < -0.3243) return -1+p*(1+p*(c2+p*c3));
    return -1+p*(1+p*(c2+p*(c3+p*(c4+p*c5))));
  }
  else
  {
    double Wd = log(1.+a);
    Wd *= (1.-log(Wd/a))/(1.+Wd);
    if (a < 0.6482 && a > -0.1838) return Wd;
    return Wd*(1.-log(Wd/a))/(1.+Wd);
  }
}

/* rough approximation to W_{-1}(0 > a > -1/e), < 1% relative error */
double
dbllambertW_1(double a)
{
  if (a < -0.2464)
  {
    const double c2 = -1./3, c3 = 11./72, c4 = -43./540, c5 = 769./17280;
    double p = -sqrt(2*(M_E*a+1));
    if (a < -0.3243) return -1+p*(1+p*(c2+p*c3));
    return -1+p*(1+p*(c2+p*(c3+p*(c4+p*c5))));
  }
  else
  {
    double Wd;
    a = -a; Wd = -log(a);
    Wd *= (1.-log(Wd/a))/(1.-Wd);
    if (a < 0.0056) return -Wd;
    return -Wd*(1.-log(Wd/a))/(1.-Wd);
  }
}

/* ac != 0 */
static double
lemma526_i(double ac, double c, double t, double B)
{
  double D = -B/ac; /* sgn(t) = sgn(a) = - sgn(D) */
  if (D <= 0)
  {
    if (D > -100)
    {
      D = -exp(D) / t;
      if (D < - 1/M_E) return 0;
      D = dbllambertW_1(D);
    }
    else
    { /* avoid underflow, use asymptotic expansion */
      double U = D - log(t);
      D = U - log(-U);
    }
    return pow(maxdd(t, -t * D), c);
  }
  else
  {
    if (D < 100)
      D = dbllambertW0(-exp(D) / t);
    else
    { /* avoid overflow, use asymptotic expansion */
      double U = D - log(-t);
      D = U - log(U);
    }
    return pow(-t * D, c);
  }
}
/* b > 0, c > 0; solve x^a exp(-b x^(1/c)) < e^(-B) for x >= 0 */
double
dbllemma526(double a, double b, double c, double B)
{
  double ac;
  if (!a) return B <= 0? 0: pow(B/b, c);
  ac = a*c; if (B < 0) B = 1e-9;
  return lemma526_i(ac, c, ac/b, B);
}
/* Same, special case b/c = 2Pi, the only one needed: for c = d/2 */
double
dblcoro526(double a, double c, double B)
{
  if (!a) return B <= 0? 0: pow(B/(2*M_PI*c), c);
  if (B < 0) B = 1e-9;
  return lemma526_i(a*c, c, a/(2*M_PI), B);
}

static const double MELLININV_CUTOFF = 121.; /* C*C */

static GEN
MOD2(GEN x) { GEN q = gdivent(x,gen_2); return gsub(x,gmul2n(q,1)); }
static GEN
RgV_MOD2(GEN v)
{
  long i, l;
  GEN w = cgetg_copy(v,&l);
  for (i=1; i<l; i++) gel(w,i) = MOD2(gel(v,i));
  return w;
}

/* poles of the gamma factor */
static GEN
gammapoles(GEN Vga)
{
  long i, m, d = lg(Vga)-1;
  GEN P, V, B = RgV_MOD2(Vga);
  P = gen_indexsort(B, (void*)gcmp, cmp_nodata);
  V = cgetg(d+1, t_VEC);
  for (i = 1, m = 1; i <= d;)
  {
    GEN u = gel(B, P[i]);
    long k;
    for(k = i+1; k <= d; ++k)
      if (!gequal(gel(B, P[k]), u)) break;
    gel(V, m++) = vecpermute(Vga, vecslice(P,i,k-1));
    i = k;
  }
  setlg(V, m); return V;
}

static GEN
sercoeff(GEN x, long n, long prec)
{
  long N = n - valp(x);
  return (N < 0)? gen_0: gtofp(gel(x, N+2), prec);
}

/* generalized power series expansion of inverse Mellin around x = 0;
 * m-th derivative */
static GEN
Kderivsmallinit(GEN Vga, long m, long bitprec)
{
  pari_sp av = avma;
  long d = lg(Vga)-1, N, j, l, limn, prec;
  GEN LA, lj, mj, mat;
  double C2 = MELLININV_CUTOFF;

  LA = gammapoles(Vga);
  N = lg(LA)-1;
  lj = cgetg(N+1, t_VECSMALL);
  mj = cgetg(N+1, t_VEC);
  for (j = 1; j <= N; ++j)
  {
    GEN L = gel(LA,j);
    lj[j] = lg(L)-1;
    gel(mj,j) = gsubsg(2, vecmin(L));
  }
  prec = nbits2prec((long)(1+bitprec*(1+M_PI*d/C2)));
  limn = ceil(2*M_LN2*bitprec/(d*dbllambertW0(C2/(M_PI*M_E))));
  mat = cgetg(N+1, t_VEC);
  l = limn + 2;
  for (j=1; j <= N; j++)
  {
    GEN C, c, mjj = gel(mj,j), pr = gen_1, t = gen_1;
    long i, k, n, ljj = lj[j], lprecdl = ljj+3;
    for (i=1; i <= d; i++)
    {
      GEN a = gmul2n(gadd(mjj, gel(Vga,i)), -1);
      GEN u = deg1pol_shallow(ghalf, a, 0);
      pr = gmul(pr, ggamma(RgX_to_ser(u, lprecdl), prec));
      t = gmul(t, u);
    }
    c = cgetg(limn+2,t_COL);
    gel(c,1) = pr;
    for (n=1; n <= limn; n++)
      gel(c,n+1) = gdiv(gel(c,n), RgX_translate(t, stoi(-2*n)));

    gel(mat, j) = C = cgetg(ljj+1, t_COL);
    for (k = 1; k <= ljj; k++)
    {
      GEN L = cgetg(l, t_POL);
      L[1] = evalsigne(1)|evalvarn(0);
      for (n = 2; n < l; n++) gel(L,n) = sercoeff(gel(c,n), -k, prec);
      gel(C,k) = L;
    }
    /* C[k] = \sum_n c_{j,k} t^n =: C_k(t) in Dokchitser's Algo 3.3 */
    /* Take m-th derivative of t^(-mj+2) sum_k (-ln t)^k/k! C_k(t^2) */
    if (m)
    {
      mjj = gsubgs(mjj, 2);
      for (i = 1; i <= m; i++, mjj = gaddgs(mjj, 1))
      {
        for (k = 1; k <= ljj; k++)
        {
          GEN c = gel(C,k), d = RgX_shift_shallow(gmul2n(RgX_deriv(c),1), 1);
          c = RgX_Rg_mul(c, mjj);
          if (k < ljj) c = RgX_add(c, gel(C,k+1));
          gel(C,k) = RgX_sub(d, c);
        }
      }
      gel(mj,j) = gaddgs(mjj,2);
    }
    for (k = 1; k <= ljj; k++)
    {
      GEN c = gel(C,k);
      if (k > 2) c = RgX_Rg_div(c, mpfact(k-1));
      gel(C,k) = RgX_to_RgC(c, lgpol(c));
    }
  }
  /* Algo 3.3: * \phi^(m)(t) = sum_j t^m_j sum_k (-ln t)^k mat[j,k](t^2) */
  return gerepilecopy(av, mkvec3(lj,RgV_neg(mj),mat));
}

/* Evaluate a vector considered as a polynomial using Horner. Unstable!
 * If ui != NULL, ui = 1/u, evaluate P(1/u)*u^(deg P): useful for |u|>1 */
static GEN
evalvec(GEN vec, long lim, GEN u, GEN ui)
{
  pari_sp ltop = avma;
  GEN S = gen_0;
  long n;
  lim = minss(lim, lg(vec)-1);
  if (!ui)
    for (n = lim; n >= 1; --n) S = gmul(u, gadd(gel(vec,n), S));
  else
  {
    for (n = 1; n <= lim; ++n) S = gmul(ui, gadd(gel(vec,n), S));
    S = gmul(gpowgs(u, n), S);
  }
  return gerepileupto(ltop, S);
}

/* gammamellininvinit accessors */
static double
get_tmax(long bitprec)
{ return (M_LN2 / MELLININV_CUTOFF) * bitprec ; }
static GEN
GMi_get_Vga(GEN K) { return gel(K,2); }
static long
GMi_get_m(GEN K) { return itos( gel(K,3) ); }
static GEN /* [lj,mj,mat], Kderivsmall only */
GMi_get_VS(GEN K) { return gel(K,4); }
static GEN /* [Ms,cd,A2], Kderivlarge only */
GMi_get_VL(GEN K) { return gel(K,5); }
static double
GMi_get_tmax(GEN K, long bitprec)
{ return (typ(GMi_get_VS(K)) == t_INT)? -1.0 : get_tmax(bitprec); }

/* Compute m-th derivative of inverse Mellin at x by generalized power series
 * around x = 0; x2d = x^(2/d), x is possibly NULL (don't bother about
 * complex branches). Assume |x|^(2/d) <= tmax = M_LN2*bitprec/MELLININV_CUTOFF*/
static GEN
Kderivsmall(GEN K, GEN x, GEN x2d, long bitprec)
{
  pari_sp ltop = avma;
  GEN Vga = GMi_get_Vga(K), VS = GMi_get_VS(K);
  GEN lj = gel(VS,1), mj = gel(VS,2), mat = gel(VS,3);
  GEN d2, Lx, x2, x2i, A, S, pi;
  long prec, d, N, j, k, limn, m = GMi_get_m(K);
  double Ed, xd, Wd;

  N = lg(lj)-1; d = lg(Vga)-1; A = vecsum(Vga);
  Ed = M_LN2*bitprec / d;
  xd = maxdd(M_PI*dblmodulus(x2d), 1E-13); /* pi |x|^2/d unless x tiny */
  if (xd > Ed) pari_err_BUG("Kderivsmall (x2d too large)");
  /* Lemma 5.2.6 (2), a = 1 + log(Pi x^(2/d)) = log(e / xd),
   * B = log(2)*bitprec / d = Ed */
  Wd = dbllambertW0( Ed / (M_E*xd) ); /* solution of w exp(w) = B exp(-a)*/
  limn = (long) ceil(2*Ed/Wd);
  prec = nbits2prec((long) ceil(bitprec+d*xd/M_LN2));
  pi = mppi(prec);
  d2 = gdivsg(d,gen_2);
  if (x)
    x = gmul(gtofp(x,prec), gpow(pi,d2,prec));
  else
    x = gpow(gmul(gtofp(x2d,prec),pi), d2, prec);
  /* at this stage, x has been replaced by pi^(d/2) x */
  x2 = gsqr(x);
  Lx = gpowers(gneg(glog(x,prec)), vecsmall_max(lj));
  x2i = (gcmp(gnorml2(x2), gen_1) <= 0)? NULL: ginv(x2);
  S = gen_0;
  for (j = 1; j <= N; ++j)
  {
    long ljj = lj[j];
    GEN s = gen_0;
    for (k = 1; k <= ljj; k++)
      s = gadd(s, gmul(gel(Lx,k), evalvec(gmael(mat,j,k), limn, x2, x2i)));
    S = gadd(S, gmul(gpow(x, gel(mj,j), prec), s));
  }
  A = gsubsg(m*d, A);
  if (!gequal0(A)) S = gmul(S, gsqrt(gpow(pi, A, prec), prec));
  return gerepileupto(ltop, gtofp(S, nbits2prec(bitprec)));
}

/* In Klarge, we conpute K(t) as (asymptotic) * F(z), where F ~ 1 is given by
 * a continued fraction and z = Pi t^(2/d). If we take 2n terms in F (n terms
 * in Euler form), F_n(z) - F(z) is experimentally in exp(- C sqrt(n*z))
 * where C ~ 8 for d > 2 [HEURISTIC] and C = 4 (theorem) for d = 1 or d = 2
 * and vga = [0,1]. For e^(-E) absolute error, we want
 *   exp(-C sqrt(nz)) < e^-(E+a), where a ~ ln(asymptotic)
 * i.e.  2n > (E+a)^2 / t^(2/d) * 2/(C^2 Pi); C^2*Pi/2 ~ 100.5 ~ 101
 *
 * In fact, this model becomes wrong for z large: we use instead
 *
 *   exp(- sqrt(D * nz/log(z+1))) < e^-(E+a),
 * i.e.  2n > (E+a)^2 * log(1 + Pi t^(2/d))/ t^(2/d) * 2/(D Pi); */
static double
get_D(long d) { return d <= 2 ? 157. : 180.; }
/* if (abs), absolute error rather than relative */
static void
Kderivlarge_optim(GEN K, long abs, GEN t2d,GEN gcd, long *pbitprec, long *pnlim)
{
  GEN Vga = GMi_get_Vga(K), VL = GMi_get_VL(K), A2 = gel(VL,3);
  long bitprec = *pbitprec, d = lg(Vga)-1;
  const double D = get_D(d), td = dblmodulus(t2d), cd = gtodouble(gcd);
  double a, rtd, E = M_LN2*bitprec;

  rtd = (typ(t2d) == t_COMPLEX)? gtodouble(gel(t2d,1)): td;

  /* A2/2 = A, log(td) = (2/d)*log t */
  a = d*gtodouble(A2)*log2(td)/2 - (M_PI/M_LN2)*d*rtd + log2(cd); /*log2 K(t)~a*/

  /* if bitprec <= 0, caller should return K(t) ~ 0 */
  bitprec += 64;
  if (abs)
  {
    bitprec += ceil(a);
    if (a <= -65) E = M_LN2*bitprec; /* guarantees E <= initial E */
  }
  *pbitprec = bitprec;
  *pnlim = ceil(E*E * log2(1+M_PI*td) / (D*td));
}

/* Compute m-th derivative of inverse Mellin at t by continued fraction of
 * asymptotic expansion; t2d = t^(2/d). If t is NULL, "lfun" mode: don't
 * bother about complex branches + use absolute (rather than relative)
 * accuracy */
static GEN
Kderivlarge(GEN K, GEN t, GEN t2d, long bitprec0)
{
  pari_sp ltop = avma;
  GEN tdA, P, S, pi, z, Vga = GMi_get_Vga(K);
  const long d = lg(Vga)-1;
  GEN M, VL = GMi_get_VL(K), Ms = gel(VL,1), cd = gel(VL,2), A2 = gel(VL,3);
  long status, prec, nlim, m = GMi_get_m(K), bitprec = bitprec0;

  Kderivlarge_optim(K, !t, t2d, cd, &bitprec, &nlim);
  if (bitprec <= 0) return gen_0;
  prec = nbits2prec(bitprec);
  t2d = gtofp(t2d, prec);
  if (t)
    tdA = gpow(t, gdivgs(A2,d), prec);
  else
    tdA = gpow(t2d, gdivgs(A2,2), prec);
  tdA = gmul(cd, tdA);

  pi = mppi(prec);
  z = gmul(pi, t2d);
  P = gmul(tdA, gexp(gmulsg(-d, z), prec));
  if (m) P = gmul(P, gpowgs(mulsr(-2, pi), m));
  M = gel(Ms,1);
  status = itos(gel(Ms,2));
  if (status == 2)
  {
    if (lg(M) == 2) /* shortcut: continued fraction is constant */
      S = gel(M,1);
    else
      S = poleval(RgV_to_RgX(M, 0), ginv(z));
  }
  else
  {
    S = contfraceval_inv(M, z, nlim/2);
    if (DEBUGLEVEL>3)
    {
      GEN S0 = contfraceval_inv(M, z, nlim/2 + 1);
      long e = gexpo(gmul(P, gabs(gsub(S,S0),0)));
      if (-e < bitprec0)
        err_printf("Kderivlarge: e = %ld, bit = %ld\n",e,bitprec0);
    }
    if (status == 1) S = gmul(S, gsubsg(1, ginv(gmul(z, pi))));
  }
  return gerepileupto(ltop, gmul(P, S));
}

/* Dokchitser's coefficients used for asymptotic expansion of inverse Mellin
 * 2 <= p <= min(n+1, d) */
static GEN
fun_vp(long p, long n, long d, GEN SM, GEN vsinh)
{
  pari_sp ltop = avma;
  long m, j, k;
  GEN s = gen_0;
  for (m = 0; m <= p; ++m)
  {
    GEN pr = gen_1, s2 = gen_0, sh = gel(vsinh, d-p+1);/* (sh(x)/x)^(d-p) */
    long pm = p-m;
    for (j = m; j < p; ++j) pr = muliu(pr, d-j);
    for (k = 0; k <= pm; k+=2)
    {
      GEN e = gdiv(powuu(2*n-p+1, pm-k), mpfact(pm-k));
      s2 = gadd(s2, gmul(e, RgX_coeff(sh, k)));
    }
    s = gadd(s, gmul(gmul(gel(SM, m+1), pr), s2));
    if (gc_needed(ltop, 1)) s = gerepilecopy(ltop, s);
  }
  return gerepileupto(ltop, gmul(gdivsg(-d, powuu(2*d, p)), s));
}

/* Asymptotic expansion of inverse Mellin, to length nlimmax. Set status = 0
 * (regular), 1 (one Hankel determinant vanishes => contfracinit will fail)
 * or 2 (same as 1, but asymptotic expansion is finite!)
 *
 * If status = 2, the asymptotic expansion is finite so return only
 * the necessary number of terms nlim <= nlimmax + d. */
static GEN
Klargeinit0(GEN Vga, long nlimmax, long *status)
{
  const long prec = LOWDEFAULTPREC;
  const long d = lg(Vga)-1;
  long k, n, m, cnt;
  GEN pol, SM, nS1, se, vsinh, M, dk;

  if (d==1 || (d==2 && gequal1(gabs(gsub(gel(Vga,1), gel(Vga,2)), prec))))
  { /* shortcut */
    *status = 2; return mkvec(gen_1);
  }
  /* d >= 2 */
  *status = 0;
  pol = roots_to_pol(gneg(Vga), 0); /* deg(pol) = d */
  nS1 = gpowers(gneg(RgX_coeff(pol, d-1)), d);
  dk = gpowers(utoi(d), d-1);
  SM = cgetg(d+3, t_VEC);
  for (m = 0; m <= d; ++m)
  {
    pari_sp btop = avma;
    GEN s = gmul(gdivgs(gel(nS1, m+1), d), binomialuu(d, m));
    for (k = 1; k <= m; ++k)
    {
      GEN e = gmul(gel(nS1, m-k+1), gel(dk, k));
      s = gadd(s, gmul(gmul(e, binomialuu(d-k, m-k)), RgX_coeff(pol, d-k)));
    }
    gel(SM, m+1) = gerepileupto(btop, s);
  }
  se = gdiv(gsinh(RgX_to_ser(pol_x(0), d+2), prec), pol_x(0));
  vsinh = gpowers(se, d);
  M = vectrunc_init(nlimmax + d);
  vectrunc_append(M, gen_1);
  for (n=2, cnt=0; (n <= nlimmax) || cnt; ++n)
  {
    pari_sp btop = avma;
    long p, ld = minss(d, n);
    GEN s = gen_0;
    for (p = 2; p <= ld; ++p)
      s = gadd(s, gmul(fun_vp(p, n-1, d, SM, vsinh), gel(M, n+1-p)));
    s = gerepileupto(btop, gdivgs(s, n-1));
    vectrunc_append(M, s);
    if (!isintzero(s))
    {
      if (n >= nlimmax) break;
      cnt = 0;
    }
    else
    {
      cnt++; *status = 1;
      if (cnt >= d-1) { *status = 2; setlg(M, lg(M) - (d-1)); break; }
    }
  }
  return M;
}

/* remove trailing zeros from vector. */
static void
stripzeros(GEN M)
{
  long i;
  for(i = lg(M)-1; i >= 1; --i)
    if (!gequal0(gel(M, i))) break;
  setlg(M, i+1);
}

/* Asymptotic expansion of the m-th derivative of inverse Mellin, to length
 * nlimmax. If status = 2, the asymptotic expansion is finite so return only
 * the necessary number of terms nlim <= nlimmax + d. */
static GEN
gammamellininvasymp_i(GEN Vga, long nlimmax, long m, long *status)
{
  pari_sp ltop = avma;
  GEN M, A, Aadd;
  long d, i, nlim, n;

  M = Klargeinit0(Vga, nlimmax, status);
  if (!m) return gerepilecopy(ltop, M);
  d = lg(Vga)-1;
  /* half the exponent of t in asymptotic expansion. */
  A = gdivgs(gaddsg(1-d, vecsum(Vga)), 2*d);
  if (*status == 2) M = shallowconcat(M, zerovec(m));
  nlim = lg(M)-1;
  Aadd = gdivgs(stoi(2-d), 2*d); /* (1/d) - (1/2) */
  for (i = 1; i <= m; i++, A = gadd(A,Aadd))
    for (n = nlim-1; n >= 1; --n)
      gel(M, n+1) = gsub(gel(M, n+1),
                         gmul(gel(M, n), gsub(A, gdivgs(stoi(n-1), d))));
  stripzeros(M);
  return gerepilecopy(ltop, M);
}
GEN
gammamellininvasymp(GEN Vga, long nlimmax, long m)
{ long status;
  if (!is_vec_t(typ(Vga))) pari_err_TYPE("gammamellininvinit",Vga);
  return gammamellininvasymp_i(Vga, nlimmax, m, &status);
}

/* Does the continued fraction of the asymptotic expansion M at oo of inverse
 * Mellin transform attached to Vga have zero Hankel determinants ? */
static long
ishankelspec(GEN Vga, GEN M)
{
  long status, i, d = lg(Vga)-1;

  if (d == 5 || d == 7)
  { /* known bad cases: a x 5 and a x 7 */
    GEN v1 = gel(Vga, 1);
    for (i = 2; i <= d; ++i)
      if (!gequal(gel(Vga,i), v1)) break;
    if (i > d) return 1;
  }
  status = 0;
  /* Heuristic: if 6 first terms in contfracinit don't fail, assume it's OK */
  pari_CATCH(e_INV) { status = 1; }
  pari_TRY { contfracinit(M, minss(lg(M)-2,6)); }
  pari_ENDCATCH; return status;
}

/* Initialize data for computing m-th derivative of inverse Mellin */
GEN
gammamellininvinit(GEN Vga, long m, long bitprec)
{
  pari_sp ltop = avma;
  GEN A2, M, VS, VL, cd;
  long d = lg(Vga)-1, status;
  const double C2 = MELLININV_CUTOFF, D = get_D(d);
  double E = M_LN2*bitprec, tmax = get_tmax(bitprec); /* = E/C2 */
  const long nlimmax = ceil(E*log2(1+M_PI*tmax)*C2/D);

  if (!is_vec_t(typ(Vga))) pari_err_TYPE("gammamellininvinit",Vga);
  A2 = gaddsg(m*(2-d) + 1-d, vecsum(Vga));
  cd = (d <= 2)? gen_2: gsqrt(gdivgs(int2n(d+1), d), nbits2prec(bitprec));
  /* if in Klarge, we have |t| > tmax = E/C2, thus nlim < E*C2/D. */
  M = gammamellininvasymp_i(Vga, nlimmax, m, &status);
  if (status == 2)
  {
    tmax = -1.; /* only use Klarge */
    VS = gen_0;
  }
  else
  {
    long prec = nbits2prec((4*bitprec)/3);
    VS = Kderivsmallinit(Vga, m, bitprec);
    if (status == 0 && ishankelspec(Vga, M)) status = 1;
    if (status == 1)
    { /* a Hankel determinant vanishes => contfracinit is undefined.
         So compute K(t) / (1 - 1/(pi^2*t)) instead of K(t)*/
      GEN t = ginv(mppi(prec));
      long i;
      for (i = 2; i < lg(M); ++i)
        gel(M, i) = gadd(gel(M, i), gmul(gel(M, i-1), t));
    }
    else
      M = RgC_gtofp(M, prec); /* convert from rationals to t_REAL: faster */
    M = contfracinit(M, lg(M)-2);
  }
  VL = mkvec3(mkvec2(M, stoi(status)), cd, A2);
  return gerepilecopy(ltop, mkvec5(dbltor(tmax), Vga, stoi(m), VS, VL));
}

/* Compute m-th derivative of inverse Mellin at s2d = s^(d/2) using
 * initialization data. Use Taylor expansion at 0 for |s2d| < tmax, and
 * asymptotic expansion at oo otherwise. WARNING: assume that accuracy
 * has been increased according to tmax by the CALLING program. */
GEN
gammamellininvrt(GEN K, GEN s2d, long bitprec)
{
  if (dblmodulus(s2d) < GMi_get_tmax(K, bitprec))
    return Kderivsmall(K, NULL, s2d, bitprec);
  else
    return Kderivlarge(K, NULL, s2d, bitprec);
}

/* Compute inverse Mellin at s. K from gammamellininv OR a Vga, in which
 * case the initialization data is computed. */
GEN
gammamellininv(GEN K, GEN s, long m, long bitprec)
{
  pari_sp av = avma;
  GEN z, s2d;
  long d;
  if (!is_vec_t(typ(K))) pari_err_TYPE("gammamellininv",K);
  if (lg(K) != 6 || !is_vec_t(typ(GMi_get_Vga(K))))
    K = gammamellininvinit(K, m, bitprec);
  d = lg(GMi_get_Vga(K))-1;
  s2d = gpow(s, gdivgs(gen_2, d), nbits2prec(bitprec));
  if (dblmodulus(s2d) < GMi_get_tmax(K, bitprec))
    z = Kderivsmall(K, s, s2d, bitprec);
  else
    z = Kderivlarge(K, s, s2d, bitprec);
  return gerepileupto(av, z);
}
