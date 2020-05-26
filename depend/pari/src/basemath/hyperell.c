/* Copyright (C) 2014  The PARI group.

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
/**                     HYPERELLIPTIC CURVES                       **/
/**                                                                **/
/********************************************************************/
#include "pari.h"
#include "paripriv.h"

/* Implementation of Kedlaya Algorithm for counting point on hyperelliptic
curves by Bill Allombert based on a GP script by Bernadette Perrin-Riou.

References:
Pierrick Gaudry and Nicolas G\"urel
Counting Points in Medium Characteristic Using Kedlaya's Algorithm
Experiment. Math.  Volume 12, Number 4 (2003), 395-402.
   http://projecteuclid.org/euclid.em/1087568016

Harrison, M. An extension of Kedlaya's algorithm for hyperelliptic
  curves. Journal of Symbolic Computation, 47 (1) (2012), 89-101.
  http://arxiv.org/pdf/1006.4206v3.pdf
*/

/* We use the basis of differentials (x^i*dx/y^k) (i=1 to 2*g-1),
   with k either 1 or 3, depending on p and d, see Harrison paper */

static long
get_basis(long p, long d)
{
  if (odd(d))
    return p < d-1 ? 3 : 1;
  else
    return 2*p <= d-2 ? 3 : 1;
}

static GEN
FpXXQ_red(GEN S, GEN T, GEN p)
{
  pari_sp av = avma;
  long i, dS = degpol(S);
  GEN A, C;
  if (signe(S)==0) return pol_0(varn(T));
  A = cgetg(dS+3, t_POL);
  C = pol_0(varn(T));
  for(i=dS; i>0; i--)
  {
    GEN Si = FpX_add(C, gel(S,i+2), p);
    GEN R, Q = FpX_divrem(Si, T, p, &R);
    gel(A,i+2) = R;
    C = Q;
  }
  gel(A,2) = FpX_add(C, gel(S,2), p);
  A[1] = S[1];
  return gerepilecopy(av, FpXX_renormalize(A,dS+3));
}

static GEN
FpXXQ_sqr(GEN x, GEN T, GEN p)
{
  pari_sp av = avma;
  long n = degpol(T);
  GEN z = FpX_red(ZXX_sqr_Kronecker(x, n), p);
  z = Kronecker_to_ZXX(z, n, varn(T));
  return gerepileupto(av, FpXXQ_red(z, T, p));
}

static GEN
FpXXQ_mul(GEN x, GEN y, GEN T, GEN p)
{
  pari_sp av = avma;
  long n = degpol(T);
  GEN z = FpX_red(ZXX_mul_Kronecker(x, y, n), p);
  z = Kronecker_to_ZXX(z, n, varn(T));
  return gerepileupto(av, FpXXQ_red(z, T, p));
}

static GEN
ZpXXQ_invsqrt(GEN S, GEN T, ulong p, long e)
{
  pari_sp av = avma, av2;
  ulong mask;
  long v = varn(S), n=1;
  GEN a = pol_1(v);
  if (e <= 1) return gerepilecopy(av, a);
  mask = quadratic_prec_mask(e);
  av2 = avma;
  for (;mask>1;)
  {
    GEN q, q2, q22, f, fq, afq;
    long n2 = n;
    n<<=1; if (mask & 1) n--;
    mask >>= 1;
    q = powuu(p,n); q2 = powuu(p,n2);
    f = RgX_sub(FpXXQ_mul(FpXX_red(S, q), FpXXQ_sqr(a, T, q), T, q), pol_1(v));
    fq = ZXX_Z_divexact(f, q2);
    q22 = shifti(addiu(q2,1),-1);
    afq = FpXX_Fp_mul(FpXXQ_mul(a, fq, T, q2), q22, q2);
    a = RgX_sub(a, ZXX_Z_mul(afq, q2));
    if (gc_needed(av2,1))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"ZpXXQ_invsqrt, e = %ld", n);
      a = gerepileupto(av2, a);
    }
  }
  return gerepileupto(av, a);
}

static GEN
to_ZX(GEN a, long v) { return typ(a)==t_INT? scalarpol(a,v): a; }

static void
is_sing(GEN H, ulong p)
{
  pari_err_DOMAIN("hyperellpadicfrobenius","H","is singular at",utoi(p),H);
}

static void
get_UV(GEN *U, GEN *V, GEN T, ulong p, long e)
{
  GEN q = powuu(p,e), d;
  GEN dT = FpX_deriv(T, q);
  GEN R = polresultantext(T, dT);
  long v = varn(T);
  if (dvdiu(gel(R,3),p)) is_sing(T, p);
  d = Fp_inv(gel(R,3), q);
  *U = FpX_Fp_mul(FpX_red(to_ZX(gel(R,1),v),q),d,q);
  *V = FpX_Fp_mul(FpX_red(to_ZX(gel(R,2),v),q),d,q);
}

static GEN
frac_to_Fp(GEN a, GEN b, GEN p)
{
  GEN d = gcdii(a, b);
  return Fp_div(diviiexact(a, d), diviiexact(b, d), p);
}

static GEN
ZpXXQ_frob(GEN S, GEN U, GEN V, long k, GEN T, ulong p, long e)
{
  pari_sp av = avma, av2;
  long i, pr = degpol(S), dT = degpol(T), vT = varn(T);
  GEN q = powuu(p,e);
  GEN Tp = FpX_deriv(T, q), Tp1 = RgX_shift_shallow(Tp, 1);
  GEN M = to_ZX(gel(S,pr+2),vT) , R;
  av2 = avma;
  for(i = pr-1; i>=k; i--)
  {
    GEN A, B, H, Bc;
    ulong v, r;
    H = FpX_divrem(FpX_mul(V,M,q), T, q, &B);
    A = FpX_add(FpX_mul(U,M,q), FpX_mul(H, Tp, q),q);
    v = u_lvalrem(2*i+1,p,&r);
    Bc = ZX_deriv(B);
    Bc = FpX_Fp_mul(ZX_Z_divexact(Bc,powuu(p,v)),Fp_div(gen_2, utoi(r), q), q);
    M = FpX_add(to_ZX(gel(S,i+2),vT), FpX_add(A, Bc, q), q);
    if (gc_needed(av2,1))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"ZpXXQ_frob, step 1, i = %ld", i);
      M = gerepileupto(av2, M);
    }
  }
  if (degpol(M)<dT-1)
    return gerepileupto(av, M);
  R = RgX_shift_shallow(M,dT-degpol(M)-2);
  av2 = avma;
  for(i = degpol(M)-dT+2; i>=1; i--)
  {
    GEN B, c;
    R = RgX_shift_shallow(R, 1);
    gel(R,2) = gel(M, i+1);
    if (degpol(R) < dT) continue;
    B = FpX_add(FpX_mulu(T, 2*i, q), Tp1, q);
    c = frac_to_Fp(leading_coeff(R), leading_coeff(B), q);
    R = FpX_sub(R, FpX_Fp_mul(B, c, q), q);
    if (gc_needed(av2,1))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"ZpXXQ_frob, step 2, i = %ld", i);
      R = gerepileupto(av2, R);
    }
  }
  if (degpol(R)==dT-1)
  {
    GEN c = frac_to_Fp(leading_coeff(R), leading_coeff(Tp), q);
    R = FpX_sub(R, FpX_Fp_mul(Tp, c, q), q);
    return gerepileupto(av, R);
  } else
    return gerepilecopy(av, R);
}

static GEN
revdigits(GEN v)
{
  long i, n = lg(v)-1;
  GEN w = cgetg(n+2, t_POL);
  w[1] = evalsigne(1)|evalvarn(0);
  for (i=0; i<n; i++)
    gel(w,i+2) = gel(v,n-i);
  return FpXX_renormalize(w, n+2);
}

static GEN
diff_red(GEN s, GEN A, long m, GEN T, GEN p)
{
  long v, n, vT = varn(T);
  GEN Q, sQ, qS;
  pari_timer ti;
  if (DEBUGLEVEL>1) timer_start(&ti);
  Q = revdigits(FpX_digits(A,T,p));
  n = degpol(Q);
  if (DEBUGLEVEL>1) timer_printf(&ti,"reddigits");
  sQ = FpXXQ_mul(s,Q,T,p);
  if (DEBUGLEVEL>1) timer_printf(&ti,"redmul");
  qS = RgX_shift_shallow(sQ,m-n);
  v = ZX_val(sQ);
  if (n > m + v)
  {
    long i, l = n-m-v;
    GEN rS = cgetg(l+1,t_VEC);
    for (i = l-1; i >=0 ; i--)
      gel(rS,i+1) = to_ZX(gel(sQ, 1+v+l-i), vT);
    rS = FpXV_FpX_fromdigits(rS,T,p);
    gel(qS,2) = FpX_add(FpX_mul(rS, T, p), gel(qS, 2), p);
    if (DEBUGLEVEL>1) timer_printf(&ti,"redadd");
  }
  return qS;
}

static GEN
ZC_to_padic(GEN C, GEN q)
{
  long i, l = lg(C);
  GEN V = cgetg(l,t_COL);
  for(i = 1; i < l; i++)
    gel(V, i) = gadd(gel(C, i), q);
  return V;
}

static GEN
ZM_to_padic(GEN M, GEN q)
{
  long i, l = lg(M);
  GEN V = cgetg(l,t_MAT);
  for(i = 1; i < l; i++)
    gel(V, i) = ZC_to_padic(gel(M, i), q);
  return V;
}

static GEN
ZX_to_padic(GEN P, GEN q)
{
  long i, l = lg(P);
  GEN Q = cgetg(l, t_POL);
  Q[1] = P[1];
  for (i=2; i<l ;i++)
    gel(Q,i) = gadd(gel(P,i), q);
  return normalizepol(Q);
}

static GEN
ZXC_to_padic(GEN x, GEN q)
{ pari_APPLY_type(t_COL, ZX_to_padic(gel(x, i), q)) }

static GEN
ZXM_to_padic(GEN x, GEN q)
{ pari_APPLY_same(ZXC_to_padic(gel(x, i), q)) }

static GEN
ZlX_hyperellpadicfrobenius(GEN H, ulong p, long n)
{
  pari_sp av = avma;
  long k, N, i, d;
  GEN F, s, Q, pN1, U, V;
  pari_timer ti;
  if (typ(H) != t_POL) pari_err_TYPE("hyperellpadicfrobenius",H);
  if (p == 2) is_sing(H, 2);
  d = degpol(H);
  if (d <= 0)
    pari_err_CONSTPOL("hyperellpadicfrobenius");
  if (n < 1)
    pari_err_DOMAIN("hyperellpadicfrobenius","n","<", gen_1, utoi(n));
  k = get_basis(p, d);
  N = n + ulogint(2*n, p) + 1;
  pN1 = powuu(p,N+1);
  Q = RgX_to_FpX(H, pN1);
  if (dvdiu(leading_coeff(Q),p)) is_sing(H, p);
  setvarn(Q,1);
  if (DEBUGLEVEL>1) timer_start(&ti);
  s = revdigits(FpX_digits(RgX_inflate(Q, p), Q, pN1));
  if (DEBUGLEVEL>1) timer_printf(&ti,"s1");
  s = ZpXXQ_invsqrt(s, Q, p, N);
  if (k==3)
    s = FpXXQ_mul(s, FpXXQ_sqr(s, Q, pN1), Q, pN1);
  if (DEBUGLEVEL>1) timer_printf(&ti,"invsqrt");
  get_UV(&U, &V, Q, p, N+1);
  F = cgetg(d, t_MAT);
  for (i = 1; i < d; i++)
  {
    pari_sp av2 = avma;
    GEN M, D;
    D = diff_red(s, monomial(utoi(p),p*i-1,1),(k*p-1)>>1, Q, pN1);
    if (DEBUGLEVEL>1) timer_printf(&ti,"red");
    M = ZpXXQ_frob(D, U, V, (k-1)>>1, Q, p, N + 1);
    if (DEBUGLEVEL>1) timer_printf(&ti,"frob");
    gel(F, i) = gerepilecopy(av2, RgX_to_RgC(M, d-1));
  }
  return gerepileupto(av, F);
}

GEN
hyperellpadicfrobenius(GEN H, ulong p, long n)
{
  pari_sp av = avma;
  GEN M = ZlX_hyperellpadicfrobenius(H, p, n);
  GEN q = zeropadic(utoi(p),n);
  return gerepileupto(av, ZM_to_padic(M, q));
}

INLINE GEN
FpXXX_renormalize(GEN x, long lx)  { return ZXX_renormalize(x,lx); }

static GEN
ZpXQXXQ_red(GEN F, GEN S, GEN T, GEN q, GEN p, long e)
{
  pari_sp av = avma;
  long i, dF = degpol(F);
  GEN A, C;
  if (signe(F)==0) return pol_0(varn(S));
  A = cgetg(dF+3, t_POL);
  C = pol_0(varn(S));
  for(i=dF; i>0; i--)
  {
    GEN Fi = FpXX_add(C, gel(F,i+2), q);
    GEN R, Q = ZpXQX_divrem(Fi, S, T, q, p, e, &R);
    gel(A,i+2) = R;
    C = Q;
  }
  gel(A,2) = FpXX_add(C, gel(F,2), q);
  A[1] = F[1];
  return gerepilecopy(av, FpXXX_renormalize(A,dF+3));
}

static GEN
ZpXQXXQ_sqr(GEN x, GEN S, GEN T, GEN q, GEN p, long e)
{
  pari_sp av = avma;
  GEN z, kx;
  long n = degpol(S);
  kx = ZXX_to_Kronecker(x, n);
  z = Kronecker_to_ZXX(FpXQX_sqr(kx, T, q), n, varn(S));
  return gerepileupto(av, ZpXQXXQ_red(z, S, T, q, p, e));
}

static GEN
ZpXQXXQ_mul(GEN x, GEN y, GEN S, GEN T, GEN q, GEN p, long e)
{
  pari_sp av = avma;
  GEN z, kx, ky;
  long n = degpol(S);
  kx = ZXX_to_Kronecker(x, n);
  ky = ZXX_to_Kronecker(y, n);
  z = Kronecker_to_ZXX(FpXQX_mul(ky, kx, T, q), n, varn(S));
  return gerepileupto(av, ZpXQXXQ_red(z, S, T, q, p, e));
}

static GEN
FpXXX_red(GEN z, GEN p)
{
  GEN res;
  long i, l = lg(z);
  res = cgetg(l,t_POL); res[1] = z[1];
  for (i=2; i<l; i++)
  {
    GEN zi = gel(z,i);
    if (typ(zi)==t_INT)
      gel(res,i) = modii(zi,p);
    else
     gel(res,i) = FpXX_red(zi,p);
  }
  return FpXXX_renormalize(res,lg(res));
}

static GEN
FpXXX_Fp_mul(GEN z, GEN a, GEN p)
{
  return FpXXX_red(RgX_Rg_mul(z, a), p);
}

static GEN
ZpXQXXQ_invsqrt(GEN F, GEN S, GEN T, ulong p, long e)
{
  pari_sp av = avma, av2, av3;
  ulong mask;
  long v = varn(F), n=1;
  pari_timer ti;
  GEN a = pol_1(v), pp = utoi(p);
  if (DEBUGLEVEL>1) timer_start(&ti);
  if (e <= 1) return gerepilecopy(av, a);
  mask = quadratic_prec_mask(e);
  av2 = avma;
  for (;mask>1;)
  {
    GEN q, q2, q22, f, fq, afq;
    long n2 = n;
    n<<=1; if (mask & 1) n--;
    mask >>= 1;
    q = powuu(p,n); q2 = powuu(p,n2);
    av3 = avma;
    f = RgX_sub(ZpXQXXQ_mul(F, ZpXQXXQ_sqr(a, S, T, q, pp, n), S, T, q, pp, n), pol_1(v));
    fq = gerepileupto(av3, RgX_Rg_divexact(f, q2));
    q22 = shifti(addiu(q2,1),-1);
    afq = FpXXX_Fp_mul(ZpXQXXQ_mul(a, fq, S, T, q2, pp, n2), q22, q2);
    a = RgX_sub(a, RgX_Rg_mul(afq, q2));
    if (gc_needed(av2,1))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"ZpXQXXQ_invsqrt, e = %ld", n);
      a = gerepileupto(av2, a);
    }
  }
  return gerepileupto(av, a);
}

static GEN
frac_to_Fq(GEN a, GEN b, GEN T, GEN q, GEN p, long e)
{
  GEN d = gcdii(ZX_content(a), ZX_content(b));
  return ZpXQ_div(ZX_Z_divexact(a, d), ZX_Z_divexact(b, d), T, q, p, e);
}

static GEN
ZpXQXXQ_frob(GEN F, GEN U, GEN V, long k, GEN S, GEN T, ulong p, long e)
{
  pari_sp av = avma, av2;
  long i, pr = degpol(F), dS = degpol(S), v = varn(T);
  GEN q = powuu(p,e), pp = utoi(p);
  GEN Sp = RgX_deriv(S), Sp1 = RgX_shift_shallow(Sp, 1);
  GEN M = gel(F,pr+2), R;
  av2 = avma;
  for(i = pr-1; i>=k; i--)
  {
    GEN A, B, H, Bc;
    ulong v, r;
    H = ZpXQX_divrem(FpXQX_mul(V, M, T, q), S, T, q, utoi(p), e, &B);
    A = FpXX_add(FpXQX_mul(U, M, T, q), FpXQX_mul(H, Sp, T, q),q);
    v = u_lvalrem(2*i+1,p,&r);
    Bc = RgX_deriv(B);
    Bc = FpXX_Fp_mul(ZXX_Z_divexact(Bc,powuu(p,v)), Fp_div(gen_2, utoi(r), q), q);
    M = FpXX_add(gel(F,i+2), FpXX_add(A, Bc, q), q);
    if (gc_needed(av2,1))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"ZpXQXXQ_frob, step 1, i = %ld", i);
      M = gerepileupto(av2, M);
    }
  }
  if (degpol(M)<dS-1)
    return gerepileupto(av, M);
  R = RgX_shift_shallow(M,dS-degpol(M)-2);
  av2 = avma;
  for(i = degpol(M)-dS+2; i>=1; i--)
  {
    GEN B, c;
    R = RgX_shift_shallow(R, 1);
    gel(R,2) = gel(M, i+1);
    if (degpol(R) < dS) continue;
    B = FpXX_add(FpXX_mulu(S, 2*i, q), Sp1, q);
    c = frac_to_Fq(to_ZX(leading_coeff(R),v), to_ZX(leading_coeff(B),v), T, q, pp, e);
    R = FpXX_sub(R, FpXQX_FpXQ_mul(B, c, T, q), q);
    if (gc_needed(av2,1))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"ZpXXQ_frob, step 2, i = %ld", i);
      R = gerepileupto(av2, R);
    }
  }
  if (degpol(R)==dS-1)
  {
    GEN c = frac_to_Fq(to_ZX(leading_coeff(R),v), to_ZX(leading_coeff(Sp),v), T, q, pp, e);
    R = FpXX_sub(R, FpXQX_FpXQ_mul(Sp, c, T, q), q);
    return gerepileupto(av, R);
  } else
    return gerepilecopy(av, R);
}


static GEN
Fq_diff_red(GEN s, GEN A, long m, GEN S, GEN T, GEN q, GEN p, long e)
{
  long v, n;
  GEN Q, sQ, qS;
  pari_timer ti;
  if (DEBUGLEVEL>1) timer_start(&ti);
  Q = revdigits(ZpXQX_digits(A, S, T, q, p, e));
  n = degpol(Q);
  if (DEBUGLEVEL>1) timer_printf(&ti,"reddigits");
  sQ = ZpXQXXQ_mul(s, Q, S, T, q, p, e);
  if (DEBUGLEVEL>1) timer_printf(&ti,"redmul");
  qS = RgX_shift_shallow(sQ,m-n);
  v = ZX_val(sQ);
  if (n > m + v)
  {
    long i, l = n-m-v;
    GEN rS = cgetg(l+1,t_VEC);
    for (i = l-1; i >=0 ; i--)
      gel(rS,i+1) = gel(sQ, 1+v+l-i);
    rS = FpXQXV_FpXQX_fromdigits(rS, S, T, q);
    gel(qS,2) = FpXX_add(FpXQX_mul(rS, S, T, q), gel(qS, 2), q);
    if (DEBUGLEVEL>1) timer_printf(&ti,"redadd");
  }
  return qS;
}

static void
Fq_get_UV(GEN *U, GEN *V, GEN S, GEN T, ulong p, long e)
{
  GEN q = powuu(p, e), d;
  GEN dS = RgX_deriv(S);
  GEN R  = polresultantext(S, dS), C;
  long v = varn(S);
  if (signe(FpX_red(to_ZX(gel(R,3),v),utoi(p)))==0) is_sing(S, p);
  C = FpXQ_red(to_ZX(gel(R, 3),v), T, q);
  d = ZpXQ_inv(C, T, utoi(p), e);
  *U = FpXQX_FpXQ_mul(FpXQX_red(to_ZX(gel(R,1),v),T,q),d,T,q);
  *V = FpXQX_FpXQ_mul(FpXQX_red(to_ZX(gel(R,2),v),T,q),d,T,q);
}

static GEN
ZXX_to_FpXC(GEN x, long N, GEN p, long v)
{
  long i, l;
  GEN z;
  l = lg(x)-1; x++;
  if (l > N+1) l = N+1; /* truncate higher degree terms */
  z = cgetg(N+1,t_COL);
  for (i=1; i<l ; i++)
  {
    GEN xi = gel(x, i);
    gel(z,i) = typ(xi)==t_INT? scalarpol(Fp_red(xi, p), v): FpX_red(xi, p);
  }
  for (   ; i<=N ; i++)
    gel(z,i) = pol_0(v);
  return z;
}

GEN
ZlXQX_hyperellpadicfrobenius(GEN H, GEN T, ulong p, long n)
{
  pari_sp av = avma;
  long k, N, i, d, N1;
  GEN xp, F, s, q, Q, pN1, U, V, pp;
  pari_timer ti;
  if (typ(H) != t_POL) pari_err_TYPE("hyperellpadicfrobenius",H);
  if (p == 2) is_sing(H, 2);
  d = degpol(H);
  if (d <= 0)
    pari_err_CONSTPOL("hyperellpadicfrobenius");
  if (n < 1)
    pari_err_DOMAIN("hyperellpadicfrobenius","n","<", gen_1, utoi(n));
  k = get_basis(p, d); pp = utoi(p);
  N = n + ulogint(2*n, p) + 1;
  q = powuu(p,n); N1 = N+1;
  pN1 = powuu(p,N1); T = FpX_get_red(T, pN1);
  Q = RgX_to_FqX(H, T, pN1);
  if (signe(FpX_red(to_ZX(leading_coeff(Q),varn(Q)),pp))==0) is_sing(H, p);
  if (DEBUGLEVEL>1) timer_start(&ti);
  xp = ZpX_Frobenius(T, pp, N1);
  s = RgX_inflate(FpXY_FpXQ_evalx(Q, xp, T, pN1), p);
  s = revdigits(ZpXQX_digits(s, Q, T, pN1, pp, N1));
  if (DEBUGLEVEL>1) timer_printf(&ti,"s1");
  s = ZpXQXXQ_invsqrt(s, Q, T, p, N);
  if (k==3)
    s = ZpXQXXQ_mul(s, ZpXQXXQ_sqr(s, Q, T, pN1, pp, N1), Q, T, pN1, pp, N1);
  if (DEBUGLEVEL>1) timer_printf(&ti,"invsqrt");
  Fq_get_UV(&U, &V, Q, T, p, N+1);
  if (DEBUGLEVEL>1) timer_printf(&ti,"get_UV");
  F = cgetg(d, t_MAT);
  for (i = 1; i < d; i++)
  {
    pari_sp av2 = avma;
    GEN M, D;
    D = Fq_diff_red(s, monomial(pp,p*i-1,1),(k*p-1)>>1, Q, T, pN1, pp, N1);
    if (DEBUGLEVEL>1) timer_printf(&ti,"red");
    M = ZpXQXXQ_frob(D, U, V, (k - 1)>>1, Q, T, p, N1);
    if (DEBUGLEVEL>1) timer_printf(&ti,"frob");
    gel(F, i) = gerepileupto(av2, ZXX_to_FpXC(M, d-1, q, varn(T)));
  }
  return gerepileupto(av, F);
}

GEN
nfhyperellpadicfrobenius(GEN H, GEN T, ulong p, long n)
{
  pari_sp av = avma;
  GEN M = ZlXQX_hyperellpadicfrobenius(lift_shallow(H),T,p,n);
  GEN MM = ZpXQM_prodFrobenius(M, T, utoi(p), n);
  GEN q = zeropadic(utoi(p),n);
  GEN m = gmul(ZXM_to_padic(MM, q), gmodulo(gen_1, T));
  return gerepileupto(av, m);
}

static GEN
F2x_genus2charpoly_naive(GEN P, GEN Q)
{
  long a, b = 1, c = 0;
  GEN T = mkvecsmall2(P[1], 7);
  GEN PT = F2x_rem(P, T), QT = F2x_rem(Q, T);
  long q0 = F2x_eval(Q, 0), q1 = F2x_eval(Q, 1);
  long dP = F2x_degree(P), dQ = F2x_degree(Q);
  a= dQ<3 ? 0: dP<=5 ? 1: -1;
  a += (q0? F2x_eval(P, 0)? -1: 1: 0) + (q1? F2x_eval(P, 1)? -1: 1: 0);
  b += q0 + q1;
  if (lgpol(QT))
    c = (F2xq_trace(F2xq_div(PT, F2xq_sqr(QT, T), T), T)==0 ? 1: -1);
  return mkvecsmalln(6, 0UL, 4, 2*a, (b+2*c+a*a)>>1, a, 1UL);
}

static GEN
Flx_difftable(GEN P, ulong p)
{
  long i, n = degpol(P);
  GEN V = cgetg(n+2, t_VEC);
  gel(V, n+1) = P;
  for(i = n; i >= 1; i--)
    gel(V, i) = Flx_diff1(gel(V, i+1), p);
  return V;
}

static GEN
FlxV_Fl2_eval_pre(GEN V, GEN x, ulong D, ulong p, ulong pi)
{
  long i, n = lg(V)-1;
  GEN r = cgetg(n+1, t_VEC);
  for (i = 1; i <= n; i++)
    gel(r, i) = Flx_Fl2_eval_pre(gel(V, i), x, D, p, pi);
  return r;
}

static GEN
Fl2V_next(GEN V, ulong p)
{
  long i, n = lg(V)-1;
  GEN r = cgetg(n+1, t_VEC);
  gel(r, 1) = gel(V, 1);
  for (i = 2; i <= n; i++)
    gel(r, i) = Flv_add(gel(V, i), gel(V, i-1), p);
  return r;
}

static GEN
Flx_genus2charpoly_naive(GEN H, ulong p)
{
  pari_sp av = avma, av2;
  ulong pi = get_Fl_red(p);
  ulong i, j, p2 = p>>1, D = 2, e = ((p&2UL) == 0) ? -1 : 1;
  long a, b, c = 0, n = degpol(H);
  GEN t, k = const_vecsmall(p, -1);
  k[1] = 0;
  for (i=1, j=1; i < p; i += 2, j = Fl_add(j, i, p)) k[j+1] = 1;
  while (k[1+D] >= 0) D++;
  b = n == 5 ? 0 : 1;
  a = b ? k[1+Flx_lead(H)]: 0;
  t = Flx_difftable(H, p);
  av2 = avma;
  for (i=0; i < p; i++)
  {
    ulong v = Flx_eval(H, i, p);
    a += k[1+v];
    b += !!v;
  }
  for (j=1; j <= p2; j++)
  {
    GEN V = FlxV_Fl2_eval_pre(t, mkvecsmall2(0, j), D, p, pi);
    for (i=0;; i++)
    {
      GEN r2 = gel(V, n+1);
      c += uel(r2,2) ?
        (uel(r2,1) ? k[1+Fl2_norm_pre(r2, D, p, pi)]: e)
         : !!uel(r2,1);
      if (i == p-1) break;
      V = Fl2V_next(V, p);
    }
    avma = av2;
  }
  avma = av;
  return mkvecsmalln(6, 0UL, p*p, a*p, (b+2*c+a*a)>>1, a, 1UL);
}

static GEN
charpoly_funceq(GEN P, GEN q)
{
  long i, l, g = degpol(P)>>1;
  GEN Q = cgetg_copy(P, &l);
  Q[1] = P[1];
  for (i=0; i<=g; i++)
    gel(Q, i+2) = mulii(gel(P, 2*g-i+2), powiu(q, g-i));
  for (; i<=2*g; i++)
    gel(Q, i+2) = icopy(gel(P, i+2));
  return Q;
}

static long
hyperell_Weil_bound(GEN q, ulong g, GEN p)
{
  pari_sp av = avma;
  GEN w = mulii(binomialuu(2*g,g),sqrtint(shifti(powiu(q, g),2)));
  long e = logint(w, p) + 1;
  avma = av; return e;
}

GEN
hyperellcharpoly(GEN PQ)
{
  pari_sp av = avma;
  GEN H, M, R, T=NULL, pp=NULL, q;
  long d, n, eps = 0;
  ulong p;
  if (is_vec_t(typ(PQ)) && lg(PQ)==3)
    H = gadd(gsqr(gel(PQ, 2)), gmul2n(gel(PQ, 1), 2));
  else
    H = PQ;
  if (typ(H)!=t_POL || !RgX_is_FpXQX(H, &T, &pp) || !pp)
    pari_err_TYPE("hyperellcharpoly",H);
  p = itou(pp);
  if (!T)
  {
    if (p==2 && is_vec_t(typ(PQ)))
    {
      long dP, dQ, v = varn(H);
      GEN P = gel(PQ,1), Q = gel(PQ,2);
      if (typ(P)!=t_POL)  P = scalarpol(P, v);
      if (typ(Q)!=t_POL)  Q = scalarpol(Q, v);
      dP = degpol(P); dQ = degpol(Q);
      if (dP<=6 && dQ <=3 && (dQ==3 || dP>=5))
      {
        GEN P2 = RgX_to_F2x(P), Q2 = RgX_to_F2x(Q);
        GEN D = F2x_add(F2x_mul(P2, F2x_sqr(F2x_deriv(Q2))), F2x_sqr(F2x_deriv(P2)));
        if (F2x_degree(F2x_gcd(D, Q2))) is_sing(PQ, 2);
        if (dP==6 && dQ<3 && F2x_coeff(P2,5)==F2x_coeff(Q2,2))
          is_sing(PQ, 2); /* The curve is singular at infinity */
        R = zx_to_ZX(F2x_genus2charpoly_naive(P2, Q2));
        return gerepileupto(av, R);
      }
    }
    H = RgX_to_FpX(H, pp);
    d = degpol(H);
    if (d <= 0) is_sing(H, p);
    if (p > 2 && ((d == 5 && p < 17500) || (d == 6 && p < 24500)))
    {
      GEN Hp = ZX_to_Flx(H, p);
      if (!Flx_is_squarefree(Hp, p)) is_sing(H, p);
      R = zx_to_ZX(Flx_genus2charpoly_naive(Hp, p));
      return gerepileupto(av, R);
    }
    n = hyperell_Weil_bound(pp, (d-1)>>1, pp);
    eps = odd(d)? 0: Fp_issquare(leading_coeff(H), pp);
    M = hyperellpadicfrobenius(H, p, n);
    R = centerlift(carberkowitz(M, 0));
    q = pp;
  }
  else
  {
    int fixvar;
    T = typ(T)==t_FFELT? FF_mod(T): RgX_to_FpX(T, pp);
    q = powuu(p, degpol(T));
    fixvar = (varncmp(varn(T),varn(H)) <= 0);
    if (fixvar) setvarn(T, fetch_var());
    H = RgX_to_FpXQX(H, T, pp);
    d = degpol(H);
    if (d <= 0) is_sing(H, p);
    eps = odd(d)? 0: Fq_issquare(leading_coeff(H), T, pp);
    n = hyperell_Weil_bound(q, (d-1)>>1, pp);
    M = nfhyperellpadicfrobenius(H, T, p, n);
    R = simplify_shallow(centerlift(liftpol_shallow(carberkowitz(M, 0))));
    if (fixvar) (void)delete_var();
  }
  if (!odd(d))
  {
    GEN b = get_basis(p, d) == 3 ? gen_1 : q;
    GEN pn = powuu(p, n);
    R = FpX_div_by_X_x(R, eps? b: negi(b), pn, NULL);
    R = FpX_center_i(R, pn, shifti(pn,-1));
  }
  R = charpoly_funceq(R, q);
  return gerepilecopy(av, R);
}
