/* Copyright (C) 2000-2004  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/*******************************************************************/
/*                                                                 */
/*            POLYNOMIAL FACTORIZATION IN A NUMBER FIELD           */
/*                                                                 */
/*******************************************************************/
#include "pari.h"
#include "paripriv.h"

static GEN nfsqff(GEN nf,GEN pol,long fl,GEN den);
static int nfsqff_use_Trager(long n, long dpol);

enum { FACTORS = 0, ROOTS, ROOTS_SPLIT };

/* for nf_bestlift: reconstruction of algebraic integers known mod P^k,
 * P maximal ideal above p */
typedef struct {
  long k;    /* input known mod P^k */
  GEN p, pk; /* p^k = denom(prk^-1) [ assume pr unramified ]*/
  GEN prk;   /* |.|^2 LLL-reduced basis (b_i) of P^k  (NOT T2-reduced) */
  GEN iprk;  /* den * prk^-1 */
  GEN GSmin; /* min |b_i^*|^2 */

  GEN Tp; /* Tpk mod p */
  GEN Tpk;
  GEN ZqProj;/* projector to Zp / P^k = Z/p^k[X] / Tpk */

  GEN tozk;
  GEN topow;
  GEN topowden; /* topow x / topowden = basistoalg(x) */
  GEN dn; /* NULL (we trust nf.zk) or a t_INT > 1 (an alg. integer has
             denominator dividing dn, when expressed on nf.zk */
} nflift_t;

typedef struct
{
  nflift_t *L;
  GEN nf;
  GEN pol, polbase; /* leading coeff is a t_INT */
  GEN fact;
  GEN Br, bound, ZC, BS_2;
} nfcmbf_t;

/*******************************************************************/
/*              RATIONAL RECONSTRUCTION (use ratlift)              */
/*******************************************************************/
/* NOT stack clean. a, b stay on the stack */
static GEN
lift_to_frac_tdenom(GEN t, GEN mod, GEN amax, GEN bmax, GEN denom, GEN tdenom)
{
  GEN a, b;
  if (signe(t) < 0) t = addii(t, mod); /* in case t is a centerlift */
  if (tdenom)
  {
    pari_sp av = avma;
    a = Fp_center_i(Fp_mul(t, tdenom, mod), mod, shifti(mod,-1));
    if (abscmpii(a, amax) < 0)
    {
      GEN d = gcdii(a, tdenom);
      a = diviiexact(a, d);
      b = diviiexact(tdenom, d);
      if (is_pm1(b)) { return gerepileuptoint(av, a); }
      return gerepilecopy(av, mkfrac(a, b));
    }
    avma = av;
  }
  if (!Fp_ratlift(t, mod, amax,bmax, &a,&b)
     || (denom && !dvdii(denom,b))
     || !is_pm1(gcdii(a,b))) return NULL;
  if (is_pm1(b)) { cgiv(b); return a; }
  return mkfrac(a, b);
}

static GEN
lift_to_frac(GEN t, GEN mod, GEN amax, GEN bmax, GEN denom)
{
  return lift_to_frac_tdenom(t, mod, amax, bmax, denom, NULL);
}

/* Compute rational lifting for all the components of M modulo mod.
 * Assume all Fp_ratlift preconditions are met; we allow centerlifts but in
 * that case are no longer stack clean. If one component fails, return NULL.
 * If denom != NULL, check that the denominators divide denom.
 *
 * We suppose gcd(mod, denom) = 1, then a and b are coprime; so we can use
 * mkfrac rather than gdiv */
GEN
FpC_ratlift(GEN P, GEN mod, GEN amax, GEN bmax, GEN denom)
{
  pari_sp ltop = avma;
  long j, l;
  GEN a, d, tdenom = NULL, Q = cgetg_copy(P, &l);
  if (l==1) return Q;
  for (j = 1; j < l; ++j)
  {
    a = lift_to_frac_tdenom(gel(P,j), mod, amax, bmax, denom, tdenom);
    if (!a) { avma = ltop; return NULL; }
    d = Q_denom(a);
    tdenom = tdenom ? cmpii(tdenom, d)<0? d: tdenom : d;
    gel(Q,j) = a;
  }
  return Q;
}

GEN
FpM_ratlift(GEN M, GEN mod, GEN amax, GEN bmax, GEN denom)
{
  pari_sp av = avma;
  long j, l = lg(M);
  GEN N = cgetg_copy(M, &l);
  if (l == 1) return N;
  for (j = 1; j < l; ++j)
  {
    GEN a = FpC_ratlift(gel(M, j), mod, amax, bmax, denom);
    if (!a) { avma = av; return NULL; }
    gel(N,j) = a;
  }
  return N;
}

GEN
FpX_ratlift(GEN P, GEN mod, GEN amax, GEN bmax, GEN denom)
{
  pari_sp ltop = avma;
  long j, l;
  GEN a, Q = cgetg_copy(P, &l);
  Q[1] = P[1];
  for (j = 2; j < l; ++j)
  {
    a = lift_to_frac(gel(P,j), mod, amax,bmax,denom);
    if (!a) { avma = ltop; return NULL; }
    gel(Q,j) = a;
  }
  return Q;
}

/*******************************************************************/
/*              GCD in K[X], K NUMBER FIELD                        */
/*******************************************************************/
/* P a non-zero ZXQX */
static GEN
lead_simplify(GEN P)
{
  GEN x = gel(P, lg(P)-1); /* x a non-zero ZX or t_INT */
  if (typ(x) == t_POL && !degpol(x)) x = gel(x,2);
  return is_pm1(x)? NULL: x;
}
/* P,Q in Z[X,Y], T in Z[Y] irreducible. compute GCD in Q[Y]/(T)[X].
 *
 * M. Encarnacion "On a modular Algorithm for computing GCDs of polynomials
 * over number fields" (ISSAC'94).
 *
 * We procede as follows
 *  1:compute the gcd modulo primes discarding bad primes as they are detected.
 *  2:reconstruct the result via FpM_ratlift, stoping as soon as we get weird
 *    denominators.
 *  3:if FpM_ratlift succeeds, try the full division.
 * Suppose accuracy is insufficient to get the result right: FpM_ratlift will
 * rarely succeed, and even if it does the polynomial we get has sensible
 * coefficients, so the full division will not be too costly.
 *
 * If not NULL, den must be a multiple of the denominator of the gcd,
 * for example the discriminant of T.
 *
 * NOTE: if T is not irreducible, nfgcd may loop forever, esp. if gcd | T */
GEN
nfgcd_all(GEN P, GEN Q, GEN T, GEN den, GEN *Pnew)
{
  pari_sp btop, ltop = avma;
  GEN lP, lQ, M, dsol, R, bo, sol, mod = NULL, lden = NULL;
  long vP = varn(P), vT = varn(T), dT = degpol(T), dM = 0, dR;
  forprime_t S;

  if (!signe(P)) { if (Pnew) *Pnew = pol_0(vT); return gcopy(Q); }
  if (!signe(Q)) { if (Pnew) *Pnew = pol_1(vT);   return gcopy(P); }
  /* Compute denominators */
  if ((lP = lead_simplify(P)) && (lQ = lead_simplify(Q)))
  {
    if (typ(lP) == t_INT && typ(lQ) == t_INT)
      lden = powiu(gcdii(lP, lQ), dT);
    else if (typ(lP) == t_INT)
      lden = gcdii(powiu(lP, dT), ZX_resultant(lQ, T));
    else if (typ(lQ) == t_INT)
      lden = gcdii(powiu(lQ, dT), ZX_resultant(lP, T));
    else
      lden = gcdii(ZX_resultant(lP, T), ZX_resultant(lQ, T));
    if (is_pm1(lden)) lden = NULL;
    den = mul_denom(den, lden);
  }
  init_modular_small(&S);
  btop = avma;
  for(;;)
  {
    ulong p = u_forprime_next(&S);
    GEN Tp;
    if (!p) pari_err_OVERFLOW("nfgcd [ran out of primes]");
    /*Discard primes dividing disc(T) or lc(PQ) */
    if (lden && !umodiu(lden, p)) continue;
    Tp = ZX_to_Flx(T,p);
    if (!Flx_is_squarefree(Tp, p)) continue;
    /*Discard primes when modular gcd does not exist*/
    if ((R = FlxqX_safegcd(ZXX_to_FlxX(P,p,vT),
                           ZXX_to_FlxX(Q,p,vT),
                           Tp, p)) == NULL) continue;
    dR = degpol(R);
    if (dR == 0) { avma = ltop; if (Pnew) *Pnew = P; return pol_1(vP); }
    if (mod && dR > dM) continue; /* p divides Res(P/gcd, Q/gcd). Discard. */

    R = FlxX_to_Flm(R, dT);
    /* previous primes divided Res(P/gcd, Q/gcd)? Discard them. */
    if (!mod || dR < dM) { M = ZM_init_CRT(R, p); mod = utoipos(p); dM = dR; continue; }
    (void)ZM_incremental_CRT(&M,R, &mod,p);
    if (gc_needed(btop, 1))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"nfgcd");
      gerepileall(btop, 2, &M, &mod);
    }
    /* I suspect it must be better to take amax > bmax*/
    bo = sqrti(shifti(mod, -1));
    if ((sol = FpM_ratlift(M, mod, bo, bo, den)) == NULL) continue;
    sol = RgM_to_RgXX(sol,vP,vT);
    dsol = Q_primpart(sol);

    if (!ZXQX_dvd(Q, dsol, T)) continue;
    if (Pnew)
    {
      *Pnew = RgXQX_pseudodivrem(P, dsol, T, &R);
      if (signe(R)) continue;
    }
    else
    {
      if (!ZXQX_dvd(P, dsol, T)) continue;
    }
    gerepileall(ltop, Pnew? 2: 1, &dsol, Pnew);
    return dsol; /* both remainders are 0 */
  }
}
GEN
nfgcd(GEN P, GEN Q, GEN T, GEN den)
{ return nfgcd_all(P,Q,T,den,NULL); }

int
nfissquarefree(GEN nf, GEN x)
{
  pari_sp av = avma;
  GEN g, y = RgX_deriv(x);
  if (RgX_is_rational(x))
    g = QX_gcd(x, y);
  else
  {
    GEN T = get_nfpol(nf,&nf);
    x = Q_primpart( liftpol_shallow(x) );
    y = Q_primpart( liftpol_shallow(y) );
    g = nfgcd(x, y, T, nf? nf_get_index(nf): NULL);
  }
  avma = av; return (degpol(g) == 0);
}

/*******************************************************************/
/*             FACTOR OVER (Z_K/pr)[X] --> FqX_factor              */
/*******************************************************************/
GEN
nffactormod(GEN nf, GEN x, GEN pr)
{
  long j, l, vx = varn(x), vn;
  pari_sp av = avma;
  GEN F, E, rep, xrd, modpr, T, p;

  nf = checknf(nf);
  vn = nf_get_varn(nf);
  if (typ(x)!=t_POL) pari_err_TYPE("nffactormod",x);
  if (varncmp(vx,vn) >= 0) pari_err_PRIORITY("nffactormod", x, ">=", vn);

  modpr = nf_to_Fq_init(nf, &pr, &T, &p);
  xrd = nfX_to_FqX(x, nf, modpr);
  rep = FqX_factor(xrd,T,p);
  settyp(rep, t_MAT);
  F = gel(rep,1); l = lg(F);
  E = gel(rep,2); settyp(E, t_COL);
  for (j = 1; j < l; j++) {
    gel(F,j) = FqX_to_nfX(gel(F,j), modpr);
    gel(E,j) = stoi(E[j]);
  }
  return gerepilecopy(av, rep);
}

/*******************************************************************/
/*               MAIN ROUTINES nfroots / nffactor                  */
/*******************************************************************/
static GEN
QXQX_normalize(GEN P, GEN T)
{
  GEN P0 = leading_coeff(P);
  long t = typ(P0);
  if (t == t_POL)
  {
    if (degpol(P0)) return RgXQX_RgXQ_mul(P, QXQ_inv(P0,T), T);
    P0 = gel(P0,2); t = typ(P0);
  }
  /* t = t_INT/t_FRAC */
  if (t == t_INT && is_pm1(P0) && signe(P0) > 0) return P; /* monic */
  return RgX_Rg_div(P, P0);
}
/* assume leading term of P is an integer */
static GEN
RgX_int_normalize(GEN P)
{
  GEN P0 = leading_coeff(P);
  /* cater for t_POL */
  if (typ(P0) == t_POL)
  {
    P0 = gel(P0,2); /* non-0 constant */
    P = shallowcopy(P);
    gel(P,lg(P)-1) = P0; /* now leading term is a t_INT */
  }
  if (typ(P0) != t_INT) pari_err_BUG("RgX_int_normalize");
  if (is_pm1(P0)) return signe(P0) > 0? P: RgX_neg(P);
  return RgX_Rg_div(P, P0);
}

/* discard change of variable if nf is of the form [nf,c] as return by nfinit
 * for non-monic polynomials */
static GEN
proper_nf(GEN nf)
{ return (lg(nf) == 3)? gel(nf,1): nf; }

/* if *pnf = NULL replace if by a "quick" K = nfinit(T), ensuring maximality
 * by small primes only. Return a multiplicative bound for the denominator of
 * algebraic integers in Z_K in terms of K.zk */
static GEN
fix_nf(GEN *pnf, GEN *pT, GEN *pA)
{
  GEN nf, NF, fa, P, Q, q, D, T = *pT;
  nfmaxord_t S;
  long i, l;

  if (*pnf) return gen_1;
  nfmaxord(&S, T, nf_PARTIALFACT);
  NF = nfinit_complete(&S, 0, DEFAULTPREC);
  *pnf = nf = proper_nf(NF);
  if (nf != NF) { /* t_POL defining base field changed (not monic) */
    GEN A = *pA, a = cgetg_copy(A, &l);
    GEN rev = gel(NF,2), pow, dpow;

    *pT = T = nf_get_pol(nf); /* need to update T */
    pow = QXQ_powers(lift_shallow(rev), degpol(T)-1, T);
    pow = Q_remove_denom(pow, &dpow);
    a[1] = A[1];
    for (i=2; i<l; i++) {
      GEN c = gel(A,i);
      if (typ(c) == t_POL) c = QX_ZXQV_eval(c, pow, dpow);
      gel(a,i) = c;
    }
    *pA = Q_primpart(a); /* need to update A */
  }

  D = nf_get_disc(nf);
  if (is_pm1(D)) return gen_1;
  fa = absZ_factor_limit(D, 0);
  P = gel(fa,1); q = gel(P, lg(P)-1);
  if (BPSW_psp(q)) return gen_1;
  /* nf_get_disc(nf) may be incorrect */
  P = nf_get_ramified_primes(nf);
  l = lg(P);
  Q = q; q = gen_1;
  for (i = 1; i < l; i++)
  {
    GEN p = gel(P,i);
    if (Z_pvalrem(Q, p, &Q) && !BPSW_psp(p)) q = mulii(q, p);
  }
  return q;
}

/* lt(A) is an integer; ensure it is not a constant t_POL. In place */
static void
ensure_lt_INT(GEN A)
{
  long n = lg(A)-1;
  GEN lt = gel(A,n);
  while (typ(lt) != t_INT) gel(A,n) = lt = gel(lt,2);
}

/* set B = A/gcd(A,A'), squarefree */
static GEN
get_nfsqff_data(GEN *pnf, GEN *pT, GEN *pA, GEN *pB, GEN *ptbad)
{
  GEN den, bad, D, B, A = *pA, T = *pT;
  long n = degpol(T);

  A = Q_primpart( QXQX_normalize(A, T) );
  if (nfsqff_use_Trager(n, degpol(A)))
  {
    *pnf = T;
    bad = den = ZX_disc(T);
    if (is_pm1(leading_coeff(T))) den = indexpartial(T, den);
  }
  else
  {
    den = fix_nf(pnf, &T, &A);
    bad = nf_get_index(*pnf);
    if (den != gen_1) bad = mulii(bad, den);
  }
  D = nfgcd_all(A, RgX_deriv(A), T, bad, &B);
  if (degpol(D)) B = Q_primpart( QXQX_normalize(B, T) );
  if (ptbad) *ptbad = bad;
  *pA = A;
  *pB = B; ensure_lt_INT(B);
  *pT = T; return den;
}

/* return the roots of pol in nf */
GEN
nfroots(GEN nf,GEN pol)
{
  pari_sp av = avma;
  GEN z, A, B, T, den;
  long d, dT;

  if (!nf) return nfrootsQ(pol);
  T = get_nfpol(nf, &nf);
  RgX_check_ZX(T,"nfroots");
  A = RgX_nffix("nfroots", T,pol,1);
  d = degpol(A);
  if (d < 0) pari_err_ROOTS0("nfroots");
  if (d == 0) return cgetg(1,t_VEC);
  if (d == 1)
  {
    A = QXQX_normalize(A,T);
    A = mkpolmod(gneg_i(gel(A,2)), T);
    return gerepilecopy(av, mkvec(A));
  }
  dT = degpol(T);
  if (dT == 1) return gerepileupto(av, nfrootsQ(simplify_shallow(A)));

  den = get_nfsqff_data(&nf, &T, &A, &B, NULL);
  if (RgX_is_ZX(B))
  {
    GEN v = gel(ZX_factor(B), 1);
    long i, l = lg(v), p = mael(factoru(dT),1,1); /* smallest prime divisor */
    z = cgetg(1, t_VEC);
    for (i = 1; i < l; i++)
    {
      GEN b = gel(v,i); /* irreducible / Q */
      long db = degpol(b);
      if (db != 1 && degpol(b) < p) continue;
      z = shallowconcat(z, nfsqff(nf, b, ROOTS, den));
    }
  }
  else
    z = nfsqff(nf,B, ROOTS, den);
  z = gerepileupto(av, QXQV_to_mod(z, T));
  gen_sort_inplace(z, (void*)&cmp_RgX, &cmp_nodata, NULL);
  return z;
}

static GEN
_norml2(GEN x) { return RgC_fpnorml2(x, DEFAULTPREC); }

/* return a minimal lift of elt modulo id, as a ZC */
static GEN
nf_bestlift(GEN elt, GEN bound, nflift_t *L)
{
  GEN u;
  long i,l = lg(L->prk), t = typ(elt);
  if (t != t_INT)
  {
    if (t == t_POL) elt = ZM_ZX_mul(L->tozk, elt);
    u = ZM_ZC_mul(L->iprk,elt);
    for (i=1; i<l; i++) gel(u,i) = diviiround(gel(u,i), L->pk);
  }
  else
  {
    u = ZC_Z_mul(gel(L->iprk,1), elt);
    for (i=1; i<l; i++) gel(u,i) = diviiround(gel(u,i), L->pk);
    elt = scalarcol(elt, l-1);
  }
  u = ZC_sub(elt, ZM_ZC_mul(L->prk, u));
  if (bound && gcmp(_norml2(u), bound) > 0) u = NULL;
  return u;
}

/* Warning: return L->topowden * (best lift). */
static GEN
nf_bestlift_to_pol(GEN elt, GEN bound, nflift_t *L)
{
  pari_sp av = avma;
  GEN u,v = nf_bestlift(elt,bound,L);
  if (!v) return NULL;
  if (ZV_isscalar(v))
  {
    if (L->topowden)
      u = mulii(L->topowden, gel(v,1));
    else
      u = icopy(gel(v,1));
    u = gerepileuptoint(av, u);
  }
  else
  {
    v = gclone(v); avma = av;
    u = RgV_dotproduct(L->topow, v);
    gunclone(v);
  }
  return u;
}

/* return the T->powden * (lift of pol with coefficients of T2-norm <= C)
 * if it exists. */
static GEN
nf_pol_lift(GEN pol, GEN bound, nflift_t *L)
{
  long i, l = lg(pol);
  GEN x = cgetg(l,t_POL);

  x[1] = pol[1];
  gel(x,l-1) = mul_content(gel(pol,l-1), L->topowden);
  for (i=l-2; i>1; i--)
  {
    GEN t = nf_bestlift_to_pol(gel(pol,i), bound, L);
    if (!t) return NULL;
    gel(x,i) = t;
  }
  return x;
}

static GEN
zerofact(long v)
{
  GEN z = cgetg(3, t_MAT);
  gel(z,1) = mkcol(pol_0(v));
  gel(z,2) = mkcol(gen_1); return z;
}

/* Return the factorization of A in Q[X]/(T) in rep [pre-allocated with
 * cgetg(3,t_MAT)], reclaiming all memory between avma and rep.
 * y is the vector of irreducible factors of B = Q_primpart( A/gcd(A,A') ).
 * Bad primes divide 'bad' */
static void
fact_from_sqff(GEN rep, GEN A, GEN B, GEN y, GEN T, GEN bad)
{
  pari_sp av = (pari_sp)rep;
  long n = lg(y)-1;
  GEN ex;

  if (A != B)
  { /* not squarefree */
    if (n == 1)
    { /* perfect power, simple ! */
      long e = degpol(A) / degpol(gel(y,1));
      y = gerepileupto(av, QXQXV_to_mod(y, T));
      ex = mkcol(utoipos(e));
    }
    else
    { /* compute valuations mod a prime of degree 1 (avoid coeff explosion) */
      GEN quo, p, r, Bp, lb = leading_coeff(B), E = cgetalloc(t_VECSMALL,n+1);
      pari_sp av1 = avma;
      ulong pp;
      long j;
      forprime_t S;
      u_forprime_init(&S, degpol(T), ULONG_MAX);
      for (; ; avma = av1)
      {
        pp = u_forprime_next(&S);
        if (! umodiu(bad,pp) || !umodiu(lb, pp)) continue;
        p = utoipos(pp);
        r = FpX_oneroot(T, p);
        if (!r) continue;
        Bp = FpXY_evalx(B, r, p);
        if (FpX_is_squarefree(Bp, p)) break;
      }

      quo = FpXY_evalx(Q_primpart(A), r, p);
      for (j=n; j>=2; j--)
      {
        GEN junk, fact = Q_remove_denom(gel(y,j), &junk);
        long e = 0;
        fact = FpXY_evalx(fact, r, p);
        for(;; e++)
        {
          GEN q = FpX_divrem(quo,fact,p,ONLY_DIVIDES);
          if (!q) break;
          quo = q;
        }
        E[j] = e;
      }
      E[1] = degpol(quo) / degpol(gel(y,1));
      y = gerepileupto(av, QXQXV_to_mod(y, T));
      ex = zc_to_ZC(E); pari_free((void*)E);
    }
  }
  else
  {
    y = gerepileupto(av, QXQXV_to_mod(y, T));
    ex = const_col(n, gen_1);
  }
  gel(rep,1) = y; settyp(y, t_COL);
  gel(rep,2) = ex;
}

/* return the factorization of x in nf */
GEN
nffactor(GEN nf,GEN pol)
{
  GEN bad, A, B, y, T, den, rep = cgetg(3, t_MAT);
  pari_sp av = avma;
  long dA;
  pari_timer ti;

  if (DEBUGLEVEL>2) { timer_start(&ti); err_printf("\nEntering nffactor:\n"); }
  T = get_nfpol(nf, &nf);
  RgX_check_ZX(T,"nffactor");
  A = RgX_nffix("nffactor",T,pol,1);
  dA = degpol(A);
  if (dA <= 0) {
    avma = (pari_sp)(rep + 3);
    return (dA == 0)? trivial_fact(): zerofact(varn(pol));
  }
  if (dA == 1) {
    GEN c;
    A = Q_primpart( QXQX_normalize(A, T) );
    A = gerepilecopy(av, A); c = gel(A,2);
    if (typ(c) == t_POL && degpol(c) > 0) gel(A,2) = mkpolmod(c, ZX_copy(T));
    gel(rep,1) = mkcol(A);
    gel(rep,2) = mkcol(gen_1); return rep;
  }
  if (degpol(T) == 1) return gerepileupto(av, QX_factor(simplify_shallow(A)));

  den = get_nfsqff_data(&nf, &T, &A, &B, &bad);
  if (DEBUGLEVEL>2) timer_printf(&ti, "squarefree test");
  if (RgX_is_ZX(B))
  {
    GEN v = gel(ZX_factor(B), 1);
    long i, l = lg(v);
    y = cgetg(1, t_VEC);
    for (i = 1; i < l; i++)
    {
      GEN b = gel(v,i); /* irreducible / Q */
      y = shallowconcat(y, nfsqff(nf, b, 0, den));
    }
  }
  else
    y = nfsqff(nf,B, 0, den);
  if (DEBUGLEVEL>3) err_printf("number of factor(s) found: %ld\n", lg(y)-1);

  fact_from_sqff(rep, A, B, y, T, bad);
  return sort_factor_pol(rep, cmp_RgX);
}

/* assume x scalar or t_COL, G t_MAT */
static GEN
arch_for_T2(GEN G, GEN x)
{
  return (typ(x) == t_COL)? RgM_RgC_mul(G,x)
                          : RgC_Rg_mul(gel(G,1),x);
}

/* polbase a zkX with t_INT leading coeff; return a bound for T_2(P),
 * P | polbase in C[X]. NB: Mignotte bound: A | S ==>
 *  |a_i| <= binom(d-1, i-1) || S ||_2 + binom(d-1, i) lc(S)
 *
 * Apply to sigma(S) for all embeddings sigma, then take the L_2 norm over
 * sigma, then take the sup over i */
static GEN
nf_Mignotte_bound(GEN nf, GEN polbase)
{ GEN lS = leading_coeff(polbase); /* t_INT */
  GEN p1, C, N2, binlS, bin;
  long prec = nf_get_prec(nf), n = nf_get_degree(nf), r1 = nf_get_r1(nf);
  long i, j, d = degpol(polbase);

  binlS = bin = vecbinomial(d-1);
  if (!isint1(lS)) binlS = ZC_Z_mul(bin,lS);

  N2 = cgetg(n+1, t_VEC);
  for (;;)
  {
    GEN G = nf_get_G(nf), matGS = cgetg(d+2, t_MAT);

    for (j=0; j<=d; j++) gel(matGS,j+1) = arch_for_T2(G, gel(polbase,j+2));
    matGS = shallowtrans(matGS);
    for (j=1; j <= r1; j++) /* N2[j] = || sigma_j(S) ||_2 */
    {
      GEN c = sqrtr( _norml2(gel(matGS,j)) );
      gel(N2,j) = c; if (!signe(c)) goto PRECPB;
    }
    for (   ; j <= n; j+=2)
    {
      GEN q1 = _norml2(gel(matGS, j));
      GEN q2 = _norml2(gel(matGS, j+1));
      GEN c = sqrtr( gmul2n(addrr(q1, q2), -1) );
      gel(N2,j) = gel(N2,j+1) = c; if (!signe(c)) goto PRECPB;
    }
    break; /* done */
PRECPB:
    prec = precdbl(prec);
    nf = nfnewprec_shallow(nf, prec);
    if (DEBUGLEVEL>1) pari_warn(warnprec, "nf_factor_bound", prec);
  }

  /* Take sup over 0 <= i <= d of
   * sum_j | binom(d-1, i-1) ||sigma_j(S)||_2 + binom(d-1,i) lc(S) |^2 */

  /* i = 0: n lc(S)^2 */
  C = mului(n, sqri(lS));
  /* i = d: sum_sigma ||sigma(S)||_2^2 */
  p1 = gnorml2(N2); if (gcmp(C, p1) < 0) C = p1;
  for (i = 1; i < d; i++)
  {
    GEN B = gel(bin,i), L = gel(binlS,i+1);
    GEN s = sqrr(addri(mulir(B, gel(N2,1)),  L)); /* j=1 */
    for (j = 2; j <= n; j++) s = addrr(s, sqrr(addri(mulir(B, gel(N2,j)), L)));
    if (mpcmp(C, s) < 0) C = s;
  }
  return C;
}

/* return a bound for T_2(P), P | polbase
 * max |b_i|^2 <= 3^{3/2 + d} / (4 \pi d) [P]_2,
 * where [P]_2 is Bombieri's 2-norm
 * Sum over conjugates */
static GEN
nf_Beauzamy_bound(GEN nf, GEN polbase)
{
  GEN lt, C, s, POL, bin;
  long d = degpol(polbase), n = nf_get_degree(nf), prec = nf_get_prec(nf);
  bin = vecbinomial(d);
  POL = polbase + 2;
  /* compute [POL]_2 */
  for (;;)
  {
    GEN G = nf_get_G(nf);
    long i;

    s = real_0(prec);
    for (i=0; i<=d; i++)
    {
      GEN c = gel(POL,i);
      if (gequal0(c)) continue;
      c = _norml2(arch_for_T2(G,c));
      if (!signe(c)) goto PRECPB;
      /* s += T2(POL[i]) / binomial(d,i) */
      s = addrr(s, divri(c, gel(bin,i+1)));
    }
    break;
PRECPB:
    prec = precdbl(prec);
    nf = nfnewprec_shallow(nf, prec);
    if (DEBUGLEVEL>1) pari_warn(warnprec, "nf_factor_bound", prec);
  }
  lt = leading_coeff(polbase);
  s = mulri(s, muliu(sqri(lt), n));
  C = powruhalf(stor(3,DEFAULTPREC), 3 + 2*d); /* 3^{3/2 + d} */
  return divrr(mulrr(C, s), mulur(d, mppi(DEFAULTPREC)));
}

static GEN
nf_factor_bound(GEN nf, GEN polbase)
{
  pari_sp av = avma;
  GEN a = nf_Mignotte_bound(nf, polbase);
  GEN b = nf_Beauzamy_bound(nf, polbase);
  if (DEBUGLEVEL>2)
  {
    err_printf("Mignotte bound: %Ps\n",a);
    err_printf("Beauzamy bound: %Ps\n",b);
  }
  return gerepileupto(av, gmin(a, b));
}

/* True nf; return Bs: if r a root of sigma_i(P), |r| < Bs[i] */
static GEN
nf_root_bounds(GEN nf, GEN P)
{
  long lR, i, j, l, prec, r1;
  GEN Ps, R, V;

  if (RgX_is_rational(P)) return polrootsbound(P, NULL);
  r1 = nf_get_r1(nf);
  P = Q_primpart(P);
  prec = ZXX_max_lg(P) + 1;
  l = lg(P);
  if (nf_get_prec(nf) >= prec)
    R = nf_get_roots(nf);
  else
    R = QX_complex_roots(nf_get_pol(nf), prec);
  lR = lg(R);
  V = cgetg(lR, t_VEC);
  Ps = cgetg(l, t_POL); /* sigma (P) */
  Ps[1] = P[1];
  for (j=1; j<lg(R); j++)
  {
    GEN r = gel(R,j);
    for (i=2; i<l; i++) gel(Ps,i) = poleval(gel(P,i), r);
    gel(V,j) = polrootsbound(Ps, NULL);
  }
  return mkvec2(vecslice(V,1,r1), vecslice(V,r1+1,lg(V)-1));
}

/* return B such that, if x = sum x_i K.zk[i] in O_K, then ||x||_2^2 <= B T_2(x)
 * den = multiplicative bound for denom(x) [usually NULL, for 1, but when we
 * use nf_PARTIALFACT K.zk may not generate O_K] */
static GEN
L2_bound(GEN nf, GEN den)
{
  GEN M, L, prep, T = nf_get_pol(nf), tozk = nf_get_invzk(nf);
  long prec = ZM_max_lg(tozk) + ZX_max_lg(T) + nbits2prec(degpol(T));
  (void)initgaloisborne(nf, den? den: gen_1, prec, &L, &prep, NULL);
  M = vandermondeinverse(L, RgX_gtofp(T,prec), den, prep);
  return RgM_fpnorml2(RgM_mul(tozk,M), DEFAULTPREC);
}

/* sum_i L[i]^p */
static GEN
normlp(GEN L, long p)
{
  long i, l = lg(L);
  GEN z;
  if (l == 1) return gen_0;
  z = gpowgs(gel(L,1), p);
  for (i=2; i<l; i++) z = gadd(z, gpowgs(gel(L,i), p));
  return z;
}
/* \sum_i deg(sigma_i) L[i]^p in dimension n (L may be a scalar
 * or [L1,L2], where Ld corresponds to the archimedean places of degree d) */
static GEN
normTp(GEN L, long p, long n)
{
  if (typ(L) != t_VEC) return gmulsg(n, gpowgs(L, p));
  return gadd(normlp(gel(L,1),p), gmul2n(normlp(gel(L,2),p), 1));
}

/* S = S0 + tS1, P = P0 + tP1 (Euclidean div. by t integer). For a true
 * factor (vS, vP), we have:
 *    | S vS + P vP |^2 < Btra
 * This implies | S1 vS + P1 vP |^2 < Bhigh, assuming t > sqrt(Btra).
 * d = dimension of low part (= [nf:Q])
 * n0 = bound for |vS|^2
 * */
static double
get_Bhigh(long n0, long d)
{
  double sqrtd = sqrt((double)d);
  double z = n0*sqrtd + sqrtd/2 * (d * (n0+1));
  z = 1. + 0.5 * z; return z * z;
}

typedef struct {
  GEN d;
  GEN dPinvS;   /* d P^(-1) S   [ integral ] */
  double **PinvSdbl; /* P^(-1) S as double */
  GEN S1, P1;   /* S = S0 + S1 q, idem P */
} trace_data;

/* S1 * u - P1 * round(P^-1 S u). K non-zero coords in u given by ind */
static GEN
get_trace(GEN ind, trace_data *T)
{
  long i, j, l, K = lg(ind)-1;
  GEN z, s, v;

  s = gel(T->S1, ind[1]);
  if (K == 1) return s;

  /* compute s = S1 u */
  for (j=2; j<=K; j++) s = ZC_add(s, gel(T->S1, ind[j]));

  /* compute v := - round(P^1 S u) */
  l = lg(s);
  v = cgetg(l, t_VECSMALL);
  for (i=1; i<l; i++)
  {
    double r, t = 0.;
    /* quick approximate computation */
    for (j=1; j<=K; j++) t += T->PinvSdbl[ ind[j] ][i];
    r = floor(t + 0.5);
    if (fabs(t + 0.5 - r) < 0.0001)
    { /* dubious, compute exactly */
      z = gen_0;
      for (j=1; j<=K; j++) z = addii(z, ((GEN**)T->dPinvS)[ ind[j] ][i]);
      v[i] = - itos( diviiround(z, T->d) );
    }
    else
      v[i] = - (long)r;
  }
  return ZC_add(s, ZM_zc_mul(T->P1, v));
}

static trace_data *
init_trace(trace_data *T, GEN S, nflift_t *L, GEN q)
{
  long e = gexpo(S), i,j, l,h;
  GEN qgood, S1, invd;

  if (e < 0) return NULL; /* S = 0 */

  qgood = int2n(e - 32); /* single precision check */
  if (cmpii(qgood, q) > 0) q = qgood;

  S1 = gdivround(S, q);
  if (gequal0(S1)) return NULL;

  invd = invr(itor(L->pk, DEFAULTPREC));

  T->dPinvS = ZM_mul(L->iprk, S);
  l = lg(S);
  h = lgcols(T->dPinvS);
  T->PinvSdbl = (double**)cgetg(l, t_MAT);
  for (j = 1; j < l; j++)
  {
    double *t = (double *) stack_malloc_align(h * sizeof(double), sizeof(double));
    GEN c = gel(T->dPinvS,j);
    pari_sp av = avma;
    T->PinvSdbl[j] = t;
    for (i=1; i < h; i++) t[i] = rtodbl(mulri(invd, gel(c,i)));
    avma = av;
  }

  T->d  = L->pk;
  T->P1 = gdivround(L->prk, q);
  T->S1 = S1; return T;
}

static void
update_trace(trace_data *T, long k, long i)
{
  if (!T) return;
  gel(T->S1,k)     = gel(T->S1,i);
  gel(T->dPinvS,k) = gel(T->dPinvS,i);
  T->PinvSdbl[k]   = T->PinvSdbl[i];
}

/* reduce coeffs mod (T,pk), then center mod pk */
static GEN
FqX_centermod(GEN z, GEN T, GEN pk, GEN pks2)
{
  long i, l;
  GEN y;
  if (!T) return centermod_i(z, pk, pks2);
  y = FpXQX_red(z, T, pk); l = lg(y);
  for (i = 2; i < l; i++)
  {
    GEN c = gel(y,i);
    if (typ(c) == t_INT)
      c = Fp_center_i(c, pk, pks2);
    else
      c = FpX_center_i(c, pk, pks2);
    gel(y,i) = c;
  }
  return y;
}

typedef struct {
  GEN lt, C, Clt, C2lt, C2ltpol;
} div_data;

static void
init_div_data(div_data *D, GEN pol, nflift_t *L)
{
  GEN C2lt, Clt, C = mul_content(L->topowden, L->dn);
  GEN lc = leading_coeff(pol), lt = is_pm1(lc)? NULL: absi_shallow(lc);
  if (C)
  {
    GEN C2 = sqri(C);
    if (lt) {
      C2lt = mulii(C2, lt);
      Clt = mulii(C,lt);
    } else {
      C2lt = C2;
      Clt = C;
    }
  }
  else
    C2lt = Clt = lt;
  D->lt = lt;
  D->C = C;
  D->Clt = Clt;
  D->C2lt = C2lt;
  D->C2ltpol = C2lt? RgX_Rg_mul(pol, C2lt): pol;
}
static void
update_target(div_data *D, GEN pol)
{ D->C2ltpol = D->Clt? RgX_Rg_mul(pol, D->Clt): pol; }

/* nb = number of modular factors; return a "good" K such that naive
 * recombination of up to maxK modular factors is not too costly */
long
cmbf_maxK(long nb)
{
  if (nb >  10) return 3;
  return nb-1;
}
/* Naive recombination of modular factors: combine up to maxK modular
 * factors, degree <= klim
 *
 * target = polynomial we want to factor
 * famod = array of modular factors.  Product should be congruent to
 * target/lc(target) modulo p^a
 * For true factors: S1,S2 <= p^b, with b <= a and p^(b-a) < 2^31 */
/* set *done = 1 if factorisation is known to be complete */
static GEN
nfcmbf(nfcmbf_t *T, long klim, long *pmaxK, int *done)
{
  GEN nf = T->nf, famod = T->fact, bound = T->bound;
  GEN ltdn, nfpol = nf_get_pol(nf);
  long K = 1, cnt = 1, i,j,k, curdeg, lfamod = lg(famod)-1, dnf = degpol(nfpol);
  pari_sp av0 = avma;
  GEN Tpk = T->L->Tpk, pk = T->L->pk, pks2 = shifti(pk,-1);
  GEN ind      = cgetg(lfamod+1, t_VECSMALL);
  GEN deg      = cgetg(lfamod+1, t_VECSMALL);
  GEN degsofar = cgetg(lfamod+1, t_VECSMALL);
  GEN fa       = cgetg(lfamod+1, t_VEC);
  const double Bhigh = get_Bhigh(lfamod, dnf);
  trace_data _T1, _T2, *T1, *T2;
  div_data D;
  pari_timer ti;

  timer_start(&ti);

  *pmaxK = cmbf_maxK(lfamod);
  init_div_data(&D, T->pol, T->L);
  ltdn = mul_content(D.lt, T->L->dn);
  {
    GEN q = ceil_safe(sqrtr(T->BS_2));
    GEN t1,t2, lt2dn = mul_content(ltdn, D.lt);
    GEN trace1   = cgetg(lfamod+1, t_MAT);
    GEN trace2   = cgetg(lfamod+1, t_MAT);
    for (i=1; i <= lfamod; i++)
    {
      pari_sp av = avma;
      GEN P = gel(famod,i);
      long d = degpol(P);

      deg[i] = d; P += 2;
      t1 = gel(P,d-1);/* = - S_1 */
      t2 = Fq_sqr(t1, Tpk, pk);
      if (d > 1) t2 = Fq_sub(t2, gmul2n(gel(P,d-2), 1), Tpk, pk);
      /* t2 = S_2 Newton sum */
      if (ltdn)
      {
        t1 = Fq_Fp_mul(t1, ltdn, Tpk, pk);
        t2 = Fq_Fp_mul(t2, lt2dn, Tpk, pk);
      }
      gel(trace1,i) = gclone( nf_bestlift(t1, NULL, T->L) );
      gel(trace2,i) = gclone( nf_bestlift(t2, NULL, T->L) ); avma = av;
    }
    T1 = init_trace(&_T1, trace1, T->L, q);
    T2 = init_trace(&_T2, trace2, T->L, q);
    for (i=1; i <= lfamod; i++) {
      gunclone(gel(trace1,i));
      gunclone(gel(trace2,i));
    }
  }
  degsofar[0] = 0; /* sentinel */

  /* ind runs through strictly increasing sequences of length K,
   * 1 <= ind[i] <= lfamod */
nextK:
  if (K > *pmaxK || 2*K > lfamod) goto END;
  if (DEBUGLEVEL > 3)
    err_printf("\n### K = %d, %Ps combinations\n", K,binomial(utoipos(lfamod), K));
  setlg(ind, K+1); ind[1] = 1;
  i = 1; curdeg = deg[ind[1]];
  for(;;)
  { /* try all combinations of K factors */
    for (j = i; j < K; j++)
    {
      degsofar[j] = curdeg;
      ind[j+1] = ind[j]+1; curdeg += deg[ind[j+1]];
    }
    if (curdeg <= klim) /* trial divide */
    {
      GEN t, y, q;
      pari_sp av;

      av = avma;
      if (T1)
      { /* d-1 test */
        t = get_trace(ind, T1);
        if (rtodbl(_norml2(t)) > Bhigh)
        {
          if (DEBUGLEVEL>6) err_printf(".");
          avma = av; goto NEXT;
        }
      }
      if (T2)
      { /* d-2 test */
        t = get_trace(ind, T2);
        if (rtodbl(_norml2(t)) > Bhigh)
        {
          if (DEBUGLEVEL>3) err_printf("|");
          avma = av; goto NEXT;
        }
      }
      avma = av;
      y = ltdn; /* full computation */
      for (i=1; i<=K; i++)
      {
        GEN q = gel(famod, ind[i]);
        if (y) q = gmul(y, q);
        y = FqX_centermod(q, Tpk, pk, pks2);
      }
      y = nf_pol_lift(y, bound, T->L);
      if (!y)
      {
        if (DEBUGLEVEL>3) err_printf("@");
        avma = av; goto NEXT;
      }
      /* y = topowden*dn*lt*\prod_{i in ind} famod[i] is apparently in O_K[X],
       * in fact in (Z[Y]/nf.pol)[X] due to multiplication by C = topowden*dn.
       * Try out this candidate factor */
      q = RgXQX_divrem(D.C2ltpol, y, nfpol, ONLY_DIVIDES);
      if (!q)
      {
        if (DEBUGLEVEL>3) err_printf("*");
        avma = av; goto NEXT;
      }
      /* Original T->pol in O_K[X] with leading coeff lt in Z,
       * y = C*lt \prod famod[i] is in O_K[X] with leading coeff in Z
       * q = C^2*lt*pol / y = C * (lt*pol) / (lt*\prod famod[i]) is a
       * K-rational factor, in fact in Z[Y]/nf.pol)[X] as above, with
       * leading term C*lt. */
      update_target(&D, q);
      gel(fa,cnt++) = D.C2lt? RgX_int_normalize(y): y; /* make monic */
      for (i=j=k=1; i <= lfamod; i++)
      { /* remove used factors */
        if (j <= K && i == ind[j]) j++;
        else
        {
          gel(famod,k) = gel(famod,i);
          update_trace(T1, k, i);
          update_trace(T2, k, i);
          deg[k] = deg[i]; k++;
        }
      }
      lfamod -= K;
      *pmaxK = cmbf_maxK(lfamod);
      if (lfamod < 2*K) goto END;
      i = 1; curdeg = deg[ind[1]];
      if (DEBUGLEVEL > 2)
      {
        err_printf("\n"); timer_printf(&ti, "to find factor %Ps",gel(fa,cnt-1));
        err_printf("remaining modular factor(s): %ld\n", lfamod);
      }
      continue;
    }

NEXT:
    for (i = K+1;;)
    {
      if (--i == 0) { K++; goto nextK; }
      if (++ind[i] <= lfamod - K + i)
      {
        curdeg = degsofar[i-1] + deg[ind[i]];
        if (curdeg <= klim) break;
      }
    }
  }
END:
  *done = 1;
  if (degpol(D.C2ltpol) > 0)
  { /* leftover factor */
    GEN q = D.C2ltpol;
    if (D.C2lt) q = RgX_int_normalize(q);
    if (lfamod >= 2*K)
    { /* restore leading coefficient [#930] */
      if (D.lt) q = RgX_Rg_mul(q, D.lt);
      *done = 0; /* ... may still be reducible */
    }
    setlg(famod, lfamod+1);
    gel(fa,cnt++) = q;
  }
  if (DEBUGLEVEL>6) err_printf("\n");
  setlg(fa, cnt);
  return gerepilecopy(av0, fa);
}

static GEN
nf_chk_factors(nfcmbf_t *T, GEN P, GEN M_L, GEN famod, GEN pk)
{
  GEN nf = T->nf, bound = T->bound;
  GEN nfT = nf_get_pol(nf);
  long i, r;
  GEN pol = P, list, piv, y;
  GEN Tpk = T->L->Tpk;
  div_data D;

  piv = ZM_hnf_knapsack(M_L);
  if (!piv) return NULL;
  if (DEBUGLEVEL>3) err_printf("ZM_hnf_knapsack output:\n%Ps\n",piv);

  r  = lg(piv)-1;
  list = cgetg(r+1, t_VEC);
  init_div_data(&D, pol, T->L);
  for (i = 1;;)
  {
    pari_sp av = avma;
    if (DEBUGLEVEL) err_printf("nf_LLL_cmbf: checking factor %ld\n", i);
    y = chk_factors_get(D.lt, famod, gel(piv,i), Tpk, pk);

    if (! (y = nf_pol_lift(y, bound, T->L)) ) return NULL;
    y = gerepilecopy(av, y);
    /* y is the candidate factor */
    pol = RgXQX_divrem(D.C2ltpol, y, nfT, ONLY_DIVIDES);
    if (!pol) return NULL;

    if (D.C2lt) y = RgX_int_normalize(y);
    gel(list,i) = y;
    if (++i >= r) break;

    update_target(&D, pol);
  }
  gel(list,i) = RgX_int_normalize(pol); return list;
}

static GEN
nf_to_Zq(GEN x, GEN T, GEN pk, GEN pks2, GEN proj)
{
  GEN y;
  if (typ(x) != t_COL) return centermodii(x, pk, pks2);
  if (!T)
  {
    y = ZV_dotproduct(proj, x);
    return centermodii(y, pk, pks2);
  }
  y = ZM_ZC_mul(proj, x);
  y = RgV_to_RgX(y, varn(T));
  return FpX_center_i(FpX_rem(y, T, pk), pk, pks2);
}

/* Assume P in nfX form, lc(P) != 0 mod p. Reduce P to Zp[X]/(T) mod p^a */
static GEN
ZqX(GEN P, GEN pk, GEN T, GEN proj)
{
  long i, l = lg(P);
  GEN z, pks2 = shifti(pk,-1);

  z = cgetg(l,t_POL); z[1] = P[1];
  for (i=2; i<l; i++) gel(z,i) = nf_to_Zq(gel(P,i),T,pk,pks2,proj);
  return normalizepol_lg(z, l);
}

static GEN
ZqX_normalize(GEN P, GEN lt, nflift_t *L)
{
  GEN R = lt? RgX_Rg_mul(P, Fp_inv(lt, L->pk)): P;
  return ZqX(R, L->pk, L->Tpk, L->ZqProj);
}

/* k allowing to reconstruct x, |x|^2 < C, from x mod pr^k */
/* return log [  2sqrt(C/d) * ( (3/2)sqrt(gamma) )^(d-1) ] ^d / log N(pr)
 * cf. Belabas relative van Hoeij algorithm, lemma 3.12 */
static double
bestlift_bound(GEN C, long d, double alpha, GEN p, long f)
{
  const double g = 1 / (alpha - 0.25); /* = 2 if alpha = 3/4 */
  GEN C4 = shiftr(gtofp(C,DEFAULTPREC), 2);
  double t, logp = log(gtodouble(p));
  if (f == d)
  { /* p inert, no LLL fudge factor: p^(2k) / 4 > C */
    t = 0.5 * rtodbl(mplog(C4));
    return ceil(t / logp);
  }
  /* (1/2)log (4C/d) + (d-1)(log 3/2 sqrt(gamma)) */
  t = 0.5 * rtodbl(mplog(divru(C4,d))) + (d-1) * log(1.5 * sqrt(g));
  return ceil((t * d) / (logp * f));
}

static GEN
get_R(GEN M)
{
  GEN R;
  long i, l, prec = nbits2prec( gexpo(M) + 64 );

  for(;;)
  {
    R = gaussred_from_QR(M, prec);
    if (R) break;
    prec = precdbl(prec);
  }
  l = lg(R);
  for (i=1; i<l; i++) gcoeff(R,i,i) = gen_1;
  return R;
}

static void
init_proj(nflift_t *L, GEN prkHNF, GEN nfT)
{
  if (degpol(L->Tp)>1)
  {
    GEN coTp = FpX_div(FpX_red(nfT, L->p), L->Tp,  L->p); /* Tp's cofactor */
    GEN z, proj;
    z = ZpX_liftfact(nfT, mkvec2(L->Tp, coTp), L->pk, L->p, L->k);
    L->Tpk = gel(z,1);
    proj = QXQV_to_FpM(L->topow, L->Tpk, L->pk);
    if (L->topowden)
      proj = FpM_red(ZM_Z_mul(proj, Fp_inv(L->topowden, L->pk)), L->pk);
    L->ZqProj = proj;
  }
  else
  {
    L->Tpk = NULL;
    L->ZqProj = dim1proj(prkHNF);
  }
}

/* Square of the radius of largest ball inscript in PRK's fundamental domain,
 *   whose orthogonalized vector's norms are the Bi
 * Rmax ^2 =  min 1/4T_i where T_i = sum_j ( s_ij^2 / B_j)
 * For p inert, S = Id, T_i = 1 / p^{2k} and Rmax = p^k / 2 */
static GEN
max_radius(GEN PRK, GEN B)
{
  GEN S, smax = gen_0;
  pari_sp av = avma;
  long i, j, d = lg(PRK)-1;

  S = RgM_inv( get_R(PRK) ); if (!S) pari_err_PREC("max_radius");
  for (i=1; i<=d; i++)
  {
    GEN s = gen_0;
    for (j=1; j<=d; j++)
      s = mpadd(s, mpdiv( mpsqr(gcoeff(S,i,j)), gel(B,j)));
    if (mpcmp(s, smax) > 0) smax = s;
  }
  return gerepileupto(av, ginv(gmul2n(smax, 2)));
}

static void
bestlift_init(long a, GEN nf, GEN C, nflift_t *L)
{
  const double alpha = 0.99; /* LLL parameter */
  const long d = nf_get_degree(nf);
  pari_sp av = avma, av2;
  GEN prk, PRK, iPRK, GSmin, T = L->Tp, p = L->p;
  long f = degpol(T);
  pari_timer ti;

  if (f == d)
  { /* inert p, much simpler */
    long a0 = bestlift_bound(C, d, alpha, p, f);
    GEN q;
    if (a < a0) a = a0; /* guarantees GSmin >= C */
    if (DEBUGLEVEL>2) err_printf("exponent %ld\n",a);
    q = powiu(p,a);
    PRK = prk = scalarmat_shallow(q, d);
    GSmin = shiftr(itor(q, DEFAULTPREC), -1);
    iPRK = matid(d); goto END;
  }
  timer_start(&ti);
  if (!a) a = (long)bestlift_bound(C, d, alpha, p, f);
  for (;; avma = av, a += (a==1)? 1: (a>>1)) /* roughly a *= 1.5 */
  {
    GEN B, q = powiu(p,a), Tq = FpXQ_powu(T, a, FpX_red(nf_get_pol(nf), q), q);
    if (DEBUGLEVEL>2) err_printf("exponent %ld\n",a);
    prk = idealhnf_two(nf, mkvec2(q, Tq));
    av2 = avma;
    PRK = ZM_lll_norms(prk, alpha, LLL_INPLACE, &B);
    GSmin = max_radius(PRK, B);
    if (gcmp(GSmin, C) >= 0) break;
  }
  gerepileall(av2, 2, &PRK, &GSmin);
  iPRK = ZM_inv(PRK, NULL);
  if (DEBUGLEVEL>2)
    err_printf("for this exponent, GSmin = %Ps\nTime reduction: %ld\n",
               GSmin, timer_delay(&ti));
END:
  L->k = a;
  L->pk = gcoeff(prk,1,1);
  L->prk = PRK;
  L->iprk = iPRK;
  L->GSmin= GSmin;
  init_proj(L, prk, nf_get_pol(nf));
}

/* Let X = Tra * M_L, Y = bestlift(X) return V s.t Y = X - PRK V
 * and set *eT2 = gexpo(Y)  [cf nf_bestlift, but memory efficient] */
static GEN
get_V(GEN Tra, GEN M_L, GEN PRK, GEN PRKinv, GEN pk, long *eT2)
{
  long i, e = 0, l = lg(M_L);
  GEN V = cgetg(l, t_MAT);
  *eT2 = 0;
  for (i = 1; i < l; i++)
  { /* cf nf_bestlift(Tra * c) */
    pari_sp av = avma, av2;
    GEN v, T2 = ZM_ZC_mul(Tra, gel(M_L,i));

    v = gdivround(ZM_ZC_mul(PRKinv, T2), pk); /* small */
    av2 = avma;
    T2 = ZC_sub(T2, ZM_ZC_mul(PRK, v));
    e = gexpo(T2); if (e > *eT2) *eT2 = e;
    avma = av2;
    gel(V,i) = gerepileupto(av, v); /* small */
  }
  return V;
}

static GEN
nf_LLL_cmbf(nfcmbf_t *T, long rec)
{
  const double BitPerFactor = 0.4; /* nb bits / modular factor */
  nflift_t *L = T->L;
  GEN famod = T->fact, ZC = T->ZC, Br = T->Br, P = T->pol, dn = T->L->dn;
  long dnf = nf_get_degree(T->nf), dP = degpol(P);
  long i, C, tmax, n0;
  GEN lP, Bnorm, Tra, T2, TT, CM_L, m, list, ZERO, Btra;
  double Bhigh;
  pari_sp av, av2;
  long ti_LLL = 0, ti_CF = 0;
  pari_timer ti2, TI;

  lP = absi_shallow(leading_coeff(P));
  if (is_pm1(lP)) lP = NULL;

  n0 = lg(famod) - 1;
 /* Lattice: (S PRK), small vector (vS vP). To find k bound for the image,
  * write S = S1 q + S0, P = P1 q + P0
  * |S1 vS + P1 vP|^2 <= Bhigh for all (vS,vP) assoc. to true factors */
  Btra = mulrr(ZC, mulur(dP*dP, normTp(Br, 2, dnf)));
  Bhigh = get_Bhigh(n0, dnf);
  C = (long)ceil(sqrt(Bhigh/n0)) + 1; /* C^2 n0 ~ Bhigh */
  Bnorm = dbltor( n0 * C * C + Bhigh );
  ZERO = zeromat(n0, dnf);

  av = avma;
  TT = const_vec(n0, NULL);
  Tra  = cgetg(n0+1, t_MAT);
  CM_L = scalarmat_s(C, n0);
  /* tmax = current number of traces used (and computed so far) */
  for(tmax = 0;; tmax++)
  {
    long a, b, bmin, bgood, delta, tnew = tmax + 1, r = lg(CM_L)-1;
    GEN M_L, q, CM_Lp, oldCM_L, S1, P1, VV;
    int first = 1;

    /* bound for f . S_k(genuine factor) = ZC * bound for T_2(S_tnew) */
    Btra = mulrr(ZC, mulur(dP*dP, normTp(Br, 2*tnew, dnf)));
    bmin = logint(ceil_safe(sqrtr(Btra)), gen_2) + 1;
    if (DEBUGLEVEL>2)
      err_printf("\nLLL_cmbf: %ld potential factors (tmax = %ld, bmin = %ld)\n",
                 r, tmax, bmin);

    /* compute Newton sums (possibly relifting first) */
    if (gcmp(L->GSmin, Btra) < 0)
    {
      GEN polred;

      bestlift_init((L->k)<<1, T->nf, Btra, L);
      polred = ZqX_normalize(T->polbase, lP, L);
      famod = ZqX_liftfact(polred, famod, L->Tpk, L->pk, L->p, L->k);
      for (i=1; i<=n0; i++) gel(TT,i) = NULL;
    }
    for (i=1; i<=n0; i++)
    {
      GEN h, lPpow = lP? powiu(lP, tnew): NULL;
      GEN z = polsym_gen(gel(famod,i), gel(TT,i), tnew, L->Tpk, L->pk);
      gel(TT,i) = z;
      h = gel(z,tnew+1);
      /* make Newton sums integral */
      lPpow = mul_content(lPpow, dn);
      if (lPpow)
        h = (typ(h) == t_INT)? Fp_mul(h, lPpow, L->pk): FpX_Fp_mul(h, lPpow, L->pk);
      gel(Tra,i) = nf_bestlift(h, NULL, L); /* S_tnew(famod) */
    }

    /* compute truncation parameter */
    if (DEBUGLEVEL>2) { timer_start(&ti2); timer_start(&TI); }
    oldCM_L = CM_L;
    av2 = avma;
    b = delta = 0; /* -Wall */
AGAIN:
    M_L = Q_div_to_int(CM_L, utoipos(C));
    VV = get_V(Tra, M_L, L->prk, L->iprk, L->pk, &a);
    if (first)
    { /* initialize lattice, using few p-adic digits for traces */
      bgood = (long)(a - maxss(32, (long)(BitPerFactor * r)));
      b = maxss(bmin, bgood);
      delta = a - b;
    }
    else
    { /* add more p-adic digits and continue reduction */
      if (a < b) b = a;
      b = maxss(b-delta, bmin);
      if (b - delta/2 < bmin) b = bmin; /* near there. Go all the way */
    }

    /* restart with truncated entries */
    q = int2n(b);
    P1 = gdivround(L->prk, q);
    S1 = gdivround(Tra, q);
    T2 = ZM_sub(ZM_mul(S1, M_L), ZM_mul(P1, VV));
    m = vconcat( CM_L, T2 );
    if (first)
    {
      first = 0;
      m = shallowconcat( m, vconcat(ZERO, P1) );
      /*     [ C M_L   0  ]
       * m = [            ]   square matrix
       *     [  T2'   PRK ]   T2' = Tra * M_L  truncated
       */
    }
    CM_L = LLL_check_progress(Bnorm, n0, m, b == bmin, /*dbg:*/ &ti_LLL);
    if (DEBUGLEVEL>2)
      err_printf("LLL_cmbf: (a,b) =%4ld,%4ld; r =%3ld -->%3ld, time = %ld\n",
                 a,b, lg(m)-1, CM_L? lg(CM_L)-1: 1, timer_delay(&TI));
    if (!CM_L) { list = mkcol(RgX_int_normalize(P)); break; }
    if (b > bmin)
    {
      CM_L = gerepilecopy(av2, CM_L);
      goto AGAIN;
    }
    if (DEBUGLEVEL>2) timer_printf(&ti2, "for this trace");

    i = lg(CM_L) - 1;
    if (i == r && ZM_equal(CM_L, oldCM_L))
    {
      CM_L = oldCM_L;
      avma = av2; continue;
    }

    CM_Lp = FpM_image(CM_L, utoipos(27449)); /* inexpensive test */
    if (lg(CM_Lp) != lg(CM_L))
    {
      if (DEBUGLEVEL>2) err_printf("LLL_cmbf: rank decrease\n");
      CM_L = ZM_hnf(CM_L);
    }

    if (i <= r && i*rec < n0)
    {
      pari_timer ti;
      if (DEBUGLEVEL>2) timer_start(&ti);
      list = nf_chk_factors(T, P, Q_div_to_int(CM_L,utoipos(C)), famod, L->pk);
      if (DEBUGLEVEL>2) ti_CF += timer_delay(&ti);
      if (list) break;
    }
    if (gc_needed(av,1))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"nf_LLL_cmbf");
      gerepileall(av, L->Tpk? 9: 8,
                      &CM_L,&TT,&Tra,&famod,&L->GSmin,&L->pk,&L->prk,&L->iprk,
                      &L->Tpk);
    }
    else CM_L = gerepilecopy(av2, CM_L);
  }
  if (DEBUGLEVEL>2)
    err_printf("* Time LLL: %ld\n* Time Check Factor: %ld\n",ti_LLL,ti_CF);
  return list;
}

static GEN
nf_combine_factors(nfcmbf_t *T, GEN polred, long klim)
{
  nflift_t *L = T->L;
  GEN res;
  long maxK;
  int done;
  pari_timer ti;

  if (DEBUGLEVEL>2) timer_start(&ti);
  T->fact = ZqX_liftfact(polred, T->fact, L->Tpk, L->pk, L->p, L->k);
  if (DEBUGLEVEL>2) timer_printf(&ti, "Hensel lift");
  res = nfcmbf(T, klim, &maxK, &done);
  if (DEBUGLEVEL>2) timer_printf(&ti, "Naive recombination");
  if (!done)
  {
    long l = lg(res)-1;
    GEN v;
    if (l > 1)
    {
      GEN den;
      T->pol = gel(res,l);
      T->polbase = Q_remove_denom(RgX_to_nfX(T->nf, T->pol), &den);
      if (den) { T->Br = gmul(T->Br, den); T->pol = RgX_Rg_mul(T->pol, den); }
    }
    v = nf_LLL_cmbf(T, maxK);
    /* remove last elt, possibly unfactored. Add all new ones. */
    setlg(res, l); res = shallowconcat(res, v);
  }
  return res;
}

static GEN
nf_DDF_roots(GEN pol, GEN polred, GEN nfpol, long fl, nflift_t *L)
{
  GEN z, Cltx_r, ltdn;
  long i, m, lz;
  div_data D;

  init_div_data(&D, pol, L);
  ltdn = mul_content(D.lt, L->dn);
  z = ZqX_roots(polred, L->Tpk, L->p, L->k);
  Cltx_r = deg1pol_shallow(D.Clt? D.Clt: gen_1, NULL, varn(pol));
  lz = lg(z);
  if (DEBUGLEVEL > 3) err_printf("Checking %ld roots:",lz-1);
  for (m=1,i=1; i<lz; i++)
  {
    GEN r = gel(z,i);
    int dvd;
    pari_sp av;
    if (DEBUGLEVEL > 3) err_printf(" %ld",i);
    /* lt*dn*topowden * r = Clt * r */
    r = nf_bestlift_to_pol(ltdn? gmul(ltdn,r): r, NULL, L);
    av = avma;
    gel(Cltx_r,2) = gneg(r); /* check P(r) == 0 */
    dvd = ZXQX_dvd(D.C2ltpol, Cltx_r, nfpol); /* integral */
    avma = av;
    /* don't go on with q, usually much larger that C2ltpol */
    if (dvd) {
      if (D.Clt) r = gdiv(r, D.Clt);
      gel(z,m++) = r;
    }
    else if (fl == ROOTS_SPLIT) return cgetg(1, t_VEC);
  }
  if (DEBUGLEVEL > 3) err_printf(" done\n");
  z[0] = evaltyp(t_VEC) | evallg(m);
  return z;
}

/* returns a few factors of T in Fp of degree <= maxf, NULL if none exist */
static GEN
get_good_factor(GEN T, ulong p, long maxf)
{
  pari_sp av = avma;
  GEN r, R = gel(Flx_factor(ZX_to_Flx(T,p),p), 1);
  if (maxf == 1)
  { /* degree 1 factors are best */
    r = gel(R,1);
    if (degpol(r) == 1) return mkvec(r);
  }
  else
  { /* otherwise, pick factor of largish degree */
    long i, j, dr, d = 0, l = lg(R);
    GEN v;
    if (l == 2) return mkvec(gel(R,1)); /* inert is fine */
    v = cgetg(l, t_VEC);
    for (i = j = 1; i < l; i++)
    {
      r = gel(R,i); dr = degpol(r);
      if (dr > maxf) break;
      if (dr != d) { gel(v,j++) = r; d = dr; }
    }
    setlg(v,j); if (j > 1) return v;
  }
  avma = av; return NULL; /* failure */
}

/* n = number of modular factors, f = residue degree; nold/fold current best
 * return 1 if new values are "better" than old ones */
static int
record(long nold, long n, long fold, long f)
{
  if (!nold) return 1; /* uninitialized */
  if (fold == f) return n < nold;
  /* if f increases, allow increasing n a little */
  if (fold < f) return n <= 20 || n < 1.1*nold;
  /* f decreases, only allow if decreasing n a lot */
  return n < 0.7*nold;
}
/* Optimization problem: factorization of polynomials over large Fq is slow,
 * BUT bestlift correspondingly faster.
 * Return maximal residue degree to be considered when picking a prime ideal */
static long
get_maxf(long nfdeg)
{
  long maxf = 1;
  if      (nfdeg >= 45) maxf =32;
  else if (nfdeg >= 30) maxf =16;
  else if (nfdeg >= 15) maxf = 8;
  return maxf;
}
/* number of maximal ideals to test before settling on best prime and number
 * of factors; B = [K:Q]*deg(P) */
static long
get_nbprimes(long B)
{
  if (B <= 128) return 5;
  if (B <= 1024) return 20;
  if (B <= 2048) return 65;
  return 100;
}
/* Select a prime ideal pr over which to factor pol.
 * Return the number of factors (or roots, according to flag fl) mod pr.
 * Set:
 *   lt: leading term of polbase (t_INT or NULL [ for 1 ])
 *   pr: a suitable maximal ideal
 *   Fa: factors found mod pr
 *   Tp: polynomial defining Fq/Fp */
static long
nf_pick_prime(GEN nf, GEN pol, long fl, GEN *lt, GEN *Tp, ulong *pp)
{
  GEN nfpol = nf_get_pol(nf), bad = mulii(nf_get_disc(nf), nf_get_index(nf));
  long nfdeg = degpol(nfpol), dpol = degpol(pol), nold = 0, fold = 1;
  long maxf = get_maxf(nfdeg), ct = get_nbprimes(nfdeg * dpol);
  ulong p;
  forprime_t S;
  pari_timer ti_pr;

  if (DEBUGLEVEL>3) timer_start(&ti_pr);
  *lt  = leading_coeff(pol); /* t_INT */
  if (gequal1(*lt)) *lt = NULL;
  *pp = 0;
  *Tp = NULL;
  (void)u_forprime_init(&S, 2, ULONG_MAX);
  /* select pr such that pol has the smallest number of factors, ct attempts */
  while ((p = u_forprime_next(&S)))
  {
    GEN vT;
    long n, i, l, ok = 0;
    ulong ltp = 0;

    if (! umodiu(bad,p)) continue;
    if (*lt) { ltp = umodiu(*lt, p); if (!ltp) continue; }
    vT = get_good_factor(nfpol, p, maxf);
    if (!vT) continue;
    l = lg(vT);
    for (i = 1; i < l; i++)
    {
      pari_sp av2 = avma;
      GEN T = gel(vT,i), red = RgX_to_FlxqX(pol, T, p);
      long f = degpol(T);
      if (f == 1)
      { /* degree 1 */
        red = FlxX_to_Flx(red);
        if (ltp) red = Flx_normalize(red, p);
        if (!Flx_is_squarefree(red, p)) { avma = av2; continue; }
        ok = 1;
        n = (fl == FACTORS)? Flx_nbfact(red,p): Flx_nbroots(red,p);
      }
      else
      {
        if (ltp) red = FlxqX_normalize(red, T, p);
        if (!FlxqX_is_squarefree(red, T, p)) { avma = av2; continue; }
        ok = 1;
        n = (fl == FACTORS)? FlxqX_nbfact(red,T,p): FlxqX_nbroots(red,T,p);
      }
      if (fl == ROOTS_SPLIT && n < dpol) return n; /* not split */
      if (n <= 1)
      {
        if (fl == FACTORS) return n; /* irreducible */
        if (!n) return 0; /* no root */
      }
      if (DEBUGLEVEL>3)
        err_printf("%3ld %s at prime (%ld,x^%ld+...)\n Time: %ld\n",
            n, (fl == FACTORS)? "factors": "roots", p,f, timer_delay(&ti_pr));

      if (fl == ROOTS && f==nfdeg) { *Tp = T; *pp = p; return n; }
      if (record(nold, n, fold, f)) { nold = n; fold = f; *Tp = T; *pp = p; }
      else avma = av2;
    }
    if (ok && --ct <= 0) break;
  }
  if (!nold) pari_err_OVERFLOW("nf_pick_prime [ran out of primes]");
  return nold;
}

/* Assume lt(T) is a t_INT and T square free. Return t_VEC of irred. factors */
static GEN
nfsqff_trager(GEN u, GEN T, GEN dent)
{
  long k = 0, i, lx;
  GEN U, P, x0, mx0, fa, n = ZX_ZXY_rnfequation(T, u, &k);
  int tmonic;
  if (DEBUGLEVEL>4) err_printf("nfsqff_trager: choosing k = %ld\n",k);

  /* n guaranteed to be squarefree */
  fa = ZX_DDF(Q_primpart(n)); lx = lg(fa);
  if (lx == 2) return mkvec(u);

  tmonic = is_pm1(leading_coeff(T));
  P = cgetg(lx,t_VEC);
  x0 = deg1pol_shallow(stoi(-k), gen_0, varn(T));
  mx0 = deg1pol_shallow(stoi(k), gen_0, varn(T));
  U = RgXQX_translate(u, mx0, T);
  if (!tmonic) U = Q_primpart(U);
  for (i=lx-1; i>0; i--)
  {
    GEN f = gel(fa,i), F = nfgcd(U, f, T, dent);
    F = RgXQX_translate(F, x0, T);
    /* F = gcd(f, u(t - x0)) [t + x0] = gcd(f(t + x0), u), more efficient */
    if (typ(F) != t_POL || degpol(F) == 0)
      pari_err_IRREDPOL("factornf [modulus]",T);
    gel(P,i) = QXQX_normalize(F, T);
  }
  gen_sort_inplace(P, (void*)&cmp_RgX, &gen_cmp_RgX, NULL);
  return P;
}

/* Factor polynomial a on the number field defined by polynomial T, using
 * Trager's trick */
GEN
polfnf(GEN a, GEN T)
{
  GEN rep = cgetg(3, t_MAT), A, B, y, dent, bad;
  long dA;
  int tmonic;

  if (typ(a)!=t_POL) pari_err_TYPE("polfnf",a);
  if (typ(T)!=t_POL) pari_err_TYPE("polfnf",T);
  T = Q_primpart(T); tmonic = is_pm1(leading_coeff(T));
  RgX_check_ZX(T,"polfnf");
  A = Q_primpart( QXQX_normalize(RgX_nffix("polfnf",T,a,1), T) );
  dA = degpol(A);
  if (dA <= 0)
  {
    avma = (pari_sp)(rep + 3);
    return (dA == 0)? trivial_fact(): zerofact(varn(A));
  }
  bad = dent = ZX_disc(T);
  if (tmonic) dent = indexpartial(T, dent);
  (void)nfgcd_all(A,RgX_deriv(A), T, dent, &B);
  if (degpol(B) != dA) B = Q_primpart( QXQX_normalize(B, T) );
  ensure_lt_INT(B);
  y = nfsqff_trager(B, T, dent);
  fact_from_sqff(rep, A, B, y, T, bad);
  return sort_factor_pol(rep, cmp_RgX);
}

static int
nfsqff_use_Trager(long n, long dpol)
{
  return dpol*3<n;
}

/* return the factorization of the square-free polynomial pol. Not memory-clean
   The coeffs of pol are in Z_nf and its leading term is a rational integer.
   deg(pol) > 0, deg(nfpol) > 1
   fl is either FACTORS (return factors), or ROOTS / ROOTS_SPLIT (return roots):
     - ROOTS, return only the roots of x in nf
     - ROOTS_SPLIT, as ROOTS if pol splits, [] otherwise
   den is usually 1, otherwise nf.zk is doubtful, and den bounds the
   denominator of an arbitrary element of Z_nf on nf.zk */
static GEN
nfsqff(GEN nf, GEN pol, long fl, GEN den)
{
  long n, nbf, dpol = degpol(pol);
  GEN C0, polbase;
  GEN N2, res, polred, lt, nfpol = typ(nf)==t_POL?nf:nf_get_pol(nf);
  ulong pp;
  nfcmbf_t T;
  nflift_t L;
  pari_timer ti, ti_tot;

  if (DEBUGLEVEL>2) { timer_start(&ti); timer_start(&ti_tot); }
  n = degpol(nfpol);
  /* deg = 1 => irreducible */
  if (dpol == 1) {
    if (fl == FACTORS) return mkvec(QXQX_normalize(pol, nfpol));
    return mkvec(gneg(gdiv(gel(pol,2),gel(pol,3))));
  }
  if (typ(nf)==t_POL || nfsqff_use_Trager(n,dpol))
  {
    GEN z;
    if (DEBUGLEVEL>2) err_printf("Using Trager's method\n");
    if (typ(nf) != t_POL) den =  mulii(den, nf_get_index(nf));
    z = nfsqff_trager(Q_primpart(pol), nfpol, den);
    if (fl != FACTORS) {
      long i, l = lg(z);
      for (i = 1; i < l; i++)
      {
        GEN LT, t = gel(z,i); if (degpol(t) > 1) break;
        LT = gel(t,3);
        if (typ(LT) == t_POL) LT = gel(LT,2); /* constant */
        gel(z,i) = gdiv(gel(t,2), negi(LT));
      }
      setlg(z, i);
      if (fl == ROOTS_SPLIT && i != l) return cgetg(1,t_VEC);
    }
    return z;
  }

  polbase = RgX_to_nfX(nf, pol);
  nbf = nf_pick_prime(nf, pol, fl, &lt, &L.Tp, &pp);
  if (L.Tp)
  {
    L.Tp = Flx_to_ZX(L.Tp);
    L.p = utoi(pp);
  }

  if (fl == ROOTS_SPLIT && nbf < dpol) return cgetg(1,t_VEC);
  if (nbf <= 1)
  {
    if (fl == FACTORS) return mkvec(QXQX_normalize(pol, nfpol)); /* irred. */
    if (!nbf) return cgetg(1,t_VEC); /* no root */
  }

  if (DEBUGLEVEL>2) {
    timer_printf(&ti, "choice of a prime ideal");
    err_printf("Prime ideal chosen: (%lu,x^%ld+...)\n", pp, degpol(L.Tp));
  }
  L.tozk = nf_get_invzk(nf);
  L.topow= nf_get_zkprimpart(nf);
  L.topowden = nf_get_zkden(nf);
  if (is_pm1(den)) den = NULL;
  L.dn = den;
  T.ZC = L2_bound(nf, den);
  T.Br = nf_root_bounds(nf, pol); if (lt) T.Br = gmul(T.Br, lt);

  /* C0 = bound for T_2(Q_i), Q | P */
  if (fl != FACTORS) C0 = normTp(T.Br, 2, n);
  else               C0 = nf_factor_bound(nf, polbase);
  T.bound = mulrr(T.ZC, C0); /* bound for |Q_i|^2 in Z^n on chosen Z-basis */

  N2 = mulur(dpol*dpol, normTp(T.Br, 4, n)); /* bound for T_2(lt * S_2) */
  T.BS_2 = mulrr(T.ZC, N2); /* bound for |S_2|^2 on chosen Z-basis */

  if (DEBUGLEVEL>2) {
    timer_printf(&ti, "bound computation");
    err_printf("  1) T_2 bound for %s: %Ps\n",
               fl == FACTORS?"factor": "root", C0);
    err_printf("  2) Conversion from T_2 --> | |^2 bound : %Ps\n", T.ZC);
    err_printf("  3) Final bound: %Ps\n", T.bound);
  }

  bestlift_init(0, nf, T.bound, &L);
  if (DEBUGLEVEL>2) timer_start(&ti);
  polred = ZqX_normalize(polbase, lt, &L); /* monic */

  if (fl != FACTORS) {
    GEN z = nf_DDF_roots(pol, polred, nfpol, fl, &L);
    if (lg(z) == 1) return cgetg(1, t_VEC);
    return z;
  }

  T.fact = gel(FqX_factor(polred, L.Tp, L.p), 1);
  if (DEBUGLEVEL>2)
    timer_printf(&ti, "splitting mod %Ps^%ld", L.p, degpol(L.Tp));
  T.L  = &L;
  T.polbase = polbase;
  T.pol   = pol;
  T.nf    = nf;
  res = nf_combine_factors(&T, polred, dpol-1);
  if (DEBUGLEVEL>2)
    err_printf("Total Time: %ld\n===========\n", timer_delay(&ti_tot));
  return res;
}

/* assume pol monic in nf.zk[X] */
GEN
nfroots_if_split(GEN *pnf, GEN pol)
{
  GEN T = get_nfpol(*pnf,pnf), den = fix_nf(pnf, &T, &pol);
  pari_sp av = avma;
  GEN z = nfsqff(*pnf, pol, ROOTS_SPLIT, den);
  if (lg(z) == 1) { avma = av; return NULL; }
  return gerepilecopy(av, z);
}

/*******************************************************************/
/*                                                                 */
/*              Roots of unity in a number field                   */
/*     (alternative to nfrootsof1 using factorization in K[X])     */
/*                                                                 */
/*******************************************************************/
/* Code adapted from nffactor. Structure of the algorithm; only step 1 is
 * specific to roots of unity.
 *
 * [Step 1]: guess roots via ramification. If trivial output this.
 * [Step 2]: select prime [p] unramified and ideal [pr] above
 * [Step 3]: evaluate the maximal exponent [k] such that the fondamental domain
 *           of a LLL-reduction of [prk] = pr^k contains a ball of radius larger
 *           than the norm of any root of unity.
 * [Step 3]: select a heuristic exponent,
 *           LLL reduce prk=pr^k and verify the exponent is sufficient,
 *           otherwise try a larger one.
 * [Step 4]: factor the cyclotomic polynomial mod [pr],
 *           Hensel lift to pr^k and find the representative in the ball
 *           If there is it is a primitive root */

/* Choose prime ideal unramified with "large" inertia degree */
static void
nf_pick_prime_for_units(GEN nf, nflift_t *L)
{
  GEN nfpol = nf_get_pol(nf), bad = mulii(nf_get_disc(nf), nf_get_index(nf));
  GEN ap = NULL, r = NULL;
  long nfdeg = degpol(nfpol), maxf = get_maxf(nfdeg);
  ulong pp;
  forprime_t S;

  (void)u_forprime_init(&S, 2, ULONG_MAX);
  while ( (pp = u_forprime_next(&S)) )
  {
    if (! umodiu(bad,pp)) continue;
    r = get_good_factor(nfpol, pp, maxf);
    if (r) break;
  }
  if (!r) pari_err_OVERFLOW("nf_pick_prime [ran out of primes]");
  r = gel(r,lg(r)-1); /* largest inertia degree */
  ap = utoipos(pp);
  L->p = ap;
  L->Tp = Flx_to_ZX(r);
  L->tozk = nf_get_invzk(nf);
  L->topow = nf_get_zkprimpart(nf);
  L->topowden = nf_get_zkden(nf);
}

/* *Heuristic* exponent k such that the fundamental domain of pr^k
 * should contain the ball of radius C */
static double
mybestlift_bound(GEN C)
{
  C = gtofp(C,DEFAULTPREC);
  return ceil(log(gtodouble(C)) / 0.2) + 3;
}

/* simplified nf_DDF_roots: polcyclo(n) monic in ZX either splits or has no
 * root in nf.
 * Return a root or NULL (no root) */
static GEN
nfcyclo_root(long n, GEN nfpol, nflift_t *L)
{
  GEN q, r, Cltx_r, pol = polcyclo(n,0), gn = utoipos(n);
  div_data D;

  init_div_data(&D, pol, L);
  (void)Fq_sqrtn(gen_1, gn, L->Tp, L->p, &r);
  /* r primitive n-th root of 1 in Fq */
  r = Zq_sqrtnlift(gen_1, gn, r, L->Tpk, L->p, L->k);
  /* lt*dn*topowden * r = Clt * r */
  r = nf_bestlift_to_pol(r, NULL, L);
  Cltx_r = deg1pol_shallow(D.Clt? D.Clt: gen_1, gneg(r), varn(pol));
  /* check P(r) == 0 */
  q = RgXQX_divrem(D.C2ltpol, Cltx_r, nfpol, ONLY_DIVIDES); /* integral */
  if (!q) return NULL;
  if (D.Clt) r = gdiv(r, D.Clt);
  return r;
}

/* Guesses the number of roots of unity in number field [nf].
 * Computes gcd of N(P)-1 for some primes. The value returned is a proven
 * multiple of the correct value. */
static long
guess_roots(GEN nf)
{
  long c = 0, nfdegree = nf_get_degree(nf), B = nfdegree + 20, l;
  ulong p = 2;
  GEN T = nf_get_pol(nf), D = nf_get_disc(nf), index = nf_get_index(nf);
  GEN nbroots = NULL;
  forprime_t S;
  pari_sp av;

  (void)u_forprime_init(&S, 3, ULONG_MAX);
  av = avma;
  /* result must be stationary (counter c) for at least B loops */
  for (l=1; (p = u_forprime_next(&S)); l++)
  {
    GEN old, F, pf_1, Tp;
    long i, nb, gcdf = 0;

    if (!umodiu(D,p) || !umodiu(index,p)) continue;
    Tp = ZX_to_Flx(T,p); /* squarefree */
    F = Flx_nbfact_by_degree(Tp, &nb, p);
    /* the gcd of the p^f - 1 is p^(gcd of the f's) - 1 */
    for (i = 1; i <= nfdegree; i++)
      if (F[i]) {
        gcdf = gcdf? ugcd(gcdf, i): i;
        if (gcdf == 1) break;
      }
    pf_1 = subiu(powuu(p, gcdf), 1);
    old = nbroots;
    nbroots = nbroots? gcdii(pf_1, nbroots): pf_1;
    if (DEBUGLEVEL>5)
      err_printf("p=%lu; gcf(f(P/p))=%ld; nbroots | %Ps",p, gcdf, nbroots);
    /* if same result go on else reset the stop counter [c] */
    if (old && equalii(nbroots,old))
    { if (!is_bigint(nbroots) && ++c > B) break; }
    else
      c = 0;
  }
  if (!nbroots) pari_err_OVERFLOW("guess_roots [ran out of primes]");
  if (DEBUGLEVEL>5) err_printf("%ld loops\n",l);
  avma = av; return itos(nbroots);
}

/* T(x) an irreducible ZX. Is it of the form Phi_n(c \pm x) ?
 * Return NULL if not, and a root of 1 of maximal order in Z[x]/(T) otherwise
 *
 * N.B. Set n_squarefree = 1 if n is squarefree, and 0 otherwise.
 * This last parameter is inconvenient, but it allows a cheap
 * stringent test. (n guessed from guess_roots())*/
static GEN
ZXirred_is_cyclo_translate(GEN T, long n_squarefree)
{
  long r, m, d = degpol(T);
  GEN T1, c = divis_rem(gel(T, d+1), d, &r); /* d-1 th coeff divisible by d ? */
  /* The trace coefficient of polcyclo(n) is \pm1 if n is square free, and 0
   * otherwise. */
  if (!n_squarefree)
  { if (r) return NULL; }
  else
  {
    if (r < -1)
    {
      r += d;
      c = subiu(c, 1);
    }
    else if (r == d-1)
    {
      r = -1;
      c = addiu(c, 1);
    }
    if (r != 1 && r != -1) return NULL;
  }
  if (signe(c)) /* presumably Phi_guess(c \pm x) */
    T = RgX_translate(T, negi(c));
  if (!n_squarefree) T = RgX_deflate_max(T, &m);
  /* presumably Phi_core(guess)(\pm x), cyclotomic iff original T was */
  T1 = ZX_graeffe(T);
  if (ZX_equal(T, T1)) /* T = Phi_n, n odd */
    return deg1pol_shallow(gen_m1, negi(c), varn(T));
  else if (ZX_equal(T1, ZX_z_unscale(T, -1))) /* T = Phi_{2n}, nodd */
    return deg1pol_shallow(gen_1, c, varn(T));
  return NULL;
}

static GEN
trivroots(void) { return mkvec2(gen_2, gen_m1); }
/* Number of roots of unity in number field [nf]. */
GEN
rootsof1(GEN nf)
{
  nflift_t L;
  GEN T, q, fa, LP, LE, C0, z, disc;
  pari_timer ti;
  long i, l, nbguessed, nbroots, nfdegree;
  pari_sp av;

  nf = checknf(nf);
  if (nf_get_r1(nf)) return trivroots();

  /* Step 1 : guess number of roots and discard trivial case 2 */
  if (DEBUGLEVEL>2) timer_start(&ti);
  nbguessed = guess_roots(nf);
  if (DEBUGLEVEL>2)
    timer_printf(&ti, "guessing roots of 1 [guess = %ld]", nbguessed);
  if (nbguessed == 2) return trivroots();

  nfdegree = nf_get_degree(nf);
  fa = factoru(nbguessed);
  LP = gel(fa,1); l = lg(LP);
  LE = gel(fa,2);
  disc = nf_get_disc(nf);
  for (i = 1; i < l; i++)
  {
    long p = LP[i];
    /* Degree and ramification test: find largest k such that Q(zeta_{p^k})
     * may be a subfield of K. Q(zeta_p^k) has degree (p-1)p^(k-1)
     * and v_p(discriminant) = ((p-1)k-1)p^(k-1); so we must have
     * v_p(disc_K) >= ((p-1)k-1) * n / (p-1) = kn - q, where q = n/(p-1) */
    if (p == 2)
    { /* the test simplifies a little in that case */
      long v, vnf, k;
      if (LE[i] == 1) continue;
      vnf = vals(nfdegree);
      v = vali(disc);
      for (k = minss(LE[i], vnf+1); k >= 1; k--)
        if (v >= nfdegree*(k-1)) { nbguessed >>= LE[i]-k; LE[i] = k; break; }
      /* N.B the test above always works for k = 1: LE[i] >= 1 */
    }
    else
    {
      long v, vnf, k;
      ulong r, q = udivuu_rem(nfdegree, p-1, &r);
      if (r) { nbguessed /= upowuu(p, LE[i]); LE[i] = 0; continue; }
      /* q = n/(p-1) */
      vnf = u_lval(q, p);
      v = Z_lval(disc, p);
      for (k = minss(LE[i], vnf+1); k >= 0; k--)
        if (v >= nfdegree*k-(long)q)
        { nbguessed /= upowuu(p, LE[i]-k); LE[i] = k; break; }
      /* N.B the test above always works for k = 0: LE[i] >= 0 */
    }
  }
  if (DEBUGLEVEL>2)
    timer_printf(&ti, "after ramification conditions [guess = %ld]", nbguessed);
  if (nbguessed == 2) return trivroots();
  av = avma;

  /* Step 1.5 : test if nf.pol == subst(polcyclo(nbguessed), x, \pm x+c) */
  T = nf_get_pol(nf);
  if (eulerphiu_fact(fa) == (ulong)nfdegree)
  {
    z = ZXirred_is_cyclo_translate(T, uissquarefree_fact(fa));
    if (DEBUGLEVEL>2) timer_printf(&ti, "checking for cyclotomic polynomial");
    if (z)
    {
      z = nf_to_scalar_or_basis(nf,z);
      return gerepilecopy(av, mkvec2(utoipos(nbguessed), z));
    }
    avma = av;
  }

  /* Step 2 : choose a prime ideal for local lifting */
  nf_pick_prime_for_units(nf, &L);
  if (DEBUGLEVEL>2)
    timer_printf(&ti, "choosing prime %Ps, degree %ld",
             L.p, L.Tp? degpol(L.Tp): 1);

  /* Step 3 : compute a reduced pr^k allowing lifting of local solutions */
  /* evaluate maximum L2 norm of a root of unity in nf */
  C0 = gmulsg(nfdegree, L2_bound(nf, gen_1));
  /* lift and reduce pr^k */
  if (DEBUGLEVEL>2) err_printf("Lift pr^k; GSmin wanted: %Ps\n",C0);
  bestlift_init((long)mybestlift_bound(C0), nf, C0, &L);
  L.dn = NULL;
  if (DEBUGLEVEL>2) timer_start(&ti);

  /* Step 4 : actual computation of roots */
  nbroots = 2; z = gen_m1;
  q = powiu(L.p,degpol(L.Tp));
  for (i = 1; i < l; i++)
  { /* for all prime power factors of nbguessed, find a p^k-th root of unity */
    long k, p = LP[i];
    for (k = minss(LE[i], Z_lval(subiu(q,1UL),p)); k > 0; k--)
    { /* find p^k-th roots */
      pari_sp av = avma;
      long pk = upowuu(p,k);
      GEN r;
      if (pk==2) continue; /* no need to test second roots ! */
      r = nfcyclo_root(pk, T, &L);
      if (DEBUGLEVEL>2) timer_printf(&ti, "for factoring Phi_%ld^%ld", p,k);
      if (r) {
        if (DEBUGLEVEL>2) err_printf("  %s root of unity found\n",uordinal(pk));
        if (p==2) { nbroots = pk; z = r; }
        else     { nbroots *= pk; z = nfmul(nf, z,r); }
        break;
      }
      avma = av;
      if (DEBUGLEVEL) pari_warn(warner,"rootsof1: wrong guess");
    }
  }
  return gerepilecopy(av, mkvec2(utoi(nbroots), z));
}

static long
zk_equal1(GEN y)
{
  if (typ(y) == t_INT) return equali1(y);
  return equali1(gel(y,1)) && ZV_isscalar(y);
}
/* x^w = 1 */
static GEN
is_primitive_root(GEN nf, GEN fa, GEN x, long w)
{
  GEN P = gel(fa,1);
  long i, l = lg(P);

  for (i = 1; i < l; i++)
  {
    long p = itos(gel(P,i));
    GEN y = nfpow_u(nf,x, w/p);
    if (zk_equal1(y) > 0) /* y = 1 */
    {
      if (p != 2 || !equali1(gcoeff(fa,i,2))) return NULL;
      x = gneg_i(x);
    }
  }
  return x;
}
GEN
rootsof1_kannan(GEN nf)
{
  pari_sp av = avma;
  long N, k, i, ws, prec;
  GEN z, y, d, list, w;

  nf = checknf(nf);
  if ( nf_get_r1(nf) ) return trivroots();

  N = nf_get_degree(nf); prec = nf_get_prec(nf);
  for (;;)
  {
    GEN R = R_from_QR(nf_get_G(nf), prec);
    if (R)
    {
      y = fincke_pohst(mkvec(R), utoipos(N), N * N, 0, NULL);
      if (y) break;
    }
    prec = precdbl(prec);
    if (DEBUGLEVEL) pari_warn(warnprec,"rootsof1",prec);
    nf = nfnewprec_shallow(nf,prec);
  }
  if (itos(ground(gel(y,2))) != N) pari_err_BUG("rootsof1 (bug1)");
  w = gel(y,1); ws = itos(w);
  if (ws == 2) { avma = av; return trivroots(); }

  d = Z_factor(w); list = gel(y,3); k = lg(list);
  for (i=1; i<k; i++)
  {
    z = is_primitive_root(nf, d, gel(list,i), ws);
    if (z) return gerepilecopy(av, mkvec2(w, z));
  }
  pari_err_BUG("rootsof1");
  return NULL; /* LCOV_EXCL_LINE */
}
