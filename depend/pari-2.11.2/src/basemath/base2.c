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
/*                                                                 */
/*                       MAXIMAL ORDERS                            */
/*                                                                 */
/*******************************************************************/
#include "pari.h"
#include "paripriv.h"

/* allow p = -1 from factorizations, avoid oo loop on p = 1 */
static long
safe_Z_pvalrem(GEN x, GEN p, GEN *z)
{
  if (is_pm1(p))
  {
    if (signe(p) > 0) return gvaluation(x,p); /*error*/
    *z = absi(x); return 1;
  }
  return Z_pvalrem(x, p, z);
}
/* D an integer, P a ZV, return a factorization matrix for D over P, removing
 * entries with 0 exponent. */
static GEN
fact_from_factors(GEN D, GEN P, long flag)
{
  long i, l = lg(P), iq = 1;
  GEN Q = cgetg(l+1,t_COL);
  GEN E = cgetg(l+1,t_COL);
  for (i=1; i<l; i++)
  {
    GEN p = gel(P,i);
    long k;
    if (flag && !equalim1(p))
    {
      p = gcdii(p, D);
      if (is_pm1(p)) continue;
    }
    k = safe_Z_pvalrem(D, p, &D);
    if (k) { gel(Q,iq) = p; gel(E,iq) = utoipos(k); iq++; }
  }
  D = absi_shallow(D);
  if (!equali1(D))
  {
    long k = Z_isanypower(D, &D);
    if (!k) k = 1;
    gel(Q,iq) = D; gel(E,iq) = utoipos(k); iq++;
  }
  setlg(Q,iq);
  setlg(E,iq); return mkmat2(Q,E);
}

/* d a t_INT; f a t_MAT factorisation of some t_INT sharing some divisors
 * with d, or a prime (t_INT). Return a factorization F of d: "primes"
 * entries in f _may_ be composite, and are included as is in d. */
static GEN
update_fact(GEN d, GEN f)
{
  GEN P;
  switch (typ(f))
  {
    case t_INT: case t_VEC: case t_COL: return f;
    case t_MAT:
      if (lg(f) == 3) { P = gel(f,1); break; }
    /*fall through*/
    default:
      pari_err_TYPE("nfbasis [factorization expected]",f);
      return NULL;/*LCOV_EXCL_LINE*/
  }
  return fact_from_factors(d, P, 1);
}

/* T = C T0(X/L); C = L^d / lt(T0), d = deg(T)
 * disc T = C^2(d - 1) L^-(d(d-1)) disc T0 = (L^d / lt(T0)^2)^(d-1) disc T0 */
static GEN
set_disc(nfmaxord_t *S)
{
  GEN l0, L, dT;
  long d;
  if (S->T0 == S->T) return ZX_disc(S->T);
  d = degpol(S->T0);
  l0 = leading_coeff(S->T0);
  L = S->unscale;
  if (typ(L) == t_FRAC && abscmpii(gel(L,1), gel(L,2)) < 0)
    dT = ZX_disc(S->T); /* more efficient */
  else
  {
    GEN a = gpowgs(gdiv(gpowgs(L, d), sqri(l0)), d-1);
    dT = gmul(a, ZX_disc(S->T0)); /* more efficient */
  }
  return S->dT = dT;
}

/* dT != 0 */
static GEN
poldiscfactors_i(GEN T, GEN dT, long flag)
{
  GEN fa = absZ_factor_limit(dT, 0);
  GEN Tp, E, P = gel(fa,1);
  long i, l = lg(P);
  GEN p = gel(P,l-1);
  if (l == 1 || ((flag || lgefint(p)==3) && BPSW_psp(p))) return fa;
  settyp(P, t_VEC);
  Tp = ZX_deriv(T);
  for (i = l-1; i < lg(P); i++)
  {
    GEN p = gel(P,i), r, L;
    if (Z_isanypower(p, &p)) gel(P,i) = p;
    if ((flag || lgefint(p)==3) && BPSW_psp(p)) continue;
    r = FpX_gcd_check(T, Tp, p);
    if (r) L = Z_cba(r, diviiexact(p,r));
    else
    {
      if (!flag) continue;
      L = gel(Z_factor(p),1); settyp(L, t_VEC);
    }
    P = shallowconcat(vecsplice(P,i), L);
    i--;
  }
  settyp(P, t_COL);
  P = ZV_sort(P); l = lg(P);
  E = cgetg(l, t_COL);
  for (i = 1; i < l; i++)
    gel(E,i) = utoi(Z_pvalrem(dT, gel(P,i), &dT));
  return mkmat2(P,E);
}
GEN
poldiscfactors(GEN T, long flag)
{
  pari_sp av = avma;
  GEN dT;
  if (typ(T) != t_POL || !RgX_is_ZX(T)) pari_err_TYPE("poldiscfactors",T);
  if (flag < 0 || flag > 1) pari_err_FLAG("poldiscfactors");
  dT = ZX_disc(T);
  if (!signe(dT)) retmkvec2(gen_0, Z_factor(gen_0));
  return gerepilecopy(av, mkvec2(dT, poldiscfactors_i(T, dT, flag)));
}

static void
nfmaxord_check_args(nfmaxord_t *S, GEN T, long flag)
{
  GEN dT, L, E, P, fa = NULL;
  pari_timer t;
  long l, ty = typ(T);

  if (DEBUGLEVEL) timer_start(&t);
  if (ty == t_VEC) {
    if (lg(T) != 3) pari_err_TYPE("nfmaxord",T);
    fa = gel(T,2); T = gel(T,1); ty = typ(T);
  }
  if (ty != t_POL) pari_err_TYPE("nfmaxord",T);
  T = Q_primpart(T);
  if (degpol(T) <= 0) pari_err_CONSTPOL("nfmaxord");
  RgX_check_ZX(T, "nfmaxord");
  S->T0 = T;
  T = ZX_Q_normalize(T, &L);
  S->unscale = L;
  S->T = T;
  S->dT = dT = set_disc(S);
  if (fa)
  {
    const long MIN = 100; /* include at least all p < 101 */
    long tf;
    if (!isint1(L)) fa = update_fact(dT, fa);
    tf = typ(fa);
    switch(tf)
    {
      case t_MAT:
        if (!is_Z_factornon0(fa)) pari_err_TYPE("nfmaxord",fa);
        fa = gel(fa,1); tf = t_COL; /* fall through */
      case t_VEC: case t_COL:
        P = gel(absZ_factor_limit(dT, MIN), 1); l = lg(P);
        if (l > 1 && abscmpiu(gel(P,1), MIN) <= 0)
        {
          if (abscmpiu(gel(P,l-1), MIN) > 0) setlg(P,l-1);
          settyp(P,tf); fa = ZV_sort_uniq(shallowconcat(fa,P));
        }
        fa = fact_from_factors(dT, fa, 0);
        break;
      case t_INT:
        fa = absZ_factor_limit(dT, (signe(fa) <= 0)? 1: maxuu(itou(fa), MIN));
        break;
        /*fall through*/
      default:
        pari_err_TYPE("nfmaxord",fa);
    }
    if (!signe(dT)) pari_err_IRREDPOL("nfmaxord",mkvec2(T,fa));
  }
  else
    fa = poldiscfactors_i(T, dT, !(flag & nf_PARTIALFACT));
  P = gel(fa,1); l = lg(P);
  E = gel(fa,2);
  if (l > 1 && is_pm1(gel(P,1)))
  {
    l--;
    P = vecslice(P, 2, l);
    E = vecslice(E, 2, l);
  }
  S->dTP = P;
  S->dTE = vec_to_vecsmall(E);
  if (DEBUGLEVEL>2) timer_printf(&t, "disc. factorisation");
}

static int
fnz(GEN x,long j)
{
  long i;
  for (i=1; i<j; i++)
    if (signe(gel(x,i))) return 0;
  return 1;
}
/* return list u[i], 2 by 2 coprime with the same prime divisors as ab */
static GEN
get_coprimes(GEN a, GEN b)
{
  long i, k = 1;
  GEN u = cgetg(3, t_COL);
  gel(u,1) = a;
  gel(u,2) = b;
  /* u1,..., uk 2 by 2 coprime */
  while (k+1 < lg(u))
  {
    GEN d, c = gel(u,k+1);
    if (is_pm1(c)) { k++; continue; }
    for (i=1; i<=k; i++)
    {
      GEN ui = gel(u,i);
      if (is_pm1(ui)) continue;
      d = gcdii(c, ui);
      if (d == gen_1) continue;
      c = diviiexact(c, d);
      gel(u,i) = diviiexact(ui, d);
      u = shallowconcat(u, d);
    }
    gel(u,++k) = c;
  }
  for (i = k = 1; i < lg(u); i++)
    if (!is_pm1(gel(u,i))) gel(u,k++) = gel(u,i);
  setlg(u, k); return u;
}

/*******************************************************************/
/*                                                                 */
/*                            ROUND 4                              */
/*                                                                 */
/*******************************************************************/
typedef struct {
  /* constants */
  long pisprime; /* -1: unknown, 1: prime,  0: composite */
  GEN p, f; /* goal: factor f p-adically */
  long df;
  GEN pdf; /* p^df = reduced discriminant of f */
  long mf; /* */
  GEN psf, pmf; /* stability precision for f, wanted precision for f */
  long vpsf; /* v_p(p_f) */
  /* these are updated along the way */
  GEN phi; /* a p-integer, in Q[X] */
  GEN phi0; /* a p-integer, in Q[X] from testb2 / testc2, to be composed with
             * phi when correct precision is known */
  GEN chi; /* characteristic polynomial of phi (mod psc) in Z[X] */
  GEN nu; /* irreducible divisor of chi mod p, in Z[X] */
  GEN invnu; /* numerator ( 1/ Mod(nu, chi) mod pmr ) */
  GEN Dinvnu;/* denominator ( ... ) */
  long vDinvnu; /* v_p(Dinvnu) */
  GEN prc, psc; /* reduced discriminant of chi, stability precision for chi */
  long vpsc; /* v_p(p_c) */
  GEN ns, nsf, precns; /* cached Newton sums for nsf and their precision */
} decomp_t;
static GEN maxord_i(decomp_t *S, GEN p, GEN f, long mf, GEN w, long flag);
static GEN dbasis(GEN p, GEN f, long mf, GEN alpha, GEN U);
static GEN maxord(GEN p,GEN f,long mf);
static GEN ZX_Dedekind(GEN F, GEN *pg, GEN p);

/* Warning: data computed for T = ZX_Q_normalize(T0). If S.unscale !=
 * gen_1, caller must take steps to correct the components if it wishes
 * to stick to the original T0. Return a vector of p-maximal orders, for
 * those p s.t p^2 | disc(T) [ = S->dTP ]*/
static GEN
get_maxord(nfmaxord_t *S, GEN T0, long flag)
{
  VOLATILE GEN P, E, O;
  VOLATILE long lP, i, k;

  nfmaxord_check_args(S, T0, flag);
  P = S->dTP; lP = lg(P);
  E = S->dTE;
  O = cgetg(1, t_VEC);
  for (i=1; i<lP; i++)
  {
    VOLATILE pari_sp av;
    /* includes the silly case where P[i] = -1 */
    if (E[i] <= 1) { O = shallowconcat(O, gen_1); continue; }
    av = avma;
    pari_CATCH(CATCH_ALL) {
      GEN N, u, err = pari_err_last();
      long l;
      switch(err_get_num(err))
      {
        case e_INV:
        {
          GEN p, x = err_get_compo(err, 2);
          if (typ(x) == t_INTMOD)
          { /* caught false prime, update factorization */
            p = gcdii(gel(x,1), gel(x,2));
            u = diviiexact(gel(x,1),p);
            if (DEBUGLEVEL) pari_warn(warner,"impossible inverse: %Ps", x);
            gerepileall(av, 2, &p, &u);

            u = get_coprimes(p, u); l = lg(u);
            /* no small factors, but often a prime power */
            for (k = 1; k < l; k++) (void)Z_isanypower(gel(u,k), &gel(u,k));
            break;
          }
          /* fall through */
        }
        case e_PRIME: case e_IRREDPOL:
        { /* we're here because we failed BPSW_isprime(), no point in
           * reporting a possible counter-example to the BPSW test */
          GEN p = gel(P,i);
          avma = av;
          if (DEBUGLEVEL)
            pari_warn(warner,"large composite in nfmaxord:loop(), %Ps", p);
          if (expi(p) < 100) /* factor should require ~20ms for this */
            u = gel(Z_factor(p), 1);
          else
          { /* give up, probably not maximal */
            GEN B, g, k = ZX_Dedekind(S->T, &g, p);
            k = FpX_normalize(k, p);
            B = dbasis(p, S->T, E[i], NULL, FpX_div(S->T,k,p));
            O = shallowconcat(O, mkvec(B));
            pari_CATCH_reset(); continue;
          }
          break;
        }
        default: pari_err(0, err);
          return NULL;/*LCOV_EXCL_LINE*/
      }
      l = lg(u);
      gel(P,i) = gel(u,1);
      P = shallowconcat(P, vecslice(u, 2, l-1));
      av = avma;
      N = S->dT; E[i] = Z_pvalrem(N, gel(P,i), &N);
      for (k=lP, lP=lg(P); k < lP; k++) E[k] = Z_pvalrem(N, gel(P,k), &N);
    } pari_RETRY {
      if (DEBUGLEVEL>2) err_printf("Treating p^k = %Ps^%ld\n",P[i],E[i]);
      O = shallowconcat(O, mkvec( maxord(gel(P,i),S->T,E[i]) ));
    } pari_ENDCATCH;
  }
  S->dTP = P; return O;
}

/* M a QM, return denominator of diagonal. All denominators are powers of
 * a given integer */
static GEN
diag_denom(GEN M)
{
  GEN d = gen_1;
  long j, l = lg(M);
  for (j=1; j<l; j++)
  {
    GEN t = gcoeff(M,j,j);
    if (typ(t) == t_INT) continue;
    t = gel(t,2);
    if (abscmpii(t,d) > 0) d = t;
  }
  return d;
}
void
nfmaxord(nfmaxord_t *S, GEN T0, long flag)
{
  GEN O = get_maxord(S, T0, flag);
  GEN f = S->T, P = S->dTP, a = NULL, da = NULL, P2, E2, D;
  long n = degpol(f), lP = lg(P), i, j, k;
  int centered = 0;
  pari_sp av = avma;
  /* r1 & basden not initialized here */
  S->r1 = -1;
  S->basden = NULL;
  for (i=1; i<lP; i++)
  {
    GEN M, db, b = gel(O,i);
    if (b == gen_1) continue;
    db = diag_denom(b);
    if (db == gen_1) continue;

    /* db = denom(b), (da,db) = 1. Compute da Im(b) + db Im(a) */
    b = Q_muli_to_int(b,db);
    if (!da) { da = db; a = b; }
    else
    { /* optimization: easy as long as both matrix are diagonal */
      j=2; while (j<=n && fnz(gel(a,j),j) && fnz(gel(b,j),j)) j++;
      k = j-1; M = cgetg(2*n-k+1,t_MAT);
      for (j=1; j<=k; j++)
      {
        gel(M,j) = gel(a,j);
        gcoeff(M,j,j) = mulii(gcoeff(a,j,j),gcoeff(b,j,j));
      }
      /* could reduce mod M(j,j) but not worth it: usually close to da*db */
      for (  ; j<=n;     j++) gel(M,j) = ZC_Z_mul(gel(a,j), db);
      for (  ; j<=2*n-k; j++) gel(M,j) = ZC_Z_mul(gel(b,j+k-n), da);
      da = mulii(da,db);
      a = ZM_hnfmodall_i(M, da, hnf_MODID|hnf_CENTER);
      gerepileall(av, 2, &a, &da);
      centered = 1;
    }
  }
  if (da)
  {
    GEN index = diviiexact(da, gcoeff(a,1,1));
    for (j=2; j<=n; j++) index = mulii(index, diviiexact(da, gcoeff(a,j,j)));
    if (!centered) a = ZM_hnfcenter(a);
    a = RgM_Rg_div(a, da);
    S->index = index;
    S->dK = diviiexact(S->dT, sqri(index));
  }
  else
  {
    S->index = gen_1;
    S->dK = S->dT;
    a = matid(n);
  }

  D = S->dK;
  P2 = cgetg(lP, t_COL);
  E2 = cgetg(lP, t_VECSMALL);
  for (k = j = 1; j < lP; j++)
  {
    long v = Z_pvalrem(D, gel(P,j), &D);
    if (v) { gel(P2,k) = gel(P,j); E2[k] = v; k++; }
  }
  setlg(P2, k); S->dKP = P2;
  setlg(E2, k); S->dKE = E2;
  S->basis = RgM_to_RgXV(a, varn(f));
}
GEN
nfbasis(GEN x, GEN *pdK, GEN fa)
{
  pari_sp av = avma;
  nfmaxord_t S;
  GEN B;
  nfmaxord(&S, fa? mkvec2(x,fa): x, 0);
  B = RgXV_unscale(S.basis, S.unscale);
  if (pdK)  *pdK = S.dK;
  gerepileall(av, pdK? 2: 1, &B, pdK); return B;
}
GEN
nfdisc(GEN x)
{
  pari_sp av = avma;
  nfmaxord_t S;
  GEN O = get_maxord(&S, x, 0);
  long n = degpol(S.T), lP = lg(O), i, j;
  GEN index = gen_1;
  for (i=1; i<lP; i++)
  {
    GEN b = gel(O,i);
    if (b == gen_1) continue;
    for (j = 1; j <= n; j++)
    {
      GEN c = gcoeff(b,j,j);
      if (typ(c) == t_FRAC) index = mulii(index, gel(c,2)) ;
    }
  }
  return gerepileuptoint(av, diviiexact(S.dT, sqri(index)));
}

GEN
nfbasis_gp(GEN x) { return nfbasis(x,NULL,NULL); }

static ulong
Flx_checkdeflate(GEN x)
{
  ulong d = 0, i, lx = (ulong)lg(x);
  for (i=3; i<lx; i++)
    if (x[i]) { d = ugcd(d,i-2); if (d == 1) break; }
  return d;
}

/* product of (monic) irreducible factors of f over Fp[X]
 * Assume f reduced mod p, otherwise valuation at x may be wrong */
static GEN
Flx_radical(GEN f, ulong p)
{
  long v0 = Flx_valrem(f, &f);
  ulong du, d, e;
  GEN u;

  d = Flx_checkdeflate(f);
  if (!d) return v0? polx_Flx(f[1]): pol1_Flx(f[1]);
  if (u_lvalrem(d,p, &e)) f = Flx_deflate(f, d/e); /* f(x^p^i) -> f(x) */
  u = Flx_gcd(f, Flx_deriv(f, p), p); /* (f,f') */
  du = degpol(u);
  if (du)
  {
    if (du == (ulong)degpol(f))
      f = Flx_radical(Flx_deflate(f,p), p);
    else
    {
      u = Flx_normalize(u, p);
      f = Flx_div(f, u, p);
      if (p <= du)
      {
        GEN w = Flxq_powu(f, du, u, p);
        w = Flx_div(u, Flx_gcd(w,u,p), p); /* u / gcd(u, v^(deg u-1)) */
        f = Flx_mul(f, Flx_radical(Flx_deflate(w,p), p), p);
      }
    }
  }
  if (v0) f = Flx_shift(f, 1);
  return f;
}
/* Assume f reduced mod p, otherwise valuation at x may be wrong */
static GEN
FpX_radical(GEN f, GEN p)
{
  GEN u;
  long v0;
  if (lgefint(p) == 3)
  {
    ulong q = p[2];
    return Flx_to_ZX( Flx_radical(ZX_to_Flx(f, q), q) );
  }
  v0 = ZX_valrem(f, &f);
  u = FpX_gcd(f,FpX_deriv(f, p), p);
  if (degpol(u)) f = FpX_div(f, u, p);
  if (v0) f = RgX_shift(f, 1);
  return f;
}
/* f / a */
static GEN
zx_z_div(GEN f, ulong a)
{
  long i, l = lg(f);
  GEN g = cgetg(l, t_VECSMALL);
  g[1] = f[1];
  for (i = 2; i < l; i++) g[i] = f[i] / a;
  return g;
}
/* Dedekind criterion; return k = gcd(g,h, (f-gh)/p), where
 *   f = \prod f_i^e_i, g = \prod f_i, h = \prod f_i^{e_i-1}
 * k = 1 iff Z[X]/(f) is p-maximal */
static GEN
ZX_Dedekind(GEN F, GEN *pg, GEN p)
{
  GEN k, h, g, f, f2;
  ulong q = p[2];
  if (lgefint(p) == 3 && q < (1UL << BITS_IN_HALFULONG))
  {
    ulong q = p[2], q2 = q*q;
    f2 = ZX_to_Flx(F, q2);
    f = Flx_red(f2, q);
    g = Flx_radical(f, q);
    h = Flx_div(f, g, q);
    k = zx_z_div(Flx_sub(f2, Flx_mul(g,h,q2), q2), q);
    k = Flx_gcd(k, Flx_gcd(g,h,q), q);
    k = Flx_to_ZX(k);
    g = Flx_to_ZX(g);
  }
  else
  {
    f2 = FpX_red(F, sqri(p));
    f = FpX_red(f2, p);
    g = FpX_radical(f, p);
    h = FpX_div(f, g, p);
    k = ZX_Z_divexact(ZX_sub(f2, ZX_mul(g,h)), p);
    k = FpX_gcd(FpX_red(k, p), FpX_gcd(g,h,p), p);
  }
  *pg = g; return k;
}

/* p-maximal order of Z[x]/f; mf = v_p(Disc(f)) or < 0 [unknown].
 * Return gen_1 if p-maximal */
static GEN
maxord(GEN p, GEN f, long mf)
{
  const pari_sp av = avma;
  GEN res, g, k = ZX_Dedekind(f, &g, p);
  long dk = degpol(k);
  if (DEBUGLEVEL>2) err_printf("  ZX_dedekind: gcd has degree %ld\n", dk);
  if (!dk) { avma = av; return gen_1; }
  if (mf < 0) mf = ZpX_disc_val(f, p);
  k = FpX_normalize(k, p);
  if (2*dk >= mf-1)
    res = dbasis(p, f, mf, NULL, FpX_div(f,k,p));
  else
  {
    GEN w, F1, F2;
    decomp_t S;
    F1 = FpX_factor(k,p);
    F2 = FpX_factor(FpX_div(g,k,p),p);
    w = merge_sort_uniq(gel(F1,1),gel(F2,1),(void*)cmpii,&gen_cmp_RgX);
    res = maxord_i(&S, p, f, mf, w, 0);
  }
  return gerepilecopy(av,res);
}
/* T monic separable ZX, p prime */
GEN
ZpX_primedec(GEN T, GEN p)
{
  const pari_sp av = avma;
  GEN w, F1, F2, res, g, k = ZX_Dedekind(T, &g, p);
  decomp_t S;
  if (!degpol(k)) return zm_to_ZM(FpX_degfact(T, p));
  k = FpX_normalize(k, p);
  F1 = FpX_factor(k,p);
  F2 = FpX_factor(FpX_div(g,k,p),p);
  w = merge_sort_uniq(gel(F1,1),gel(F2,1),(void*)cmpii,&gen_cmp_RgX);
  res = maxord_i(&S, p, T, ZpX_disc_val(T, p), w, -1);
  if (!res)
  {
    long f = degpol(S.nu), e = degpol(T) / f;
    avma = av; retmkmat2(mkcols(f), mkcols(e));
  }
  return gerepilecopy(av,res);
}

static GEN
Zlx_sylvester_echelon(GEN f1, GEN f2, long early_abort, ulong p, ulong pm)
{
  long j, n = degpol(f1);
  GEN h, a = cgetg(n+1,t_MAT);
  f1 = Flx_get_red(f1, pm);
  h = Flx_rem(f2,f1,pm);
  for (j=1;; j++)
  {
    gel(a,j) = Flx_to_Flv(h, n);
    if (j == n) break;
    h = Flx_rem(Flx_shift(h, 1), f1, pm);
  }
  return zlm_echelon(a, early_abort, p, pm);
}
/* Sylvester's matrix, mod p^m (assumes f1 monic). If early_abort
 * is set, return NULL if one pivot is 0 mod p^m */
static GEN
ZpX_sylvester_echelon(GEN f1, GEN f2, long early_abort, GEN p, GEN pm)
{
  long j, n = degpol(f1);
  GEN h, a = cgetg(n+1,t_MAT);
  h = FpXQ_red(f2,f1,pm);
  for (j=1;; j++)
  {
    gel(a,j) = RgX_to_RgC(h, n);
    if (j == n) break;
    h = FpX_rem(RgX_shift_shallow(h, 1), f1, pm);
  }
  return ZpM_echelon(a, early_abort, p, pm);
}

/* polynomial gcd mod p^m (assumes f1 monic). Return a QpX ! */
static GEN
Zlx_gcd(GEN f1, GEN f2, ulong p, ulong pm)
{
  pari_sp av = avma;
  GEN a = Zlx_sylvester_echelon(f1,f2,0,p,pm);
  long c, l = lg(a), sv = f1[1];
  for (c = 1; c < l; c++)
  {
    ulong t = ucoeff(a,c,c);
    if (t)
    {
      a = Flx_to_ZX(Flv_to_Flx(gel(a,c), sv));
      if (t == 1) return gerepilecopy(av, a);
      return gerepileupto(av, RgX_Rg_div(a, utoipos(t)));
    }
  }
  avma = av;
  a = cgetg(2,t_POL); a[1] = sv; return a;
}
GEN
ZpX_gcd(GEN f1, GEN f2, GEN p, GEN pm)
{
  pari_sp av = avma;
  GEN a;
  long c, l, v;
  if (lgefint(pm) == 3)
  {
    ulong q = pm[2];
    return Zlx_gcd(ZX_to_Flx(f1, q), ZX_to_Flx(f2,q), p[2], q);
  }
  a = ZpX_sylvester_echelon(f1,f2,0,p,pm);
  l = lg(a); v = varn(f1);
  for (c = 1; c < l; c++)
  {
    GEN t = gcoeff(a,c,c);
    if (signe(t))
    {
      a = RgV_to_RgX(gel(a,c), v);
      if (equali1(t)) return gerepilecopy(av, a);
      return gerepileupto(av, RgX_Rg_div(a, t));
    }
  }
  avma = av; return pol_0(v);
}

/* Return m > 0, such that p^m ~ 2^16 for initial value of m; p > 1 */
static long
init_m(GEN p)
{
  if (lgefint(p) > 3) return 1;
  return (long)(16 / log2(p[2]));
}

/* reduced resultant mod p^m (assumes x monic) */
GEN
ZpX_reduced_resultant(GEN x, GEN y, GEN p, GEN pm)
{
  pari_sp av = avma;
  GEN z;
  if (lgefint(pm) == 3)
  {
    ulong q = pm[2];
    z = Zlx_sylvester_echelon(ZX_to_Flx(x,q), ZX_to_Flx(y,q),0,p[2],q);
    if (lg(z) > 1)
    {
      ulong c = ucoeff(z,1,1);
      if (c) { avma = av; return utoipos(c); }
    }
  }
  else
  {
    z = ZpX_sylvester_echelon(x,y,0,p,pm);
    if (lg(z) > 1)
    {
      GEN c = gcoeff(z,1,1);
      if (signe(c)) return gerepileuptoint(av, c);
    }
  }
  avma = av; return gen_0;
}
/* Assume Res(f,g) divides p^M. Return Res(f, g), using dynamic p-adic
 * precision (until result is non-zero or p^M). */
GEN
ZpX_reduced_resultant_fast(GEN f, GEN g, GEN p, long M)
{
  GEN R, q = NULL;
  long m;
  m = init_m(p); if (m < 1) m = 1;
  for(;; m <<= 1) {
    if (M < 2*m) break;
    q = q? sqri(q): powiu(p, m); /* p^m */
    R = ZpX_reduced_resultant(f,g, p, q); if (signe(R)) return R;
  }
  q = powiu(p, M);
  R = ZpX_reduced_resultant(f,g, p, q); return signe(R)? R: q;
}

/* v_p(Res(x,y) mod p^m), assumes (lc(x),p) = 1 */
static long
ZpX_resultant_val_i(GEN x, GEN y, GEN p, GEN pm)
{
  pari_sp av = avma;
  GEN z;
  long i, l, v;
  if (lgefint(pm) == 3)
  {
    ulong q = pm[2], pp = p[2];
    z = Zlx_sylvester_echelon(ZX_to_Flx(x,q), ZX_to_Flx(y,q), 1, pp, q);
    if (!z) { avma = av; return -1; } /* failure */
    v = 0; l = lg(z);
    for (i = 1; i < l; i++) v += u_lval(ucoeff(z,i,i), pp);
  }
  else
  {
    z = ZpX_sylvester_echelon(x, y, 1, p, pm);
    if (!z) { avma = av; return -1; } /* failure */
    v = 0; l = lg(z);
    for (i = 1; i < l; i++) v += Z_pval(gcoeff(z,i,i), p);
  }
  return v;
}

/* assume (lc(f),p) = 1; no assumption on g */
long
ZpX_resultant_val(GEN f, GEN g, GEN p, long M)
{
  pari_sp av = avma;
  GEN q = NULL;
  long v, m;
  m = init_m(p); if (m < 2) m = 2;
  for(;; m <<= 1) {
    if (m > M) m = M;
    q = q? sqri(q): powiu(p, m); /* p^m */
    v = ZpX_resultant_val_i(f,g, p, q); if (v >= 0) break;
    if (m == M) return M;
  }
  avma = av; return v;
}

/* assume f separable and (lc(f),p) = 1 */
long
ZpX_disc_val(GEN f, GEN p)
{
  pari_sp av = avma;
  long v;
  if (degpol(f) == 1) return 0;
  v = ZpX_resultant_val(f, ZX_deriv(f), p, LONG_MAX);
  avma = av; return v;
}

/* *e a ZX, *d, *z in Z, *d = p^(*vd). Simplify e / d by cancelling a
 * common factor p^v; if z!=NULL, update it by cancelling the same power of p */
static void
update_den(GEN p, GEN *e, GEN *d, long *vd, GEN *z)
{
  GEN newe;
  long ve = ZX_pvalrem(*e, p, &newe);
  if (ve) {
    GEN newd;
    long v = minss(*vd, ve);
    if (v) {
      if (v == *vd)
      { /* rare, denominator cancelled */
        if (ve != v) newe = ZX_Z_mul(newe, powiu(p, ve - v));
        newd = gen_1;
        *vd = 0;
        if (z) *z =diviiexact(*z, powiu(p, v));
      }
      else
      { /* v = ve < vd, generic case */
        GEN q = powiu(p, v);
        newd = diviiexact(*d, q);
        *vd -= v;
        if (z) *z = diviiexact(*z, q);
      }
      *e = newe;
      *d = newd;
    }
  }
}

/* return denominator, a power of p */
static GEN
QpX_denom(GEN x)
{
  long i, l = lg(x);
  GEN maxd = gen_1;
  for (i=2; i<l; i++)
  {
    GEN d = gel(x,i);
    if (typ(d) == t_FRAC && cmpii(gel(d,2), maxd) > 0) maxd = gel(d,2);
  }
  return maxd;
}
static GEN
QpXV_denom(GEN x)
{
  long l = lg(x), i;
  GEN maxd = gen_1;
  for (i = 1; i < l; i++)
  {
    GEN d = QpX_denom(gel(x,i));
    if (cmpii(d, maxd) > 0) maxd = d;
  }
  return maxd;
}

static GEN
QpX_remove_denom(GEN x, GEN p, GEN *pdx, long *pv)
{
  *pdx = QpX_denom(x);
  if (*pdx == gen_1) { *pv = 0; *pdx = NULL; }
  else {
    x = Q_muli_to_int(x,*pdx);
    *pv = Z_pval(*pdx, p);
  }
  return x;
}

/* p^v * f o g mod (T,q). q = p^vq  */
static GEN
compmod(GEN p, GEN f, GEN g, GEN T, GEN q, long v)
{
  GEN D = NULL, z, df, dg, qD;
  long vD = 0, vdf, vdg;

  f = QpX_remove_denom(f, p, &df, &vdf);
  if (typ(g) == t_VEC) /* [num,den,v_p(den)] */
  { vdg = itos(gel(g,3)); dg = gel(g,2); g = gel(g,1); }
  else
    g = QpX_remove_denom(g, p, &dg, &vdg);
  if (df) { D = df; vD = vdf; }
  if (dg) {
    long degf = degpol(f);
    D = mul_content(D, powiu(dg, degf));
    vD += degf * vdg;
  }
  qD = D ? mulii(q, D): q;
  if (dg) f = FpX_rescale(f, dg, qD);
  z = FpX_FpXQ_eval(f, g, T, qD);
  if (!D) {
    if (v) {
      if (v > 0)
        z = ZX_Z_mul(z, powiu(p, v));
      else
        z = RgX_Rg_div(z, powiu(p, -v));
    }
    return z;
  }
  update_den(p, &z, &D, &vD, NULL);
  qD = mulii(D,q);
  if (v) vD -= v;
  z = FpX_center_i(z, qD, shifti(qD,-1));
  if (vD > 0)
    z = RgX_Rg_div(z, powiu(p, vD));
  else if (vD < 0)
    z = ZX_Z_mul(z, powiu(p, -vD));
  return z;
}

/* fast implementation of ZM_hnfmodid(M, D) / D, D = p^k */
static GEN
ZpM_hnfmodid(GEN M, GEN p, GEN D)
{
  long i, l = lg(M);
  M = RgM_Rg_div(ZpM_echelon(M,0,p,D), D);
  for (i = 1; i < l; i++)
    if (gequal0(gcoeff(M,i,i))) gcoeff(M,i,i) = gen_1;
  return M;
}

/* Return Z-basis for Z[a] + U(a)/p Z[a] in Z[t]/(f), mf = v_p(disc f), U
 * a ZX. Special cases: a = t is coded as NULL, U = 0 is coded as NULL */
static GEN
dbasis(GEN p, GEN f, long mf, GEN a, GEN U)
{
  long n = degpol(f), i, dU;
  GEN b, h;

  if (n == 1) return matid(1);
  if (a && gequalX(a)) a = NULL;
  if (DEBUGLEVEL>5)
  {
    err_printf("  entering Dedekind Basis with parameters p=%Ps\n",p);
    err_printf("  f = %Ps,\n  a = %Ps\n",f, a? a: pol_x(varn(f)));
  }
  if (a)
  {
    GEN pd = powiu(p, mf >> 1);
    GEN da, pdp = mulii(pd,p), D = pdp;
    long vda;
    dU = U ? degpol(U): 0;
    b = cgetg(n+1, t_MAT);
    h = scalarpol(pd, varn(f));
    a = QpX_remove_denom(a, p, &da, &vda);
    if (da) D = mulii(D, da);
    gel(b,1) = scalarcol_shallow(pd, n);
    for (i=2; i<=n; i++)
    {
      if (i == dU+1)
        h = compmod(p, U, mkvec3(a,da,stoi(vda)), f, pdp, (mf>>1) - 1);
      else
      {
        h = FpXQ_mul(h, a, f, D);
        if (da) h = ZX_Z_divexact(h, da);
      }
      gel(b,i) = RgX_to_RgC(h,n);
    }
    return ZpM_hnfmodid(b, p, pd);
  }
  else
  {
    if (!U) return matid(n);
    dU = degpol(U);
    if (dU == n) return matid(n);
    U = FpX_normalize(U, p);
    b = cgetg(n+1, t_MAT);
    for (i = 1; i <= dU; i++) gel(b,i) = vec_ei(n, i);
    h = RgX_Rg_div(U, p);
    for ( ; i <= n; i++)
    {
      gel(b, i) = RgX_to_RgC(h,n);
      if (i == n) break;
      h = RgX_shift_shallow(h,1);
    }
    return b;
  }
}

static GEN
get_partial_order_as_pols(GEN p, GEN f)
{
  GEN O = maxord(p, f, -1);
  long v = varn(f);
  return O == gen_1? pol_x_powers(degpol(f), v): RgM_to_RgXV(O, v);
}

static long
p_is_prime(decomp_t *S)
{
  if (S->pisprime < 0) S->pisprime = BPSW_psp(S->p);
  return S->pisprime;
}
static GEN ZpX_monic_factor_squarefree(GEN f, GEN p, long prec);

/* if flag = 0, maximal order, else factorization to precision r = flag */
static GEN
Decomp(decomp_t *S, long flag)
{
  pari_sp av = avma;
  GEN fred, pr2, pr, pk, ph2, ph, b1, b2, a, e, de, f1, f2, dt, th, chip;
  GEN p = S->p;
  long vde, vdt, k, r = maxss(flag, 2*S->df + 1);

  if (DEBUGLEVEL>5) err_printf("  entering Decomp: %Ps^%ld\n  f = %Ps\n",
                               p, r, S->f);
  else if (DEBUGLEVEL>2) err_printf("  entering Decomp\n");
  chip = FpX_red(S->chi, p);
  if (!FpX_valrem(chip, S->nu, p, &b1))
  {
    if (!p_is_prime(S)) pari_err_PRIME("Decomp",p);
    pari_err_BUG("Decomp (not a factor)");
  }
  b2 = FpX_div(chip, b1, p);
  a = FpX_mul(FpXQ_inv(b2, b1, p), b2, p);
  /* E = e / de, e in Z[X], de in Z,  E = a(phi) mod (f, p) */
  th = QpX_remove_denom(S->phi, p, &dt, &vdt);
  if (dt)
  {
    long dega = degpol(a);
    vde = dega * vdt;
    de = powiu(dt, dega);
    pr = mulii(p, de);
    a = FpX_rescale(a, dt, pr);
  }
  else
  {
    vde = 0;
    de = gen_1;
    pr = p;
  }
  e = FpX_FpXQ_eval(a, th, S->f, pr);
  update_den(p, &e, &de, &vde, NULL);

  pk = p; k = 1;
  /* E, (1 - E) tend to orthogonal idempotents in Zp[X]/(f) */
  while (k < r + vde)
  { /* E <-- E^2(3-2E) mod p^2k, with E = e/de */
    GEN D;
    pk = sqri(pk); k <<= 1;
    e = ZX_mul(ZX_sqr(e), Z_ZX_sub(mului(3,de), gmul2n(e,1)));
    de= mulii(de, sqri(de));
    vde *= 3;
    D = mulii(pk, de);
    e = FpX_rem(e, centermod(S->f, D), D); /* e/de defined mod pk */
    update_den(p, &e, &de, &vde, NULL);
  }
  /* required precision of the factors */
  pr = powiu(p, r); pr2 = shifti(pr, -1);
  ph = mulii(de,pr);ph2 = shifti(ph, -1);
  fred = FpX_center_i(FpX_red(S->f, ph), ph, ph2);
  e    = FpX_center_i(FpX_red(e, ph), ph, ph2);

  f1 = ZpX_gcd(fred, Z_ZX_sub(de, e), p, ph); /* p-adic gcd(f, 1-e) */
  fred = FpX_center_i(fred, pr, pr2);
  f1   = FpX_center_i(f1,   pr, pr2);
  f2 = FpX_div(fred,f1, pr);
  f2 = FpX_center_i(f2, pr, pr2);

  if (DEBUGLEVEL>5)
    err_printf("  leaving Decomp: f1 = %Ps\nf2 = %Ps\ne = %Ps\nde= %Ps\n", f1,f2,e,de);

  if (flag < 0)
  {
    GEN m = vconcat(ZpX_primedec(f1, p), ZpX_primedec(f2, p));
    return sort_factor(m, (void*)&cmpii, &cmp_nodata);
  }
  else if (flag)
  {
    gerepileall(av, 2, &f1, &f2);
    return shallowconcat(ZpX_monic_factor_squarefree(f1, p, flag),
                         ZpX_monic_factor_squarefree(f2, p, flag));
  } else {
    GEN D, d1, d2, B1, B2, M;
    long n, n1, n2, i;
    gerepileall(av, 4, &f1, &f2, &e, &de);
    D = de;
    B1 = get_partial_order_as_pols(p,f1); n1 = lg(B1)-1;
    B2 = get_partial_order_as_pols(p,f2); n2 = lg(B2)-1; n = n1+n2;
    d1 = QpXV_denom(B1);
    d2 = QpXV_denom(B2); if (cmpii(d1, d2) < 0) d1 = d2;
    if (d1 != gen_1) {
      B1 = Q_muli_to_int(B1, d1);
      B2 = Q_muli_to_int(B2, d1);
      D = mulii(d1, D);
    }
    fred = centermod_i(S->f, D, shifti(D,-1));
    M = cgetg(n+1, t_MAT);
    for (i=1; i<=n1; i++)
      gel(M,i) = RgX_to_RgC(FpX_rem(FpX_mul(gel(B1,i),e,D), fred, D), n);
    e = Z_ZX_sub(de, e); B2 -= n1;
    for (   ; i<=n; i++)
      gel(M,i) = RgX_to_RgC(FpX_rem(FpX_mul(gel(B2,i),e,D), fred, D), n);
    return ZpM_hnfmodid(M, p, D);
  }
}

/* minimum extension valuation: L/E */
static void
vstar(GEN p,GEN h, long *L, long *E)
{
  long first, j, k, v, w, m = degpol(h);

  first = 1; k = 1; v = 0;
  for (j=1; j<=m; j++)
  {
    GEN c = gel(h, m-j+2);
    if (signe(c))
    {
      w = Z_pval(c,p);
      if (first || w*k < v*j) { v = w; k = j; }
      first = 0;
    }
  }
  /* v/k = min_j ( v_p(h_{m-j}) / j ) */
  w = (long)ugcd(v,k);
  *L = v/w;
  *E = k/w;
}

static GEN
redelt_i(GEN a, GEN N, GEN p, GEN *pda, long *pvda)
{
  GEN z;
  a = Q_remove_denom(a, pda);
  *pvda = 0;
  if (*pda)
  {
    long v = Z_pvalrem(*pda, p, &z);
    if (v) {
      *pda = powiu(p, v);
      *pvda = v;
      N  = mulii(*pda, N);
    }
    else
      *pda = NULL;
    if (!is_pm1(z)) a = ZX_Z_mul(a, Fp_inv(z, N));
  }
  return centermod(a, N);
}
/* reduce the element a modulo N [ a power of p ], taking first care of the
 * denominators */
static GEN
redelt(GEN a, GEN N, GEN p)
{
  GEN da;
  long vda;
  a = redelt_i(a, N, p, &da, &vda);
  if (da) a = RgX_Rg_div(a, da);
  return a;
}

/* compute the c first Newton sums modulo pp of the
   characteristic polynomial of a/d mod chi, d > 0 power of p (NULL = gen_1),
   a, chi in Zp[X], vda = v_p(da)
   ns = Newton sums of chi */
static GEN
newtonsums(GEN p, GEN a, GEN da, long vda, GEN chi, long c, GEN pp, GEN ns)
{
  GEN va, pa, dpa, s;
  long j, k, vdpa, lns = lg(ns);
  pari_sp av;

  a = centermod(a, pp); av = avma;
  dpa = pa = NULL; /* -Wall */
  vdpa = 0;
  va = zerovec(c);
  for (j = 1; j <= c; j++)
  { /* pa/dpa = (a/d)^(j-1) mod (chi, pp), dpa = p^vdpa */
    long l;
    pa = j == 1? a: FpXQ_mul(pa, a, chi, pp);
    l = lg(pa); if (l == 2) break;
    if (lns < l) l = lns;

    if (da) {
      dpa = j == 1? da: mulii(dpa, da);
      vdpa += vda;
      update_den(p, &pa, &dpa, &vdpa, &pp);
    }
    s = mulii(gel(pa,2), gel(ns,2)); /* k = 2 */
    for (k = 3; k < l; k++) s = addii(s, mulii(gel(pa,k), gel(ns,k)));
    if (da) {
      GEN r;
      s = dvmdii(s, dpa, &r);
      if (r != gen_0) return NULL;
    }
    gel(va,j) = centermodii(s, pp, shifti(pp,-1));

    if (gc_needed(av, 1))
    {
      if(DEBUGMEM>1) pari_warn(warnmem, "newtonsums");
      gerepileall(av, dpa?4:3, &pa, &va, &pp, &dpa);
    }
  }
  for (; j <= c; j++) gel(va,j) = gen_0;
  return va;
}

/* compute the characteristic polynomial of a/da mod chi (a in Z[X]), given
 * by its Newton sums to a precision of pp using Newton sums */
static GEN
newtoncharpoly(GEN pp, GEN p, GEN NS)
{
  long n = lg(NS)-1, j, k;
  GEN c = cgetg(n + 2, t_VEC), pp2 = shifti(pp,-1);

  gel(c,1) = (n & 1 ? gen_m1: gen_1);
  for (k = 2; k <= n+1; k++)
  {
    pari_sp av2 = avma;
    GEN s = gen_0;
    ulong z;
    long v = u_pvalrem(k - 1, p, &z);
    for (j = 1; j < k; j++)
    {
      GEN t = mulii(gel(NS,j), gel(c,k-j));
      if (!odd(j)) t = negi(t);
      s = addii(s, t);
    }
    if (v) {
      s = gdiv(s, powiu(p, v));
      if (typ(s) != t_INT) return NULL;
    }
    s = mulii(s, Fp_inv(utoipos(z), pp));
    gel(c,k) = gerepileuptoint(av2, Fp_center_i(s, pp, pp2));
  }
  for (k = odd(n)? 1: 2; k <= n+1; k += 2) gel(c,k) = negi(gel(c,k));
  return gtopoly(c, 0);
}

static void
manage_cache(decomp_t *S, GEN f, GEN pp)
{
  GEN t = S->precns;

  if (!t) t = mulii(S->pmf, powiu(S->p, S->df));
  if (cmpii(t, pp) < 0) t = pp;

  if (!S->precns || !RgX_equal(f, S->nsf) || cmpii(S->precns, t) < 0)
  {
    if (DEBUGLEVEL>4)
      err_printf("  Precision for cached Newton sums for %Ps: %Ps -> %Ps\n",
                 f, S->precns? S->precns: gen_0, t);
    S->nsf = f;
    S->ns = FpX_Newton(f, degpol(f), t);
    S->precns = t;
  }
}

/* return NULL if a mod f is not an integer
 * The denominator of any integer in Zp[X]/(f) divides pdr */
static GEN
mycaract(decomp_t *S, GEN f, GEN a, GEN pp, GEN pdr)
{
  pari_sp av;
  GEN d, chi, prec1, prec2, prec3, ns;
  long vd, n = degpol(f);

  if (gequal0(a)) return pol_0(varn(f));

  a = QpX_remove_denom(a, S->p, &d, &vd);
  prec1 = pp;
  if (lgefint(S->p) == 3)
    prec1 = mulii(prec1, powiu(S->p, factorial_lval(n, itou(S->p))));
  if (d)
  {
    GEN p1 = powiu(d, n);
    prec2 = mulii(prec1, p1);
    prec3 = mulii(prec1, gmin_shallow(mulii(p1, d), pdr));
  }
  else
    prec2 = prec3 = prec1;
  manage_cache(S, f, prec3);

  av = avma;
  ns = newtonsums(S->p, a, d, vd, f, n, prec2, S->ns);
  if (!ns) return NULL;
  chi = newtoncharpoly(prec1, S->p, ns);
  if (!chi) return NULL;
  setvarn(chi, varn(f));
  return gerepileupto(av, centermod(chi, pp));
}

static GEN
get_nu(GEN chi, GEN p, long *ptl)
{ /* split off powers of x first for efficiency */
  long v = ZX_valrem(FpX_red(chi,p), &chi), n;
  GEN P;
  if (!degpol(chi)) { *ptl = 1; return pol_x(varn(chi)); }
  P = gel(FpX_factor(chi,p), 1); n = lg(P)-1;
  *ptl = v? n+1: n; return gel(P,n);
}

/* Factor characteristic polynomial chi of phi mod p. If it splits, update
 * S->{phi, chi, nu} and return 1. In any case, set *nu to an irreducible
 * factor mod p of chi */
static int
split_char(decomp_t *S, GEN chi, GEN phi, GEN phi0, GEN *nu)
{
  long l;
  *nu  = get_nu(chi, S->p, &l);
  if (l == 1) return 0; /* single irreducible factor: doesn't split */
  /* phi o phi0 mod (p, f) */
  S->phi = compmod(S->p, phi, phi0, S->f, S->p, 0);
  S->chi = chi;
  S->nu = *nu; return 1;
}

/* Return the prime element in Zp[phi], a t_INT (iff *Ep = 1) or QX;
 * nup, chip are ZX. phi = NULL codes X
 * If *Ep < oE or Ep divides Ediv (!=0) return NULL (uninteresting) */
static GEN
getprime(decomp_t *S, GEN phi, GEN chip, GEN nup, long *Lp, long *Ep,
         long oE, long Ediv)
{
  GEN z, chin, q, qp;
  long r, s;

  if (phi && dvdii(constant_coeff(chip), S->psc))
  {
    chip = mycaract(S, S->chi, phi, S->pmf, S->prc);
    if (dvdii(constant_coeff(chip), S->pmf))
      chip = ZXQ_charpoly(phi, S->chi, varn(chip));
  }
  if (degpol(nup) == 1)
  {
    GEN c = gel(nup,2); /* nup = X + c */
    chin = signe(c)? RgX_translate(chip, negi(c)): chip;
  }
  else
    chin = ZXQ_charpoly(nup, chip, varn(chip));

  vstar(S->p, chin, Lp, Ep);
  if (*Ep < oE || (Ediv && Ediv % *Ep == 0)) return NULL;

  if (*Ep == 1) return S->p;
  (void)cbezout(*Lp, -*Ep, &r, &s); /* = 1 */
  if (r <= 0)
  {
    long t = 1 + ((-r) / *Ep);
    r += t * *Ep;
    s += t * *Lp;
  }
  /* r > 0 minimal such that r L/E - s = 1/E
   * pi = nu^r / p^s is an element of valuation 1/E,
   * so is pi + O(p) since 1/E < 1. May compute nu^r mod p^(s+1) */
  q = powiu(S->p, s); qp = mulii(q, S->p);
  nup = FpXQ_powu(nup, r, S->chi, qp);
  if (!phi) return RgX_Rg_div(nup, q); /* phi = X : no composition */
  z = compmod(S->p, nup, phi, S->chi, qp, -s);
  return signe(z)? z: NULL;
}

static int
update_phi(decomp_t *S)
{
  GEN PHI = NULL, prc, psc, X = pol_x(varn(S->f));
  long k;
  for (k = 1;; k++)
  {
    prc = ZpX_reduced_resultant_fast(S->chi, ZX_deriv(S->chi), S->p, S->vpsc);
    if (!equalii(prc, S->psc)) break;

    /* increase precision */
    S->vpsc = maxss(S->vpsf, S->vpsc + 1);
    S->psc = (S->vpsc == S->vpsf)? S->psf: mulii(S->psc, S->p);

    PHI = S->phi;
    if (S->phi0) PHI = compmod(S->p, PHI, S->phi0, S->f, S->psc, 0);
    PHI = gadd(PHI, ZX_Z_mul(X, mului(k, S->p)));
    S->chi = mycaract(S, S->f, PHI, S->psc, S->pdf);
  }
  psc = mulii(sqri(prc), S->p);

  if (!PHI) /* ok above for k = 1 */
  {
    PHI = S->phi;
    if (S->phi0)
    {
      PHI = compmod(S->p, PHI, S->phi0, S->f, psc, 0);
      S->chi = mycaract(S, S->f, PHI, psc, S->pdf);
    }
  }
  S->phi = PHI;
  S->chi = FpX_red(S->chi, psc);

  /* may happen if p is unramified */
  if (is_pm1(prc)) return 0;
  S->psc = psc;
  S->vpsc = 2*Z_pval(prc, S->p) + 1;
  S->prc = mulii(prc, S->p); return 1;
}

/* return 1 if at least 2 factors mod p ==> chi splits
 * Replace S->phi such that F increases (to D) */
static int
testb2(decomp_t *S, long D, GEN theta)
{
  long v = varn(S->chi), dlim = degpol(S->chi)-1;
  GEN T0 = S->phi, chi, phi, nu;
  if (DEBUGLEVEL>4) err_printf("  Increasing Fa\n");
  for (;;)
  {
    phi = gadd(theta, random_FpX(dlim, v, S->p));
    chi = mycaract(S, S->chi, phi, S->psf, S->prc);
    /* phi non-primary ? */
    if (split_char(S, chi, phi, T0, &nu)) return 1;
    if (degpol(nu) == D) break;
  }
  /* F_phi=lcm(F_alpha, F_theta)=D and E_phi=E_alpha */
  S->phi0 = T0;
  S->chi = chi;
  S->phi = phi;
  S->nu = nu; return 0;
}

/* return 1 if at least 2 factors mod p ==> chi can be split.
 * compute a new S->phi such that E = lcm(Ea, Et);
 * A a ZX, T a t_INT (iff Et = 1, probably impossible ?) or QX */
static int
testc2(decomp_t *S, GEN A, long Ea, GEN T, long Et)
{
  GEN c, chi, phi, nu, T0 = S->phi;

  if (DEBUGLEVEL>4) err_printf("  Increasing Ea\n");
  if (Et == 1) /* same as other branch, split for efficiency */
    c = A; /* Et = 1 => s = 1, r = 0, t = 0 */
  else
  {
    long r, s, t;
    (void)cbezout(Ea, Et, &r, &s); t = 0;
    while (r < 0) { r = r + Et; t++; }
    while (s < 0) { s = s + Ea; t++; }

    /* A^s T^r / p^t */
    c = RgXQ_mul(RgXQ_powu(A, s, S->chi), RgXQ_powu(T, r, S->chi), S->chi);
    c = RgX_Rg_div(c, powiu(S->p, t));
    c = redelt(c, S->psc, S->p);
  }
  phi = RgX_add(c,  pol_x(varn(S->chi)));
  chi = mycaract(S, S->chi, phi, S->psf, S->prc);
  if (split_char(S, chi, phi, T0, &nu)) return 1;
  /* E_phi = lcm(E_alpha,E_theta) */
  S->phi0 = T0;
  S->chi = chi;
  S->phi = phi;
  S->nu = nu; return 0;
}

/* Return h^(-degpol(P)) P(x * h) if result is integral, NULL otherwise */
static GEN
ZX_rescale_inv(GEN P, GEN h)
{
  long i, l = lg(P);
  GEN Q = cgetg(l,t_POL), hi = h;
  gel(Q,l-1) = gel(P,l-1);
  for (i=l-2; i>=2; i--)
  {
    GEN r;
    gel(Q,i) = dvmdii(gel(P,i), hi, &r);
    if (signe(r)) return NULL;
    if (i == 2) break;
    hi = mulii(hi,h);
  }
  Q[1] = P[1]; return Q;
}

/* x p^-eq nu^-er mod p */
static GEN
get_gamma(decomp_t *S, GEN x, long eq, long er)
{
  GEN q, g = x, Dg = powiu(S->p, eq);
  long vDg = eq;
  if (er)
  {
    if (!S->invnu)
    {
      while (gdvd(S->chi, S->nu)) S->nu = RgX_Rg_add(S->nu, S->p);
      S->invnu = QXQ_inv(S->nu, S->chi);
      S->invnu = redelt_i(S->invnu, S->psc, S->p, &S->Dinvnu, &S->vDinvnu);
    }
    if (S->Dinvnu) {
      Dg = mulii(Dg, powiu(S->Dinvnu, er));
      vDg += er * S->vDinvnu;
    }
    q = mulii(S->p, Dg);
    g = ZX_mul(g, FpXQ_powu(S->invnu, er, S->chi, q));
    g = FpX_rem(g, S->chi, q);
    update_den(S->p, &g, &Dg, &vDg, NULL);
    g = centermod(g, mulii(S->p, Dg));
  }
  if (!is_pm1(Dg)) g = RgX_Rg_div(g, Dg);
  return g;
}
static GEN
get_g(decomp_t *S, long Ea, long L, long E, GEN beta, GEN *pchig,
      long *peq, long *per)
{
  long eq, er;
  GEN g, chig, chib = NULL;
  for(;;) /* at most twice */
  {
    if (L < 0)
    {
      chib = ZXQ_charpoly(beta, S->chi, varn(S->chi));
      vstar(S->p, chib, &L, &E);
    }
    eq = L / E; er = L*Ea / E - eq*Ea;
    /* floor(L Ea/E) = eq Ea + er */
    if (er || !chib)
    { /* g might not be an integer ==> chig = NULL */
      g = get_gamma(S, beta, eq, er);
      chig = mycaract(S, S->chi, g, S->psc, S->prc);
    }
    else
    { /* g = beta/p^eq, special case of the above */
      GEN h = powiu(S->p, eq);
      g = RgX_Rg_div(beta, h);
      chig = ZX_rescale_inv(chib, h); /* chib(x h) / h^N */
      if (chig) chig = FpX_red(chig, S->pmf);
    }
    /* either success or second consecutive failure */
    if (chig || chib) break;
    /* if g fails the v*-test, v(beta) was wrong. Retry once */
    L = -1;
  }
  *pchig = chig; *peq = eq; *per = er; return g;
}

/* return 1 if at least 2 factors mod p ==> chi can be split */
static int
loop(decomp_t *S, long Ea)
{
  pari_sp av = avma;
  GEN beta = FpXQ_powu(S->nu, Ea, S->chi, S->p);
  long N = degpol(S->f), v = varn(S->f);
  S->invnu = NULL;
  for (;;)
  { /* beta tends to a factor of chi */
    long L, i, Fg, eq, er;
    GEN chig = NULL, d, g, nug;

    if (DEBUGLEVEL>4) err_printf("  beta = %Ps\n", beta);
    L = ZpX_resultant_val(S->chi, beta, S->p, S->mf+1);
    if (L > S->mf) L = -1; /* from scratch */
    g = get_g(S, Ea, L, N, beta, &chig, &eq, &er);
    if (DEBUGLEVEL>4) err_printf("  (eq,er) = (%ld,%ld)\n", eq,er);
    /* g = beta p^-eq  nu^-er (a unit), chig = charpoly(g) */
    if (split_char(S, chig, g,S->phi, &nug)) return 1;

    Fg = degpol(nug);
    if (Fg == 1)
    { /* frequent special case nug = x - d */
      long Le, Ee;
      GEN chie, nue, e, pie;
      d = negi(gel(nug,2));
      chie = RgX_translate(chig, d);
      nue = pol_x(v);
      e = RgX_Rg_sub(g, d);
      pie = getprime(S, e, chie, nue, &Le, &Ee,  0,Ea);
      if (pie) return testc2(S, S->nu, Ea, pie, Ee);
    }
    else
    {
      long Fa = degpol(S->nu), vdeng;
      GEN deng, numg, nume;
      if (Fa % Fg) return testb2(S, ulcm(Fa,Fg), g);
      /* nu & nug irreducible mod p, deg nug | deg nu. To improve beta, look
       * for a root d of nug in Fp[phi] such that v_p(g - d) > 0 */
      if (ZX_equal(nug, S->nu))
        d = pol_x(v);
      else
      {
        if (!p_is_prime(S)) pari_err_PRIME("FpX_ffisom",S->p);
        d = FpX_ffisom(nug, S->nu, S->p);
      }
      /* write g = numg / deng, e = nume / deng */
      numg = QpX_remove_denom(g, S->p, &deng, &vdeng);
      for (i = 1; i <= Fg; i++)
      {
        GEN chie, nue, e;
        if (i != 1) d = FpXQ_pow(d, S->p, S->nu, S->p); /* next root */
        nume = ZX_sub(numg, ZX_Z_mul(d, deng));
        /* test e = nume / deng */
        if (ZpX_resultant_val(S->chi, nume, S->p, vdeng*N+1) <= vdeng*N)
          continue;
        e = RgX_Rg_div(nume, deng);
        chie = mycaract(S, S->chi, e, S->psc, S->prc);
        if (split_char(S, chie, e,S->phi, &nue)) return 1;
        if (RgX_is_monomial(nue))
        { /* v_p(e) = v_p(g - d) > 0 */
          long Le, Ee;
          GEN pie;
          pie = getprime(S, e, chie, nue, &Le, &Ee,  0,Ea);
          if (pie) return testc2(S, S->nu, Ea, pie, Ee);
          break;
        }
      }
      if (i > Fg)
      {
        if (!p_is_prime(S)) pari_err_PRIME("nilord",S->p);
        pari_err_BUG("nilord (no root)");
      }
    }
    if (eq) d = gmul(d, powiu(S->p,  eq));
    if (er) d = gmul(d, gpowgs(S->nu, er));
    beta = gsub(beta, d);

    if (gc_needed(av,1))
    {
      if (DEBUGMEM > 1) pari_warn(warnmem, "nilord");
      gerepileall(av, S->invnu? 6: 4, &beta, &(S->precns), &(S->ns), &(S->nsf), &(S->invnu), &(S->Dinvnu));
    }
  }
}

/* E and F cannot decrease; return 1 if O = Zp[phi], 2 if we can get a
 * decomposition and 0 otherwise */
static long
progress(decomp_t *S, GEN *ppa, long *pE)
{
  long E = *pE, F;
  GEN pa = *ppa;
  S->phi0 = NULL; /* no delayed composition */
  for(;;)
  {
    long l, La, Ea; /* N.B If E = 0, getprime cannot return NULL */
    GEN pia  = getprime(S, NULL, S->chi, S->nu, &La, &Ea, E,0);
    if (pia) { /* success, we break out in THIS loop */
      pa = (typ(pia) == t_POL)? RgX_RgXQ_eval(pia, S->phi, S->f): pia;
      E = Ea;
      if (La == 1) break; /* no need to change phi so that nu = pia */
    }
    /* phi += prime elt */
    S->phi = typ(pa) == t_INT? RgX_Rg_add_shallow(S->phi, pa)
                             : RgX_add(S->phi, pa);
    /* recompute char. poly. chi from scratch */
    S->chi = mycaract(S, S->f, S->phi, S->psf, S->pdf);
    S->nu = get_nu(S->chi, S->p, &l);
    if (l > 1) return 2;
    if (!update_phi(S)) return 1; /* unramified */
    if (pia) break;
  }
  *pE = E; *ppa = pa; F = degpol(S->nu);
  if (DEBUGLEVEL>4) err_printf("  (E, F) = (%ld,%ld)\n", E, F);
  if (E * F == degpol(S->f)) return 1;
  if (loop(S, E)) return 2;
  if (!update_phi(S)) return 1;
  return 0;
}

/* flag != 0 iff we're looking for the p-adic factorization,
   in which case it is the p-adic precision we want */
static GEN
maxord_i(decomp_t *S, GEN p, GEN f, long mf, GEN w, long flag)
{
  long oE, n = lg(w)-1; /* factor of largest degree */
  GEN opa, D = ZpX_reduced_resultant_fast(f, ZX_deriv(f), p, mf);
  S->pisprime = -1;
  S->p = p;
  S->mf = mf;
  S->nu = gel(w,n);
  S->df = Z_pval(D, p);
  S->pdf = powiu(p, S->df);
  S->phi = pol_x(varn(f));
  S->chi = S->f = f;
  if (n > 1) return Decomp(S, flag); /* FIXME: use bezout_lift_fact */

  if (DEBUGLEVEL>4)
    err_printf("  entering Nilord: %Ps^%ld\n  f = %Ps, nu = %Ps\n",
               p, S->df, S->f, S->nu);
  else if (DEBUGLEVEL>2) err_printf("  entering Nilord\n");
  S->psf = S->psc = mulii(sqri(D), p);
  S->vpsf = S->vpsc = 2*S->df + 1;
  S->prc = mulii(D, p);
  S->chi = FpX_red(S->f, S->psc);
  S->pmf = powiu(p, S->mf+1);
  S->precns = NULL;
  for(opa = NULL, oE = 0;;)
  {
    long n = progress(S, &opa, &oE);
    if (n == 1) return flag? NULL: dbasis(p, S->f, S->mf, S->phi, S->chi);
    if (n == 2) return Decomp(S, flag);
  }
}

static int
expo_is_squarefree(GEN e)
{
  long i, l = lg(e);
  for (i=1; i<l; i++)
    if (e[i] != 1) return 0;
  return 1;
}
/* pure round 4 */
static GEN
ZpX_round4(GEN f, GEN p, GEN w, long prec)
{
  decomp_t S;
  GEN L = maxord_i(&S, p, f, ZpX_disc_val(f,p), w, prec);
  return L? L: mkvec(f);
}
/* f a squarefree ZX with leading_coeff 1, degree > 0. Return list of
 * irreducible factors in Zp[X] (computed mod p^prec) */
static GEN
ZpX_monic_factor_squarefree(GEN f, GEN p, long prec)
{
  pari_sp av = avma;
  GEN L, fa, w, e;
  long i, l;
  if (degpol(f) == 1) return mkvec(f);
  fa = FpX_factor(f,p); w = gel(fa,1); e = gel(fa,2);
  /* no repeated factors: Hensel lift */
  if (expo_is_squarefree(e)) return ZpX_liftfact(f, w, powiu(p,prec), p, prec);
  l = lg(w);
  if (l == 2)
  {
    L = ZpX_round4(f,p,w,prec);
    if (lg(L) == 2) { avma = av; return mkvec(f); }
  }
  else
  { /* >= 2 factors mod p: partial Hensel lift */
    GEN D = ZpX_reduced_resultant_fast(f, ZX_deriv(f), p, ZpX_disc_val(f,p));
    long r = maxss(2*Z_pval(D,p)+1, prec);
    GEN W = cgetg(l, t_VEC);
    for (i = 1; i < l; i++)
      gel(W,i) = e[i] == 1? gel(w,i): FpX_powu(gel(w,i), e[i], p);
    L = ZpX_liftfact(f, W, powiu(p,r), p, r);
    for (i = 1; i < l; i++)
      gel(L,i) = e[i] == 1? mkvec(gel(L,i))
                          : ZpX_round4(gel(L,i), p, mkvec(gel(w,i)), prec);
    L = shallowconcat1(L);
  }
  return gerepilecopy(av, L);
}

/* assume f a ZX with leading_coeff 1, degree > 0 */
GEN
ZpX_monic_factor(GEN f, GEN p, long prec)
{
  GEN poly, ex, P, E;
  long l, i;

  if (degpol(f) == 1) return mkmat2(mkcol(f), mkcol(gen_1));
  poly = ZX_squff(f,&ex); l = lg(poly);
  P = cgetg(l, t_VEC);
  E = cgetg(l, t_VEC);
  for (i = 1; i < l; i++)
  {
    GEN L = ZpX_monic_factor_squarefree(gel(poly,i), p, prec);
    gel(P,i) = L; settyp(L, t_COL);
    gel(E,i) = const_col(lg(L)-1, utoipos(ex[i]));
  }
  return mkmat2(shallowconcat1(P), shallowconcat1(E));
}

/* DT = multiple of disc(T) or NULL
 * Return a multiple of the denominator of an algebraic integer (in Q[X]/(T))
 * when expressed in terms of the power basis */
GEN
indexpartial(GEN T, GEN DT)
{
  pari_sp av = avma;
  long i, nb;
  GEN fa, E, P, res = gen_1, dT = ZX_deriv(T);

  if (!DT) DT = ZX_disc(T);
  fa = absZ_factor_limit(DT, 0);
  P = gel(fa,1);
  E = gel(fa,2); nb = lg(P)-1;
  for (i = 1; i <= nb; i++)
  {
    long e = itou(gel(E,i)), e2 = e >> 1;
    GEN p = gel(P,i), q = p;
    if (i == nb)
      q = powiu(p, (odd(e) && !BPSW_psp(p))? e2+1: e2);
    else if (e2 >= 2)
      q = ZpX_reduced_resultant_fast(T, dT, p, e2);
    res = mulii(res, q);
  }
  return gerepileuptoint(av,res);
}

/*******************************************************************/
/*                                                                 */
/*    2-ELT REPRESENTATION FOR PRIME IDEALS (dividing index)       */
/*                                                                 */
/*******************************************************************/
/* to compute norm of elt in basis form */
typedef struct {
  long r1;
  GEN M;  /* via embed_norm */

  GEN D, w, T; /* via resultant if M = NULL */
} norm_S;

static GEN
get_norm(norm_S *S, GEN a)
{
  if (S->M)
  {
    long e;
    GEN N = grndtoi( embed_norm(RgM_RgC_mul(S->M, a), S->r1), &e );
    if (e > -5) pari_err_PREC( "get_norm");
    return N;
  }
  if (S->w) a = RgV_RgC_mul(S->w, a);
  return ZX_resultant_all(S->T, a, S->D, 0);
}
static void
init_norm(norm_S *S, GEN nf, GEN p)
{
  GEN T = nf_get_pol(nf), M = nf_get_M(nf);
  long N = degpol(T), ex = gexpo(M) + gexpo(mului(8 * N, p));

  S->r1 = nf_get_r1(nf);
  if (N * ex <= prec2nbits(gprecision(M)) - 20)
  { /* enough prec to use embed_norm */
    S->M = M;
    S->D = NULL;
    S->w = NULL;
    S->T = NULL;
  }
  else
  {
    GEN w = leafcopy(nf_get_zkprimpart(nf)), D = nf_get_zkden(nf), Dp = sqri(p);
    long i;
    if (!equali1(D))
    {
      GEN w1 = D;
      long v = Z_pval(D, p);
      D = powiu(p, v);
      Dp = mulii(D, Dp);
      gel(w, 1) = remii(w1, Dp);
    }
    for (i=2; i<=N; i++) gel(w,i) = FpX_red(gel(w,i), Dp);
    S->M = NULL;
    S->D = D;
    S->w = w;
    S->T = T;
  }
}
/* f = f(pr/p), q = p^(f+1), a in pr.
 * Return 1 if v_pr(a) = 1, and 0 otherwise */
static int
is_uniformizer(GEN a, GEN q, norm_S *S) { return !dvdii(get_norm(S,a), q); }

/* Return x * y, x, y are t_MAT (Fp-basis of in O_K/p), assume (x,y)=1.
 * Either x or y may be NULL (= O_K), not both */
static GEN
mul_intersect(GEN x, GEN y, GEN p)
{
  if (!x) return y;
  if (!y) return x;
  return FpM_intersect(x, y, p);
}
/* Fp-basis of (ZK/pr): applied to the primes found in primedec_aux()
 * true nf */
static GEN
Fp_basis(GEN nf, GEN pr)
{
  long i, j, l;
  GEN x, y;
  /* already in basis form (from Buchman-Lenstra) ? */
  if (typ(pr) == t_MAT) return pr;
  /* ordinary prid (from Kummer) */
  x = pr_hnf(nf, pr);
  l = lg(x);
  y = cgetg(l, t_MAT);
  for (i=j=1; i<l; i++)
    if (gequal1(gcoeff(x,i,i))) gel(y,j++) = gel(x,i);
  setlg(y, j); return y;
}
/* Let Ip = prod_{ P | p } P be the p-radical. The list L contains the
 * P (mod Ip) seen as sub-Fp-vector spaces of ZK/Ip.
 * Return the list of (Ip / P) (mod Ip).
 * N.B: All ideal multiplications are computed as intersections of Fp-vector
 * spaces. true nf */
static GEN
get_LV(GEN nf, GEN L, GEN p, long N)
{
  long i, l = lg(L)-1;
  GEN LV, LW, A, B;

  LV = cgetg(l+1, t_VEC);
  if (l == 1) { gel(LV,1) = matid(N); return LV; }
  LW = cgetg(l+1, t_VEC);
  for (i=1; i<=l; i++) gel(LW,i) = Fp_basis(nf, gel(L,i));

  /* A[i] = L[1]...L[i-1], i = 2..l */
  A = cgetg(l+1, t_VEC); gel(A,1) = NULL;
  for (i=1; i < l; i++) gel(A,i+1) = mul_intersect(gel(A,i), gel(LW,i), p);
  /* B[i] = L[i+1]...L[l], i = 1..(l-1) */
  B = cgetg(l+1, t_VEC); gel(B,l) = NULL;
  for (i=l; i>=2; i--) gel(B,i-1) = mul_intersect(gel(B,i), gel(LW,i), p);
  for (i=1; i<=l; i++) gel(LV,i) = mul_intersect(gel(A,i), gel(B,i), p);
  return LV;
}

static void
errprime(GEN p) { pari_err_PRIME("idealprimedec",p); }

/* P = Fp-basis (over O_K/p) for pr.
 * V = Z-basis for I_p/pr. ramif != 0 iff some pr|p is ramified.
 * Return a p-uniformizer for pr. Assume pr not inert, i.e. m > 0 */
static GEN
uniformizer(GEN nf, norm_S *S, GEN P, GEN V, GEN p, int ramif)
{
  long i, l, f, m = lg(P)-1, N = nf_get_degree(nf);
  GEN u, Mv, x, q;

  f = N - m; /* we want v_p(Norm(x)) = p^f */
  q = powiu(p,f+1);

  u = FpM_FpC_invimage(shallowconcat(P, V), col_ei(N,1), p);
  setlg(u, lg(P));
  u = centermod(ZM_ZC_mul(P, u), p);
  if (is_uniformizer(u, q, S)) return u;
  if (signe(gel(u,1)) <= 0) /* make sure u[1] in ]-p,p] */
    gel(u,1) = addii(gel(u,1), p); /* try u + p */
  else
    gel(u,1) = subii(gel(u,1), p); /* try u - p */
  if (!ramif || is_uniformizer(u, q, S)) return u;

  /* P/p ramified, u in P^2, not in Q for all other Q|p */
  Mv = zk_multable(nf, Z_ZC_sub(gen_1,u));
  l = lg(P);
  for (i=1; i<l; i++)
  {
    x = centermod(ZC_add(u, ZM_ZC_mul(Mv, gel(P,i))), p);
    if (is_uniformizer(x, q, S)) return x;
  }
  errprime(p);
  return NULL; /* LCOV_EXCL_LINE */
}

/*******************************************************************/
/*                                                                 */
/*                   BUCHMANN-LENSTRA ALGORITHM                    */
/*                                                                 */
/*******************************************************************/
static GEN
mk_pr(GEN p, GEN u, long e, long f, GEN t)
{ return mkvec5(p, u, utoipos(e), utoipos(f), t); }

/* nf a true nf; pr = (p,u) of ramification index e */
GEN
idealprimedec_kummer(GEN nf,GEN u,long e,GEN p)
{
  GEN t, T = nf_get_pol(nf);
  long f = degpol(u), N = degpol(T);

  if (f == N) /* inert */
  {
    u = scalarcol_shallow(p,N);
    t = gen_1;
  }
  else
  { /* make sure v_pr(u) = 1 (automatic if e>1) */
    t = poltobasis(nf, FpX_div(T,u,p));
    t = centermod(t, p);
    u = FpX_center_i(u, p, shifti(p,-1));
    if (e == 1 && ZpX_resultant_val(T, u, p, f+1) > f)
      gel(u,2) = addii(gel(u,2), p);
    u = poltobasis(nf,u);
    t = zk_multable(nf, t); /* t never a scalar here since pr is not inert */
  }
  return mk_pr(p,u,e,f,t);
}

typedef struct {
  GEN nf, p;
  long I;
} eltmod_muldata;

static GEN
sqr_mod(void *data, GEN x)
{
  eltmod_muldata *D = (eltmod_muldata*)data;
  return FpC_red(nfsqri(D->nf, x), D->p);
}
static GEN
ei_msqr_mod(void *data, GEN x)
{
  GEN x2 = sqr_mod(data, x);
  eltmod_muldata *D = (eltmod_muldata*)data;
  return FpC_red(zk_ei_mul(D->nf, x2, D->I), D->p);
}
/* nf a true nf; compute lift(nf.zk[I]^p mod p) */
static GEN
pow_ei_mod_p(GEN nf, long I, GEN p)
{
  pari_sp av = avma;
  eltmod_muldata D;
  long N = nf_get_degree(nf);
  GEN y = col_ei(N,I);
  if (I == 1) return y;
  D.nf = nf;
  D.p = p;
  D.I = I;
  y = gen_pow_fold(y, p, (void*)&D, &sqr_mod, &ei_msqr_mod);
  return gerepileupto(av,y);
}

/* nf a true nf; return a Z basis of Z_K's p-radical, phi = x--> x^p-x */
static GEN
pradical(GEN nf, GEN p, GEN *phi)
{
  long i, N = nf_get_degree(nf);
  GEN q,m,frob,rad;

  /* matrix of Frob: x->x^p over Z_K/p */
  frob = cgetg(N+1,t_MAT);
  for (i=1; i<=N; i++) gel(frob,i) = pow_ei_mod_p(nf,i,p);

  m = frob; q = p;
  while (abscmpiu(q,N) < 0) { q = mulii(q,p); m = FpM_mul(m, frob, p); }
  rad = FpM_ker(m, p); /* m = Frob^k, s.t p^k >= N */
  for (i=1; i<=N; i++) gcoeff(frob,i,i) = subiu(gcoeff(frob,i,i), 1);
  *phi = frob; return rad;
}

/* return powers of a: a^0, ... , a^d,  d = dim A */
static GEN
get_powers(GEN mul, GEN p)
{
  long i, d = lgcols(mul);
  GEN z, pow = cgetg(d+2,t_MAT), P = pow+1;

  gel(P,0) = scalarcol_shallow(gen_1, d-1);
  z = gel(mul,1);
  for (i=1; i<=d; i++)
  {
    gel(P,i) = z; /* a^i */
    if (i!=d) z = FpM_FpC_mul(mul, z, p);
  }
  return pow;
}

/* minimal polynomial of a in A (dim A = d).
 * mul = multiplication table by a in A */
static GEN
pol_min(GEN mul, GEN p)
{
  pari_sp av = avma;
  GEN z = FpM_deplin(get_powers(mul, p), p);
  return gerepilecopy(av, RgV_to_RgX(z,0));
}

static GEN
get_pr(GEN nf, norm_S *S, GEN p, GEN P, GEN V, int ramif, long N, long flim)
{
  GEN u, t;
  long e, f;

  if (typ(P) == t_VEC)
  { /* already done (Kummer) */
    f = pr_get_f(P);
    if (flim > 0 && f > flim) return NULL;
    if (flim == -2) return (GEN)f;
    return P;
  }
  f = N - (lg(P)-1);
  if (flim > 0 && f > flim) return NULL;
  if (flim == -2) return (GEN)f;
  /* P = (p,u) prime. t is an anti-uniformizer: Z_K + t/p Z_K = P^(-1),
   * so that v_P(t) = e(P/p)-1 */
  if (f == N) {
    u = scalarcol_shallow(p,N);
    t = gen_1;
    e = 1;
  } else {
    GEN mt;
    u = uniformizer(nf, S, P, V, p, ramif);
    t = FpM_deplin(zk_multable(nf,u), p);
    mt = zk_multable(nf, t);
    e = ramif? 1 + ZC_nfval(t,mk_pr(p,u,0,0,mt)): 1;
    t = mt;
  }
  return mk_pr(p,u,e,f,t);
}

/* true nf */
static GEN
primedec_end(GEN nf, GEN L, GEN p, long flim)
{
  long i, j, l = lg(L), N = nf_get_degree(nf);
  GEN LV = get_LV(nf, L,p,N);
  int ramif = dvdii(nf_get_disc(nf), p);
  norm_S S; init_norm(&S, nf, p);
  for (i = j = 1; i < l; i++)
  {
    GEN P = get_pr(nf, &S, p, gel(L,i), gel(LV,i), ramif, N, flim);
    if (!P) continue;
    gel(L,j++) = P;
    if (flim == -1) return P;
  }
  setlg(L, j); return L;
}

/* prime ideal decomposition of p; if flim>0, restrict to f(P,p) <= flim
 * if flim = -1 return only the first P
 * if flim = -2 return only the f(P/p) in a t_VECSMALL */
static GEN
primedec_aux(GEN nf, GEN p, long flim)
{
  const long TYP = (flim == -2)? t_VECSMALL: t_VEC;
  GEN E, F, L, Ip, phi, f, g, h, UN, T = nf_get_pol(nf);
  long i, k, c, iL, N;
  int kummer;

  F = FpX_factor(T, p);
  E = gel(F,2);
  F = gel(F,1);

  k = lg(F); if (k == 1) errprime(p);
  if ( !dvdii(nf_get_index(nf),p) ) /* p doesn't divide index */
  {
    L = cgetg(k, TYP);
    for (i=1; i<k; i++)
    {
      GEN t = gel(F,i);
      long f = degpol(t);
      if (flim > 0 && f > flim) { setlg(L, i); break; }
      if (flim == -2)
        L[i] = f;
      else
        gel(L,i) = idealprimedec_kummer(nf, t, E[i],p);
      if (flim == -1) return gel(L,1);
    }
    return L;
  }

  kummer = 0;
  g = FpXV_prod(F, p);
  h = FpX_div(T,g,p);
  f = FpX_red(ZX_Z_divexact(ZX_sub(ZX_mul(g,h), T), p), p);

  N = degpol(T);
  L = cgetg(N+1,TYP);
  iL = 1;
  for (i=1; i<k; i++)
    if (E[i] == 1 || signe(FpX_rem(f,gel(F,i),p)))
    {
      GEN t = gel(F,i);
      kummer = 1;
      gel(L,iL++) = idealprimedec_kummer(nf, t, E[i],p);
      if (flim == -1) return gel(L,1);
    }
    else /* F[i] | (f,g,h), happens at least once by Dedekind criterion */
      E[i] = 0;

  /* phi matrix of x -> x^p - x in algebra Z_K/p */
  Ip = pradical(nf,p,&phi);

  /* split etale algebra Z_K / (p,Ip) */
  h = cgetg(N+1,t_VEC);
  if (kummer)
  { /* split off Kummer factors */
    GEN mb, b = NULL;
    for (i=1; i<k; i++)
      if (!E[i]) b = b? FpX_mul(b, gel(F,i), p): gel(F,i);
    if (!b) errprime(p);
    b = FpC_red(poltobasis(nf,b), p);
    mb = FpM_red(zk_multable(nf,b), p);
    /* Fp-base of ideal (Ip, b) in ZK/p */
    gel(h,1) = FpM_image(shallowconcat(mb,Ip), p);
  }
  else
    gel(h,1) = Ip;

  UN = col_ei(N, 1);
  for (c=1; c; c--)
  { /* Let A:= (Z_K/p) / Ip etale; split A2 := A / Im H ~ Im M2
       H * ? + M2 * Mi2 = Id_N ==> M2 * Mi2 projector A --> A2 */
    GEN M, Mi, M2, Mi2, phi2, mat1, H = gel(h,c); /* maximal rank */
    long dim, r = lg(H)-1;

    M   = FpM_suppl(shallowconcat(H,UN), p);
    Mi  = FpM_inv(M, p);
    M2  = vecslice(M, r+1,N); /* M = (H|M2) invertible */
    Mi2 = rowslice(Mi,r+1,N);
    /* FIXME: FpM_mul(,M2) could be done with vecpermute */
    phi2 = FpM_mul(Mi2, FpM_mul(phi,M2, p), p);
    mat1 = FpM_ker(phi2, p);
    dim = lg(mat1)-1; /* A2 product of 'dim' fields */
    if (dim > 1)
    { /* phi2 v = 0 => a = M2 v in Ker phi, a not in Fp.1 + H */
      GEN R, a, mula, mul2, v = gel(mat1,2);
      long n;

      a = FpM_FpC_mul(M2,v, p); /* not a scalar */
      mula = FpM_red(zk_multable(nf,a), p);
      mul2 = FpM_mul(Mi2, FpM_mul(mula,M2, p), p);
      R = FpX_roots(pol_min(mul2,p), p); /* totally split mod p */
      n = lg(R)-1;
      for (i=1; i<=n; i++)
      {
        GEN I = RgM_Rg_sub_shallow(mula, gel(R,i));
        gel(h,c++) = FpM_image(shallowconcat(H, I), p);
      }
      if (n == dim)
        for (i=1; i<=n; i++) gel(L,iL++) = gel(h,--c);
    }
    else /* A2 field ==> H maximal, f = N-r = dim(A2) */
      gel(L,iL++) = H;
  }
  setlg(L, iL);
  return primedec_end(nf, L, p, flim);
}

GEN
idealprimedec_limit_f(GEN nf, GEN p, long f)
{
  pari_sp av = avma;
  GEN v;
  if (typ(p) != t_INT) pari_err_TYPE("idealprimedec",p);
  if (f < 0) pari_err_DOMAIN("idealprimedec", "f", "<", gen_0, stoi(f));
  v = primedec_aux(checknf(nf), p, f);
  v = gen_sort(v, (void*)&cmp_prime_over_p, &cmp_nodata);
  return gerepileupto(av,v);
}
GEN
idealprimedec_galois(GEN nf, GEN p)
{
  pari_sp av = avma;
  GEN v = primedec_aux(checknf(nf), p, -1);
  return gerepilecopy(av,v);
}
GEN
idealprimedec_degrees(GEN nf, GEN p)
{
  pari_sp av = avma;
  GEN v = primedec_aux(checknf(nf), p, -2);
  vecsmall_sort(v); return gerepileuptoleaf(av, v);
}
GEN
idealprimedec_limit_norm(GEN nf, GEN p, GEN B)
{ return idealprimedec_limit_f(nf, p, logint(B,p)); }
GEN
idealprimedec(GEN nf, GEN p)
{ return idealprimedec_limit_f(nf, p, 0); }
GEN
nf_pV_to_prV(GEN nf, GEN P)
{
  long i, l;
  GEN Q = cgetg_copy(P,&l);
  if (l == 1) return Q;
  for (i = 1; i < l; i++) gel(Q,i) = idealprimedec(nf, gel(P,i));
  return shallowconcat1(Q);
}

/* return [Fp[x]: Fp] */
static long
ffdegree(GEN x, GEN frob, GEN p)
{
  pari_sp av = avma;
  long d, f = lg(frob)-1;
  GEN y = x;

  for (d=1; d < f; d++)
  {
    y = FpM_FpC_mul(frob, y, p);
    if (ZV_equal(y, x)) break;
  }
  avma = av; return d;
}

static GEN
lift_to_zk(GEN v, GEN c, long N)
{
  GEN w = zerocol(N);
  long i, l = lg(c);
  for (i=1; i<l; i++) gel(w,c[i]) = gel(v,i);
  return w;
}

/* return t = 1 mod pr, t = 0 mod p / pr^e(pr/p) */
static GEN
anti_uniformizer(GEN nf, GEN pr)
{
  long N = nf_get_degree(nf), e = pr_get_e(pr);
  GEN p, b, z;

  if (e * pr_get_f(pr) == N) return gen_1;
  p = pr_get_p(pr);
  b = pr_get_tau(pr); /* ZM */
  if (e != 1)
  {
    GEN q = powiu(pr_get_p(pr), e-1);
    b = ZM_Z_divexact(ZM_powu(b,e), q);
  }
  /* b = tau^e / p^(e-1), v_pr(b) = 0, v_Q(b) >= e(Q/p) for other Q | p */
  z = ZM_hnfmodid(FpM_red(b,p), p); /* ideal (p) / pr^e, coprime to pr */
  z = idealaddtoone_raw(nf, pr, z);
  return Z_ZC_sub(gen_1, FpC_center(FpC_red(z,p), p, shifti(p,-1)));
}

#define mpr_TAU 1
#define mpr_FFP 2
#define mpr_NFP 5
#define SMALLMODPR 4
#define LARGEMODPR 6
static GEN
modpr_TAU(GEN modpr)
{
  GEN tau = gel(modpr,mpr_TAU);
  return isintzero(tau)? NULL: tau;
}

/* prh = HNF matrix, which is identity but for the first line. Return a
 * projector to ZK / prh ~ Z/prh[1,1] */
GEN
dim1proj(GEN prh)
{
  long i, N = lg(prh)-1;
  GEN ffproj = cgetg(N+1, t_VEC);
  GEN x, q = gcoeff(prh,1,1);
  gel(ffproj,1) = gen_1;
  for (i=2; i<=N; i++)
  {
    x = gcoeff(prh,1,i);
    if (signe(x)) x = subii(q,x);
    gel(ffproj,i) = x;
  }
  return ffproj;
}

/* p not necessarily prime, but coprime to denom(basis) */
GEN
QXQV_to_FpM(GEN basis, GEN T, GEN p)
{
  long i, l = lg(basis), f = degpol(T);
  GEN z = cgetg(l, t_MAT);
  for (i = 1; i < l; i++)
  {
    GEN w = gel(basis,i);
    if (typ(w) == t_INT)
      w = scalarcol_shallow(w, f);
    else
    {
      GEN dx;
      w = Q_remove_denom(w, &dx);
      w = FpXQ_red(w, T, p);
      if (dx)
      {
        dx = Fp_inv(dx, p);
        if (!equali1(dx)) w = FpX_Fp_mul(w, dx, p);
      }
      w = RgX_to_RgC(w, f);
    }
    gel(z,i) = w; /* w_i mod (T,p) */
  }
  return z;
}

/* initialize reduction mod pr; if zk = 1, will only init data required to
 * reduce *integral* element.  Realize (O_K/pr) as Fp[X] / (T), for a
 * *monic* T */
static GEN
modprinit(GEN nf, GEN pr, int zk)
{
  pari_sp av = avma;
  GEN res, tau, mul, x, p, T, pow, ffproj, nfproj, prh, c;
  long N, i, k, f;

  nf = checknf(nf); checkprid(pr);
  f = pr_get_f(pr);
  N = nf_get_degree(nf);
  prh = pr_hnf(nf, pr);
  tau = zk? gen_0: anti_uniformizer(nf, pr);
  p = pr_get_p(pr);

  if (f == 1)
  {
    res = cgetg(SMALLMODPR, t_COL);
    gel(res,mpr_TAU) = tau;
    gel(res,mpr_FFP) = dim1proj(prh);
    gel(res,3) = pr; return gerepilecopy(av, res);
  }

  c = cgetg(f+1, t_VECSMALL);
  ffproj = cgetg(N+1, t_MAT);
  for (k=i=1; i<=N; i++)
  {
    x = gcoeff(prh, i,i);
    if (!is_pm1(x)) { c[k] = i; gel(ffproj,i) = col_ei(N, i); k++; }
    else
      gel(ffproj,i) = ZC_neg(gel(prh,i));
  }
  ffproj = rowpermute(ffproj, c);
  if (! dvdii(nf_get_index(nf), p))
  {
    GEN basis = nf_get_zkprimpart(nf), D = nf_get_zkden(nf);
    if (N == f)
    { /* pr inert */
      T = nf_get_pol(nf);
      T = FpX_red(T,p);
      ffproj = RgV_to_RgM(basis, lg(basis)-1);
    }
    else
    {
      T = RgV_RgC_mul(basis, pr_get_gen(pr));
      T = FpX_normalize(T,p);
      basis = FqV_red(vecpermute(basis,c), T, p);
      basis = RgV_to_RgM(basis, lg(basis)-1);
      ffproj = ZM_mul(basis, ffproj);
    }
    ffproj = FpM_red(ffproj, p);
    if (!equali1(D))
    {
      D = modii(D,p);
      if (!equali1(D)) ffproj = FpM_Fp_mul(ffproj, Fp_inv(D,p), p);
    }

    res = cgetg(SMALLMODPR+1, t_COL);
    gel(res,mpr_TAU) = tau;
    gel(res,mpr_FFP) = ffproj;
    gel(res,3) = pr;
    gel(res,4) = T; return gerepilecopy(av, res);
  }

  if (uisprime(f))
  {
    mul = ei_multable(nf, c[2]);
    mul = vecpermute(mul, c);
  }
  else
  {
    GEN v, u, u2, frob;
    long deg,deg1,deg2;

    /* matrix of Frob: x->x^p over Z_K/pr = < w[c1], ..., w[cf] > over Fp */
    frob = cgetg(f+1, t_MAT);
    for (i=1; i<=f; i++)
    {
      x = pow_ei_mod_p(nf,c[i],p);
      gel(frob,i) = FpM_FpC_mul(ffproj, x, p);
    }
    u = col_ei(f,2); k = 2;
    deg1 = ffdegree(u, frob, p);
    while (deg1 < f)
    {
      k++; u2 = col_ei(f, k);
      deg2 = ffdegree(u2, frob, p);
      deg = ulcm(deg1,deg2);
      if (deg == deg1) continue;
      if (deg == deg2) { deg1 = deg2; u = u2; continue; }
      u = ZC_add(u, u2);
      while (ffdegree(u, frob, p) < deg) u = ZC_add(u, u2);
      deg1 = deg;
    }
    v = lift_to_zk(u,c,N);

    mul = cgetg(f+1,t_MAT);
    gel(mul,1) = v; /* assume w_1 = 1 */
    for (i=2; i<=f; i++) gel(mul,i) = zk_ei_mul(nf,v,c[i]);
  }

  /* Z_K/pr = Fp(v), mul = mul by v */
  mul = FpM_red(mul, p);
  mul = FpM_mul(ffproj, mul, p);

  pow = get_powers(mul, p);
  T = RgV_to_RgX(FpM_deplin(pow, p), nf_get_varn(nf));
  nfproj = cgetg(f+1, t_MAT);
  for (i=1; i<=f; i++) gel(nfproj,i) = lift_to_zk(gel(pow,i), c, N);

  setlg(pow, f+1);
  ffproj = FpM_mul(FpM_inv(pow, p), ffproj, p);

  res = cgetg(LARGEMODPR, t_COL);
  gel(res,mpr_TAU) = tau;
  gel(res,mpr_FFP) = ffproj;
  gel(res,3) = pr;
  gel(res,4) = T;
  gel(res,mpr_NFP) = nfproj; return gerepilecopy(av, res);
}

GEN
nfmodprinit(GEN nf, GEN pr) { return modprinit(nf, pr, 0); }
GEN
zkmodprinit(GEN nf, GEN pr) { return modprinit(nf, pr, 1); }

/* x may be a modpr */
static int
ok_modpr(GEN x)
{ return typ(x) == t_COL && lg(x) >= SMALLMODPR && lg(x) <= LARGEMODPR; }
void
checkmodpr(GEN x)
{
  if (!ok_modpr(x)) pari_err_TYPE("checkmodpr [use nfmodprinit]", x);
  checkprid(modpr_get_pr(x));
}
GEN
get_modpr(GEN x)
{ return ok_modpr(x)? x: NULL; }

int
checkprid_i(GEN x)
{
  return (typ(x) == t_VEC && lg(x) == 6
          && typ(gel(x,2)) == t_COL && typ(gel(x,3)) == t_INT
          && typ(gel(x,5)) != t_COL); /* tau changed to t_MAT/t_INT in 2.6 */
}
void
checkprid(GEN x)
{ if (!checkprid_i(x)) pari_err_TYPE("checkprid",x); }
GEN
get_prid(GEN x)
{
  long lx = lg(x);
  if (lx == 3 && typ(x) == t_VEC) x = gel(x,1);
  if (checkprid_i(x)) return x;
  if (ok_modpr(x)) {
    x = modpr_get_pr(x);
    if (checkprid_i(x)) return x;
  }
  return NULL;
}

static GEN
to_ff_init(GEN nf, GEN *pr, GEN *T, GEN *p, int zk)
{
  GEN modpr = ok_modpr(*pr)? *pr: modprinit(nf, *pr, zk);
  *T = modpr_get_T(modpr);
  *pr = modpr_get_pr(modpr);
  *p = pr_get_p(*pr); return modpr;
}

/* Return an element of O_K which is set to x Mod T */
GEN
modpr_genFq(GEN modpr)
{
  switch(lg(modpr))
  {
    case SMALLMODPR: /* Fp */
      return gen_1;
    case LARGEMODPR:  /* painful case, p \mid index */
      return gmael(modpr,mpr_NFP, 2);
    default: /* trivial case : p \nmid index */
    {
      long v = varn( modpr_get_T(modpr) );
      return pol_x(v);
    }
  }
}

GEN
nf_to_Fq_init(GEN nf, GEN *pr, GEN *T, GEN *p) {
  GEN modpr = to_ff_init(nf,pr,T,p,0);
  GEN tau = modpr_TAU(modpr);
  if (!tau) gel(modpr,mpr_TAU) = anti_uniformizer(nf, *pr);
  return modpr;
}
GEN
zk_to_Fq_init(GEN nf, GEN *pr, GEN *T, GEN *p) {
  return to_ff_init(nf,pr,T,p,1);
}

/* assume x in 'basis' form (t_COL) */
GEN
zk_to_Fq(GEN x, GEN modpr)
{
  GEN pr = modpr_get_pr(modpr), p = pr_get_p(pr);
  GEN ffproj = gel(modpr,mpr_FFP);
  GEN T = modpr_get_T(modpr);
  return T? FpM_FpC_mul_FpX(ffproj,x, p, varn(T)): FpV_dotproduct(ffproj,x, p);
}

/* REDUCTION Modulo a prime ideal */

/* nf a true nf */
static GEN
Rg_to_ff(GEN nf, GEN x0, GEN modpr)
{
  GEN x = x0, den, pr = modpr_get_pr(modpr), p = pr_get_p(pr);
  long tx = typ(x);

  if (tx == t_POLMOD) { x = gel(x,2); tx = typ(x); }
  switch(tx)
  {
    case t_INT: return modii(x, p);
    case t_FRAC: return Rg_to_Fp(x, p);
    case t_POL:
      switch(lg(x))
      {
        case 2: return gen_0;
        case 3: return Rg_to_Fp(gel(x,2), p);
      }
      x = Q_remove_denom(x, &den);
      x = poltobasis(nf, x);
      /* content(x) and den may not be coprime */
      break;
    case t_COL:
      x = Q_remove_denom(x, &den);
      /* content(x) and den are coprime */
      if (lg(x)-1 == nf_get_degree(nf)) break;
    default: pari_err_TYPE("Rg_to_ff",x);
      return NULL;/*LCOV_EXCL_LINE*/
  }
  if (den)
  {
    long v = Z_pvalrem(den, p, &den);
    if (v)
    {
      if (tx == t_POL) v -= ZV_pvalrem(x, p, &x);
      /* now v = valuation(true denominator of x) */
      if (v > 0)
      {
        GEN tau = modpr_TAU(modpr);
        if (!tau) pari_err_TYPE("zk_to_ff", x0);
        x = nfmuli(nf,x, nfpow_u(nf, tau, v));
        v -= ZV_pvalrem(x, p, &x);
      }
      if (v > 0) pari_err_INV("Rg_to_ff", mkintmod(gen_0,p));
      if (v) return gen_0;
      if (is_pm1(den)) den = NULL;
    }
    x = FpC_red(x, p);
  }
  x = zk_to_Fq(x, modpr);
  if (den)
  {
    GEN c = Fp_inv(den, p);
    x = typ(x) == t_INT? Fp_mul(x,c,p): FpX_Fp_mul(x,c,p);
  }
  return x;
}

GEN
nfreducemodpr(GEN nf, GEN x, GEN modpr)
{
  pari_sp av = avma;
  nf = checknf(nf); checkmodpr(modpr);
  return gerepileupto(av, algtobasis(nf, Fq_to_nf(Rg_to_ff(nf,x,modpr),modpr)));
}

GEN
nfmodpr(GEN nf, GEN x, GEN pr)
{
  pari_sp av = avma;
  GEN T, p, modpr;
  nf = checknf(nf);
  modpr = nf_to_Fq_init(nf, &pr, &T, &p);
  x = Rg_to_ff(nf, x, modpr);
  x = Fq_to_FF(x, Tp_to_FF(T,p));
  return gerepilecopy(av, x);
}
GEN
nfmodprlift(GEN nf, GEN x, GEN pr)
{
  pari_sp av = avma;
  GEN y, T, p, modpr;
  long i, l, d;
  nf = checknf(nf);
  switch(typ(x))
  {
    case t_INT: return icopy(x);
    case t_FFELT: break;
    case t_VEC: case t_COL: case t_MAT:
      y = cgetg_copy(x,&l);
      for (i = 1; i < l; i++) gel(y,i) = nfmodprlift(nf,gel(x,i),pr);
      return y;
    default: pari_err_TYPE("nfmodprlit",x);
  }
  x = FF_to_FpXQ_i(x);
  d = degpol(x);
  if (d <= 0) { avma = av; return d? gen_0: icopy(gel(x,2)); }
  modpr = nf_to_Fq_init(nf, &pr, &T, &p);
  return gerepilecopy(av, Fq_to_nf(x, modpr));
}

/* lift A from residue field to nf */
GEN
Fq_to_nf(GEN A, GEN modpr)
{
  long dA;
  if (typ(A) == t_INT || lg(modpr) < LARGEMODPR) return A;
  dA = degpol(A);
  if (dA <= 0) return dA ? gen_0: gel(A,2);
  return ZM_ZX_mul(gel(modpr,mpr_NFP), A);
}
GEN
FqV_to_nfV(GEN x, GEN modpr)
{ pari_APPLY_same(Fq_to_nf(gel(x,i), modpr)) }
GEN
FqM_to_nfM(GEN A, GEN modpr)
{
  long i,j,h,l = lg(A);
  GEN B = cgetg(l, t_MAT);

  if (l == 1) return B;
  h = lgcols(A);
  for (j=1; j<l; j++)
  {
    GEN Aj = gel(A,j), Bj = cgetg(h,t_COL); gel(B,j) = Bj;
    for (i=1; i<h; i++) gel(Bj,i) = Fq_to_nf(gel(Aj,i), modpr);
  }
  return B;
}
GEN
FqX_to_nfX(GEN A, GEN modpr)
{
  long i, l;
  GEN B;

  if (typ(A)!=t_POL) return icopy(A); /* scalar */
  B = cgetg_copy(A, &l); B[1] = A[1];
  for (i=2; i<l; i++) gel(B,i) = Fq_to_nf(gel(A,i), modpr);
  return B;
}

/* reduce A to residue field */
GEN
nf_to_Fq(GEN nf, GEN A, GEN modpr)
{
  pari_sp av = avma;
  return gerepileupto(av, Rg_to_ff(checknf(nf), A, modpr));
}
/* A t_VEC/t_COL */
GEN
nfV_to_FqV(GEN A, GEN nf,GEN modpr)
{
  long i,l = lg(A);
  GEN B = cgetg(l,typ(A));
  for (i=1; i<l; i++) gel(B,i) = nf_to_Fq(nf,gel(A,i), modpr);
  return B;
}
/* A  t_MAT */
GEN
nfM_to_FqM(GEN A, GEN nf,GEN modpr)
{
  long i,j,h,l = lg(A);
  GEN B = cgetg(l,t_MAT);

  if (l == 1) return B;
  h = lgcols(A);
  for (j=1; j<l; j++)
  {
    GEN Aj = gel(A,j), Bj = cgetg(h,t_COL); gel(B,j) = Bj;
    for (i=1; i<h; i++) gel(Bj,i) = nf_to_Fq(nf, gel(Aj,i), modpr);
  }
  return B;
}
/* A t_POL */
GEN
nfX_to_FqX(GEN A, GEN nf,GEN modpr)
{
  long i,l = lg(A);
  GEN B = cgetg(l,t_POL); B[1] = A[1];
  for (i=2; i<l; i++) gel(B,i) = nf_to_Fq(nf,gel(A,i),modpr);
  return normalizepol_lg(B, l);
}

/*******************************************************************/
/*                                                                 */
/*                       RELATIVE ROUND 2                          */
/*                                                                 */
/*******************************************************************/
/* Shallow functions */
/* FIXME: use a bb_field and export the nfX_* routines */
static GEN
nfX_sub(GEN nf, GEN x, GEN y)
{
  long i, lx = lg(x), ly = lg(y);
  GEN z;
  if (ly <= lx) {
    z = cgetg(lx,t_POL); z[1] = x[1];
    for (i=2; i < ly; i++) gel(z,i) = nfsub(nf,gel(x,i),gel(y,i));
    for (   ; i < lx; i++) gel(z,i) = gel(x,i);
    z = normalizepol_lg(z, lx);
  } else {
    z = cgetg(ly,t_POL); z[1] = y[1];
    for (i=2; i < lx; i++) gel(z,i) = nfsub(nf,gel(x,i),gel(y,i));
    for (   ; i < ly; i++) gel(z,i) = gneg(gel(y,i));
    z = normalizepol_lg(z, ly);
  }
  return z;
}
/* FIXME: quadratic multiplication */
static GEN
nfX_mul(GEN nf, GEN a, GEN b)
{
  long da = degpol(a), db = degpol(b), dc, lc, k;
  GEN c;
  if (da < 0 || db < 0) return gen_0;
  dc = da + db;
  if (dc == 0) return nfmul(nf, gel(a,2),gel(b,2));
  lc = dc+3;
  c = cgetg(lc, t_POL); c[1] = a[1];
  for (k = 0; k <= dc; k++)
  {
    long i, I = minss(k, da);
    GEN d = NULL;
    for (i = maxss(k-db, 0); i <= I; i++)
    {
      GEN e = nfmul(nf, gel(a, i+2), gel(b, k-i+2));
      d = d? nfadd(nf, d, e): e;
    }
    gel(c, k+2) = d;
  }
  return normalizepol_lg(c, lc);
}
/* assume b monic */
static GEN
nfX_rem(GEN nf, GEN a, GEN b)
{
  long da = degpol(a), db = degpol(b);
  if (da < 0) return gen_0;
  a = leafcopy(a);
  while (da >= db)
  {
    long i, k = da;
    GEN A = gel(a, k+2);
    for (i = db-1, k--; i >= 0; i--, k--)
      gel(a,k+2) = nfsub(nf, gel(a,k+2), nfmul(nf, A, gel(b,i+2)));
    a = normalizepol_lg(a, lg(a)-1);
    da = degpol(a);
  }
  return a;
}
static GEN
nfXQ_mul(GEN nf, GEN a, GEN b, GEN T)
{
  GEN c = nfX_mul(nf, a, b);
  if (typ(c) != t_POL) return c;
  return nfX_rem(nf, c, T);
}

static void
fill(long l, GEN H, GEN Hx, GEN I, GEN Ix)
{
  long i;
  if (typ(Ix) == t_VEC) /* standard */
    for (i=1; i<l; i++) { gel(H,i) = gel(Hx,i); gel(I,i) = gel(Ix,i); }
  else /* constant ideal */
    for (i=1; i<l; i++) { gel(H,i) = gel(Hx,i); gel(I,i) = Ix; }
}

/* given MODULES x and y by their pseudo-bases, returns a pseudo-basis of the
 * module generated by x and y. */
static GEN
rnfjoinmodules_i(GEN nf, GEN Hx, GEN Ix, GEN Hy, GEN Iy)
{
  long lx = lg(Hx), ly = lg(Hy), l = lx+ly-1;
  GEN H = cgetg(l, t_MAT), I = cgetg(l, t_VEC);
  fill(lx, H     , Hx, I     , Ix);
  fill(ly, H+lx-1, Hy, I+lx-1, Iy); return nfhnf(nf, mkvec2(H, I));
}
static GEN
rnfjoinmodules(GEN nf, GEN x, GEN y)
{
  if (!x) return y;
  if (!y) return x;
  return rnfjoinmodules_i(nf, gel(x,1), gel(x,2), gel(y,1), gel(y,2));
}

typedef struct {
  GEN multab, T,p;
  long h;
} rnfeltmod_muldata;

static GEN
_sqr(void *data, GEN x)
{
  rnfeltmod_muldata *D = (rnfeltmod_muldata *) data;
  GEN z = x? tablesqr(D->multab,x)
           : tablemul_ei_ej(D->multab,D->h,D->h);
  return FqV_red(z,D->T,D->p);
}
static GEN
_msqr(void *data, GEN x)
{
  GEN x2 = _sqr(data, x), z;
  rnfeltmod_muldata *D = (rnfeltmod_muldata *) data;
  z = tablemul_ei(D->multab, x2, D->h);
  return FqV_red(z,D->T,D->p);
}

/* Compute W[h]^n mod (T,p) in the extension, assume n >= 0. T a ZX */
static GEN
rnfeltid_powmod(GEN multab, long h, GEN n, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN y;
  rnfeltmod_muldata D;

  if (!signe(n)) return gen_1;

  D.multab = multab;
  D.h = h;
  D.T = T;
  D.p = p;
  y = gen_pow_fold(NULL, n, (void*)&D, &_sqr, &_msqr);
  return gerepilecopy(av, y);
}

/* P != 0 has at most degpol(P) roots. Look for an element in Fq which is not
 * a root, cf repres() */
static GEN
FqX_non_root(GEN P, GEN T, GEN p)
{
  long dP = degpol(P), f, vT;
  long i, j, k, pi, pp;
  GEN v;

  if (dP == 0) return gen_1;
  pp = is_bigint(p) ? dP+1: itos(p);
  v = cgetg(dP + 2, t_VEC);
  gel(v,1) = gen_0;
  if (T)
  { f = degpol(T); vT = varn(T); }
  else
  { f = 1; vT = 0; }
  for (i=pi=1; i<=f; i++,pi*=pp)
  {
    GEN gi = i == 1? gen_1: pol_xn(i-1, vT), jgi = gi;
    for (j=1; j<pp; j++)
    {
      for (k=1; k<=pi; k++)
      {
        GEN z = Fq_add(gel(v,k), jgi, T,p);
        if (!gequal0(FqX_eval(P, z, T,p))) return z;
        gel(v, j*pi+k) = z;
      }
      if (j < pp-1) jgi = Fq_add(jgi, gi, T,p); /* j*g[i] */
    }
  }
  return NULL;
}

/* Relative Dedekind criterion over (true) nf, applied to the order defined by a
 * root of monic irreducible polynomial P, modulo the prime ideal pr. Assume
 * vdisc = v_pr( disc(P) ).
 * Return NULL if nf[X]/P is pr-maximal. Otherwise, return [flag, O, v]:
 *   O = enlarged order, given by a pseudo-basis
 *   flag = 1 if O is proven pr-maximal (may be 0 and O nevertheless pr-maximal)
 *   v = v_pr(disc(O)). */
static GEN
rnfdedekind_i(GEN nf, GEN P, GEN pr, long vdisc, long only_maximal)
{
  GEN Ppr, A, I, p, tau, g, h, k, base, T, gzk, hzk, prinvp, pal, nfT, modpr;
  long m, vt, r, d, i, j, mpr;

  if (vdisc < 0) pari_err_TYPE("rnfdedekind [non integral pol]", P);
  if (vdisc == 1) return NULL; /* pr-maximal */
  if (!only_maximal && !gequal1(leading_coeff(P)))
    pari_err_IMPL( "the full Dedekind criterion in the non-monic case");
  /* either monic OR only_maximal = 1 */
  m = degpol(P);
  nfT = nf_get_pol(nf);
  modpr = nf_to_Fq_init(nf,&pr, &T, &p);
  Ppr = nfX_to_FqX(P, nf, modpr);
  mpr = degpol(Ppr);
  if (mpr < m) /* non-monic => only_maximal = 1 */
  {
    if (mpr < 0) return NULL;
    if (! RgX_valrem(Ppr, &Ppr))
    { /* non-zero constant coefficient */
      Ppr = RgX_shift_shallow(RgX_recip_shallow(Ppr), m - mpr);
      P = RgX_recip_shallow(P);
    }
    else
    {
      GEN z = FqX_non_root(Ppr, T, p);
      if (!z) pari_err_IMPL( "Dedekind in the difficult case");
      z = Fq_to_nf(z, modpr);
      if (typ(z) == t_INT)
        P = RgX_translate(P, z);
      else
        P = RgXQX_translate(P, z, T);
      P = RgX_recip_shallow(P);
      Ppr = nfX_to_FqX(P, nf, modpr); /* degpol(P) = degpol(Ppr) = m */
    }
  }
  A = gel(FqX_factor(Ppr,T,p),1);
  r = lg(A); /* > 1 */
  g = gel(A,1);
  for (i=2; i<r; i++) g = FqX_mul(g, gel(A,i), T, p);
  h = FqX_div(Ppr,g, T, p);
  gzk = FqX_to_nfX(g, modpr);
  hzk = FqX_to_nfX(h, modpr);
  k = nfX_sub(nf, P, nfX_mul(nf, gzk,hzk));
  tau = pr_get_tau(pr);
  switch(typ(tau))
  {
    case t_INT: k = gdiv(k, p); break;
    case t_MAT: k = RgX_Rg_div(tablemulvec(NULL,tau, k), p); break;
  }
  k = nfX_to_FqX(k, nf, modpr);
  k = FqX_normalize(FqX_gcd(FqX_gcd(g,h,  T,p), k, T,p), T,p);
  d = degpol(k);  /* <= m */
  if (!d) return NULL; /* pr-maximal */
  if (only_maximal) return gen_0; /* not maximal */

  A = cgetg(m+d+1,t_MAT);
  I = cgetg(m+d+1,t_VEC); base = mkvec2(A, I);
 /* base[2] temporarily multiplied by p, for the final nfhnfmod,
  * which requires integral ideals */
  prinvp = pr_inv_p(pr); /* again multiplied by p */
  for (j=1; j<=m; j++)
  {
    gel(A,j) = col_ei(m, j);
    gel(I,j) = p;
  }
  pal = FqX_to_nfX(FqX_div(Ppr,k, T,p), modpr);
  for (   ; j<=m+d; j++)
  {
    gel(A,j) = RgX_to_RgC(pal,m);
    gel(I,j) = prinvp;
    if (j < m+d) pal = RgXQX_rem(RgX_shift_shallow(pal,1),P,nfT);
  }
  /* the modulus is integral */
  base = nfhnfmod(nf,base, idealmulpowprime(nf, powiu(p,m), pr, utoineg(d)));
  gel(base,2) = gdiv(gel(base,2), p); /* cancel the factor p */
  vt = vdisc - 2*d;
  return mkvec3(vt < 2? gen_1: gen_0, base, stoi(vt));
}

/* [L:K] = n */
static GEN
triv_order(long n)
{
  GEN z = cgetg(3, t_VEC);
  gel(z,1) = matid(n);
  gel(z,2) = const_vec(n, gen_1); return z;
}

/* if flag is set, return gen_1 (resp. gen_0) if the order K[X]/(P)
 * is pr-maximal (resp. not pr-maximal). */
GEN
rnfdedekind(GEN nf, GEN P, GEN pr, long flag)
{
  pari_sp av = avma;
  GEN z, dP;
  long v;

  nf = checknf(nf);
  P = RgX_nffix("rnfdedekind", nf_get_pol(nf), P, 0);
  dP = RgX_disc(P); P = lift_shallow(P);
  if (!pr)
  {
    GEN fa = idealfactor(nf, dP);
    GEN Q = gel(fa,1), E = gel(fa,2);
    pari_sp av2 = avma;
    long i, l = lg(Q);
    for (i = 1; i < l; i++, avma = av2)
    {
      v = itos(gel(E,i));
      if (rnfdedekind_i(nf,P,gel(Q,i),v,1)) { avma=av; return gen_0; }
      avma = av2;
    }
    avma = av; return gen_1;
  }
  else if (typ(pr) == t_VEC)
  { /* flag = 1 is implicit */
    if (lg(pr) == 1) { avma = av; return gen_1; }
    if (typ(gel(pr,1)) == t_VEC)
    { /* list of primes */
      GEN Q = pr;
      pari_sp av2 = avma;
      long i, l = lg(Q);
      for (i = 1; i < l; i++, avma = av2)
      {
        v = nfval(nf, dP, gel(Q,i));
        if (rnfdedekind_i(nf,P,gel(Q,i),v,1)) { avma=av; return gen_0; }
      }
      avma = av; return gen_1;
    }
  }
  /* single prime */
  v = nfval(nf, dP, pr);
  z = rnfdedekind_i(nf, P, pr, v, flag);
  if (z)
  {
    if (flag) { avma = av; return gen_0; }
    z = gerepilecopy(av, z);
  }
  else
  {
    avma = av; if (flag) return gen_1;
    z = cgetg(4, t_VEC);
    gel(z,1) = gen_1;
    gel(z,2) = triv_order(degpol(P));
    gel(z,3) = stoi(v);
  }
  return z;
}

static int
ideal_is1(GEN x) {
  switch(typ(x))
  {
    case t_INT: return is_pm1(x);
    case t_MAT: return RgM_isidentity(x);
  }
  return 0;
}

/* return a in ideal A such that v_pr(a) = v_pr(A) */
static GEN
minval(GEN nf, GEN A, GEN pr)
{
  GEN ab = idealtwoelt(nf,A), a = gel(ab,1), b = gel(ab,2);
  if (nfval(nf,a,pr) > nfval(nf,b,pr)) a = b;
  return a;
}

/* nf a true nf. Return NULL if power order if pr-maximal */
static GEN
rnfmaxord(GEN nf, GEN pol, GEN pr, long vdisc)
{
  pari_sp av = avma, av1;
  long i, j, k, n, nn, vpol, cnt, sep;
  GEN q, q1, p, T, modpr, W, I, p1;
  GEN prhinv, mpi, Id;

  if (DEBUGLEVEL>1) err_printf(" treating %Ps^%ld\n", pr, vdisc);
  modpr = nf_to_Fq_init(nf,&pr,&T,&p);
  av1 = avma;
  p1 = rnfdedekind_i(nf, pol, modpr, vdisc, 0);
  if (!p1) { avma = av; return NULL; }
  if (is_pm1(gel(p1,1))) return gerepilecopy(av,gel(p1,2));
  sep = itos(gel(p1,3));
  W = gmael(p1,2,1);
  I = gmael(p1,2,2);
  gerepileall(av1, 2, &W, &I);

  mpi = zk_multable(nf, pr_get_gen(pr));
  n = degpol(pol); nn = n*n;
  vpol = varn(pol);
  q1 = q = pr_norm(pr);
  while (abscmpiu(q1,n) < 0) q1 = mulii(q1,q);
  Id = matid(n);
  prhinv = pr_inv(pr);
  av1 = avma;
  for(cnt=1;; cnt++)
  {
    GEN I0 = leafcopy(I), W0 = leafcopy(W);
    GEN Wa, Winv, Ip, A, MW, MWmod, F, pseudo, C, G;
    GEN Tauinv = cgetg(n+1, t_VEC), Tau = cgetg(n+1, t_VEC);

    if (DEBUGLEVEL>1) err_printf("    pass no %ld\n",cnt);
    for (j=1; j<=n; j++)
    {
      GEN tau, tauinv;
      if (ideal_is1(gel(I,j)))
      {
        gel(I,j) = gel(Tau,j) = gel(Tauinv,j) = gen_1;
        continue;
      }
      gel(Tau,j) = tau = minval(nf, gel(I,j), pr);
      gel(Tauinv,j) = tauinv = nfinv(nf, tau);
      gel(W,j) = nfC_nf_mul(nf, gel(W,j), tau);
      gel(I,j) = idealmul(nf, tauinv, gel(I,j)); /* v_pr(I[j]) = 0 */
    }
    /* W = (Z_K/pr)-basis of O/pr. O = (W0,I0) ~ (W, I) */

   /* compute MW: W_i*W_j = sum MW_k,(i,j) W_k */
    Wa = RgM_to_RgXV(W,vpol);
    Winv = nfM_inv(nf, W);
    MW = cgetg(nn+1, t_MAT);
    /* W_1 = 1 */
    for (j=1; j<=n; j++) gel(MW, j) = gel(MW, (j-1)*n+1) = gel(Id,j);
    for (i=2; i<=n; i++)
      for (j=i; j<=n; j++)
      {
        GEN z = nfXQ_mul(nf, gel(Wa,i), gel(Wa,j), pol);
        if (typ(z) != t_POL)
          z = nfC_nf_mul(nf, gel(Winv,1), z);
        else
        {
          z = RgX_to_RgC(z, lg(Winv)-1);
          z = nfM_nfC_mul(nf, Winv, z);
        }
        gel(MW, (i-1)*n+j) = gel(MW, (j-1)*n+i) = z;
      }

    /* compute Ip =  pr-radical [ could use Ker(trace) if q large ] */
    MWmod = nfM_to_FqM(MW,nf,modpr);
    F = cgetg(n+1, t_MAT); gel(F,1) = gel(Id,1);
    for (j=2; j<=n; j++) gel(F,j) = rnfeltid_powmod(MWmod, j, q1, T,p);
    Ip = FqM_ker(F,T,p);
    if (lg(Ip) == 1) { W = W0; I = I0; break; }

    /* Fill C: W_k A_j = sum_i C_(i,j),k A_i */
    A = FqM_to_nfM(FqM_suppl(Ip,T,p), modpr);
    for (j = lg(Ip); j<=n; j++) gel(A,j) = nfC_multable_mul(gel(A,j), mpi);
    MW = nfM_mul(nf, nfM_inv(nf,A), MW);
    C = cgetg(n+1, t_MAT);
    for (k=1; k<=n; k++)
    {
      GEN mek = vecslice(MW, (k-1)*n+1, k*n), Ck;
      gel(C,k) = Ck = cgetg(nn+1, t_COL);
      for (j=1; j<=n; j++)
      {
        GEN z = nfM_nfC_mul(nf, mek, gel(A,j));
        for (i=1; i<=n; i++) gel(Ck, (j-1)*n+i) = nf_to_Fq(nf,gel(z,i),modpr);
      }
    }
    G = FqM_to_nfM(FqM_ker(C,T,p), modpr);

    pseudo = rnfjoinmodules_i(nf, G,prhinv, Id,I);
    /* express W in terms of the power basis */
    W = nfM_mul(nf, W, gel(pseudo,1));
    I = gel(pseudo,2);
    /* restore the HNF property W[i,i] = 1. NB: W upper triangular, with
     * W[i,i] = Tau[i] */
    for (j=1; j<=n; j++)
      if (gel(Tau,j) != gen_1)
      {
        gel(W,j) = nfC_nf_mul(nf, gel(W,j), gel(Tauinv,j));
        gel(I,j) = idealmul(nf, gel(Tau,j), gel(I,j));
      }
    if (DEBUGLEVEL>3) err_printf(" new order:\n%Ps\n%Ps\n", W, I);
    if (sep <= 3 || gequal(I,I0)) break;

    if (gc_needed(av1,2))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"rnfmaxord");
      gerepileall(av1,2, &W,&I);
    }
  }
  return gerepilecopy(av, mkvec2(W, I));
}

GEN
Rg_nffix(const char *f, GEN T, GEN c, int lift)
{
  switch(typ(c))
  {
    case t_INT: case t_FRAC: return c;
    case t_POL:
      if (lg(c) >= lg(T)) c = RgX_rem(c,T);
      break;
    case t_POLMOD:
      if (!RgX_equal_var(gel(c,1), T)) pari_err_MODULUS(f, gel(c,1),T);
      c = gel(c,2);
      switch(typ(c))
      {
        case t_POL: break;
        case t_INT: case t_FRAC: return c;
        default: pari_err_TYPE(f, c);
      }
      break;
    default: pari_err_TYPE(f,c);
  }
  /* typ(c) = t_POL */
  if (varn(c) != varn(T)) pari_err_VAR(f, c,T);
  switch(lg(c))
  {
    case 2: return gen_0;
    case 3:
      c = gel(c,2); if (is_rational_t(typ(c))) return c;
      pari_err_TYPE(f,c);
  }
  RgX_check_QX(c, f);
  return lift? c: mkpolmod(c, T);
}
/* check whether P is a polynomials with coeffs in number field Q[y]/(T) */
GEN
RgX_nffix(const char *f, GEN T, GEN P, int lift)
{
  long i, l, vT = varn(T);
  GEN Q = cgetg_copy(P, &l);
  if (typ(P) != t_POL) pari_err_TYPE(stack_strcat(f," [t_POL expected]"), P);
  if (varncmp(varn(P), vT) >= 0) pari_err_PRIORITY(f, P, ">=", vT);
  Q[1] = P[1];
  for (i=2; i<l; i++) gel(Q,i) = Rg_nffix(f, T, gel(P,i), lift);
  return normalizepol_lg(Q, l);
}
GEN
RgV_nffix(const char *f, GEN T, GEN P, int lift)
{
  long i, l;
  GEN Q = cgetg_copy(P, &l);
  for (i=1; i<l; i++) gel(Q,i) = Rg_nffix(f, T, gel(P,i), lift);
  return Q;
}

static GEN
get_d(GEN nf, GEN d)
{
  GEN b = idealredmodpower(nf, d, 2, 100000);
  return nfmul(nf, d, nfsqr(nf,b));
}

static GEN
pr_factorback(GEN nf, GEN fa)
{
  GEN P = gel(fa,1), E = gel(fa,2), z = gen_1;
  long i, l = lg(P);
  for (i = 1; i < l; i++) z = idealmulpowprime(nf, z, gel(P,i), gel(E,i));
  return z;
}
static GEN
pr_factorback_scal(GEN nf, GEN fa)
{
  GEN D = pr_factorback(nf,fa);
  if (typ(D) == t_MAT && RgM_isscalar(D,NULL)) D = gcoeff(D,1,1);
  return D;
}

/* nf = base field K
 * pol= monic polynomial in Z_K[X] defining a relative extension L = K[X]/(pol).
 * Returns a pseudo-basis [A,I] of Z_L, set *pD to [D,d] and *pf to the
 * index-ideal; rnf is used when lim != 0 and may be NULL */
GEN
rnfallbase(GEN nf, GEN pol, ulong lim, GEN rnf, GEN *pD, GEN *pf)
{
  long i, j, jf, l;
  GEN fa, E, P, Ef, Pf, z, disc;

  nf = checknf(nf);
  disc = nf_to_scalar_or_basis(nf, RgX_disc(pol));
  if (lim)
  {
    GEN rnfeq, zknf, dzknf, U, vU, dA, A, MB, dB, BdB, vj, B, Tabs;
    GEN D = idealhnf(nf, disc);
    long rU, m = nf_get_degree(nf), n = degpol(pol), N = n*m;

    P = ZV_union_shallow(nf_get_ramified_primes(nf),
                         gel(Z_factor_limit(gcoeff(D,1,1), lim), 1));
    if (rnf)
    {
      rnfeq = rnf_get_map(rnf);
      zknf = rnf_get_nfzk(rnf);
    }
    else
    {
      rnfeq = nf_rnfeq(nf, pol);
      zknf = nf_nfzk(nf, rnfeq);
    }
    dzknf = gel(zknf,1);
    if (gequal1(dzknf)) dzknf = NULL;
    Tabs = gel(rnfeq,1);
    B = nfbasis(Tabs, NULL, P);
    BdB = Q_remove_denom(B, &dB);
    MB = RgXV_to_RgM(BdB, N); /* HNF */

    vU = cgetg(N+1, t_VEC);
    vj = cgetg(N+1, t_VECSMALL);
    gel(vU,1) = U = cgetg(m+1, t_MAT);
    gel(U,1) = col_ei(N, 1);
    A = dB? (dzknf? gdiv(dB,dzknf): dB): NULL;
    if (A && gequal1(A)) A = NULL;
    for (j = 2; j <= m; j++)
    {
      GEN t = gel(zknf,j);
      if (A) t = ZX_Z_mul(t, A);
      gel(U,j) = hnf_solve(MB, RgX_to_RgC(t, N));
    }
    for (i = 2; i <= N; i++)
    {
      GEN b = gel(BdB,i);
      gel(vU,i) = U = cgetg(m+1, t_MAT);
      gel(U,1) = hnf_solve(MB, RgX_to_RgC(b, N));
      for (j = 2; j <= m; j++)
      {
        GEN t = ZX_rem(ZX_mul(b, gel(zknf,j)), Tabs);
        if (dzknf) t = gdiv(t, dzknf);
        gel(U,j) = hnf_solve(MB, RgX_to_RgC(t, N));
      }
    }
    vj[1] = 1; U = gel(vU,1); rU = m;
    for (i = j = 2; i <= N; i++)
    {
      GEN V = shallowconcat(U, gel(vU,i));
      if (ZM_rank(V) != rU)
      {
        U = V; rU += m; vj[j++] = i;
        if (rU == N) break;
      }
    }
    if (dB) for(;;)
    {
      GEN c = gen_1, H = ZM_hnfmodid(U, dB);
      long ic = 0;
      for (i = 1; i <= N; i++)
        if (cmpii(gcoeff(H,i,i), c) > 0) { c = gcoeff(H,i,i); ic = i; }
      if (!ic) break;
      vj[j++] = ic;
      U = shallowconcat(H, gel(vU, ic));
    }
    setlg(vj, j);
    B = vecpermute(B, vj);

    l = lg(B);
    A = cgetg(l,t_MAT);
    for (j = 1; j < l; j++)
    {
      GEN t = eltabstorel_lift(rnfeq, gel(B,j));
      gel(A,j) = Rg_to_RgC(t, n);
    }
    A = RgM_to_nfM(nf, A);
    A = Q_remove_denom(A, &dA);
    if (!dA)
    { /* order is maximal */
      z = triv_order(n);
      if (pf) *pf = gen_1;
    }
    else
    {
      GEN fi;
      /* the first n columns of A are probably in HNF already */
      A = shallowconcat(vecslice(A,n+1,lg(A)-1), vecslice(A,1,n));
      A = mkvec2(A, const_vec(l-1,gen_1));
      if (DEBUGLEVEL > 2) err_printf("rnfallbase: nfhnf in dim %ld\n", l-1);
      z = nfhnfmod(nf, A, nfdetint(nf,A));
      gel(z,2) = gdiv(gel(z,2), dA);
      fi = idealprod(nf,gel(z,2));
      D = idealmul(nf, D, idealsqr(nf, fi));
      if (pf) *pf = idealinv(nf, fi);
    }
    if (RgM_isscalar(D,NULL)) D = gcoeff(D,1,1);
    *pD = mkvec2(D, get_d(nf, disc)); return z;
  }
  pol = lift_shallow(pol);
  fa = idealfactor_limit(nf, disc, lim);
  P = gel(fa,1); l = lg(P); z = NULL;
  E = gel(fa,2);
  Pf = cgetg(l, t_COL);
  Ef = cgetg(l, t_COL);
  for (i = j = jf = 1; i < l; i++)
  {
    GEN pr = gel(P,i);
    long e = itos(gel(E,i));
    if (e > 1)
    {
      GEN vD = rnfmaxord(nf, pol, pr, e);
      if (vD)
      {
        long ef = idealprodval(nf, gel(vD,2), pr);
        z = rnfjoinmodules(nf, z, vD);
        if (ef) { gel(Pf, jf) = pr; gel(Ef, jf++) = stoi(-ef); }
        e += 2 * ef;
      }
    }
    if (e) { gel(P, j) = pr; gel(E, j++) = stoi(e); }
  }
  setlg(P,j);
  setlg(E,j);
  if (pf)
  {
    setlg(Pf, jf);
    setlg(Ef, jf); *pf = pr_factorback_scal(nf, mkmat2(Pf,Ef));
  }
  *pD = mkvec2(pr_factorback_scal(nf,fa), get_d(nf, disc));
  return z? z: triv_order(degpol(pol));
}

GEN
rnfpseudobasis(GEN nf, GEN pol)
{
  pari_sp av = avma;
  GEN D, z;
  ulong lim;
  nf = checknf(nf);
  pol = check_polrel(nf, pol, &lim);
  z = rnfallbase(nf, pol, lim, NULL, &D, NULL);
  return gerepilecopy(av, shallowconcat(z,D));
}

GEN
rnfdisc_factored(GEN nf, GEN pol, GEN *pd)
{
  long i, j, l;
  ulong lim;
  GEN fa, E, P, disc;

  nf = checknf(nf);
  pol = check_polrel(nf, pol, &lim);
  disc = nf_to_scalar_or_basis(nf, RgX_disc(pol));
  pol = lift_shallow(pol);
  fa = idealfactor_limit(nf, disc, lim);
  P = gel(fa,1); l = lg(P);
  E = gel(fa,2);
  for (i = j = 1; i < l; i++)
  {
    long e = itos(gel(E,i));
    GEN pr = gel(P,i);
    if (e > 1)
    {
      GEN vD = rnfmaxord(nf, pol, pr, e);
      if (vD) e += 2*idealprodval(nf, gel(vD,2), pr);
    }
    if (e) { gel(P, j) = pr; gel(E, j++) = stoi(e); }
  }
  if (pd) *pd = get_d(nf, disc);
  setlg(P, j);
  setlg(E, j); return fa;
}
GEN
rnfdiscf(GEN nf, GEN pol)
{
  pari_sp av = avma;
  GEN d, fa = rnfdisc_factored(nf, pol, &d);
  return gerepilecopy(av, mkvec2(pr_factorback_scal(nf,fa), d));
}

GEN
gen_if_principal(GEN bnf, GEN x)
{
  pari_sp av = avma;
  GEN z = bnfisprincipal0(bnf,x, nf_GEN_IF_PRINCIPAL | nf_FORCE);
  if (isintzero(z)) { avma = av; return NULL; }
  return z;
}

static int
is_pseudo_matrix(GEN O)
{
  return (typ(O) ==t_VEC && lg(O) >= 3
          && typ(gel(O,1)) == t_MAT
          && typ(gel(O,2)) == t_VEC
          && lgcols(O) == lg(gel(O,2)));
}

/* given bnf and a pseudo-basis of an order in HNF [A,I], tries to simplify
 * the HNF as much as possible. The resulting matrix will be upper triangular
 * but the diagonal coefficients will not be equal to 1. The ideals are
 * guaranteed to be integral and primitive. */
GEN
rnfsimplifybasis(GEN bnf, GEN x)
{
  pari_sp av = avma;
  long i, l;
  GEN y, Az, Iz, nf, A, I;

  bnf = checkbnf(bnf); nf = bnf_get_nf(bnf);
  if (!is_pseudo_matrix(x)) pari_err_TYPE("rnfsimplifybasis",x);
  A = gel(x,1);
  I = gel(x,2); l = lg(I);
  y = cgetg(3, t_VEC);
  Az = cgetg(l, t_MAT); gel(y,1) = Az;
  Iz = cgetg(l, t_VEC); gel(y,2) = Iz;
  for (i = 1; i < l; i++)
  {
    GEN c, d;
    if (ideal_is1(gel(I,i))) {
      gel(Iz,i) = gen_1;
      gel(Az,i) = gel(A,i);
      continue;
    }

    gel(Iz,i) = Q_primitive_part(gel(I,i), &c);
    gel(Az,i) = c? RgC_Rg_mul(gel(A,i),c): gel(A,i);
    if (c && ideal_is1(gel(Iz,i))) continue;

    d = gen_if_principal(bnf, gel(Iz,i));
    if (d)
    {
      gel(Iz,i) = gen_1;
      gel(Az,i) = nfC_nf_mul(nf, gel(Az,i), d);
    }
  }
  return gerepilecopy(av, y);
}

static GEN
get_order(GEN nf, GEN O, const char *s)
{
  if (typ(O) == t_POL)
    return rnfpseudobasis(nf, O);
  if (!is_pseudo_matrix(O)) pari_err_TYPE(s, O);
  return O;
}

GEN
rnfdet(GEN nf, GEN order)
{
  pari_sp av = avma;
  GEN A, I, D;
  nf = checknf(nf);
  order = get_order(nf, order, "rnfdet");
  A = gel(order,1);
  I = gel(order,2);
  D = idealmul(nf, nfM_det(nf,A), idealprod(nf,I));
  return gerepileupto(av, D);
}

/* Given two fractional ideals a and b, gives x in a, y in b, z in b^-1,
   t in a^-1 such that xt-yz=1. In the present version, z is in Z. */
static void
nfidealdet1(GEN nf, GEN a, GEN b, GEN *px, GEN *py, GEN *pz, GEN *pt)
{
  GEN x, uv, y, da, db;

  a = idealinv(nf,a);
  a = Q_remove_denom(a, &da);
  b = Q_remove_denom(b, &db);
  x = idealcoprime(nf,a,b);
  uv = idealaddtoone(nf, idealmul(nf,x,a), b);
  y = gel(uv,2);
  if (da) x = gmul(x,da);
  if (db) y = gdiv(y,db);
  *px = x;
  *py = y;
  *pz = db ? negi(db): gen_m1;
  *pt = nfdiv(nf, gel(uv,1), x);
}

/* given a pseudo-basis of an order in HNF [A,I] (or [A,I,D,d]), gives an
 * n x n matrix (not in HNF) of a pseudo-basis and an ideal vector
 * [1,1,...,1,I] such that order = Z_K^(n-1) x I.
 * Uses the approximation theorem ==> slow. */
GEN
rnfsteinitz(GEN nf, GEN order)
{
  pari_sp av = avma;
  long i, n, l;
  GEN A, I, p1;

  nf = checknf(nf);
  order = get_order(nf, order, "rnfsteinitz");
  A = RgM_to_nfM(nf, gel(order,1));
  I = leafcopy(gel(order,2)); n=lg(A)-1;
  for (i=1; i<n; i++)
  {
    GEN c1, c2, b, a = gel(I,i);
    gel(I,i) = gen_1;
    if (ideal_is1(a)) continue;

    c1 = gel(A,i);
    c2 = gel(A,i+1);
    b = gel(I,i+1);
    if (ideal_is1(b))
    {
      gel(A,i) = c2;
      gel(A,i+1) = gneg(c1);
      gel(I,i+1) = a;
    }
    else
    {
      pari_sp av2 = avma;
      GEN x, y, z, t;
      nfidealdet1(nf,a,b, &x,&y,&z,&t);
      x = RgC_add(nfC_nf_mul(nf, c1, x), nfC_nf_mul(nf, c2, y));
      y = RgC_add(nfC_nf_mul(nf, c1, z), nfC_nf_mul(nf, c2, t));
      gerepileall(av2, 2, &x,&y);
      gel(A,i) = x;
      gel(A,i+1) = y;
      gel(I,i+1) = Q_primitive_part(idealmul(nf,a,b), &p1);
      if (p1) gel(A,i+1) = nfC_nf_mul(nf, gel(A,i+1), p1);
    }
  }
  l = lg(order);
  p1 = cgetg(l,t_VEC);
  gel(p1,1) = A;
  gel(p1,2) = I; for (i=3; i<l; i++) gel(p1,i) = gel(order,i);
  return gerepilecopy(av, p1);
}

/* Given bnf and either an order as output by rnfpseudobasis or a polynomial,
 * and outputs a basis if it is free, an n+1-generating set if it is not */
GEN
rnfbasis(GEN bnf, GEN order)
{
  pari_sp av = avma;
  long j, n;
  GEN nf, A, I, cl, col, a;

  bnf = checkbnf(bnf); nf = bnf_get_nf(bnf);
  order = get_order(nf, order, "rnfbasis");
  I = gel(order,2); n = lg(I)-1;
  j=1; while (j<n && ideal_is1(gel(I,j))) j++;
  if (j<n)
  {
    order = rnfsteinitz(nf,order);
    I = gel(order,2);
  }
  A = gel(order,1);
  col= gel(A,n); A = vecslice(A, 1, n-1);
  cl = gel(I,n);
  a = gen_if_principal(bnf, cl);
  if (!a)
  {
    GEN v = idealtwoelt(nf, cl);
    A = shallowconcat(A, gmul(gel(v,1), col));
    a = gel(v,2);
  }
  A = shallowconcat(A, nfC_nf_mul(nf, col, a));
  return gerepilecopy(av, A);
}

/* Given bnf and either an order as output by rnfpseudobasis or a polynomial,
 * and outputs a basis (not pseudo) in Hermite Normal Form if it exists, zero
 * if not
 */
GEN
rnfhnfbasis(GEN bnf, GEN order)
{
  pari_sp av = avma;
  long j, n;
  GEN nf, A, I, a;

  bnf = checkbnf(bnf); nf = bnf_get_nf(bnf);
  order = get_order(nf, order, "rnfbasis");
  A = gel(order,1); A = RgM_shallowcopy(A);
  I = gel(order,2); n = lg(A)-1;
  for (j=1; j<=n; j++)
  {
    if (ideal_is1(gel(I,j))) continue;
    a = gen_if_principal(bnf, gel(I,j));
    if (!a) { avma = av; return gen_0; }
    gel(A,j) = nfC_nf_mul(nf, gel(A,j), a);
  }
  return gerepilecopy(av,A);
}

static long
rnfisfree_aux(GEN bnf, GEN order)
{
  long n, j;
  GEN nf, P, I;

  bnf = checkbnf(bnf);
  if (is_pm1( bnf_get_no(bnf) )) return 1;
  nf = bnf_get_nf(bnf);
  order = get_order(nf, order, "rnfisfree");
  I = gel(order,2); n = lg(I)-1;
  j=1; while (j<=n && ideal_is1(gel(I,j))) j++;
  if (j>n) return 1;

  P = gel(I,j);
  for (j++; j<=n; j++)
    if (!ideal_is1(gel(I,j))) P = idealmul(nf,P,gel(I,j));
  return gequal0( isprincipal(bnf,P) );
}

long
rnfisfree(GEN bnf, GEN order)
{
  pari_sp av = avma;
  long n = rnfisfree_aux(bnf, order);
  avma = av; return n;
}

/**********************************************************************/
/**                                                                  **/
/**                   COMPOSITUM OF TWO NUMBER FIELDS                **/
/**                                                                  **/
/**********************************************************************/
static GEN
compositum_fix(GEN nf, GEN A)
{
  int ok;
  if (nf)
  {
    long i, l = lg(A);
    A = shallowcopy(A);
    for (i=2; i<l; i++) gel(A,i) = basistoalg(nf, gel(A,i));
    ok = nfissquarefree(nf,A);
  }
  else
  {
    A = Q_primpart(A); RgX_check_ZX(A,"polcompositum");
    ok = ZX_is_squarefree(A);
  }
  if (!ok) pari_err_DOMAIN("polcompositum","issquarefree(arg)","=",gen_0,A);
  return A;
}
INLINE long
nextk(long k) { return k>0 ? -k : 1-k; }

/* modular version */
GEN
nfcompositum(GEN nf, GEN A, GEN B, long flag)
{
  pari_sp av = avma;
  int same;
  long v, k;
  GEN C, D, LPRS;

  if (typ(A)!=t_POL) pari_err_TYPE("polcompositum",A);
  if (typ(B)!=t_POL) pari_err_TYPE("polcompositum",B);
  if (degpol(A)<=0 || degpol(B)<=0) pari_err_CONSTPOL("polcompositum");
  v = varn(A);
  if (varn(B) != v) pari_err_VAR("polcompositum", A,B);
  if (nf)
  {
    nf = checknf(nf);
    if (varncmp(v,nf_get_varn(nf))>=0) pari_err_PRIORITY("polcompositum", nf, ">=",  v);
  }
  same = (A == B || RgX_equal(A,B));
  A = compositum_fix(nf,A);
  if (!same) B = compositum_fix(nf,B);

  D = LPRS = NULL; /* -Wall */
  k = same? -1: 1;
  if (nf)
  {
    long v0 = fetch_var();
    GEN q;
    for(;; k = nextk(k))
    {
      GEN chgvar = deg1pol_shallow(stoi(k),pol_x(v0),v);
      GEN B1 = poleval(B,chgvar);
      C = RgX_resultant_all(A,B1,&q);
      C = gsubst(C,v0,pol_x(v));
      if (nfissquarefree(nf,C)) break;
    }
    C = lift_if_rational(C);
    if (flag&1)
    {
      GEN H0, H1;
      H0 = gsubst(gel(q,2),v0,pol_x(v));
      H1 = gsubst(gel(q,3),v0,pol_x(v));
      if (typ(H0) != t_POL) H0 = scalarpol_shallow(H0,v);
      if (typ(H1) != t_POL) H1 = scalarpol_shallow(H1,v);
      H0 = lift_if_rational(H0);
      H1 = lift_if_rational(H1);
      LPRS = mkvec2(H0,H1);
    }
  }
  else
  {
    B = leafcopy(B); setvarn(B,fetch_var_higher());
    C = ZX_ZXY_resultant_all(A, B, &k, (flag&1)? &LPRS: NULL);
    setvarn(C, v);
  }
  /* C = Res_Y (A(Y), B(X + kY)) guaranteed squarefree */
  if (same)
  {
    D = RgX_rescale(A, stoi(1 - k));
    C = RgX_div(C, D);
    if (degpol(C) <= 0)
      C = mkvec(D);
    else
      C = shallowconcat(nf? gel(nffactor(nf,C),1): ZX_DDF(C), D);
  }
  else if (flag & 2)
    C = mkvec(C);
  else
    C = nf? gel(nffactor(nf,C),1): ZX_DDF(C);
  gen_sort_inplace(C, (void*)(nf?&cmp_RgX: &cmpii), &gen_cmp_RgX, NULL);
  if (flag&1)
  { /* a,b,c root of A,B,C = compositum, c = b - k a */
    long i, l = lg(C);
    GEN a, b, mH0 = RgX_neg(gel(LPRS,1)), H1 = gel(LPRS,2);
    setvarn(mH0,v);
    setvarn(H1,v);
    for (i=1; i<l; i++)
    {
      GEN D = gel(C,i);
      a = RgXQ_mul(mH0, nf? RgXQ_inv(H1,D): QXQ_inv(H1,D), D);
      b = gadd(pol_x(v), gmulsg(k,a));
      if (degpol(D) == 1) b = RgX_rem(b,D);
      gel(C,i) = mkvec4(D, mkpolmod(a,D), mkpolmod(b,D), stoi(-k));
    }
  }
  (void)delete_var();
  settyp(C, t_VEC);
  if (flag&2) C = gel(C,1);
  return gerepilecopy(av, C);
}
GEN
polcompositum0(GEN A, GEN B, long flag)
{ return nfcompositum(NULL,A,B,flag); }

GEN
compositum(GEN pol1,GEN pol2) { return polcompositum0(pol1,pol2,0); }
GEN
compositum2(GEN pol1,GEN pol2) { return polcompositum0(pol1,pol2,1); }

/* Assume A,B irreducible (in particular squarefree) and define linearly
 * disjoint extensions: no factorisation needed */
GEN
ZX_compositum_disjoint(GEN A, GEN B)
{
  long k = 1;
  return ZX_ZXY_rnfequation(A, B, &k);
}

static GEN
lastel(GEN x) { return gel(x, lg(x)-1); }

static GEN
nfsplitting_composite(GEN P)
{
  GEN F = gel(ZX_factor(P), 1), Q = NULL;
  long i, n = lg(F)-1;
  for (i = 1; i <= n; i++)
  {
    GEN Fi = gel(F, i);
    if (degpol(Fi) == 1) continue;
    Q = Q ? lastel(compositum(Q, Fi)): Fi;
  }
  return Q ? Q: pol_x(varn(P));
}
GEN
nfsplitting(GEN T, GEN D)
{
  pari_sp av = avma;
  long d, v;
  GEN F, K;
  T = get_nfpol(T,&K);
  if (!K)
  {
    if (typ(T) != t_POL) pari_err_TYPE("nfsplitting",T);
    T = Q_primpart(T);
    RgX_check_ZX(T,"nfsplitting");
  }
  T = nfsplitting_composite(T);
  d = degpol(T);
  if (d<=1) return pol_x(varn(T));
  if (!K) {
    if (!isint1(leading_coeff(T))) K = T = polredbest(T,0);
    K = T;
  }
  if (D)
  {
    if (typ(D) != t_INT || signe(D) < 1) pari_err_TYPE("nfsplitting",D);
  }
  else
  {
    char *data = stack_strcat(pari_datadir, "/galdata");
    long dmax = pari_is_dir(data)? 11: 7;
    D = (d <= dmax)? gel(polgalois(T,DEFAULTPREC), 1): mpfact(d);
  }
  d = itos_or_0(D);
  v = varn(T);
  T = leafcopy(T); setvarn(T, fetch_var_higher());
  for(F = T;;)
  {
    GEN P = gel(nffactor(K, F), 1), Q = gel(P,lg(P)-1);
    if (degpol(gel(P,1)) == degpol(Q)) break;
    F = rnfequation(K,Q);
    if (degpol(F) == d) break;
  }
  if (umodiu(D,degpol(F)))
  {
    char *sD = itostr(D);
    pari_warn(warner,stack_strcat("ignoring incorrect degree bound ",sD));
  }
  (void)delete_var();
  setvarn(F,v);
  return gerepilecopy(av, F);
}
