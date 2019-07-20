/* Copyright (C) 2000  The PARI group.

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
/**         TORSION OF ELLIPTIC CURVES over NUMBER FIELDS          **/
/**                                                                **/
/********************************************************************/
#include "pari.h"
#include "paripriv.h"
static int
smaller_x(GEN p, GEN q)
{
  int s = abscmpii(denom_i(p), denom_i(q));
  return (s<0 || (s==0 && abscmpii(numer_i(p),numer_i(q)) < 0));
}

/* best generator in cycle of length k */
static GEN
best_in_cycle(GEN e, GEN p, long k)
{
  GEN p0 = p,q = p;
  long i;

  for (i=2; i+i<k; i++)
  {
    q = elladd(e,q,p0);
    if (ugcd(i,k)==1 && smaller_x(gel(q,1), gel(p,1))) p = q;
  }
  return (gsigne(ec_dmFdy_evalQ(e,p)) < 0)? ellneg(e,p): p;
}

/* <p,q> = E_tors, possibly NULL (= oo), p,q independent unless NULL
 * order p = k, order q = 2 unless NULL */
static GEN
tors(GEN e, long k, GEN p, GEN q, GEN v)
{
  GEN r;
  if (q)
  {
    long n = k>>1;
    GEN p1, best = q, np = ellmul(e,p,utoipos(n));
    if (n % 2 && smaller_x(gel(np,1), gel(best,1))) best = np;
    p1 = elladd(e,q,np);
    if (smaller_x(gel(p1,1), gel(best,1))) q = p1;
    else if (best == np) { p = elladd(e,p,q); q = np; }
    p = best_in_cycle(e,p,k);
    if (v)
    {
      p = ellchangepointinv(p,v);
      q = ellchangepointinv(q,v);
    }
    r = cgetg(4,t_VEC);
    gel(r,1) = utoipos(2*k);
    gel(r,2) = mkvec2(utoipos(k), gen_2);
    gel(r,3) = mkvec2copy(p, q);
  }
  else
  {
    if (p)
    {
      p = best_in_cycle(e,p,k);
      if (v) p = ellchangepointinv(p,v);
      r = cgetg(4,t_VEC);
      gel(r,1) = utoipos(k);
      gel(r,2) = mkvec( gel(r,1) );
      gel(r,3) = mkvec( gcopy(p) );
    }
    else
    {
      r = cgetg(4,t_VEC);
      gel(r,1) = gen_1;
      gel(r,2) = cgetg(1,t_VEC);
      gel(r,3) = cgetg(1,t_VEC);
    }
  }
  return r;
}

/* Finds a multiplicative upper bound for #E_tor; assume integral model */
static long
torsbound(GEN e)
{
  GEN D = ell_get_disc(e);
  pari_sp av = avma, av2;
  long m, b, bold, nb;
  forprime_t S;
  long CM = ellQ_get_CM(e);
  nb = expi(D) >> 3;
  /* nb = number of primes to try ~ 1 prime every 8 bits in D */
  b = bold = 5040; /* = 2^4 * 3^2 * 5 * 7 */
  m = 0;
  /* p > 2 has good reduction => E(Q) injects in E(Fp) */
  (void)u_forprime_init(&S, 3, ULONG_MAX);
  av2 = avma;
  while (m < nb || (b > 12 && b != 16))
  {
    ulong p = u_forprime_next(&S);
    if (!p) pari_err_BUG("torsbound [ran out of primes]");
    if (!umodiu(D, p)) continue;

    b = ugcd(b, p+1 - ellap_CM_fast(e,p,CM));
    avma = av2;
    if (b == 1) break;
    if (b == bold) m++; else { bold = b; m = 0; }
  }
  avma = av; return b;
}

/* return a rational point of order pk = p^k on E, or NULL if E(Q)[k] = O.
 * *fk is either NULL (pk = 4 or prime) or elldivpol(p^(k-1)).
 * Set *fk to elldivpol(p^k) */
static GEN
tpoint(GEN E, long pk, GEN *fk)
{
  GEN f = elldivpol(E,pk,0), g = *fk, v;
  long i, l;
  *fk = f;
  if (g) f = RgX_div(f, g);
  v = nfrootsQ(f); l = lg(v);
  for (i = 1; i < l; i++)
  {
    GEN x = gel(v,i);
    GEN y = ellordinate(E,x,0);
    if (lg(y) != 1) return mkvec2(x,gel(y,1));
  }
  return NULL;
}
/* return E(Q)[2] */
static GEN
t2points(GEN E, GEN *f2)
{
  long i, l;
  GEN v;
  *f2 = ec_bmodel(E);
  v = nfrootsQ(*f2); l = lg(v);
  for (i = 1; i < l; i++)
  {
    GEN x = gel(v,i);
    GEN y = ellordinate(E,x,0);
    if (lg(y) != 1) gel(v,i) = mkvec2(x,gel(y,1));
  }
  return v;
}

static GEN
elltors_divpol(GEN E)
{
  GEN T2 = NULL, p, P, Q, v;
  long v2, r2, B;

  E = ellintegralmodel_i(E, &v);
  B = torsbound(E); /* #E_tor | B */
  if (B == 1) return tors(E,1,NULL,NULL, v);
  v2 = vals(B); /* bound for v_2(point order) */
  B >>= v2;
  p = const_vec(9, NULL);
  r2 = 0;
  if (v2) {
    GEN f;
    T2 = t2points(E, &f);
    switch(lg(T2)-1)
    {
      case 0:  v2 = 0; break;
      case 1:  r2 = 1; if (v2 == 4) v2 = 3; break;
      default: r2 = 2; v2--; break; /* 3 */
    }
    if (v2) gel(p,2) = gel(T2,1);
    /* f = f_2 */
    if (v2 > 1) { gel(p,4) = tpoint(E,4, &f); if (!gel(p,4)) v2 = 1; }
    /* if (v2>1) now f = f4 */
    if (v2 > 2) { gel(p,8) = tpoint(E,8, &f); if (!gel(p,8)) v2 = 2; }
  }
  B <<= v2;
  if (B % 3 == 0) {
    GEN f3 = NULL;
    gel(p,3) = tpoint(E,3,&f3);
    if (!gel(p,3)) B /= (B%9)? 3: 9;
    if (gel(p,3) && B % 9 == 0)
    {
      gel(p,9) = tpoint(E,9,&f3);
      if (!gel(p,9)) B /= 3;
    }
  }
  if (B % 5 == 0) {
    GEN junk = NULL;
    gel(p,5) = tpoint(E,5,&junk);
    if (!gel(p,5)) B /= 5;
  }
  if (B % 7 == 0) {
    GEN junk = NULL;
    gel(p,7) = tpoint(E,7,&junk);
    if (!gel(p,7)) B /= 7;
  }
  /* B is the exponent of E_tors(Q), r2 is the rank of its 2-Sylow,
   * for i > 1, p[i] is a point of order i if one exists and i is a prime power
   * and NULL otherwise */
  if (r2 == 2) /* 2 cyclic factors */
  { /* C2 x C2 */
    if (B == 2) return tors(E,2, gel(T2,1), gel(T2,2), v);
    else if (B == 6)
    { /* C2 x C6 */
      P = elladd(E, gel(p,3), gel(T2,1));
      Q = gel(T2,2);
    }
    else
    { /* C2 x C4 or C2 x C8 */
      P = gel(p, B);
      Q = gel(T2,2);
      if (gequal(Q, ellmul(E, P, utoipos(B>>1)))) Q = gel(T2,1);
    }
  }
  else /* cyclic */
  {
    Q = NULL;
    if (v2)
    {
      if (B>>v2 == 1)
        P = gel(p, B);
      else
        P = elladd(E, gel(p, B>>v2), gel(p,1<<v2));
    }
    else P = gel(p, B);
  }
  return tors(E,B, P, Q, v);
}

/* either return one prime of degree 1 above p or NULL (none or expensive) */
static GEN
primedec_deg1(GEN K, GEN p)
{
  GEN r, T, f = nf_get_index(K);
  if (dvdii(f,p)) return NULL;
  T = nf_get_pol(K);
  r = FpX_oneroot(T, p); if (!r) return NULL;
  r = deg1pol_shallow(gen_1, Fp_neg(r,p), varn(T));
  return idealprimedec_kummer(K, r, 1, p);
}

/* Bound for the elementary divisors of the torsion group of elliptic curve
 * Reduce the curve modulo some small good primes */
static GEN
nftorsbound(GEN E)
{
  pari_sp av;
  long k = 0, g;
  GEN B1 = gen_0, B2 = gen_0, K = ellnf_get_nf(E);
  GEN D = ell_get_disc(E), ND = idealnorm(K,D);
  forprime_t S;
  if (typ(ND) == t_FRAC) ND = gel(ND,1);
  ND = mulii(ND, Q_denom(vecslice(E,1,5)));
  g = maxss(5, expi(ND) >> 3);
  if (g > 20) g = 20;
  /* P | p such that e(P/p) < p-1 => E(K) injects in E(k(P)) [otherwise
   * we may lose some p-torsion]*/
  (void)u_forprime_init(&S, 3, ULONG_MAX);
  av = avma;
  while (k < g) /* k = number of good primes already used */
  {
    ulong p = u_forprime_next(&S);
    GEN P, gp;
    long j, l;
    if (!umodiu(ND,p)) continue;
    gp = utoipos(p);
    /* primes of degree 1 are easier and give smaller bounds */
    if (typ(D) != t_POLMOD) /* E/Q */
    {
      P = primedec_deg1(K, gp); /* single P|p has all the information */
      if (!P) continue;
      P = mkvec(P);
    }
    else
      P = idealprimedec_limit_f(K, utoipos(p), 1);
    l = lg(P);
    for (j = 1; j < l; j++,k++)
    {
      GEN Q = gel(P,j), EQ, cyc;
      long n;
      if ((ulong)pr_get_e(Q) >= p-1) continue;
      EQ = ellinit(E,zkmodprinit(K,Q),0);
      cyc = ellgroup(EQ, NULL);
      n = lg(cyc)-1;
      if (n == 0) return mkvec2(gen_1,gen_1);
      B1 = gcdii(B1,gel(cyc,1));
      B2 = (n == 1)? gen_1: gcdii(B2,gel(cyc,2));
      obj_free(EQ);
      /* division by 2 is cheap when it fails, no need to have a sharp bound */
      if (Z_ispow2(B1)) return mkvec2(B1,B2);
    }
    if ((g & 15) == 0) gerepileall(av, 2, &B1, &B2);
  }
  if (abscmpiu(B2, 2) > 0)
  { /* if E(K) has full n-torsion then K contains the n-th roots of 1 */
    GEN n = gel(rootsof1(K), 1);
    B2 = gcdii(B2,n);
  }
  return mkvec2(B1,B2);
}

/* Checks whether the point P is divisible by n in E(K), where xn is
 * [phi_n, psi_n^2]
 * If true, returns a point Q such that nQ = P or -P. Else, returns NULL */
static GEN
ellnfis_divisible_by(GEN E, GEN K, GEN P, GEN xn)
{
  GEN r, x = gel(P,1);
  long i, l;
  if (ell_is_inf(P)) return P;
  r = nfroots(K, RgX_sub(RgX_Rg_mul(gel(xn,2), x), gel(xn,1)));
  l = lg(r);
  for(i=1; i<l; i++)
  {
    GEN a = gel(r,i), y = ellordinate(E,a,0);
    if (lg(y) != 1) return mkvec2(a, gel(y,1));
  }
  return NULL;
}

/* w a variable number of highest priority */
static long
ellisdivisible_i(GEN E, GEN P, GEN n, long w, GEN *pQ)
{
  GEN xP, R, K = NULL, N = NULL;
  long i, l;
  checkell(E);
  switch(ell_get_type(E))
  {
    case t_ELL_Q: break;
    case t_ELL_NF: K = ellnf_get_nf(E); break;
    default: pari_err_TYPE("ellisdivisible",E);
  }
  checkellpt(P);
  switch(typ(n))
  {
    case t_INT:
      N = n;
      if (!isprime(absi_shallow(n)))
      {
        GEN f = absZ_factor(n), LP = gel(f,1), LE = gel(f,2);
        l = lg(LP);
        for (i = 1; i < l; i++)
        {
          long j, e = itos(gel(LE,i));
          GEN xp = ellxn(E,itos(gel(LP,i)), w);
          for (j = 1; j <= e; j++)
            if (!ellisdivisible(E, P, xp, &P)) return 0;
        }
        if (pQ) *pQ = signe(n) < 0? ellneg(E, P): P;
        return 1;
      }
      n = ellxn(E, itou(n), w);
      break;
    case t_VEC:
      if (lg(n) == 3 && typ(gel(n,1)) == t_POL && typ(gel(n,2)) == t_POL) break;
    default:
      pari_err_TYPE("ellisdivisible",n);
      break;
  }
  if (ell_is_inf(P)) { if (pQ) *pQ = ellinf(); return 1; }
  if (!N)
  {
    long d, d2 = degpol(gel(n,1));
    if (d2 < 0)
      N = gen_0;
    else
    {
      if (!uissquareall(d2,(ulong*)&d)) pari_err_TYPE("ellisdivisible",n);
      N = stoi(d);
    }
  }
  if (!signe(N)) return 0;
  xP = gel(P,1);
  R = nfroots(K, RgX_sub(RgX_Rg_mul(gel(n,2), xP), gel(n,1)));
  l = lg(R);
  for(i = 1; i < l; i++)
  {
    GEN Q,y, x = gel(R,i), a = ellordinate(E,x,0);
    if (lg(a) == 1) continue;
    y = gel(a,1);
    Q = mkvec2(x,y);
    if (!gequal(P,ellmul(E,Q,N))) Q = ellneg(E,Q); /* nQ = -P */
    if (pQ) *pQ = Q;
    return 1;
  }
  return 0;
}
long
ellisdivisible(GEN E, GEN P, GEN n, GEN *pQ)
{
  pari_sp av = avma;
  long w = fetch_var_higher(), t = ellisdivisible_i(E, P, n, w, pQ);
  delete_var();
  if (!t) { avma = av; return 0; }
  if (pQ) *pQ = gerepilecopy(av, *pQ); else avma = av;
  return 1;
}
/* 2-torsion point of abscissa x */
static GEN
tor2(GEN E, GEN x) { return mkvec2(x, gmul2n(gneg(ec_h_evalx(E,x)), -1)); }

static GEN
ptor0(void)
{ return mkvec2(mkvec(gen_1),cgetg(1,t_VEC)); }
static GEN
ptor1(long p, long n, GEN P)
{ return mkvec2(mkvec(powuu(p,n)), mkvec(P)); }
static GEN
ptor2(long p, long n1, long n2, GEN P1, GEN P2)
{ return mkvec2(mkvec2(powuu(p,n1), powuu(p,n2)), mkvec2(P1,P2)); }

/* Computes the p-primary torsion in E(K). Assume that p is small, should use
 * Weil pairing otherwise.
 * N1, N2 = upper bounds on the integers n1 >= n2 such that
 * E(K)[p^oo] = Z/p^n1 x Z/p^n2
 * Returns [cyc,gen], where E(K)[p^oo] = sum Z/cyc[i] gen[i] */
static GEN
ellnftorsprimary(GEN E, long p, long N1, long N2, long v)
{
  GEN X, P1, P2, Q1, Q2, xp, K = ellnf_get_nf(E);
  long n1, n2;

  /* compute E[p] = < P1 > or < P1, P2 > */
  P1 = P2 = ellinf();
  X = nfroots(K, elldivpol(E,p,v));
  if(lg(X) == 1) return ptor0();
  if (p==2)
  {
    P1 = tor2(E, gel(X,1));
    if (lg(X) > 2) P2 = tor2(E, gel(X,2)); /* E[2] = (Z/2Z)^2 */
  }
  else
  {
    long j, l = lg(X), nT, a;
    GEN T = vectrunc_init(l);
    for(j=1; j < l; j++)
    {
      GEN a = gel(X,j), Y = ellordinate(E,a,0);
      if (lg(Y) != 1) vectrunc_append(T, mkvec2(a,gel(Y,1)));
    }
    nT = lg(T)-1;
    if (!nT) return ptor0();
    P1 = gel(T,1);
    a = (p-1)/2;
    if (nT != a)
    { /* E[p] = (Z/pZ)^2 */
      GEN Z = cgetg(a+1,t_VEC), Q1 = P1;
      long k;
      gel(Z,1) = Q1;
      for (k=2; k <= a; k++) gel(Z,k) = elladd(E,Q1,P1);
      gen_sort_inplace(Z, (void*)&cmp_universal, &cmp_nodata, NULL);
      while (tablesearch(Z, gel(T,k), &cmp_universal)) k++;
      P2 = gel(T,k);
    }
  }
  xp = ellxn(E, p, v);

  if (ell_is_inf(P2))
  { /* E[p^oo] is cyclic, start from P1 and divide by p while possible */
    for (n1 = 1; n1 < N1; n1++)
    {
      GEN Q = ellnfis_divisible_by(E,K,P1,xp);
      if (!Q) break;
      P1 = Q;
    }
    return ptor1(p, n1, P1);
  }

  /* E[p] = (Z/pZ)^2, compute n2 and E[p^n2] */
  Q1 = NULL;
  for (n2 = 1; n2 < N2; n2++)
  {
    Q1 = ellnfis_divisible_by(E,K,P1,xp);
    Q2 = ellnfis_divisible_by(E,K,P2,xp);
    if (!Q1 || !Q2) break;
    P1 = Q1;
    P2 = Q2;
  }

  /* compute E[p^oo] = < P1, P2 > */
  n1 = n2;
  if (n2 == N2)
  {
    if (N1 == N2) return ptor2(p, n2,n2, P1,P2);
    Q1 = ellnfis_divisible_by(E,K,P1,xp);
  }
  if (Q1) { P1 = Q1; n1++; }
  else
  {
    Q2 = ellnfis_divisible_by(E,K,P2,xp);
    if (Q2) { P2 = P1; P1 = Q2; n1++; }
    else
    {
      long k;
      for (k = 1; k < p; k++)
      {
        P1 = elladd(E,P1,P2);
        Q1 = ellnfis_divisible_by(E,K,P1,xp);
        if (Q1) { P1 = Q1; n1++; break; }
      }
      if (k == p) return ptor2(p, n2,n2, P1,P2);
    }
  }
  /* P1,P2 of order p^n1,p^n2 with n1=n2+1.
   * Keep trying to divide P1 + k P2 with 0 <= k < p by p */
  while (n1 < N1)
  {
    Q1 = ellnfis_divisible_by(E,K,P1,xp);
    if (Q1) { P1 = Q1; n1++; }
    else
    {
      long k;
      for (k = 1; k < p; k++)
      {
        P1 = elladd(E,P1,P2);
        Q1 = ellnfis_divisible_by(E,K,P1,xp);
        if (Q1) { P1 = Q1; n1++; break; }
      }
      if (k == p) break;
    }
  }
  return ptor2(p, n1,n2, P1,P2);
}

/* P affine point */
static GEN
nfpt(GEN e, GEN P)
{
  GEN T = nf_get_pol(ellnf_get_nf(e));
  GEN x = gel(P,1), y = gel(P,2);
  long tx = typ(x), ty = typ(y);
  if (tx == ty) return P;
  if (tx != t_POLMOD) x = mkpolmod(x,T); else y = mkpolmod(y,T);
  return mkvec2(x,y);
}
/* Computes the torsion subgroup of E(K), as [order, cyc, gen] */
static GEN
ellnftors(GEN e)
{
  GEN B = nftorsbound(e), B1 = gel(B,1), B2 = gel(B,2), d1,d2, P1,P2;
  GEN f = Z_factor(B1), P = gel(f,1), E = gel(f,2);
  long i, l = lg(P), v = fetch_var_higher();

  d1 = d2 = gen_1; P1 = P2 = ellinf();
  for (i=1; i<l; i++)
  {
    long p = itos(gel(P,i)); /* Compute p-primary torsion */
    long N1 = itos(gel(E,i)); /* >= n1 */
    long N2 = Z_lval(B2,p); /* >= n2 */
    GEN T = ellnftorsprimary(e, p, N1, N2, v), cyc = gel(T,1), gen = gel(T,2);
    if (is_pm1(gel(cyc,1))) continue;
    /* update generators P1,P2 and their respective orders d1,d2 */
    P1 = elladd(e, P1, gel(gen,1)); d1 = mulii(d1, gel(cyc,1));
    if (lg(cyc) > 2)
    { P2 = elladd(e, P2, gel(gen,2)); d2 = mulii(d2, gel(cyc,2)); }
  }
  (void)delete_var();
  if (is_pm1(d1)) return mkvec3(gen_1,cgetg(1,t_VEC),cgetg(1,t_VEC));
  if (is_pm1(d2)) return mkvec3(d1, mkvec(d1), mkvec(nfpt(e,P1)));
  return mkvec3(mulii(d1,d2), mkvec2(d1,d2), mkvec2(nfpt(e,P1),nfpt(e,P2)));
}

GEN
elltors(GEN e)
{
  pari_sp av = avma;
  GEN t = NULL;
  checkell(e);
  switch(ell_get_type(e))
  {
    case t_ELL_Q:  t = elltors_divpol(e); break;
    case t_ELL_NF: t = ellnftors(e); break;
    case t_ELL_Fp:
    case t_ELL_Fq: return ellgroup0(e,NULL,1);
    default: pari_err_TYPE("elltors",e);
  }
  return gerepilecopy(av, t);
}

GEN
elltors0(GEN e, long flag) { (void)flag; return elltors(e); }

/********************************************************************/
/**                                                                **/
/**                ORDER OF POINTS over NUMBER FIELDS              **/
/**                                                                **/
/********************************************************************/
/* E a t_ELL_Q (use Mazur's theorem) */
long
ellorder_Q(GEN E, GEN P)
{
  pari_sp av = avma;
  GEN dx, dy, d4, d6, D, Pp, Q;
  forprime_t S;
  ulong a4, p;
  long k;
  if (ell_is_inf(P)) return 1;
  if (gequal(P, ellneg(E,P))) return 2;

  dx = Q_denom(gel(P,1));
  dy = Q_denom(gel(P,2));
  if (ell_is_integral(E)) /* integral model, try Nagell Lutz */
    if (abscmpiu(dx, 4) > 0 || abscmpiu(dy, 8) > 0) return 0;

  d4 = Q_denom(ell_get_c4(E));
  d6 = Q_denom(ell_get_c6(E));
  D = ell_get_disc (E);
  /* choose not too small prime p dividing neither a coefficient of the
     short Weierstrass form nor of P and leading to good reduction */
  u_forprime_init(&S, 100003, ULONG_MAX);
  while ( (p = u_forprime_next(&S)) )
    if (umodiu(d4, p) && umodiu(d6, p) && Rg_to_Fl(D, p)
     && umodiu(dx, p) && umodiu(dy, p)) break;

  /* transform E into short Weierstrass form Ep modulo p and P to Pp on Ep,
   * check whether the order of Pp on Ep is <= 12 */
  Pp = point_to_a4a6_Fl(E, P, p, &a4);
  for (Q = Fle_dbl(Pp, a4, p), k = 2;
       !ell_is_inf(Q) && k <= 12;
       Q = Fle_add(Q, Pp, a4, p), k++) /* empty */;

  if (k == 13) k = 0;
  else
  { /* check whether [k]P = O over Q. Save potentially costly last elladd */
    GEN R;
    Q = ellmul(E, P, utoipos(k>>1));
    R = odd(k)? elladd(E, P,Q): Q;
    if (!gequal(Q, ellneg(E,R))) k = 0;
  }
  avma = av; return k;
}
/* E a t_ELL_NF */
static GEN
ellorder_nf(GEN E, GEN P)
{
  GEN K = ellnf_get_nf(E), B;
  pari_sp av = avma;
  GEN dx, dy, d4, d6, D, ND, Ep, Pp, Q, gp, modpr, pr, T, k;
  forprime_t S;
  ulong a4, p;
  if (ell_is_inf(P)) return gen_1;
  if (gequal(P, ellneg(E,P))) return gen_2;

  B = gel(nftorsbound(E), 1);
  dx = Q_denom(gel(P,1));
  dy = Q_denom(gel(P,2));
  d4 = Q_denom(ell_get_c4(E));
  d6 = Q_denom(ell_get_c6(E));
  D = ell_get_disc(E);
  ND = idealnorm(K,D);
  if (typ(ND) == t_FRAC) ND = gel(ND,1);

  /* choose not too small prime p of degree 1 dividing neither a coefficient of
   * the short Weierstrass form nor of P and leading to good reduction */
  u_forprime_init(&S, 100003, ULONG_MAX);
  while ( (p = u_forprime_next(&S)) )
  {
    if (!umodiu(d4, p) || !umodiu(d6, p) || !umodiu(ND, p)
     || !umodiu(dx, p) || !umodiu(dy, p)) continue;
    gp = utoipos(p);
    pr = primedec_deg1(K, gp);
    if (pr) break;
  }

  modpr = nf_to_Fq_init(K, &pr,&T,&gp);
  Ep = ellinit(E, pr, 0);
  Pp = nfV_to_FqV(P, K, modpr);

  /* transform E into short Weierstrass form Ep modulo p and P to Pp on Ep,
   * check whether the order of Pp on Ep divides B */
  Pp = point_to_a4a6_Fl(Ep, Pp, p, &a4);
  if (!ell_is_inf(Fle_mul(Pp, B, a4, p))) { avma = av; return gen_0; }
  k = Fle_order(Pp, B, a4, p);
  { /* check whether [k]P = O over K. Save potentially costly last elladd */
    GEN R;
    Q = ellmul(E, P, shifti(k,-1));
    R = mod2(k)? elladd(E, P,Q): Q;
    if (!gequal(Q, ellneg(E,R))) k = gen_0;
  }
  return gerepileuptoint(av, k);
}

GEN
ellorder(GEN E, GEN P, GEN o)
{
  pari_sp av = avma;
  GEN fg, r, E0 = E;
  checkell(E); checkellpt(P);
  if (ell_is_inf(P)) return gen_1;
  if (ell_get_type(E)==t_ELL_Q)
  {
    long tx = typ(gel(P,1)), ty = typ(gel(P,2));
    GEN p = NULL;
    if (is_rational_t(tx) && is_rational_t(ty)) return utoi(ellorder_Q(E, P));
    if (tx == t_INTMOD || tx == t_FFELT) p = gel(P,1);
    if (!p && (ty == t_INTMOD || ty == t_FFELT)) p = gel(P,2);
    if (p)
    {
      E = ellinit(E,p,0);
      if (lg(E)==1) pari_err_IMPL("ellorder for curve with singular reduction");
    }
  }
  if (ell_get_type(E)==t_ELL_NF) return ellorder_nf(E, P);
  checkell_Fq(E);
  fg = ellff_get_field(E);
  if (!o) o = ellff_get_o(E);
  if (typ(fg)==t_FFELT)
    r = FF_ellorder(E, P, o);
  else
  {
    GEN p = fg, e = ellff_get_a4a6(E);
    GEN Pp = FpE_changepointinv(RgE_to_FpE(P,p), gel(e,3), p);
    r = FpE_order(Pp, o, gel(e,1), p);
  }
  if (E != E0) obj_free(E);
  return gerepileuptoint(av, r);
}

GEN
orderell(GEN e, GEN z) { return ellorder(e,z,NULL); }
