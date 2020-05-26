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
/*               S-CLASS GROUP AND NORM SYMBOLS                    */
/*          (Denis Simon, desimon@math.u-bordeaux.fr)              */
/*                                                                 */
/*******************************************************************/
#include "pari.h"
#include "paripriv.h"

/* p > 2, T ZX, p prime, x t_INT */
static long
lemma6(GEN T, GEN p, long nu, GEN x)
{
  long la, mu;
  pari_sp av = avma;
  GEN gpx, gx = poleval(T, x);

  if (Zp_issquare(gx, p)) { avma = av; return 1; }

  la = Z_pval(gx, p);
  gpx = poleval(ZX_deriv(T), x);
  mu = signe(gpx)? Z_pval(gpx,p)
                 : la+nu+1; /* mu = +oo */
  avma = av;
  if (la > mu<<1) return 1;
  if (la >= nu<<1 && mu >= nu) return 0;
  return -1;
}
/* p = 2, T ZX, x t_INT: return 1 = yes, -1 = no, 0 = inconclusive */
static long
lemma7(GEN T, long nu, GEN x)
{
  long odd4, la, mu;
  pari_sp av = avma;
  GEN gpx, oddgx, gx = poleval(T, x);

  if (Zp_issquare(gx,gen_2)) return 1;

  gpx = poleval(ZX_deriv(T), x);
  la = Z_lvalrem(gx, 2, &oddgx);
  odd4 = umodiu(oddgx,4); avma = av;

  mu = vali(gpx);
  if (mu < 0) mu = la+nu+1; /* mu = +oo */

  if (la > mu<<1) return 1;
  if (nu > mu)
  {
    long mnl = mu+nu-la;
    if (odd(la)) return -1;
    if (mnl==1) return 1;
    if (mnl==2 && odd4==1) return 1;
  }
  else
  {
    long nu2 = nu << 1;
    if (la >= nu2) return 0;
    if (la == nu2 - 2 && odd4==1) return 0;
  }
  return -1;
}

/* T a ZX, p a prime, pnu = p^nu, x0 t_INT */
static long
zpsol(GEN T, GEN p, long nu, GEN pnu, GEN x0)
{
  long i, res;
  pari_sp av = avma, btop;
  GEN x, pnup;

  res = absequaliu(p,2)? lemma7(T,nu,x0): lemma6(T,p,nu,x0);
  if (res== 1) return 1;
  if (res==-1) return 0;
  x = x0; pnup = mulii(pnu,p);
  btop = avma;
  for (i=0; i < itos(p); i++)
  {
    x = addii(x,pnu);
    if (zpsol(T,p,nu+1,pnup,x)) { avma = av; return 1; }
    if (gc_needed(btop, 2))
    {
      x = gerepileupto(btop, x);
      if (DEBUGMEM > 1) pari_warn(warnmem, "zpsol: %ld/%Ps",i,p);
    }
  }
  avma = av; return 0;
}

/* return 1 if equation y^2=T(x) has a rational p-adic solution (possibly
 * infinite), 0 otherwise. */
long
hyperell_locally_soluble(GEN T,GEN p)
{
  pari_sp av = avma;
  long res;
  if (typ(T)!=t_POL) pari_err_TYPE("zpsoluble",T);
  if (typ(p)!=t_INT) pari_err_TYPE("zpsoluble",p);
  RgX_check_ZX(T, "zpsoluble");
  res = zpsol(T,p,0,gen_1,gen_0) || zpsol(RgX_recip_shallow(T), p, 1, p, gen_0);
  avma = av; return res;
}

/* is t a square in (O_K/pr) ? Assume v_pr(t) = 0 */
static long
quad_char(GEN nf, GEN t, GEN pr)
{
  GEN ord, ordp, T, p, modpr = zk_to_Fq_init(nf, &pr,&T,&p);
  t = nf_to_Fq(nf,t,modpr);
  if (T)
  {
    ord = subiu( pr_norm(pr), 1 ); /* |(O_K / pr)^*| */
    ordp= subiu( p, 1);            /* |F_p^*|        */
    t = Fq_pow(t, diviiexact(ord, ordp), T,p); /* in F_p^* */
    if (typ(t) == t_POL)
    {
      if (degpol(t)) pari_err_BUG("nfhilbertp");
      t = gel(t,2);
    }
  }
  return kronecker(t, p);
}
/* quad_char(x), x in Z, non-zero mod p */
static long
Z_quad_char(GEN x, GEN pr)
{
  long f = pr_get_f(pr);
  if (!odd(f)) return 1;
  return kronecker(x, pr_get_p(pr));
}

/* (pr,2) = 1. return 1 if x in Z_K is a square in Z_{K_pr}, 0 otherwise.
 * modpr = zkmodprinit(nf,pr) */
static long
psquarenf(GEN nf,GEN x,GEN pr,GEN modpr)
{
  pari_sp av = avma;
  GEN p = pr_get_p(pr);
  long v;

  x = nf_to_scalar_or_basis(nf, x);
  if (typ(x) == t_INT) {
    if (!signe(x)) return 1;
    v = Z_pvalrem(x, p, &x) * pr_get_e(pr);
    if (v&1) return 0;
    v = (Z_quad_char(x, pr) == 1);
  } else {
    v = ZC_nfvalrem(x, pr, &x);
    if (v&1) return 0;
    v = (quad_char(nf, x, modpr) == 1);
  }
  avma = av; return v;
}

/* Is  x a square in (ZK / pr^(1+2e))^* ?  pr | 2 */
static long
check2(GEN nf, GEN x, GEN sprk)
{
  GEN zlog = zlog_pr(nf, x, sprk);
  long i, l = lg(zlog);
  for (i=1; i<l; i++) /* all elementary divisors are even (1+2e > 1) */
    if (mpodd(gel(zlog,i))) return 0;
  return 1;
}

/* pr | 2. Return 1 if x in Z_K is square in Z_{K_pr}, 0 otherwise */
static int
psquare2nf_i(GEN nf,GEN x,GEN pr,GEN sprk)
{
  long v = nfvalrem(nf, x, pr, &x);
  /* now (x,pr) = 1 */
  return v == LONG_MAX || (!odd(v) && check2(nf,x,sprk));
}
static int
psquare2nf(GEN nf,GEN x,GEN pr,GEN sprk)
{
  pari_sp av = avma;
  long v = psquare2nf_i(nf,x,pr,sprk);
  avma = av; return v;
}

/* pr above an odd prime */
static long
lemma6nf(GEN nf, GEN T, GEN pr, long nu, GEN x, GEN modpr)
{
  pari_sp av = avma;
  long la, mu;
  GEN gpx, gx = nfpoleval(nf, T, x);

  if (psquarenf(nf,gx,pr,modpr)) return 1;

  la = nfval(nf,gx,pr);
  gpx = nfpoleval(nf, RgX_deriv(T), x);
  mu = gequal0(gpx)? la+nu+1: nfval(nf,gpx,pr);
  avma = av;
  if (la > (mu<<1)) return 1;
  if (la >= (nu<<1)  && mu >= nu) return 0;
  return -1;
}
/* pr above 2 */
static long
lemma7nf(GEN nf, GEN T, GEN pr, long nu, GEN x, GEN sprk)
{
  long res, la, mu, q;
  GEN gpx, gx = nfpoleval(nf, T, x);

  if (psquare2nf(nf,gx,pr,sprk)) return 1;

  gpx = nfpoleval(nf, RgX_deriv(T), x);
  /* gx /= pi^la, pi a pr-uniformizer */
  la = nfvalrem(nf, gx, pr, &gx);
  mu = gequal0(gpx)? la+nu+1: nfval(nf,gpx,pr);

  if (la > (mu<<1)) return 1;
  if (nu > mu)
  {
    if (la&1) return -1;
    q = mu+nu-la; res = 1;
  }
  else
  {
    long nu2 = nu<<1;
    if (la >= nu2) return 0;
    if (odd(la)) return -1;
    q = nu2-la; res = 0;
  }
  if (q > pr_get_e(pr)<<1)  return -1;
  if (q == 1) return res;

  /* is gx a square mod pi^q ? FIXME : highly inefficient */
  sprk = zlog_pr_init(nf, pr, q);
  if (!check2(nf, gx, sprk)) res = -1;
  return res;
}
/* zinit either a sprk (pr | 2) or a modpr structure (pr | p odd).
   pnu = pi^nu, pi a uniformizer */
static long
zpsolnf(GEN nf,GEN T,GEN pr,long nu,GEN pnu,GEN x0,GEN repr,GEN zinit)
{
  long i, res;
  pari_sp av = avma;
  GEN pnup;

  res = typ(zinit) == t_VEC? lemma7nf(nf,T,pr,nu,x0,zinit)
                           : lemma6nf(nf,T,pr,nu,x0,zinit);
  avma = av;
  if (res== 1) return 1;
  if (res==-1) return 0;
  pnup = nfmul(nf, pnu, pr_get_gen(pr));
  nu++;
  for (i=1; i<lg(repr); i++)
  {
    GEN x = nfadd(nf, x0, nfmul(nf,pnu,gel(repr,i)));
    if (zpsolnf(nf,T,pr,nu,pnup,x,repr,zinit)) { avma = av; return 1; }
  }
  avma = av; return 0;
}

/* Let y = copy(x); y[k] := j; return y */
static GEN
ZC_add_coeff(GEN x, long k, long j)
{ GEN y = shallowcopy(x); gel(y, k) = utoipos(j); return y; }

/* system of representatives for Zk/pr */
static GEN
repres(GEN nf, GEN pr)
{
  long f = pr_get_f(pr), N = nf_get_degree(nf), p = itos(pr_get_p(pr));
  long i, j, k, pi, pf = upowuu(p, f);
  GEN perm = pr_basis_perm(nf, pr), rep = cgetg(pf+1,t_VEC);

  gel(rep,1) = zerocol(N);
  for (pi=i=1; i<=f; i++,pi*=p)
  {
    long t = perm[i];
    for (j=1; j<p; j++)
      for (k=1; k<=pi; k++) gel(rep, j*pi+k) = ZC_add_coeff(gel(rep,k), t, j);
  }
  return rep;
}

/* = 1 if equation y^2 = z^deg(T) * T(x/z) has a pr-adic rational solution
 * (possibly (1,y,0) = oo), 0 otherwise.
 * coeffs of T are algebraic integers in nf */
long
nf_hyperell_locally_soluble(GEN nf,GEN T,GEN pr)
{
  GEN repr, zinit, p1;
  pari_sp av = avma;

  if (typ(T)!=t_POL) pari_err_TYPE("nf_hyperell_locally_soluble",T);
  if (gequal0(T)) return 1;
  checkprid(pr); nf = checknf(nf);
  if (absequaliu(pr_get_p(pr), 2))
  { /* tough case */
    zinit = zlog_pr_init(nf, pr, 1+2*pr_get_e(pr));
    if (psquare2nf(nf,constant_coeff(T),pr,zinit)) return 1;
    if (psquare2nf(nf, leading_coeff(T),pr,zinit)) return 1;
  }
  else
  {
    zinit = zkmodprinit(nf, pr);
    if (psquarenf(nf,constant_coeff(T),pr,zinit)) return 1;
    if (psquarenf(nf, leading_coeff(T),pr,zinit)) return 1;
  }
  repr = repres(nf,pr);
  if (zpsolnf(nf,T,pr,0,gen_1,gen_0,repr,zinit)) { avma=av; return 1; }
  p1 = pr_get_gen(pr);
  if (zpsolnf(nf,RgX_recip_shallow(T),pr,1,p1,gen_0,repr,zinit)) { avma=av; return 1; }

  avma = av; return 0;
}

/* return a * denom(a)^2, as an 'liftalg' */
static GEN
den_remove(GEN nf, GEN a)
{
  GEN da;
  a = nf_to_scalar_or_basis(nf, a);
  switch(typ(a))
  {
    case t_INT: return a;
    case t_FRAC: return mulii(gel(a,1), gel(a,2));
    case t_COL:
      a = Q_remove_denom(a, &da);
      if (da) a = ZC_Z_mul(a, da);
      return nf_to_scalar_or_alg(nf, a);
    default: pari_err_TYPE("nfhilbert",a);
      return NULL;/*LCOV_EXCL_LINE*/
  }
}

static long
hilb2nf(GEN nf,GEN a,GEN b,GEN p)
{
  pari_sp av = avma;
  long rep;
  GEN pol;

  a = den_remove(nf, a);
  b = den_remove(nf, b);
  pol = mkpoln(3, a, gen_0, b);
  /* varn(nf.pol) = 0, pol is not a valid GEN  [as in Pol([x,x], x)].
   * But it is only used as a placeholder, hence it is not a problem */

  rep = nf_hyperell_locally_soluble(nf,pol,p)? 1: -1;
  avma = av; return rep;
}

/* local quadratic Hilbert symbol (a,b)_pr, for a,b (non-zero) in nf */
static long
nfhilbertp(GEN nf, GEN a, GEN b, GEN pr)
{
  GEN t;
  long va, vb, rep;
  pari_sp av = avma;

  if (absequaliu(pr_get_p(pr), 2)) return hilb2nf(nf,a,b,pr);

  /* pr not above 2, compute t = tame symbol */
  va = nfval(nf,a,pr);
  vb = nfval(nf,b,pr);
  if (!odd(va) && !odd(vb)) { avma = av; return 1; }
  /* Trick: pretend the exponent is 2, result is OK up to squares ! */
  t = famat_makecoprime(nf, mkvec2(a,b), mkvec2s(vb, -va),
                        pr, pr_hnf(nf, pr), gen_2);
  if (typ(t) == t_INT) {
    if (odd(va) && odd(vb)) t = negi(t);
    /* t = (-1)^(v(a)v(b)) a^v(b) b^(-v(a)) */
    rep = Z_quad_char(t, pr);
  }
  else if (ZV_isscalar(t)) {
    t = gel(t,1);
    if (odd(va) && odd(vb)) t = negi(t);
    /* t = (-1)^(v(a)v(b)) a^v(b) b^(-v(a)) */
    rep = Z_quad_char(t, pr);
  } else {
    if (odd(va) && odd(vb)) t = ZC_neg(t);
    /* t = (-1)^(v(a)v(b)) a^v(b) b^(-v(a)) */
    rep = quad_char(nf, t, pr);
  }
  /* quad. symbol is image of t by the quadratic character  */
  avma = av; return rep;
}

/* Global quadratic Hilbert symbol (a,b):
 *  =  1 if X^2 - aY^2 - bZ^2 has a point in projective plane
 *  = -1 otherwise
 * a, b should be non-zero */
long
nfhilbert(GEN nf, GEN a, GEN b)
{
  pari_sp av = avma;
  long i, l;
  GEN S, S2, Sa, Sb, sa, sb;

  nf = checknf(nf);
  a = nf_to_scalar_or_basis(nf, a);
  b = nf_to_scalar_or_basis(nf, b);
  /* local solutions in real completions ? [ error in nfsign if arg is 0 ]*/
  sa = nfsign(nf, a);
  sb = nfsign(nf, b); l = lg(sa);
  for (i=1; i<l; i++)
    if (sa[i] && sb[i])
    {
      if (DEBUGLEVEL>3)
        err_printf("nfhilbert not soluble at real place %ld\n",i);
      avma = av; return -1;
    }

  /* local solutions in finite completions ? (pr | 2ab)
   * primes above 2 are toughest. Try the others first */
  Sa = idealfactor(nf, a);
  Sb = idealfactor(nf, b);
  S2 = idealfactor(nf, gen_2);
  S = merge_factor(Sa, Sb, (void*)&cmp_prime_ideal, &cmp_nodata);
  S = merge_factor(S,  S2, (void*)&cmp_prime_ideal, &cmp_nodata);
  S = gel(S,1);
  /* product of all hilbertp is 1 ==> remove one prime (above 2!) */
  for (i=lg(S)-1; i>1; i--)
    if (nfhilbertp(nf,a,b,gel(S,i)) < 0)
    {
      if (DEBUGLEVEL>3)
        err_printf("nfhilbert not soluble at finite place %Ps\n",S[i]);
      avma = av; return -1;
    }
  avma = av; return 1;
}

long
nfhilbert0(GEN nf,GEN a,GEN b,GEN p)
{
  nf = checknf(nf);
  if (p) {
    checkprid(p);
    if (gequal0(a)) pari_err_DOMAIN("nfhilbert", "a", "=", gen_0, a);
    if (gequal0(b)) pari_err_DOMAIN("nfhilbert", "b", "=", gen_0, b);
    return nfhilbertp(nf,a,b,p);
  }
  return nfhilbert(nf,a,b);
}

/* S a list of prime ideal in idealprimedec format. Return res:
 * res[1] = generators of (S-units / units), as polynomials
 * res[2] = [perm, HB, den], for bnfissunit
 * res[3] = [] (was: log. embeddings of res[1])
 * res[4] = S-regulator ( = R * det(res[2]) * \prod log(Norm(S[i])))
 * res[5] = S class group
 * res[6] = S */
GEN
bnfsunit0(GEN bnf, GEN S, long flag, long prec)
{
  pari_sp av = avma;
  long i,j,ls;
  GEN p1,nf,gen,M,U,H;
  GEN sunit,card,sreg,res,pow;

  if (!is_vec_t(typ(S))) pari_err_TYPE("bnfsunit",S);
  bnf = checkbnf(bnf);
  nf = bnf_get_nf(bnf);
  gen = bnf_get_gen(bnf);

  sreg = bnf_get_reg(bnf);
  res=cgetg(7,t_VEC);
  gel(res,1) = gel(res,2) = gel(res,3) = cgetg(1,t_VEC);
  gel(res,4) = sreg;
  gel(res,5) = bnf_get_clgp(bnf);
  gel(res,6) = S; ls=lg(S);

 /* M = relation matrix for the S class group (in terms of the class group
  * generators given by gen)
  * 1) ideals in S
  */
  M = cgetg(ls,t_MAT);
  for (i=1; i<ls; i++)
  {
    p1 = gel(S,i); checkprid(p1);
    gel(M,i) = isprincipal(bnf,p1);
  }
  /* 2) relations from bnf class group */
  M = shallowconcat(M, diagonal_shallow(bnf_get_cyc(bnf)));

  /* S class group */
  H = ZM_hnfall(M, &U, 1);
  card = gen_1;
  if (lg(H) > 1)
  { /* non trivial (rare!) */
    GEN A, u, D = ZM_snfall_i(H, &u, NULL, 1);
    long l;
    ZV_snf_trunc(D); l = lg(D);
    card = ZV_prod(D);
    A = cgetg(l, t_VEC); pow = ZM_inv(u, NULL);
    for(i = 1; i < l; i++) gel(A,i) = idealfactorback(nf, gen, gel(pow,i), 1);
    gel(res,5) = mkvec3(card, D, A);
  }

  /* S-units */
  if (ls>1)
  {
    GEN den, Sperm, perm, dep, B, A, U1 = U;
    long lH, lB, FLAG = flag|nf_FORCE;

   /* U1 = upper left corner of U, invertible. S * U1 = principal ideals
    * whose generators generate the S-units */
    setlg(U1,ls); p1 = cgetg(ls, t_MAT); /* p1 is junk for mathnfspec */
    for (i=1; i<ls; i++) { setlg(U1[i],ls); gel(p1,i) = cgetg(1,t_COL); }
    H = mathnfspec(U1,&perm,&dep,&B,&p1);
    lH = lg(H);
    lB = lg(B);
    if (lg(dep) > 1 && lgcols(dep) > 1) pari_err_BUG("bnfsunit");
   /*                   [ H B  ]            [ H^-1   - H^-1 B ]
    * perm o HNF(U1) =  [ 0 Id ], inverse = [  0         Id   ]
    * (permute the rows)
    * S * HNF(U1) = _integral_ generators for S-units  = sunit */
    Sperm = cgetg(ls, t_VEC); sunit = cgetg(ls, t_VEC);
    for (i=1; i<ls; i++) Sperm[i] = S[perm[i]]; /* S o perm */

    setlg(Sperm, lH);
    for (i=1; i<lH; i++)
    {
      GEN v = isprincipalfact(bnf, NULL,Sperm,gel(H,i), FLAG);
      v = gel(v,2); if (flag == nf_GEN) v = nf_to_scalar_or_alg(nf, v);
      gel(sunit,i) = v;
    }
    for (j=1; j<lB; j++,i++)
    {
      GEN v = isprincipalfact(bnf, gel(Sperm,i),Sperm,gel(B,j),FLAG);
      v = gel(v,2); if (flag == nf_GEN) v = nf_to_scalar_or_alg(nf, v);
      gel(sunit,i) = v;
   }
    H = ZM_inv(H,&den);
    A = shallowconcat(H, ZM_neg(ZM_mul(H,B))); /* top part of inverse * den */
    /* HNF in split form perm + (H B) [0 Id missing] */
    gel(res,1) = sunit;
    gel(res,2) = mkvec3(perm,A,den);
  }

  /* S-regulator */
  sreg = mpmul(sreg,card);
  for (i=1; i<ls; i++)
  {
    GEN p = pr_get_p( gel(S,i) );
    sreg = mpmul(sreg, logr_abs(itor(p,prec)));
  }
  gel(res,4) = sreg;
  return gerepilecopy(av,res);
}
GEN
bnfsunit(GEN bnf,GEN S,long prec) { return bnfsunit0(bnf,S,nf_GEN,prec); }

static GEN
make_unit(GEN nf, GEN bnfS, GEN *px)
{
  long lB, cH, i, ls;
  GEN den, gen, S, v, p1, xp, xb, N, N0, HB, perm;

  if (gequal0(*px)) return NULL;
  S = gel(bnfS,6); ls = lg(S);
  if (ls==1) return cgetg(1, t_COL);

  xb = nf_to_scalar_or_basis(nf,*px);
  switch(typ(xb))
  {
    case t_INT:  N = xb; break;
    case t_FRAC: N = mulii(gel(xb,1),gel(xb,2)); break;
    default: { GEN d = Q_denom(xb); N = mulii(idealnorm(nf,gmul(*px,d)), d); }
  } /* relevant primes divide N */
  if (is_pm1(N)) return zerocol(ls -1);

  p1 = gel(bnfS,2);
  perm = gel(p1,1);
  HB   = gel(p1,2);
  den  = gel(p1,3);
  cH = nbrows(HB);
  lB = lg(HB) - cH;
  v = zero_zv(ls-1);
  N0 = N;
  for (i=1; i<ls; i++)
  {
    GEN P = gel(S,i), p = pr_get_p(P);
    if (dvdii(N, p))
    {
      v[i] = nfval(nf,xb,P);
      (void)Z_pvalrem(N0, p, &N0);
    }
  }
  if (!is_pm1(N0)) return NULL;
  /* here, x = S v */
  p1 = vecsmallpermute(v, perm);
  v = ZM_zc_mul(HB, p1);
  for (i=1; i<=cH; i++)
  {
    GEN r, w = dvmdii(gel(v,i), den, &r);
    if (r != gen_0) return NULL;
    gel(v,i) = w;
  }
  p1 += cH; p1[0] = evaltyp(t_VECSMALL) | evallg(lB);
  v = shallowconcat(v, zc_to_ZC(p1)); /* append bottom of p1 (= [0 Id] part) */

  gen = gel(bnfS,1);
  xp = trivial_fact();
  for (i=1; i<ls; i++)
  {
    GEN e = gel(v,i);
    if (!signe(e)) continue;
    xp = famat_mulpow_shallow(xp, gel(gen,i), negi(e));
  }
  if (lgcols(xp) != 1) *px = famat_mulpow_shallow(xp, xb, gen_1);
  return v;
}

/* Analog to bnfisunit, for S-units. Let v the result
 * If x not an S-unit, v = []~, else
 * x = \prod_{i=0}^r e_i^v[i] * prod{i=r+1}^{r+s} s_i^v[i]
 * where the e_i are the field units (cf bnfisunit), and the s_i are
 * the S-units computed by bnfsunit (in the same order) */
GEN
bnfissunit(GEN bnf,GEN bnfS,GEN x)
{
  pari_sp av = avma;
  GEN v, w, nf;

  bnf = checkbnf(bnf);
  nf = bnf_get_nf(bnf);
  if (typ(bnfS)!=t_VEC || lg(bnfS)!=7) pari_err_TYPE("bnfissunit",bnfS);
  x = nf_to_scalar_or_alg(nf,x);
  v = NULL;
  if ( (w = make_unit(nf, bnfS, &x)) ) v = bnfisunit(bnf, x);
  if (!v || lg(v) == 1) { avma = av; return cgetg(1,t_COL); }
  return gerepileupto(av, gconcat(v, w));
}

static void
p_append(GEN p, hashtable *H, hashtable *H2)
{
  ulong h = H->hash(p);
  hashentry *e = hash_search2(H, (void*)p, h);
  if (!e)
  {
    hash_insert2(H, (void*)p, NULL, h);
    if (H2) hash_insert2(H2, (void*)p, NULL, h);
  }
}

/* N a t_INT */
static void
Zfa_append(GEN N, hashtable *H, hashtable *H2)
{
  if (!is_pm1(N))
  {
    GEN v = gel(absZ_factor(N),1);
    long i, l = lg(v);
    for (i=1; i<l; i++) p_append(gel(v,i), H, H2);
  }
}
/* N a t_INT or t_FRAC or ideal in HNF*/
static void
fa_append(GEN N, hashtable *H, hashtable *H2)
{
  switch(typ(N))
  {
    case t_INT:
      Zfa_append(N,H,H2);
      break;
    case t_FRAC:
      Zfa_append(gel(N,1),H,H2);
      Zfa_append(gel(N,2),H,H2);
      break;
    default: /*t_MAT*/
      Zfa_append(gcoeff(N,1,1),H,H2);
      break;
  }
}

/* apply lift(rnfeltup) to all coeffs, without rnf structure */
static GEN
nfX_eltup(GEN nf, GEN rnfeq, GEN x)
{
  long i, l;
  GEN y = cgetg_copy(x, &l), zknf = nf_nfzk(nf, rnfeq);
  for (i=2; i<l; i++) gel(y,i) = nfeltup(nf, gel(x,i), zknf);
  y[1] = x[1]; return y;
}

static hashtable *
hash_create_INT(ulong s)
{ return hash_create(s, (ulong(*)(void*))&hash_GEN,
                        (int(*)(void*,void*))&equalii, 1); }
GEN
rnfisnorminit(GEN T, GEN relpol, int galois)
{
  pari_sp av = avma;
  long i, l, drel;
  GEN S, gen, cyc, bnf, nf, nfabs, rnfeq, bnfabs, k, polabs;
  GEN y = cgetg(9, t_VEC);
  hashtable *H = hash_create_INT(100UL);

  if (galois < 0 || galois > 2) pari_err_FLAG("rnfisnorminit");
  T = get_bnfpol(T, &bnf, &nf);
  if (!bnf) bnf = Buchall(nf? nf: T, nf_FORCE, DEFAULTPREC);
  if (!nf) nf = bnf_get_nf(bnf);

  relpol = get_bnfpol(relpol, &bnfabs, &nfabs);
  if (!gequal1(leading_coeff(relpol))) pari_err_IMPL("non monic relative equation");
  drel = degpol(relpol);
  if (drel <= 2) galois = 1;

  relpol = RgX_nffix("rnfisnorminit", T, relpol, 1);
  if (nf_get_degree(nf) == 1) /* over Q */
    rnfeq = mkvec5(relpol,gen_0,gen_0,T,relpol);
  else if (galois == 2) /* needs eltup+abstorel */
    rnfeq = nf_rnfeq(nf, relpol);
  else /* needs abstorel */
    rnfeq = nf_rnfeqsimple(nf, relpol);
  polabs = gel(rnfeq,1);
  k = gel(rnfeq,3);
  if (!bnfabs || !gequal0(k))
    bnfabs = Buchall(polabs, nf_FORCE, nf_get_prec(nf));
  if (!nfabs) nfabs = bnf_get_nf(bnfabs);

  if (galois == 2)
  {
    GEN P = polabs==relpol? leafcopy(relpol): nfX_eltup(nf, rnfeq, relpol);
    setvarn(P, fetch_var_higher());
    galois = !!nfroots_if_split(&nfabs, P);
    (void)delete_var();
  }

  cyc = bnf_get_cyc(bnfabs);
  gen = bnf_get_gen(bnfabs); l = lg(cyc);
  for(i=1; i<l; i++)
  {
    GEN g = gel(gen,i);
    if (ugcdiu(gel(cyc,i), drel) == 1) break;
    Zfa_append(gcoeff(g,1,1), H, NULL);
  }
  if (!galois)
  {
    GEN Ndiscrel = diviiexact(nf_get_disc(nfabs), powiu(nf_get_disc(nf), drel));
    Zfa_append(Ndiscrel, H, NULL);
  }
  S = hash_keys(H); settyp(S,t_VEC);
  gel(y,1) = bnf;
  gel(y,2) = bnfabs;
  gel(y,3) = relpol;
  gel(y,4) = rnfeq;
  gel(y,5) = S;
  gel(y,6) = nf_pV_to_prV(nf, S);
  gel(y,7) = nf_pV_to_prV(nfabs, S);
  gel(y,8) = stoi(galois); return gerepilecopy(av, y);
}

/* T as output by rnfisnorminit
 * if flag=0 assume extension is Galois (==> answer is unconditional)
 * if flag>0 add to S all primes dividing p <= flag
 * if flag<0 add to S all primes dividing abs(flag)

 * answer is a vector v = [a,b] such that
 * x = N(a)*b and x is a norm iff b = 1  [assuming S large enough] */
GEN
rnfisnorm(GEN T, GEN x, long flag)
{
  pari_sp av = avma;
  GEN bnf, rel, relpol, rnfeq, nfpol;
  GEN nf, aux, H, U, Y, M, A, bnfS, sunitrel, futu, S, S1, S2, Sx;
  long L, i, drel, itu;
  hashtable *H0, *H2;
  if (typ(T) != t_VEC || lg(T) != 9)
    pari_err_TYPE("rnfisnorm [please apply rnfisnorminit()]", T);
  bnf = gel(T,1);
  rel = gel(T,2);
  bnf = checkbnf(bnf);
  rel = checkbnf(rel);
  nf = bnf_get_nf(bnf);
  x = nf_to_scalar_or_alg(nf,x);
  if (gequal0(x)) { avma = av; return mkvec2(gen_0, gen_1); }
  if (gequal1(x)) { avma = av; return mkvec2(gen_1, gen_1); }
  relpol = gel(T,3);
  rnfeq = gel(T,4);
  drel = degpol(relpol);
  if (gequalm1(x) && odd(drel)) { avma = av; return mkvec2(gen_m1, gen_1); }

  /* build set T of ideals involved in the solutions */
  nfpol = nf_get_pol(nf);
  S = gel(T,5);
  H0 = hash_create_INT(100UL);
  H2 = hash_create_INT(100UL);
  L = lg(S);
  for (i = 1; i < L; i++) p_append(gel(S,i),H0,NULL);
  S1 = gel(T,6);
  S2 = gel(T,7);
  if (flag && !gequal0(gel(T,8)))
    pari_warn(warner,"useless flag in rnfisnorm: the extension is Galois");
  if (flag > 0)
  {
    forprime_t T;
    ulong p;
    u_forprime_init(&T, 2, flag);
    while ((p = u_forprime_next(&T))) p_append(utoipos(p), H0,H2);
  }
  else if (flag < 0)
    Zfa_append(utoipos(-flag),H0,H2);
  /* overkill: prime ideals dividing x would be enough */
  A = idealnumden(nf, x);
  fa_append(gel(A,1), H0,H2);
  fa_append(gel(A,2), H0,H2);
  Sx = hash_keys(H2); L = lg(Sx);
  if (L > 1)
  { /* new primes */
    settyp(Sx, t_VEC);
    S1 = shallowconcat(S1, nf_pV_to_prV(nf, Sx));
    S2 = shallowconcat(S2, nf_pV_to_prV(rel, Sx));
  }

  /* computation on T-units */
  futu = shallowconcat(bnf_get_fu(rel), bnf_get_tuU(rel));
  bnfS = bnfsunit(bnf,S1,LOWDEFAULTPREC);
  sunitrel = shallowconcat(futu, gel(bnfsunit(rel,S2,LOWDEFAULTPREC), 1));

  A = lift_shallow(bnfissunit(bnf,bnfS,x));
  L = lg(sunitrel);
  itu = lg(nf_get_roots(nf))-1; /* index of torsion unit in bnfsunit(nf) output */
  M = cgetg(L+1,t_MAT);
  for (i=1; i<L; i++)
  {
    GEN u = eltabstorel(rnfeq, gel(sunitrel,i));
    gel(sunitrel,i) = u;
    u = bnfissunit(bnf,bnfS, gnorm(u));
    if (lg(u) == 1) pari_err_BUG("rnfisnorm");
    gel(u,itu) = lift_shallow(gel(u,itu)); /* lift root of 1 part */
    gel(M,i) = u;
  }
  aux = zerocol(lg(A)-1); gel(aux,itu) = utoipos( bnf_get_tuN(rel) );
  gel(M,L) = aux;
  H = ZM_hnfall(M, &U, 2);
  Y = RgM_RgC_mul(U, inverseimage(H,A));
  /* Y: sols of MY = A over Q */
  setlg(Y, L);
  aux = factorback2(sunitrel, gfloor(Y));
  x = mkpolmod(x,nfpol);
  if (!gequal1(aux)) x = gdiv(x, gnorm(aux));
  x = lift_if_rational(x);
  if (typ(aux) == t_POLMOD && degpol(nfpol) == 1)
    gel(aux,2) = lift_if_rational(gel(aux,2));
  return gerepilecopy(av, mkvec2(aux, x));
}

GEN
bnfisnorm(GEN bnf, GEN x, long flag)
{
  pari_sp av = avma;
  GEN T = rnfisnorminit(pol_x(fetch_var()), bnf, flag == 0? 1: 2);
  GEN r = rnfisnorm(T, x, flag == 1? 0: flag);
  (void)delete_var();
  return gerepileupto(av,r);
}
