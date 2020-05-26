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

/********************************************************************/
/**                                                                **/
/**             THUE EQUATION SOLVER (G. Hanrot)                   **/
/**                                                                **/
/********************************************************************/
/* In all the forthcoming remarks, "paper" designs the paper "Thue Equations of
 * High Degree", by Yu. Bilu and G. Hanrot, J. Number Theory (1996). The
 * numbering of the constants corresponds to Hanrot's thesis rather than to the
 * paper. See also
 * "Solving Thue equations without the full unit group", Math. Comp. (2000) */

/* Check whether tnf is a valid structure */
static int
checktnf(GEN tnf)
{
  long l = lg(tnf);
  GEN v;
  if (typ(tnf)!=t_VEC || (l!=8 && l!=4)) return 0;
  v = gel(tnf,1);
  if (typ(v) != t_VEC || lg(v) != 4) return 0;
  if (l == 4) return 1; /* s=0 */

  (void)checkbnf(gel(tnf,2));
  return (typ(gel(tnf,3)) == t_COL
       && typ(gel(tnf,4)) == t_COL
       && typ(gel(tnf,5)) == t_MAT
       && typ(gel(tnf,6)) == t_MAT
       && typ(gel(tnf,7)) == t_VEC);
}

/* Compensates rounding errors for computation/display of the constants.
 * Round up if dir > 0, down otherwise */
static GEN
myround(GEN x, long dir)
{
  GEN eps = powis(stoi(dir > 0? 10: -10), -10);
  return gmul(x, gadd(gen_1, eps));
}

/* v a t_VEC/t_VEC */
static GEN
vecmax_shallow(GEN v) { return gel(v, vecindexmax(v)); }

static GEN
tnf_get_roots(GEN poly, long prec, long S, long T)
{
  GEN R0 = QX_complex_roots(poly, prec), R = cgetg(lg(R0), t_COL);
  long k;

  for (k=1; k<=S; k++) gel(R,k) = gel(R0,k);
  /* swap roots to get the usual order */
  for (k=1; k<=T; k++)
  {
    gel(R,k+S)  = gel(R0,2*k+S-1);
    gel(R,k+S+T)= gel(R0,2*k+S);
  }
  return R;
}

/* Computation of the logarithmic height of x (given by embeddings) */
static GEN
LogHeight(GEN x, long prec)
{
  pari_sp av = avma;
  long i, n = lg(x)-1;
  GEN LH = gen_1;
  for (i=1; i<=n; i++)
  {
    GEN t = gabs(gel(x,i), prec);
    if (gcmpgs(t,1) > 0) LH = gmul(LH, t);
  }
  return gerepileupto(av, gdivgs(glog(LH,prec), n));
}

/* |x|^(1/n), x t_INT */
static GEN
absisqrtn(GEN x, long n, long prec)
{ GEN r = itor(x,prec); setabssign(r); return sqrtnr(r, n); }

static GEN
get_emb(GEN x, GEN r)
{
  long l = lg(r), i;
  GEN y;

  if (typ(x) == t_INT) return const_col(l-1, x);
  y = cgetg(l, t_COL);
  for (i=1; i<l; i++)
  {
    GEN e = poleval(x, gel(r,i));
    if (gequal0(e) || (typ(e) != t_INT && precision(e) <= LOWDEFAULTPREC ))
      return NULL;
    gel(y,i) = e;
  }
  return y;
}

/* Computation of the conjugates (sigma_i(v_j)), and log. heights, of elts of v */
static GEN
Conj_LH(GEN v, GEN *H, GEN r, long prec)
{
  long j, l = lg(v);
  GEN e, M = cgetg(l,t_MAT);

  (*H) = cgetg(l,t_COL);
  for (j = 1; j < l; j++)
  {
    if (! (e = get_emb(gel(v,j), r)) ) return NULL; /* FAIL */
    gel(M,j) = e;
    gel(*H,j) = LogHeight(e, prec);
  }
  return M;
}

/* Computation of M, its inverse A and precision check (see paper) */
static GEN
T_A_Matrices(GEN MatFU, long r, GEN *eps5, long prec)
{
  GEN A, p1, m1, IntM, nia, eps3, eps2;
  long e = prec2nbits(prec);

  m1 = matslice(MatFU, 1,r, 1,r); /* minor order r */
  m1 = glog(gabs(m1, prec), prec); /* HIGH accuracy */
  A = RgM_inv(m1); if (!A) pari_err_PREC("thue");
  IntM = RgM_Rg_add(RgM_mul(A,m1), gen_m1);
  IntM = gabs(IntM, 0);

  eps2 = gadd(vecmax(IntM), real2n(-e, LOWDEFAULTPREC)); /* t_REAL */
  nia = vecmax(gabs(A, 0));

  /* Check for the precision in matrix inversion. See paper, Lemma 2.4.2. */
  p1 = addrr(mulsr(r, gmul2n(nia, e)), eps2); /* t_REAL */
  if (expo(p1) < -2*r) pari_err_PREC("thue");

  p1 = addrr(mulsr(r, gmul2n(nia,-e)), eps2);
  eps3 = mulrr(mulsr(2*r*r,nia), p1);
  if (!signe(eps3))
    eps3 = real2n(expo(eps3), LOWDEFAULTPREC);
  else
    eps3 = myround(eps3, 1);

  if (DEBUGLEVEL>1) err_printf("epsilon_3 -> %Ps\n",eps3);
  *eps5 = mulur(r, eps3); return A;
}

/* find a few large primes such that p Z_K = P1 P2 P3 Q, whith f(Pi/p) = 1
 * From x - \alpha y = \prod u_i^b_i we will deduce 3 equations in F_p
 * in check_prinfo. Eliminating x,y we get a stringent condition on (b_i). */
static GEN
get_prime_info(GEN bnf)
{
  long n = 1, e = gexpo(bnf_get_reg(bnf)), nbp = e < 20? 1: 2;
  GEN L = cgetg(nbp+1, t_VEC), nf = checknf(bnf), fu = bnf_get_fu(bnf);
  GEN X = pol_x(nf_get_varn(nf));
  ulong p;
  for(p = 2147483659UL; n <= nbp; p = unextprime(p+1))
  {
    GEN PR, A, U, LP = idealprimedec_limit_f(bnf, utoipos(p), 1);
    long i;
    if (lg(LP) < 4) continue;
    A = cgetg(5, t_VECSMALL);
    U = cgetg(4, t_VEC);
    PR = cgetg(4, t_VEC);
    for (i = 1; i <= 3; i++)
    {
      GEN modpr = zkmodprinit(nf, gel(LP,i));
      GEN a = nf_to_Fq(nf, X, modpr);
      GEN u = nfV_to_FqV(fu, nf, modpr);
      A[i] = itou(a);
      gel(U,i) = ZV_to_Flv(u,p);
      gel(PR,i) = modpr;
    }
    A[4] = p;
    gel(L,n++) = mkvec3(A,U,PR);
  }
  return L;
}

/* Performs basic computations concerning the equation.
 * Returns a "tnf" structure containing
 *  1) the polynomial
 *  2) the bnf (used to solve the norm equation)
 *  3) roots, with presumably enough precision
 *  4) The logarithmic heights of units
 *  5) The matrix of conjugates of units
 *  6) its inverse
 *  7) a few technical constants */
static GEN
inithue(GEN P, GEN bnf, long flag, long prec)
{
  GEN MatFU, x0, tnf, tmp, gpmin, dP, csts, ALH, eps5, ro, c1, c2, Ind = gen_1;
  long k,j, n = degpol(P);
  long s,t, prec_roots;

  if (!bnf)
  {
    bnf = Buchall(P, nf_FORCE, maxss(prec, DEFAULTPREC));
    if (flag) (void)bnfcertify(bnf);
    else
      Ind = floorr(mulru(bnf_get_reg(bnf), 5));
  }

  nf_get_sign(bnf_get_nf(bnf), &s, &t);
  prec_roots = prec;
  for(;;)
  {
    ro = tnf_get_roots(P, prec_roots, s, t);
    MatFU = Conj_LH(bnf_get_fu(bnf), &ALH, ro, prec);
    if (MatFU) break;
    prec_roots = precdbl(prec_roots);
    if (DEBUGLEVEL>1) pari_warn(warnprec, "inithue", prec_roots);
  }

  dP = ZX_deriv(P);
  c1 = NULL; /* min |P'(r_i)|, i <= s */
  for (k=1; k<=s; k++)
  {
    tmp = gabs(poleval(dP,gel(ro,k)),prec);
    if (!c1 || gcmp(tmp,c1) < 0) c1 = tmp;
  }
  c1 = gdiv(int2n(n-1), c1);
  c1 = gprec_w(myround(c1, 1), DEFAULTPREC);

  c2 = NULL; /* max |r_i - r_j|, i!=j */
  for (k=1; k<=n; k++)
    for (j=k+1; j<=n; j++)
    {
      tmp = gabs(gsub(gel(ro,j),gel(ro,k)), prec);
      if (!c2 || gcmp(c2,tmp) > 0) c2 = tmp;
    }
  c2 = gprec_w(myround(c2, -1), DEFAULTPREC);

  if (t==0)
    x0 = real_1(DEFAULTPREC);
  else
  {
    gpmin = NULL; /* min |P'(r_i)|, i > s */
    for (k=1; k<=t; k++)
    {
      tmp = gabs(poleval(dP,gel(ro,s+k)), prec);
      if (!gpmin || gcmp(tmp,gpmin) < 0) gpmin = tmp;
    }
    gpmin = gprec_w(gpmin, DEFAULTPREC);

    /* Compute x0. See paper, Prop. 2.2.1 */
    x0 = gmul(gpmin, vecmax_shallow(gabs(imag_i(ro), prec)));
    x0 = sqrtnr(gdiv(int2n(n-1), x0), n);
  }
  if (DEBUGLEVEL>1)
    err_printf("c1 = %Ps\nc2 = %Ps\nIndice <= %Ps\n", c1, c2, Ind);

  ALH = gmul2n(ALH, 1);
  tnf = cgetg(8,t_VEC); csts = cgetg(9,t_VEC);
  gel(tnf,1) = P;
  gel(tnf,2) = bnf;
  gel(tnf,3) = ro;
  gel(tnf,4) = ALH;
  gel(tnf,5) = MatFU;
  gel(tnf,6) = T_A_Matrices(MatFU, s+t-1, &eps5, prec);
  gel(tnf,7) = csts;
  gel(csts,1) = c1; gel(csts,2) = c2;   gel(csts,3) = LogHeight(ro, prec);
  gel(csts,4) = x0; gel(csts,5) = eps5; gel(csts,6) = utoipos(prec);
  gel(csts,7) = Ind;
  gel(csts,8) = get_prime_info(bnf);
  return tnf;
}

typedef struct {
  GEN c10, c11, c13, c15, c91, bak, NE, Ind, hal, MatFU, divro, Hmu;
  GEN delta, lambda, inverrdelta, ro, Pi, Pi2;
  long r, iroot, deg;
} baker_s;

static void
other_roots(long iroot, long *i1, long *i2)
{
  switch (iroot) {
    case 1: *i1=2; *i2=3; break;
    case 2: *i1=1; *i2=3; break;
   default: *i1=1; *i2=2; break;
  }
}
/* low precision */
static GEN abslog(GEN x) { return gabs(glog(gtofp(x,DEFAULTPREC),0), 0); }

/* Compute Baker's bound c9 and B_0, the bound for the b_i's. See Thm 2.3.1 */
static GEN
Baker(baker_s *BS)
{
  GEN tmp, B0, hb0, c9, Indc11;
  long i1, i2;

  other_roots(BS->iroot, &i1,&i2);
  /* Compute a bound for the h_0 */
  hb0 = gadd(gmul2n(BS->hal,2), gmul2n(gadd(BS->Hmu,mplog2(DEFAULTPREC)), 1));
  tmp = gmul(BS->divro, gdiv(gel(BS->NE,i1), gel(BS->NE,i2)));
  tmp = gmax_shallow(gen_1, abslog(tmp));
  hb0 = gmax_shallow(hb0, gdiv(tmp, BS->bak));
  c9 = gmul(BS->c91,hb0);
  c9 = gprec_w(myround(c9, 1), DEFAULTPREC);
  Indc11 = rtor(mulir(BS->Ind,BS->c11), DEFAULTPREC);
  /* Compute B0 according to Lemma 2.3.3 */
  B0 = mulir(shifti(BS->Ind,1),
             divrr(addrr(mulrr(c9,mplog(divrr(mulir(BS->Ind, c9),BS->c10))),
                         mplog(Indc11)), BS->c10));
  B0 = gmax_shallow(B0, dbltor(2.71828183));
  B0 = gmax_shallow(B0, mulrr(divir(BS->Ind, BS->c10),
                              mplog(divrr(Indc11, BS->Pi2))));
  if (DEBUGLEVEL>1) {
    err_printf("  B0  = %Ps\n",B0);
    err_printf("  Baker = %Ps\n",c9);
  }
  return B0;
}

/* || x d ||, x t_REAL, d t_INT */
static GEN
errnum(GEN x, GEN d)
{
  GEN dx = mulir(d, x), D = subri(dx, roundr(dx));
  setabssign(D); return D;
}

/* Try to reduce the bound through continued fractions; see paper. */
static int
CF_1stPass(GEN *B0, GEN kappa, baker_s *BS)
{
  GEN a, b, q, ql, qd, l0, denbound = mulri(*B0, kappa);

  if (cmprr(mulrr(dbltor(0.1),sqrr(denbound)), BS->inverrdelta) > 0)
    return -1;

  q = denom_i( bestappr(BS->delta, denbound) );
  qd = errnum(BS->delta, q);
  ql = errnum(BS->lambda,q);

  l0 = subrr(ql, addrr(mulrr(qd, *B0), divri(dbltor(0.1),kappa)));
  if (signe(l0) <= 0) return 0;

  if (BS->r > 1) {
    a = BS->c15; b = BS->c13;
  }
  else {
    a = BS->c11; b = BS->c10;
    l0 = mulrr(l0, Pi2n(1, DEFAULTPREC));
  }
  *B0 = divrr(mplog(divrr(mulir(q,a), l0)), b);
  if (DEBUGLEVEL>1) err_printf("    B0 -> %Ps\n",*B0);
  return 1;
}

static void
get_B0Bx(baker_s *BS, GEN l0, GEN *B0, GEN *Bx)
{
  GEN t = divrr(mulir(BS->Ind, BS->c15), l0);
  *B0 = divrr(mulir(BS->Ind, mplog(t)), BS->c13);
  *Bx = sqrtnr(shiftr(t,1), BS->deg);
}

static int
LLL_1stPass(GEN *pB0, GEN kappa, baker_s *BS, GEN *pBx)
{
  GEN B0 = *pB0, Bx = *pBx, lllmat, C, l0, l1, triv;
  long e;

  C = grndtoi(mulir(mulii(BS->Ind, kappa),
                    gpow(B0, dbltor(2.2), DEFAULTPREC)), &e);

  if (DEBUGLEVEL > 1) err_printf("C (bitsize) : %d\n", expi(C));
  lllmat = matid(3);
  if (cmpri(B0, BS->Ind) > 0)
  {
    gcoeff(lllmat, 1, 1) = grndtoi(divri(B0, BS->Ind), &e);
    triv = shiftr(sqrr(B0), 1);
  }
  else
    triv = addir(sqri(BS->Ind), sqrr(B0));

  gcoeff(lllmat, 3, 1) = grndtoi(negr(mulir(C, BS->lambda)), &e);
  if (e >= 0) return -1;
  gcoeff(lllmat, 3, 2) = grndtoi(negr(mulir(C, BS->delta)), &e);
  if (e >= 0) return -1;
  gcoeff(lllmat, 3, 3) = C;
  lllmat = ZM_lll(lllmat, 0.99, LLL_IM|LLL_INPLACE);

  l0 = gnorml2(gel(lllmat,1));
  l0 = subrr(divir(l0, dbltor(1.8262)), triv); /* delta = 0.99 */
  if (signe(l0) <= 0) return 0;

  l1 = shiftr(addri(shiftr(B0,1), BS->Ind), -1);
  l0 = divri(subrr(sqrtr(l0), l1), C);

  if (signe(l0) <= 0) return 0;

  get_B0Bx(BS, l0, &B0, &Bx);
  if (DEBUGLEVEL>=2)
  {
    err_printf("LLL_First_Pass successful\n");
    err_printf("B0 -> %Ps\n", B0);
    err_printf("x <= %Ps\n", Bx);
  }
  *pB0 = B0; *pBx = Bx; return 1;
}

/* add solution (x,y) if not already known */
static void
add_sol(GEN *pS, GEN x, GEN y)
{ *pS = shallowconcat(*pS, mkvec(mkvec2(x,y))); }
/* z = P(p,q), d = deg P, |z| = |rhs|. Check signs and (possibly)
 * add solutions (p,q), (-p,-q) */
static void
add_pm(GEN *pS, GEN p, GEN q, GEN z, long d, GEN rhs)
{
  if (signe(z) == signe(rhs))
  {
    add_sol(pS, p, q);
    if (!odd(d)) add_sol(pS, negi(p), negi(q));
  }
  else
    if (odd(d))  add_sol(pS, negi(p), negi(q));
}

/* Check whether a potential solution is a true solution. Return 0 if
 * truncation error (increase precision) */
static int
CheckSol(GEN *pS, GEN z1, GEN z2, GEN P, GEN rhs, GEN ro)
{
  GEN x, y, ro1 = gel(ro,1), ro2 = gel(ro,2);
  long e;

  y = grndtoi(real_i(gdiv(gsub(z2,z1), gsub(ro1,ro2))), &e);
  if (e > 0) return 0;
  if (!signe(y)) return 1; /* y = 0 taken care of in SmallSols */
  x = gadd(z1, gmul(ro1, y));
  x = grndtoi(real_i(x), &e);
  if (e > 0) return 0;
  if (e <= -13)
  { /* y != 0 and rhs != 0; check whether P(x,y) = rhs or P(-x,-y) = rhs */
    GEN z = poleval(ZX_rescale(P,y),x);
    if (absequalii(z, rhs)) add_pm(pS, x,y, z, degpol(P), rhs);
  }
  return 1;
}

static const long EXPO1 = 7;
static int
round_to_b(GEN v, long B, long b, GEN Delta2, long i1, GEN L)
{
  long i, l = lg(v);
  if (!b)
  {
    for (i = 1; i < l; i++)
    {
      long c;
      if (i == i1)
        c = 0;
      else
      {
        GEN d = gneg(gel(L,i));
        long e;
        d = grndtoi(d,&e);
        if (e > -EXPO1 || is_bigint(d)) return 0;
        c = itos(d); if (labs(c) > B) return 0;
      }
      v[i] = c;
    }
  }
  else
  {
    for (i = 1; i < l; i++)
    {
      long c;
      if (i == i1)
        c = b;
      else
      {
        GEN d = gsub(gmulgs(gel(Delta2,i), b), gel(L,i));
        long e;
        d = grndtoi(d,&e);
        if (e > -EXPO1 || is_bigint(d)) return 0;
        c = itos(d); if (labs(c) > B) return 0;
      }
      v[i] = c;
    }
  }
  return 1;
}

/* mu \prod U[i]^b[i] */
static ulong
Fl_factorback(ulong mu, GEN U, GEN b, ulong p)
{
  long i, l = lg(U);
  ulong r = mu;
  for (i = 1; i < l; i++)
  {
    long c = b[i];
    ulong u = U[i];
    if (!c) continue;
    if (c < 0) { u = Fl_inv(u,p); c = -c; }
    r = Fl_mul(r, Fl_powu(u,c,p), p);
  }
  return r;
}

/* x - alpha y = \pm mu \prod \mu_i^{b_i}. Reduce mod 3 distinct primes of
 * degree 1 above the same p, and eliminate x,y => drastic conditions on b_i */
static int
check_pr(GEN bi, GEN Lmu, GEN L)
{
  GEN A = gel(L,1), U = gel(L,2);
  ulong a = A[1], b = A[2], c = A[3], p = A[4];
  ulong r = Fl_mul(Fl_sub(c,b,p), Fl_factorback(Lmu[1],gel(U,1),bi, p), p);
  ulong s = Fl_mul(Fl_sub(a,c,p), Fl_factorback(Lmu[2],gel(U,2),bi, p), p);
  ulong t = Fl_mul(Fl_sub(b,a,p), Fl_factorback(Lmu[3],gel(U,3),bi, p), p);
  return Fl_add(Fl_add(r,s,p),t,p) == 0;
}
static int
check_prinfo(GEN b, GEN Lmu, GEN prinfo)
{
  long i;
  for (i = 1; i < lg(prinfo); i++)
    if (!check_pr(b, gel(Lmu,i), gel(prinfo,i))) return 0;
  return 1;
}
/* For each possible value of b_i1, compute the b_i's
* and 2 conjugates of z = x - alpha y. Then check. */
static int
TrySol(GEN *pS, GEN B0, long i1, GEN Delta2, GEN Lambda, GEN ro,
       GEN Lmu, GEN NE, GEN MatFU, GEN prinfo, GEN P, GEN rhs)
{
  long bi1, i, B = itos(gceil(B0)), l = lg(Delta2);
  GEN b = cgetg(l,t_VECSMALL), L = cgetg(l,t_VEC);

  for (i = 1; i < l; i++)
  {
    if (i == i1)
      gel(L,i) = gen_0;
    else
    {
      GEN delta = gel(Delta2,i);
      gel(L, i) = gsub(gmul(delta,gel(Lambda,i1)), gel(Lambda,i));
    }
  }
  for (bi1 = -B; bi1 <= B; bi1++)
  {
    GEN z1, z2;
    if (!round_to_b(b, B, bi1, Delta2, i1, L)) continue;
    if (!check_prinfo(b, Lmu, prinfo)) continue;
    z1 = gel(NE,1);
    z2 = gel(NE,2);
    for (i = 1; i < l; i++)
    {
      z1 = gmul(z1, gpowgs(gcoeff(MatFU,1,i), b[i]));
      z2 = gmul(z2, gpowgs(gcoeff(MatFU,2,i), b[i]));
    }
    if (!CheckSol(pS, z1,z2,P,rhs,ro)) return 0;
  }
  return 1;
}

/* find q1,q2,q3 st q1 b + q2 c + q3 ~ 0 */
static GEN
GuessQi(GEN b, GEN c, GEN *eps)
{
  const long shift = 65;
  GEN Q, Lat;

  Lat = matid(3);
  gcoeff(Lat,3,1) = ground(gmul2n(b, shift));
  gcoeff(Lat,3,2) = ground(gmul2n(c, shift));
  gcoeff(Lat,3,3) = int2n(shift);

  Q = gel(lllint(Lat),1);
  if (gequal0(gel(Q,2))) return NULL; /* FAIL */

  *eps = mpadd(mpadd(gel(Q,3), mpmul(gel(Q,1),b)), mpmul(gel(Q,2),c));
  *eps = mpabs_shallow(*eps); return Q;
}

/* x a t_REAL */
static GEN
myfloor(GEN x) { return expo(x) > 30 ? ceil_safe(x): floorr(x); }

/* Check for not-so-small solutions. Return a t_REAL or NULL */
static GEN
MiddleSols(GEN *pS, GEN bound, GEN roo, GEN P, GEN rhs, long s, GEN c1)
{
  long j, k, nmax, d;
  GEN bndcf;

  if (expo(bound) < 0) return bound;
  d = degpol(P);
  bndcf = sqrtnr(shiftr(c1,1), d - 2);
  if (cmprr(bound, bndcf) < 0) return bound;
  /* divide by log2((1+sqrt(5))/2)
   * 1 + ==> ceil
   * 2 + ==> continued fraction is normalized if last entry is 1
   * 3 + ==> start at a0, not a1 */
  nmax = 3 + (long)(dbllog2(bound) * 1.44042009041256);
  bound = myfloor(bound);

  for (k = 1; k <= s; k++)
  {
    GEN ro = real_i(gel(roo,k)), t = gboundcf(ro, nmax);
    GEN pm1, qm1, p0, q0;

    pm1 = gen_0; p0 = gen_1;
    qm1 = gen_1; q0 = gen_0;

    for (j = 1; j < lg(t); j++)
    {
      GEN p, q, z, Q, R;
      pari_sp av;
      p = addii(mulii(p0, gel(t,j)), pm1); pm1 = p0; p0 = p;
      q = addii(mulii(q0, gel(t,j)), qm1); qm1 = q0; q0 = q;
      if (cmpii(q, bound) > 0) break;
      if (DEBUGLEVEL >= 2) err_printf("Checking (+/- %Ps, +/- %Ps)\n",p, q);
      av = avma;
      z = poleval(ZX_rescale(P,q), p); /* = P(p/q) q^dep(P) */
      Q = dvmdii(rhs, z, &R);
      if (R != gen_0) { avma = av; continue; }
      setabssign(Q);
      if (Z_ispowerall(Q, d, &Q))
      {
        if (!is_pm1(Q)) { p = mulii(p, Q); q = mulii(q, Q); }
        add_pm(pS, p, q, z, d, rhs);
      }
    }
    if (j == lg(t))
    {
      long prec;
      if (j > nmax) pari_err_BUG("thue [short continued fraction]");
      /* the theoretical value is bit_prec = gexpo(ro)+1+log2(bound) */
      prec = precdbl(precision(ro));
      if (DEBUGLEVEL>1) pari_warn(warnprec,"thue",prec);
      roo = realroots(P, NULL, prec);
      if (lg(roo)-1 != s) pari_err_BUG("thue [realroots]");
      k--;
    }
  }
  return bndcf;
}

static void
check_y_root(GEN *pS, GEN P, GEN Y)
{
  GEN r = nfrootsQ(P);
  long j;
  for (j = 1; j < lg(r); j++)
    if (typ(gel(r,j)) == t_INT) add_sol(pS, gel(r,j), Y);
}

static void
check_y(GEN *pS, GEN P, GEN poly, GEN Y, GEN rhs)
{
  long j, l = lg(poly);
  GEN Yn = Y;
  gel(P, l-1) = gel(poly, l-1);
  for (j = l-2; j >= 2; j--)
  {
    gel(P,j) = mulii(Yn, gel(poly,j));
    if (j > 2) Yn = mulii(Yn, Y);
  }
  gel(P,2) = subii(gel(P,2), rhs); /* P = poly(Y/y)*y^deg(poly) - rhs */
  check_y_root(pS, P, Y);
}

/* Check for solutions under a small bound (see paper) */
static GEN
SmallSols(GEN S, GEN x3, GEN poly, GEN rhs)
{
  pari_sp av = avma;
  GEN X, P, rhs2;
  long j, l = lg(poly), n = degpol(poly);
  ulong y, By;

  x3 = myfloor(x3);

  if (DEBUGLEVEL>1) err_printf("* Checking for small solutions <= %Ps\n", x3);
  if (lgefint(x3) > 3)
    pari_err_OVERFLOW(stack_sprintf("thue (SmallSols): y <= %Ps", x3));
  By = itou(x3);
  /* y = 0 first: solve X^n = rhs */
  if (odd(n))
  {
    if (Z_ispowerall(absi_shallow(rhs), n, &X))
      add_sol(&S, signe(rhs) > 0? X: negi(X), gen_0);
  }
  else if (signe(rhs) > 0 && Z_ispowerall(rhs, n, &X))
  {
    add_sol(&S, X, gen_0);
    add_sol(&S, negi(X), gen_0);
  }
  rhs2 = shifti(rhs,1);
  /* y != 0 */
  P = cgetg(l, t_POL); P[1] = poly[1];
  for (y = 1; y <= By; y++)
  {
    pari_sp av2 = avma;
    long lS = lg(S);
    GEN Y = utoipos(y);
    /* try y */
    check_y(&S, P, poly, Y, rhs);
    /* try -y */
    for (j = l-2; j >= 2; j -= 2) togglesign( gel(P,j) );
    if (j == 0) gel(P,2) = subii(gel(P,2), rhs2);
    check_y_root(&S, P, utoineg(y));
    if (lS == lg(S)) { avma = av2; continue; } /* no solution found */

    if (gc_needed(av,1))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"SmallSols");
      gerepileall(av, 2, &S, &rhs2);
      P = cgetg(l, t_POL); P[1] = poly[1];
    }
  }
  return S;
}

/* Computes [x]! */
static double
fact(double x)
{
  double ft = 1.0;
  x = floor(x); while (x>1) { ft *= x; x--; }
  return ft ;
}

static GEN
RgX_homogenize(GEN P, long v)
{
  GEN Q = leafcopy(P);
  long i, l = lg(P), d = degpol(P);
  for (i = 2; i < l; i++) gel(Q,i) = monomial(gel(Q,i), d--, v);
  return Q;
}

/* Compute all relevant constants needed to solve the equation P(x,y)=a given
 * the solutions of N_{K/Q}(x)=a (see inithue). */
GEN
thueinit(GEN pol, long flag, long prec)
{
  GEN POL, C, L, fa, tnf, bnf = NULL;
  pari_sp av = avma;
  long s, lfa, dpol;

  if (checktnf(pol)) { bnf = checkbnf(gel(pol,2)); pol = gel(pol,1); }
  if (typ(pol)!=t_POL) pari_err_TYPE("thueinit",pol);
  dpol = degpol(pol);
  if (dpol <= 0) pari_err_CONSTPOL("thueinit");
  RgX_check_ZX(pol, "thueinit");
  if (varn(pol)) { pol = leafcopy(pol); setvarn(pol, 0); }

  POL = Q_primitive_part(pol, &C);
  L = gen_1;
  fa = ZX_factor(POL); lfa = lgcols(fa);
  if (lfa > 2 || itos(gcoeff(fa,1,2)) > 1)
  { /* reducible polynomial, no need to reduce to the monic case */
    GEN P, Q, R, g, f = gcoeff(fa,1,1), E = gcoeff(fa,1,2);
    long e = itos(E);
    long vy = fetch_var();
    long va = fetch_var();
    long vb = fetch_var();
    C = C? ginv(C): gen_1;
    if (e != 1)
    {
      if (lfa == 2) {
        tnf = mkvec3(mkvec3(POL,C,L), thueinit(f, flag, prec), E);
        delete_var(); delete_var(); delete_var();
        return gerepilecopy(av, tnf);
      }
      P = gpowgs(f,e);
    }
    else
      P = f;
    g = RgX_div(POL, P);
    P = RgX_Rg_sub(RgX_homogenize(f, vy), pol_x(va));
    Q = RgX_Rg_sub(RgX_homogenize(g, vy), pol_x(vb));
    R = polresultant0(P, Q, -1, 0);
    tnf = mkvec3(mkvec3(POL,C,L), mkvecsmall4(degpol(f), e, va,vb),  R);
    delete_var(); delete_var(); delete_var();
    return gerepilecopy(av, tnf);
  }
  /* POL monic: POL(x) = C pol(x/L), L integer */
  POL = ZX_primitive_to_monic(POL, &L);
  C = gdiv(powiu(L, dpol), gel(pol, dpol+2));
  pol = POL;

  s = ZX_sturm(pol);
  if (s)
  {
    long PREC, n = degpol(pol);
    double d, dr, dn = (double)n;

    if (dpol <= 2) pari_err_DOMAIN("thueinit", "P","=",pol,pol);
    dr = (double)((s+n-2)>>1); /* s+t-1 */
    d = dn*(dn-1)*(dn-2);
    /* Guess precision by approximating Baker's bound. The guess is most of
     * the time not sharp, ie 10 to 30 decimal digits above what is _really_
     * necessary. Note that the limiting step is the reduction. See paper. */
    PREC = nbits2prec((long)((5.83 + (dr+4)*5 + log(fact(dr+3)) + (dr+3)*log(dr+2) +
                     (dr+3)*log(d) + log(log(2*d*(dr+2))) + (dr+1))
                     /10.)*32+32);

    if (flag == 0) PREC = (long)(2.2 * PREC); /* Lazy, to be improved */
    if (PREC < prec) PREC = prec;
    if (DEBUGLEVEL >=2) err_printf("prec = %d\n", PREC);

    for (;;)
    {
      if (( tnf = inithue(pol, bnf, flag, PREC) )) break;
      PREC = precdbl(PREC);
      if (DEBUGLEVEL>1) pari_warn(warnprec,"thueinit",PREC);
      bnf = NULL; avma = av;
    }
  }
  else
  {
    GEN ro, c0;
    long k,l;
    if (!bnf)
    {
      bnf = gen_0;
      if (expi(ZX_disc(pol)) <= 50)
      {
        bnf = Buchall(pol, nf_FORCE, DEFAULTPREC);
        if (flag) (void)bnfcertify(bnf);
      }
    }
    ro = typ(bnf)==t_VEC? nf_get_roots(bnf_get_nf(bnf))
                        : QX_complex_roots(pol, DEFAULTPREC);
    l = lg(ro); c0 = imag_i(gel(ro,1));
    for (k = 2; k < l; k++) c0 = mulrr(c0, imag_i(gel(ro,k)));
    setsigne(c0,1); c0 = invr(c0); tnf = mkvec3(pol, bnf, c0);
  }
  gel(tnf,1) = mkvec3(gel(tnf,1), C, L);
  return gerepilecopy(av,tnf);
}

/* arg(t^2) / 2Pi; arg(t^2) = arg(t/conj(t)) */
static GEN
argsqr(GEN t, GEN Pi)
{
  GEN v, u = divrr(garg(t,0), Pi); /* in -1 < u <= 1 */
  /* reduce mod Z to -1/2 < u <= 1/2 */
  if (signe(u) > 0)
  {
    v = subrs(u,1); /* ]-1,0] */
    if (abscmprr(v,u) < 0) u = v;
  }
  else
  {
    v = addrs(u,1);/* ]0,1] */
    if (abscmprr(v,u) <= 0) u = v;
  }
  return u;
}
/* i1 != i2 */
static void
init_get_B(long i1, long i2, GEN Delta2, GEN Lambda, GEN Deps5, baker_s *BS,
           long prec)
{
  GEN delta, lambda;
  if (BS->r > 1)
  {
    delta = gel(Delta2,i2);
    lambda = gsub(gmul(delta,gel(Lambda,i1)), gel(Lambda,i2));
    if (Deps5) BS->inverrdelta = divrr(Deps5, addsr(1,delta));
  }
  else
  { /* r == 1: i1 = s = t = 1; i2 = 2 */
    GEN fu = gel(BS->MatFU,1), ro = BS->ro, t;

    t = gel(fu,2);
    delta = argsqr(t, BS->Pi);
    if (Deps5) BS->inverrdelta = shiftr(gabs(t,prec), prec2nbits(prec)-1);

    t = gmul(gsub(gel(ro,1), gel(ro,2)), gel(BS->NE,3));
    lambda = argsqr(t, BS->Pi);
  }
  BS->delta = delta;
  BS->lambda = lambda;
}

static GEN
get_B0(long i1, GEN Delta2, GEN Lambda, GEN Deps5, long prec, baker_s *BS)
{
  GEN B0 = Baker(BS);
  long step = 0, i2 = (i1 == 1)? 2: 1;
  for(;;) /* i2 from 1 to r unless r = 1 [then i2 = 2] */
  {
    init_get_B(i1,i2, Delta2,Lambda,Deps5, BS, prec);
    /* Reduce B0 as long as we make progress: newB0 < oldB0 - 0.1 */
    for (;;)
    {
      GEN oldB0 = B0, kappa = utoipos(10);
      long cf;

      for (cf = 0; cf < 10; cf++, kappa = muliu(kappa,10))
      {
        int res = CF_1stPass(&B0, kappa, BS);
        if (res < 0) return NULL; /* prec problem */
        if (res) break;
        if (DEBUGLEVEL>1) err_printf("CF failed. Increasing kappa\n");
      }
      if (!step && cf == 10)
      { /* Semirational or totally rational case */
        GEN Q, ep, q, l0, denbound;

        if (! (Q = GuessQi(BS->delta, BS->lambda, &ep)) ) break;

        denbound = mpadd(B0, absi_shallow(gel(Q,1)));
        q = denom_i( bestappr(BS->delta, denbound) );
        l0 = subrr(errnum(BS->delta, q), ep);
        if (signe(l0) <= 0) break;

        B0 = divrr(mplog(divrr(mulir(gel(Q,2), BS->c15), l0)),  BS->c13);
        if (DEBUGLEVEL>1) err_printf("Semirat. reduction: B0 -> %Ps\n",B0);
      }
      /* if no progress, stop */
      if (gcmp(oldB0, gadd(B0,dbltor(0.1))) <= 0)
        return gmin_shallow(oldB0, B0);
      else step++;
    }
    i2++; if (i2 == i1) i2++;
    if (i2 > BS->r) break;
  }
  pari_err_BUG("thue (totally rational case)");
  return NULL; /* LCOV_EXCL_LINE */
}

static GEN
get_Bx_LLL(long i1, GEN Delta2, GEN Lambda, long prec, baker_s *BS)
{
  GEN B0 = Baker(BS), Bx = NULL;
  long step = 0, i2 = (i1 == 1)? 2: 1;
  for(;;) /* i2 from 1 to r unless r = 1 [then i2 = 2] */
  {
    init_get_B(i1,i2, Delta2,Lambda,NULL, BS, prec);
    if (DEBUGLEVEL>1) err_printf("  Entering LLL...\n");
    /* Reduce B0 as long as we make progress: newB0 < oldB0 - 0.1 */
    for (;;)
    {
      GEN oldBx = Bx, kappa = utoipos(10);
      const long cfMAX = 10;
      long cf;

      for (cf = 0; cf < cfMAX; cf++, kappa = muliu(kappa,10))
      {
        int res = LLL_1stPass(&B0, kappa, BS, &Bx);
        if (res < 0) return NULL;
        if (res) break;
        if (DEBUGLEVEL>1) err_printf("LLL failed. Increasing kappa\n");
      }

      /* FIXME: TO BE COMPLETED */
      if (!step && cf == cfMAX)
      { /* Semirational or totally rational case */
        GEN Q, Q1, Q2, ep, q, l0, denbound;

        if (! (Q = GuessQi(BS->delta, BS->lambda, &ep)) ) break;

        /* Q[2] != 0 */
        Q1 = absi_shallow(gel(Q,1));
        Q2 = absi_shallow(gel(Q,2));
        denbound = gadd(mulri(B0, Q1), mulii(BS->Ind, Q2));
        q = denom_i( bestappr(BS->delta, denbound) );
        l0 = divri(subrr(errnum(BS->delta, q), ep), Q2);
        if (signe(l0) <= 0) break;

        get_B0Bx(BS, l0, &B0, &Bx);
        if (DEBUGLEVEL>1)
          err_printf("Semirat. reduction: B0 -> %Ps x <= %Ps\n",B0, Bx);
      }
      /* if no progress, stop */
      if (oldBx && gcmp(oldBx, Bx) <= 0) return oldBx; else step++;
    }
    i2++; if (i2 == i1) i2++;
    if (i2 > BS->r) break;
  }
  pari_err_BUG("thue (totally rational case)");
  return NULL; /* LCOV_EXCL_LINE */
}

static GEN
LargeSols(GEN P, GEN tnf, GEN rhs, GEN ne)
{
  GEN S = NULL, Delta0, ro, ALH, bnf, nf, MatFU, A, csts, dP, Bx;
  GEN c1,c2,c3,c4,c90,c91,c14, x0, x1, x2, x3, tmp, eps5, prinfo;
  long iroot, ine, n, r, Prec, prec, s,t;
  baker_s BS;
  pari_sp av = avma;

  prec = 0; /*-Wall*/
  bnf = NULL; /*-Wall*/
  iroot = 1;
  ine = 1;

START:
  if (S) /* restart from precision problems */
  {
    S = gerepilecopy(av, S);
    prec = precdbl(prec);
    if (DEBUGLEVEL) pari_warn(warnprec,"thue",prec);
    tnf = inithue(P, bnf, 0, prec);
  }
  else
    S = cgetg(1, t_VEC);
  bnf= gel(tnf,2);
  nf = bnf_get_nf(bnf);
  csts = gel(tnf,7);
  nf_get_sign(nf, &s, &t);
  BS.r = r = s+t-1; n = degpol(P);
  ro     = gel(tnf,3);
  ALH    = gel(tnf,4);
  MatFU  = gel(tnf,5);
  A      = gel(tnf,6);
  c1     = mpmul(absi_shallow(rhs), gel(csts,1));
  c2     = gel(csts,2);
  BS.hal = gel(csts,3);
  x0     = gel(csts,4);
  eps5   = gel(csts,5);
  Prec = itos(gel(csts,6));
  BS.Ind = gel(csts,7);
  BS.MatFU = MatFU;
  BS.bak = muluu(n, (n-1)*(n-2)); /* safe */
  BS.deg = n;
  prinfo = gel(csts,8);

  if (t) x0 = gmul(x0, absisqrtn(rhs, n, Prec));
  tmp = divrr(c1,c2);
  c3 = mulrr(dbltor(1.39), tmp);
  c4 = mulur(n-1, c3);
  c14 = mulrr(c4, vecmax_shallow(RgM_sumcol(gabs(A,DEFAULTPREC))));

  x1 = gmax_shallow(x0, sqrtnr(shiftr(tmp,1),n));
  x2 = gmax_shallow(x1, sqrtnr(mulur(10,c14), n));
  x3 = gmax_shallow(x2, sqrtnr(shiftr(c14, EXPO1+1),n));
  c90 = gmul(shiftr(mulur(18,mppi(DEFAULTPREC)), 5*(4+r)),
                    gmul(gmul(mpfact(r+3), powiu(muliu(BS.bak,r+2), r+3)),
                         glog(muliu(BS.bak,2*(r+2)),DEFAULTPREC)));

  dP = ZX_deriv(P);
  Delta0 = RgM_sumcol(A);

  for (; iroot<=s; iroot++)
  {
    GEN Delta = Delta0, Delta2, D, Deps5, MatNE, Hmu, diffRo, c5, c7, ro0;
    long i1, iroot1, iroot2, k;

    if (iroot <= r) Delta = RgC_add(Delta, RgC_Rg_mul(gel(A,iroot), stoi(-n)));
    D = gabs(Delta,Prec); i1 = vecindexmax(D);
    c5 = gel(D, i1);
    Delta2 = RgC_Rg_div(Delta, gel(Delta, i1));
    c5  = myround(gprec_w(c5,DEFAULTPREC), 1);
    Deps5 = divrr(subrr(c5,eps5), eps5);
    c7  = mulur(r,c5);
    BS.c10 = divur(n,c7);
    BS.c13 = divur(n,c5);
    if (DEBUGLEVEL>1) {
      err_printf("* real root no %ld/%ld\n", iroot,s);
      err_printf("  c10 = %Ps\n",BS.c10);
      err_printf("  c13 = %Ps\n",BS.c13);
    }

    prec = Prec;
    for (;;)
    {
      if (( MatNE = Conj_LH(ne, &Hmu, ro, prec) )) break;
      prec = precdbl(prec);
      if (DEBUGLEVEL>1) pari_warn(warnprec,"thue",prec);
      ro = tnf_get_roots(P, prec, s, t);
    }
    ro0 = gel(ro,iroot);
    BS.ro    = ro;
    BS.iroot = iroot;
    BS.Pi  = mppi(prec);
    BS.Pi2 = Pi2n(1,prec);
    diffRo = cgetg(r+1, t_VEC);
    for (k=1; k<=r; k++)
    {
      GEN z = gel(ro,k);
      z = (k == iroot)? gdiv(rhs, poleval(dP, z)): gsub(ro0, z);
      gel(diffRo,k) = gabs(z, prec);
    }
    other_roots(iroot, &iroot1,&iroot2);
    BS.divro = gdiv(gsub(ro0, gel(ro,iroot2)), gsub(ro0, gel(ro,iroot1)));
    /* Compute h_1....h_r */
    c91 = c90;
    for (k=1; k<=r; k++)
    {
      GEN z = gdiv(gcoeff(MatFU,iroot1,k), gcoeff(MatFU,iroot2,k));
      z = gmax_shallow(gen_1, abslog(z));
      c91 = gmul(c91, gmax_shallow(gel(ALH,k), gdiv(z, BS.bak)));
    }
    BS.c91 = c91;

    for (; ine<lg(ne); ine++)
    {
      pari_sp av2 = avma;
      long lS = lg(S);
      GEN Lambda, B0, c6, c8;
      GEN NE = gel(MatNE,ine), v = cgetg(r+1,t_COL);

      if (DEBUGLEVEL>1) err_printf("  - norm sol. no %ld/%ld\n",ine,lg(ne)-1);
      for (k=1; k<=r; k++)
      {
        GEN z = gdiv(gel(diffRo,k), gabs(gel(NE,k), prec));
        gel(v,k) = glog(z, prec);
      }
      Lambda = RgM_RgC_mul(A,v);

      c6 = addrr(dbltor(0.1), vecmax_shallow(gabs(Lambda,DEFAULTPREC)));
      c6 = myround(c6, 1);
      c8 = addrr(dbltor(1.23), mulur(r,c6));
      BS.c11= mulrr(shiftr(c3,1) , mpexp(divrr(mulur(n,c8),c7)));
      BS.c15= mulrr(shiftr(c14,1), mpexp(divrr(mulur(n,c6),c5)));
      BS.NE = NE;
      BS.Hmu = gel(Hmu,ine);
      if (is_pm1(BS.Ind))
      {
        GEN mu = gel(ne,ine), Lmu = cgetg(lg(prinfo),t_VEC);
        long i, j;

        for (i = 1; i < lg(prinfo); i++)
        {
          GEN v = gel(prinfo,i), PR = gel(v,3), L = cgetg(4, t_VECSMALL);
          for (j = 1; j <= 3; j++) L[j] = itou(nf_to_Fq(nf, mu, gel(PR,j)));
          gel(Lmu, i) = L;
        }
        if (! (B0 = get_B0(i1, Delta2, Lambda, Deps5, prec, &BS)) ||
            !TrySol(&S, B0, i1, Delta2, Lambda, ro, Lmu, NE,MatFU,prinfo,
                    P,rhs))
          goto START;
        if (lg(S) == lS) avma = av2;
      }
      else
      {
        if (! (Bx = get_Bx_LLL(i1, Delta2, Lambda, prec, &BS)) )
           goto START;
        x3 = gerepileupto(av2, gmax_shallow(Bx, x3));
      }
    }
    ine = 1;
  }
  x3 = gmax_shallow(x0, MiddleSols(&S, x3, ro, P, rhs, s, c1));
  return SmallSols(S, x3, P, rhs);
}

/* restrict to solutions (x,y) with L | x, replacing each by (x/L, y) */
static GEN
filter_sol_x(GEN S, GEN L)
{
  long i, k, l;
  if (is_pm1(L)) return S;
  l = lg(S); k = 1;
  for (i = 1; i < l; i++)
  {
    GEN s = gel(S,i), r;
    gel(s,1) = dvmdii(gel(s,1), L, &r);
    if (r == gen_0) gel(S, k++) = s;
  }
  setlg(S, k); return S;
}
static GEN
filter_sol_Z(GEN S)
{
  long i, k = 1, l = lg(S);
  for (i = 1; i < l; i++)
  {
    GEN s = gel(S,i);
    if (RgV_is_ZV(s)) gel(S, k++) = s;
  }
  setlg(S, k); return S;
}

static GEN bnfisintnorm_i(GEN bnf, GEN a, long s, GEN z);
static GEN
tnf_get_Ind(GEN tnf) { return gmael(tnf,7,7); }
static GEN
tnf_get_bnf(GEN tnf) { return gel(tnf,2); }

static void
maybe_warn(GEN bnf, GEN a, GEN Ind)
{
  if (!is_pm1(Ind) && !is_pm1(bnf_get_no(bnf)) && !is_pm1(a))
    pari_warn(warner, "The result returned by 'thue' is conditional on the GRH");
}
/* return solutions of Norm(x) = a mod U(K)^+ */
static GEN
get_ne(GEN bnf, GEN a, GEN Ind)
{
  if (DEBUGLEVEL) maybe_warn(bnf,a,Ind);
  return bnfisintnorm(bnf, a);
}
/* return solutions of |Norm(x)| = |a| mod U(K) */
static GEN
get_neabs(GEN bnf, GEN a, GEN Ind)
{
  if (DEBUGLEVEL) maybe_warn(bnf,a,Ind);
  return bnfisintnormabs(bnf, a);
}

/* Let P(z)=z^2+Bz+C, convert t=u+v*z (mod P) solution of norm equation N(t)=A
 * to [x,y] = [u,-v] form: y^2P(x/y) = A */
static GEN
ne2_to_xy(GEN t)
{
  GEN u,v;
  if (typ(t) != t_POL) { u = t; v = gen_0; }
  else switch(degpol(t))
  {
    case -1: u = v = gen_0; break;
    case 0: u = gel(t,2); v = gen_0; break;
    default: u = gel(t,2); v = gneg(gel(t,3));
  }
  return mkvec2(u, v);
}
static GEN
ne2V_to_xyV(GEN v)
{
  long i, l;
  GEN w = cgetg_copy(v,&l);
  for (i=1; i<l; i++) gel(w,i) = ne2_to_xy(gel(v,i));
  return w;
}

static GEN
sol_0(void) { retmkvec( mkvec2(gen_0,gen_0) ); }
static void
sols_from_R(GEN Rab, GEN *pS, GEN P, GEN POL, GEN rhs)
{
  GEN ry = nfrootsQ(Rab);
  long k, l = lg(ry);
  for (k = 1; k < l; k++)
    if (typ(gel(ry,k)) == t_INT) check_y(pS, P, POL, gel(ry,k), rhs);
}
static GEN
Z_factor_if_easy(GEN rhs)
{
  GEN F, P;
  long l;
  if (expi(rhs) < 150) return Z_factor(rhs);
  F = Z_factor_limit(rhs, 500000);
  P = gel(F,1); l = lg(P);
  return (l == 1 || BPSW_psp(gel(P,l-1)))? F: NULL;
}
/* Given a tnf structure as returned by thueinit, a RHS and
 * optionally the solutions to the norm equation, returns the solutions to
 * the Thue equation F(x,y)=a */
GEN
thue(GEN tnf, GEN rhs, GEN ne)
{
  pari_sp av = avma;
  GEN POL, C, L, x3, S;

  if (typ(tnf) == t_POL) tnf = thueinit(tnf, 0, DEFAULTPREC);
  if (!checktnf(tnf)) pari_err_TYPE("thue [please apply thueinit()]", tnf);
  if (typ(rhs) != t_INT) pari_err_TYPE("thue",rhs);
  if (ne && typ(ne) != t_VEC) pari_err_TYPE("thue",ne);

  /* solve P(x,y) = rhs <=> POL(L x, y) = C rhs, with POL monic in Z[X] */
  POL = gel(tnf,1);
  C = gel(POL,2); rhs = gmul(C, rhs);
  if (typ(rhs) != t_INT) { avma = av; return cgetg(1, t_VEC); }
  if (!signe(rhs))
  {
    GEN v = gel(tnf,2);
    avma = av;
    /* at least 2 irreducible factors, one of which has degree 1 */
    if (typ(v) == t_VECSMALL && v[1] ==1)
      pari_err_DOMAIN("thue","#sols","=",strtoGENstr("oo"),rhs);
    return sol_0();
  }
  L = gel(POL,3);
  POL = gel(POL,1);
  if (lg(tnf) == 8)
  {
    if (!ne) ne = get_ne(tnf_get_bnf(tnf), rhs, tnf_get_Ind(tnf));
    if (lg(ne) == 1) { avma = av; return cgetg(1, t_VEC); }
    S = LargeSols(POL, tnf, rhs, ne);
  }
  else if (typ(gel(tnf,3)) == t_REAL)
  { /* Case s=0. All solutions are "small". */
    GEN bnf = tnf_get_bnf(tnf);
    GEN c0 = gel(tnf,3), F;
    x3 = sqrtnr(mulir(absi_shallow(rhs),c0), degpol(POL));
    x3 = addrr(x3, dbltor(0.1)); /* guard from round-off errors */
    S = cgetg(1,t_VEC);
    if (!ne && typ(bnf) == t_VEC && expo(x3) > 10)
    {
      F = Z_factor_if_easy(rhs);
      if (F) ne = get_ne(bnf, F, gen_1);
    }
    if (ne)
    {
      if (lg(ne) == 1) { avma = av; return cgetg(1,t_VEC); }
      if (degpol(POL) == 2) /* quadratic imaginary */
      {
        GEN u = NULL;
        long w = 2;
        if (typ(bnf) == t_VEC)
        {
          u = bnf_get_tuU(bnf);
          w =  bnf_get_tuN(bnf);
        }
        else
        {
          GEN D = coredisc(ZX_disc(POL));
          if (cmpis(D, -4) >= 0)
          {
            GEN F, T = quadpoly(D);
            w = equalis(D, -4)? 4: 6;
            setvarn(T, fetch_var_higher());
            F = gcoeff(nffactor(POL, T), 1, 1);
            u = gneg(lift_shallow(gel(F,2))); delete_var();
          }
        }
        if (w == 4) /* u = I */
          ne = shallowconcat(ne, RgXQV_RgXQ_mul(ne,u,POL));
        else if (w == 6) /* u = j */
        {
          GEN u2 = RgXQ_sqr(u,POL);
          ne = shallowconcat1(mkvec3(ne, RgXQV_RgXQ_mul(ne,u,POL),
                                         RgXQV_RgXQ_mul(ne,u2,POL)));
        }
        S = ne2V_to_xyV(ne);
        S = filter_sol_Z(S);
        S = shallowconcat(S, RgV_neg(S));
      }
    }
    if (lg(S) == 1) S = SmallSols(S, x3, POL, rhs);
  }
  else if (typ(gel(tnf,3)) == t_INT) /* reducible case, pure power*/
  {
    GEN bnf, ne1 = NULL, ne2 = NULL;
    long e = itos( gel(tnf,3) );
    if (!Z_ispowerall(rhs, e, &rhs)) { avma = av; return cgetg(1, t_VEC); }
    tnf = gel(tnf,2);
    bnf = tnf_get_bnf(tnf);
    ne = get_neabs(bnf, rhs, lg(tnf)==8?tnf_get_Ind(tnf): gen_1);
    ne1= bnfisintnorm_i(bnf,rhs,1,ne);
    S = thue(tnf, rhs, ne1);
    if (!odd(e) && lg(tnf)==8) /* if s=0, norms are positive */
    {
      ne2 = bnfisintnorm_i(bnf,rhs,-1,ne);
      S = shallowconcat(S, thue(tnf, negi(rhs), ne2));
    }
  }
  else /* other reducible cases */
  { /* solve f^e * g = rhs, f irreducible factor of smallest degree */
    GEN P, D, v = gel(tnf, 2), R = gel(tnf, 3);
    long i, l, e = v[2], va = v[3], vb = v[4];
    P = cgetg(lg(POL), t_POL); P[1] = POL[1];
    D = divisors(rhs); l = lg(D);
    S = cgetg(1,t_VEC);
    for (i = 1; i < l; i++)
    {
      GEN Rab, df = gel(D,i), dg = gel(D,l-i); /* df*dg=|rhs| */
      if (e > 1 && !Z_ispowerall(df, e, &df)) continue;
      /* Rab: univariate polynomial in Z[Y], whose roots are the possible y. */
      /* Here and below, Rab != 0 */
      if (signe(rhs) < 0) dg = negi(dg); /* df*dg=rhs */
      Rab = gsubst(gsubst(R, va, df), vb, dg);
      sols_from_R(Rab, &S,P,POL,rhs);
      Rab = gsubst(gsubst(R, va, negi(df)), vb, odd(e)? negi(dg): dg);
      sols_from_R(Rab, &S,P,POL,rhs);
    }
  }
  S = filter_sol_x(S, L);
  S = gen_sort_uniq(S, (void*)lexcmp, cmp_nodata);
  return gerepileupto(av, S);
}

/********************************************************************/
/**                                                                **/
/**                      BNFISINTNORM (K. Belabas)                 **/
/**                                                                **/
/********************************************************************/
struct sol_abs
{
  GEN rel; /* Primes PR[i] above a, expressed on generators of Cl(K) */
  GEN partrel; /* list of vectors, partrel[i] = rel[1..i] * u[1..i] */
  GEN cyc;     /* orders of generators of Cl(K) given in bnf */

  long *f;     /* f[i] = f(PR[i]/p), inertia degree */
  long *n;     /* a = prod p^{ n_p }. n[i]=n_p if PR[i] divides p */
  long *next;  /* index of first P above next p, 0 if p is last */
  long *S;     /* S[i] = n[i] - sum_{ 1<=k<=i } f[k]*u[k] */
  long *u;     /* We want principal ideals I = prod PR[i]^u[i] */
  GEN  normsol;/* lists of copies of the u[] which are solutions */

  long nPR;    /* length(T->rel) = #PR */
  long sindex, smax; /* current index in T->normsol; max. index */
};

/* u[1..i] has been filled. Norm(u) is correct.
 * Check relations in class group then save it. */
static void
test_sol(struct sol_abs *T, long i)
{
  long k, l;
  GEN s;

  if (T->partrel && !ZV_dvd(gel(T->partrel, i),  T->cyc)) return;
  if (T->sindex == T->smax)
  { /* no more room in solution list: enlarge */
    long new_smax = T->smax << 1;
    GEN  new_normsol = new_chunk(new_smax+1);

    for (k=1; k<=T->smax; k++) gel(new_normsol,k) = gel(T->normsol,k);
    T->normsol = new_normsol; T->smax = new_smax;
  }
  gel(T->normsol, ++T->sindex) = s = cgetg_copy(T->u, &l);
  for (k=1; k <= i; k++) s[k] = T->u[k];
  for (   ; k < l;  k++) s[k] = 0;
  if (DEBUGLEVEL>2)
  {
    err_printf("sol = %Ps\n",s);
    if (T->partrel) err_printf("T->partrel = %Ps\n",T->partrel);
    err_flush();
  }
}
/* partrel[i] <-- partrel[i-1] + u[i] * rel[i] */
static void
fix_partrel(struct sol_abs *T, long i)
{
  pari_sp av = avma;
  GEN part1 = gel(T->partrel,i);
  GEN part0 = gel(T->partrel,i-1);
  GEN rel = gel(T->rel, i);
  ulong u = T->u[i];
  long k, l = lg(part1);
  for (k=1; k < l; k++)
    affii(addii(gel(part0,k), muliu(gel(rel,k), u)), gel(part1,k));
  avma = av;
}

/* Recursive loop. Suppose u[1..i] has been filled
 * Find possible solutions u such that, Norm(prod PR[i]^u[i]) = a, taking
 * into account:
 *  1) the relations in the class group if need be.
 *  2) the factorization of a. */
static void
isintnorm_loop(struct sol_abs *T, long i)
{
  if (T->S[i] == 0) /* sum u[i].f[i] = n[i], do another prime */
  {
    long k, next = T->next[i];
    if (next == 0) { test_sol(T, i); return; } /* no primes left */

    /* some primes left */
    if (T->partrel) gaffect(gel(T->partrel,i), gel(T->partrel, next-1));
    for (k=i+1; k < next; k++) T->u[k] = 0;
    i = next-1;
  }
  else if (i == T->next[i]-2 || i == T->nPR-1)
  { /* only one Prime left above prime; change prime, fix u[i+1] */
    long q;
    if (T->S[i] % T->f[i+1]) return;
    q = T->S[i] / T->f[i+1];
    i++; T->u[i] = q;
    if (T->partrel) fix_partrel(T,i);
    if (T->next[i] == 0) { test_sol(T,i); return; }
  }

  i++; T->u[i] = 0;
  if (T->partrel) gaffect(gel(T->partrel,i-1), gel(T->partrel,i));
  if (i == T->next[i-1])
  { /* change prime */
    if (T->next[i] == i+1 || i == T->nPR) /* only one Prime above p */
    {
      T->S[i] = 0;
      T->u[i] = T->n[i] / T->f[i]; /* we already know this is exact */
      if (T->partrel) fix_partrel(T, i);
    }
    else T->S[i] = T->n[i];
  }
  else T->S[i] = T->S[i-1]; /* same prime, different Prime */
  for(;;)
  {
    isintnorm_loop(T, i);
    T->S[i] -= T->f[i]; if (T->S[i] < 0) break;
    T->u[i]++;
    if (T->partrel) {
      pari_sp av = avma;
      gaffect(ZC_add(gel(T->partrel,i), gel(T->rel,i)), gel(T->partrel,i));
      avma = av;
    }
  }
}

static int
get_sol_abs(struct sol_abs *T, GEN bnf, GEN fact, GEN *ptPR)
{
  GEN nf = bnf_get_nf(bnf);
  GEN P = gel(fact,1), E = gel(fact,2), PR;
  long N = nf_get_degree(nf), nP = lg(P)-1, Ngen, max, nPR, i, j;

  max = nP*N; /* upper bound for T->nPR */
  T->f = new_chunk(max+1);
  T->n = new_chunk(max+1);
  T->next = new_chunk(max+1);
  *ptPR = PR = cgetg(max+1, t_VEC); /* length to be fixed later */

  nPR = 0;
  for (i = 1; i <= nP; i++)
  {
    GEN L = idealprimedec(nf, gel(P,i));
    long lL = lg(L), gcd, k, v;
    ulong vn = itou(gel(E,i));

    /* check that gcd_{P | p} f_P  divides  n_p */
    gcd = pr_get_f(gel(L,1));
    for (j=2; gcd > 1 && j < lL; j++) gcd = ugcd(gcd, pr_get_f(gel(L,j)));
    if (gcd > 1 && vn % gcd)
    {
      if (DEBUGLEVEL>2)
      { err_printf("gcd f_P  does not divide n_p\n"); err_flush(); }
      return 0;
    }
    v = (i==nP)? 0: nPR + lL;
    for (k = 1; k < lL; k++)
    {
      GEN pr = gel(L,k);
      gel(PR, ++nPR) = pr;
      T->f[nPR] = pr_get_f(pr) / gcd;
      T->n[nPR] = vn / gcd;
      T->next[nPR] = v;
    }
  }
  T->nPR = nPR;
  setlg(PR, nPR + 1);

  T->u = cgetg(nPR+1, t_VECSMALL);
  T->S = new_chunk(nPR+1);
  T->cyc = bnf_get_cyc(bnf);
  Ngen = lg(T->cyc)-1;
  if (Ngen == 0)
    T->rel = T->partrel = NULL; /* trivial Cl(K), no relations to check */
  else
  {
    int triv = 1;
    T->partrel = new_chunk(nPR+1);
    T->rel = new_chunk(nPR+1);
    for (i=1; i <= nPR; i++)
    {
      GEN c = isprincipal(bnf, gel(PR,i));
      gel(T->rel,i) = c;
      if (triv && !ZV_equal0(c)) triv = 0; /* non trivial relations in Cl(K)*/
    }
    /* triv = 1: all ideals dividing a are principal */
    if (triv) T->rel = T->partrel = NULL;
  }
  if (T->partrel)
  {
    long B = ZV_max_lg(T->cyc) + 3;
    for (i = 0; i <= nPR; i++)
    { /* T->partrel[0] also needs to be initialized */
      GEN c = cgetg(Ngen+1, t_COL); gel(T->partrel,i) = c;
      for (j=1; j<=Ngen; j++)
      {
        GEN z = cgeti(B); gel(c,j) = z;
        z[1] = evalsigne(0)|evallgefint(B);
      }
    }
  }
  T->smax = 511;
  T->normsol = new_chunk(T->smax+1);
  T->S[0] = T->n[1];
  T->next[0] = 1;
  T->sindex = 0;
  isintnorm_loop(T, 0); return 1;
}

/* Look for unit of norm -1. Return 1 if it exists and set *unit, 0 otherwise */
static long
get_unit_1(GEN bnf, GEN *unit)
{
  GEN v, nf = bnf_get_nf(bnf);
  long i, n = nf_get_degree(nf);

  if (DEBUGLEVEL > 2) err_printf("looking for a fundamental unit of norm -1\n");
  if (odd(n)) { *unit = gen_m1; return 1; }
  v = nfsign_units(bnf, NULL, 0);
  for (i = 1; i < lg(v); i++)
    if ( Flv_sum( gel(v,i), 2) ) { *unit = gel(bnf_get_fu(bnf), i); return 1; }
  return 0;
}

GEN
bnfisintnormabs(GEN bnf, GEN a)
{
  struct sol_abs T;
  GEN nf, res, PR, F;
  long i;

  if ((F = check_arith_all(a,"bnfisintnormabs")))
  {
    a = typ(a) == t_VEC? gel(a,1): factorback(F);
    if (signe(a) < 0) F = clean_Z_factor(F);
  }
  bnf = checkbnf(bnf); nf = bnf_get_nf(bnf);
  if (!signe(a)) return mkvec(gen_0);
  if (is_pm1(a)) return mkvec(gen_1);
  if (!F) F = absZ_factor(a);
  if (!get_sol_abs(&T, bnf, F, &PR)) return cgetg(1, t_VEC);
  /* |a| > 1 => T.nPR > 0 */
  res = cgetg(T.sindex+1, t_VEC);
  for (i=1; i<=T.sindex; i++)
  {
    GEN x = vecsmall_to_col( gel(T.normsol,i) );
    x = isprincipalfact(bnf, NULL, PR, x, nf_FORCE | nf_GEN_IF_PRINCIPAL);
    gel(res,i) = nf_to_scalar_or_alg(nf, x); /* x solution, up to sign */
  }
  return res;
}

/* z = bnfisintnormabs(bnf,a), sa = 1 or -1, return bnfisintnorm(bnf,sa*|a|) */
static GEN
bnfisintnorm_i(GEN bnf, GEN a, long sa, GEN z)
{
  GEN nf = checknf(bnf), T = nf_get_pol(nf), f = nf_get_index(nf), unit = NULL;
  GEN Tp, A = signe(a) == sa? a: negi(a);
  long sNx, i, j, N = degpol(T), l = lg(z);
  long norm_1 = 0; /* gcc -Wall */
  ulong p, Ap = 0; /* gcc -Wall */
  forprime_t S;
  if (!signe(a)) return z;
  u_forprime_init(&S,3,ULONG_MAX);
  while((p = u_forprime_next(&S)))
    if (umodiu(f,p)) { Ap = umodiu(A,p); if (Ap) break; }
  Tp = ZX_to_Flx(T,p);
  /* p > 2 doesn't divide A nor Q_denom(z in Z_K)*/

  /* update z in place to get correct signs: multiply by unit of norm -1 if
   * it exists, otherwise delete solution with wrong sign */
  for (i = j = 1; i < l; i++)
  {
    GEN x = gel(z,i);
    int xpol = (typ(x) == t_POL);

    if (xpol)
    {
      GEN dx, y = Q_remove_denom(x,&dx);
      ulong Np = Flx_resultant(Tp, ZX_to_Flx(y,p), p);
      ulong dA = dx? Fl_mul(Ap, Fl_powu(umodiu(dx,p), N, p), p): Ap;
      /* Nx = Res(T,y) / dx^N = A or -A. Check mod p */
      sNx = dA == Np? sa: -sa;
    }
    else
      sNx = gsigne(x) < 0 && odd(N) ? -1 : 1;
    if (sNx != sa)
    {
      if (! unit) norm_1 = get_unit_1(bnf, &unit);
      if (!norm_1)
      {
        if (DEBUGLEVEL > 2) err_printf("%Ps eliminated because of sign\n",x);
        continue;
      }
      if (xpol) x = (unit == gen_m1)? RgX_neg(x): RgXQ_mul(unit,x,T);
      else      x = (unit == gen_m1)? gneg(x): RgX_Rg_mul(unit,x);
    }
    gel(z,j++) = x;
  }
  setlg(z, j); return z;
}
GEN
bnfisintnorm(GEN bnf, GEN a)
{
  pari_sp av = avma;
  GEN ne = bnfisintnormabs(bnf,a);
  switch(typ(a))
  {
    case t_VEC: a = gel(a,1); break;
    case t_MAT: a = factorback(a); break;
  }
  return gerepilecopy(av, bnfisintnorm_i(bnf,a,signe(a), ne));
}
