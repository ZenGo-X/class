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
/**                 LLL Algorithm and close friends                **/
/**                                                                **/
/********************************************************************/
#include "pari.h"
#include "paripriv.h"

/********************************************************************/
/**             QR Factorization via Householder matrices          **/
/********************************************************************/
static int
no_prec_pb(GEN x)
{
  return (typ(x) != t_REAL || realprec(x) > LOWDEFAULTPREC
                           || expo(x) < BITS_IN_LONG/2);
}
/* Find a Householder transformation which, applied to x[k..#x], zeroes
 * x[k+1..#x]; fill L = (mu_{i,j}). Return 0 if precision problem [obtained
 * a 0 vector], 1 otherwise */
static int
FindApplyQ(GEN x, GEN L, GEN B, long k, GEN Q, long prec)
{
  long i, lx = lg(x)-1;
  GEN x2, x1, xd = x + (k-1);

  x1 = gel(xd,1);
  x2 = mpsqr(x1);
  if (k < lx)
  {
    long lv = lx - (k-1) + 1;
    GEN beta, Nx, v = cgetg(lv, t_VEC);
    for (i=2; i<lv; i++) {
      x2 = mpadd(x2, mpsqr(gel(xd,i)));
      gel(v,i) = gel(xd,i);
    }
    if (!signe(x2)) return 0;
    Nx = gsqrt(x2, prec); if (signe(x1) < 0) setsigne(Nx, -1);
    gel(v,1) = mpadd(x1, Nx);

    if (!signe(x1))
      beta = gtofp(x2, prec); /* make sure typ(beta) != t_INT */
    else
      beta = mpadd(x2, mpmul(Nx,x1));
    gel(Q,k) = mkvec2(invr(beta), v);

    togglesign(Nx);
    gcoeff(L,k,k) = Nx;
  }
  else
    gcoeff(L,k,k) = gel(x,k);
  gel(B,k) = x2;
  for (i=1; i<k; i++) gcoeff(L,k,i) = gel(x,i);
  return no_prec_pb(x2);
}

/* apply Householder transformation Q = [beta,v] to r with t_INT/t_REAL
 * coefficients, in place: r -= ((0|v).r * beta) v */
static void
ApplyQ(GEN Q, GEN r)
{
  GEN s, rd, beta = gel(Q,1), v = gel(Q,2);
  long i, l = lg(v), lr = lg(r);

  rd = r + (lr - l);
  s = mpmul(gel(v,1), gel(rd,1));
  for (i=2; i<l; i++) s = mpadd(s, mpmul(gel(v,i) ,gel(rd,i)));
  s = mpmul(beta, s);
  for (i=1; i<l; i++)
    if (signe(gel(v,i))) gel(rd,i) = mpsub(gel(rd,i), mpmul(s, gel(v,i)));
}
/* apply Q[1], ..., Q[j-1] to r */
static GEN
ApplyAllQ(GEN Q, GEN r, long j)
{
  pari_sp av = avma;
  long i;
  r = leafcopy(r);
  for (i=1; i<j; i++) ApplyQ(gel(Q,i), r);
  return gerepilecopy(av, r);
}

/* same, arbitrary coefficients [20% slower for t_REAL at DEFAULTPREC] */
static void
RgC_ApplyQ(GEN Q, GEN r)
{
  GEN s, rd, beta = gel(Q,1), v = gel(Q,2);
  long i, l = lg(v), lr = lg(r);

  rd = r + (lr - l);
  s = gmul(gel(v,1), gel(rd,1));
  for (i=2; i<l; i++) s = gadd(s, gmul(gel(v,i) ,gel(rd,i)));
  s = gmul(beta, s);
  for (i=1; i<l; i++)
    if (signe(gel(v,i))) gel(rd,i) = gsub(gel(rd,i), gmul(s, gel(v,i)));
}
static GEN
RgC_ApplyAllQ(GEN Q, GEN r, long j)
{
  pari_sp av = avma;
  long i;
  r = leafcopy(r);
  for (i=1; i<j; i++) RgC_ApplyQ(gel(Q,i), r);
  return gerepilecopy(av, r);
}

int
RgM_QR_init(GEN x, GEN *pB, GEN *pQ, GEN *pL, long prec)
{
  x = RgM_gtomp(x, prec);
  return QR_init(x, pB, pQ, pL, prec);
}

static void
check_householder(GEN Q)
{
  long i, l = lg(Q);
  if (typ(Q) != t_VEC) pari_err_TYPE("mathouseholder", Q);
  for (i = 1; i < l; i++)
  {
    GEN q = gel(Q,i), v;
    if (typ(q) != t_VEC || lg(q) != 3) pari_err_TYPE("mathouseholder", Q);
    v = gel(q,2);
    if (typ(v) != t_VEC || lg(v)+i-2 != l) pari_err_TYPE("mathouseholder", Q);
  }
}

GEN
mathouseholder(GEN Q, GEN v)
{
  long l = lg(Q);
  check_householder(Q);
  switch(typ(v))
  {
    case t_MAT:
    {
      long lx, i;
      GEN M = cgetg_copy(v, &lx);
      if (lx == 1) return M;
      if (lgcols(v) != l+1) pari_err_TYPE("mathouseholder", v);
      for (i = 1; i < lx; i++) gel(M,i) = RgC_ApplyAllQ(Q, gel(v,i), l);
      return M;
    }
    case t_COL: if (lg(v) == l+1) break;
      /* fall through */
    default: pari_err_TYPE("mathouseholder", v);
  }
  return RgC_ApplyAllQ(Q, v, l);
}

GEN
matqr(GEN x, long flag, long prec)
{
  pari_sp av = avma;
  GEN B, Q, L;
  long n = lg(x)-1;
  if (typ(x) != t_MAT) pari_err_TYPE("matqr",x);
  if (!n)
  {
    if (!flag) retmkvec2(cgetg(1,t_MAT),cgetg(1,t_MAT));
    retmkvec2(cgetg(1,t_VEC),cgetg(1,t_MAT));
  }
  if (n != nbrows(x)) pari_err_DIM("matqr");
  if (!RgM_QR_init(x, &B,&Q,&L, prec)) pari_err_PREC("matqr");
  if (!flag) Q = shallowtrans(mathouseholder(Q, matid(n)));
  return gerepilecopy(av, mkvec2(Q, shallowtrans(L)));
}

/* compute B = | x[k] |^2, Q = Householder transforms and L = mu_{i,j} */
int
QR_init(GEN x, GEN *pB, GEN *pQ, GEN *pL, long prec)
{
  long j, k = lg(x)-1;
  GEN B = cgetg(k+1, t_VEC), Q = cgetg(k, t_VEC), L = zeromatcopy(k,k);
  for (j=1; j<=k; j++)
  {
    GEN r = gel(x,j);
    if (j > 1) r = ApplyAllQ(Q, r, j);
    if (!FindApplyQ(r, L, B, j, Q, prec)) return 0;
  }
  *pB = B; *pQ = Q; *pL = L; return 1;
}
/* x a square t_MAT with t_INT / t_REAL entries and maximal rank. Return
 * qfgaussred(x~*x) */
GEN
gaussred_from_QR(GEN x, long prec)
{
  long j, k = lg(x)-1;
  GEN B, Q, L;
  if (!QR_init(x, &B,&Q,&L, prec)) return NULL;
  for (j=1; j<k; j++)
  {
    GEN m = gel(L,j), invNx = invr(gel(m,j));
    long i;
    gel(m,j) = gel(B,j);
    for (i=j+1; i<=k; i++) gel(m,i) = mpmul(invNx, gel(m,i));
  }
  gcoeff(L,j,j) = gel(B,j);
  return shallowtrans(L);
}
GEN
R_from_QR(GEN x, long prec)
{
  GEN B, Q, L;
  if (!QR_init(x, &B,&Q,&L, prec)) return NULL;
  return shallowtrans(L);
}

/********************************************************************/
/**             QR Factorization via Gram-Schmidt                  **/
/********************************************************************/

/* return Gram-Schmidt orthogonal basis (f) attached to (e), B is the
 * vector of the (f_i . f_i)*/
GEN
RgM_gram_schmidt(GEN e, GEN *ptB)
{
  long i,j,lx = lg(e);
  GEN f = RgM_shallowcopy(e), B, iB;

  B = cgetg(lx, t_VEC);
  iB= cgetg(lx, t_VEC);

  for (i=1;i<lx;i++)
  {
    GEN p1 = NULL;
    pari_sp av = avma;
    for (j=1; j<i; j++)
    {
      GEN mu = gmul(RgV_dotproduct(gel(e,i),gel(f,j)), gel(iB,j));
      GEN p2 = gmul(mu, gel(f,j));
      p1 = p1? gadd(p1,p2): p2;
    }
    p1 = p1? gerepileupto(av, gsub(gel(e,i), p1)): gel(e,i);
    gel(f,i) = p1;
    gel(B,i) = RgV_dotsquare(gel(f,i));
    gel(iB,i) = ginv(gel(B,i));
  }
  *ptB = B; return f;
}

/* Assume B an LLL-reduced basis, t a vector. Apply Babai's nearest plane
 * algorithm to (B,t) */
GEN
RgM_Babai(GEN B, GEN t)
{
  GEN C, N, G = RgM_gram_schmidt(B, &N), b = t;
  long j, n = lg(B)-1;

  C = cgetg(n+1,t_COL);
  for (j = n; j > 0; j--)
  {
    GEN c = gdiv( RgV_dotproduct(b, gel(G,j)), gel(N,j) );
    long e;
    c = grndtoi(c,&e);
    if (e >= 0) return NULL;
    if (signe(c)) b = RgC_sub(b, RgC_Rg_mul(gel(G,j), c));
    gel(C,j) = c;
  }
  return C;
}

/********************************************************************/
/**                                                                **/
/**                          LLL ALGORITHM                         **/
/**                                                                **/
/********************************************************************/
/* Def: a matrix M is said to be -partially reduced- if | m1 +- m2 | >= |m1|
 * for any two columns m1 != m2, in M.
 *
 * Input: an integer matrix mat whose columns are linearly independent. Find
 * another matrix T such that mat * T is partially reduced.
 *
 * Output: mat * T if flag = 0;  T if flag != 0,
 *
 * This routine is designed to quickly reduce lattices in which one row
 * is huge compared to the other rows.  For example, when searching for a
 * polynomial of degree 3 with root a mod N, the four input vectors might
 * be the coefficients of
 *     X^3 - (a^3 mod N), X^2 - (a^2 mod N), X - (a mod N), N.
 * All four constant coefficients are O(p) and the rest are O(1). By the
 * pigeon-hole principle, the coefficients of the smallest vector in the
 * lattice are O(p^(1/4)), hence significant reduction of vector lengths
 * can be anticipated.
 *
 * An improved algorithm would look only at the leading digits of dot*.  It
 * would use single-precision calculations as much as possible.
 *
 * Original code: Peter Montgomery (1994) */
static GEN
lllintpartialall(GEN m, long flag)
{
  const long ncol = lg(m)-1;
  const pari_sp av = avma;
  GEN tm1, tm2, mid;

  if (ncol <= 1) return flag? matid(ncol): gcopy(m);

  tm1 = flag? matid(ncol): NULL;
  {
    const pari_sp av2 = avma;
    GEN dot11 = ZV_dotsquare(gel(m,1));
    GEN dot22 = ZV_dotsquare(gel(m,2));
    GEN dot12 = ZV_dotproduct(gel(m,1), gel(m,2));
    GEN tm  = matid(2); /* For first two columns only */

    int progress = 0;
    long npass2 = 0;

/* Row reduce the first two columns of m. Our best result so far is
 * (first two columns of m)*tm.
 *
 * Initially tm = 2 x 2 identity matrix.
 * Inner products of the reduced matrix are in dot11, dot12, dot22. */
    while (npass2 < 2 || progress)
    {
      GEN dot12new, q = diviiround(dot12, dot22);

      npass2++; progress = signe(q);
      if (progress)
      {/* Conceptually replace (v1, v2) by (v1 - q*v2, v2), where v1 and v2
        * represent the reduced basis for the first two columns of the matrix.
        * We do this by updating tm and the inner products. */
        togglesign(q);
        dot12new = addii(dot12, mulii(q, dot22));
        dot11 = addii(dot11, mulii(q, addii(dot12, dot12new)));
        dot12 = dot12new;
        ZC_lincomb1_inplace(gel(tm,1), gel(tm,2), q);
      }

      /* Interchange the output vectors v1 and v2.  */
      swap(dot11,dot22);
      swap(gel(tm,1), gel(tm,2));

      /* Occasionally (including final pass) do garbage collection.  */
      if ((npass2 & 0xff) == 0 || !progress)
        gerepileall(av2, 4, &dot11,&dot12,&dot22,&tm);
    } /* while npass2 < 2 || progress */

    {
      long i;
      GEN det12 = subii(mulii(dot11, dot22), sqri(dot12));

      mid = cgetg(ncol+1, t_MAT);
      for (i = 1; i <= 2; i++)
      {
        GEN tmi = gel(tm,i);
        if (tm1)
        {
          GEN tm1i = gel(tm1,i);
          gel(tm1i,1) = gel(tmi,1);
          gel(tm1i,2) = gel(tmi,2);
        }
        gel(mid,i) = ZC_lincomb(gel(tmi,1),gel(tmi,2), gel(m,1),gel(m,2));
      }
      for (i = 3; i <= ncol; i++)
      {
        GEN c = gel(m,i);
        GEN dot1i = ZV_dotproduct(gel(mid,1), c);
        GEN dot2i = ZV_dotproduct(gel(mid,2), c);
       /* ( dot11  dot12 ) (q1)   ( dot1i )
        * ( dot12  dot22 ) (q2) = ( dot2i )
        *
        * Round -q1 and -q2 to nearest integer. Then compute
        *   c - q1*mid[1] - q2*mid[2].
        * This will be approximately orthogonal to the first two vectors in
        * the new basis. */
        GEN q1neg = subii(mulii(dot12, dot2i), mulii(dot22, dot1i));
        GEN q2neg = subii(mulii(dot12, dot1i), mulii(dot11, dot2i));

        q1neg = diviiround(q1neg, det12);
        q2neg = diviiround(q2neg, det12);
        if (tm1)
        {
          gcoeff(tm1,1,i) = addii(mulii(q1neg, gcoeff(tm,1,1)),
                                  mulii(q2neg, gcoeff(tm,1,2)));
          gcoeff(tm1,2,i) = addii(mulii(q1neg, gcoeff(tm,2,1)),
                                  mulii(q2neg, gcoeff(tm,2,2)));
        }
        gel(mid,i) = ZC_add(c, ZC_lincomb(q1neg,q2neg, gel(mid,1),gel(mid,2)));
      } /* for i */
    } /* local block */
  }
  if (DEBUGLEVEL>6)
  {
    if (tm1) err_printf("tm1 = %Ps",tm1);
    err_printf("mid = %Ps",mid); /* = m * tm1 */
  }
  gerepileall(av, tm1? 2: 1, &mid, &tm1);
  {
   /* For each pair of column vectors v and w in mid * tm2,
    * try to replace (v, w) by (v, v - q*w) for some q.
    * We compute all inner products and check them repeatedly. */
    const pari_sp av3 = avma;
    long i, j, npass = 0, e = LONG_MAX;
    GEN dot = cgetg(ncol+1, t_MAT); /* scalar products */

    tm2 = matid(ncol);
    for (i=1; i <= ncol; i++)
    {
      gel(dot,i) = cgetg(ncol+1,t_COL);
      for (j=1; j <= i; j++)
        gcoeff(dot,j,i) = gcoeff(dot,i,j) = ZV_dotproduct(gel(mid,i),gel(mid,j));
    }
    for(;;)
    {
      long reductions = 0, olde = e;
      for (i=1; i <= ncol; i++)
      {
        long ijdif;
        for (ijdif=1; ijdif < ncol; ijdif++)
        {
          long d, k1, k2;
          GEN codi, q;

          j = i + ijdif; if (j > ncol) j -= ncol;
          /* let k1, resp. k2,  index of larger, resp. smaller, column */
          if (cmpii(gcoeff(dot,i,i), gcoeff(dot,j,j)) > 0) { k1 = i; k2 = j; }
          else                                             { k1 = j; k2 = i; }
          codi = gcoeff(dot,k2,k2);
          q = signe(codi)? diviiround(gcoeff(dot,k1,k2), codi): gen_0;
          if (!signe(q)) continue;

          /* Try to subtract a multiple of column k2 from column k1.  */
          reductions++; togglesign_safe(&q);
          ZC_lincomb1_inplace(gel(tm2,k1), gel(tm2,k2), q);
          ZC_lincomb1_inplace(gel(dot,k1), gel(dot,k2), q);
          gcoeff(dot,k1,k1) = addii(gcoeff(dot,k1,k1),
                                    mulii(q, gcoeff(dot,k2,k1)));
          for (d = 1; d <= ncol; d++) gcoeff(dot,k1,d) = gcoeff(dot,d,k1);
        } /* for ijdif */
        if (gc_needed(av3,2))
        {
          if(DEBUGMEM>1) pari_warn(warnmem,"lllintpartialall");
          gerepileall(av3, 2, &dot,&tm2);
        }
      } /* for i */
      if (!reductions) break;
      e = 0;
      for (i = 1; i <= ncol; i++) e += expi( gcoeff(dot,i,i) );
      if (e == olde) break;
      if (DEBUGLEVEL>6)
      {
        npass++;
        err_printf("npass = %ld, red. last time = %ld, log_2(det) ~ %ld\n\n",
                    npass, reductions, e);
      }
    } /* for(;;)*/

   /* Sort columns so smallest comes first in m * tm1 * tm2.
    * Use insertion sort. */
    for (i = 1; i < ncol; i++)
    {
      long j, s = i;

      for (j = i+1; j <= ncol; j++)
        if (cmpii(gcoeff(dot,s,s),gcoeff(dot,j,j)) > 0) s = j;
      if (i != s)
      { /* Exchange with proper column; only the diagonal of dot is updated */
        swap(gel(tm2,i), gel(tm2,s));
        swap(gcoeff(dot,i,i), gcoeff(dot,s,s));
      }
    }
  } /* local block */
  return gerepileupto(av, ZM_mul(tm1? tm1: mid, tm2));
}

GEN
lllintpartial(GEN mat) { return lllintpartialall(mat,1); }

GEN
lllintpartial_inplace(GEN mat) { return lllintpartialall(mat,0); }

/********************************************************************/
/**                                                                **/
/**                    COPPERSMITH ALGORITHM                       **/
/**           Finding small roots of univariate equations.         **/
/**                                                                **/
/********************************************************************/

static int
check_condition(double beta, double tau, double rho, long d, long delta, long t)
{
  long dim = d*delta + t;
  double cond = d*delta*(delta+1)/2 - beta*delta*dim
    + rho*delta*(delta - 1) / 2
    + rho * t * delta + tau*dim*(dim - 1)/2;

  if (DEBUGLEVEL >= 4)
    err_printf("delta = %d, t = %d, cond = %.1lf\n", delta, t, cond);

  return (cond <= 0);
}

static void
choose_params(GEN P, GEN N, GEN X, GEN B, long *pdelta, long *pt)
{
  long d = degpol(P);
  GEN P0 = leading_coeff(P);
  double logN = gtodouble(glog(N, DEFAULTPREC));
  double tau, beta, rho;
  long delta, t;
  tau = gtodouble(glog(X, DEFAULTPREC)) / logN;
  beta = B? gtodouble(glog(B, DEFAULTPREC)) / logN: 1.;
  if (tau >= beta * beta / d)
    pari_err_OVERFLOW("zncoppersmith [bound too large]");
  /* TODO : remove P0 completely ! */
  rho = gtodouble(glog(P0, DEFAULTPREC)) / logN;

  /* Enumerate (delta,t) by increasing dimension of resulting lattice.
   * Not subtle, but o(1) for computing time */
  t = d; delta = 0;
  for(;;)
  {
    t += d * delta + 1; delta = 0;
    while (t >= 0) {
      if (check_condition(beta, tau, rho, d, delta, t)) {
        *pdelta = delta; *pt = t; return;
      }
      delta++; t -= d;
    }
  }
}

static int
sol_OK(GEN x, GEN N, GEN B)
{ return B? (cmpii(gcdii(x,N),B) >= 0): dvdii(x,N); }
/* deg(P) > 0, x >= 0. Find all j such that gcd(P(j), N) >= B, |j| <= x */
static GEN
do_exhaustive(GEN P, GEN N, long x, GEN B)
{
  GEN Pe, Po, sol = vecsmalltrunc_init(2*x + 2);
  pari_sp av;
  long j;
  RgX_even_odd(P, &Pe,&Po); av = avma;
  if (sol_OK(gel(P,2), N,B)) vecsmalltrunc_append(sol, 0);
  for (j = 1; j <= x; j++, avma = av)
  {
    GEN j2 = sqru(j), E = FpX_eval(Pe,j2,N), O = FpX_eval(Po,j2,N);
    if (sol_OK(addmuliu(E,O,j), N,B)) vecsmalltrunc_append(sol, j);
    if (sol_OK(submuliu(E,O,j), N,B)) vecsmalltrunc_append(sol,-j);
  }
  vecsmall_sort(sol); return zv_to_ZV(sol);
}

/* General Coppersmith, look for a root x0 <= p, p >= B, p | N, |x0| <= X.
 * B = N coded as NULL */
GEN
zncoppersmith(GEN P0, GEN N, GEN X, GEN B)
{
  GEN Q, R, N0, M, sh, short_pol, *Xpowers, sol, nsp, P, Z;
  long delta, i, j, row, d, l, dim, t, bnd = 10;
  const ulong X_SMALL = 1000;

  pari_sp av = avma;

  if (typ(P0) != t_POL) pari_err_TYPE("zncoppersmith",P0);
  if (typ(N) != t_INT) pari_err_TYPE("zncoppersmith",N);
  if (typ(X) != t_INT) {
    X = gfloor(X);
    if (typ(X) != t_INT) pari_err_TYPE("zncoppersmith",X);
  }
  if (signe(X) < 0) pari_err_DOMAIN("zncoppersmith", "X", "<", gen_0, X);
  d = degpol(P0);
  if (d == 0) { avma = av; return cgetg(1, t_VEC); }
  if (d < 0) pari_err_ROOTS0("zncoppersmith");
  if (B && typ(B) != t_INT) B = gceil(B);

  if (abscmpiu(X, X_SMALL) <= 0)
    return gerepileupto(av, do_exhaustive(P0, N, itos(X), B));

  if (B && equalii(B,N)) B = NULL;
  if (B) bnd = 1; /* bnd-hack is only for the case B = N */
  P = leafcopy(P0);
  if (!gequal1(gel(P,d+2)))
  {
    GEN r, z;
    gel(P,d+2) = bezout(gel(P,d+2), N, &z, &r);
    for (j = 0; j < d; j++) gel(P,j+2) = modii(mulii(gel(P,j+2), z), N);
  }
  if (DEBUGLEVEL >= 2) err_printf("Modified P: %Ps\n", P);

  choose_params(P, N, X, B, &delta, &t);
  if (DEBUGLEVEL >= 2)
    err_printf("Init: trying delta = %d, t = %d\n", delta, t);
  for(;;)
  {
    dim = d * delta + t;

    /* TODO: In case of failure do not recompute the full vector */
    Xpowers = (GEN*)new_chunk(dim + 1);
    Xpowers[0] = gen_1;
    for (j = 1; j <= dim; j++) Xpowers[j] = mulii(Xpowers[j-1], X);

    /* TODO: in case of failure, use the part of the matrix already computed */
    M = zeromatcopy(dim,dim);

    /* Rows of M correspond to the polynomials
     * N^delta, N^delta Xi, ... N^delta (Xi)^d-1,
     * N^(delta-1)P(Xi), N^(delta-1)XiP(Xi), ... N^(delta-1)P(Xi)(Xi)^d-1,
     * ...
     * P(Xi)^delta, XiP(Xi)^delta, ..., P(Xi)^delta(Xi)^t-1 */
    for (j = 1; j <= d;   j++) gcoeff(M, j, j) = gel(Xpowers,j-1);

    /* P-part */
    if (delta) row = d + 1; else row = 0;

    Q = P;
    for (i = 1; i < delta; i++)
    {
      for (j = 0; j < d; j++,row++)
        for (l = j + 1; l <= row; l++)
          gcoeff(M, l, row) = mulii(Xpowers[l-1], gel(Q,l-j+1));
      Q = ZX_mul(Q, P);
    }
    for (j = 0; j < t; row++, j++)
      for (l = j + 1; l <= row; l++)
        gcoeff(M, l, row) = mulii(Xpowers[l-1], gel(Q,l-j+1));

    /* N-part */
    row = dim - t; N0 = N;
    while (row >= 1)
    {
      for (j = 0; j < d; j++,row--)
        for (l = 1; l <= row; l++)
          gcoeff(M, l, row) = mulii(gmael(M, row, l), N0);
      if (row >= 1) N0 = mulii(N0, N);
    }
    /* Z is the upper bound for the L^1 norm of the polynomial,
       ie. N^delta if B = N, B^delta otherwise */
    if (B) Z = powiu(B, delta); else Z = N0;

    if (DEBUGLEVEL >= 2)
    {
      if (DEBUGLEVEL >= 6) err_printf("Matrix to be reduced:\n%Ps\n", M);
      err_printf("Entering LLL\nbitsize bound: %ld\n", expi(Z));
      err_printf("expected shvector bitsize: %ld\n", expi(ZM_det_triangular(M))/dim);
    }

    sh = ZM_lll(M, 0.75, LLL_INPLACE);
    /* Take the first vector if it is non constant */
    short_pol = gel(sh,1);
    if (ZV_isscalar(short_pol)) short_pol = gel(sh, 2);

    nsp = gen_0;
    for (j = 1; j <= dim; j++) nsp = addii(nsp, absi_shallow(gel(short_pol,j)));

    if (DEBUGLEVEL >= 2)
    {
      err_printf("Candidate: %Ps\n", short_pol);
      err_printf("bitsize Norm: %ld\n", expi(nsp));
      err_printf("bitsize bound: %ld\n", expi(mului(bnd, Z)));
    }
    if (cmpii(nsp, mului(bnd, Z)) < 0) break; /* SUCCESS */

    /* Failed with the precomputed or supplied value */
    t++; if (t == d) { delta++; t = 1; }
    if (DEBUGLEVEL >= 2)
      err_printf("Increasing dim, delta = %d t = %d\n", delta, t);
  }
  bnd = itos(divii(nsp, Z)) + 1;

  while (!signe(gel(short_pol,dim))) dim--;

  R = cgetg(dim + 2, t_POL); R[1] = P[1];
  for (j = 1; j <= dim; j++)
    gel(R,j+1) = diviiexact(gel(short_pol,j), Xpowers[j-1]);
  gel(R,2) = subii(gel(R,2), mului(bnd - 1, N0));

  sol = cgetg(1, t_VEC);
  for (i = -bnd + 1; i < bnd; i++)
  {
    GEN r = nfrootsQ(R);
    if (DEBUGLEVEL >= 2) err_printf("Roots: %Ps\n", r);
    for (j = 1; j < lg(r); j++)
    {
      GEN z = gel(r,j);
      if (typ(z) == t_INT && sol_OK(FpX_eval(P,z,N), N,B))
        sol = shallowconcat(sol, z);
    }
    if (i < bnd) gel(R,2) = addii(gel(R,2), Z);
  }
  return gerepileupto(av, ZV_sort_uniq(sol));
}

/********************************************************************/
/**                                                                **/
/**                   LINEAR & ALGEBRAIC DEPENDENCE                **/
/**                                                                **/
/********************************************************************/

static int
real_indep(GEN re, GEN im, long bit)
{
  GEN d = gsub(gmul(gel(re,1),gel(im,2)), gmul(gel(re,2),gel(im,1)));
  return (!gequal0(d) && gexpo(d) > - bit);
}

GEN
lindepfull_bit(GEN x, long bit)
{
  long lx = lg(x), ly, i, j;
  GEN re, im, M;

  if (! is_vec_t(typ(x))) pari_err_TYPE("lindep2",x);
  if (lx <= 2)
  {
    if (lx == 2 && gequal0(x)) return matid(1);
    return NULL;
  }
  re = real_i(x);
  im = imag_i(x);
  /* independent over R ? */
  if (lx == 3 && real_indep(re,im,bit)) return NULL;
  if (gequal0(im)) im = NULL;
  ly = im? lx+2: lx+1;
  M = cgetg(lx,t_MAT);
  for (i=1; i<lx; i++)
  {
    GEN c = cgetg(ly,t_COL); gel(M,i) = c;
    for (j=1; j<lx; j++) gel(c,j) = gen_0;
    gel(c,i) = gen_1;
    gel(c,lx)           = gtrunc2n(gel(re,i), bit);
    if (im) gel(c,lx+1) = gtrunc2n(gel(im,i), bit);
  }
  return ZM_lll(M, 0.99, LLL_INPLACE);
}
GEN
lindep_bit(GEN x, long bit)
{
  pari_sp av = avma;
  GEN v, M = lindepfull_bit(x,bit);
  if (!M) { avma = av; return cgetg(1, t_COL); }
  v = gel(M,1); setlg(v, lg(M));
  return gerepilecopy(av, v);
}
/* deprecated */
GEN
lindep2(GEN x, long dig)
{
  long bit;
  if (dig < 0) pari_err_DOMAIN("lindep2", "accuracy", "<", gen_0, stoi(dig));
  if (dig) bit = (long) (dig/LOG10_2);
  else
  {
    bit = gprecision(x);
    if (!bit)
    {
      x = Q_primpart(x); /* left on stack */
      bit = 32 + gexpo(x);
    }
    else
      bit = (long)prec2nbits_mul(bit, 0.8);
  }
  return lindep_bit(x, bit);
}

/* x is a vector of elts of a p-adic field */
GEN
lindep_padic(GEN x)
{
  long i, j, prec = LONG_MAX, nx = lg(x)-1, v;
  pari_sp av = avma;
  GEN p = NULL, pn, m, a;

  if (nx < 2) return cgetg(1,t_COL);
  for (i=1; i<=nx; i++)
  {
    GEN c = gel(x,i), q;
    if (typ(c) != t_PADIC) continue;

    j = precp(c); if (j < prec) prec = j;
    q = gel(c,2);
    if (!p) p = q; else if (!equalii(p, q)) pari_err_MODULUS("lindep_padic", p, q);
  }
  if (!p) pari_err_TYPE("lindep_padic [not a p-adic vector]",x);
  v = gvaluation(x,p); pn = powiu(p,prec);
  if (v) x = gmul(x, powis(p, -v));
  x = RgV_to_FpV(x, pn);

  a = negi(gel(x,1));
  m = cgetg(nx,t_MAT);
  for (i=1; i<nx; i++)
  {
    GEN c = zerocol(nx);
    gel(c,1+i) = a;
    gel(c,1) = gel(x,i+1);
    gel(m,i) = c;
  }
  m = ZM_lll(ZM_hnfmodid(m, pn), 0.99, LLL_INPLACE);
  return gerepilecopy(av, gel(m,1));
}
/* x is a vector of t_POL/t_SER */
GEN
lindep_Xadic(GEN x)
{
  long i, prec = LONG_MAX, deg = 0, lx = lg(x), vx, v;
  pari_sp av = avma;
  GEN m;

  if (lx == 1) return cgetg(1,t_COL);
  vx = gvar(x);
  v = gvaluation(x, pol_x(vx));
  if (!v)         x = shallowcopy(x);
  else if (v > 0) x = gdiv(x, pol_xn(v, vx));
  else            x = gmul(x, pol_xn(-v, vx));
  /* all t_SER have valuation >= 0 */
  for (i=1; i<lx; i++)
  {
    GEN c = gel(x,i);
    if (gvar(c) != vx) { gel(x,i) = scalarpol_shallow(c, vx); continue; }
    switch(typ(c))
    {
      case t_POL: deg = maxss(deg, degpol(c)); break;
      case t_RFRAC: pari_err_TYPE("lindep_Xadic", c);
      case t_SER:
        prec = minss(prec, valp(c)+lg(c)-2);
        gel(x,i) = ser2rfrac_i(c);
    }
  }
  if (prec == LONG_MAX) prec = deg+1;
  m = RgXV_to_RgM(x, prec);
  return gerepileupto(av, deplin(m));
}
static GEN
vec_lindep(GEN x)
{
  pari_sp av = avma;
  long i, l = lg(x); /* > 1 */
  long t = typ(gel(x,1)), h = lg(gel(x,1));
  GEN m = cgetg(l, t_MAT);
  for (i = 1; i < l; i++)
  {
    GEN y = gel(x,i);
    if (lg(y) != h || typ(y) != t) pari_err_TYPE("lindep",x);
    if (t != t_COL) y = shallowtrans(y); /* Sigh */
    gel(m,i) = y;
  }
  return gerepileupto(av, deplin(m));
}

GEN
lindep(GEN x) { return lindep2(x, 0); }

GEN
lindep0(GEN x,long bit)
{
  long i, tx = typ(x);
  if (tx == t_MAT) return deplin(x);
  if (! is_vec_t(tx)) pari_err_TYPE("lindep",x);
  for (i = 1; i < lg(x); i++)
    switch(typ(gel(x,i)))
    {
      case t_PADIC: return lindep_padic(x);
      case t_POL:
      case t_RFRAC:
      case t_SER: return lindep_Xadic(x);
      case t_VEC:
      case t_COL: return vec_lindep(x);
    }
  return lindep2(x, bit);
}

GEN
algdep0(GEN x, long n, long bit)
{
  long tx = typ(x), i;
  pari_sp av;
  GEN y;

  if (! is_scalar_t(tx)) pari_err_TYPE("algdep0",x);
  if (tx==t_POLMOD) { y = RgX_copy(gel(x,1)); setvarn(y,0); return y; }
  if (gequal0(x)) return pol_x(0);
  if (n <= 0)
  {
    if (!n) return gen_1;
    pari_err_DOMAIN("algdep", "degree", "<", gen_0, stoi(n));
  }

  av = avma; y = cgetg(n+2,t_COL);
  gel(y,1) = gen_1;
  gel(y,2) = x; /* n >= 1 */
  for (i=3; i<=n+1; i++) gel(y,i) = gmul(gel(y,i-1),x);
  if (typ(x) == t_PADIC)
    y = lindep_padic(y);
  else
    y = lindep2(y, bit);
  if (lg(y) == 1) pari_err(e_DOMAIN,"algdep", "degree(x)",">", stoi(n), x);
  y = RgV_to_RgX(y, 0);
  if (signe(leading_coeff(y)) > 0) return gerepilecopy(av, y);
  return gerepileupto(av, ZX_neg(y));
}

GEN
algdep(GEN x, long n)
{
  return algdep0(x,n,0);
}

GEN
seralgdep(GEN s, long p, long r)
{
  pari_sp av = avma;
  long vy, i, m, n, prec;
  GEN S, v, D;

  if (typ(s) != t_SER) pari_err_TYPE("seralgdep",s);
  if (p <= 0) pari_err_DOMAIN("seralgdep", "p", "<=", gen_0, stoi(p));
  if (r < 0) pari_err_DOMAIN("seralgdep", "r", "<", gen_0, stoi(r));
  if (is_bigint(addiu(muluu(p, r), 1))) pari_err_OVERFLOW("seralgdep");
  vy = varn(s);
  if (!vy) pari_err_PRIORITY("seralgdep", s, ">", 0);
  r++; p++;
  prec = valp(s) + lg(s)-2;
  if (r > prec) r = prec;
  S = cgetg(p+1, t_VEC); gel(S, 1) = s;
  for (i = 2; i <= p; i++) gel(S,i) = gmul(gel(S,i-1), s);
  v = cgetg(r*p+1, t_VEC); /* v[r*n+m+1] = s^n * y^m */
  /* n = 0 */
  for (m = 0; m < r; m++) gel(v, m+1) = pol_xn(m, vy);
  for(n=1; n < p; n++)
    for (m = 0; m < r; m++)
    {
      GEN c = gel(S,n);
      if (m)
      {
        c = shallowcopy(c);
        setvalp(c, valp(c) + m);
      }
      gel(v, r*n + m + 1) = c;
    }
  D = lindep_Xadic(v);
  if (lg(D) == 1) { avma = av; return gen_0; }
  v = cgetg(p+1, t_VEC);
  for (n = 0; n < p; n++)
    gel(v, n+1) = RgV_to_RgX(vecslice(D, r*n+1, r*n+r), vy);
  return gerepilecopy(av, RgV_to_RgX(v, 0));
}

/* FIXME: could precompute ZM_lll attached to V[2..] */
static GEN
lindepcx(GEN V, long bit)
{
  GEN Vr = real_i(V), Vi = imag_i(V);
  if (gexpo(Vr) < -bit) V = Vi;
  else if (gexpo(Vi) < -bit) V = Vr;
  return lindepfull_bit(V, bit);
}
/* c floating point t_REAL or t_COMPLEX, T ZX, recognize in Q[x]/(T).
 * V helper vector (containing complex roots of T), MODIFIED */
static GEN
cx_bestapprnf(GEN c, GEN T, GEN V, long bit)
{
  GEN M, a, v = NULL;
  long i, l;
  gel(V,1) = gneg(c); M = lindepcx(V, bit);
  if (!M) pari_err(e_MISC, "cannot rationalize coeff in bestapprnf");
  l = lg(M); a = NULL;
  for (i = 1; i < l; i ++) { v = gel(M,i); a = gel(v,1); if (signe(a)) break; }
  v = RgC_Rg_div(vecslice(v, 2, lg(M)-1), a);
  if (!T) return gel(v,1);
  v = RgV_to_RgX(v, varn(T)); l = lg(v);
  if (l == 2) return gen_0;
  if (l == 3) return gel(v,2);
  return mkpolmod(v, T);
}
static GEN
bestapprnf_i(GEN x, GEN T, GEN V, long bit)
{
  long i, l, tx = typ(x);
  GEN z;
  switch (tx)
  {
    case t_INT: case t_FRAC: return x;
    case t_REAL: case t_COMPLEX: return cx_bestapprnf(x, T, V, bit);
    case t_POLMOD: if (RgX_equal(gel(x,1),T)) return x;
                   break;
    case t_POL: case t_SER: case t_VEC: case t_COL: case t_MAT:
      l = lg(x); z = cgetg(l, tx);
      for (i = 1; i < lontyp[tx]; i++) z[i] = x[i];
      for (; i < l; i++) gel(z,i) = bestapprnf_i(gel(x,i), T, V, bit);
      return z;
  }
  pari_err_TYPE("mfcxtoQ", x);
  return NULL;/*LCOV_EXCL_LINE*/
}

GEN
bestapprnf(GEN x, GEN T, GEN roT, long prec)
{
  pari_sp av = avma;
  long tx = typ(x), dT = 1, bit;
  GEN V;

  if (T)
  {
    if (typ(T) != t_POL) T = nf_get_pol(checknf(T));
    else if (!RgX_is_ZX(T)) pari_err_TYPE("bestapprnf", T);
    dT = degpol(T);
  }
  if (is_rational_t(tx)) return gcopy(x);
  if (tx == t_POLMOD)
  {
    if (!T || !RgX_equal(T, gel(x,1))) pari_err_TYPE("bestapprnf",x);
    return gcopy(x);
  }

  if (roT)
  {
    long l = gprecision(roT);
    switch(typ(roT))
    {
      case t_INT: case t_FRAC: case t_REAL: case t_COMPLEX: break;
      default: pari_err_TYPE("bestapprnf", roT);
    }
    if (prec < l) prec = l;
  }
  else if (!T)
    roT = gen_1;
  else
  {
    long n = poliscyclo(T); /* cyclotomic is an important special case */
    roT = n? rootsof1u_cx(n,prec): gel(QX_complex_roots(T,prec), 1);
  }
  V = vec_prepend(gpowers(roT, dT-1), NULL);
  bit = prec2nbits_mul(prec, 0.8);
  return gerepilecopy(av, bestapprnf_i(x, T, V, bit));
}

/********************************************************************/
/**                                                                **/
/**                              MINIM                             **/
/**                                                                **/
/********************************************************************/
void
minim_alloc(long n, double ***q, GEN *x, double **y,  double **z, double **v)
{
  long i, s;

  *x = cgetg(n, t_VECSMALL);
  *q = (double**) new_chunk(n);
  s = n * sizeof(double);
  *y = (double*) stack_malloc_align(s, sizeof(double));
  *z = (double*) stack_malloc_align(s, sizeof(double));
  *v = (double*) stack_malloc_align(s, sizeof(double));
  for (i=1; i<n; i++) (*q)[i] = (double*) stack_malloc_align(s, sizeof(double));
}

static GEN
ZC_canon(GEN V)
{
  long l = lg(V), j;
  for (j = 1; j < l  &&  signe(gel(V,j)) == 0; ++j);
  return (j < l  &&  signe(gel(V,j)) < 0)? ZC_neg(V): V;
}

static GEN
ZM_zc_mul_canon(GEN u, GEN x)
{
  return ZC_canon(ZM_zc_mul(u,x));
}

struct qfvec
{
  GEN a, r, u;
};

static void
err_minim(GEN a)
{
  pari_err_DOMAIN("minim0","form","is not",
                  strtoGENstr("positive definite"),a);
}

static GEN
minim_lll(GEN a, GEN *u)
{
  *u = lllgramint(a);
  if (lg(*u) != lg(a)) err_minim(a);
  return qf_apply_ZM(a,*u);
}

static void
forqfvec_init_dolll(struct qfvec *qv, GEN a, long dolll)
{
  GEN r, u;
  if (!dolll) u = NULL;
  else
  {
    if (typ(a) != t_MAT || !RgM_is_ZM(a)) pari_err_TYPE("qfminim",a);
    a = minim_lll(a, &u);
  }
  qv->a = RgM_gtofp(a, DEFAULTPREC);
  r = qfgaussred_positive(qv->a);
  if (!r)
  {
    r = qfgaussred_positive(a); /* exact computation */
    if (!r) err_minim(a);
    r = RgM_gtofp(r, DEFAULTPREC);
  }
  qv->r = r;
  qv->u = u;
}

static void
forqfvec_init(struct qfvec *qv, GEN a)
{ forqfvec_init_dolll(qv, a, 1); }

static void
forqfvec_i(void *E, long (*fun)(void *, GEN, GEN, double), struct qfvec *qv, GEN BORNE)
{
  GEN x, a = qv->a, r = qv->r, u = qv->u;
  long n = lg(a), i, j, k;
  double p,BOUND,*v,*y,*z,**q;
  const double eps = 0.0001;
  if (!BORNE) BORNE = gen_0;
  else
  {
    BORNE = gfloor(BORNE);
    if (typ(BORNE) != t_INT) pari_err_TYPE("minim0",BORNE);
  }
  if (n == 1) return;
  minim_alloc(n, &q, &x, &y, &z, &v);
  n--;
  for (j=1; j<=n; j++)
  {
    v[j] = rtodbl(gcoeff(r,j,j));
    for (i=1; i<j; i++) q[i][j] = rtodbl(gcoeff(r,i,j));
  }

  if (gequal0(BORNE))
  {
    double c;
    p = rtodbl(gcoeff(a,1,1));
    for (i=2; i<=n; i++) { c = rtodbl(gcoeff(a,i,i)); if (c < p) p = c; }
    BORNE = roundr(dbltor(p));
  }
  else
    p = gtodouble(BORNE);
  BOUND = p * (1 + eps);
  if (BOUND == p) pari_err_PREC("minim0");

  k = n; y[n] = z[n] = 0;
  x[n] = (long)sqrt(BOUND/v[n]);
  for(;;x[1]--)
  {
    do
    {
      if (k>1)
      {
        long l = k-1;
        z[l] = 0;
        for (j=k; j<=n; j++) z[l] += q[l][j]*x[j];
        p = (double)x[k] + z[k];
        y[l] = y[k] + p*p*v[k];
        x[l] = (long)floor(sqrt((BOUND-y[l])/v[l])-z[l]);
        k = l;
      }
      for(;;)
      {
        p = (double)x[k] + z[k];
        if (y[k] + p*p*v[k] <= BOUND) break;
        k++; x[k]--;
      }
    } while (k > 1);
    if (! x[1] && y[1]<=eps) break;

    p = (double)x[1] + z[1]; p = y[1] + p*p*v[1]; /* norm(x) */
    if (fun(E, u, x, p)) break;
  }
}

void
forqfvec(void *E, long (*fun)(void *, GEN, GEN, double), GEN a, GEN BORNE)
{
  pari_sp av = avma;
  struct qfvec qv;
  forqfvec_init(&qv, a);
  forqfvec_i(E, fun, &qv, BORNE);
  avma = av;
}

static long
_gp_forqf(void *E, GEN u, GEN x, double p/*unused*/)
{
  pari_sp av = avma;
  (void)p;
  set_lex(-1, ZM_zc_mul_canon(u, x));
  closure_evalvoid((GEN)E);
  avma = av;
  return loop_break();
}

void
forqfvec0(GEN a, GEN BORNE, GEN code)
{
  pari_sp av = avma;
  struct qfvec qv;
  forqfvec_init(&qv, a);
  push_lex(gen_0, code);
  forqfvec_i((void*) code, &_gp_forqf, &qv, BORNE);
  pop_lex(1);
  avma = av;
}

enum { min_ALL = 0, min_FIRST, min_VECSMALL, min_VECSMALL2 };

/* Minimal vectors for the integral definite quadratic form: a.
 * Result u:
 *   u[1]= Number of vectors of square norm <= BORNE
 *   u[2]= maximum norm found
 *   u[3]= list of vectors found (at most STOCKMAX, unless NULL)
 *
 *  If BORNE = NULL: Minimal non-zero vectors.
 *  flag = min_ALL,   as above
 *  flag = min_FIRST, exits when first suitable vector is found.
 *  flag = min_VECSMALL, return a t_VECSMALL of (half) the number of vectors
 *  for each norm
 *  flag = min_VECSMALL2, same but count only vectors with even norm, and shift
 *  the answer */
static GEN
minim0_dolll(GEN a, GEN BORNE, GEN STOCKMAX, long flag, long dolll)
{
  GEN x, u, r, L, gnorme;
  long n = lg(a), i, j, k, s, maxrank, sBORNE;
  pari_sp av = avma, av1;
  double p,maxnorm,BOUND,*v,*y,*z,**q;
  const double eps = 1e-10;
  int stockall = 0;
  struct qfvec qv;

  if (!BORNE)
    sBORNE = 0;
  else
  {
    BORNE = gfloor(BORNE);
    if (typ(BORNE) != t_INT) pari_err_TYPE("minim0",BORNE);
    if (is_bigint(BORNE)) pari_err_PREC( "qfminim");
    sBORNE = itos(BORNE); avma = av;
  }
  if (!STOCKMAX)
  {
    stockall = 1;
    maxrank = 200;
  }
  else
  {
    STOCKMAX = gfloor(STOCKMAX);
    if (typ(STOCKMAX) != t_INT) pari_err_TYPE("minim0",STOCKMAX);
    maxrank = itos(STOCKMAX);
    if (maxrank < 0)
      pari_err_TYPE("minim0 [negative number of vectors]",STOCKMAX);
  }

  switch(flag)
  {
    case min_VECSMALL:
    case min_VECSMALL2:
      if (sBORNE <= 0) return cgetg(1, t_VECSMALL);
      L = zero_zv(sBORNE);
      if (flag == min_VECSMALL2) sBORNE <<= 1;
      if (n == 1) return L;
      break;
    case min_FIRST:
      if (n == 1 || (!sBORNE && BORNE)) return cgetg(1,t_VEC);
      L = NULL; /* gcc -Wall */
      break;
    case min_ALL:
      if (n == 1 || (!sBORNE && BORNE))
        retmkvec3(gen_0, gen_0, cgetg(1, t_MAT));
      L = new_chunk(1+maxrank);
      break;
    default:
      return NULL;
  }
  minim_alloc(n, &q, &x, &y, &z, &v);

  forqfvec_init_dolll(&qv, a, dolll);
  av1 = avma;
  r = qv.r;
  u = qv.u;
  n--;
  for (j=1; j<=n; j++)
  {
    v[j] = rtodbl(gcoeff(r,j,j));
    for (i=1; i<j; i++) q[i][j] = rtodbl(gcoeff(r,i,j)); /* |.| <= 1/2 */
  }

  if (sBORNE) maxnorm = 0.;
  else
  {
    GEN B = gcoeff(a,1,1);
    long t = 1;
    for (i=2; i<=n; i++)
    {
      GEN c = gcoeff(a,i,i);
      if (cmpii(c, B) < 0) { B = c; t = i; }
    }
    if (flag == min_FIRST) return gerepilecopy(av, mkvec2(B, gel(u,t)));
    maxnorm = -1.; /* don't update maxnorm */
    if (is_bigint(B)) return NULL;
    sBORNE = itos(B);
  }
  BOUND = sBORNE * (1 + eps);
  if ((long)BOUND != sBORNE) return NULL;

  s = 0;
  k = n; y[n] = z[n] = 0;
  x[n] = (long)sqrt(BOUND/v[n]);
  for(;;x[1]--)
  {
    do
    {
      if (k>1)
      {
        long l = k-1;
        z[l] = 0;
        for (j=k; j<=n; j++) z[l] += q[l][j]*x[j];
        p = (double)x[k] + z[k];
        y[l] = y[k] + p*p*v[k];
        x[l] = (long)floor(sqrt((BOUND-y[l])/v[l])-z[l]);
        k = l;
      }
      for(;;)
      {
        p = (double)x[k] + z[k];
        if (y[k] + p*p*v[k] <= BOUND) break;
        k++; x[k]--;
      }
    }
    while (k > 1);
    if (! x[1] && y[1]<=eps) break;

    p = (double)x[1] + z[1]; p = y[1] + p*p*v[1]; /* norm(x) */
    if (maxnorm >= 0)
    {
      if (p > maxnorm) maxnorm = p;
    }
    else
    { /* maxnorm < 0 : only look for minimal vectors */
      pari_sp av2 = avma;
      gnorme = roundr(dbltor(p));
      if (cmpis(gnorme, sBORNE) >= 0) avma = av2;
      else
      {
        sBORNE = itos(gnorme); avma = av1;
        BOUND = sBORNE * (1+eps);
        L = new_chunk(maxrank+1);
        s = 0;
      }
    }
    s++;

    switch(flag)
    {
      case min_FIRST:
        if (dolll) x = ZM_zc_mul_canon(u,x);
        return gerepilecopy(av, mkvec2(roundr(dbltor(p)), x));

      case min_ALL:
        if (s > maxrank && stockall) /* overflow */
        {
          long maxranknew = maxrank << 1;
          GEN Lnew = new_chunk(1 + maxranknew);
          for (i=1; i<=maxrank; i++) Lnew[i] = L[i];
          L = Lnew; maxrank = maxranknew;
        }
        if (s<=maxrank) gel(L,s) = leafcopy(x);
        break;

      case min_VECSMALL:
        { ulong norm = (ulong)(p + 0.5); L[norm]++; }
        break;

      case min_VECSMALL2:
        { ulong norm = (ulong)(p + 0.5); if (!odd(norm)) L[norm>>1]++; }
        break;

    }
  }
  switch(flag)
  {
    case min_FIRST:
      avma = av; return cgetg(1,t_VEC);
    case min_VECSMALL:
    case min_VECSMALL2:
      avma = (pari_sp)L; return L;
  }
  r = (maxnorm >= 0) ? roundr(dbltor(maxnorm)): stoi(sBORNE);
  k = minss(s,maxrank);
  L[0] = evaltyp(t_MAT) | evallg(k + 1);
  if (dolll)
    for (j=1; j<=k; j++) gel(L,j) = ZM_zc_mul_canon(u, gel(L,j));
  return gerepilecopy(av, mkvec3(stoi(s<<1), r, L));
}

static GEN
minim0(GEN a, GEN BORNE, GEN STOCKMAX, long flag)
{
  GEN v = minim0_dolll(a, BORNE, STOCKMAX, flag, 1);
  if (!v) pari_err_PREC("qfminim");
  return v;
}

GEN
qfrep0(GEN a, GEN borne, long flag)
{ return minim0(a, borne, gen_0, (flag & 1)? min_VECSMALL2: min_VECSMALL); }

GEN
qfminim0(GEN a, GEN borne, GEN stockmax, long flag, long prec)
{
  switch(flag)
  {
    case 0: return minim0(a,borne,stockmax,min_ALL);
    case 1: return minim0(a,borne,gen_0   ,min_FIRST);
    case 2:
    {
      long maxnum = -1;
      if (typ(a) != t_MAT) pari_err_TYPE("qfminim",a);
      if (stockmax) {
        if (typ(stockmax) != t_INT) pari_err_TYPE("qfminim",stockmax);
        maxnum = itos(stockmax);
      }
      a = fincke_pohst(a,borne,maxnum,prec,NULL);
      if (!a) pari_err_PREC("qfminim");
      return a;
    }
    default: pari_err_FLAG("qfminim");
  }
  return NULL; /* LCOV_EXCL_LINE */
}

GEN
minim(GEN a, GEN borne, GEN stockmax)
{ return minim0(a,borne,stockmax,min_ALL); }

GEN
minim_raw(GEN a, GEN BORNE, GEN STOCKMAX)
{ return minim0_dolll(a, BORNE, STOCKMAX, min_ALL, 0); }

GEN
minim2(GEN a, GEN borne, GEN stockmax)
{ return minim0(a,borne,stockmax,min_FIRST); }

/* If V depends linearly from the columns of the matrix, return 0.
 * Otherwise, update INVP and L and return 1. No GC. */
static int
addcolumntomatrix(GEN V, GEN invp, GEN L)
{
  long i,j,k, n = lg(invp);
  GEN a = cgetg(n, t_COL), ak = NULL, mak;

  for (k = 1; k < n; k++)
    if (!L[k])
    {
      ak = RgMrow_zc_mul(invp, V, k);
      if (!gequal0(ak)) break;
    }
  if (k == n) return 0;
  L[k] = 1;
  mak = gneg_i(ak);
  for (i=k+1; i<n; i++)
    gel(a,i) = gdiv(RgMrow_zc_mul(invp, V, i), mak);
  for (j=1; j<=k; j++)
  {
    GEN c = gel(invp,j), ck = gel(c,k);
    if (gequal0(ck)) continue;
    gel(c,k) = gdiv(ck, ak);
    if (j==k)
      for (i=k+1; i<n; i++)
        gel(c,i) = gmul(gel(a,i), ck);
    else
      for (i=k+1; i<n; i++)
        gel(c,i) = gadd(gel(c,i), gmul(gel(a,i), ck));
  }
  return 1;
}

GEN
perf(GEN a)
{
  pari_sp av = avma;
  GEN u, L;
  long r, s, k, l, n = lg(a)-1;

  if (!n) return gen_0;
  if (typ(a) != t_MAT || !RgM_is_ZM(a)) pari_err_TYPE("qfperfection",a);
  a = minim_lll(a, &u);
  L = minim_raw(a,NULL,NULL);
  r = (n*(n+1)) >> 1;
  if (L)
  {
    GEN D, V, invp;
    L = gel(L, 3); l = lg(L);
    if (l == 2) { avma = av; return gen_1; }

    D = zero_zv(r);
    V = cgetg(r+1, t_VECSMALL);
    invp = matid(r);
    s = 0;
    for (k = 1; k < l; k++)
    {
      pari_sp av2 = avma;
      GEN x = gel(L,k);
      long i, j, I;
      for (i = I = 1; i<=n; i++)
        for (j=i; j<=n; j++,I++) V[I] = x[i]*x[j];
      if (!addcolumntomatrix(V,invp,D)) avma = av2;
      else if (++s == r) break;
    }
  }
  else
  {
    GEN M;
    L = fincke_pohst(a,NULL,-1, DEFAULTPREC, NULL);
    if (!L) pari_err_PREC("qfminim");
    L = gel(L, 3); l = lg(L);
    if (l == 2) { avma = av; return gen_1; }
    M = cgetg(l, t_MAT);
    for (k = 1; k < l; k++)
    {
      GEN x = gel(L,k), c = cgetg(r+1, t_COL);
      long i, I, j;
      for (i = I = 1; i<=n; i++)
        for (j=i; j<=n; j++,I++) gel(c,I) = mulii(gel(x,i), gel(x,j));
      gel(M,k) = c;
    }
    s = ZM_rank(M);
  }
 avma = av; return utoipos(s);
}

static GEN
clonefill(GEN S, long s, long t)
{ /* initialize to dummy values */
  GEN T = S, dummy = cgetg(1, t_STR);
  long i;
  for (i = s+1; i <= t; i++) gel(S,i) = dummy;
  S = gclone(S); if (isclone(T)) gunclone(T);
  return S;
}

/* increment ZV x, by incrementing cell of index k. Initial value x0[k] was
 * chosen to minimize qf(x) for given x0[1..k-1] and x0[k+1,..] = 0
 * The last non-zero entry must be positive and goes through x0[k]+1,2,3,...
 * Others entries go through: x0[k]+1,-1,2,-2,...*/
INLINE void
step(GEN x, GEN y, GEN inc, long k)
{
  if (!signe(gel(y,k))) /* x[k+1..] = 0 */
    gel(x,k) = addiu(gel(x,k), 1); /* leading coeff > 0 */
  else
  {
    long i = inc[k];
    gel(x,k) = addis(gel(x,k), i),
    inc[k] = (i > 0)? -1-i: 1-i;
  }
}

/* 1 if we are "sure" that x < y, up to few rounding errors, i.e.
 * x < y - epsilon. More precisely :
 * - sign(x - y) < 0
 * - lgprec(x-y) > 3 || expo(x - y) - expo(x) > -24 */
static int
mplessthan(GEN x, GEN y)
{
  pari_sp av = avma;
  GEN z = mpsub(x, y);
  avma = av;
  if (typ(z) == t_INT) return (signe(z) < 0);
  if (signe(z) >= 0) return 0;
  if (realprec(z) > LOWDEFAULTPREC) return 1;
  return ( expo(z) - mpexpo(x) > -24 );
}

/* 1 if we are "sure" that x > y, up to few rounding errors, i.e.
 * x > y + epsilon */
static int
mpgreaterthan(GEN x, GEN y)
{
  pari_sp av = avma;
  GEN z = mpsub(x, y);
  avma = av;
  if (typ(z) == t_INT) return (signe(z) > 0);
  if (signe(z) <= 0) return 0;
  if (realprec(z) > LOWDEFAULTPREC) return 1;
  return ( expo(z) - mpexpo(x) > -24 );
}

/* x a t_INT, y  t_INT or t_REAL */
INLINE GEN
mulimp(GEN x, GEN y)
{
  if (typ(y) == t_INT) return mulii(x,y);
  return signe(x) ? mulir(x,y): gen_0;
}
/* x + y*z, x,z two mp's, y a t_INT */
INLINE GEN
addmulimp(GEN x, GEN y, GEN z)
{
  if (!signe(y)) return x;
  if (typ(z) == t_INT) return mpadd(x, mulii(y, z));
  return mpadd(x, mulir(y, z));
}

/* yk + vk * (xk + zk)^2 */
static GEN
norm_aux(GEN xk, GEN yk, GEN zk, GEN vk)
{
  GEN t = mpadd(xk, zk);
  if (typ(t) == t_INT) { /* probably gen_0, avoid loss of accuracy */
    yk = addmulimp(yk, sqri(t), vk);
  } else {
    yk = mpadd(yk, mpmul(sqrr(t), vk));
  }
  return yk;
}
/* yk + vk * (xk + zk)^2 < B + epsilon */
static int
check_bound(GEN B, GEN xk, GEN yk, GEN zk, GEN vk)
{
  pari_sp av = avma;
  int f = mpgreaterthan(norm_aux(xk,yk,zk,vk), B);
  avma = av; return !f;
}

/* q(k-th canonical basis vector), where q is given in Cholesky form
 * q(x) = sum_{i = 1}^n q[i,i] (x[i] + sum_{j > i} q[i,j] x[j])^2.
 * Namely q(e_k) = q[k,k] + sum_{i < k} q[i,i] q[i,k]^2
 * Assume 1 <= k <= n. */
static GEN
cholesky_norm_ek(GEN q, long k)
{
  GEN t = gcoeff(q,k,k);
  long i;
  for (i = 1; i < k; i++) t = norm_aux(gen_0, t, gcoeff(q,i,k), gcoeff(q,i,i));
  return t;
}

/* q is the Cholesky decomposition of a quadratic form
 * Enumerate vectors whose norm is less than BORNE (Algo 2.5.7),
 * minimal vectors if BORNE = NULL (implies check = NULL).
 * If (check != NULL) consider only vectors passing the check, and assumes
 *   we only want the smallest possible vectors */
static GEN
smallvectors(GEN q, GEN BORNE, long maxnum, FP_chk_fun *CHECK)
{
  long N = lg(q), n = N-1, i, j, k, s, stockmax, checkcnt = 1;
  pari_sp av, av1;
  GEN inc, S, x, y, z, v, p1, alpha, norms;
  GEN norme1, normax1, borne1, borne2;
  GEN (*check)(void *,GEN) = CHECK? CHECK->f: NULL;
  void *data = CHECK? CHECK->data: NULL;
  const long skipfirst = CHECK? CHECK->skipfirst: 0;
  const int stockall = (maxnum == -1);

  alpha = dbltor(0.95);
  normax1 = gen_0;

  v = cgetg(N,t_VEC);
  inc = const_vecsmall(n, 1);

  av = avma;
  stockmax = stockall? 2000: maxnum;
  norms = cgetg(check?(stockmax+1): 1,t_VEC); /* unused if (!check) */
  S = cgetg(stockmax+1,t_VEC);
  x = cgetg(N,t_COL);
  y = cgetg(N,t_COL);
  z = cgetg(N,t_COL);
  for (i=1; i<N; i++) {
    gel(v,i) = gcoeff(q,i,i);
    gel(x,i) = gel(y,i) = gel(z,i) = gen_0;
  }
  if (BORNE)
  {
    borne1 = BORNE;
    if (typ(borne1) != t_REAL)
    {
      long prec;
      if (gequal0(borne1)) retmkvec3(gen_0, gen_0, cgetg(1,t_MAT));
      prec = nbits2prec(gexpo(borne1) + 10);
      borne1 = gtofp(borne1, maxss(prec, DEFAULTPREC));
    }
  }
  else
  {
    borne1 = gcoeff(q,1,1);
    for (i=2; i<N; i++)
    {
      GEN b = cholesky_norm_ek(q, i);
      if (gcmp(b, borne1) < 0) borne1 = b;
    }
    /* borne1 = norm of smallest basis vector */
  }
  borne2 = mulrr(borne1,alpha);
  if (DEBUGLEVEL>2)
    err_printf("smallvectors looking for norm < %P.4G\n",borne1);
  s = 0; k = n;
  for(;; step(x,y,inc,k)) /* main */
  { /* x (supposedly) small vector, ZV.
     * For all t >= k, we have
     *   z[t] = sum_{j > t} q[t,j] * x[j]
     *   y[t] = sum_{i > t} q[i,i] * (x[i] + z[i])^2
     *        = 0 <=> x[i]=0 for all i>t */
    do
    {
      int skip = 0;
      if (k > 1)
      {
        long l = k-1;
        av1 = avma;
        p1 = mulimp(gel(x,k), gcoeff(q,l,k));
        for (j=k+1; j<N; j++) p1 = addmulimp(p1, gel(x,j), gcoeff(q,l,j));
        gel(z,l) = gerepileuptoleaf(av1,p1);

        av1 = avma;
        p1 = norm_aux(gel(x,k), gel(y,k), gel(z,k), gel(v,k));
        gel(y,l) = gerepileuptoleaf(av1, p1);
        /* skip the [x_1,...,x_skipfirst,0,...,0] */
        if ((l <= skipfirst && !signe(gel(y,skipfirst)))
         || mplessthan(borne1, gel(y,l))) skip = 1;
        else /* initial value, minimizing (x[l] + z[l])^2, hence qf(x) for
                the given x[1..l-1] */
          gel(x,l) = mpround( mpneg(gel(z,l)) );
        k = l;
      }
      for(;; step(x,y,inc,k))
      { /* at most 2n loops */
        if (!skip)
        {
          if (check_bound(borne1, gel(x,k),gel(y,k),gel(z,k),gel(v,k))) break;
          step(x,y,inc,k);
          if (check_bound(borne1, gel(x,k),gel(y,k),gel(z,k),gel(v,k))) break;
        }
        skip = 0; inc[k] = 1;
        if (++k > n) goto END;
      }

      if (gc_needed(av,2))
      {
        if(DEBUGMEM>1) pari_warn(warnmem,"smallvectors");
        if (stockmax) S = clonefill(S, s, stockmax);
        if (check) {
          GEN dummy = cgetg(1, t_STR);
          for (i=s+1; i<=stockmax; i++) gel(norms,i) = dummy;
        }
        gerepileall(av,7,&x,&y,&z,&normax1,&borne1,&borne2,&norms);
      }
    }
    while (k > 1);
    if (!signe(gel(x,1)) && !signe(gel(y,1))) continue; /* exclude 0 */

    av1 = avma;
    norme1 = norm_aux(gel(x,1),gel(y,1),gel(z,1),gel(v,1));
    if (mpgreaterthan(norme1,borne1)) { avma = av1; continue; /* main */ }

    norme1 = gerepileuptoleaf(av1,norme1);
    if (check)
    {
      if (checkcnt < 5 && mpcmp(norme1, borne2) < 0)
      {
        if (!check(data,x)) { checkcnt++ ; continue; /* main */}
        if (DEBUGLEVEL>4) err_printf("New bound: %Ps", norme1);
        borne1 = norme1;
        borne2 = mulrr(borne1, alpha);
        s = 0; checkcnt = 0;
      }
    }
    else
    {
      if (!BORNE) /* find minimal vectors */
      {
        if (mplessthan(norme1, borne1))
        { /* strictly smaller vector than previously known */
          borne1 = norme1; /* + epsilon */
          s = 0;
        }
      }
      else
        if (mpcmp(norme1,normax1) > 0) normax1 = norme1;
    }
    if (++s > stockmax) continue; /* too many vectors: no longer remember */
    if (check) gel(norms,s) = norme1;
    gel(S,s) = leafcopy(x);
    if (s != stockmax) continue; /* still room, get next vector */

    if (check)
    { /* overflow, eliminate vectors failing "check" */
      pari_sp av2 = avma;
      long imin, imax;
      GEN per = indexsort(norms), S2 = cgetg(stockmax+1, t_VEC);
      if (DEBUGLEVEL>2) err_printf("sorting... [%ld elts]\n",s);
      /* let N be the minimal norm so far for x satisfying 'check'. Keep
       * all elements of norm N */
      for (i = 1; i <= s; i++)
      {
        long k = per[i];
        if (check(data,gel(S,k))) { borne1 = gel(norms,k); break; }
      }
      imin = i;
      for (; i <= s; i++)
        if (mpgreaterthan(gel(norms,per[i]), borne1)) break;
      imax = i;
      for (i=imin, s=0; i < imax; i++) gel(S2,++s) = gel(S,per[i]);
      for (i = 1; i <= s; i++) gel(S,i) = gel(S2,i);
      avma = av2;
      if (s) { borne2 = mulrr(borne1, alpha); checkcnt = 0; }
      if (!stockall) continue;
      if (s > stockmax/2) stockmax <<= 1;
      norms = cgetg(stockmax+1, t_VEC);
      for (i = 1; i <= s; i++) gel(norms,i) = borne1;
    }
    else
    {
      if (!stockall && BORNE) goto END;
      if (!stockall) continue;
      stockmax <<= 1;
    }

    {
      GEN Snew = clonefill(vec_lengthen(S,stockmax), s, stockmax);
      if (isclone(S)) gunclone(S);
      S = Snew;
    }
  }
END:
  if (s < stockmax) stockmax = s;
  if (check)
  {
    GEN per, alph, pols, p;
    if (DEBUGLEVEL>2) err_printf("final sort & check...\n");
    setlg(norms,stockmax+1); per = indexsort(norms);
    alph = cgetg(stockmax+1,t_VEC);
    pols = cgetg(stockmax+1,t_VEC);
    for (j=0,i=1; i<=stockmax; i++)
    {
      long t = per[i];
      GEN N = gel(norms,t);
      if (j && mpgreaterthan(N, borne1)) break;
      if ((p = check(data,gel(S,t))))
      {
        if (!j) borne1 = N;
        j++;
        gel(pols,j) = p;
        gel(alph,j) = gel(S,t);
      }
    }
    setlg(pols,j+1);
    setlg(alph,j+1);
    if (stockmax && isclone(S)) { alph = gcopy(alph); gunclone(S); }
    return mkvec2(pols, alph);
  }
  if (stockmax)
  {
    setlg(S,stockmax+1);
    settyp(S,t_MAT);
    if (isclone(S)) { p1 = S; S = gcopy(S); gunclone(p1); }
  }
  else
    S = cgetg(1,t_MAT);
  return mkvec3(utoi(s<<1), borne1, S);
}

/* solve q(x) = x~.a.x <= bound, a > 0.
 * If check is non-NULL keep x only if check(x).
 * If a is a vector, assume a[1] is the LLL-reduced Cholesky form of q */
GEN
fincke_pohst(GEN a, GEN B0, long stockmax, long PREC, FP_chk_fun *CHECK)
{
  pari_sp av = avma;
  VOLATILE long i,j,l;
  VOLATILE GEN r,rinv,rinvtrans,u,v,res,z,vnorm,rperm,perm,uperm, bound = B0;

  if (typ(a) == t_VEC)
  {
    r = gel(a,1);
    u = NULL;
  }
  else
  {
    long prec = PREC;
    l = lg(a);
    if (l == 1)
    {
      if (CHECK) pari_err_TYPE("fincke_pohst [dimension 0]", a);
      retmkvec3(gen_0, gen_0, cgetg(1,t_MAT));
    }
    u = lllfp(a, 0.75, LLL_GRAM);
    if (lg(u) != lg(a)) return NULL;
    r = qf_apply_RgM(a,u);
    i = gprecision(r);
    if (i)
      prec = i;
    else {
      prec = DEFAULTPREC + nbits2extraprec(gexpo(r));
      if (prec < PREC) prec = PREC;
    }
    if (DEBUGLEVEL>2) err_printf("first LLL: prec = %ld\n", prec);
    r = qfgaussred_positive(r);
    if (!r) return NULL;
    for (i=1; i<l; i++)
    {
      GEN s = gsqrt(gcoeff(r,i,i), prec);
      gcoeff(r,i,i) = s;
      for (j=i+1; j<l; j++) gcoeff(r,i,j) = gmul(s, gcoeff(r,i,j));
    }
  }
  /* now r~ * r = a in LLL basis */
  rinv = RgM_inv_upper(r);
  if (!rinv) return NULL;
  rinvtrans = shallowtrans(rinv);
  if (DEBUGLEVEL>2)
    err_printf("Fincke-Pohst, final LLL: prec = %ld\n", gprecision(rinvtrans));
  v = lll(rinvtrans);
  if (lg(v) != lg(rinvtrans)) return NULL;

  rinvtrans = RgM_mul(rinvtrans, v);
  v = ZM_inv(shallowtrans(v),NULL);
  r = RgM_mul(r,v);
  u = u? ZM_mul(u,v): v;

  l = lg(r);
  vnorm = cgetg(l,t_VEC);
  for (j=1; j<l; j++) gel(vnorm,j) = gnorml2(gel(rinvtrans,j));
  rperm = cgetg(l,t_MAT);
  uperm = cgetg(l,t_MAT); perm = indexsort(vnorm);
  for (i=1; i<l; i++) { uperm[l-i] = u[perm[i]]; rperm[l-i] = r[perm[i]]; }
  u = uperm;
  r = rperm; res = NULL;
  pari_CATCH(e_PREC) { }
  pari_TRY {
    GEN q;
    if (CHECK && CHECK->f_init) bound = CHECK->f_init(CHECK, r, u);
    q = gaussred_from_QR(r, gprecision(vnorm));
    if (!q) pari_err_PREC("fincke_pohst");
    res = smallvectors(q, bound, stockmax, CHECK);
  } pari_ENDCATCH;
  if (CHECK)
  {
    if (CHECK->f_post) res = CHECK->f_post(CHECK, res, u);
    return res;
  }
  if (!res) pari_err_PREC("fincke_pohst");

  z = cgetg(4,t_VEC);
  gel(z,1) = gcopy(gel(res,1));
  gel(z,2) = gcopy(gel(res,2));
  gel(z,3) = ZM_mul(u, gel(res,3)); return gerepileupto(av,z);
}
