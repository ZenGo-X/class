/* Copyright (C) 2016  The PARI group.

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
/**                                                               **/
/**           Isomorphisms between finite fields                  **/
/**                                                               **/
/*******************************************************************/
static void
err_Flxq(const char *s, GEN P, ulong l)
{
  if (!uisprime(l)) pari_err_PRIME(s, utoi(l));
  pari_err_IRREDPOL(s, Flx_to_ZX(get_Flx_mod(P)));
}
static void
err_FpXQ(const char *s, GEN P, GEN l)
{
  if (!BPSW_psp(l)) pari_err_PRIME(s, l);
  pari_err_IRREDPOL(s, get_FpX_mod(P));
}

/* compute the reciprocical isomorphism of S mod T,p, i.e. V such that
   V(S)=X  mod T,p*/
GEN
Flxq_ffisom_inv(GEN S,GEN T, ulong p)
{
  pari_sp ltop = avma;
  long n = get_Flx_degree(T);
  GEN M = Flxq_matrix_pow(S,n,n,T,p);
  GEN V = Flm_Flc_invimage(M, vecsmall_ei(n, 2), p);
  if (!V) err_Flxq("Flxq_ffisom_inv", T, p);
  return gerepileupto(ltop, Flv_to_Flx(V, get_Flx_var(T)));
}

GEN
FpXQ_ffisom_inv(GEN S,GEN T, GEN p)
{
  pari_sp ltop = avma;
  long n = get_FpX_degree(T);
  GEN M = FpXQ_matrix_pow(S,n,n,T,p);
  GEN V = FpM_FpC_invimage(M, col_ei(n, 2), p);
  if (!V) err_FpXQ("Flxq_ffisom_inv", T, p);
  return gerepilecopy(ltop, RgV_to_RgX(V, get_FpX_var(T)));
}

/* Let M the matrix of the Frobenius automorphism of Fp[X]/(T). Compute M^d
 * TODO: use left-right binary (tricky!) */
GEN
Flm_Frobenius_pow(GEN M, long d, GEN T, ulong p)
{
  pari_sp ltop=avma;
  long i,l = get_Flx_degree(T);
  GEN R, W = gel(M,2);
  for (i = 2; i <= d; ++i) W = Flm_Flc_mul(M,W,p);
  R=Flxq_matrix_pow(Flv_to_Flx(W,get_Flx_var(T)),l,l,T,p);
  return gerepileupto(ltop,R);
}

GEN
FpM_Frobenius_pow(GEN M, long d, GEN T, GEN p)
{
  pari_sp ltop=avma;
  long i,l = get_FpX_degree(T);
  GEN R, W = gel(M,2);
  for (i = 2; i <= d; ++i) W = FpM_FpC_mul(M,W,p);
  R=FpXQ_matrix_pow(RgV_to_RgX(W, get_FpX_var(T)),l,l,T,p);
  return gerepilecopy(ltop,R);
}

/* Essentially we want to compute FqM_ker(MA-pol_x(v),U,l)
 * To avoid use of matrix in Fq we compute FpM_ker(U(MA),l) then recover the
 * eigenvalue by Galois action */
static GEN
Flx_Flm_Flc_eval(GEN U, GEN MA, GEN a, ulong p)
{
  long i, l = lg(U);
  GEN b = Flv_Fl_mul(a, uel(U, l-1), p);
  for (i=l-2; i>=2; i--)
    b = Flv_add(Flm_Flc_mul(MA, b, p), Flv_Fl_mul(a, uel(U, i), p), p);
  return b;
}

static GEN
Flx_intersect_ker(GEN P, GEN MA, GEN U, ulong p)
{
  pari_sp ltop = avma;
  long i, vp = get_Flx_var(P), vu = get_Flx_var(U), r = get_Flx_degree(U);
  GEN V, A, R;
  ulong ib0;
  pari_timer T;
  if (DEBUGLEVEL>=4) timer_start(&T);
  V = Flx_div(Flx_Fl_add(monomial_Flx(1, get_Flx_degree(P), vu), p-1, p), U, p);
  do
  {
    A = Flx_Flm_Flc_eval(V, MA, random_Flv(lg(MA)-1, p), p);
  } while (zv_equal0(A));
  if (DEBUGLEVEL>=4) timer_printf(&T,"matrix polcyclo");
  /*The formula is
   * a_{r-1} = -\phi(a_0)/b_0
   * a_{i-1} = \phi(a_i)+b_ia_{r-1}  i=r-1 to 1
   * Where a_0=A[1] and b_i=U[i+2] */
  ib0 = Fl_inv(Fl_neg(U[2], p), p);
  R = cgetg(r+1,t_MAT);
  gel(R,1) = A;
  gel(R,r) = Flm_Flc_mul(MA, Flv_Fl_mul(A,ib0, p), p);
  for(i=r-1; i>1; i--)
  {
    gel(R,i) = Flm_Flc_mul(MA,gel(R,i+1),p);
    Flv_add_inplace(gel(R,i), Flv_Fl_mul(gel(R,r), U[i+2], p), p);
  }
  return gerepileupto(ltop, Flm_to_FlxX(Flm_transpose(R),vp,vu));
}

static GEN
FpX_FpM_FpC_eval(GEN U, GEN MA, GEN a, GEN p)
{
  long i, l = lg(U);
  GEN b = FpC_Fp_mul(a, gel(U, l-1), p);
  for (i=l-2; i>=2; i--)
    b = FpC_add(FpM_FpC_mul(MA, b, p), FpC_Fp_mul(a, gel(U, i), p), p);
  return b;
}

static GEN
FpX_intersect_ker(GEN P, GEN MA, GEN U, GEN l)
{
  pari_sp ltop = avma;
  long i, vp = get_FpX_var(P), vu = get_FpX_var(U), r = get_FpX_degree(U);
  GEN V, A, R, ib0;
  pari_timer T;
  if (DEBUGLEVEL>=4) timer_start(&T);
  V = FpX_div(FpX_Fp_sub(pol_xn(get_FpX_degree(P), vu), gen_1, l), U, l);
  do
  {
    A = FpX_FpM_FpC_eval(V, MA, random_FpC(lg(MA)-1, l), l);
  } while (ZV_equal0(A));
  if (DEBUGLEVEL>=4) timer_printf(&T,"matrix polcyclo");
  /*The formula is
   * a_{r-1} = -\phi(a_0)/b_0
   * a_{i-1} = \phi(a_i)+b_ia_{r-1}  i=r-1 to 1
   * Where a_0=A[1] and b_i=U[i+2] */
  ib0 = Fp_inv(negi(gel(U,2)),l);
  R = cgetg(r+1,t_MAT);
  gel(R,1) = A;
  gel(R,r) = FpM_FpC_mul(MA, FpC_Fp_mul(A,ib0,l), l);
  for(i=r-1;i>1;i--)
    gel(R,i) = FpC_add(FpM_FpC_mul(MA,gel(R,i+1),l),
        FpC_Fp_mul(gel(R,r), gel(U,i+2), l),l);
  return gerepilecopy(ltop,RgM_to_RgXX(shallowtrans(R),vp,vu));
}

/* n must divide both the degree of P and Q.  Compute SP and SQ such
 * that the subfield of FF_l[X]/(P) generated by SP and the subfield of
 * FF_l[X]/(Q) generated by SQ are isomorphic of degree n.  P and Q do
 * not need to be of the same variable; if MA, resp. MB, is not NULL, must be
 * the matrix of the Frobenius map in FF_l[X]/(P), resp. FF_l[X]/(Q).
 * Implementation choice:  we assume the prime p is large so we handle
 * Frobenius as matrices. */
void
Flx_ffintersect(GEN P, GEN Q, long n, ulong l,GEN *SP, GEN *SQ, GEN MA, GEN MB)
{
  pari_sp ltop = avma;
  long vp = get_Flx_var(P), vq =  get_Flx_var(Q);
  long np = get_Flx_degree(P), nq = get_Flx_degree(Q), e;
  ulong pg;
  GEN A, B, Ap, Bp;
  if (np<=0) pari_err_IRREDPOL("FpX_ffintersect", P);
  if (nq<=0) pari_err_IRREDPOL("FpX_ffintersect", Q);
  if (n<=0 || np%n || nq%n)
    pari_err_TYPE("FpX_ffintersect [bad degrees]",stoi(n));
  e = u_lvalrem(n, l, &pg);
  if(!MA) MA = Flx_matFrobenius(P,l);
  if(!MB) MB = Flx_matFrobenius(Q,l);
  A = Ap = pol0_Flx(vp);
  B = Bp = pol0_Flx(vq);
  if (pg > 1)
  {
    pari_timer T;
    GEN ipg = utoipos(pg);
    if (l%pg == 1)
    { /* more efficient special case */
      ulong L, z, An, Bn;
      z = Fl_neg(rootsof1_Fl(pg, l), l);
      if (DEBUGLEVEL>=4) timer_start(&T);
      A = Flm_ker(Flm_Fl_add(MA, z, l),l);
      if (lg(A)!=2) err_Flxq("FpX_ffintersect",P,l);
      A = Flv_to_Flx(gel(A,1),vp);

      B = Flm_ker(Flm_Fl_add(MB, z, l),l);
      if (lg(B)!=2) err_Flxq("FpX_ffintersect",Q,l);
      B = Flv_to_Flx(gel(B,1),vq);

      if (DEBUGLEVEL>=4) timer_printf(&T, "FpM_ker");
      An = Flxq_powu(A,pg,P,l)[2];
      Bn = Flxq_powu(B,pg,Q,l)[2];
      if (!Bn) pari_err_IRREDPOL("FpX_ffintersect", mkvec2(P,Q));
      z = Fl_div(An,Bn,l);
      L = Fl_sqrtn(z, pg, l, NULL);
      if (L==ULONG_MAX) pari_err_IRREDPOL("FpX_ffintersect", mkvec2(P,Q));
      if (DEBUGLEVEL>=4) timer_printf(&T, "Fp_sqrtn");
      B = Flx_Fl_mul(B,L,l);
    }
    else
    {
      GEN L, An, Bn, z, U;
      U = gmael(Flx_factor(ZX_to_Flx(polcyclo(pg, fetch_var()),l),l),1,1);
      A = Flx_intersect_ker(P, MA, U, l);
      B = Flx_intersect_ker(Q, MB, U, l);
      if (DEBUGLEVEL>=4) timer_start(&T);
      An = gel(FlxYqq_pow(A,ipg,P,U,l),2);
      Bn = gel(FlxYqq_pow(B,ipg,Q,U,l),2);
      if (DEBUGLEVEL>=4) timer_printf(&T,"pows [P,Q]");
      z = Flxq_div(An,Bn,U,l);
      L = Flxq_sqrtn(z,ipg,U,l,NULL);
      if (!L) pari_err_IRREDPOL("FpX_ffintersect", mkvec2(P,Q));
      if (DEBUGLEVEL>=4) timer_printf(&T,"FpXQ_sqrtn");
      B = FlxqX_Flxq_mul(B,L,U,l);
      A = FlxY_evalx(A,0,l);
      B = FlxY_evalx(B,0,l);
      (void)delete_var();
    }
  }
  if (e)
  {
    GEN VP, VQ, Ay, By;
    ulong lmun = l-1;
    long j;
    MA = Flm_Fl_add(MA,lmun,l);
    MB = Flm_Fl_add(MB,lmun,l);
    Ay = pol1_Flx(vp);
    By = pol1_Flx(vq);
    VP = vecsmall_ei(np, 1);
    VQ = np == nq? VP: vecsmall_ei(nq, 1); /* save memory */
    for(j=0;j<e;j++)
    {
      if (j)
      {
        Ay = Flxq_mul(Ay,Flxq_powu(Ap,lmun,P,l),P,l);
        VP = Flx_to_Flv(Ay,np);
      }
      Ap = Flm_Flc_invimage(MA,VP,l);
      if (!Ap) err_Flxq("FpX_ffintersect",P,l);
      Ap = Flv_to_Flx(Ap,vp);

      if (j)
      {
        By = Flxq_mul(By,Flxq_powu(Bp,lmun,Q,l),Q,l);
        VQ = Flx_to_Flv(By,nq);
      }
      Bp = Flm_Flc_invimage(MB,VQ,l);
      if (!Bp) err_Flxq("FpX_ffintersect",Q,l);
      Bp = Flv_to_Flx(Bp,vq);
    }
  }
  *SP = Flx_add(A,Ap,l);
  *SQ = Flx_add(B,Bp,l);
  gerepileall(ltop,2,SP,SQ);
}

/* Let l be a prime number, P, Q in Z[X]; both are irreducible modulo l and
 * degree(P) divides degree(Q).  Output a monomorphism between F_l[X]/(P) and
 * F_l[X]/(Q) as a polynomial R such that Q | P(R) mod l.  If P and Q have the
 * same degree, it is of course an isomorphism.  */
GEN
Flx_ffisom(GEN P,GEN Q,ulong l)
{
  pari_sp av = avma;
  GEN SP, SQ, R;
  Flx_ffintersect(P,Q,get_Flx_degree(P),l,&SP,&SQ,NULL,NULL);
  R = Flxq_ffisom_inv(SP,P,l);
  return gerepileupto(av, Flx_Flxq_eval(R,SQ,Q,l));
}

void
FpX_ffintersect(GEN P, GEN Q, long n, GEN l, GEN *SP, GEN *SQ, GEN MA, GEN MB)
{
  pari_sp ltop = avma;
  long vp, vq, np, nq, e;
  ulong pg;
  GEN A, B, Ap, Bp;
  if (lgefint(l)==3)
  {
    ulong pp = l[2];
    GEN Pp = ZX_to_Flx(P,pp), Qp = ZX_to_Flx(Q,pp);
    GEN MAp = MA ? ZM_to_Flm(MA, pp): NULL;
    GEN MBp = MB ? ZM_to_Flm(MB, pp): NULL;
    Flx_ffintersect(Pp, Qp, n, pp, SP, SQ, MAp, MBp);
    *SP = Flx_to_ZX(*SP); *SQ = Flx_to_ZX(*SQ);
    gerepileall(ltop,2,SP,SQ);
    return;
  }
  vp = get_FpX_var(P); np = get_FpX_degree(P);
  vq = get_FpX_var(Q); nq = get_FpX_degree(Q);
  if (np<=0) pari_err_IRREDPOL("FpX_ffintersect", P);
  if (nq<=0) pari_err_IRREDPOL("FpX_ffintersect", Q);
  if (n<=0 || np%n || nq%n)
    pari_err_TYPE("FpX_ffintersect [bad degrees]",stoi(n));
  e = u_pvalrem(n, l, &pg);
  if(!MA) MA = FpX_matFrobenius(P, l);
  if(!MB) MB = FpX_matFrobenius(Q, l);
  A = Ap = pol_0(vp);
  B = Bp = pol_0(vq);
  if (pg > 1)
  {
    GEN ipg = utoipos(pg);
    pari_timer T;
    if (umodiu(l,pg) == 1)
    /* No need to use relative extension, so don't. (Well, now we don't
     * in the other case either, but this special case is more efficient) */
    {
      GEN L, An, Bn, z;
      z = negi( rootsof1u_Fp(pg, l) );
      if (DEBUGLEVEL>=4) timer_start(&T);
      A = FpM_ker(RgM_Rg_add_shallow(MA, z),l);
      if (lg(A)!=2) err_FpXQ("FpX_ffintersect",P,l);
      A = RgV_to_RgX(gel(A,1),vp);

      B = FpM_ker(RgM_Rg_add_shallow(MB, z),l);
      if (lg(B)!=2) err_FpXQ("FpX_ffintersect",Q,l);
      B = RgV_to_RgX(gel(B,1),vq);

      if (DEBUGLEVEL>=4) timer_printf(&T, "FpM_ker");
      An = gel(FpXQ_pow(A,ipg,P,l),2);
      Bn = gel(FpXQ_pow(B,ipg,Q,l),2);
      if (!signe(Bn)) pari_err_IRREDPOL("FpX_ffintersect", mkvec2(P,Q));
      z = Fp_div(An,Bn,l);
      L = Fp_sqrtn(z,ipg,l,NULL);
      if (!L) pari_err_IRREDPOL("FpX_ffintersect", mkvec2(P,Q));
      if (DEBUGLEVEL>=4) timer_printf(&T, "Fp_sqrtn");
      B = FpX_Fp_mul(B,L,l);
    }
    else
    {
      GEN L, An, Bn, z, U;
      U = gmael(FpX_factor(polcyclo(pg,fetch_var()),l),1,1);
      A = FpX_intersect_ker(P, MA, U, l);
      B = FpX_intersect_ker(Q, MB, U, l);
      if (DEBUGLEVEL>=4) timer_start(&T);
      An = gel(FpXYQQ_pow(A,ipg,P,U,l),2);
      Bn = gel(FpXYQQ_pow(B,ipg,Q,U,l),2);
      if (DEBUGLEVEL>=4) timer_printf(&T,"pows [P,Q]");
      if (!signe(Bn)) pari_err_IRREDPOL("FpX_ffintersect", mkvec2(P,Q));
      z = Fq_div(An,Bn,U,l);
      L = Fq_sqrtn(z,ipg,U,l,NULL);
      if (!L) pari_err_IRREDPOL("FpX_ffintersect", mkvec2(P,Q));
      if (DEBUGLEVEL>=4) timer_printf(&T,"FpXQ_sqrtn");
      B = FqX_Fq_mul(B,L,U,l);
      A = FpXY_evalx(A,gen_0,l);
      B = FpXY_evalx(B,gen_0,l);
      (void)delete_var();
    }
  }
  if (e)
  {
    GEN VP, VQ, Ay, By, lmun = subiu(l,1);
    long j;
    MA = RgM_Rg_add_shallow(MA,gen_m1);
    MB = RgM_Rg_add_shallow(MB,gen_m1);
    Ay = pol_1(vp);
    By = pol_1(vq);
    VP = col_ei(np, 1);
    VQ = np == nq? VP: col_ei(nq, 1); /* save memory */
    for(j=0;j<e;j++)
    {
      if (j)
      {
        Ay = FpXQ_mul(Ay,FpXQ_pow(Ap,lmun,P,l),P,l);
        VP = RgX_to_RgC(Ay,np);
      }
      Ap = FpM_FpC_invimage(MA,VP,l);
      if (!Ap) err_FpXQ("FpX_ffintersect",P,l);
      Ap = RgV_to_RgX(Ap,vp);

      if (j)
      {
        By = FpXQ_mul(By,FpXQ_pow(Bp,lmun,Q,l),Q,l);
        VQ = RgX_to_RgC(By,nq);
      }
      Bp = FpM_FpC_invimage(MB,VQ,l);
      if (!Bp) err_FpXQ("FpX_ffintersect",Q,l);
      Bp = RgV_to_RgX(Bp,vq);
    }
  }
  *SP = FpX_add(A,Ap,l);
  *SQ = FpX_add(B,Bp,l);
  gerepileall(ltop,2,SP,SQ);
}
/* Let l be a prime number, P, Q in Z[X]; both are irreducible modulo l and
 * degree(P) divides degree(Q).  Output a monomorphism between F_l[X]/(P) and
 * F_l[X]/(Q) as a polynomial R such that Q | P(R) mod l.  If P and Q have the
 * same degree, it is of course an isomorphism.  */
GEN
FpX_ffisom(GEN P, GEN Q, GEN p)
{
  pari_sp av = avma;
  GEN SP, SQ, R;
  if (lgefint(p)==3)
  {
    ulong pp = p[2];
    GEN R = Flx_ffisom(ZX_to_Flx(P,pp), ZX_to_Flx(Q,pp), pp);
    return gerepileupto(av, Flx_to_ZX(R));
  }
  FpX_ffintersect(P,Q,get_FpX_degree(P),p,&SP,&SQ,NULL,NULL);
  R = FpXQ_ffisom_inv(SP,P,p);
  return gerepileupto(av, FpX_FpXQ_eval(R,SQ,Q,p));
}

/* Let l be a prime number, P a ZX irreducible modulo l, MP the matrix of the
 * Frobenius automorphism of F_l[X]/(P).
 * Factor P over the subfield of F_l[X]/(P) of index d. */
static GEN
FpX_factorgalois(GEN P, GEN l, long d, long w, GEN MP)
{
  pari_sp ltop = avma;
  GEN R, V, Tl, z, M;
  long v = get_FpX_var(P), n = get_FpX_degree(P);
  long k, m = n/d;

  /* x - y */
  if (m == 1) return deg1pol_shallow(gen_1, deg1pol_shallow(subis(l,1), gen_0, w), v);
  M = FpM_Frobenius_pow(MP,d,P,l);

  Tl = leafcopy(P); setvarn(Tl,w);
  V = cgetg(m+1,t_VEC);
  gel(V,1) = pol_x(w);
  z = gel(M,2);
  gel(V,2) = RgV_to_RgX(z,w);
  for(k=3;k<=m;k++)
  {
    z = FpM_FpC_mul(M,z,l);
    gel(V,k) = RgV_to_RgX(z,w);
  }
  R = FqV_roots_to_pol(V,Tl,l,v);
  return gerepileupto(ltop,R);
}
/* same: P is an Flx, MP an Flm */
static GEN
Flx_factorgalois(GEN P, ulong l, long d, long w, GEN MP)
{
  pari_sp ltop = avma;
  GEN R, V, Tl, z, M;
  long k, n = get_Flx_degree(P), m = n/d;
  long v = get_Flx_var(P);

  if (m == 1) {
    R = polx_Flx(v);
    gel(R,2) = z = polx_Flx(w); z[3] = l - 1; /* - y */
    gel(R,3) = pol1_Flx(w);
    return R; /* x - y */
  }
  M = Flm_Frobenius_pow(MP,d,P,l);

  Tl = leafcopy(P); setvarn(Tl,w);
  V = cgetg(m+1,t_VEC);
  gel(V,1) = polx_Flx(w);
  z = gel(M,2);
  gel(V,2) = Flv_to_Flx(z,w);
  for(k=3;k<=m;k++)
  {
    z = Flm_Flc_mul(M,z,l);
    gel(V,k) = Flv_to_Flx(z,w);
  }
  R = FlxqV_roots_to_pol(V,Tl,l,v);
  return gerepileupto(ltop,R);
}

GEN
Flx_factorff_irred(GEN P, GEN Q, ulong p)
{
  pari_sp ltop = avma, av;
  GEN SP, SQ, MP, MQ, M, FP, FQ, E, V, IR, res;
  long np = get_Flx_degree(P), nq = get_Flx_degree(Q), d = ugcd(np,nq);
  long i, vp = get_Flx_var(P), vq = get_Flx_var(Q);
  if (d==1) retmkcol(Flx_to_FlxX(P, vq));
  FQ = Flx_matFrobenius(Q,p);
  av = avma;
  FP = Flx_matFrobenius(P,p);
  Flx_ffintersect(P,Q,d,p,&SP,&SQ, FP, FQ);
  E = Flx_factorgalois(P,p,d,vq, FP);
  E = FlxX_to_Flm(E,np);
  MP= Flxq_matrix_pow(SP,np,d,P,p);
  IR= gel(Flm_indexrank(MP,p),1);
  E = rowpermute(E, IR);
  M = rowpermute(MP,IR);
  M = Flm_inv(M,p);
  MQ= Flxq_matrix_pow(SQ,nq,d,Q,p);
  M = Flm_mul(MQ,M,p);
  M = Flm_mul(M,E,p);
  M = gerepileupto(av,M);
  V = cgetg(d+1,t_VEC);
  gel(V,1) = M;
  for(i=2;i<=d;i++)
    gel(V,i) = Flm_mul(FQ,gel(V,i-1),p);
  res = cgetg(d+1,t_COL);
  for(i=1;i<=d;i++)
    gel(res,i) = Flm_to_FlxX(gel(V,i),vp,vq);
  return gerepileupto(ltop,res);
}

/* P,Q irreducible over F_p. Factor P over FF_p[X] / Q  [factors are ordered as
 * a Frobenius cycle] */
GEN
FpX_factorff_irred(GEN P, GEN Q, GEN p)
{
  pari_sp ltop = avma, av;
  GEN res;
  long np = get_FpX_degree(P), nq = get_FpX_degree(Q), d = ugcd(np,nq);
  if (d==1) return mkcolcopy(P);

  if (lgefint(p)==3)
  {
    ulong pp = p[2];
    GEN F = Flx_factorff_irred(ZX_to_Flx(P,pp), ZX_to_Flx(Q,pp), pp);
    long i, lF = lg(F);
    res = cgetg(lF, t_COL);
    for(i=1; i<lF; i++)
      gel(res,i) = FlxX_to_ZXX(gel(F,i));
  }
  else
  {
    GEN SP, SQ, MP, MQ, M, FP, FQ, E, V, IR;
    long i, vp = get_FpX_var(P), vq = get_FpX_var(Q);
    FQ = FpX_matFrobenius(Q,p);
    av = avma;
    FP = FpX_matFrobenius(P,p);
    FpX_ffintersect(P,Q,d,p,&SP,&SQ,FP,FQ);

    E = FpX_factorgalois(P,p,d,vq,FP);
    E = RgXX_to_RgM(E,np);
    MP= FpXQ_matrix_pow(SP,np,d,P,p);
    IR= gel(FpM_indexrank(MP,p),1);
    E = rowpermute(E, IR);
    M = rowpermute(MP,IR);
    M = FpM_inv(M,p);
    MQ= FpXQ_matrix_pow(SQ,nq,d,Q,p);
    M = FpM_mul(MQ,M,p);
    M = FpM_mul(M,E,p);
    M = gerepileupto(av,M);
    V = cgetg(d+1,t_VEC);
    gel(V,1) = M;
    for(i=2;i<=d;i++)
      gel(V,i) = FpM_mul(FQ,gel(V,i-1),p);
    res = cgetg(d+1,t_COL);
    for(i=1;i<=d;i++)
      gel(res,i) = RgM_to_RgXX(gel(V,i),vp,vq);
  }
  return gerepilecopy(ltop,res);
}

/* not memory-clean, as Flx_factorff_i, returning only linear factors */
static GEN
Flx_rootsff_i(GEN P, GEN T, ulong p)
{
  GEN V, F = gel(Flx_factor(P,p), 1);
  long i, lfact = 1, nmax = lgpol(P), n = lg(F), dT = get_Flx_degree(T);

  V = cgetg(nmax,t_COL);
  for(i=1;i<n;i++)
  {
    GEN R, Fi = gel(F,i);
    long di = degpol(Fi), j, r;
    if (dT % di) continue;
    R = Flx_factorff_irred(gel(F,i),T,p);
    r = lg(R);
    for (j=1; j<r; j++,lfact++)
      gel(V,lfact) = Flx_neg(gmael(R,j, 2), p);
  }
  setlg(V,lfact);
  gen_sort_inplace(V, (void*) &cmp_Flx, &cmp_nodata, NULL);
  return V;
}
GEN
Flx_rootsff(GEN P, GEN T, ulong p)
{
  pari_sp av = avma;
  return gerepilecopy(av, Flx_rootsff_i(P, T, p));
}

/* dummy implementation */
static GEN
F2x_rootsff_i(GEN P, GEN T)
{
  return FlxC_to_F2xC(Flx_rootsff_i(F2x_to_Flx(P), F2x_to_Flx(T), 2UL));
}

/* not memory-clean, as FpX_factorff_i, returning only linear factors */
static GEN
FpX_rootsff_i(GEN P, GEN T, GEN p)
{
  GEN V, F;
  long i, lfact, nmax, n, dT;
  if (lgefint(p)==3)
  {
    ulong pp = p[2];
    GEN V = Flx_rootsff_i(ZX_to_Flx(P,pp), ZXT_to_FlxT(T,pp), pp);
    return FlxC_to_ZXC(V);
  }
  F = gel(FpX_factor(P,p), 1);
  lfact = 1; nmax = lgpol(P); n = lg(F); dT = get_FpX_degree(T);

  V = cgetg(nmax,t_COL);
  for(i=1;i<n;i++)
  {
    GEN R, Fi = gel(F,i);
    long di = degpol(Fi), j, r;
    if (dT % di) continue;
    R = FpX_factorff_irred(gel(F,i),T,p);
    r = lg(R);
    for (j=1; j<r; j++,lfact++)
      gel(V,lfact) = Fq_to_FpXQ(Fq_neg(gmael(R,j, 2), T, p), T, p);
  }
  setlg(V,lfact);
  gen_sort_inplace(V, (void*) &cmp_RgX, &cmp_nodata, NULL);
  return V;
}
GEN
FpX_rootsff(GEN P, GEN T, GEN p)
{
  pari_sp av = avma;
  return gerepilecopy(av, FpX_rootsff_i(P, T, p));
}

static GEN
Flx_factorff_i(GEN P, GEN T, ulong p)
{
  GEN V, E, F = Flx_factor(P, p);
  long i, lfact = 1, nmax = lgpol(P), n = lgcols(F);

  V = cgetg(nmax,t_VEC);
  E = cgetg(nmax,t_VECSMALL);
  for(i=1;i<n;i++)
  {
    GEN R = Flx_factorff_irred(gmael(F,1,i),T,p), e = gmael(F,2,i);
    long j, r = lg(R);
    for (j=1; j<r; j++,lfact++)
    {
      gel(V,lfact) = gel(R,j);
      gel(E,lfact) = e;
    }
  }
  setlg(V,lfact);
  setlg(E,lfact); return sort_factor_pol(mkvec2(V,E), cmp_Flx);
}

static long
simpleff_to_nbfact(GEN F, long dT)
{
  long i, l = lg(F), k = 0;
  for (i = 1; i < l; i++) k += ugcd(uel(F,i), dT);
  return k;
}

static long
Flx_nbfactff(GEN P, GEN T, ulong p)
{
  pari_sp av = avma;
  GEN F = gel(Flx_degfact(P, p), 1);
  long s = simpleff_to_nbfact(F, get_Flx_degree(T));
  avma = av; return s;
}

/* dummy implementation */
static GEN
F2x_factorff_i(GEN P, GEN T)
{
  GEN M = Flx_factorff_i(F2x_to_Flx(P), F2x_to_Flx(T), 2);
  return mkvec2(FlxXC_to_F2xXC(gel(M,1)), gel(M,2));
}

/* not memory-clean */
static GEN
FpX_factorff_i(GEN P, GEN T, GEN p)
{
  GEN V, E, F = FpX_factor(P,p);
  long i, lfact = 1, nmax = lgpol(P), n = lgcols(F);

  V = cgetg(nmax,t_VEC);
  E = cgetg(nmax,t_VECSMALL);
  for(i=1;i<n;i++)
  {
    GEN R = FpX_factorff_irred(gmael(F,1,i),T,p), e = gmael(F,2,i);
    long j, r = lg(R);
    for (j=1; j<r; j++,lfact++)
    {
      gel(V,lfact) = gel(R,j);
      gel(E,lfact) = e;
    }
  }
  setlg(V,lfact);
  setlg(E,lfact); return sort_factor_pol(mkvec2(V,E), cmp_RgX);
}

static long
FpX_nbfactff(GEN P, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN F = gel(FpX_degfact(P, p), 1);
  long s = simpleff_to_nbfact(F, get_FpX_degree(T));
  avma = av; return s;
}

GEN
FpX_factorff(GEN P, GEN T, GEN p)
{
  pari_sp av = avma;
  return gerepilecopy(av, FpX_factorff_i(P, T, p));
}

/***********************************************************************/
/**                                                                   **/
/**               Factorisation over finite fields                    **/
/**                                                                   **/
/***********************************************************************/

static GEN
FlxqXQ_halfFrobenius_i(GEN a, GEN xp, GEN Xp, GEN S, GEN T, ulong p)
{
  GEN ap2 = FlxqXQ_powu(a, p>>1, S, T, p);
  GEN V = FlxqXQ_autsum(mkvec3(xp, Xp, ap2), get_Flx_degree(T), S, T, p);
  return gel(V,3);
}

GEN
FlxqXQ_halfFrobenius(GEN a, GEN S, GEN T, ulong p)
{
  long vT = get_Flx_var(T);
  GEN xp, Xp;
  T = Flx_get_red(T, p);
  S = FlxqX_get_red(S, T, p);
  xp = Flx_Frobenius(T, p);
  Xp = FlxqXQ_powu(polx_FlxX(get_FlxqX_var(S), vT), p, S, T, p);
  return FlxqXQ_halfFrobenius_i(a, xp, Xp, S, T, p);
}

static GEN
FpXQXQ_halfFrobenius_i(GEN a, GEN xp, GEN Xp, GEN S, GEN T, GEN p)
{
  GEN ap2 = FpXQXQ_pow(a, shifti(p,-1), S, T, p);
  GEN V = FpXQXQ_autsum(mkvec3(xp, Xp, ap2), get_FpX_degree(T), S, T, p);
  return gel(V, 3);
}

GEN
FpXQXQ_halfFrobenius(GEN a, GEN S, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN z;
  if (lgefint(p)==3)
  {
    ulong pp = p[2];
    long v = get_FpX_var(T);
    GEN Tp = ZXT_to_FlxT(T,pp), Sp = ZXXT_to_FlxXT(S, pp, v);
    z = FlxX_to_ZXX(FlxqXQ_halfFrobenius(ZXX_to_FlxX(a,pp,v),Sp,Tp,pp));
  }
  else
  {
    GEN xp, Xp;
    T = FpX_get_red(T, p);
    S = FpXQX_get_red(S, T, p);
    xp = FpX_Frobenius(T, p);
    Xp = FpXQXQ_pow(pol_x(get_FpXQX_var(S)), p, S, T, p);
    z = FpXQXQ_halfFrobenius_i(a, xp, Xp, S, T, p);
  }
  return gerepilecopy(av, z);
}

static GEN
FlxqXQ_Frobenius(GEN xp, GEN Xp, GEN f, GEN T, ulong p)
{
  ulong dT = get_Flx_degree(T), df = get_FlxqX_degree(f);
  GEN q = powuu(p,dT);
  if (expi(q) >= expu(dT)*(long)usqrt(df))
    return gel(FlxqXQ_autpow(mkvec2(xp, Xp), dT, f, T, p), 2);
  else
    return FlxqXQ_pow(pol_x(get_FlxqX_var(f)), q, f, T, p);
}

GEN
FlxqX_Frobenius(GEN S, GEN T, ulong p)
{
  pari_sp av = avma;
  GEN X  = polx_FlxX(get_FlxqX_var(S), get_Flx_var(T));
  GEN xp = Flx_Frobenius(T, p);
  GEN Xp = FlxqXQ_powu(X, p, S, T, p);
  GEN Xq = FlxqXQ_Frobenius(xp, Xp, S, T, p);
  return gerepilecopy(av, Xq);
}

static GEN
FpXQXQ_Frobenius(GEN xp, GEN Xp, GEN f, GEN T, GEN p)
{
  ulong dT = get_FpX_degree(T), df = get_FpXQX_degree(f);
  GEN q = powiu(p, dT);
  if (expi(q) >= expu(dT)*(long)usqrt(df))
    return gel(FpXQXQ_autpow(mkvec2(xp, Xp), dT, f, T, p), 2);
  else
    return FpXQXQ_pow(pol_x(get_FpXQX_var(f)), q, f, T, p);
}

GEN
FpXQX_Frobenius(GEN S, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN X  = pol_x(get_FpXQX_var(S));
  GEN xp = FpX_Frobenius(T, p);
  GEN Xp = FpXQXQ_pow(X, p, S, T, p);
  GEN Xq = FpXQXQ_Frobenius(xp, Xp, S, T, p);
  return gerepilecopy(av, Xq);
}

static GEN
F2xqXQ_Frobenius(GEN xp, GEN Xp, GEN f, GEN T)
{
  ulong dT = get_F2x_degree(T), df = get_F2xqX_degree(f);
  if (dT >= expu(dT)*usqrt(df))
    return gel(F2xqXQ_autpow(mkvec2(xp, Xp), dT, f, T), 2);
  else
  {
    long v = get_F2xqX_var(f), vT = get_F2x_var(T);
    return F2xqXQ_pow(polx_F2xX(v,vT), int2n(dT), f, T);
  }
}

static GEN
FlxqX_split_part(GEN f, GEN T, ulong p)
{
  long n = degpol(f);
  GEN z, Xq, X = polx_FlxX(varn(f),get_Flx_var(T));
  if (n <= 1) return f;
  f = FlxqX_red(f, T, p);
  Xq = FlxqX_Frobenius(f, T, p);
  z = FlxX_sub(Xq, X , p);
  return FlxqX_gcd(z, f, T, p);
}

GEN
FpXQX_split_part(GEN f, GEN T, GEN p)
{
  if(lgefint(p)==3)
  {
    ulong pp=p[2];
    GEN Tp = ZXT_to_FlxT(T, pp);
    GEN z = FlxqX_split_part(ZXX_to_FlxX(f, pp, get_Flx_var(T)), Tp, pp);
    return FlxX_to_ZXX(z);
  } else
  {
    long n = degpol(f);
    GEN z, X = pol_x(varn(f));
    if (n <= 1) return f;
    f = FpXQX_red(f, T, p);
    z = FpXQX_Frobenius(f, T, p);
    z = FpXX_sub(z, X , p);
    return FpXQX_gcd(z, f, T, p);
  }
}

long
FpXQX_nbroots(GEN f, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN z = FpXQX_split_part(f, T, p);
  avma = av; return degpol(z);
}

long
FqX_nbroots(GEN f, GEN T, GEN p)
{ return T ? FpXQX_nbroots(f, T, p): FpX_nbroots(f, p); }

long
FlxqX_nbroots(GEN f, GEN T, ulong p)
{
  pari_sp av = avma;
  GEN z = FlxqX_split_part(f, T, p);
  avma = av; return degpol(z);
}

static GEN
FlxqX_Berlekamp_ker_i(GEN Xq, GEN S, GEN T, ulong p)
{
  long j, N = get_FlxqX_degree(S);
  GEN Q  = FlxqXQ_matrix_pow(Xq,N,N,S,T,p);
  for (j=1; j<=N; j++)
    gcoeff(Q,j,j) = Flx_Fl_add(gcoeff(Q,j,j), p-1, p);
  return FlxqM_ker(Q,T,p);
}

static GEN
FpXQX_Berlekamp_ker_i(GEN Xq, GEN S, GEN T, GEN p)
{
  long j,N = get_FpXQX_degree(S);
  GEN Q  = FpXQXQ_matrix_pow(Xq,N,N,S,T,p);
  for (j=1; j<=N; j++)
    gcoeff(Q,j,j) = Fq_sub(gcoeff(Q,j,j), gen_1, T, p);
  return FqM_ker(Q,T,p);
}

static long
isabsolutepol(GEN f)
{
  long i, l = lg(f);
  for(i=2; i<l; i++)
  {
    GEN c = gel(f,i);
    if (typ(c) == t_POL && degpol(c) > 0) return 0;
  }
  return 1;
}

#define set_irred(i) { if ((i)>ir) swap(t[i],t[ir]); ir++;}

static long
FlxqX_split_Berlekamp(GEN *t, GEN xp, GEN T, ulong p)
{
  GEN u = *t, a,b,vker,pol;
  long vu = varn(u), vT = get_Flx_var(T), dT = get_Flx_degree(T);
  long d, i, ir, L, la, lb;
  GEN S, X, Xp, Xq;
  if (degpol(u)==1) return 1;
  T = Flx_get_red(T, p);
  S = FlxqX_get_red(u, T, p);
  X  = polx_FlxX(get_FlxqX_var(S),get_Flx_var(T));
  Xp = FlxqXQ_powu(X, p, S, T, p);
  Xq = FlxqXQ_Frobenius(xp, Xp, S, T, p);
  vker = FlxqX_Berlekamp_ker_i(Xq, S, T, p);
  vker = Flm_to_FlxV(vker,u[1]);
  d = lg(vker)-1;
  ir = 0;
  /* t[i] irreducible for i < ir, still to be treated for i < L */
  for (L=1; L<d; )
  {
    pol= scalarpol(random_Flx(dT,vT,p),vu);
    for (i=2; i<=d; i++)
      pol = FlxX_add(pol, FlxqX_Flxq_mul(gel(vker,i),
                                         random_Flx(dT,vT,p), T, p), p);
    pol = FlxqX_red(pol,T,p);
    for (i=ir; i<L && L<d; i++)
    {
      a = t[i]; la = degpol(a);
      if (la == 1) { set_irred(i); }
      else
      {
        pari_sp av = avma;
        GEN S = FlxqX_get_red(a, T, p);
        b = FlxqX_rem(pol, S, T,p);
        if (degpol(b)<=0) { avma=av; continue; }
        b = FlxqXQ_halfFrobenius_i(b, xp, FlxqX_rem(Xp, S, T, p), S, T, p);
        if (degpol(b)<=0) { avma=av; continue; }
        gel(b,2) = Flxq_sub(gel(b,2), gen_1,T,p);
        b = FlxqX_gcd(a,b, T,p); lb = degpol(b);
        if (lb && lb < la)
        {
          b = FlxqX_normalize(b, T,p);
          t[L] = FlxqX_div(a,b,T,p);
          t[i]= b; L++;
        }
        else avma = av;
      }
    }
  }
  return d;
}


static long
FpXQX_split_Berlekamp(GEN *t, GEN T, GEN p)
{
  GEN u = *t, a, b, vker, pol;
  GEN X, xp, Xp, Xq, S;
  long vu = varn(u), vT = get_FpX_var(T), dT = get_FpX_degree(T);
  long d, i, ir, L, la, lb;
  if (degpol(u)==1) return 1;
  T = FpX_get_red(T, p);
  xp = FpX_Frobenius(T, p);
  S = FpXQX_get_red(u, T, p);
  X  = pol_x(get_FpXQX_var(S));
  Xp = FpXQXQ_pow(X, p, S, T, p);
  Xq = FpXQXQ_Frobenius(xp, Xp, S, T, p);
  vker = FpXQX_Berlekamp_ker_i(Xq, S, T, p);
  vker = RgM_to_RgXV(vker,vu);
  d = lg(vker)-1;
  ir = 0;
  /* t[i] irreducible for i < ir, still to be treated for i < L */
  for (L=1; L<d; )
  {
    pol= scalarpol(random_FpX(dT,vT,p),vu);
    for (i=2; i<=d; i++)
      pol = FqX_add(pol, FqX_Fq_mul(gel(vker,i),
                                    random_FpX(dT,vT,p), T, p), T, p);
    pol = FpXQX_red(pol,T,p);
    for (i=ir; i<L && L<d; i++)
    {
      a = t[i]; la = degpol(a);
      if (la == 1) { set_irred(i); }
      else
      {
        pari_sp av = avma;
        GEN S = FpXQX_get_red(a, T, p);
        b = FqX_rem(pol, S, T,p);
        if (degpol(b)<=0) { avma=av; continue; }
        b = FpXQXQ_halfFrobenius_i(b, xp, FpXQX_rem(Xp, S, T, p), S, T, p);
        if (degpol(b)<=0) { avma=av; continue; }
        gel(b,2) = Fq_sub(gel(b,2), gen_1,T,p);
        b = FqX_gcd(a,b, T,p); lb = degpol(b);
        if (lb && lb < la)
        {
          b = FpXQX_normalize(b, T,p);
          t[L] = FqX_div(a,b,T,p);
          t[i]= b; L++;
        }
        else avma = av;
      }
    }
  }
  return d;
}

static GEN
F2xqX_quad_roots(GEN P, GEN T)
{
  GEN b= gel(P,3), c = gel(P,2);
  if (lgpol(b))
  {
    GEN z, d = F2xq_div(c, F2xq_sqr(b,T),T);
    if (F2xq_trace(d,T))
      return cgetg(1, t_COL);
    z = F2xq_mul(b, F2xq_Artin_Schreier(d, T), T);
    return mkcol2(z, F2x_add(b, z));
  }
  else
    return mkcol(F2xq_sqrt(c, T));
}

/* Assume p>2 and x monic */
static GEN
FlxqX_quad_roots(GEN x, GEN T, ulong p)
{
  GEN s, D, nb, b = gel(x,3), c = gel(x,2);
  D = Flx_sub(Flxq_sqr(b,T,p), Flx_mulu(c,4,p), p);
  nb = Flx_neg(b,p);
  if (lgpol(D)==0)
    return mkcol(Flx_halve(nb, p));
  s = Flxq_sqrt(D,T,p);
  if (!s) return cgetg(1, t_COL);
  s = Flx_halve(Flx_add(s,nb,p),p);
  return mkcol2(s, Flx_sub(nb,s,p));
}

static GEN
FpXQX_quad_roots(GEN x, GEN T, GEN p)
{
  GEN s, D, nb, b = gel(x,3), c = gel(x,2);
  if (absequaliu(p, 2))
  {
    GEN f2 = ZXX_to_F2xX(x, get_FpX_var(T));
    s = F2xqX_quad_roots(f2, ZX_to_F2x(get_FpX_mod(T)));
    return F2xC_to_ZXC(s);
  }
  D = Fq_sub(Fq_sqr(b,T,p), Fq_Fp_mul(c,utoi(4),T,p), T,p);
  nb = Fq_neg(b,T,p);
  if (signe(D)==0)
    return mkcol(Fq_to_FpXQ(Fq_halve(nb,T, p),T,p));
  s = Fq_sqrt(D,T,p);
  if (!s) return cgetg(1, t_COL);
  s = Fq_halve(Fq_add(s,nb,T,p),T, p);
  return mkcol2(Fq_to_FpXQ(s,T,p), Fq_to_FpXQ(Fq_sub(nb,s,T,p),T,p));
}

static GEN
F2xqX_Frobenius_deflate(GEN S, GEN T)
{
  GEN F = RgX_deflate(S, 2);
  long i, l = lg(F);
  for (i=2; i<l; i++)
    gel(F,i) = F2xq_sqrt(gel(F,i), T);
  return F;
}

static GEN
F2xX_to_F2x(GEN x)
{
  long l=nbits2lg(lgpol(x));
  GEN z=cgetg(l,t_VECSMALL);
  long i,j,k;
  z[1]=x[1];
  for(i=2, k=1,j=BITS_IN_LONG;i<lg(x);i++,j++)
  {
    if (j==BITS_IN_LONG)
    {
      j=0; k++; z[k]=0;
    }
    if (lgpol(gel(x,i)))
      z[k]|=1UL<<j;
  }
  return F2x_renormalize(z,l);
}

static GEN
F2xqX_easyroots(GEN f, GEN T)
{
  if (F2xY_degreex(f) <= 0) return F2x_rootsff_i(F2xX_to_F2x(f), T);
  if (degpol(f)==1) return mkcol(constant_coeff(f));
  if (degpol(f)==2) return F2xqX_quad_roots(f,T);
  return NULL;
}

/* Adapted from Shoup NTL */
GEN
F2xqX_factor_squarefree(GEN f, GEN T)
{
  pari_sp av = avma;
  GEN r, t, v, tv;
  long i, q, n = degpol(f);
  GEN u = const_vec(n+1, pol1_F2xX(varn(f), get_F2x_var(T)));
  for(q = 1;;q *= 2)
  {
    r = F2xqX_gcd(f, F2xX_deriv(f), T);
    if (degpol(r) == 0)
    {
      gel(u, q) = F2xqX_normalize(f, T);
      break;
    }
    t = F2xqX_div(f, r, T);
    if (degpol(t) > 0)
    {
      long j;
      for(j = 1;;j++)
      {
        v = F2xqX_gcd(r, t, T);
        tv = F2xqX_div(t, v, T);
        if (degpol(tv) > 0)
          gel(u, j*q) = F2xqX_normalize(tv, T);
        if (degpol(v) <= 0) break;
        r = F2xqX_div(r, v, T);
        t = v;
      }
      if (degpol(r) == 0) break;
    }
    f = F2xqX_Frobenius_deflate(r, T);
  }
  for (i = n; i; i--)
    if (degpol(gel(u,i))) break;
  setlg(u,i+1); return gerepilecopy(av, u);
}

long
F2xqX_ispower(GEN f, long k, GEN T, GEN *pt_r)
{
  pari_sp av = avma;
  GEN lc, F;
  long i, l, n = degpol(f), v = varn(f);
  if (n % k) return 0;
  lc = F2xq_sqrtn(leading_coeff(f), stoi(k), T, NULL);
  if (!lc) { av = avma; return 0; }
  F = F2xqX_factor_squarefree(f, T); l = lg(F)-1;
  for(i=1; i<=l; i++)
    if (i%k && degpol(gel(F,i))) { avma = av; return 0; }
  if (pt_r)
  {
    GEN r = scalarpol(lc, v), s = pol1_F2xX(v, T[1]);
    for(i=l; i>=1; i--)
    {
      if (i%k) continue;
      s = F2xqX_mul(s, gel(F,i), T);
      r = F2xqX_mul(r, s, T);
    }
    *pt_r = gerepileupto(av, r);
  } else av = avma;
  return 1;
}

static void
F2xqX_roots_edf(GEN Sp, GEN xp, GEN Xp, GEN T, GEN V, long idx)
{
  pari_sp btop;
  long n = degpol(Sp);
  GEN S, f, ff;
  long dT = get_F2x_degree(T);
  GEN R = F2xqX_easyroots(Sp, T);
  if (R)
  {
    long i, l = lg(R)-1;
    for (i=0; i<l; i++)
      gel(V, idx+i) = gel(R,1+i);
    return;
  }
  S = F2xqX_get_red(Sp, T);
  Xp = F2xqX_rem(Xp, S, T);
  btop = avma;
  while (1)
  {
    GEN a = random_F2xqX(degpol(Sp), varn(Sp), T);
    GEN R = gel(F2xqXQ_auttrace(mkvec3(xp, Xp, a), dT, S, T), 3);
    f = F2xqX_gcd(R, Sp, T);
    if (degpol(f) > 0 && degpol(f) < n) break;
    avma = btop;
  }
  f = gerepileupto(btop, F2xqX_normalize(f, T));
  ff = F2xqX_div(Sp, f, T);
  F2xqX_roots_edf(f, xp, Xp, T, V, idx);
  F2xqX_roots_edf(ff,xp, Xp, T, V, idx+degpol(f));
}

static GEN
F2xqX_roots_ddf(GEN f, GEN xp, GEN T)
{
  GEN X, Xp, Xq, g, V;
  long n;
  GEN R = F2xqX_easyroots(f, T);
  if (R) return R;
  X  = pol_x(varn(f));
  Xp = F2xqXQ_sqr(X, f, T);
  Xq = F2xqXQ_Frobenius(xp, Xp, f, T);
  g = F2xqX_gcd(F2xX_add(Xq, X), f, T);
  n = degpol(g);
  if (n==0) return cgetg(1, t_COL);
  g = F2xqX_normalize(g, T);
  V = cgetg(n+1,t_COL);
  F2xqX_roots_edf(g, xp, Xp, T, V, 1);
  return V;
}
static GEN
F2xqX_roots_i(GEN S, GEN T)
{
  GEN M;
  S = F2xqX_red(S, T);
  if (!signe(S)) pari_err_ROOTS0("F2xqX_roots");
  if (degpol(S)==0) return cgetg(1, t_COL);
  S = F2xqX_normalize(S, T);
  M = F2xqX_easyroots(S, T);
  if (!M)
  {
    GEN xp = F2x_Frobenius(T);
    GEN F, V = F2xqX_factor_squarefree(S, T);
    long i, j, l = lg(V);
    F = cgetg(l, t_VEC);
    for (i=1, j=1; i < l; i++)
      if (degpol(gel(V,i)))
        gel(F, j++) = F2xqX_roots_ddf(gel(V,i), xp, T);
    setlg(F,j); M = shallowconcat1(F);
  }
  gen_sort_inplace(M, (void*) &cmp_Flx, &cmp_nodata, NULL);
  return M;
}

static GEN
FlxqX_easyroots(GEN f, GEN T, ulong p)
{
  if (FlxY_degreex(f) <= 0) return Flx_rootsff_i(FlxX_to_Flx(f), T, p);
  if (degpol(f)==1) return mkcol(Flx_neg(constant_coeff(f), p));
  if (degpol(f)==2) return FlxqX_quad_roots(f,T,p);
  return NULL;
}

static GEN
FlxqX_invFrobenius(GEN xp, GEN T, ulong p)
{
  return Flxq_autpow(xp, get_Flx_degree(T)-1, T, p);
}

static GEN
FlxqX_Frobenius_deflate(GEN S, GEN ixp, GEN T, ulong p)
{
  GEN F = RgX_deflate(S, p);
  long i, l = lg(F);
  if (typ(ixp)==t_INT)
    for (i=2; i<l; i++)
      gel(F,i) = Flxq_pow(gel(F,i), ixp, T, p);
  else
  {
    long n = brent_kung_optpow(get_Flx_degree(T)-1, l-2, 1);
    GEN V = Flxq_powers(ixp, n, T, p);
    for (i=2; i<l; i++)
      gel(F,i) = Flx_FlxqV_eval(gel(F,i), V, T, p);
  }
  return F;
}

/* Adapted from Shoup NTL */
static GEN
FlxqX_factor_squarefree_i(GEN f, GEN xp, GEN T, ulong p)
{
  pari_sp av = avma;
  GEN r, t, v, tv;
  long i, q, n = degpol(f);
  GEN u = const_vec(n+1, pol1_FlxX(varn(f),get_Flx_var(T)));
  GEN ixp = NULL;
  for(q = 1;;q *= p)
  {
    r = FlxqX_gcd(f, FlxX_deriv(f, p), T, p);
    if (degpol(r) == 0)
    {
      gel(u, q) = FlxqX_normalize(f, T, p);
      break;
    }
    t = FlxqX_div(f, r, T, p);
    if (degpol(t) > 0)
    {
      long j;
      for(j = 1;;j++)
      {
        v = FlxqX_gcd(r, t, T, p);
        tv = FlxqX_div(t, v, T, p);
        if (degpol(tv) > 0)
          gel(u, j*q) = FlxqX_normalize(tv, T, p);
        if (degpol(v) <= 0) break;
        r = FlxqX_div(r, v, T, p);
        t = v;
      }
      if (degpol(r) == 0) break;
    }
    if (!xp)   xp = Flx_Frobenius(T, p);
    if (!ixp) ixp = FlxqX_invFrobenius(xp, T, p);
    f = FlxqX_Frobenius_deflate(r, ixp, T, p);
  }
  for (i = n; i; i--)
    if (degpol(gel(u,i))) break;
  setlg(u,i+1); return gerepilecopy(av, u);
}

GEN
FlxqX_factor_squarefree(GEN f, GEN T, ulong p)
{
  return FlxqX_factor_squarefree_i(f, NULL, T, p);
}

long
FlxqX_ispower(GEN f, ulong k, GEN T, ulong p, GEN *pt_r)
{
  pari_sp av = avma;
  GEN lc, F;
  long i, l, n = degpol(f), v = varn(f);
  if (n % k) return 0;
  lc = Flxq_sqrtn(leading_coeff(f), stoi(k), T, p, NULL);
  if (!lc) { av = avma; return 0; }
  F = FlxqX_factor_squarefree_i(f, NULL, T, p); l = lg(F)-1;
  for(i=1; i<=l; i++)
    if (i%k && degpol(gel(F,i))) { avma = av; return 0; }
  if (pt_r)
  {
    GEN r = scalarpol(lc, v), s = pol1_FlxX(v, T[1]);
    for(i=l; i>=1; i--)
    {
      if (i%k) continue;
      s = FlxqX_mul(s, gel(F,i), T, p);
      r = FlxqX_mul(r, s, T, p);
    }
    *pt_r = gerepileupto(av, r);
  } else av = avma;
  return 1;
}

static GEN
FlxqX_roots_split(GEN Sp, GEN xp, GEN Xp, GEN S, GEN T, ulong p)
{
  pari_sp btop = avma;
  long n = degpol(Sp);
  GEN f;
  long vT = get_Flx_var(T), dT = get_Flx_degree(T);
  pari_timer ti;
  if (DEBUGLEVEL >= 7) timer_start(&ti);
  while (1)
  {
    GEN a = deg1pol(pol1_Flx(vT), random_Flx(dT, vT, p), varn(Sp));
    GEN R = FlxqXQ_halfFrobenius_i(a, xp, Xp, S, T, p);
    if (DEBUGLEVEL >= 7) timer_printf(&ti, "FlxqXQ_halfFrobenius");
    f = FlxqX_gcd(FlxX_Flx_sub(R, pol1_Flx(vT), p), Sp, T, p);
    if (degpol(f) > 0 && degpol(f) < n) break;
    avma = btop;
  }
  return gerepileupto(btop, FlxqX_normalize(f, T, p));
}

static void
FlxqX_roots_edf(GEN Sp, GEN xp, GEN Xp, GEN T, ulong p, GEN V, long idx)
{
  GEN S, f, ff;
  GEN R = FlxqX_easyroots(Sp, T, p);
  if (R)
  {
    long i, l = lg(R)-1;
    for (i=0; i<l; i++)
      gel(V, idx+i) = gel(R,1+i);
    return;
  }
  S  = FlxqX_get_red(Sp, T, p);
  Xp = FlxqX_rem(Xp, S, T, p);
  f  = FlxqX_roots_split(Sp, xp, Xp, S, T, p);
  ff = FlxqX_div(Sp, f, T, p);
  FlxqX_roots_edf(f, xp, Xp, T, p, V, idx);
  FlxqX_roots_edf(ff,xp, Xp, T, p, V, idx+degpol(f));
}

static GEN
FlxqX_roots_ddf(GEN f, GEN xp, GEN T, ulong p)
{
  GEN X, Xp, Xq, g, V;
  long n;
  GEN R = FlxqX_easyroots(f, T, p);
  if (R) return R;
  X  = pol_x(varn(f));
  Xp = FlxqXQ_powu(X, p, f, T, p);
  Xq = FlxqXQ_Frobenius(xp, Xp, f, T, p);
  g = FlxqX_gcd(FlxX_sub(Xq, X, p), f, T, p);
  n = degpol(g);
  if (n==0) return cgetg(1, t_COL);
  g = FlxqX_normalize(g, T, p);
  V = cgetg(n+1,t_COL);
  FlxqX_roots_edf(g, xp, Xp, T, p, V, 1);
  return V;
}

/* do not handle p==2 */
static GEN
FlxqX_roots_i(GEN S, GEN T, ulong p)
{
  GEN M;
  S = FlxqX_red(S, T, p);
  if (!signe(S)) pari_err_ROOTS0("FlxqX_roots");
  if (degpol(S)==0) return cgetg(1, t_COL);
  S = FlxqX_normalize(S, T, p);
  M = FlxqX_easyroots(S, T, p);
  if (!M)
  {
    GEN xp = Flx_Frobenius(T, p);
    GEN F, V = FlxqX_factor_squarefree_i(S, xp, T, p);
    long i, j, l = lg(V);
    F = cgetg(l, t_VEC);
    for (i=1, j=1; i < l; i++)
      if (degpol(gel(V,i)))
        gel(F, j++) = FlxqX_roots_ddf(gel(V,i), xp, T, p);
    setlg(F,j); M = shallowconcat1(F);
  }
  gen_sort_inplace(M, (void*) &cmp_Flx, &cmp_nodata, NULL);
  return M;
}

static GEN
FpXQX_easyroots(GEN f, GEN T, GEN p)
{
  if (isabsolutepol(f)) return FpX_rootsff_i(simplify_shallow(f), T, p);
  if (degpol(f)==1) return mkcol(Fq_to_FpXQ(Fq_neg(constant_coeff(f),T,p),T,p));
  if (degpol(f)==2) return FpXQX_quad_roots(f,T,p);
  return NULL;
}

/* Adapted from Shoup NTL */
static GEN
FpXQX_factor_Yun(GEN f, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN r, t, v, tv;
  long j, n = degpol(f);
  GEN u = const_vec(n+1, pol_1(varn(f)));
  r = FpXQX_gcd(f, FpXX_deriv(f, p), T, p);
  t = FpXQX_div(f, r, T, p);
  for (j = 1;;j++)
  {
    v = FpXQX_gcd(r, t, T, p);
    tv = FpXQX_div(t, v, T, p);
    if (degpol(tv) > 0)
      gel(u, j) = FpXQX_normalize(tv, T, p);
    if (degpol(v) <= 0) break;
    r = FpXQX_div(r, v, T, p);
    t = v;
  }
  setlg(u, j+1); return gerepilecopy(av, u);
}

GEN
FpXQX_factor_squarefree(GEN f, GEN T, GEN p)
{
  if (lgefint(p)==3)
  {
    pari_sp av = avma;
    ulong pp = p[2];
    GEN M;
    long vT = get_FpX_var(T);
    if (pp==2)
    {
      M = F2xqX_factor_squarefree(ZXX_to_F2xX(f, vT),  ZX_to_F2x(get_FpX_mod(T)));
      return gerepileupto(av, F2xXC_to_ZXXC(M));
    }
    M = FlxqX_factor_squarefree(ZXX_to_FlxX(f, pp, vT),  ZXT_to_FlxT(T, pp), pp);
    return gerepileupto(av, FlxXC_to_ZXXC(M));
  }
  return FpXQX_factor_Yun(f, T, p);
}

long
FpXQX_ispower(GEN f, ulong k, GEN T, GEN p, GEN *pt_r)
{
  pari_sp av = avma;
  GEN lc, F;
  long i, l, n = degpol(f), v = varn(f);
  if (n % k) return 0;
  if (lgefint(p)==3)
  {
    ulong pp = p[2];
    GEN fp = ZXX_to_FlxX(f, pp, varn(T));
    if (!FlxqX_ispower(fp, k, ZX_to_Flx(T, pp), pp, pt_r))
    { avma = av; return 0; }
    if (pt_r) *pt_r = gerepileupto(av, FlxX_to_ZXX(*pt_r));
    else avma = av;
    return 1;
  }
  lc = FpXQ_sqrtn(leading_coeff(f), stoi(k), T, p, NULL);
  if (!lc) { av = avma; return 0; }
  F = FpXQX_factor_Yun(f, T, p); l = lg(F)-1;
  for(i=1; i <= l; i++)
    if (i%k && degpol(gel(F,i))) { avma = av; return 0; }
  if (pt_r)
  {
    GEN r = scalarpol(lc, v), s = pol_1(v);
    for(i=l; i>=1; i--)
    {
      if (i%k) continue;
      s = FpXQX_mul(s, gel(F,i), T, p);
      r = FpXQX_mul(r, s, T, p);
    }
    *pt_r = gerepileupto(av, r);
  } else av = avma;
  return 1;
}

long
FqX_ispower(GEN f, ulong k, GEN T, GEN p, GEN *pt_r)
{ return T ? FpXQX_ispower(f, k, T, p, pt_r): FpX_ispower(f, k, p, pt_r); }

static GEN
FpXQX_roots_split(GEN Sp, GEN xp, GEN Xp, GEN S, GEN T, GEN p)
{
  pari_sp btop = avma;
  long n = degpol(Sp);
  GEN f;
  long vT = get_FpX_var(T), dT = get_FpX_degree(T);
  pari_timer ti;
  if (DEBUGLEVEL >= 7) timer_start(&ti);
  while (1)
  {
    GEN a = deg1pol(pol_1(vT), random_FpX(dT, vT, p), varn(Sp));
    GEN R = FpXQXQ_halfFrobenius_i(a, xp, Xp, S, T, p);
    if (DEBUGLEVEL >= 7) timer_printf(&ti, "FpXQXQ_halfFrobenius");
    f = FpXQX_gcd(FqX_Fq_sub(R, pol_1(vT), T, p), Sp, T, p);
    if (degpol(f) > 0 && degpol(f) < n) break;
    avma = btop;
  }
  return gerepileupto(btop, FpXQX_normalize(f, T, p));
}

static void
FpXQX_roots_edf(GEN Sp, GEN xp, GEN Xp, GEN T, GEN p, GEN V, long idx)
{
  GEN S, f, ff;
  GEN R = FpXQX_easyroots(Sp, T, p);
  if (R)
  {
    long i, l = lg(R)-1;
    for (i=0; i<l; i++)
      gel(V, idx+i) = gel(R,1+i);
    return;
  }
  S  = FpXQX_get_red(Sp, T, p);
  Xp = FpXQX_rem(Xp, S, T, p);
  f  = FpXQX_roots_split(Sp, xp, Xp, S, T, p);
  ff = FpXQX_div(Sp, f, T, p);
  FpXQX_roots_edf(f, xp, Xp, T, p, V, idx);
  FpXQX_roots_edf(ff,xp, Xp, T, p, V, idx+degpol(f));
}

static GEN
FpXQX_roots_ddf(GEN f, GEN xp, GEN T, GEN p)
{
  GEN X, Xp, Xq, g, V;
  long n;
  GEN R = FpXQX_easyroots(f, T, p);
  if (R) return R;
  X  = pol_x(varn(f));
  Xp = FpXQXQ_pow(X, p, f, T, p);
  Xq = FpXQXQ_Frobenius(xp, Xp, f, T, p);
  g = FpXQX_gcd(FpXX_sub(Xq, X, p), f, T, p);
  n = degpol(g);
  if (n==0) return cgetg(1, t_COL);
  g = FpXQX_normalize(g, T, p);
  V = cgetg(n+1,t_COL);
  FpXQX_roots_edf(g, xp, Xp, T, p, V, 1);
  return V;
}

/* do not handle small p */
static GEN
FpXQX_roots_i(GEN S, GEN T, GEN p)
{
  GEN F, M;
  if (lgefint(p)==3)
  {
    ulong pp = p[2];
    if (pp == 2)
    {
      GEN V = F2xqX_roots_i(ZXX_to_F2xX(S,get_FpX_var(T)), ZX_to_F2x(get_FpX_mod(T)));
      return F2xC_to_ZXC(V);
    }
    else
    {
      GEN V = FlxqX_roots_i(ZXX_to_FlxX(S,pp,get_FpX_var(T)), ZXT_to_FlxT(T,pp), pp);
      return FlxC_to_ZXC(V);
    }
  }
  S = FpXQX_red(S, T, p);
  if (!signe(S)) pari_err_ROOTS0("FpXQX_roots");
  if (degpol(S)==0) return cgetg(1, t_COL);
  S = FpXQX_normalize(S, T, p);
  M = FpXQX_easyroots(S, T, p);
  if (!M)
  {
    GEN xp = FpX_Frobenius(T, p);
    GEN V = FpXQX_factor_Yun(S, T, p);
    long i, j, l = lg(V);
    F = cgetg(l, t_VEC);
    for (i=1, j=1; i < l; i++)
      if (degpol(gel(V,i)))
        gel(F, j++) = FpXQX_roots_ddf(gel(V,i), xp, T, p);
    setlg(F,j); M = shallowconcat1(F);
  }
  gen_sort_inplace(M, (void*) &cmp_RgX, &cmp_nodata, NULL);
  return M;
}

GEN
F2xqX_roots(GEN x, GEN T)
{
  pari_sp av = avma;
  return gerepilecopy(av, F2xqX_roots_i(x, T));
}

GEN
FlxqX_roots(GEN x, GEN T, ulong p)
{
  pari_sp av = avma;
  if (p==2)
  {
    GEN V = F2xqX_roots_i(FlxX_to_F2xX(x), Flx_to_F2x(get_Flx_mod(T)));
    return gerepileupto(av, F2xC_to_FlxC(V));
  }
  return gerepilecopy(av, FlxqX_roots_i(x, T, p));
}

GEN
FpXQX_roots(GEN x, GEN T, GEN p)
{
  pari_sp av = avma;
  return gerepilecopy(av, FpXQX_roots_i(x, T, p));
}

static GEN
FE_concat(GEN F, GEN E, long l)
{
  setlg(E,l); E = shallowconcat1(E);
  setlg(F,l); F = shallowconcat1(F); return mkvec2(F,E);
}

static GEN
F2xqX_factor_2(GEN f, GEN T)
{
  long v = varn(f), vT = get_F2x_var(T);
  GEN r = F2xqX_quad_roots(f, T);
  switch(lg(r)-1)
  {
  case 0:
    return mkvec2(mkcolcopy(f), mkvecsmall(1));
  case 1:
    return mkvec2(mkcol(deg1pol_shallow(pol1_F2x(vT), gel(r,1), v)), mkvecsmall(2));
  default: /* 2 */
    {
      GEN f1 = deg1pol_shallow(pol1_F2x(vT), gel(r,1), v);
      GEN f2 = deg1pol_shallow(pol1_F2x(vT), gel(r,2), v);
      GEN t = mkcol2(f1, f2), E = mkvecsmall2(1, 1);
      sort_factor_pol(mkvec2(t, E), cmp_Flx);
      return mkvec2(t, E);
    }
  }
}

static GEN
FlxqX_factor_2(GEN f, GEN T, ulong p)
{
  long v = varn(f), vT = get_Flx_var(T);
  GEN r = FlxqX_quad_roots(f, T, p);
  switch(lg(r)-1)
  {
  case 0:
    return mkvec2(mkcolcopy(f), mkvecsmall(1));
  case 1:
    return mkvec2(mkcol(deg1pol_shallow(pol1_Flx(vT),
                        Flx_neg(gel(r,1), p), v)), mkvecsmall(2));
  default: /* 2 */
    {
      GEN f1 = deg1pol_shallow(pol1_Flx(vT), Flx_neg(gel(r,1), p), v);
      GEN f2 = deg1pol_shallow(pol1_Flx(vT), Flx_neg(gel(r,2), p), v);
      GEN t = mkcol2(f1, f2), E = mkvecsmall2(1, 1);
      sort_factor_pol(mkvec2(t, E), cmp_Flx);
      return mkvec2(t, E);
    }
  }
}

static GEN
FpXQX_factor_2(GEN f, GEN T, GEN p)
{
  long v = varn(f);
  GEN r = FpXQX_quad_roots(f, T, p);
  switch(lg(r)-1)
  {
  case 0:
    return mkvec2(mkcolcopy(f), mkvecsmall(1));
  case 1:
    return mkvec2(mkcol(deg1pol_shallow(gen_1, Fq_neg(gel(r,1), T, p), v)),
        mkvecsmall(2));
  default: /* 2 */
    {
      GEN f1 = deg1pol_shallow(gen_1, Fq_neg(gel(r,1), T, p), v);
      GEN f2 = deg1pol_shallow(gen_1, Fq_neg(gel(r,2), T, p), v);
      GEN t = mkcol2(f1, f2), E = mkvecsmall2(1, 1);
      sort_factor_pol(mkvec2(t, E), cmp_RgX);
      return mkvec2(t, E);
    }
  }
}

static GEN
F2xqX_ddf_Shoup(GEN S, GEN Xq, GEN T)
{
  pari_sp av = avma;
  GEN b, g, h, F, f, Sr, xq;
  long i, j, n, v, vT, dT, bo, ro;
  long B, l, m;
  pari_timer ti;
  n = get_F2xqX_degree(S); v = get_F2xqX_var(S);
  vT = get_F2x_var(T); dT = get_F2x_degree(T);
  if (n == 0) return cgetg(1, t_VEC);
  if (n == 1) return mkvec(get_F2xqX_mod(S));
  B = n/2;
  l = usqrt(B);
  m = (B+l-1)/l;
  S = F2xqX_get_red(S, T);
  b = cgetg(l+2, t_VEC);
  gel(b, 1) = polx_F2xX(v, vT);
  gel(b, 2) = Xq;
  bo = brent_kung_optpow(n, l-1, 1);
  ro = l<=1 ? 0: (bo-1)/(l-1) + ((n-1)/bo);
  if (DEBUGLEVEL>=7) timer_start(&ti);
  if (dT <= ro)
    for (i = 3; i <= l+1; i++)
      gel(b, i) = F2xqXQ_pow(gel(b, i-1), int2n(dT), S, T);
  else
  {
    xq = F2xqXQ_powers(gel(b, 2), bo, S, T);
    if (DEBUGLEVEL>=7) timer_printf(&ti,"F2xqX_ddf_Shoup: xq baby");
    for (i = 3; i <= l+1; i++)
      gel(b, i) = F2xqX_F2xqXQV_eval(gel(b, i-1), xq, S, T);
  }
  if (DEBUGLEVEL>=7) timer_printf(&ti,"F2xqX_ddf_Shoup: baby");
  xq = F2xqXQ_powers(gel(b, l+1), brent_kung_optpow(n, m-1, 1), S, T);
  if (DEBUGLEVEL>=7) timer_printf(&ti,"F2xqX_ddf_Shoup: xq giant");
  g = cgetg(m+1, t_VEC);
  gel(g, 1) = gel(xq, 2);
  for(i = 2; i <= m; i++)
    gel(g, i) = F2xqX_F2xqXQV_eval(gel(g, i-1), xq, S, T);
  if (DEBUGLEVEL>=7) timer_printf(&ti,"F2xqX_ddf_Shoup: giant");
  h = cgetg(m+1, t_VEC);
  for (j = 1; j <= m; j++)
  {
    pari_sp av = avma;
    GEN gj = gel(g, j);
    GEN e = F2xX_add(gj, gel(b, 1));
    for (i = 2; i <= l; i++)
      e = F2xqXQ_mul(e, F2xX_add(gj, gel(b, i)), S, T);
    gel(h, j) = gerepileupto(av, e);
  }
  if (DEBUGLEVEL>=7) timer_printf(&ti,"F2xqX_ddf_Shoup: diff");
  Sr = get_F2xqX_mod(S);
  F = cgetg(m+1, t_VEC);
  for (j = 1; j <= m; j++)
  {
    GEN u = F2xqX_gcd(Sr, gel(h,j), T);
    if (degpol(u))
    {
      u = F2xqX_normalize(u, T);
      Sr = F2xqX_div(Sr, u, T);
    }
    gel(F,j) = u;
  }
  if (DEBUGLEVEL>=7) timer_printf(&ti,"F2xqX_ddf_Shoup: F");
  f = const_vec(n, pol1_F2xX(v, vT));
  for (j = 1; j <= m; j++)
  {
    GEN e = gel(F, j);
    for (i=l-1; i >= 0; i--)
    {
      GEN u = F2xqX_gcd(e, F2xX_add(gel(g, j), gel(b, i+1)), T);
      if (degpol(u))
      {
        gel(f, l*j-i) = u = F2xqX_normalize(u, T);
        e = F2xqX_div(e, u, T);
      }
      if (!degpol(e)) break;
    }
  }
  if (DEBUGLEVEL>=7) timer_printf(&ti,"F2xqX_ddf_Shoup: f");
  if (degpol(Sr)) gel(f, degpol(Sr)) = Sr;
  return gerepilecopy(av, f);
}

static GEN
F2xqX_ddf_i(GEN f, GEN T, GEN X, GEN xp)
{
  GEN Xp, Xq;
  if (!get_F2xqX_degree(f)) return cgetg(1,t_VEC);
  f = F2xqX_get_red(f, T);
  Xp = F2xqXQ_sqr(X, f, T);
  Xq = F2xqXQ_Frobenius(xp, Xp, f, T);
  return F2xqX_ddf_Shoup(f, Xq, T);
}
static void
F2xqX_ddf_init(GEN *S, GEN *T, GEN *xp, GEN *X)
{
  *T = F2x_get_red(*T);
  *S = F2xqX_normalize(get_F2xqX_mod(*S), *T);
  *xp = F2x_Frobenius(*T);
  *X  = polx_F2xX(get_F2xqX_var(*S), get_F2x_var(*T));
}
GEN
F2xqX_degfact(GEN S, GEN T)
{
  GEN xp, X, V;
  long i, l;
  F2xqX_ddf_init(&S,&T,&xp,&X);
  V = F2xqX_factor_squarefree(S, T); l = lg(V);
  for (i=1; i < l; i++) gel(V,i) = F2xqX_ddf_i(gel(V,i), T, X, xp);
  return vddf_to_simplefact(V, degpol(S));
}
GEN
F2xqX_ddf(GEN S, GEN T)
{
  GEN xp, X;
  F2xqX_ddf_init(&S,&T,&xp,&X);
  return ddf_to_ddf2( F2xqX_ddf_i(S, T, X, xp) );
}

static void
F2xqX_edf_simple(GEN Sp, GEN xp, GEN Xp, GEN Sq, long d, GEN T, GEN V, long idx)
{
  long v = varn(Sp), n = degpol(Sp), r = n/d;
  GEN S, f, ff;
  long dT = get_F2x_degree(T);
  if (r==1) { gel(V, idx) = Sp; return; }
  S = F2xqX_get_red(Sp, T);
  Xp = F2xqX_rem(Xp, S, T);
  Sq = F2xqXQV_red(Sq, S, T);
  while (1)
  {
    pari_sp btop = avma;
    long l;
    GEN w0 = random_F2xqX(n, v, T), g = w0;
    for (l=1; l<d; l++) /* sum_{0<i<d} w^(q^i), result in (F_q)^r */
      g = F2xX_add(w0, F2xqX_F2xqXQV_eval(g, Sq, S, T));
    w0 = g;
    for (l=1; l<dT; l++) /* sum_{0<i<k} w^(2^i), result in (F_2)^r */
      g = F2xX_add(w0, F2xqXQ_sqr(g,S,T));
    f = F2xqX_gcd(g, Sp, T);
    if (degpol(f) > 0 && degpol(f) < n) break;
    avma = btop;
  }
  f = F2xqX_normalize(f, T);
  ff = F2xqX_div(Sp, f , T);
  F2xqX_edf_simple(f, xp, Xp, Sq, d, T, V, idx);
  F2xqX_edf_simple(ff, xp, Xp, Sq, d, T, V, idx+degpol(f)/d);
}

static GEN
F2xqX_factor_Shoup(GEN S, GEN xp, GEN T)
{
  long i, n, s = 0;
  GEN X, Xp, Xq, Sq, D, V;
  long vT = get_F2x_var(T);
  pari_timer ti;
  n = get_F2xqX_degree(S);
  S = F2xqX_get_red(S, T);
  if (DEBUGLEVEL>=6) timer_start(&ti);
  X  = polx_F2xX(get_F2xqX_var(S), vT);
  Xp = F2xqXQ_sqr(X, S, T);
  Xq = F2xqXQ_Frobenius(xp, Xp, S, T);
  Sq = F2xqXQ_powers(Xq, n-1, S, T);
  if (DEBUGLEVEL>=6) timer_printf(&ti,"F2xqX_Frobenius");
  D = F2xqX_ddf_Shoup(S, Xq, T);
  if (DEBUGLEVEL>=6) timer_printf(&ti,"F2xqX_ddf_Shoup");
  s = ddf_to_nbfact(D);
  V = cgetg(s+1, t_COL);
  for (i = 1, s = 1; i <= n; i++)
  {
    GEN Di = gel(D,i);
    long ni = degpol(Di), ri = ni/i;
    if (ni == 0) continue;
    Di = F2xqX_normalize(Di, T);
    if (ni == i) { gel(V, s++) = Di; continue; }
    F2xqX_edf_simple(Di, xp, Xp, Sq, i, T, V, s);
    if (DEBUGLEVEL>=6) timer_printf(&ti,"F2xqX_edf(%ld)",i);
    s += ri;
  }
  return V;
}

static GEN
F2xqX_factor_Cantor(GEN f, GEN T)
{
  GEN xp, E, F, V;
  long i, j, l;
  T = F2x_get_red(T);
  f = F2xqX_normalize(f, T);
  switch(degpol(f))
  {
    case -1: retmkmat2(mkcol(f), mkvecsmall(1));
    case 0: return trivial_fact();
    case 1: retmkmat2(mkcol(f), mkvecsmall(1));
    case 2: return F2xqX_factor_2(f, T);
  }
  if (F2xY_degreex(f) <= 0) return F2x_factorff_i(F2xX_to_F2x(f), T);
  xp = F2x_Frobenius(T);
  V = F2xqX_factor_squarefree(f, T);
  l = lg(V);
  F = cgetg(l, t_VEC);
  E = cgetg(l, t_VEC);
  for (i=1, j=1; i < l; i++)
    if (degpol(gel(V,i)))
    {
      GEN Fj = F2xqX_factor_Shoup(gel(V,i), xp, T);
      gel(F, j) = Fj;
      gel(E, j) = const_vecsmall(lg(Fj)-1, i);
      j++;
    }
  return sort_factor_pol(FE_concat(F,E,j), cmp_Flx);
}

static GEN
FlxqX_Berlekamp_i(GEN f, GEN T, ulong p)
{
  long lfact, d = degpol(f), j, k, lV;
  GEN E, t, V, xp;
  switch(d)
  {
    case -1: retmkmat2(mkcolcopy(f), mkvecsmall(1));
    case 0: return trivial_fact();
  }
  T = Flx_get_red(T, p);
  f = FlxqX_normalize(f, T, p);
  if (FlxY_degreex(f) <= 0) return Flx_factorff_i(FlxX_to_Flx(f), T, p);
  if (degpol(f)==2) return FlxqX_factor_2(f, T, p);
  xp = Flx_Frobenius(T, p);
  V = FlxqX_factor_squarefree_i(f, xp, T, p); lV = lg(V);

  /* to hold factors and exponents */
  t = cgetg(d+1,t_VEC);
  E = cgetg(d+1, t_VECSMALL);
  lfact = 1;
  for (k=1; k<lV ; k++)
  {
    if (degpol(gel(V,k))==0) continue;
    gel(t,lfact) = FlxqX_normalize(gel(V, k), T,p);
    d = FlxqX_split_Berlekamp(&gel(t,lfact), xp, T, p);
    for (j = 0; j < d; j++) E[lfact+j] = k;
    lfact += d;
  }
  setlg(t, lfact);
  setlg(E, lfact);
  return sort_factor_pol(mkvec2(t, E), cmp_Flx);
}

static GEN
FpXQX_Berlekamp_i(GEN f, GEN T, GEN p)
{
  long lfact, d = degpol(f), j, k, lV;
  GEN E, t, V;
  switch(d)
  {
    case -1: retmkmat2(mkcolcopy(f), mkvecsmall(1));
    case 0: return trivial_fact();
  }
  T = FpX_get_red(T, p);
  f = FpXQX_normalize(f, T, p);
  if (isabsolutepol(f)) return FpX_factorff_i(simplify_shallow(f), T, p);
  if (degpol(f)==2) return FpXQX_factor_2(f, T, p);
  V = FpXQX_factor_Yun(f, T, p); lV = lg(V);

  /* to hold factors and exponents */
  t = cgetg(d+1,t_VEC);
  E = cgetg(d+1, t_VECSMALL);
  lfact = 1;
  for (k=1; k<lV ; k++)
  {
    if (degpol(gel(V,k))==0) continue;
    gel(t,lfact) = FpXQX_normalize(gel(V, k), T,p);
    d = FpXQX_split_Berlekamp(&gel(t,lfact), T, p);
    for (j = 0; j < d; j++) E[lfact+j] = k;
    lfact += d;
  }
  setlg(t, lfact);
  setlg(E, lfact);
  return sort_factor_pol(mkvec2(t, E), cmp_RgX);
}

long
FlxqX_ddf_degree(GEN S, GEN XP, GEN T, ulong p)
{
  pari_sp av = avma;
  GEN X, b, g, xq, q;
  long i, j, n, v, B, l, m, bo, ro;
  pari_timer ti;
  hashtable h;

  n = get_FlxqX_degree(S); v = get_FlxqX_var(S);
  X = polx_FlxX(v,get_Flx_var(T));
  if (gequal(X,XP)) return 1;
  B = n/2;
  l = usqrt(B);
  m = (B+l-1)/l;
  T = Flx_get_red(T, p);
  S = FlxqX_get_red(S, T, p);
  hash_init_GEN(&h, l+2, gequal, 1);
  hash_insert_long(&h, X,  0);
  hash_insert_long(&h, XP, 1);
  bo = brent_kung_optpow(n, l-1, 1);
  ro = l<=1 ? 0: (bo-1)/(l-1) + ((n-1)/bo);
  q = powuu(p, get_Flx_degree(T));
  if (DEBUGLEVEL>=7) timer_start(&ti);
  b = XP;
  if (expi(q) > ro)
  {
    xq = FlxqXQ_powers(b, brent_kung_optpow(n, l-1, 1),  S, T, p);
    if (DEBUGLEVEL>=7) timer_printf(&ti,"FlxqX_ddf_degree: xq baby");
  } else xq = NULL;
  for (i = 3; i <= l+1; i++)
  {
    b = xq ? FlxqX_FlxqXQV_eval(b, xq, S, T, p)
           : FlxqXQ_pow(b, q, S, T, p);
    if (gequal(b,X)) { avma = av; return i-1; }
    hash_insert_long(&h, b, i-1);
  }
  if (DEBUGLEVEL>=7) timer_printf(&ti,"FlxqX_ddf_degree: baby");
  g = b;
  xq = FlxqXQ_powers(g, brent_kung_optpow(n, m, 1),  S, T, p);
  if (DEBUGLEVEL>=7) timer_printf(&ti,"FlxqX_ddf_degree: xq giant");
  for(i = 2; i <= m+1; i++)
  {
    g = FlxqX_FlxqXQV_eval(g, xq, S, T, p);
    if (hash_haskey_long(&h, g, &j)) { avma=av; return l*i-j; }
  }
  avma = av; return n;
}

static GEN
FlxqX_ddf_Shoup(GEN S, GEN Xq, GEN T, ulong p)
{
  pari_sp av = avma;
  GEN b, g, h, F, f, Sr, xq, q;
  long i, j, n, v, vT, bo, ro;
  long B, l, m;
  pari_timer ti;
  n = get_FlxqX_degree(S); v = get_FlxqX_var(S);
  vT = get_Flx_var(T);
  if (n == 0) return cgetg(1, t_VEC);
  if (n == 1) return mkvec(get_FlxqX_mod(S));
  B = n/2;
  l = usqrt(B);
  m = (B+l-1)/l;
  S = FlxqX_get_red(S, T, p);
  b = cgetg(l+2, t_VEC);
  gel(b, 1) = polx_FlxX(v, vT);
  gel(b, 2) = Xq;
  bo = brent_kung_optpow(n, l-1, 1);
  ro = l<=1 ? 0: (bo-1)/(l-1) + ((n-1)/bo);
  q = powuu(p, get_Flx_degree(T));
  if (DEBUGLEVEL>=7) timer_start(&ti);
  if (expi(q) <= ro)
    for (i = 3; i <= l+1; i++)
      gel(b, i) = FlxqXQ_pow(gel(b, i-1), q, S, T, p);
  else
  {
    xq = FlxqXQ_powers(gel(b, 2), bo, S, T, p);
    if (DEBUGLEVEL>=7) timer_printf(&ti,"FlxqX_ddf_Shoup: xq baby");
    for (i = 3; i <= l+1; i++)
      gel(b, i) = FlxqX_FlxqXQV_eval(gel(b, i-1), xq, S, T, p);
  }
  if (DEBUGLEVEL>=7) timer_printf(&ti,"FlxqX_ddf_Shoup: baby");
  xq = FlxqXQ_powers(gel(b, l+1), brent_kung_optpow(n, m-1, 1), S, T, p);
  if (DEBUGLEVEL>=7) timer_printf(&ti,"FlxqX_ddf_Shoup: xq giant");
  g = cgetg(m+1, t_VEC);
  gel(g, 1) = gel(xq, 2);
  for(i = 2; i <= m; i++)
    gel(g, i) = FlxqX_FlxqXQV_eval(gel(g, i-1), xq, S, T, p);
  if (DEBUGLEVEL>=7) timer_printf(&ti,"FlxqX_ddf_Shoup: giant");
  h = cgetg(m+1, t_VEC);
  for (j = 1; j <= m; j++)
  {
    pari_sp av = avma;
    GEN gj = gel(g, j);
    GEN e = FlxX_sub(gj, gel(b, 1), p);
    for (i = 2; i <= l; i++)
      e = FlxqXQ_mul(e, FlxX_sub(gj, gel(b, i), p), S, T, p);
    gel(h, j) = gerepileupto(av, e);
  }
  if (DEBUGLEVEL>=7) timer_printf(&ti,"FlxqX_ddf_Shoup: diff");
  Sr = get_FlxqX_mod(S);
  F = cgetg(m+1, t_VEC);
  for (j = 1; j <= m; j++)
  {
    GEN u = FlxqX_gcd(Sr, gel(h, j), T, p);
    if (degpol(u))
    {
      u = FlxqX_normalize(u, T, p);
      Sr = FlxqX_div(Sr, u, T, p);
    }
    gel(F,j) = u;
  }
  if (DEBUGLEVEL>=7) timer_printf(&ti,"FlxqX_ddf_Shoup: F");
  f = const_vec(n, pol1_FlxX(v, vT));
  for (j = 1; j <= m; j++)
  {
    GEN e = gel(F, j);
    for (i=l-1; i >= 0; i--)
    {
      GEN u = FlxqX_gcd(e, FlxX_sub(gel(g, j), gel(b, i+1), p), T, p);
      if (degpol(u))
      {
        gel(f, l*j-i) = u = FlxqX_normalize(u, T, p);
        e = FlxqX_div(e, u, T, p);
      }
      if (!degpol(e)) break;
    }
  }
  if (DEBUGLEVEL>=7) timer_printf(&ti,"FlxqX_ddf_Shoup: f");
  if (degpol(Sr)) gel(f, degpol(Sr)) = Sr;
  return gerepilecopy(av, f);
}

static GEN
FlxqX_ddf_i(GEN f, GEN T, ulong p)
{
  GEN Xq;
  if (!get_FlxqX_degree(f)) return cgetg(1, t_VEC);
  f = FlxqX_get_red(f, T, p);
  Xq = FlxqX_Frobenius(f, T, p);
  return FlxqX_ddf_Shoup(f, Xq, T, p);
}
GEN
FlxqX_ddf(GEN S, GEN T, ulong p)
{
  T = Flx_get_red(T, p);
  S = FlxqX_normalize(get_FlxqX_mod(S), T, p);
  return ddf_to_ddf2( FlxqX_ddf_i(S, T, p) );
}
GEN
FlxqX_degfact(GEN S, GEN T, ulong p)
{
  GEN V;
  long i, l;
  T = Flx_get_red(T, p);
  S = FlxqX_normalize(get_FlxqX_mod(S), T, p);
  V = FlxqX_factor_squarefree(S, T, p); l = lg(V);
  for (i=1; i < l; i++) gel(V,i) = FlxqX_ddf_i(gel(V,i), T, p);
  return vddf_to_simplefact(V, degpol(S));
}

static void
FlxqX_edf_rec(GEN S, GEN xp, GEN Xp, GEN hp, GEN t, long d, GEN T, ulong p, GEN V, long idx)
{
  GEN Sp = get_FlxqX_mod(S);
  GEN u1, u2, f1, f2;
  GEN h;
  h = FlxqX_get_red(hp, T, p);
  t = FlxqX_rem(t, S, T, p);
  Xp = FlxqX_rem(Xp, h, T, p);
  u1 = FlxqX_roots_split(hp, xp, Xp, h, T, p);
  f1 = FlxqX_gcd(FlxqX_FlxqXQ_eval(u1, t, S, T, p), Sp, T, p);
  f1 = FlxqX_normalize(f1, T, p);
  u2 = FlxqX_div(hp, u1, T, p);
  f2 = FlxqX_div(Sp, f1, T, p);
  if (degpol(u1)==1)
    gel(V, idx) = f1;
  else
    FlxqX_edf_rec(FlxqX_get_red(f1, T, p), xp, Xp, u1, t, d, T, p, V, idx);
  idx += degpol(f1)/d;
  if (degpol(u2)==1)
    gel(V, idx) = f2;
  else
    FlxqX_edf_rec(FlxqX_get_red(f2, T, p), xp, Xp, u2, t, d, T, p, V, idx);
}

static void
FlxqX_edf(GEN Sp, GEN xp, GEN Xp, GEN Xq, long d, GEN T, ulong p, GEN V, long idx)
{
  long n = degpol(Sp), r = n/d, vS = varn(Sp), vT = get_Flx_var(T);
  GEN S, h, t;
  pari_timer ti;
  if (r==1) { gel(V, idx) = Sp; return; }
  S = FlxqX_get_red(Sp, T, p);
  Xp = FlxqX_rem(Xp, S, T, p);
  Xq = FlxqX_rem(Xq, S, T, p);
  if (DEBUGLEVEL>=7) timer_start(&ti);
  do
  {
    GEN g = random_FlxqX(n, vS, T, p);
    t = gel(FlxqXQ_auttrace(mkvec2(Xq, g), d, S, T, p), 2);
    if (DEBUGLEVEL>=7) timer_printf(&ti,"FlxqX_edf: FlxqXQ_auttrace");
    h = FlxqXQ_minpoly(t, S, T, p);
    if (DEBUGLEVEL>=7) timer_printf(&ti,"FlxqX_edf: FlxqXQ_minpoly");
  } while (degpol(h) != r);
  Xp = FlxqXQ_powu(polx_FlxX(vS, vT), p, h, T, p);
  FlxqX_edf_rec(S, xp, Xp, h, t, d, T, p, V, idx);
}

static void
FlxqX_edf_simple(GEN Sp, GEN xp, GEN Xp, GEN Xq, long d, GEN T, ulong p, GEN V, long idx)
{
  long v = varn(Sp), n = degpol(Sp), r = n/d;
  GEN S, f, ff;
  long vT = get_Flx_var(T), dT = get_Flx_degree(T);
  if (r==1) { gel(V, idx) = Sp; return; }
  S = FlxqX_get_red(Sp, T, p);
  Xp = FlxqX_rem(Xp, S, T, p);
  Xq = FlxqX_rem(Xq, S, T, p);
  while (1)
  {
    pari_sp btop = avma;
    long i;
    GEN g = random_FlxqX(n, v, T, p);
    GEN t = gel(FlxqXQ_auttrace(mkvec2(Xq, g), d, S, T, p), 2);
    if (lgpol(t) == 0) continue;
    for(i=1; i<=10; i++)
    {
      pari_sp btop2 = avma;
      GEN r = random_Flx(dT, vT, p);
      GEN R = FlxqXQ_halfFrobenius_i(FlxX_Flx_add(t, r, p), xp, Xp, S, T, p);
      f = FlxqX_gcd(FlxX_Flx_sub(R, pol1_Flx(vT), p), Sp, T, p);
      if (degpol(f) > 0 && degpol(f) < n) break;
      avma = btop2;
    }
    if (degpol(f) > 0 && degpol(f) < n) break;
    avma = btop;
  }
  f = FlxqX_normalize(f, T, p);
  ff = FlxqX_div(Sp, f , T, p);
  FlxqX_edf_simple(f, xp, Xp, Xq, d, T, p, V, idx);
  FlxqX_edf_simple(ff, xp, Xp, Xq, d, T, p, V, idx+degpol(f)/d);
}

static GEN
FlxqX_factor_Shoup(GEN S, GEN xp, GEN T, ulong p)
{
  long i, n, s = 0;
  GEN X, Xp, Xq, D, V;
  long dT = get_Flx_degree(T), vT = get_Flx_var(T);
  long e = expi(powuu(p, dT));
  pari_timer ti;
  n = get_FlxqX_degree(S);
  S = FlxqX_get_red(S, T, p);
  if (DEBUGLEVEL>=6) timer_start(&ti);
  X  = polx_FlxX(get_FlxqX_var(S), vT);
  Xp = FlxqXQ_powu(X, p, S, T, p);
  Xq = FlxqXQ_Frobenius(xp, Xp, S, T, p);
  if (DEBUGLEVEL>=6) timer_printf(&ti,"FlxqX_Frobenius");
  D = FlxqX_ddf_Shoup(S, Xq, T, p);
  if (DEBUGLEVEL>=6) timer_printf(&ti,"FlxqX_ddf_Shoup");
  s = ddf_to_nbfact(D);
  V = cgetg(s+1, t_COL);
  for (i = 1, s = 1; i <= n; i++)
  {
    GEN Di = gel(D,i);
    long ni = degpol(Di), ri = ni/i;
    if (ni == 0) continue;
    Di = FlxqX_normalize(Di, T, p);
    if (ni == i) { gel(V, s++) = Di; continue; }
    if (ri <= e*expu(e))
      FlxqX_edf(Di, xp, Xp, Xq, i, T, p, V, s);
    else
      FlxqX_edf_simple(Di, xp, Xp, Xq, i, T, p, V, s);
    if (DEBUGLEVEL>=6) timer_printf(&ti,"FlxqX_edf(%ld)",i);
    s += ri;
  }
  return V;
}

static GEN
FlxqX_factor_Cantor(GEN f, GEN T, ulong p)
{
  GEN xp, E, F, V;
  long i, j, l;
  T = Flx_get_red(T, p);
  f = FlxqX_normalize(f, T, p);
  switch(degpol(f))
  {
    case -1: retmkmat2(mkcol(f), mkvecsmall(1));
    case 0: return trivial_fact();
    case 1: retmkmat2(mkcol(f), mkvecsmall(1));
    case 2: return FlxqX_factor_2(f, T, p);
  }
  if (FlxY_degreex(f) <= 0) return Flx_factorff_i(FlxX_to_Flx(f), T, p);
  xp = Flx_Frobenius(T, p);
  V = FlxqX_factor_squarefree_i(f, xp, get_Flx_mod(T), p);
  l = lg(V);
  F = cgetg(l, t_VEC);
  E = cgetg(l, t_VEC);
  for (i=1, j=1; i < l; i++)
    if (degpol(gel(V,i)))
    {
      GEN Fj = FlxqX_factor_Shoup(gel(V,i), xp, T, p);
      gel(F, j) = Fj;
      gel(E, j) = const_vecsmall(lg(Fj)-1, i);
      j++;
    }
  return sort_factor_pol(FE_concat(F,E,j), cmp_Flx);
}

long
FlxqX_nbfact_Frobenius(GEN S, GEN Xq, GEN T, ulong p)
{
  pari_sp av = avma;
  GEN u = get_FlxqX_mod(S);
  long s;
  if (FlxY_degreex(u) <= 0)
    s = Flx_nbfactff(FlxX_to_Flx(u), T, p);
  else
    s = ddf_to_nbfact(FlxqX_ddf_Shoup(S, Xq, T, p));
  avma = av; return s;
}

long
FlxqX_nbfact(GEN S, GEN T, ulong p)
{
  pari_sp av = avma;
  GEN u = get_FlxqX_mod(S);
  long s;
  if (FlxY_degreex(u) <= 0)
    s = Flx_nbfactff(FlxX_to_Flx(u), T, p);
  else
    s = ddf_to_nbfact(FlxqX_ddf_Shoup(S, FlxqX_Frobenius(S, T, p), T, p));
  avma = av; return s;
}

GEN
FlxqX_factor(GEN x, GEN T, ulong p)
{
  pari_sp av = avma;
  return gerepilecopy(av, FlxqX_factor_Cantor(x, T, p));
}

GEN
F2xqX_factor(GEN x, GEN T)
{
  pari_sp av = avma;
  return gerepilecopy(av, F2xqX_factor_Cantor(x, T));
}

long
FpXQX_ddf_degree(GEN S, GEN XP, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN X, b, g, xq, q;
  long i, j, n, v, B, l, m, bo, ro;
  pari_timer ti;
  hashtable h;

  n = get_FpXQX_degree(S); v = get_FpXQX_var(S);
  X = pol_x(v);
  if (gequal(X,XP)) return 1;
  B = n/2;
  l = usqrt(B);
  m = (B+l-1)/l;
  T = FpX_get_red(T, p);
  S = FpXQX_get_red(S, T, p);
  hash_init_GEN(&h, l+2, gequal, 1);
  hash_insert_long(&h, X,  0);
  hash_insert_long(&h, simplify_shallow(XP), 1);
  bo = brent_kung_optpow(n, l-1, 1);
  ro = l<=1 ? 0: (bo-1)/(l-1) + ((n-1)/bo);
  q = powiu(p, get_FpX_degree(T));
  if (DEBUGLEVEL>=7) timer_start(&ti);
  b = XP;
  if (expi(q) > ro)
  {
    xq = FpXQXQ_powers(b, brent_kung_optpow(n, l-1, 1),  S, T, p);
    if (DEBUGLEVEL>=7) timer_printf(&ti,"FpXQX_ddf_degree: xq baby");
  } else xq = NULL;
  for (i = 3; i <= l+1; i++)
  {
    b = xq ? FpXQX_FpXQXQV_eval(b, xq, S, T, p)
           : FpXQXQ_pow(b, q, S, T, p);
    if (gequal(b,X)) { avma = av; return i-1; }
    hash_insert_long(&h, simplify_shallow(b), i-1);
  }
  if (DEBUGLEVEL>=7) timer_printf(&ti,"FpXQX_ddf_degree: baby");
  g = b;
  xq = FpXQXQ_powers(g, brent_kung_optpow(n, m, 1),  S, T, p);
  if (DEBUGLEVEL>=7) timer_printf(&ti,"FpXQX_ddf_degree: xq giant");
  for(i = 2; i <= m+1; i++)
  {
    g = FpXQX_FpXQXQV_eval(g, xq, S, T, p);
    if (hash_haskey_long(&h, simplify_shallow(g), &j)) { avma=av; return l*i-j; }
  }
  avma = av; return n;
}

static GEN
FpXQX_ddf_Shoup(GEN S, GEN Xq, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN b, g, h, F, f, Sr, xq, q;
  long i, j, n, v, bo, ro;
  long B, l, m;
  pari_timer ti;
  n = get_FpXQX_degree(S); v = get_FpXQX_var(S);
  if (n == 0) return cgetg(1, t_VEC);
  if (n == 1) return mkvec(get_FpXQX_mod(S));
  B = n/2;
  l = usqrt(B);
  m = (B+l-1)/l;
  S = FpXQX_get_red(S, T, p);
  b = cgetg(l+2, t_VEC);
  gel(b, 1) = pol_x(v);
  gel(b, 2) = Xq;
  bo = brent_kung_optpow(n, l-1, 1);
  ro = l<=1 ? 0: (bo-1)/(l-1) + ((n-1)/bo);
  q = powiu(p, get_FpX_degree(T));
  if (DEBUGLEVEL>=7) timer_start(&ti);
  if (expi(q) <= ro)
    for (i = 3; i <= l+1; i++)
      gel(b, i) = FpXQXQ_pow(gel(b, i-1), q, S, T, p);
  else
  {
    xq = FpXQXQ_powers(gel(b, 2), bo, S, T, p);
    if (DEBUGLEVEL>=7) timer_printf(&ti,"FpXQX_ddf_Shoup: xq baby");
    for (i = 3; i <= l+1; i++)
      gel(b, i) = FpXQX_FpXQXQV_eval(gel(b, i-1), xq, S, T, p);
  }
  if (DEBUGLEVEL>=7) timer_printf(&ti,"FpXQX_ddf_Shoup: baby");
  xq = FpXQXQ_powers(gel(b, l+1), brent_kung_optpow(n, m-1, 1), S, T, p);
  if (DEBUGLEVEL>=7) timer_printf(&ti,"FpXQX_ddf_Shoup: xq giant");
  g = cgetg(m+1, t_VEC);
  gel(g, 1) = gel(xq, 2);
  for(i = 2; i <= m; i++)
    gel(g, i) = FpXQX_FpXQXQV_eval(gel(g, i-1), xq, S, T, p);
  if (DEBUGLEVEL>=7) timer_printf(&ti,"FpXQX_ddf_Shoup: giant");
  h = cgetg(m+1, t_VEC);
  for (j = 1; j <= m; j++)
  {
    pari_sp av = avma;
    GEN gj = gel(g, j);
    GEN e = FpXX_sub(gj, gel(b, 1), p);
    for (i = 2; i <= l; i++)
      e = FpXQXQ_mul(e, FpXX_sub(gj, gel(b, i), p), S, T, p);
    gel(h, j) = gerepileupto(av, e);
  }
  if (DEBUGLEVEL>=7) timer_printf(&ti,"FpXQX_ddf_Shoup: diff");
  Sr = get_FpXQX_mod(S);
  F = cgetg(m+1, t_VEC);
  for (j = 1; j <= m; j++)
  {
    GEN u = FpXQX_gcd(Sr, gel(h,j), T, p);
    if (degpol(u))
    {
      u = FpXQX_normalize(u, T, p);
      Sr = FpXQX_div(Sr, u, T, p);
    }
    gel(F,j) = u;
  }
  if (DEBUGLEVEL>=7) timer_printf(&ti,"FpXQX_ddf_Shoup: F");
  f = const_vec(n, pol_1(v));
  for (j = 1; j <= m; j++)
  {
    GEN e = gel(F, j);
    for (i=l-1; i >= 0; i--)
    {
      GEN u = FpXQX_gcd(e, FpXX_sub(gel(g, j), gel(b, i+1), p), T, p);
      if (degpol(u))
      {
        gel(f, l*j-i) = u = FpXQX_normalize(u, T, p);
        e = FpXQX_div(e, u, T, p);
      }
      if (!degpol(e)) break;
    }
  }
  if (DEBUGLEVEL>=7) timer_printf(&ti,"FpXQX_ddf_Shoup: f");
  if (degpol(Sr)) gel(f, degpol(Sr)) = Sr;
  return gerepilecopy(av, f);
}

static GEN
FpXQX_ddf_i(GEN f, GEN T, GEN p)
{
  GEN Xq;
  if (!get_FpXQX_degree(f)) return cgetg(1,t_VEC);
  f = FpXQX_get_red(f, T, p);
  Xq = FpXQX_Frobenius(f, T, p);
  return FpXQX_ddf_Shoup(f, Xq, T, p);
}

static GEN
FpXQX_ddf_raw(GEN f, GEN T, GEN p)
{
  if (lgefint(p)==3)
  {
    ulong pp = p[2];
    GEN M;
    long vT = get_FpX_var(T);
    if (pp==2)
    {
      M = F2xqX_ddf(ZXX_to_F2xX(f, vT),  ZX_to_F2x(get_FpX_mod(T)));
      return mkvec2(F2xXC_to_ZXXC(gel(M,1)), gel(M,2));
    }
    M = FlxqX_ddf(ZXX_to_FlxX(f, pp, vT),  ZXT_to_FlxT(T, pp), pp);
    return mkvec2(FlxXC_to_ZXXC(gel(M,1)), gel(M,2));
  }
  T = FpX_get_red(T, p);
  f = FpXQX_normalize(get_FpXQX_mod(f), T, p);
  return ddf_to_ddf2( FpXQX_ddf_i(f, T, p) );
}

GEN
FpXQX_ddf(GEN x, GEN T, GEN p)
{ pari_sp av = avma; return gerepilecopy(av, FpXQX_ddf_raw(x,T,p)); }

static GEN
FpXQX_degfact_raw(GEN f, GEN T, GEN p)
{
  GEN V;
  long i,l;
  if (lgefint(p)==3)
  {
    ulong pp = p[2];
    long vT = get_FpX_var(T);
    if (pp==2)
      return F2xqX_degfact(ZXX_to_F2xX(f, vT),  ZX_to_F2x(get_FpX_mod(T)));
    else
      return FlxqX_degfact(ZXX_to_FlxX(f, pp, vT),  ZXT_to_FlxT(T, pp), pp);
  }
  T = FpX_get_red(T, p);
  f = FpXQX_normalize(get_FpXQX_mod(f), T, p);
  V = FpXQX_factor_Yun(f, T, p); l = lg(V);
  for (i=1; i < l; i++) gel(V,i) = FpXQX_ddf_i(gel(V,i), T, p);
  return vddf_to_simplefact(V, degpol(f));
}

GEN
FpXQX_degfact(GEN x, GEN T, GEN p)
{ pari_sp av = avma; return gerepilecopy(av, FpXQX_degfact_raw(x,T,p)); }

static void
FpXQX_edf_rec(GEN S, GEN xp, GEN Xp, GEN hp, GEN t, long d, GEN T, GEN p, GEN V, long idx)
{
  GEN Sp = get_FpXQX_mod(S);
  GEN u1, u2, f1, f2;
  GEN h;
  h = FpXQX_get_red(hp, T, p);
  t = FpXQX_rem(t, S, T, p);
  Xp = FpXQX_rem(Xp, h, T, p);
  u1 = FpXQX_roots_split(hp, xp, Xp, h, T, p);
  f1 = FpXQX_gcd(FpXQX_FpXQXQ_eval(u1, t, S, T, p), Sp, T, p);
  f1 = FpXQX_normalize(f1, T, p);
  u2 = FpXQX_div(hp, u1, T, p);
  f2 = FpXQX_div(Sp, f1, T, p);
  if (degpol(u1)==1)
    gel(V, idx) = f1;
  else
    FpXQX_edf_rec(FpXQX_get_red(f1, T, p), xp, Xp, u1, t, d, T, p, V, idx);
  idx += degpol(f1)/d;
  if (degpol(u2)==1)
    gel(V, idx) = f2;
  else
    FpXQX_edf_rec(FpXQX_get_red(f2, T, p), xp, Xp, u2, t, d, T, p, V, idx);
}

static void
FpXQX_edf(GEN Sp, GEN xp, GEN Xp, GEN Xq, long d, GEN T, GEN p, GEN V, long idx)
{
  long n = degpol(Sp), r = n/d, vS = varn(Sp);
  GEN S, h, t;
  pari_timer ti;
  if (r==1) { gel(V, idx) = Sp; return; }
  S = FpXQX_get_red(Sp, T, p);
  Xp = FpXQX_rem(Xp, S, T, p);
  Xq = FpXQX_rem(Xq, S, T, p);
  if (DEBUGLEVEL>=7) timer_start(&ti);
  do
  {
    GEN g = random_FpXQX(n, vS, T, p);
    t = gel(FpXQXQ_auttrace(mkvec2(Xq, g), d, S, T, p), 2);
    if (DEBUGLEVEL>=7) timer_printf(&ti,"FpXQX_edf: FpXQXQ_auttrace");
    h = FpXQXQ_minpoly(t, S, T, p);
    if (DEBUGLEVEL>=7) timer_printf(&ti,"FpXQX_edf: FpXQXQ_minpoly");
  } while (degpol(h) != r);
  Xp = FpXQXQ_pow(pol_x(vS), p, h, T, p);
  FpXQX_edf_rec(S, xp, Xp, h, t, d, T, p, V, idx);
}

static void
FpXQX_edf_simple(GEN Sp, GEN xp, GEN Xp, GEN Xq, long d, GEN T, GEN p, GEN V, long idx)
{
  long v = varn(Sp), n = degpol(Sp), r = n/d;
  GEN S, f, ff;
  long vT = get_FpX_var(T), dT = get_FpX_degree(T);
  if (r==1) { gel(V, idx) = Sp; return; }
  S = FpXQX_get_red(Sp, T, p);
  Xp = FpXQX_rem(Xp, S, T, p);
  Xq = FpXQX_rem(Xq, S, T, p);
  while (1)
  {
    pari_sp btop = avma;
    long i;
    GEN g = random_FpXQX(n, v, T, p);
    GEN t = gel(FpXQXQ_auttrace(mkvec2(Xq, g), d, S, T, p), 2);
    if (lgpol(t) == 0) continue;
    for(i=1; i<=10; i++)
    {
      pari_sp btop2 = avma;
      GEN r = random_FpX(dT, vT, p);
      GEN R = FpXQXQ_halfFrobenius_i(FqX_Fq_add(t, r, T, p), xp, Xp, S, T, p);
      f = FpXQX_gcd(FqX_Fq_add(R, gen_m1, T, p), Sp, T, p);
      if (degpol(f) > 0 && degpol(f) < n) break;
      avma = btop2;
    }
    if (degpol(f) > 0 && degpol(f) < n) break;
    avma = btop;
  }
  f = FpXQX_normalize(f, T, p);
  ff = FpXQX_div(Sp, f , T, p);
  FpXQX_edf_simple(f,  xp, Xp, Xq, d, T, p, V, idx);
  FpXQX_edf_simple(ff, xp, Xp, Xq, d, T, p, V, idx+degpol(f)/d);
}

static GEN
FpXQX_factor_Shoup(GEN S, GEN xp, GEN T, GEN p)
{
  long i, n, s = 0, dT = get_FpX_degree(T), e = expi(powiu(p, dT));
  GEN X, Xp, Xq, D, V;
  pari_timer ti;
  n = get_FpXQX_degree(S);
  S = FpXQX_get_red(S, T, p);
  if (DEBUGLEVEL>=6) timer_start(&ti);
  X  = pol_x(get_FpXQX_var(S));
  Xp = FpXQXQ_pow(X, p, S, T, p);
  Xq = FpXQXQ_Frobenius(xp, Xp, S, T, p);
  if (DEBUGLEVEL>=6) timer_printf(&ti,"FpXQX_Frobenius");
  D = FpXQX_ddf_Shoup(S, Xq, T, p);
  if (DEBUGLEVEL>=6) timer_printf(&ti,"FpXQX_ddf_Shoup");
  s = ddf_to_nbfact(D);
  V = cgetg(s+1, t_COL);
  for (i = 1, s = 1; i <= n; i++)
  {
    GEN Di = gel(D,i);
    long ni = degpol(Di), ri = ni/i;
    if (ni == 0) continue;
    Di = FpXQX_normalize(Di, T, p);
    if (ni == i) { gel(V, s++) = Di; continue; }
    if (ri <= e*expu(e))
      FpXQX_edf(Di, xp, Xp, Xq, i, T, p, V, s);
    else
      FpXQX_edf_simple(Di, xp, Xp, Xq, i, T, p, V, s);
    if (DEBUGLEVEL>=6) timer_printf(&ti,"FpXQX_edf(%ld)",i);
    s += ri;
  }
  return V;
}

static GEN
FpXQX_factor_Cantor(GEN f, GEN T, GEN p)
{
  GEN xp, E, F, V;
  long i, j, l;
  T = FpX_get_red(T, p);
  f = FpXQX_normalize(f, T, p);
  switch(degpol(f))
  {
    case -1: retmkmat2(mkcol(f), mkvecsmall(1));
    case 0: return trivial_fact();
    case 1: retmkmat2(mkcol(f), mkvecsmall(1));
    case 2: return FpXQX_factor_2(f, T, p);
  }
  if (isabsolutepol(f)) return FpX_factorff_i(simplify_shallow(f), T, p);
  xp = FpX_Frobenius(T, p);
  V = FpXQX_factor_Yun(f, T, p);
  l = lg(V);
  F = cgetg(l, t_VEC);
  E = cgetg(l, t_VEC);
  for (i=1, j=1; i < l; i++)
    if (degpol(gel(V,i)))
    {
      GEN Fj = FpXQX_factor_Shoup(gel(V,i), xp, T, p);
      gel(E,j) = const_vecsmall(lg(Fj)-1, i);
      gel(F,j) = Fj; j++;
    }
  return sort_factor_pol(FE_concat(F,E,j), cmp_RgX);
}

long
FpXQX_nbfact_Frobenius(GEN S, GEN Xq, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN u = get_FpXQX_mod(S);
  long s;
  if (lgefint(p)==3)
  {
    ulong pp = p[2];
    long vT = get_FpX_var(T);
    GEN Sp = ZXXT_to_FlxXT(S,pp,vT), Xqp = ZXX_to_FlxX(Xq,pp,vT);
    s = FlxqX_nbfact_Frobenius(Sp, Xqp, ZXT_to_FlxT(T,pp), pp);
  }
  else if (isabsolutepol(u))
    s = FpX_nbfactff(simplify_shallow(u), T, p);
  else
    s = ddf_to_nbfact(FpXQX_ddf_Shoup(S, Xq, T, p));
  avma = av; return s;
}

long
FpXQX_nbfact(GEN S, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN u = get_FpXQX_mod(S);
  long s;
  if (lgefint(p)==3)
  {
    ulong pp = p[2];
    long vT = get_FpX_var(T);
    s = FlxqX_nbfact(ZXXT_to_FlxXT(S,pp,vT), ZXT_to_FlxT(T,pp), pp);
  }
  else if (isabsolutepol(u))
    s = FpX_nbfactff(simplify_shallow(u), T, p);
  else
    s = ddf_to_nbfact(FpXQX_ddf_Shoup(S, FpXQX_Frobenius(S, T, p), T, p));
  avma = av; return s;
}
long
FqX_nbfact(GEN u, GEN T, GEN p)
{ return T ? FpXQX_nbfact(u, T, p): FpX_nbfact(u, p); }

static GEN
FpXQX_factor_Berlekamp_i(GEN f, GEN T, GEN p)
{
  if (lgefint(p)==3)
  {
    ulong pp = p[2];
    GEN M;
    long vT = get_FpX_var(T);
    if (pp==2)
    {
      M = F2xqX_factor_Cantor(ZXX_to_F2xX(f, vT),  ZX_to_F2x(get_FpX_mod(T)));
      return mkvec2(F2xXC_to_ZXXC(gel(M,1)), gel(M,2));
    }
    M = FlxqX_Berlekamp_i(ZXX_to_FlxX(f, pp, vT),  ZXT_to_FlxT(T, pp), pp);
    return mkvec2(FlxXC_to_ZXXC(gel(M,1)), gel(M,2));
  }
  return FpXQX_Berlekamp_i(f, T, p);
}
GEN
FpXQX_factor_Berlekamp(GEN x, GEN T, GEN p)
{ pari_sp av = avma; return gerepilecopy(av, FpXQX_factor_Berlekamp_i(x,T,p)); }

static GEN
FpXQX_factor_i(GEN f, GEN T, GEN p)
{
  if (lgefint(p)==3)
  {
    ulong pp = p[2];
    GEN M;
    long vT = get_FpX_var(T);
    if (pp==2)
    {
      M = F2xqX_factor_Cantor(ZXX_to_F2xX(f, vT),  ZX_to_F2x(get_FpX_mod(T)));
      return mkvec2(F2xXC_to_ZXXC(gel(M,1)), gel(M,2));
    }
    M = FlxqX_factor_Cantor(ZXX_to_FlxX(f, pp, vT),  ZXT_to_FlxT(T, pp), pp);
    return mkvec2(FlxXC_to_ZXXC(gel(M,1)), gel(M,2));
  }
  return FpXQX_factor_Cantor(f, T, p);
}
GEN
FpXQX_factor(GEN x, GEN T, GEN p)
{ pari_sp av = avma; return gerepilecopy(av, FpXQX_factor_i(x,T,p)); }

long
FlxqX_is_squarefree(GEN P, GEN T, ulong p)
{
  pari_sp av = avma;
  GEN z = FlxqX_gcd(P, FlxX_deriv(P, p), T, p);
  avma = av; return degpol(z)==0;
}

long
FqX_is_squarefree(GEN P, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN z = FqX_gcd(P, FqX_deriv(P, T, p), T, p);
  avma = av; return degpol(z)==0;
}

/* as RgX_to_FpXQ(FqX_to_FFX), leaving alone t_FFELT */
static GEN
RgX_to_FFX(GEN x, GEN ff)
{
  long i, lx;
  GEN p = FF_p_i(ff), T = FF_mod(ff), y =  cgetg_copy(x,&lx);
  y[1] = x[1]; if (degpol(T) == 1) T = NULL;
  for (i = 2; i < lx; i++)
  {
    GEN c = gel(x,i);
    gel(y,i) = typ(c) == t_FFELT? c: Fq_to_FF(Rg_to_Fq(c,T,p), ff);
  }
  return y;
}

#define code(t1,t2) ((t1 << 6) | t2)
/* Check types and replace F by a monic normalized FpX having the same roots
 * Don't bother to make constant polynomials monic */
static GEN
factmod_init(GEN f, GEN *pD, GEN *pT, GEN *pp)
{
  const char *s = "factormod";
  GEN T = NULL, p = NULL, D = *pD;
  if (typ(f) != t_POL) pari_err_TYPE(s,f);
  if (!D)
  {
    long pa, t = RgX_type(f, pp, pT, &pa);
    if (t == t_FFELT) return f;
    *pD = gen_0;
    if (t != t_INTMOD && t != code(t_POLMOD,t_INTMOD)) pari_err_TYPE(s,f);
    return RgX_to_FqX(f, *pT, *pp);
  }
  switch(typ(D))
  {
    case t_INT: p = D; break;
    case t_FFELT: { *pD = NULL; *pT = D; return RgX_to_FFX(f,D); }
    case t_VEC:
      if (lg(D) == 3)
      {
        p = gel(D,1);
        T = gel(D,2);
        if (typ(p) == t_INT) break;
        if (typ(T) == t_INT) { swap(T,p); break; }
      }
    default: pari_err_TYPE(s,D);
  }
  if (signe(p) <= 0) pari_err_PRIME(s,p);
  if (T)
  {
    if (typ(T) != t_POL) pari_err_TYPE(s,p);
    T = RgX_to_FpX(T,p);
    if (varncmp(varn(T), varn(f)) <= 0) pari_err_PRIORITY(s, T, "<=", varn(f));
  }
  *pT = T; *pp = p; return RgX_to_FqX(f, T, p);
}
#undef code

static GEN
to_Fq(GEN x, GEN T, GEN p)
{
  long i, lx, tx = typ(x);
  GEN y;

  if (tx == t_INT)
    y = mkintmod(x,p);
  else
  {
    if (tx != t_POL) pari_err_TYPE("to_Fq",x);
    y = cgetg_copy(x,&lx); y[1] = x[1];
    for (i=2; i<lx; i++) gel(y,i) = mkintmod(gel(x,i), p);
  }
  return mkpolmod(y, T);
}
static GEN
to_Fq_pol(GEN x, GEN T, GEN p)
{
  long i, lx = lg(x);
  if (lx == 2)
  {
    GEN y = cgetg(3,t_POL); y[1]=x[1];
    gel(y,2) = mkintmod(gen_0,p); return y;
  }
  for (i = 2; i < lx; i++) gel(x,i) = to_Fq(gel(x,i),T,p);
  return x;
}
static GEN
to_Fq_fact(GEN fa, GEN T, GEN p)
{
  GEN P = gel(fa,1);
  long j, l = lg(P);
  p = icopy(p); T = FpX_to_mod(T, p);
  for (j=1; j<l; j++) gel(P,j) = to_Fq_pol(gel(P,j), T,p);
  return fa;
}
static GEN
to_FqC(GEN P, GEN T, GEN p)
{
  long j, l = lg(P);
  p = icopy(p); T = FpX_to_mod(T, p);
  for (j=1; j<l; j++) gel(P,j) = to_Fq(gel(P,j), T,p);
  return P;
}

static GEN
FpXC_to_mod(GEN x, GEN p)
{ pari_APPLY_type(t_COL, FpX_to_mod(gel(x,i),p)) }
static GEN
FqXC_to_mod(GEN x, GEN T, GEN p)
{ pari_APPLY_type(t_COL, FqX_to_mod(gel(x,i), T, p)) }

GEN
factmod(GEN f, GEN D)
{
  pari_sp av;
  GEN y, F, P, E, T, p;
  f = factmod_init(f, &D, &T,&p);
  if (!D) return FFX_factor(f, T);
  av = avma;
  F = FqX_factor(f, T, p); P = gel(F,1); E = gel(F,2);
  if (!T)
  {
    y = cgetg(3, t_MAT);
    gel(y,1) = FpXC_to_mod(P, p);
    gel(y,2) = Flc_to_ZC(E); return gerepileupto(av, y);
  }
  F = gerepilecopy(av, mkmat2(simplify_shallow(P), Flc_to_ZC(E)));
  return to_Fq_fact(F, T, p);
}
GEN
simplefactmod(GEN f, GEN D)
{
  pari_sp av = avma;
  GEN T, p;
  f = factmod_init(f, &D, &T,&p);
  if (lg(f) <= 3) { avma = av; return trivial_fact(); }
  f = D? FqX_degfact(f, T, p): FFX_degfact(f, T);
  return gerepileupto(av, Flm_to_ZM(f));
}
static GEN
sqf_to_fact(GEN f)
{
  long i, j, l = lg(f);
  GEN P = cgetg(l, t_COL), E = cgetg(l, t_COL);
  for (i = j = 1; i < l; i++)
    if (degpol(gel(f,i)))
    {
      gel(P,j) = gel(f,i);
      gel(E,j) = utoi(i); j++;
    }
  setlg(P,j);
  setlg(E,j); return mkvec2(P,E);
}

GEN
factormodSQF(GEN f, GEN D)
{
  pari_sp av = avma;
  GEN F, T, p;
  f = factmod_init(f, &D, &T,&p);
  if (lg(f) <= 3) { avma = av; return trivial_fact(); }
  if (!D)
    F = sqf_to_fact(FFX_factor_squarefree(f, T));
  else
  {
    F = sqf_to_fact(FqX_factor_squarefree(f,T,p));
    gel(F,1) = FqXC_to_mod(gel(F,1), T,p);
  }
  settyp(F,t_MAT); return gerepilecopy(av, F);
}
GEN
factormodDDF(GEN f, GEN D)
{
  pari_sp av = avma;
  GEN F, T, p;
  f = factmod_init(f, &D, &T,&p);
  if (lg(f) <= 3) { avma = av; return trivial_fact(); }
  if (!D) return FFX_ddf(f, T);
  F = FqX_ddf(f,T,p);
  gel(F,1) = FqXC_to_mod(gel(F,1), T,p);
  gel(F,2) = Flc_to_ZC(gel(F,2));
  settyp(F, t_MAT); return gerepilecopy(av, F);
}

GEN
factormod0(GEN f, GEN p, long flag)
{
  if (flag == 0) return factmod(f,p);
  if (flag != 1) pari_err_FLAG("factormod");
  return simplefactmod(f,p);
}
GEN
polrootsmod(GEN f, GEN D)
{
  pari_sp av;
  GEN y, T, p;
  f = factmod_init(f, &D, &T,&p);
  if (!D) return FFX_roots(f, T);
  av = avma; y = FqX_roots(f, T, p);
  if (!T) return gerepileupto(av, FpC_to_mod(y,p));
  y = gerepilecopy(av, simplify_shallow(y));
  return to_FqC(y, T, p);
}

GEN /* OBSOLETE */
rootmod0(GEN f, GEN p, long flag) { (void)flag; return polrootsmod(f,p); }
GEN /* OBSOLETE */
factorff(GEN f, GEN p, GEN T)
{
  pari_sp av = avma;
  GEN D = (p && T)? mkvec2(T,p): NULL;
  return gerepileupto(av, factmod(f,D));
}
GEN /* OBSOLETE */
polrootsff(GEN f, GEN p, GEN T)
{
  pari_sp av = avma;
  GEN D = (p && T)? mkvec2(T,p): NULL;
  return gerepileupto(av, polrootsmod(f, D));
}
