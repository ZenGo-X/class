/* Copyright (C) 2012  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA. */

#include "pari.h"
#include "paripriv.h"

/*To be moved elsewhere */

static long
Z_trunc(GEN z)
{
  long s = signe(z);
  return s==0 ? 0: (long)(s*mod2BIL(z));
}

static GEN
ZV_trunc_to_zv(GEN z)
{
  long i, l = lg(z);
  GEN x = cgetg(l, t_VECSMALL);
  for (i=1; i<l; i++) x[i] = Z_trunc(gel(z,i));
  return x;
}

/* returns scalar product of vectors x and y with respect to Gram-matrix F */
static long
scp(GEN x, GEN F, GEN y)
{
  long i, j;
  ulong sum = 0;
  long n = lg(F)-1;
  for (i = 1; i <= n; ++i)
  {
    ulong xi = uel(x,i);
    if (xi)
    {
      GEN Fi = gel(F, i);
      for (j = 1; j <= n; ++j)
        sum += xi * uel(Fi,j) * uel(y,j);
    }
  }
  return sum;
}

static GEN
ZM_trunc_to_zm(GEN z)
{
  long i, l = lg(z);
  GEN x = cgetg(l,t_MAT);
  for (i=1; i<l; i++) gel(x,i) = ZV_trunc_to_zv(gel(z,i));
  return x;
}

static GEN
zm_divmod(GEN A, GEN B, ulong p)
{
  pari_sp av = avma;
  GEN Ap = zm_to_Flm(A,p), Bp = zm_to_Flm(B,p);
  GEN C = Flm_center(Flm_mul(Flm_inv(Ap, p), Bp, p), p, p>>1);
  return gerepileupto(av, C);
}

static int
zv_canon(GEN V)
{
  long l = lg(V), j, k;
  for (j = 1; j < l  &&  V[j] == 0; ++j);
  if (j < l  &&  V[j] < 0)
  {
    for (k = j; k < l; ++k)
      V[k] = -V[k];
    return -1;
  }
  return 1;
}

static GEN
ZM_to_zm_canon(GEN V)
{
  GEN W = ZM_to_zm(V);
  long i, l = lg(W);
  for(i=1; i<l; i++)
    (void)zv_canon(gel(W,i));
  return W;
}

static GEN
zm_apply_zm(GEN M, GEN U)
{
  return zm_mul(zm_transpose(U),zm_mul(M, U));
}

static GEN
zmV_apply_zm(GEN v, GEN U)
{
  long i, l;
  GEN V = cgetg_copy(v, &l);
  for(i=1; i<l; i++) gel(V,i) = zm_apply_zm(gel(v,i), U);
  return V;
}

/********************************************************************/
/**                                                                **/
/**      QFAUTO/QFISOM ported from B. Souvignier ISOM program      **/
/**                                                                **/
/********************************************************************/

/* This is a port by Bill Allombert of the program ISOM by Bernt Souvignier
which implement an algorithm published in
W. PLESKEN, B. SOUVIGNIER, Computing Isometries of Lattices,
Journal of Symbolic Computation, Volume 24, Issues 3-4, September 1997,
Pages 327-334, ISSN 0747-7171, 10.1006/jsco.1996.0130.
(http://www.sciencedirect.com/science/article/pii/S0747717196901303)

We thanks Professor Souvignier for giving us permission to port his code.
*/

struct group
{
  GEN     ord;
  GEN     ng;
  GEN     nsg;
  GEN     g;
};

struct fingerprint
{
  GEN diag;
  GEN per;
  GEN e;
};

struct qfauto
{
  long dim;
  GEN F, U, V, W, v;
  ulong p;
};

struct qfcand
{
  long cdep;
  GEN comb;
  GEN bacher_pol;
};

static long
possible(GEN F, GEN Ftr, GEN V, GEN W, GEN per, long I, long J)
{
  long i, j, k, count;
  long n = lg(W)-1, f = lg(F)-1;
  count = 0;
  for (j = 1; j <= n; ++j)
  {
    GEN Wj = gel(W,j), Vj = gel(V,j);
    i = I+1;
    /* check the length of the vector */
    for (k = 1; k <= f  &&  i > I  &&  Wj[k] == mael3(F,k,J,J); ++k)
      /* check the scalar products with the basis-vectors */
      for (i = 1; i <= I; ++i)
        if (zv_dotproduct(Vj,gmael(Ftr,k,per[i])) != coeff(gel(F,k),J,per[i]))
          break;
    if (k == f+1  &&  i > I)
      ++count;
    /* the same for the negative vector */
    i = I+1;
    for (k = 1; k <= f  &&  i > I  &&  Wj[k] == mael3(F,k,J,J); ++k)
      for (i = 1; i <= I ; ++i)
        if (zv_dotproduct(Vj,gmael(Ftr,k,per[i])) != -coeff(gel(F,k),J,per[i]))
          break;
    if (k == f+1  &&  i > I)
      ++count;
  }
  return count;
}

static void
fingerprint(struct fingerprint *fp, struct qfauto *qf)
{
  pari_sp av;
  GEN V=qf->V, W=qf->W, F=qf->F;
  GEN Mf;
  long i, j, k, min;
  long dim = qf->dim, n = lg(V)-1, f = lg(F)-1;
  GEN Ftr;
  fp->per = identity_perm(dim);
  fp->e = cgetg(dim+1, t_VECSMALL);
  fp->diag = cgetg(dim+1, t_VECSMALL);
  av = avma;
  Ftr = cgetg(f+1,t_VEC);
  for (i = 1; i <= f; ++i)
    gel(Ftr,i) = zm_transpose(gel(F,i));
  Mf = zero_Flm_copy(dim, dim);
  /* the first row of the fingerprint has as entry nr. i the number of
   vectors, which have the same length as the i-th basis-vector with
   respect to every invariant form */
  for (j = 1; j <= n; ++j)
  {
    GEN Wj = gel(W,j);
    for (i = 1; i <= dim; ++i)
    {
      for (k = 1; k <= f  &&  Wj[k] == mael3(F,k,i,i); ++k);
      if (k == f+1)
        mael(Mf,1,i) += 2;
    }
  }
  for (i = 1; i <= dim-1; ++i)
  {
    /* a minimal entry != 0 in the i-th row is chosen */
    min = i;
    for (j = i+1; j <= dim; ++j)
    {
      if (mael(Mf,i,fp->per[j]) < mael(Mf,i,fp->per[min]))
        min = j;
    }
    lswap(fp->per[i],fp->per[min]);
    /* the column below the minimal entry is set to 0 */
    for (j = i+1; j <= dim; ++j)
      mael(Mf,j,fp->per[i]) = 0;
    /* compute the row i+1 of the fingerprint */
    for (j = i+1; j <= dim; ++j)
      mael(Mf,i+1,fp->per[j]) = possible(F, Ftr, V, W, fp->per, i, fp->per[j]);
  }
  /* only the diagonal of f will be needed later */
  for (i = 1; i <= dim; ++i)
    fp->diag[i] = mael(Mf,i,fp->per[i]);
  for (i = 1; i <= dim; ++i)
  {
    fp->e[i] = vecvecsmall_search(V,vecsmall_ei(dim,fp->per[i]),0);
    if (!fp->e[i])
      pari_err_BUG("qfisom, standard basis vector not found");
  }
  avma = av;
}

/* The Bacher-polynomial for v[I] with scalar product S is
 * defined as follows: let list be the vectors which have the same length as
 * v[I] and with scalar product S with v[I], for each vector w in list let n_w
 * be the number of pairs (y,z) of vectors in list, such that all scalar
 * products between w,y and z are S, then the Bacher-polynomial is the sum over
 * the w in list of the monomials X^n_w  */

static GEN
bacher(long I, long S, struct qfauto *qf)
{
  pari_sp av=avma;
  GEN V=qf->V, W=qf->W, Fv=gel(qf->v,1);
  GEN  list, listxy, counts, vI;
  long i, j, k, nlist, nxy;
  long n = lg(V)-1;
  long sum, mind, maxd;
  GEN coef;

  /* the Bacher-polynomials of v[I] and -v[I] are equal */
  I = labs(I);
  vI = gel(V,I);
  /* list of vectors that have scalar product S with v[I] */
  list = zero_Flv(2*n);
  nlist = 0;
  for (i = 1; i <= n; ++i)
    if (mael(W,i,1) == mael(W,I,1))
    {
      long s = zv_dotproduct(vI, gel(Fv,i));
      if (s == S)
        list[++nlist] = i;
      if (-s == S)
        list[++nlist] = -i;
    }
  /* there are nlist vectors that have scalar product S with v[I] */
  sum = nlist;
  if (nlist==0) retmkvec2(mkvecsmall3(0,0,0),cgetg(1,t_VEC));
  counts = cgetg(nlist+1, t_VECSMALL);
  listxy = cgetg(nlist+1, t_VECSMALL);
  for (i = 1; i <= nlist; ++i)
  {
    long S1;
    /* listxy is the list of the nxy vectors from list that have scalar
       product S with v[list[i]] */
    for (j = 1; j <= nlist; ++j)
      listxy[j] = 0;
    nxy = 0;
    S1 = list[i] > 0 ? S : -S;
    for (j = 1; j <= nlist; ++j)
    {
      long S2 = list[j] > 0 ? S1 : -S1;
      /* note: for i > 0 is v[-i] = -v[i] */
      if (zv_dotproduct(gel(V,labs(list[i])), gel(Fv,labs(list[j]))) == S2)
        listxy[++nxy] = list[j];
    }
    /* counts[i] is the number of pairs for the vector v[list[i]] */
    counts[i] = 0;
    for (j = 1; j <= nxy; ++j)
    {
      long S1 = listxy[j] > 0 ? S : -S;
      for (k = j+1; k <= nxy; ++k)
      {
        long S2 = listxy[k] > 0 ? S1 : -S1;
        long lj = labs(listxy[j]), lk = labs(listxy[k]);
        if (zv_dotproduct(gel(V,lj), gel(Fv,lk)) == S2)
          counts[i] += 1;
      }
    }
  }
   /* maxd is the maximal degree of the Bacher-polynomial,
      mind the minimal degree */
  maxd = counts[1];
  mind = counts[1];
  for (i = 2; i <= nlist; ++i)
  {
    if (counts[i] > maxd)
      maxd = counts[i];
    else if (counts[i] < mind)
      mind = counts[i];
  }
  coef = zero_Flv(maxd - mind + 1);
  for (i = 1; i <= nlist; ++i)
    coef[1+counts[i] - mind] += 1;
  if (DEBUGLEVEL)
    err_printf("QFIsom: mind=%ld maxd=%ld sum=%ld\n",mind,maxd,sum);
  /* the Bacher-polynomial is now: sum from i=mind to maxd over
     coef[i - mind] * X^i */
  return gerepilecopy(av, mkvec2(mkvecsmall3(sum, mind, maxd),coef));
}

static GEN
init_bacher(long bachdep, struct fingerprint *fp, struct qfauto *qf)
{
  GEN z = cgetg(bachdep+1,t_VEC);
  long i;
  for (i=1;i<=bachdep;i++)
  {
    long bachscp = mael(qf->W,fp->e[i],1) / 2;
    gel(z,i) = bacher(fp->e[i], bachscp, qf);
  }
  return z;
}

/* checks, whether the vector v[I] has the Bacher-polynomial pol  */
static long
bachcomp(GEN pol, long I, GEN V, GEN W, GEN Fv)
{
  pari_sp av = avma;
  GEN co, list, listxy, vI;
  long i, j, k;
  long nlist, nxy, count;
  const long n = lg(V)-1, S = mael(W,I,1) / 2;
  long sum = mael(pol,1,1), mind = mael(pol,1,2), maxd = mael(pol,1,3);
  GEN coef = gel(pol,2);
  vI = gel(V,I);
  list = zero_Flv(sum);
  /* nlist should be equal to pol.sum */
  nlist = 0;
  for (i = 1; i <= n  &&  nlist <= sum; ++i)
  {
    if (mael(W,i,1) == mael(W,I,1))
    {
      long s = zv_dotproduct(vI, gel(Fv,i));
      if (s == S)
      {
        if (nlist < sum)
          list[nlist+1] = i;
        nlist++;
      }
      if (-s == S)
      {
        if (nlist < sum)
          list[nlist+1] = -i;
        nlist++;
      }
    }
  }
  if (nlist != sum)
  {
    /* the number of vectors with scalar product S is already different */
    avma=av; return 0;
  }
  if (nlist == 0) { avma=av; return 1; }
  /* listxy is the list of the nxy vectors from list that have scalar product S
     with v[list[i]] */
  listxy = cgetg(nlist+1,t_VECSMALL);
  co = zero_Flv(maxd - mind + 1);
  for (i = 1; i <= nlist; ++i)
  {
    long S1 = list[i] > 0 ? S : -S;
    for (j = 1; j <= nlist; ++j)
      listxy[j] = 0;
    nxy = 0;
    for (j = 1; j <= nlist; ++j)
    {
      long S2 = list[j] > 0 ? S1 : -S1;
      if (zv_dotproduct(gel(V,labs(list[i])), gel(Fv,labs(list[j]))) == S2)
        listxy[++nxy] = list[j];
    }
    /* count is the number of pairs */
    count = 0;
    for (j = 1; j <= nxy  &&  count <= maxd; ++j)
    {
      long S1 = listxy[j] > 0 ? S : -S;
      for (k = j+1; k <= nxy  &&  count <= maxd; ++k)
      {
        long S2 = listxy[k] > 0 ? S1 : -S1;
        long lj = labs(listxy[j]), lk = labs(listxy[k]);
        if (zv_dotproduct(gel(V,lj), gel(Fv,lk)) == S2)
          count++;
      }
    }
    if (count < mind  ||  count > maxd  ||
        co[count-mind+1] >= coef[count-mind+1])
    /* if the number of pairs is smaller than pol.mind or larger than pol.maxd
       or if the coefficient of X^count becomes now larger than the one in pol,
       then the Bacher-polynomials can not be equal */
    {
      avma = av;
      return 0;
    }
    else
      co[count-mind+1]++;
  }
  /* the Bacher-polynomials are equal */
  avma = av;
  return 1;
}

static GEN
checkvecs(GEN V, GEN F, GEN norm)
{
  long i, j, k;
  long n = lg(V)-1, f = lg(F)-1;
  GEN W = cgetg(n+1, t_MAT);
  j = 0;
  for (i = 1; i <= n; ++i)
  {
    GEN normvec = cgetg(f+1, t_VECSMALL);
    GEN Vi = gel(V,i);
    for (k = 1; k <= f; ++k)
      normvec[k] = scp(Vi, gel(F,k), Vi);
    if (!vecvecsmall_search(norm,normvec,0))
      ++j;
    else
    {
      gel(V,i-j) = Vi;
      gel(W,i-j) = normvec;
    }
  }
  setlg(V, n+1-j);
  setlg(W, n+1-j);
  return W;
}

static long
operate(long nr, GEN A, GEN V)
{
  pari_sp av = avma;
  long im,eps;
  GEN w = zm_zc_mul(A,gel(V,labs(nr)));
  eps = zv_canon(w);
  if (nr < 0) eps = -eps; /* -w */
  im = vecvecsmall_search(V,w,0);
  if (!im) pari_err_BUG("qfauto, image of vector not found");
  avma = av;
  return eps*im;
}

static GEN
orbit(GEN pt, long ipt, long npt, GEN H, GEN V)
{
  pari_sp av = avma;
  long i, cnd, im;
  long n = lg(V)-1, nH = lg(H)-1, no = npt;
  GEN flag = zero_Flv(2*n+1)+n+1; /*We need negative indices*/
  GEN orb = cgetg(2*n+1,t_VECSMALL);
  for (i = 1; i <= npt; ++i)
  {
    orb[i] = pt[ipt+i];
    flag[pt[ipt+i]] = 1;
  }
  for (cnd=1; cnd <= no; ++cnd)
    for (i = 1; i <= nH; ++i)
    {
      im = operate(orb[cnd], gel(H,i), V);
      if (flag[im] == 0)
        /* the image is a new point in the orbit */
      {
        orb[++no] = im;
        flag[im] = 1;
      }
    }
  setlg(orb,no+1); return gerepileuptoleaf(av, orb);
}

/* return the length of the orbit of pt under the first nG matrices in G */

static long
orbitlen(long pt, long orblen, GEN G, long nG, GEN V)
{
  pari_sp av = avma;
  long i, len, cnd;
  long n = lg(V)-1;
  GEN orb, flag;
  /* if flag[i + n+1] = 1, -n <= i <= n, then the point i is already in the
     orbit */
  flag = zero_Flv(2*n + 1)+n+1;
  orb  = zero_Flv(orblen);
  orb[1] = pt;
  flag[pt] = 1;
  len = 1;
  for(cnd = 1; cnd <= len  &&  len < orblen; ++cnd)
    for (i = 1; i <= nG  &&  len < orblen; ++i)
    {
      long im = operate(orb[cnd], gel(G,i), V);
      if (flag[im] == 0)
        /* the image is a new point in the orbit */
      {
        orb[++len] = im;
        flag[im] = 1;
      }
    }
  avma = av;
  return len;
}

/* delete the elements in orb2 from orb1, an entry 0 marks the end of the
 * list, returns the length of orb1 */

static long
orbdelete(GEN orb1, GEN orb2)
{
  long i, j, len;
  long l1 = lg(orb1)-1;
  long l2 = lg(orb2)-1;
  for (i = 1; i <= l1  &&  orb1[i] != 0; ++i);
  len = i - 1;
  for (i = 1; i <= l2  &&  orb2[i] != 0; ++i)
  {
    long o2i = orb2[i];
    for (j = 1; j <= len  &&  orb1[j] != o2i; ++j);
    /* orb1[j] = orb2[i], hence delete orb1[j] from orb1 */
    if (j <= len)
    {
      orb1[j] = orb1[len];
      orb1[len--] = 0;
    }
  }
  return len;
}

static long
orbsubtract(GEN Cs, GEN pt, long ipt, long npt, GEN H, GEN V, long *len)
{
  pari_sp av = avma;
  long nC;
  GEN orb = orbit(pt, ipt, npt, H, V);
  if (len) *len = lg(orb)-1;
  nC = orbdelete(Cs, orb);
  avma = av; return nC;
}

/* Generates the matrix X which has as row per[i] the vector nr. x[i] from the
 * list V */

static GEN
matgen(GEN x, GEN per, GEN V)
{
  long i, j;
  long dim = lg(x)-1;
  GEN X = cgetg(dim+1,t_MAT);
  for (i = 1; i <= dim; ++i)
  {
    long xi = x[i];
    GEN Xp = cgetg(dim+1,t_VECSMALL);
    for (j = 1; j <= dim; ++j)
      Xp[j] = xi > 0? mael(V,xi,j): -mael(V,-xi,j);
    gel(X,per[i]) = Xp;
  }
  return X;
}
/* x1 corresponds to an element X1 mapping some vector e on p1, x2 to an
 * element X2 mapping e on p2 and G is a generator mapping p1 on p2, then
 * S = X1*G*X2^-1 stabilizes e
 */

static GEN
stabil(GEN x1, GEN x2, GEN per, GEN G, GEN V, ulong p)
{
  pari_sp av = avma;
  long i;
  GEN x, XG, X2;
  long dim = lg(x1)-1;
  x = cgetg(dim+1,t_VECSMALL);
  for (i = 1; i <= dim; ++i)
    x[i] = operate(x1[i], G, V);
  /* XG is the composite mapping of the matrix corresponding to x1 and G */
  XG = matgen(x, per, V);
  X2 = matgen(x2, per, V);
  return gerepileupto(av,zm_divmod(X2,XG,p));
}

/* computes the orbit of fp.e[I] under the generators in G->g[I]...G->g[n-1]
 * and elements stabilizing fp.e[I], has some heuristic break conditions, the
 * generators in G->g[i] stabilize fp.e[0]...fp.e[i-1] but not fp.e[i],
 * G->ng[i] is the number of generators in G->g[i], the first G->nsg[i] of
 * which are elements which are obtained as stabilizer elements in
 * <G->g[0],...,G->g[i-1]>, G->ord[i] is the orbit length of fp.e[i] under
 * <G->g[i],...,G->g[n-1]> */

static void
stab(long I, struct group *G, struct fingerprint *fp, GEN V, ulong p)
{
  long len, cnd, tmplen;
  GEN orb, w, flag, H, Hj, S;
  long i, j, k, l, im, nH, nHj, fail;
  long Maxfail, Rest;
  long dim = lg(fp->diag)-1, n = lg(V)-1;
  /* Some heuristic break conditions for the computation of stabilizer elements:
     it would be too expensive to calculate all the stabilizer generators,
     which are obtained from the orbit, since this is highly redundant, on the
     other hand every new generator which enlarges the group is much cheaper
     than one obtained from the backtrack, after Maxfail subsequent stabilizer
     elements, that do not enlarge the group, Rest more elements are calculated
     even if they leave the group unchanged, since it turned out that this is
     often useful in the following steps, increasing the parameters will
     possibly decrease the number of generators for the group, but will
     increase the running time, there is no magic behind this heuristic, tuning
     might be appropriate */

  for (Rest = 0, i = I; i <= dim; ++i)
    if (fp->diag[i] > 1  &&  G->ord[i] < fp->diag[i])
      ++Rest;
  for (Maxfail = Rest, i = 1; i <= dim; ++i)
    if (fp->diag[i] > 1)
      ++Maxfail;
  for (nH = 0, i = I; i <= dim; ++i)
    nH += G->ng[i];
  /* H are the generators of the group in which the stabilizer is computed */
  H = cgetg(nH+1,t_MAT);
  Hj = cgetg(nH+2,t_MAT);
  k = 0;
  for (i = I; i <= dim; ++i)
    for (j = 1; j <= G->ng[i]; ++j)
      gel(H,++k) = gmael(G->g,i,j);
  /* in w[V.n+i] an element is stored that maps fp.e[I] on v[i] */
  w = cgetg(2*n+2,t_VEC);
  /* orb contains the orbit of fp.e[I] */
  orb = zero_Flv(2*n);
  /* if flag[i + V.n] = 1, then the point i is already in the orbit */
  flag = zero_Flv(2*n+1);
  orb[1] = fp->e[I];
  flag[orb[1]+n+1] = 1;
  gel(w,orb[1]+n+1) = cgetg(dim+1,t_VECSMALL);
  for (i = 1; i <= dim; ++i)
    mael(w,orb[1]+n+1,i) = fp->e[i];
  cnd = 1;
  len = 1;
  /* fail is the number of successive failures */
  fail = 0;
  while (cnd <= len && fail < Maxfail+Rest)
  {
    for (i = 1; i <= nH  &&  fail < Maxfail+Rest; ++i)
    {
      if (fail >= Maxfail)
        /* there have already been Maxfail successive failures, now a random
           generator is applied to a random point of the orbit to get Rest more
           stabilizer elements */
      {
        cnd = 1+(long)random_Fl(len);
        i = 1+(long)random_Fl(nH);
      }
      im = operate(orb[cnd], gel(H,i), V);
      if (flag[im+n+1] == 0)
        /* a new element is found, appended to the orbit and an element mapping
           fp.e[I] to im is stored in w[im+V.n] */
      {
        GEN wim;
        orb[++len] = im;
        flag[im+n+1] = 1;
        wim = cgetg(dim+1,t_VECSMALL);
        gel(w,im+n+1) = wim;
        for (j = 1; j <= dim; ++j)
          wim[j] = operate(mael(w,orb[cnd]+n+1,j), gel(H,i), V);
      }
      else
        /* the image was already in the orbit */
      {
        /* j is the first index where the images of the old and the new element
           mapping e[I] on im differ */
        for (j = I; j <= dim; j++)
          if (operate(mael(w,orb[cnd]+n+1,j), gel(H,i), V) != mael(w,im+n+1,j))
            break;
        if (j <= dim  &&
            (G->ord[j] < fp->diag[j] || fail >= Maxfail))
        {
          GEN wo = gel(w,orb[cnd]+n+1);
      /* new stabilizer element S = w[orb[cnd]+V.n] * H[i] * (w[im+V.n])^-1 */
          S = stabil(wo, gel(w,im+n+1), fp->per, gel(H,i), V, p);
          gel(Hj,1) = S;
          nHj = 1;
          for (k = j; k <= dim; ++k)
            for (l = 1; l <= G->ng[k]; ++l)
              gel(Hj,++nHj) = gmael(G->g,k,l);
          tmplen = orbitlen(fp->e[j], fp->diag[j], Hj, nHj, V);
          if (tmplen > G->ord[j]  ||  fail >= Maxfail)
            /* the new stabilizer element S either enlarges the orbit of e[j]
               or it is one of the additional elements after MAXFAIL failures */
          {
            GEN Ggj;
            G->ord[j] = tmplen;
            G->ng[j]++;
            G->nsg[j]++;
            /* allocate memory for the new generator */
            gel(G->g,j) = vec_lengthen(gel(G->g,j),G->ng[j]);
            Ggj = gel(G->g,j);
            /* the new generator is inserted as stabilizer element
               nr. nsg[j]-1 */
            for (k = G->ng[j]; k > G->nsg[j]; --k)
              gel(Ggj,k) = gel(Ggj,k-1);
            gel(Ggj,G->nsg[j]) = S;
            nH++;
            H = vec_lengthen(H, nH);
            Hj = vec_lengthen(Hj, nH+1);
            /* the new generator is appended to H */
            gel(H,nH) = gel(Ggj,G->nsg[j]);
            /* the number of failures is reset to 0 */
            if (fail < Maxfail)
              fail = 0;
            else
              ++fail;
          }
          else
            /*the new stabilizer element S does not enlarge the orbit of e[j]*/
            ++fail;
        }
        else if ((j < dim  &&  fail < Maxfail)  ||
            (j == dim  &&  fail >= Maxfail))
          ++fail;
        /* if S is the identity and fail < Maxfail, nothing is done */
      }
    }
    if (fail < Maxfail)
      ++cnd;
  }
}

/* tests, whether x[1],...,x[I-1] is a partial automorphism, using scalar
 * product combinations and Bacher-polynomials depending on the chosen options,
 * puts the candidates for x[I] (i.e. the vectors vec such that the scalar
 * products of x[1],...,x[I-1],vec are correct) on CI, returns their number
 * (should be fp.diag[I]) */

static long
qfisom_candidates_novec(GEN CI, long I, GEN x, struct qfauto *qf,
       struct qfauto *qff, struct fingerprint *fp)
{
  pari_sp av = avma;
  long i, j, k, okp, okm, nr, fail;
  GEN vec;
  GEN F =qf->F, V=qff->V, W=qff->W, v=qff->v;
  long n = lg(V)-1, f = lg(F)-1;
  vec = cgetg(I,t_VECSMALL);
  /* CI is the list for the candidates */
  for (i = 1; i <= fp->diag[I]; ++i)
    CI[i] = 0;
  nr = 0;
  fail = 0;
  for (j = 1; j <= n  &&  fail == 0; ++j)
  {
    GEN Vj = gel(V,j), Wj = gel(W, j);
    okp = 0;
    okm = 0;
    for (i = 1; i <= f; ++i)
    {
      GEN FAiI = gmael(F,i,fp->per[I]);
      GEN FFvi = gel(v,i);
      /* vec is the vector of scalar products of V.v[j] with the first I base
         vectors x[0]...x[I-1] */
      for (k = 1; k < I; ++k)
      {
        long xk = x[k];
        if (xk > 0)
          vec[k] = zv_dotproduct(Vj, gel(FFvi,xk));
        else
          vec[k] = -zv_dotproduct(Vj, gel(FFvi,-xk));
      }
      for (k = 1; k < I  &&  vec[k] == FAiI[fp->per[k]]; ++k);
      if (k == I  &&  Wj[i] == FAiI[fp->per[I]])
        /* V.v[j] is a candidate for x[I] with respect to the form F.A[i] */
        ++okp;
      for (k = 1; k < I  &&  vec[k] == -FAiI[fp->per[k]]; ++k);
      if (k == I  &&  Wj[i] == FAiI[fp->per[I]])
        /* -V.v[j] is a candidate for x[I] with respect to the form F.A[i] */
        ++okm;
    }
    if (okp == f)
      /* V.v[j] is a candidate for x[I] */
    {
      if (nr < fp->diag[I])
        CI[++nr] = j;
      else
        /* there are too many candidates */
        fail = 1;
    }
    if (okm == f)
      /* -V.v[j] is a candidate for x[I] */
    {
      if (nr < fp->diag[I])
        CI[++nr] = -j;
      else
        /* there are too many candidates */
        fail = 1;
    }
  }
  if (fail == 1)
    nr = 0;
  avma = av;
  return nr;
}

static long
qfisom_candidates(GEN CI, long I, GEN x, struct qfauto *qf,
      struct qfauto *qff, struct fingerprint *fp, struct qfcand *qfcand)
{
  pari_sp av = avma;
  long i, j, k, okp, okm, nr, fail;
  GEN vec;
  GEN xvec, xbase, Fxbase, scpvec;
  long vj, rank, num;
  GEN com, list, trans, ccoef, cF;
  GEN F =qf->F, V=qff->V, W=qff->W, v=qff->v, FF= qff->F;
  long dim = qf->dim, n = lg(V)-1, f = lg(F)-1;
  long nc;
  long DEP = qfcand->cdep, len = f * DEP;
  if (I >= 2  &&  I <= lg(qfcand->bacher_pol))
  {
    long t = labs(x[I-1]);
    GEN bpolI = gel(qfcand->bacher_pol,I-1);
    if (bachcomp(bpolI, t, V, W, gel(v,1)) == 0) return 0;
  }
  if (I==1 || DEP ==0)
    return qfisom_candidates_novec(CI,I,x,qf,qff,fp);
  vec = cgetg(I,t_VECSMALL);
  scpvec = cgetg(len+1,t_VECSMALL);
  com = gel(qfcand->comb,I-1);
  list=gel(com,1); trans = gel(com,2); ccoef = gel(com,3); cF=gel(com,4);
  rank = lg(trans)-1;
  nc = lg(list)-2;
  /* xvec is the list of vector sums which are computed with respect to the
     partial basis in x */
  xvec = zero_Flm_copy(dim,nc+1);
  /* xbase should be a basis for the lattice generated by the vectors in xvec,
     it is obtained via the transformation matrix comb[I-1].trans */
  xbase = cgetg(rank+1,t_MAT);
  for (i = 1; i <= rank; ++i)
    gel(xbase,i) = cgetg(dim+1,t_VECSMALL);
  /* Fxbase is the product of a form F with the base xbase */
  Fxbase = cgetg(rank+1,t_MAT);
  for (i = 1; i <= rank; ++i)
    gel(Fxbase,i) = cgetg(dim+1,t_VECSMALL);
  /* CI is the list for the candidates */
  for (i = 1; i <= fp->diag[I]; ++i)
    CI[i] = 0;
  nr = 0;
  fail = 0;
  for (j = 1; j <= n  &&  fail == 0; ++j)
  {
    long sign;
    GEN Vj = gel(V,j), Wj = gel(W, j);
    okp = 0;
    okm = 0;
    for (k = 1; k <= len; ++k)
      scpvec[k] = 0;
    for (i = 1; i <= f; ++i)
    {
      GEN FAiI = gmael(F,i,fp->per[I]);
      GEN FFvi = gel(v,i);
      /* vec is the vector of scalar products of V.v[j] with the first I base
         vectors x[0]...x[I-1] */
      for (k = 1; k < I; ++k)
      {
        long xk = x[k];
        if (xk > 0)
          vec[k] = zv_dotproduct(Vj, gel(FFvi,xk));
        else
          vec[k] = -zv_dotproduct(Vj, gel(FFvi,-xk));
      }
      for (k = 1; k < I  &&  vec[k] == FAiI[fp->per[k]]; ++k);
      if (k == I  &&  Wj[i] == FAiI[fp->per[I]])
        /* V.v[j] is a candidate for x[I] with respect to the form F.A[i] */
        ++okp;
      for (k = 1; k < I  &&  vec[k] == -FAiI[fp->per[k]]; ++k);
      if (k == I  &&  Wj[i] == FAiI[fp->per[I]])
        /* -V.v[j] is a candidate for x[I] with respect to the form F.A[i] */
        ++okm;
      for (k = I-1; k >= 1  &&  k > I-1-DEP; --k)
        scpvec[(i-1)*DEP+I-k] = vec[k];
    }
    /* check, whether the scalar product combination scpvec is contained in the
       list comb[I-1].list */
    if (!zv_equal0(scpvec))
    {
      sign = zv_canon(scpvec);
      num = vecvecsmall_search(list,scpvec,0);
      if (!num)
        /* scpvec is not found, hence x[0]...x[I-1] is not a partial
           automorphism */
        fail = 1;
      else
        /* scpvec is found and the vector is added to the corresponding
           vector sum */
      {
        GEN xnum = gel(xvec,num);
        for (k = 1; k <= dim; ++k)
          xnum[k] += sign * Vj[k];
      }
    }
    if (okp == f)
      /* V.v[j] is a candidate for x[I] */
    {
      if (nr < fp->diag[I])
        CI[++nr] = j;
      else
        /* there are too many candidates */
        fail = 1;
    }
    if (okm == f)
      /* -V.v[j] is a candidate for x[I] */
    {
      if (nr < fp->diag[I])
        CI[++nr] = -j;
      else
        /* there are too many candidates */
        fail = 1;
    }
  }
  if (fail == 1)
    nr = 0;
  if (nr == fp->diag[I])
  {
    /* compute the basis of the lattice generated by the vectors in xvec via
       the transformation matrix comb[I-1].trans */
    for (i = 1; i <= rank; ++i)
    {
      GEN comtri = gel(trans,i);
      for (j = 1; j <= dim; ++j)
      {
        long xbij = 0;
        for (k = 1; k <= nc+1; ++k)
          xbij += comtri[k] * mael(xvec,k,j);
        mael(xbase,i,j) = xbij;
      }
    }
    /* check, whether the base xbase has the right scalar products */
    for (i = 1; i <= f &&  nr > 0; ++i)
    {
      for (j = 1; j <= rank; ++j)
        for (k = 1; k <= dim; ++k)
          mael(Fxbase,j,k) = zv_dotproduct(gmael(FF,i,k), gel(xbase,j));
      for (j = 1; j <= rank  &&  nr > 0; ++j)
        for (k = 1; k <= j  &&  nr > 0; ++k)
        {
          if (zv_dotproduct(gel(xbase,j), gel(Fxbase,k)) != mael3(cF,i,j,k))
            /* a scalar product is wrong */
            nr = 0;
        }
    }
    for (i = 1; i <= nc+1  &&  nr > 0; ++i)
    {
      GEN comcoi = gel(ccoef,i);
      for (j = 1; j <= dim && nr > 0; ++j)
      {
        vj = 0;
        for (k = 1; k <= rank; ++k)
          vj += comcoi[k] * mael(xbase,k,j);
        if (vj != mael(xvec,i,j))
          /* an entry is wrong */
          nr = 0;
      }
    }
  }
  avma = av;
  return nr;
}

static long
aut(long step, GEN x, GEN C, struct group *G, struct qfauto *qf,
                             struct fingerprint *fp, struct qfcand *cand)
{
  long dim = qf->dim;
  GEN orb = cgetg(2,t_VECSMALL);
  while (mael(C,step,1) != 0)
  {
    if (step < dim)
    {
      long nbc;
      /* choose the image of the base-vector nr. step */
      gel(x,step) = gmael(C,step,1);
      /* check, whether x[0]...x[step] is a partial automorphism and compute
         the candidates for x[step+1] */
      nbc = qfisom_candidates(gel(C,step+1), step+1, x, qf, qf, fp, cand);
      if (nbc == fp->diag[step+1])
        /* go deeper into the recursion */
        if (aut(step+1, x, C, G, qf, fp, cand))
          return 1;
      orb[1] = x[step];
      /* delete the chosen vector from the list of candidates */
      (void)orbdelete(gel(C,step), orb);
    }
    else
    {
      /* a new automorphism is found */
      gel(x,dim) = gmael(C,dim,1);
      return 1;
    }
  }
  return 0;
}

/* search new automorphisms until on all levels representatives for all orbits
 * have been tested */

static void
autom(struct group *G, struct qfauto *qf, struct fingerprint *fp,
                                          struct qfcand *cand)
{
  long i, j, step, im, nC, nH, found, tries;
  GEN  x, bad, H;
  long nbad;
  GEN V = qf->V;
  long dim = qf->dim, n = lg(V)-1;
  long STAB = 1;
  GEN C = cgetg(dim+1,t_VEC);
  /* C[i] is the list of candidates for the image of the i-th base-vector */
  for (i = 1; i <= dim; ++i)
    gel(C,i) = cgetg(fp->diag[i]+1, t_VECSMALL);
  /* x is the new base i.e. x[i] is the index in V.v of the i-th base-vector */
  x = cgetg(dim+1, t_VECSMALL);
  for (step = STAB; step <= dim; ++step)
  {
    if(DEBUGLEVEL) err_printf("QFAuto: Step %ld/%ld\n",step,dim);
    nH = 0;
    for (nH = 0, i = step; i <= dim; ++i)
      nH += G->ng[i];
    H = cgetg(nH+1,t_VEC);
    for (nH = 0, i = step; i <= dim; ++i)
      for (j = 1; j <= G->ng[i]; ++j)
        gel(H,++nH) = gmael(G->g,i,j);
    bad = zero_Flv(2*n);
    nbad = 0;
    /* the first step base-vectors are fixed */
    for (i = 1; i < step; ++i)
      x[i] = fp->e[i];
    /* compute the candidates for x[step] */
    if (fp->diag[step] > 1)
      /* if fp.diag[step] > 1 compute the candidates for x[step] */
      nC = qfisom_candidates(gel(C,step), step, x, qf, qf, fp, cand);
    else
      /* if fp.diag[step] == 1, fp.e[step] is the only candidate */
    {
      mael(C,step,1) = fp->e[step];
      nC = 1;
    }
    /* delete the orbit of the step-th base-vector from the candidates */
    nC = orbsubtract(gel(C,step), fp->e, step-1, 1, H, V, &(G->ord[step]));
    while (nC > 0  &&  (im = mael(C,step,1)) != 0)
    {
      found = 0;
      /* tries vector V.v[im] as image of the step-th base-vector */
      x[step] = im;
      if (step < dim)
      {
        long nbc;
        /* check, whether x[0]...x[step] is a partial basis and compute the
           candidates for x[step+1] */
        nbc = qfisom_candidates(gel(C,step+1), step+1, x, qf, qf, fp, cand);
        if (nbc == fp->diag[step+1])
          /* go into the recursion */
          found = aut(step+1, x, C, G, qf, fp, cand);
        else
          found = 0;
      }
      else
        found = 1;
      if (found == 0)
        /* x[0]...x[step] can not be continued to an automorphism */
      {
        /* delete the orbit of im from the candidates for x[step] */
        nC = orbsubtract(gel(C,step),mkvecsmall(im), 0, 1, H, V, NULL);
        bad[++nbad] = im;
      }
      else
        /* a new generator has been found */
      {
        GEN Gstep;
        ++G->ng[step];
        /* append the new generator to G->g[step] */
        Gstep = vec_lengthen(gel(G->g,step),G->ng[step]);
        gel(Gstep,G->ng[step]) = matgen(x, fp->per, V);
        gel(G->g,step) = Gstep;
        ++nH;
        H = cgetg(nH+1, t_VEC);
        for (nH = 0, i = step; i <= dim; ++i)
          for (j = 1; j <= G->ng[i]; ++j)
            gel(H,++nH) = gmael(G->g,i,j);
        nC = orbsubtract(gel(C,step), fp->e, step-1, 1, H, V, &(G->ord[step]));
        nC = orbsubtract(gel(C,step), bad, 0, nbad, H, V, NULL);
      }
    }
    /* test, whether on step STAB some generators may be omitted */
    if (step == STAB)
      for (tries = G->nsg[step]; tries <= G->ng[step]; ++tries)
      {
        nH = 0;
        for (j = 1; j < tries; ++j)
          gel(H,++nH) = gmael(G->g,step,j);
        for (j = tries+1; j < G->ng[step]; ++j)
          gel(H,++nH) = gmael(G->g,step,j);
        for (i = step+1; i <= dim; ++i)
          for (j = 1; j <= G->ng[i]; ++j)
            gel(H,++nH) = gmael(G->g,i,j);
        if (orbitlen(fp->e[step], G->ord[step], H, nH, V) == G->ord[step])
          /* the generator g[step][tries] can be omitted */
        {
          G->ng[step]--;
          for (i = tries; i < G->ng[step]; ++i)
            gmael(G->g,step,i) = gmael(G->g,step,i+1);
          tries--;
        }
      }
    if (step < dim  &&  G->ord[step] > 1)
      /* calculate stabilizer elements fixing the basis-vectors
         fp.e[0]...fp.e[step] */
      stab(step, G, fp, V, qf->p);
  }
}

#define MAXENTRY (1L<<((BITS_IN_LONG-2)>>1))
#define MAXNORM (1L<<(BITS_IN_LONG-2))

static long
zm_maxdiag(GEN A)
{
  long dim = lg(A)-1;
  long max = coeff(A,1,1);
  long i;
  for (i = 2; i <= dim; ++i)
    if (coeff(A,i,i) > max)
      max = coeff(A,i,i);
  return max;
}

static GEN
init_qfauto(GEN F, GEN U, long max, struct qfauto *qf, GEN norm, GEN minvec)
{
  long i, j, k;
  GEN W, v;
  GEN M = minvec? minvec: gel(minim(zm_to_ZM(gel(F,1)), stoi(max), NULL), 3);
  GEN V = ZM_to_zm_canon(M);
  long n = lg(V)-1, f = lg(F)-1, dim = lg(gel(F,1))-1;
  for (i = 1; i <= n; ++i)
  {
    GEN Vi = gel(V,i);
    for (k = 1; k <= dim; ++k)
    {
      long l = labs(Vi[k]);
      if (l > max)
        max = l;
    }
  }
  if (max > MAXENTRY) pari_err_OVERFLOW("qfisom [lattice too large]");
  qf->p = unextprime(2*max+1);
  V = vecvecsmall_sort_uniq(V);
  if (!norm)
  {
    norm = cgetg(dim+1,t_VEC);
    for (i = 1; i <= dim; ++i)
    {
      GEN Ni = cgetg(f+1,t_VECSMALL);
      for (k = 1; k <= f; ++k)
        Ni[k] = mael3(F,k,i,i);
      gel(norm,i) = Ni;
    }
    norm = vecvecsmall_sort_uniq(norm);
  }
  W = checkvecs(V, F, norm);
  v = cgetg(f+1,t_VEC);
  /* the product of the maximal entry in the short vectors with the maximal
     entry in v[i] should not exceed MAXNORM to avoid overflow */
  max = MAXNORM / max;
  for (i = 1; i <= f; ++i)
  {
    GEN Fi = gel(F,i), vi;
    vi = cgetg(n+1,t_MAT);
    gel(v,i) = vi;
    for (j = 1; j <= n; ++j)
    {
      GEN Vj = gel(V,j);
      GEN vij = cgetg(dim+1, t_VECSMALL);
      gel(vi,j) = vij;
      for (k = 1; k <= dim; ++k)
      {
        vij[k] = zv_dotproduct(gel(Fi,k), Vj);
        if (labs(vij[k]) > max) pari_err_OVERFLOW("qfisom [lattice too large]");
      }
    }
  }
  qf->dim = dim; qf->F = F; qf->V = V; qf->W = W; qf->v = v; qf->U = U;
  return norm;
}

static void
init_qfgroup(struct group *G, struct fingerprint *fp, struct qfauto *qf)
{
  GEN H, M, V = qf->V;
  long nH;
  long i, j, k;
  long dim = qf->dim;
  G->ng  = zero_Flv(dim+1);
  G->nsg = zero_Flv(dim+1);
  G->ord = cgetg(dim+1,t_VECSMALL);
  G->g = cgetg(dim+1,t_VEC);
  for (i = 1; i <= dim; ++i)
    gel(G->g,i) = mkvec(gen_0);
  M = matid_Flm(dim);
  gmael(G->g,1,1) = M;
  G->ng[1] = 1;
  /* -Id is always an automorphism */
  for (i = 1; i <= dim; ++i)
    mael(M,i,i) = -1;
  nH = 0;
  for (i = 1; i <= dim; ++i)
    nH += G->ng[i];
  H = cgetg(nH+1,t_MAT);
  /* calculate the orbit lengths under the automorphisms known so far */
  for (i = 1; i <= dim; ++i)
  {
    if (G->ng[i] > 0)
    {
      nH = 0;
      for (j = i; j <= dim; ++j)
        for (k = 1; k <= G->ng[j]; ++k)
          gel(H,++nH) = gmael(G->g,j,k);
      G->ord[i] = orbitlen(fp->e[i], fp->diag[i], H, nH, V);
    }
    else
      G->ord[i] = 1;
  }
}

/* calculates the scalar products of the vector w with the base vectors
 * v[b[I]] down to v[b[I-dep+1]] with respect to all invariant forms and puts
 * them on scpvec  */
static GEN
scpvector(GEN w, GEN b, long I, long dep, GEN v)
{
  long  i, j, n = lg(v)-1;
  GEN scpvec = zero_Flv(dep*n);
  for (i = I; i >= 1  &&  i > I-dep; --i)
  {
    long bi = b[i];
    if (bi > 0)
      for (j = 1; j <= n; ++j)
        scpvec[1+(j-1)*dep + I-i] = zv_dotproduct(w, gmael(v,j,bi));
    else
      for (j = 1; j <= n; ++j)
        scpvec[1+(j-1)*dep + I-i] = -zv_dotproduct(w, gmael(v,j,-bi));
  }
  return scpvec;
}

/* computes the list of scalar product combinations of the vectors
 * in V.v with the basis-vectors in b */
static GEN
scpvecs(GEN *pt_vec, long I, GEN b, long dep, struct qfauto *qf)
{
  long  i, j, nr, sign;
  GEN list, vec;
  GEN vecnr;
  GEN V = qf->V, F = qf->F, v = qf->v;
  long n = lg(V)-1;
  long dim = lg(gel(F,1))-1;
  long len = (lg(F)-1)*dep;
  /* the first vector in the list is the 0-vector and is not counted */
  list = mkmat(zero_Flv(len));
  vec  = mkmat(zero_Flv(dim));
  for (j = 1; j <= n; ++j)
  {
    GEN Vvj = gel(V,j);
    GEN scpvec = scpvector(Vvj, b, I, dep, v);
    if (zv_equal0(scpvec))
      nr = -1;
    else
    {
      sign = zv_canon(scpvec);
      nr = vecvecsmall_search(list,scpvec,0);
    }
    /* scpvec is already in list */
    if (nr > 0)
    {
      vecnr = gel(vec,nr);
      for (i = 1; i <= dim; ++i)
        vecnr[i] += sign * Vvj[i];
    }
    /* scpvec is a new scalar product combination */
    else if (nr==0)
    {
      nr = vecvecsmall_search(list,scpvec,1);
      list=vec_insert(list,nr,scpvec);
      vec=vec_insert(vec,nr,sign < 0 ? zv_neg(Vvj) : zv_copy(Vvj));
    }
  }
  settyp(list,t_MAT);
  settyp(vec,t_MAT);
  *pt_vec = vec;
  return list;
}

/* com->F[i] is the Gram-matrix of the basis b with respect to F.A[i] */
static GEN
scpforms(GEN b, struct qfauto *qf)
{
  long i, j, k;
  GEN F = qf->F;
  long n = lg(F)-1, dim = lg(gel(F,1))-1;
  long nb = lg(b)-1;
  GEN gram = cgetg(n+1, t_VEC);
  /* Fbi is the list of products of F.A[i] with the vectors in b */
  GEN Fbi = cgetg(nb+1, t_MAT);
  for (j = 1; j <= nb; ++j)
    gel(Fbi, j) = cgetg(dim+1, t_VECSMALL);
  for (i = 1; i <= n; ++i)
  {
    GEN FAi = gel(F,i);
    gel(gram, i) = cgetg(nb+1, t_MAT);
    for (j = 1; j <= nb; ++j)
      for (k = 1; k <= dim; ++k)
        mael(Fbi,j,k) = zv_dotproduct(gel(FAi,k), gel(b,j));
    for (j = 1; j <= nb; ++j)
    {
      GEN comFij = cgetg(nb+1, t_VECSMALL);
      for (k = 1; k <= nb; ++k)
        comFij[k] = zv_dotproduct(gel(b,j), gel(Fbi,k));
      gmael(gram,i,j) = comFij;
    }
  }
  return gram;
}

static GEN
gen_comb(long cdep, GEN A, GEN e, struct qfauto *qf, long lim)
{
  long i, dim = lg(A)-1;
  GEN comb = cgetg(dim+1,t_VEC);
  for (i = 1; i <= dim; ++i)
  {
    pari_sp av = avma;
    GEN trans, ccoef, cF, B, BI;
    GEN sumveclist, sumvecbase;
    GEN list = scpvecs(&sumveclist, i, e, cdep, qf);
    GEN M = zm_to_ZM(sumveclist);
    GEN T = lllgramint(qf_apply_ZM(A,M));
    if (lim && lg(T)-1>=lim) return NULL;
    B = ZM_mul(M,T);
    BI = RgM_inv(B);
    sumvecbase = ZM_trunc_to_zm(B);
    trans = ZM_trunc_to_zm(T);
    ccoef = ZM_trunc_to_zm(RgM_mul(BI,M));
    cF = scpforms(sumvecbase, qf);
    gel(comb,i) = gerepilecopy(av, mkvec4(list, trans, ccoef, cF));
  }
  return comb;
}

static void
init_comb(struct qfcand *cand, GEN A, GEN e, struct qfauto *qf)
{
  long dim = lg(A)-1;
  GEN Am = zm_to_ZM(A);
  for (cand->cdep = 1; ; cand->cdep++)
  {
    cand->comb = gen_comb(cand->cdep, Am, e, qf, (dim+1)>>1);
    if (!cand->comb) break;
  }
  cand->cdep= maxss(1, cand->cdep-1);
  cand->comb = gen_comb(cand->cdep, Am, e, qf, 0);
}

static void
init_flags(struct qfcand *cand, GEN A, struct fingerprint *fp,
                                       struct qfauto *qf, GEN flags)
{
  if (!flags)
  {
    init_comb(cand, A, fp->e, qf);
    cand->bacher_pol = init_bacher(0, fp, qf);
  }
  else
  {
    long cdep, bach;
    if (typ(flags)!=t_VEC || lg(flags)!=3)
      pari_err_TYPE("qfisominit",flags);
    cdep = gtos(gel(flags,1));
    bach = minss(gtos(gel(flags,2)),lg(fp->e)-1);
    if (cdep<0 || bach<0) pari_err_FLAG("qfisom");
    cand->cdep = cdep;
    cand->comb = cdep ? gen_comb(cdep, zm_to_ZM(A), fp->e, qf, 0): NULL;
    cand->bacher_pol = init_bacher(bach, fp, qf);
  }
}

static GEN
gen_group(struct group *G, GEN U)
{
  GEN V;
  long i, j, n=1, dim = lg(G->ord)-1;
  GEN o = gen_1;
  for (i = 1; i <= dim; ++i)
    o = muliu(o, G->ord[i]);
  for (i = 1; i <= dim; ++i)
    n += G->ng[i]-G->nsg[i];
  V = cgetg(n, t_VEC); n = 1;
  for (i = 1; i <= dim; ++i)
    for (j=G->nsg[i]+1; j<=G->ng[i]; j++)
      gel(V,n++) = U ? zm_mul(gel(U,1), zm_mul(gmael(G->g,i,j), gel(U,2)))
                     : gmael(G->g,i,j);
  return mkvec2(o, V);
}

static long
is_qfisom(GEN F)
{
  return (lg(F)==6 && typ(F)==t_VEC && typ(gel(F,1))==t_VEC
                   && typ(gel(F,3))==t_VEC && typ(gel(F,4))==t_VEC);
}

static GEN
unpack_qfisominit(GEN F, GEN *norm, struct qfauto *qf,
      struct fingerprint *fp, struct qfcand *cand)
{
  GEN QF = gel(F,3);
  qf->F = gel(QF,1);
  qf->V = gel(QF,2);
  qf->W = gel(QF,3);
  qf->v = gel(QF,4);
  qf->p = itou(gel(QF,5));
  qf->U = lg(QF)>6 ? gel(QF,6):NULL;
  QF = gel(F,4);
  fp->diag = gel(QF,1);
  fp->per  = gel(QF,2);
  fp->e    = gel(QF,3);
  QF = gel(F,5);
  cand->cdep =itos(gel(QF,1));
  cand->comb = gel(QF,2);
  cand->bacher_pol = gel(QF,3);
  *norm = gel(F,2);
  qf->dim = lg(gmael(F,1,1))-1;
  return qf->F;
}

static GEN
qfisom_bestmat(GEN A, long *pt_max)
{
  long max = zm_maxdiag(A), max2;
  GEN A1 = zm_to_ZM(A), A2;
  GEN U = lllgramint(A1);
  if (lg(U) != lg(A1))
    pari_err_DOMAIN("qfisom","form","is not", strtoGENstr("positive definite"), A1);
  A2 = ZM_to_zm(qf_apply_ZM(A1, U));
  max2 = zm_maxdiag(A2);
  if (max2 < max)
  {
    *pt_max = max2; return mkvec2(ZM_to_zm(U),ZM_to_zm(ZM_inv(U,NULL)));
  } else
  {
    *pt_max = max; return NULL;
  }
}

static GEN
init_qfisom(GEN F, struct fingerprint *fp, struct qfcand *cand,
                   struct qfauto *qf, GEN flags, long *max, GEN minvec)
{
  GEN U, A, norm;
  if (is_qfisom(F))
  {
    F = unpack_qfisominit(F, &norm, qf, fp, cand);
    A = gel(F,1);
    *max = zm_maxdiag(A);
    if (flags)
      init_flags(cand, A, fp, qf, flags);
  }
  else
  {
    if (lg(F)<2) pari_err_TYPE("qfisom",F);
    A = gel(F,1);
    if (lg(A)<2) pari_err_TYPE("qfisom",A);
    if (!minvec)
    {
      U = qfisom_bestmat(A, max);
      if (DEBUGLEVEL) err_printf("QFIsom: max=%ld\n",*max);
      if (U) F = zmV_apply_zm(F, gel(U,1));
    } else
    {
      *max = zm_maxdiag(A); U = NULL;
      if (typ(minvec)==t_VEC && lg(minvec)==4 && typ(gel(minvec,2))==t_INT)
      {
        long n = itos(gel(minvec,2));
        if (n != *max)
          pari_err_DOMAIN("qfisominit","m[2]","!=",stoi(*max),stoi(n));
        minvec = gel(minvec, 3);
      }
      if (typ(minvec)!=t_MAT || lg(gel(minvec,1))!=lg(A))
        pari_err_TYPE("qfisominit",minvec);
    }
    norm = init_qfauto(F, U, *max, qf, NULL, minvec);
    fingerprint(fp, qf);
    if (DEBUGLEVEL) err_printf("QFIsom: fp=%Ps\n",fp->diag);
    init_flags(cand, A, fp, qf, flags);
  }
  return norm;
}

GEN
qfauto(GEN F, GEN flags)
{
  pari_sp av = avma;
  struct fingerprint fp;
  struct group G;
  struct qfcand cand;
  struct qfauto qf;
  long max;
  (void)init_qfisom(F, &fp, &cand, &qf, flags, &max, NULL);
  init_qfgroup(&G, &fp, &qf);
  autom(&G, &qf, &fp, &cand);
  return gerepilecopy(av, gen_group(&G, qf.U));
}

static GEN
qf_to_zmV(GEN F)
{
  return typ(F)==t_MAT ?
     (RgM_is_ZM(F) ? mkvec(ZM_to_zm(F)): NULL)
     : typ(F)==t_VEC ? (RgV_is_ZMV(F) ? ZMV_to_zmV(F): NULL)
     : NULL;
}

GEN
qfauto0(GEN x, GEN flags)
{
  pari_sp av = avma;
  GEN F, G;
  if (is_qfisom(x))
    F = x;
  else
  {
    F = qf_to_zmV(x);
    if (!F) pari_err_TYPE("qfauto",x);
  }
  G = qfauto(F, flags);
  return gerepilecopy(av, mkvec2(gel(G,1), zmV_to_ZMV(gel(G,2))));
}
/* computes the orbit of V.v[pt] under the generators G[0],...,G[nG-1] and
 * elements stabilizing V.v[pt], which are stored in H, returns the number of
 * generators in H */

static GEN
isostab(long pt, GEN G, GEN V, long Maxfail, ulong p)
{
  pari_sp av = avma;
  long  len, cnd, orblen, tmplen, rpt;
  GEN  w, flag, orb;
  long  i, im, nH, fail;
  long dim = lg(gel(V,1))-1, n = lg(V)-1, nG = lg(G)-1;
  GEN H;
  /* a heuristic break condition for the computation of stabilizer elements:
     it would be too expensive to calculate all the stabilizer generators,
     which are obtained from the orbit, since this is highly redundant,
     on the other hand every new generator which enlarges the group reduces the
     number of orbits and hence the number of candidates to be tested, after
     Maxfail subsequent stabilizer elements, that do not enlarge the group, the
     procedure stops, increasing Maxfail will possibly decrease the number of
     tests, but will increase the running time of the stabilizer computation
     there is no magic behind the heuristic, tuning might be appropriate */
  /* H are the generators of the stabilizer of V.v[pt] */
  H = cgetg(2,t_VEC);
  nH = 0;
  /* w[i+V.n] is a matrix that maps V.v[pt] on V.v[i] */
  w = cgetg(2*n+2,t_MAT);
  orb = zero_Flv(2*n);
  /* orblen is the length of the orbit of a random vector in V.v */
  orblen = 1;
  /* if flag[i+V.n] = 1, then the point i is already in the orbit */
  flag = zero_Flv(2*n+1);
  orb[1] = pt;
  flag[orb[1]+n+1] = 1;
  /* w[pt+V.n] is the Identity */
  gel(w,orb[1]+n+1) = matid_Flm(dim);
  cnd = 1;
  len = 1;
  /* fail is the number of successive failures */
  fail = 0;
  while (cnd <= len &&  fail < Maxfail)
  {
    for (i = 1; i <= nG  &&  fail < Maxfail; ++i)
    {
      im = operate(orb[cnd], gel(G,i), V);
      if (flag[im+n+1] == 0)
        /* a new element is found, appended to the orbit and an element mapping
           V.v[pt] to im is stored in w[im+V.n] */
      {
        orb[++len] = im;
        flag[im+n+1] = 1;
        gel(w,im+n+1)= zm_mul(gel(G,i), gel(w,orb[cnd]+n+1));
      }
      else /* the image was already in the orbit */
      {
        GEN B = zm_mul(gel(G,i), gel(w,orb[cnd]+n+1));
        /* check whether the old and the new element mapping pt on im differ */
        if (!zvV_equal(B, gel(w,im+n+1)))
        {
          gel(H,nH+1) = zm_divmod(gel(w,im+n+1),B,p);
          rpt = 1+(long)random_Fl(n);
          tmplen = orbitlen(rpt, 2*n, H, nH+1, V);
          while (tmplen < orblen)
            /* the orbit of this vector is shorter than a previous one, hence
               choose a new random vector */
          {
            rpt = 1+(long)random_Fl(n);
            tmplen = orbitlen(rpt, 2*n, H, nH+1, V);
          }
          if (tmplen > orblen)
            /* the new stabilizer element H[nH] enlarges the group generated by
               H */
          {
            orblen = tmplen;
            /* allocate memory for the new generator */
            H = vec_lengthen(H, (++nH)+1);
            fail = 0;
          }
          else
            /* the new stabilizer element does not enlarge the orbit of a
               random vector */
            ++fail;
        }
        /* if H[nH] is the identity, nothing is done */
      }
    }
    ++cnd;
  }
  setlg(H,nH+1);
  return gerepilecopy(av, H);
}

/* the heart of the program: the recursion */

static long
iso(long step, GEN x, GEN C, struct qfauto *qf, struct qfauto *qff,
    struct fingerprint *fp, GEN G, struct qfcand *cand)
{
  int  i, Maxfail;
  GEN H;
  long dim = qf->dim;
  long found = 0;
  while (mael(C,step,1) != 0  &&  found == 0)
  {
    if (step < dim)
    {
      long nbc;
      /* choose the image of the base-vector nr. step */
      x[step] = mael(C,step,1);
      /* check whether x[0]...x[step] is a partial automorphism and compute the
         candidates for x[step+1] */
      nbc = qfisom_candidates(gel(C,step+1), step+1, x, qf, qff, fp, cand);
      if (nbc == fp->diag[step+1])
      {
        /* go deeper into the recursion */
        Maxfail = 0;
        /* determine the heuristic value of Maxfail for the break condition in
           isostab */
        for (i = 1; i <= step; ++i)
          if (fp->diag[i] > 1)
            Maxfail += 1;
        for (i = step+1; i <= dim; ++i)
          if (fp->diag[i] > 1)
            Maxfail += 2;
        /* compute the stabilizer H of x[step] in G */
        H = isostab(x[step], G, qff->V, Maxfail,qff->p);
        found = iso(step+1, x, C, qf, qff, fp, H, cand);
      }
      if (found == 1)
        return 1;
      /* delete the orbit of the chosen vector from the list of candidates */
      orbsubtract(gel(C,step), x, step-1, 1, G, qff->V, NULL);
    }
    else
    {
      /* an isomorphism is found */
      x[dim] = mael(C,dim,1);
      found = 1;
    }
  }
  return found;
}

/* search for an isometry */

static GEN
isometry(struct qfauto *qf, struct qfauto *qff, struct fingerprint *fp, GEN G,
                                                struct qfcand *cand)

{
  long i, found;
  GEN x;
  long dim = qf->dim;
  GEN C = cgetg(dim+1,t_VEC);
  /* C[i] is the list of candidates for the image of the i-th base-vector */
  for (i = 1; i <= dim; ++i)
    gel(C,i) = cgetg(fp->diag[i]+1, t_VECSMALL);
  x = cgetg(dim+1, t_VECSMALL);
  /* compute the candidates for x[1] */
  qfisom_candidates(gel(C,1), 1, x, qf, qff, fp, cand);
  found = iso(1, x, C, qf, qff, fp, G, cand);
  return found ? matgen(x, fp->per, qff->V): NULL;
}

GEN
qfisominit(GEN F, GEN flags, GEN minvec)
{
  pari_sp av = avma;
  struct fingerprint fp;
  struct qfauto qf;
  struct qfcand cand;
  long max;
  GEN norm = init_qfisom(F, &fp, &cand, &qf, flags, &max, minvec);
  return gerepilecopy(av, mkvec5(F, norm,
                          mkvecn(qf.U?6:5, qf.F, qf.V, qf.W, qf.v, utoi(qf.p), qf.U),
                          mkvec3(fp.diag, fp.per, fp.e),
                          mkvec3(stoi(cand.cdep),cand.comb?cand.comb:cgetg(1,t_VEC),
                                 cand.bacher_pol)));
}

GEN
qfisominit0(GEN x, GEN flags, GEN minvec)
{
  pari_sp av = avma;
  GEN F = qf_to_zmV(x);
  if (!F) pari_err_TYPE("qfisom",x);
  return gerepileupto(av, qfisominit(F, flags, minvec));
}

GEN
qfisom(GEN F, GEN FF, GEN flags, GEN G)
{
  pari_sp av = avma;
  struct fingerprint fp;
  GEN res;
  struct qfauto qf, qff;
  struct qfcand cand;
  long max;
  GEN norm = init_qfisom(F, &fp, &cand, &qf, flags, &max, NULL);
  init_qfauto(FF, NULL, max, &qff, norm, NULL);
  if (lg(qf.W)!=lg(qff.W)
      || !zvV_equal(vecvecsmall_sort(qf.W), vecvecsmall_sort(qff.W)))
    { avma=av; return gen_0; }
  if (!G) G = mkvec(scalar_Flm(-1, qff.dim));
  res = isometry(&qf, &qff, &fp, G, &cand);
  if (!res) { avma=av; return gen_0; }
  return gerepilecopy(av, zm_to_ZM(qf.U? zm_mul(res,gel(qf.U, 2)):res));
}

static GEN
check_qfauto(GEN G)
{
  if (typ(G)==t_VEC && lg(G)==3 && typ(gel(G,1))==t_INT)
    G = gel(G,2);
  return qf_to_zmV(G);
}

GEN
qfisom0(GEN x, GEN y, GEN flags, GEN G)
{
  pari_sp av = avma;
  GEN F, FF;
  if (is_qfisom(x))
    F = x;
  else
  {
    F = qf_to_zmV(x);
    if (!F) pari_err_TYPE("qfisom",x);
  }
  FF = qf_to_zmV(y);
  if (!FF) pari_err_TYPE("qfisom",y);
  if (G) G = check_qfauto(G);
  return gerepileupto(av, qfisom(F, FF, flags, G));
}

static GEN
ZM_to_GAP(GEN M)
{
  pari_sp ltop=avma;
  long rows = nbrows(M), cols = lg(M)-1;
  long i, j, c;
  GEN comma = strtoGENstr(", ");
  GEN bra = strtoGENstr("[");
  GEN ket = strtoGENstr("]");
  GEN s = cgetg(2*rows*cols+2*rows+2,t_VEC);
  gel(s,1) = bra; c=2;
  for (i = 1; i <= rows; ++i)
  {
    if (i > 1)
      gel(s,c++) = comma;
    gel(s,c++) = bra;
    for (j = 1; j <= cols; ++j)
    {
      if (j > 1)
        gel(s,c++) = comma;
      gel(s,c++) = GENtoGENstr(gcoeff(M,i,j));
    }
    gel(s,c++) = ket;
  }
  gel(s,c++) = ket;
  return gerepilecopy(ltop,shallowconcat1(s));
}

GEN
qfautoexport(GEN G, long flag)
{
  pari_sp av = avma;
  long i, lgen,  c = 2;
  GEN gen, str, comma = strtoGENstr(", ");
  if (typ(G)!=t_VEC || lg(G)!=3) pari_err_TYPE("qfautoexport", G);
  if (flag!=0 && flag!=1) pari_err_FLAG("qfautoexport");
  gen = gel(G,2); lgen = lg(gen)-1;
  str = cgetg(2+2*lgen,t_VEC);
  /* in GAP or MAGMA the matrix group is called BG */
  if (flag == 0)
    gel(str,1) = strtoGENstr("Group(");
  else
  {
    long dim = lg(gmael(gen,1,1))-1;
    gel(str,1) = gsprintf("MatrixGroup<%d, Integers() |",dim);
  }
  for(i = 1; i <= lgen; i++)
  {
    if (i!=1)
      gel(str,c++) = comma;
    gel(str,c++) = ZM_to_GAP(gel(gen,i));
  }
  gel(str,c++) = strtoGENstr(flag ? ">":")");
  return gerepilecopy(av, shallowconcat1(str));
}

GEN
qforbits(GEN G, GEN V)
{
  pari_sp av = avma;
  GEN gen, w, W, p, v, orb, o;
  long i, j, n, ng;
  long nborbits = 0;
  gen = check_qfauto(G);
  if (!gen) pari_err_TYPE("qforbits", G);
  if (typ(V)==t_VEC && lg(V)==4
   && typ(gel(V,1))==t_INT && typ(gel(V,2))==t_INT)
    V = gel(V,3);
  if (typ(V)!=t_MAT || !RgM_is_ZM(V)) pari_err_TYPE("qforbits", V);
  n = lg(V)-1; ng = lg(gen)-1;
  W = ZM_to_zm_canon(V);
  p = vecvecsmall_indexsort(W);
  v = vecpermute(W, p);
  w = zero_zv(n);
  orb = cgetg(n+1, t_VEC);
  o = cgetg(n+1, t_VECSMALL);
  if (lg(v) != lg(V)) return gen_0;
  for (i=1; i<=n; i++)
  {
    long cnd, no = 1;
    GEN T;
    if (w[i]) continue;
    w[i] = ++nborbits;
    o[1] = i;
    for (cnd=1; cnd <= no; ++cnd)
      for(j=1; j <= ng; j++)
      {
        long k;
        GEN Vij = zm_zc_mul(gel(gen, j), gel(v, o[cnd]));
        (void) zv_canon(Vij);
        k = vecvecsmall_search(v, Vij, 0);
        if (k == 0) { avma = av; return gen_0; }
        if (w[k] == 0)
        {
          o[++no] = k;
          w[k] = nborbits;
        }
      }
    T = cgetg(no+1, t_VEC);
    for (j=1; j<=no; j++) gel(T,j) = gel(V,p[o[j]]);
    gel(orb, nborbits) = T;
  }
  setlg(orb, nborbits+1);
  return gerepilecopy(av, orb);
}
