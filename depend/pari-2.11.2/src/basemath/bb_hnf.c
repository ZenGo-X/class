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

#define dbg_printf(lvl) if (DEBUGLEVEL >= (lvl) + 3) err_printf

/********************************************************************/
/**                                                                **/
/**          BLACK BOX HERMITE RINGS AND HOWELL NORMAL FORM        **/
/**                 contributed by Aurel Page (2017)               **/
/**                                                                **/
/********************************************************************/

/*
  bb_hermite R:
    - add(a,b): a+b
    - neg(a): -a
    - mul(a,b): a*b
    - extgcd(a,b,&small): [d,U] with d in R and U in GL_2(R) such that [0;d] = [a;b]*U.
      set small==1 to assert that U is a 'small' operation (no red needed).
    - rann(a): b in R such that b*R = {x in R | a*x==0}
    - lquo(a,b,&r): q in R such that r=a-b*q is a canonical representative
      of the image of a in R/b*R. The canonical lift of 0 must be 0.
    - unit(a): u unit in R^* such that a*u is a canonical generator of the ideal a*R
    - equal0(a): a==0?
    - equal1(a): a==1?
    - s(n): image of the small integer n in R
    - red(a): unique representative of a as an element of R

  op encoding of elementary operations:
    - t_VECSMALL: the corresponding permutation (vecpermute)
    - [Vecsmall([i,j])]: the transposition Ci <-> Cj
    - [Vecsmall([i]),u], u in R^*: Ci <- Ci*u
    - [Vecsmall([i,j]),a], a in R: Ci <- Ci + Cj*a
    - [Vecsmall([i,j,0]),U], U in GL_2(R): (Ci|Cj) <- (Ci|Cj)*U
*/

struct bb_hermite
{
  GEN (*add)(void*, GEN, GEN);
  GEN (*neg)(void*, GEN);
  GEN (*mul)(void*, GEN, GEN);
  GEN (*extgcd)(void*, GEN, GEN, int*);
  GEN (*rann)(void*, GEN);
  GEN (*lquo)(void*, GEN, GEN, GEN*);
  GEN (*unit)(void*, GEN);
  int (*equal0)(GEN);
  int (*equal1)(GEN);
  GEN (*s)(void*, long);
  GEN (*red)(void*, GEN);
};

static GEN
_Fp_add(void *data, GEN x, GEN y) { (void) data; return addii(x,y); }

static GEN
_Fp_neg(void *data, GEN x) { (void) data; return negi(x); }

static GEN
_Fp_mul(void *data, GEN x, GEN y) { (void) data; return mulii(x,y); }

static GEN
_Fp_rann(void *data, GEN x)
{
  GEN d, N = (GEN)data;
  if (!signe(x)) return gen_1;
  d = gcdii(x,N);
  return modii(diviiexact(N,d),N);
}

static GEN
_Fp_lquo(void *data, GEN x, GEN y, GEN* r) { (void) data; return truedvmdii(x,y,r); }

/* D=MN, p|M => !p|a, p|N => p|a, return M */
static GEN
Z_split(GEN D, GEN a)
{
  long i, n;
  GEN N;
  n = expi(D);
  n = n<2 ? 1 : expu(n)+1;
  for (i=1;i<=n;i++)
    a = Fp_sqr(a,D);
  N = gcdii(a,D);
  return diviiexact(D,N);
}

/* c s.t. gcd(a+cb,N) = gcd(a,b,N) without factoring */
static GEN
Z_stab(GEN a, GEN b, GEN N)
{
  GEN g, a2, N2;
  g = gcdii(a,b);
  g = gcdii(g,N);
  N2 = diviiexact(N,g);
  a2 = diviiexact(a,g);
  return Z_split(N2,a2);
}

static GEN
_Fp_unit(void *data, GEN x)
{
  GEN g,s,v,d,N=(GEN)data,N2;
  long i;
  if (!signe(x)) return NULL;
  g = bezout(x,N,&s,&v);
  if (equali1(g) || equali1(gcdii(s,N))) return mkvec2(g,s);
  N2 = diviiexact(N,g);
  for (i=0; i<5; i++)
  {
    s = addii(s,N2);
    if (equali1(gcdii(s,N))) return mkvec2(g,s);
  }
  d = Z_stab(s,N2,N);
  d = mulii(d,N2);
  v = Fp_add(s,d,N);
  if (equali1(v)) return NULL;
  return mkvec2(g,v);
}

static GEN
_Fp_extgcd(void *data, GEN x, GEN y, int* smallop)
{
  GEN d,u,v,m;
  if (equali1(y))
  {
    *smallop = 1;
    return mkvec2(y,mkmat2(
          mkcol2(gen_1,Fp_neg(x,(GEN)data)),
          mkcol2(gen_0,gen_1)));
  }
  *smallop = 0;
  d = bezout(x,y,&u,&v);
  if (!signe(d)) return mkvec2(d,matid(2));
  m = cgetg(3,t_MAT);
  m = mkmat2(
    mkcol2(diviiexact(y,d),negi(diviiexact(x,d))),
    mkcol2(u,v));
  return mkvec2(d,m);
}

static int
_Fp_equal0(GEN x) { return !signe(x); }

static int
_Fp_equal1(GEN x) { return equali1(x); }

static GEN
_Fp_s(void *data, long x)
{
  if (!x) return gen_0;
  if (x==1) return gen_1;
  return modsi(x,(GEN)data);
}

static GEN
_Fp_red(void *data, GEN x) { return Fp_red(x, (GEN)data); }

/* p not necessarily prime */
static const struct bb_hermite Fp_hermite=
  {_Fp_add,_Fp_neg,_Fp_mul,_Fp_extgcd,_Fp_rann,_Fp_lquo,_Fp_unit,_Fp_equal0,_Fp_equal1,_Fp_s,_Fp_red};

static const struct bb_hermite*
get_Fp_hermite(void **data, GEN p)
{
  *data = (void*)p; return &Fp_hermite;
}

static void
gen_redcol(GEN C, long lim, void* data, const struct bb_hermite *R)
{
  long i;
  for (i=1; i<=lim; i++)
    if (!R->equal0(gel(C,i)))
      gel(C,i) = R->red(data, gel(C,i));
}

static GEN
/* return NULL if a==0 */
/* assume C*a is zero after lim */
gen_rightmulcol(GEN C, GEN a, long lim, int fillzeros, void* data, const struct bb_hermite *R)
{
  GEN Ca,zero;
  long i;
  if (R->equal1(a)) return C;
  if (R->equal0(a)) return NULL;
  Ca = cgetg(lg(C),t_COL);
  for (i=1; i<=lim; i++)
    gel(Ca,i) = R->mul(data, gel(C,i), a);
  if (fillzeros && lim+1 < lg(C))
  {
    zero = R->s(data,0);
    for (i=lim+1; i<lg(C); i++)
      gel(Ca,i) = zero;
  }
  return Ca;
}

static void
/* C1 <- C1 + C2 */
/* assume C2[i]==0 for i>lim */
gen_addcol(GEN C1, GEN C2, long lim, void* data, const struct bb_hermite *R)
{
  long i;
  for (i=1; i<=lim; i++)
    gel(C1,i) = R->add(data, gel(C1,i), gel(C2,i));
}

static void
/* H[,i] <- H[,i] + C*a */
/* assume C is zero after lim */
gen_addrightmul(GEN H, GEN C, GEN a, long i, long lim, void* data, const struct bb_hermite *R)
{
  GEN Ca;
  if (R->equal0(a)) return;
  Ca = gen_rightmulcol(C, a, lim, 0, data, R);
  gen_addcol(gel(H,i), Ca, lim, data, R);
}

static GEN
gen_zerocol(long n, void* data, const struct bb_hermite *R)
{
  GEN C = cgetg(n+1,t_COL), zero = R->s(data, 0);
  long i;
  for (i=1; i<=n; i++) gel(C,i) = zero;
  return C;
}

static GEN
gen_zeromat(long m, long n, void* data, const struct bb_hermite *R)
{
  GEN M = cgetg(n+1,t_MAT);
  long i;
  for (i=1; i<=n; i++) gel(M,i) = gen_zerocol(m, data, R);
  return M;
}

static GEN
gen_colei(long n, long i, void* data, const struct bb_hermite *R)
{
  GEN C = cgetg(n+1,t_COL), zero = R->s(data, 0);
  long j;
  for (j=1; j<=n; j++)
    if (i!=j)   gel(C,j) = zero;
    else        gel(C,j) = R->s(data,1);
  return C;
}

static GEN
gen_matid_hermite(long n, void* data, const struct bb_hermite *R)
{
  GEN M = cgetg(n+1,t_MAT);
  long i;
  for (i=1; i<=n; i++) gel(M,i) = gen_colei(n, i, data, R);
  return M;
}

static GEN
gen_matmul_hermite(GEN A, GEN B, void* data, const struct bb_hermite *R)
{
  GEN M,sum,prod,zero = R->s(data,0);
  long a,b,c,c2,i,j,k;
  RgM_dimensions(A,&a,&c);
  RgM_dimensions(B,&c2,&b);
  if (c!=c2) pari_err_DIM("gen_matmul_hermite");
  M = cgetg(b+1,t_MAT);
  for (j=1; j<=b; j++)
  {
    gel(M,j) = cgetg(a+1,t_COL);
    for (i=1; i<=a; i++)
    {
      sum = zero;
      for (k=1; k<=c; k++)
      {
        prod = R->mul(data, gcoeff(A,i,k), gcoeff(B,k,j));
        sum = R->add(data, sum, prod);
      }
      gcoeff(M,i,j) = sum;
    }
    gen_redcol(gel(M,j), a, data, R);
  }
  return M;
}

static void
/* U = [u1,u2]~, C <- A*u1 + B*u2 */
/* assume both A, B and C are zero after lim */
gen_rightlincomb(GEN A, GEN B, GEN U, GEN *C, long lim, void* data, const struct bb_hermite *R)
{
  GEN Au1, Bu2;
  Au1 = gen_rightmulcol(A, gel(U,1), lim, 1, data, R);
  Bu2 = gen_rightmulcol(B, gel(U,2), lim, 1, data, R);
  if (!Au1 && !Bu2) { *C = gen_zerocol(lg(A)-1, data, R); return; }
  if (!Au1) { *C = Bu2; return; }
  if (!Bu2) { *C = Au1; return; }
  gen_addcol(Au1, Bu2, lim, data, R);
  *C = Au1;
}

static void
/* (H[,i] | H[,j]) <- (H[,i] | H[,j]) * U */
/* assume both columns are zero after lim */
gen_elem(GEN H, GEN U, long i, long j, long lim, void* data, const struct bb_hermite *R)
{
  GEN Hi, Hj;
  Hi = shallowcopy(gel(H,i));
  Hj = shallowcopy(gel(H,j));
  gen_rightlincomb(Hi, Hj, gel(U,1), &gel(H,i), lim, data, R);
  gen_rightlincomb(Hi, Hj, gel(U,2), &gel(H,j), lim, data, R);
}

static int
/* assume C is zero after lim */
gen_is_zerocol(GEN C, long lim, void* data, const struct bb_hermite *R)
{
  long i;
  (void) data;
  for (i=1; i<=lim; i++)
    if (!R->equal0(gel(C,i))) return 0;
  return 1;
}

/* The mkop* functions return NULL if the corresponding operation is the identity */

static GEN
/* Ci <- Ci + Cj*a */
mkoptransv(long i, long j, GEN a, void* data, const struct bb_hermite *R)
{
  a = R->red(data,a);
  if (R->equal0(a)) return NULL;
  return mkvec2(mkvecsmall2(i,j),a);
}

static GEN
/* (Ci|Cj) <- (Ci|Cj)*U */
mkopU(long i, long j, GEN U, void* data, const struct bb_hermite *R)
{
  if (R->equal1(gcoeff(U,1,1)) && R->equal0(gcoeff(U,1,2))
      && R->equal1(gcoeff(U,2,2))) return mkoptransv(i,j,gcoeff(U,2,1),data,R);
  return mkvec2(mkvecsmall3(i,j,0),U);
}

static GEN
/* Ci <- Ci*u */
mkopmul(long i, GEN u, const struct bb_hermite *R)
{
  if (R->equal1(u)) return NULL;
  return mkvec2(mkvecsmall(i),u);
}

static GEN
/* Ci <-> Cj */
mkopswap(long i, long j)
{
  return mkvec(mkvecsmall2(i,j));
}

/* M: t_MAT. Apply the operation op to M by right multiplication. */
static void
gen_rightapply(GEN M, GEN op, void* data, const struct bb_hermite *R)
{
  GEN M2, ind, X;
  long i, j, m = lg(gel(M,1))-1;
  switch (typ(op))
  {
    case t_VECSMALL:
      M2 = vecpermute(M,op);
      for (i=1; i<lg(M); i++) gel(M,i) = gel(M2,i);
      return;
    case t_VEC:
      ind = gel(op,1);
      switch (lg(op))
      {
        case 2:
          swap(gel(M,ind[1]),gel(M,ind[2]));
          return;
        case 3:
          X = gel(op,2);
          i = ind[1];
          switch (lg(ind))
          {
            case 2:
              gel(M,i) = gen_rightmulcol(gel(M,i), X, m, 0, data, R);
              gen_redcol(gel(M,i), m, data, R);
              return;
            case 3:
              gen_addrightmul(M, gel(M,ind[2]), X, i, m, data, R);
              gen_redcol(gel(M,i), m, data, R);
              return;
            case 4:
              j = ind[2];
              gen_elem(M, X, i, j, m, data, R);
              gen_redcol(gel(M,i), m, data, R);
              gen_redcol(gel(M,j), m, data, R);
              return;
          }
      }
  }
}

/* C: t_COL. Apply the operation op to C by left multiplication. */
static void
gen_leftapply(GEN C, GEN op, void* data, const struct bb_hermite *R)
{
  GEN C2, ind, X;
  long i, j;
  switch (typ(op))
  {
    case t_VECSMALL:
      C2 = vecpermute(C,perm_inv(op));
      for (i=1; i<lg(C); i++) gel(C,i) = gel(C2,i);
      return;
    case t_VEC:
      ind = gel(op,1);
      switch (lg(op))
      {
        case 2:
          swap(gel(C,ind[1]),gel(C,ind[2]));
          return;
        case 3:
          X = gel(op,2);
          i = ind[1];
          switch (lg(ind))
          {
            case 2:
              gel(C,i) = R->mul(data, X, gel(C,i));
              gel(C,i) = R->red(data, gel(C,i));
              return;
            case 3:
              j = ind[2];
              if (R->equal0(gel(C,i))) return;
              gel(C,j) = R->add(data, gel(C,j), R->mul(data, X, gel(C,i)));
              return;
            case 4:
              j = ind[2];
              C2 = gen_matmul_hermite(X, mkmat(mkcol2(gel(C,i),gel(C,j))), data, R);
              gel(C,i) = gcoeff(C2,1,1);
              gel(C,j) = gcoeff(C2,2,1);
              return;
          }
      }
  }
}

/* \prod_i det ops[i]. Only makes sense if R is commutative. */
static GEN
gen_detops(GEN ops, void* data, const struct bb_hermite *R)
{
  GEN d = R->s(data,1);
  long i, l = lg(ops);
  for (i = 1; i < l; i++)
  {
    GEN X, op = gel(ops,i);
    switch (typ(op))
    {
      case t_VECSMALL:
        if (perm_sign(op) < 0) d = R->neg(data,d);
        break;
      case t_VEC:
        switch (lg(op))
        {
          case 2:
            d = R->neg(data,d);
            break;
          case 3:
            X = gel(op,2);
            switch (lg(gel(op,1)))
            {
              case 2:
                 d = R->mul(data, d, X);
                 d = R->red(data, d);
                 break;
              case 4:
               {
                 GEN A = gcoeff(X,1,1), B = gcoeff(X,1,2);
                 GEN C = gcoeff(X,2,1), D = gcoeff(X,2,2);
                 GEN AD = R->mul(data,A,D);
                 GEN BC = R->mul(data,B,C);
                 d = R->mul(data, d, R->add(data, AD, R->neg(data,BC)));
                 d = R->red(data, d);
                 break;
               }
            }
            break;
        }
        break;
    }
  }
  return d;
}

static int
gen_is_inv(GEN x, void* data, const struct bb_hermite *R)
{
  GEN u = R->unit(data, x);
  if (!u) return R->equal1(x);
  return R->equal1(gel(u,1));
}

static long
gen_last_inv_diago(GEN A, void* data, const struct bb_hermite *R)
{
  long i,m,n,j;
  RgM_dimensions(A,&m,&n);
  for (i=1,j=n-m+1; i<=m; i++,j++)
    if (!gen_is_inv(gcoeff(A,i,j),data,R)) return i-1;
  return m;
}

static GEN
/* remove_zerocols: 0 none, 1 until square, 2 all */
/* early abort: if not right-invertible, abort, return NULL, and set ops to the
 * non-invertible pivot */
gen_howell_i(GEN A, long remove_zerocols, long permute_zerocols, long early_abort, long only_triangular, GEN* ops, void *data, const struct bb_hermite *R)
{
  pari_sp av = avma, av1;
  GEN H,U,piv=gen_0,u,q,a,perm,iszero,C,zero=R->s(data,0),d,g,r,op,one=R->s(data,1);
  long m,n,i,j,s,si,i2,si2,nbz,lim,extra,maxop=0,nbop=0,lastinv=0;
  int smallop;

  av1 = avma;

  RgM_dimensions(A,&m,&n);
  if (early_abort && n<m)
  {
    if (ops) *ops = zero;
    return NULL;
  }
  if (n<m+1)
  {
    extra = m+1-n;
    H = shallowmatconcat(mkvec2(gen_zeromat(m,extra,data,R),A));
  }
  else
  {
    extra = 0;
    H = RgM_shallowcopy(A);
  }
  RgM_dimensions(H,&m,&n);
  s = n-m; /* shift */

  if(ops)
  {
    maxop = m*n + (m*(m+1))/2 + 1;
    *ops = zerovec(maxop); /* filled with placeholders so gerepile can handle it */
  }

  /* put in triangular form */
  for (i=m,si=s+m; i>0 && si>extra; i--,si--) /* si = s+i */
  {
    if (R->red) gcoeff(H,i,si) = R->red(data, gcoeff(H,i,si));
    /* bottom-right diagonal */
    for (j = extra+1; j < si; j++)
    {
      if (R->red) gcoeff(H,i,j) = R->red(data, gcoeff(H,i,j));
      if (R->equal0(gcoeff(H,i,j))) continue;
      U = R->extgcd(data, gcoeff(H,i,j), gcoeff(H,i,si), &smallop);
      d = gel(U,1);
      U = gel(U,2);
      if (n>10)
      {
        /* normalize diagonal coefficient -> faster reductions on this row */
        u = R->unit(data, d);
        if (u)
        {
          g = gel(u,1);
          u = gel(u,2);
          gcoeff(U,1,2) = R->mul(data, gcoeff(U,1,2), u);
          gcoeff(U,2,2) = R->mul(data, gcoeff(U,2,2), u);
          d = g;
        }
      }
      gen_elem(H, U, j, si, i-1, data, R);
      if (ops)
      {
        op =  mkopU(j,si,U,data,R);
        if (op) { nbop++; gel(*ops, nbop) = op; }
      }
      gcoeff(H,i,j) = zero;
      gcoeff(H,i,si) = d;
      if (R->red && !smallop)
      {
        gen_redcol(gel(H,si), i-1, data, R);
        gen_redcol(gel(H,j), i-1, data, R);
      }
    }


    if (early_abort)
    {
      d = gcoeff(H,i,si);
      u = R->unit(data, d);
      if (u) d = gel(u,1);
      if (!R->equal1(d))
      {
        if (ops) *ops = d;
        return NULL;
      }
    }

    if (gc_needed(av,1))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"gen_howell[1]. i=%ld",i);
      gerepileall(av1,ops?2:1,&H,ops);
    }
  }

  if (!ops)
    lastinv = gen_last_inv_diago(H, data, R);

  /* put in reduced Howell form */
  if (!only_triangular)
  {
    for (i=m,si=s+m; i>0; i--,si--) /* si = s+i */
    {
      /* normalize diagonal coefficient */
      if (i<=lastinv) /* lastinv>0 => !ops */
        gcoeff(H,i,si) = one;
      else
      {
        u = R->unit(data,gcoeff(H,i,si));
        if (u)
        {
          g = gel(u,1);
          u = gel(u,2);
          gel(H,si) = gen_rightmulcol(gel(H,si), u, i-1, 1, data, R);
          gcoeff(H,i,si) = g;
          if (R->red) gen_redcol(gel(H,si), i-1, data, R);
          if (ops)
          {
            op = mkopmul(si,u,R);
            if (op) { nbop++; gel(*ops,nbop) = op; }
          }
        }
        else if (R->red) gcoeff(H,i,si) = R->red(data, gcoeff(H,i,si));
      }
      piv = gcoeff(H,i,si);

      /* reduce above diagonal */
      if (!R->equal0(piv))
      {
        C = gel(H,si);
        for (j=si+1; j<=n; j++)
        {
          if (i<=lastinv) /* lastinv>0 => !ops */
            gcoeff(H,i,j) = zero;
          else
          {
            gcoeff(H,i,j) = R->red(data, gcoeff(H,i,j));
            if (R->equal1(piv)) { q = gcoeff(H,i,j); r = zero; }
            else                q = R->lquo(data, gcoeff(H,i,j), piv, &r);
            q = R->neg(data,q);
            gen_addrightmul(H, C, q, j, i-1, data, R);
            if (ops)
            {
              op = mkoptransv(j,si,q,data,R);
              if (op) { nbop++; gel(*ops,nbop) = op; }
            }
            gcoeff(H,i,j) = r;
          }
        }
      }

      /* ensure Howell property */
      if (i>1)
      {
        a = R->rann(data, piv);
        if (!R->equal0(a))
        {
          gel(H,1) = gen_rightmulcol(gel(H,si), a, i-1, 1, data, R);
          if (gel(H,1) == gel(H,si)) gel(H,1) = shallowcopy(gel(H,1)); /* in case rightmulcol cheated */
          if (ops)
          {
            op = mkoptransv(1,si,a,data,R);
            if (op) { nbop++; gel(*ops,nbop) = op; }
          }
          for (i2=i-1,si2=s+i2; i2>0; i2--,si2--)
          {
            if (R->red) gcoeff(H,i2,1) = R->red(data, gcoeff(H,i2,1));
            if (R->equal0(gcoeff(H,i2,1))) continue;
            if (R->red) gcoeff(H,i2,si2) = R->red(data, gcoeff(H,i2,si2));
            if (R->equal0(gcoeff(H,i2,si2)))
            {
              swap(gel(H,1), gel(H,si2));
              if (ops) { nbop++; gel(*ops,nbop) = mkopswap(1,si2); }
              continue;
            }
            U = R->extgcd(data, gcoeff(H,i2,1), gcoeff(H,i2,si2), &smallop);
            d = gel(U,1);
            U = gel(U,2);
            gen_elem(H, U, 1, si2, i2-1, data, R);
            if (ops)
            {
              op = mkopU(1,si2,U,data,R);
              if (op) { nbop++; gel(*ops,nbop) = op; }
            }
            gcoeff(H,i2,1) = zero;
            gcoeff(H,i2,si2) = d;
            if (R->red && !smallop)
            {
              gen_redcol(gel(H,si2), i2, data, R);
              gen_redcol(gel(H,1), i2-1, data, R);
            }
          }
        }
      }

      if (gc_needed(av,1))
      {
        if (DEBUGMEM>1) pari_warn(warnmem,"gen_howell[2]. i=%ld",i);
        gerepileall(av1,ops?3:2,&H,&piv,ops);
      }
    }
  }

  if (R->red)
    for (j=1; j<=n; j++)
    {
      lim = maxss(0,m-n+j);
      gen_redcol(gel(H,j), lim, data, R);
      for (i=lim+1; i<=m; i++) gcoeff(H,i,j) = zero;
    }

  /* put zero columns first */
  iszero = cgetg(n+1,t_VECSMALL);

  nbz = 0;
  for (i=1; i<=n; i++)
  {
    iszero[i] = gen_is_zerocol(gel(H,i), maxss(0,m-n+i), data, R);
    if (iszero[i]) nbz++;
  }

  j = 1;
  if (permute_zerocols)
  {
    perm = cgetg(n+1, t_VECSMALL);
    for (i=1; i<=n; i++)
      if (iszero[i])
      {
        perm[j] = i;
        j++;
      }
  }
  else perm = cgetg(n-nbz+1, t_VECSMALL);
  for (i=1; i<=n; i++)
    if (!iszero[i])
    {
      perm[j] = i;
      j++;
    }

  if (permute_zerocols || remove_zerocols==2) H = vecpermute(H, perm);
  if (permute_zerocols && remove_zerocols==2) H = vecslice(H, nbz+1, n);
  if (remove_zerocols==1) H = vecslice(H, s+1, n);
  if (permute_zerocols && ops) { nbop++; gel(*ops,nbop) = perm; }

  if (ops) { setlg(*ops, nbop+1); } /* should have nbop <= maxop */

  return H;
}

static GEN
gen_howell(GEN A, long remove_zerocols, long permute_zerocols, long early_abort, long only_triangular, GEN* ops, void *data, const struct bb_hermite *R)
{
  pari_sp av = avma;
  GEN H = gen_howell_i(A, remove_zerocols, permute_zerocols, early_abort, only_triangular, ops, data, R);
  gerepileall(av, ops?2:1, &H, ops);
  return H;
}

static GEN
gen_matimage(GEN A, GEN* U, void *data, const struct bb_hermite *R)
{
  GEN ops, H;
  if (U)
  {
    pari_sp av = avma;
    long m, n, i, r, n2;
    RgM_dimensions(A,&m,&n);
    H = gen_howell_i(A, 2, 1, 0, 0, &ops, data, R);
    r = lg(H)-1;
    *U = shallowmatconcat(mkvec2(gen_zeromat(n, maxss(0,m-n+1), data, R), gen_matid_hermite(n, data, R)));
    n2 = lg(*U)-1;
    for (i=1; i<lg(ops); i++)
      gen_rightapply(*U, gel(ops,i), data, R);
    if (r<n2) *U = vecslice(*U, n2-r+1, n2);
    gerepileall(av, 2, &H, U);
    return H;
  }
  else return gen_howell(A, 2, 0, 0, 0, NULL, data, R);
}

static GEN
/* H in true Howell form: no zero columns */
gen_kernel_howell(GEN H, void *data, const struct bb_hermite *R)
{
  GEN K, piv, FK;
  long m, n, j, j2, i;
  RgM_dimensions(H,&m,&n);
  K = gen_zeromat(n, n, data, R);
  for (j=n,i=m; j>0; j--)
  {
    while (R->equal0(gcoeff(H,i,j))) i--;
    piv = gcoeff(H,i,j);
    if (R->equal0(piv)) continue;
    gcoeff(K,j,j) = R->rann(data, piv);
    if (j<n)
    {
      FK = gen_matmul_hermite(matslice(H,i,i,j+1,n), matslice(K, j+1, n, j+1, n), data, R);
      for (j2=j+1; j2<=n; j2++)
        gcoeff(K,j,j2) = R->neg(data, R->lquo(data, gcoeff(FK,1,j2-j), piv, NULL));
        /* remainder has to be zero */
    }
  }
  return K;
}

static GEN
/* (H,ops) Howell form of A, n = number of columns of A, return a kernel of A */
gen_kernel_from_howell(GEN H, GEN ops, long n, void *data, const struct bb_hermite *R)
{
  pari_sp av;
  GEN K, KH, zC;
  long m, r, n2, nbz, i, o, extra, j;
  RgM_dimensions(H,&m,&r);
  if (!r) return gen_matid_hermite(n, data, R); /* zerology: what if 0==1 in R? */
  n2 = maxss(n,m+1);
  extra = n2-n;
  nbz = n2-r;
  /* compute kernel of augmented matrix */
  KH = gen_kernel_howell(H, data, R);
  zC = gen_zerocol(nbz, data, R);
  K = cgetg(nbz+r+1, t_MAT);
  for (i=1; i<=nbz; i++)
    gel(K,i) = gen_colei(nbz+r, i, data, R);
  for (i=1; i<=r; i++)
    gel(K,nbz+i) = shallowconcat(zC, gel(KH,i));
  for (i=1; i<lg(K); i++)
  {
    av = avma;
    for (o=lg(ops)-1; o>0; o--)
      gen_leftapply(gel(K,i), gel(ops,o), data, R);
    gen_redcol(gel(K,i), nbz+r, data, R);
    gerepileall(av, 1, &gel(K,i));
  }
  /* deduce kernel of original matrix */
  K = rowpermute(K, cyclic_perm(n2,extra));
  K = gen_howell_i(K, 2, 0, 0, 0, NULL, data, R);
  for (j=lg(K)-1, i=n2; j>0; j--)
  {
    while (R->equal0(gcoeff(K,i,j))) i--;
    if (i<=n) return matslice(K, 1, n, 1, j);
  }
  return cgetg(1,t_MAT);
}

/* not GC-clean */
static GEN
gen_kernel(GEN A, GEN* im, void *data, const struct bb_hermite *R)
{
  pari_sp av = avma;
  long n = lg(A)-1;
  GEN H, ops, K;
  H = gen_howell_i(A, 2, 1, 0, 0, &ops, data, R);
  gerepileall(av,2,&H,&ops);
  K = gen_kernel_from_howell(H, ops, n, data, R);
  if (im) *im = H;
  return K;
}

/* right inverse, not GC-clean */
static GEN
gen_inv(GEN A, void* data, const struct bb_hermite *R)
{
  pari_sp av;
  GEN ops, H, U, un=R->s(data,1);
  long m,n,j,o,n2;
  RgM_dimensions(A,&m,&n);
  av = avma;
  H = gen_howell_i(A, 0, 0, 1, 0, &ops, data, R);
  if (!H) pari_err_INV("gen_inv", ops);
  n2 = lg(H)-1;
  ops = gerepilecopy(av,ops); /* get rid of H */
  U = gen_zeromat(n2, m, data, R);
  for (j=1; j<=m; j++)
    gcoeff(U,j+n2-m,j) = un;
  for (j=1; j<=m; j++)
  {
    av = avma;
    for (o=lg(ops)-1; o>0; o--)
      gen_leftapply(gel(U,j), gel(ops,o), data, R);
    gen_redcol(gel(U,j), n2, data, R);
    gerepileall(av, 1, &gel(U,j));
  }
  if (n2>n) U = rowslice(U, n2-n+1, n2);
  return U;
}

/*
  H true Howell form (no zero columns).
  Compute Z = Y - HX canonical representative of R^m mod H(R^n)
*/
static GEN
gen_reduce_mod_howell(GEN H, GEN Y, GEN *X, void* data, const struct bb_hermite *R)
{
  pari_sp av = avma;
  long m,n,i,j;
  GEN Z, q, r, C;
  RgM_dimensions(H,&m,&n);
  if (X) *X = gen_zerocol(n,data,R);
  Z = shallowcopy(Y);
  i = m;
  for (j=n; j>0; j--)
  {
    while (R->equal0(gcoeff(H,i,j))) i--;
    q = R->lquo(data, gel(Z,i), gcoeff(H,i,j), &r);
    gel(Z,i) = r;
    C = gen_rightmulcol(gel(H,j), R->neg(data,q), i, 0, data, R);
    if (C) gen_addcol(Z, C, i-1, data, R);
    if (X) gel(*X,j) = q;
  }
  gen_redcol(Z, lg(Z)-1, data, R);
  if (X)
  {
    gerepileall(av, 2, &Z, X);
    return Z;
  }
  return gerepilecopy(av, Z);
}

/* H: Howell form of A */
/* (m,n): dimensions of original matrix A */
/* return NULL if no solution */
static GEN
gen_solve_from_howell(GEN H, GEN ops, long m, long n, GEN Y, void* data, const struct bb_hermite *R)
{
  pari_sp av = avma;
  GEN Z, X;
  long n2, mH, nH, i;
  RgM_dimensions(H,&mH,&nH);
  n2 = maxss(n,m+1);
  Z = gen_reduce_mod_howell(H, Y, &X, data, R);
  if (!gen_is_zerocol(Z,m,data,R)) { avma=av; return NULL; }

  X = shallowconcat(zerocol(n2-nH),X);
  for (i=lg(ops)-1; i>0; i--) gen_leftapply(X, gel(ops,i), data, R);
  X = vecslice(X, n2-n+1, n2);
  gen_redcol(X, n, data, R);
  return gerepilecopy(av, X);
}

/* return NULL if no solution, not GC-clean */
static GEN
gen_solve(GEN A, GEN Y, GEN* K, void* data, const struct bb_hermite *R)
{
  GEN H, ops, X;
  long m,n;

  RgM_dimensions(A,&m,&n);
  if (!n) m = lg(Y)-1;
  H = gen_howell_i(A, 2, 1, 0, 0, &ops, data, R);
  X = gen_solve_from_howell(H, ops, m, n, Y, data, R);
  if (!X) return NULL;
  if (K) *K = gen_kernel_from_howell(H, ops, n, data, R);
  return X;
}

GEN
matimagemod(GEN A, GEN d, GEN* U)
{
  void *data;
  const struct bb_hermite* R;
  if (typ(A)!=t_MAT || !RgM_is_ZM(A)) pari_err_TYPE("matimagemod", A);
  if (typ(d)!=t_INT) pari_err_TYPE("matimagemod", d);
  if (signe(d)<=0) pari_err_DOMAIN("matimagemod", "d", "<=", gen_0, d);
  if (equali1(d)) return cgetg(1,t_MAT);
  R = get_Fp_hermite(&data, d);
  return gen_matimage(A, U, data, R);
}

/* for testing purpose */
/*
GEN
ZM_hnfmodid2(GEN A, GEN d)
{
  pari_sp av = avma;
  void *data;
  long i;
  const struct bb_hermite* R = get_Fp_hermite(&data, d);
  GEN H;
  if (typ(A)!=t_MAT || !RgM_is_ZM(A)) pari_err_TYPE("ZM_hnfmodid2", A);
  if (typ(d)!=t_INT) pari_err_TYPE("ZM_hnfmodid2", d);
  H = gen_howell_i(A, 1, 0, 0, 0, NULL, data, R);
  for (i=1; i<lg(H); i++)
    if (!signe(gcoeff(H,i,i))) gcoeff(H,i,i) = d;
  return gerepilecopy(av,H);
}
*/

GEN
matdetmod(GEN A, GEN d)
{
  pari_sp av = avma;
  void *data;
  const struct bb_hermite* R;
  long n = lg(A)-1, i;
  GEN D, H, ops;
  if (typ(A)!=t_MAT || !RgM_is_ZM(A)) pari_err_TYPE("matdetmod", A);
  if (typ(d)!=t_INT) pari_err_TYPE("matdetmod", d);
  if (signe(d)<=0) pari_err_DOMAIN("matdetmod", "d", "<=", gen_0, d);
  if (!n) return equali1(d) ? gen_0 : gen_1;
  if (n != nbrows(A)) pari_err_DIM("matdetmod");
  if (equali1(d)) return gen_0;
  R = get_Fp_hermite(&data, d);
  H = gen_howell_i(A, 1, 0, 0, 1, &ops, data, R);
  D = gen_detops(ops, data, R);
  D = Fp_inv(D, d);
  for (i = 1; i <= n; i++) D = Fp_mul(D, gcoeff(H,i,i), d);
  return gerepileuptoint(av, D);
}

GEN
matkermod(GEN A, GEN d, GEN* im)
{
  pari_sp av = avma;
  void *data;
  const struct bb_hermite* R;
  long m,n;
  GEN K;
  if (typ(A)!=t_MAT || !RgM_is_ZM(A)) pari_err_TYPE("matkermod", A);
  if (typ(d)!=t_INT) pari_err_TYPE("matkermod", d);
  if (signe(d)<=0) pari_err_DOMAIN("makermod", "d", "<=", gen_0, d);
  if (equali1(d)) return cgetg(1,t_MAT);
  R = get_Fp_hermite(&data, d);
  RgM_dimensions(A,&m,&n);
  if (!im && m>2*n) /* TODO tune treshold */
    A = shallowtrans(matimagemod(shallowtrans(A),d,NULL));
  K = gen_kernel(A, im, data, R);
  gerepileall(av,im?2:1,&K,im);
  return K;
}

/* left inverse */
GEN
matinvmod(GEN A, GEN d)
{
  pari_sp av = avma;
  void *data;
  const struct bb_hermite* R;
  GEN U;
  if (typ(A)!=t_MAT || !RgM_is_ZM(A)) pari_err_TYPE("matinvmod", A);
  if (typ(d)!=t_INT) pari_err_TYPE("matinvmod", d);
  if (signe(d)<=0) pari_err_DOMAIN("matinvmod", "d", "<=", gen_0, d);
  if (equali1(d)) {
    long m,n;
    RgM_dimensions(A,&m,&n);
    if (m<n) pari_err_INV("matinvmod",A);
    return zeromatcopy(n,m);
  }
  R = get_Fp_hermite(&data, d);
  U = gen_inv(shallowtrans(A), data, R);
  return gerepilecopy(av, shallowtrans(U));
}

/* assume all D[i]>0, not GC-clean */
static GEN
matsolvemod_finite(GEN M, GEN D, GEN Y, long flag)
{
  void *data;
  const struct bb_hermite* R;
  GEN X, K, d;
  long m, n;

  RgM_dimensions(M,&m,&n);
  if (typ(D)==t_COL)
  { /* create extra variables for the D[i] */
    GEN MD;
    long i, i2, extra = 0;
    d = gen_1;
    for (i=1; i<lg(D); i++) d = lcmii(d,gel(D,i));
    for (i=1; i<lg(D); i++) if (!equalii(gel(D,i),d)) extra++;
    MD = cgetg(extra+1,t_MAT);
    i2 = 1;
    for (i=1; i<lg(D); i++)
      if (!equalii(gel(D,i),d))
      {
        gel(MD,i2) = Rg_col_ei(gel(D,i),m,i);
        i2++;
      }
    M = shallowconcat(M,MD);
  }
  else d = D;

  R = get_Fp_hermite(&data, d);
  X = gen_solve(M, Y, flag? &K: NULL, data, R);
  if (!X) return gen_0;
  X = vecslice(X,1,n);

  if (flag)
  {
    K = rowslice(K,1,n);
    K = hnfmodid(shallowconcat(zerocol(n),K),d);
    X = mkvec2(X,K);
  }
  return X;
}

/* Return a solution of congruence system sum M[i,j] X_j = Y_i mod D_i
 * If pU != NULL, put in *pU a Z-basis of the homogeneous system.
 * Works for all non negative D_i but inefficient compared to
 * matsolvemod_finite; to be used only when one D_i is 0 */
static GEN
gaussmoduloall(GEN M, GEN D, GEN Y, GEN *pU)
{
  pari_sp av = avma;
  long n, m, j, l, lM = lg(M);
  GEN delta, H, U, u1, u2, x;

  if (lM == 1)
  {
    long lY = 0;
    switch(typ(Y))
    {
      case t_INT: break;
      case t_COL: lY = lg(Y); break;
      default: pari_err_TYPE("gaussmodulo",Y);
    }
    switch(typ(D))
    {
      case t_INT: break;
      case t_COL: if (lY && lY != lg(D)) pari_err_DIM("gaussmodulo");
                  break;
      default: pari_err_TYPE("gaussmodulo",D);
    }
    if (pU) *pU = cgetg(1, t_MAT);
    return cgetg(1,t_COL);
  }
  n = nbrows(M);
  switch(typ(D))
  {
    case t_COL:
      if (lg(D)-1!=n) pari_err_DIM("gaussmodulo");
      delta = diagonal_shallow(D); break;
    case t_INT: delta = scalarmat_shallow(D,n); break;
    default: pari_err_TYPE("gaussmodulo",D);
      return NULL; /* LCOV_EXCL_LINE */
  }
  switch(typ(Y))
  {
    case t_INT: Y = const_col(n, Y); break;
    case t_COL:
      if (lg(Y)-1!=n) pari_err_DIM("gaussmodulo");
      break;
    default: pari_err_TYPE("gaussmodulo",Y);
      return NULL; /* LCOV_EXCL_LINE */
  }
  H = ZM_hnfall_i(shallowconcat(M,delta), &U, 1);
  Y = hnf_solve(H,Y); if (!Y) return gen_0;
  l = lg(H); /* may be smaller than lM if some moduli are 0 */
  n = l-1;
  m = lg(U)-1 - n;
  u1 = cgetg(m+1,t_MAT);
  u2 = cgetg(n+1,t_MAT);
  for (j=1; j<=m; j++) { GEN c = gel(U,j); setlg(c,lM); gel(u1,j) = c; }
  U += m;
  for (j=1; j<=n; j++) { GEN c = gel(U,j); setlg(c,lM); gel(u2,j) = c; }
  /*       (u1 u2)
   * (M D) (*  * ) = (0 H) */
  u1 = ZM_lll(u1, 0.75, LLL_INPLACE);
  Y = ZM_ZC_mul(u2,Y);
  x = ZC_reducemodmatrix(Y, u1);
  if (!pU) x = gerepileupto(av, x);
  else
  {
    gerepileall(av, 2, &x, &u1);
    *pU = u1;
  }
  return x;
}
/* to be used when one D_i is 0 */
static GEN
msolvemod0(GEN M, GEN D, GEN Y, long flag)
{
  pari_sp av = avma;
  GEN y, x, U;
  if (!flag) return gaussmoduloall(M,D,Y,NULL);
  y = cgetg(3,t_VEC);
  x = gaussmoduloall(M,D,Y,&U);
  if (x == gen_0) { avma = av; return gen_0; }
  gel(y,1) = x;
  gel(y,2) = U; return y;

}
GEN
matsolvemod(GEN M, GEN D, GEN Y, long flag)
{
  pari_sp av = avma;
  long m, n, i, char0 = 0;
  if (typ(M)!=t_MAT || !RgM_is_ZM(M)) pari_err_TYPE("matsolvemod (M)",M);
  RgM_dimensions(M,&m,&n);
  if (typ(D)!=t_INT && (typ(D)!=t_COL || !RgV_is_ZV(D)))
    pari_err_TYPE("matsolvemod (D)",D);
  if (n)
    { if (typ(D)==t_COL && lg(D)!=m+1) pari_err_DIM("matsolvemod [1]"); }
  else
    { if (typ(D)==t_COL) m = lg(D)-1; }
  if (typ(Y)==t_INT)
    Y = const_col(m,Y);
  else if (typ(Y)!=t_COL || !RgV_is_ZV(Y)) pari_err_TYPE("matsolvemod (Y)",Y);
  if (!n && !m) m = lg(Y)-1;
  else if (m != lg(Y)-1) pari_err_DIM("matsolvemod [2]");
  if (typ(D)==t_INT)
  {
    if (signe(D)<0) pari_err_DOMAIN("matsolvemod","D","<",gen_0,D);
    if (!signe(D)) char0 = 1;
  }
  else /*typ(D)==t_COL*/
    for (i=1; i<=m; i++)
    {
      if (signe(gel(D,i))<0)
        pari_err_DOMAIN("matsolvemod","D[i]","<",gen_0,gel(D,i));
      if (!signe(gel(D,i))) char0 = 1;
    }
  return gerepilecopy(av, char0? msolvemod0(M,D,Y,flag)
                               : matsolvemod_finite(M,D,Y,flag));
}
GEN
gaussmodulo2(GEN M, GEN D, GEN Y) { return matsolvemod(M,D,Y, 1); }
GEN
gaussmodulo(GEN M, GEN D, GEN Y) { return matsolvemod(M,D,Y, 0); }
