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
/*                       BASIC NF OPERATIONS                       */
/*                                                                 */
/*******************************************************************/
#include "pari.h"
#include "paripriv.h"

/*******************************************************************/
/*                                                                 */
/*                OPERATIONS OVER NUMBER FIELD ELEMENTS.           */
/*     represented as column vectors over the integral basis       */
/*                                                                 */
/*******************************************************************/
static GEN
get_tab(GEN nf, long *N)
{
  GEN tab = (typ(nf) == t_MAT)? nf: gel(nf,9);
  *N = nbrows(tab); return tab;
}

/* x != 0, y t_INT. Return x * y (not memory clean if x = 1) */
static GEN
_mulii(GEN x, GEN y) {
  return is_pm1(x)? (signe(x) < 0)? negi(y): y
                  : mulii(x, y);
}

GEN
tablemul_ei_ej(GEN M, long i, long j)
{
  long N;
  GEN tab = get_tab(M, &N);
  tab += (i-1)*N; return gel(tab,j);
}

/* Outputs x.ei, where ei is the i-th elt of the algebra basis.
 * x an RgV of correct length and arbitrary content (polynomials, scalars...).
 * M is the multiplication table ei ej = sum_k M_k^(i,j) ek */
GEN
tablemul_ei(GEN M, GEN x, long i)
{
  long j, k, N;
  GEN v, tab;

  if (i==1) return gcopy(x);
  tab = get_tab(M, &N);
  if (typ(x) != t_COL) { v = zerocol(N); gel(v,i) = gcopy(x); return v; }
  tab += (i-1)*N; v = cgetg(N+1,t_COL);
  /* wi . x = [ sum_j tab[k,j] x[j] ]_k */
  for (k=1; k<=N; k++)
  {
    pari_sp av = avma;
    GEN s = gen_0;
    for (j=1; j<=N; j++)
    {
      GEN c = gcoeff(tab,k,j);
      if (!gequal0(c)) s = gadd(s, gmul(c, gel(x,j)));
    }
    gel(v,k) = gerepileupto(av,s);
  }
  return v;
}
/* as tablemul_ei, assume x a ZV of correct length */
GEN
zk_ei_mul(GEN nf, GEN x, long i)
{
  long j, k, N;
  GEN v, tab;

  if (i==1) return ZC_copy(x);
  tab = get_tab(nf, &N); tab += (i-1)*N;
  v = cgetg(N+1,t_COL);
  for (k=1; k<=N; k++)
  {
    pari_sp av = avma;
    GEN s = gen_0;
    for (j=1; j<=N; j++)
    {
      GEN c = gcoeff(tab,k,j);
      if (signe(c)) s = addii(s, _mulii(c, gel(x,j)));
    }
    gel(v,k) = gerepileuptoint(av, s);
  }
  return v;
}

/* table of multiplication by wi in R[w1,..., wN] */
GEN
ei_multable(GEN TAB, long i)
{
  long k,N;
  GEN m, tab = get_tab(TAB, &N);
  tab += (i-1)*N;
  m = cgetg(N+1,t_MAT);
  for (k=1; k<=N; k++) gel(m,k) = gel(tab,k);
  return m;
}

GEN
zk_multable(GEN nf, GEN x)
{
  long i, l = lg(x);
  GEN mul = cgetg(l,t_MAT);
  gel(mul,1) = x; /* assume w_1 = 1 */
  for (i=2; i<l; i++) gel(mul,i) = zk_ei_mul(nf,x,i);
  return mul;
}
GEN
multable(GEN M, GEN x)
{
  long i, N;
  GEN mul;
  if (typ(x) == t_MAT) return x;
  M = get_tab(M, &N);
  if (typ(x) != t_COL) return scalarmat(x, N);
  mul = cgetg(N+1,t_MAT);
  gel(mul,1) = x; /* assume w_1 = 1 */
  for (i=2; i<=N; i++) gel(mul,i) = tablemul_ei(M,x,i);
  return mul;
}

/* x integral in nf; table of multiplication by x in ZK = Z[w1,..., wN].
 * Return a t_INT if x is scalar, and a ZM otherwise */
GEN
zk_scalar_or_multable(GEN nf, GEN x)
{
  long tx = typ(x);
  if (tx == t_MAT || tx == t_INT) return x;
  x = nf_to_scalar_or_basis(nf, x);
  return (typ(x) == t_COL)? zk_multable(nf, x): x;
}

GEN
nftrace(GEN nf, GEN x)
{
  pari_sp av = avma;
  nf = checknf(nf);
  x = nf_to_scalar_or_basis(nf, x);
  x = (typ(x) == t_COL)? RgV_dotproduct(x, gel(nf_get_Tr(nf),1))
                       : gmulgs(x, nf_get_degree(nf));
  return gerepileupto(av, x);
}
GEN
rnfelttrace(GEN rnf, GEN x)
{
  pari_sp av = avma;
  checkrnf(rnf);
  x = rnfeltabstorel(rnf, x);
  x = (typ(x) == t_POLMOD)? rnfeltdown(rnf, gtrace(x))
                          : gmulgs(x, rnf_get_degree(rnf));
  return gerepileupto(av, x);
}

/* assume nf is a genuine nf, fa a famat */
static GEN
famat_norm(GEN nf, GEN fa)
{
  pari_sp av = avma;
  GEN g = gel(fa,1), e = gel(fa,2), N = gen_1;
  long i, l = lg(g);
  for (i = 1; i < l; i++)
    N = gmul(N, powgi(nfnorm(nf, gel(g,i)), gel(e,i)));
  return gerepileupto(av, N);
}
GEN
nfnorm(GEN nf, GEN x)
{
  pari_sp av = avma;
  nf = checknf(nf);
  if (typ(x) == t_MAT) return famat_norm(nf, x);
  x = nf_to_scalar_or_alg(nf, x);
  x = (typ(x) == t_POL)? RgXQ_norm(x, nf_get_pol(nf))
                       : gpowgs(x, nf_get_degree(nf));
  return gerepileupto(av, x);
}

GEN
rnfeltnorm(GEN rnf, GEN x)
{
  pari_sp av = avma;
  checkrnf(rnf);
  x = rnfeltabstorel(rnf, x);
  x = (typ(x) == t_POLMOD)? rnfeltdown(rnf, gnorm(x))
                          : gpowgs(x, rnf_get_degree(rnf));
  return gerepileupto(av, x);
}

/* x + y in nf */
GEN
nfadd(GEN nf, GEN x, GEN y)
{
  pari_sp av = avma;
  GEN z;

  nf = checknf(nf);
  x = nf_to_scalar_or_basis(nf, x);
  y = nf_to_scalar_or_basis(nf, y);
  if (typ(x) != t_COL)
  { z = (typ(y) == t_COL)? RgC_Rg_add(y, x): gadd(x,y); }
  else
  { z = (typ(y) == t_COL)? RgC_add(x, y): RgC_Rg_add(x, y); }
  return gerepileupto(av, z);
}
/* x - y in nf */
GEN
nfsub(GEN nf, GEN x, GEN y)
{
  pari_sp av = avma;
  GEN z;

  nf = checknf(nf);
  x = nf_to_scalar_or_basis(nf, x);
  y = nf_to_scalar_or_basis(nf, y);
  if (typ(x) != t_COL)
  { z = (typ(y) == t_COL)? Rg_RgC_sub(x,y): gsub(x,y); }
  else
  { z = (typ(y) == t_COL)? RgC_sub(x,y): RgC_Rg_sub(x,y); }
  return gerepileupto(av, z);
}

/* product of x and y in nf */
GEN
nfmul(GEN nf, GEN x, GEN y)
{
  GEN z;
  pari_sp av = avma;

  if (x == y) return nfsqr(nf,x);

  nf = checknf(nf);
  x = nf_to_scalar_or_basis(nf, x);
  y = nf_to_scalar_or_basis(nf, y);
  if (typ(x) != t_COL)
  {
    if (isintzero(x)) return gen_0;
    z = (typ(y) == t_COL)? RgC_Rg_mul(y, x): gmul(x,y); }
  else
  {
    if (typ(y) != t_COL)
    {
      if (isintzero(y)) return gen_0;
      z = RgC_Rg_mul(x, y);
    }
    else
    {
      GEN dx, dy;
      x = Q_remove_denom(x, &dx);
      y = Q_remove_denom(y, &dy);
      z = nfmuli(nf,x,y);
      dx = mul_denom(dx,dy);
      if (dx) z = ZC_Z_div(z, dx);
    }
  }
  return gerepileupto(av, z);
}
/* square of x in nf */
GEN
nfsqr(GEN nf, GEN x)
{
  pari_sp av = avma;
  GEN z;

  nf = checknf(nf);
  x = nf_to_scalar_or_basis(nf, x);
  if (typ(x) != t_COL) z = gsqr(x);
  else
  {
    GEN dx;
    x = Q_remove_denom(x, &dx);
    z = nfsqri(nf,x);
    if (dx) z = RgC_Rg_div(z, sqri(dx));
  }
  return gerepileupto(av, z);
}

/* x a ZC, v a t_COL of ZC/Z */
GEN
zkC_multable_mul(GEN v, GEN x)
{
  long i, l = lg(v);
  GEN y = cgetg(l, t_COL);
  for (i = 1; i < l; i++)
  {
    GEN c = gel(v,i);
    if (typ(c)!=t_COL) {
      if (!isintzero(c)) c = ZC_Z_mul(gel(x,1), c);
    } else {
      c = ZM_ZC_mul(x,c);
      if (ZV_isscalar(c)) c = gel(c,1);
    }
    gel(y,i) = c;
  }
  return y;
}

GEN
nfC_multable_mul(GEN v, GEN x)
{
  long i, l = lg(v);
  GEN y = cgetg(l, t_COL);
  for (i = 1; i < l; i++)
  {
    GEN c = gel(v,i);
    if (typ(c)!=t_COL) {
      if (!isintzero(c)) c = RgC_Rg_mul(gel(x,1), c);
    } else {
      c = RgM_RgC_mul(x,c);
      if (QV_isscalar(c)) c = gel(c,1);
    }
    gel(y,i) = c;
  }
  return y;
}

GEN
nfC_nf_mul(GEN nf, GEN v, GEN x)
{
  long tx;
  GEN y;

  x = nf_to_scalar_or_basis(nf, x);
  tx = typ(x);
  if (tx != t_COL)
  {
    long l, i;
    if (tx == t_INT)
    {
      long s = signe(x);
      if (!s) return zerocol(lg(v)-1);
      if (is_pm1(x)) return s > 0? leafcopy(v): RgC_neg(v);
    }
    l = lg(v); y = cgetg(l, t_COL);
    for (i=1; i < l; i++)
    {
      GEN c = gel(v,i);
      if (typ(c) != t_COL) c = gmul(c, x); else c = RgC_Rg_mul(c, x);
      gel(y,i) = c;
    }
    return y;
  }
  else
  {
    GEN dx;
    x = zk_multable(nf, Q_remove_denom(x,&dx));
    y = nfC_multable_mul(v, x);
    return dx? RgC_Rg_div(y, dx): y;
  }
}
static GEN
mulbytab(GEN M, GEN c)
{ return typ(c) == t_COL? RgM_RgC_mul(M,c): RgC_Rg_mul(gel(M,1), c); }
GEN
tablemulvec(GEN M, GEN x, GEN v)
{
  long l, i;
  GEN y;

  if (typ(x) == t_COL && RgV_isscalar(x))
  {
    x = gel(x,1);
    return typ(v) == t_POL? RgX_Rg_mul(v,x): RgV_Rg_mul(v,x);
  }
  x = multable(M, x); /* multiplication table by x */
  y = cgetg_copy(v, &l);
  if (typ(v) == t_POL)
  {
    y[1] = v[1];
    for (i=2; i < l; i++) gel(y,i) = mulbytab(x, gel(v,i));
    y = normalizepol(y);
  }
  else
  {
    for (i=1; i < l; i++) gel(y,i) = mulbytab(x, gel(v,i));
  }
  return y;
}

GEN
zkmultable_capZ(GEN mx) { return Q_denom(zkmultable_inv(mx)); }

GEN
zkmultable_inv(GEN mx)
{ return ZM_gauss(mx, col_ei(lg(mx)-1,1)); }

/* nf a true nf, x a ZC */
GEN
zk_inv(GEN nf, GEN x) { return zkmultable_inv(zk_multable(nf,x)); }

/* inverse of x in nf */
GEN
nfinv(GEN nf, GEN x)
{
  pari_sp av = avma;
  GEN z;

  nf = checknf(nf);
  x = nf_to_scalar_or_basis(nf, x);
  if (typ(x) == t_COL)
  {
    GEN d;
    x = Q_remove_denom(x, &d);
    z = zk_inv(nf, x);
    if (d) z = RgC_Rg_mul(z, d);
  }
  else
    z = ginv(x);
  return gerepileupto(av, z);
}

/* quotient of x and y in nf */
GEN
nfdiv(GEN nf, GEN x, GEN y)
{
  pari_sp av = avma;
  GEN z;

  nf = checknf(nf);
  y = nf_to_scalar_or_basis(nf, y);
  if (typ(y) != t_COL)
  {
    x = nf_to_scalar_or_basis(nf, x);
    z = (typ(x) == t_COL)? RgC_Rg_div(x, y): gdiv(x,y);
  }
  else
  {
    GEN d;
    y = Q_remove_denom(y, &d);
    z = nfmul(nf, x, zk_inv(nf,y));
    if (d) z = RgC_Rg_mul(z, d);
  }
  return gerepileupto(av, z);
}

/* product of INTEGERS (t_INT or ZC) x and y in nf
 * compute xy as ( sum_i x_i sum_j y_j m^{i,j}_k )_k */
GEN
nfmuli(GEN nf, GEN x, GEN y)
{
  long i, j, k, N;
  GEN s, v, TAB = get_tab(nf, &N);

  if (typ(x) == t_INT) return (typ(y) == t_COL)? ZC_Z_mul(y, x): mulii(x,y);
  if (typ(y) == t_INT) return ZC_Z_mul(x, y);
  /* both x and y are ZV */
  v = cgetg(N+1,t_COL);
  for (k=1; k<=N; k++)
  {
    pari_sp av = avma;
    GEN TABi = TAB;
    if (k == 1)
      s = mulii(gel(x,1),gel(y,1));
    else
      s = addii(mulii(gel(x,1),gel(y,k)),
                mulii(gel(x,k),gel(y,1)));
    for (i=2; i<=N; i++)
    {
      GEN t, xi = gel(x,i);
      TABi += N;
      if (!signe(xi)) continue;

      t = NULL;
      for (j=2; j<=N; j++)
      {
        GEN p1, c = gcoeff(TABi, k, j); /* m^{i,j}_k */
        if (!signe(c)) continue;
        p1 = _mulii(c, gel(y,j));
        t = t? addii(t, p1): p1;
      }
      if (t) s = addii(s, mulii(xi, t));
    }
    gel(v,k) = gerepileuptoint(av,s);
  }
  return v;
}
/* square of INTEGER (t_INT or ZC) x in nf */
GEN
nfsqri(GEN nf, GEN x)
{
  long i, j, k, N;
  GEN s, v, TAB = get_tab(nf, &N);

  if (typ(x) == t_INT) return sqri(x);
  v = cgetg(N+1,t_COL);
  for (k=1; k<=N; k++)
  {
    pari_sp av = avma;
    GEN TABi = TAB;
    if (k == 1)
      s = sqri(gel(x,1));
    else
      s = shifti(mulii(gel(x,1),gel(x,k)), 1);
    for (i=2; i<=N; i++)
    {
      GEN p1, c, t, xi = gel(x,i);
      TABi += N;
      if (!signe(xi)) continue;

      c = gcoeff(TABi, k, i);
      t = signe(c)? _mulii(c,xi): NULL;
      for (j=i+1; j<=N; j++)
      {
        c = gcoeff(TABi, k, j);
        if (!signe(c)) continue;
        p1 = _mulii(c, shifti(gel(x,j),1));
        t = t? addii(t, p1): p1;
      }
      if (t) s = addii(s, mulii(xi, t));
    }
    gel(v,k) = gerepileuptoint(av,s);
  }
  return v;
}

/* both x and y are RgV */
GEN
tablemul(GEN TAB, GEN x, GEN y)
{
  long i, j, k, N;
  GEN s, v;
  if (typ(x) != t_COL) return gmul(x, y);
  if (typ(y) != t_COL) return gmul(y, x);
  N = lg(x)-1;
  v = cgetg(N+1,t_COL);
  for (k=1; k<=N; k++)
  {
    pari_sp av = avma;
    GEN TABi = TAB;
    if (k == 1)
      s = gmul(gel(x,1),gel(y,1));
    else
      s = gadd(gmul(gel(x,1),gel(y,k)),
               gmul(gel(x,k),gel(y,1)));
    for (i=2; i<=N; i++)
    {
      GEN t, xi = gel(x,i);
      TABi += N;
      if (gequal0(xi)) continue;

      t = NULL;
      for (j=2; j<=N; j++)
      {
        GEN p1, c = gcoeff(TABi, k, j); /* m^{i,j}_k */
        if (gequal0(c)) continue;
        p1 = gmul(c, gel(y,j));
        t = t? gadd(t, p1): p1;
      }
      if (t) s = gadd(s, gmul(xi, t));
    }
    gel(v,k) = gerepileupto(av,s);
  }
  return v;
}
GEN
tablesqr(GEN TAB, GEN x)
{
  long i, j, k, N;
  GEN s, v;

  if (typ(x) != t_COL) return gsqr(x);
  N = lg(x)-1;
  v = cgetg(N+1,t_COL);

  for (k=1; k<=N; k++)
  {
    pari_sp av = avma;
    GEN TABi = TAB;
    if (k == 1)
      s = gsqr(gel(x,1));
    else
      s = gmul2n(gmul(gel(x,1),gel(x,k)), 1);
    for (i=2; i<=N; i++)
    {
      GEN p1, c, t, xi = gel(x,i);
      TABi += N;
      if (gequal0(xi)) continue;

      c = gcoeff(TABi, k, i);
      t = !gequal0(c)? gmul(c,xi): NULL;
      for (j=i+1; j<=N; j++)
      {
        c = gcoeff(TABi, k, j);
        if (gequal0(c)) continue;
        p1 = gmul(gmul2n(c,1), gel(x,j));
        t = t? gadd(t, p1): p1;
      }
      if (t) s = gadd(s, gmul(xi, t));
    }
    gel(v,k) = gerepileupto(av,s);
  }
  return v;
}

static GEN
_mul(void *data, GEN x, GEN y) { return nfmuli((GEN)data,x,y); }
static GEN
_sqr(void *data, GEN x) { return nfsqri((GEN)data,x); }

/* Compute z^n in nf, left-shift binary powering */
GEN
nfpow(GEN nf, GEN z, GEN n)
{
  pari_sp av = avma;
  long s;
  GEN x, cx;

  if (typ(n)!=t_INT) pari_err_TYPE("nfpow",n);
  nf = checknf(nf);
  s = signe(n); if (!s) return gen_1;
  x = nf_to_scalar_or_basis(nf, z);
  if (typ(x) != t_COL) return powgi(x,n);
  if (s < 0)
  { /* simplified nfinv */
    GEN d;
    x = Q_remove_denom(x, &d);
    x = zk_inv(nf, x);
    x = primitive_part(x, &cx);
    cx = mul_content(cx, d);
    n = negi(n);
  }
  else
    x = primitive_part(x, &cx);
  x = gen_pow(x, n, (void*)nf, _sqr, _mul);
  if (cx) x = gmul(x, powgi(cx, n));
  return av==avma? gcopy(x): gerepileupto(av,x);
}
/* Compute z^n in nf, left-shift binary powering */
GEN
nfpow_u(GEN nf, GEN z, ulong n)
{
  pari_sp av = avma;
  GEN x, cx;

  nf = checknf(nf);
  if (!n) return gen_1;
  x = nf_to_scalar_or_basis(nf, z);
  if (typ(x) != t_COL) return gpowgs(x,n);
  x = primitive_part(x, &cx);
  x = gen_powu(x, n, (void*)nf, _sqr, _mul);
  if (cx) x = gmul(x, powgi(cx, utoipos(n)));
  return av==avma? gcopy(x): gerepileupto(av,x);
}

static GEN
_nf_red(void *E, GEN x) { (void)E; return x; }

static GEN
_nf_add(void *E, GEN x, GEN y) { return nfadd((GEN)E,x,y); }

static GEN
_nf_neg(void *E, GEN x) { (void)E; return gneg(x); }

static GEN
_nf_mul(void *E, GEN x, GEN y) { return nfmul((GEN)E,x,y); }

static GEN
_nf_inv(void *E, GEN x) { return nfinv((GEN)E,x); }

static GEN
_nf_s(void *E, long x) { (void)E; return stoi(x); }

static const struct bb_field nf_field={_nf_red,_nf_add,_nf_mul,_nf_neg,
                                        _nf_inv,&gequal0,_nf_s };

const struct bb_field *get_nf_field(void **E, GEN nf)
{ *E = (void*)nf; return &nf_field; }

GEN
nfM_det(GEN nf, GEN M)
{
  void *E;
  const struct bb_field *S = get_nf_field(&E, nf);
  return gen_det(M, E, S);
}
GEN
nfM_inv(GEN nf, GEN M)
{
  void *E;
  const struct bb_field *S = get_nf_field(&E, nf);
  return gen_Gauss(M, matid(lg(M)-1), E, S);
}
GEN
nfM_mul(GEN nf, GEN A, GEN B)
{
  void *E;
  const struct bb_field *S = get_nf_field(&E, nf);
  return gen_matmul(A, B, E, S);
}
GEN
nfM_nfC_mul(GEN nf, GEN A, GEN B)
{
  void *E;
  const struct bb_field *S = get_nf_field(&E, nf);
  return gen_matcolmul(A, B, E, S);
}

/* valuation of integral x (ZV), with resp. to prime ideal pr */
long
ZC_nfvalrem(GEN x, GEN pr, GEN *newx)
{
  long i, v, l;
  GEN r, y, p = pr_get_p(pr), mul = pr_get_tau(pr);

  /* p inert */
  if (typ(mul) == t_INT) return newx? ZV_pvalrem(x, p, newx):ZV_pval(x, p);
  y = cgetg_copy(x, &l); /* will hold the new x */
  x = leafcopy(x);
  for(v=0;; v++)
  {
    for (i=1; i<l; i++)
    { /* is (x.b)[i] divisible by p ? */
      gel(y,i) = dvmdii(ZMrow_ZC_mul(mul,x,i),p,&r);
      if (r != gen_0) { if (newx) *newx = x; return v; }
    }
    swap(x, y);
  }
}
long
ZC_nfval(GEN x, GEN P)
{ return ZC_nfvalrem(x, P, NULL); }

/* v_P(x) != 0, x a ZV. Simpler version of ZC_nfvalrem */
int
ZC_prdvd(GEN x, GEN P)
{
  pari_sp av = avma;
  long i, l;
  GEN p = pr_get_p(P), mul = pr_get_tau(P);
  if (typ(mul) == t_INT) return ZV_Z_dvd(x, p);
  l = lg(x);
  for (i=1; i<l; i++)
    if (!dvdii(ZMrow_ZC_mul(mul,x,i), p)) { avma = av; return 0; }
  avma = av; return 1;
}

int
pr_equal(GEN P, GEN Q)
{
  GEN gQ, p = pr_get_p(P);
  long e = pr_get_e(P), f = pr_get_f(P), n;
  if (!equalii(p, pr_get_p(Q)) || e != pr_get_e(Q) || f != pr_get_f(Q))
    return 0;
  gQ = pr_get_gen(Q); n = lg(gQ)-1;
  if (2*e*f > n) return 1; /* room for only one such pr */
  return ZV_equal(pr_get_gen(P), gQ) || ZC_prdvd(gQ, P);
}

long
nfval(GEN nf, GEN x, GEN pr)
{
  pari_sp av = avma;
  long w, e;
  GEN cx, p;

  if (gequal0(x)) return LONG_MAX;
  nf = checknf(nf);
  checkprid(pr);
  p = pr_get_p(pr);
  e = pr_get_e(pr);
  x = nf_to_scalar_or_basis(nf, x);
  if (typ(x) != t_COL) return e*Q_pval(x,p);
  x = Q_primitive_part(x, &cx);
  w = ZC_nfval(x,pr);
  if (cx) w += e*Q_pval(cx,p);
  avma = av; return w;
}

/* want to write p^v = uniformizer^(e*v) * z^v, z coprime to pr */
/* z := tau^e / p^(e-1), algebraic integer coprime to pr; return z^v */
static GEN
powp(GEN nf, GEN pr, long v)
{
  GEN b, z;
  long e;
  if (!v) return gen_1;
  b = pr_get_tau(pr);
  if (typ(b) == t_INT) return gen_1;
  e = pr_get_e(pr);
  z = gel(b,1);
  if (e != 1) z = gdiv(nfpow_u(nf, z, e), powiu(pr_get_p(pr),e-1));
  if (v < 0) { v = -v; z = nfinv(nf, z); }
  if (v != 1) z = nfpow_u(nf, z, v);
  return z;
}
long
nfvalrem(GEN nf, GEN x, GEN pr, GEN *py)
{
  pari_sp av = avma;
  long w, e;
  GEN cx, p, t;

  if (!py) return nfval(nf,x,pr);
  if (gequal0(x)) { *py = gcopy(x); return LONG_MAX; }
  nf = checknf(nf);
  checkprid(pr);
  p = pr_get_p(pr);
  e = pr_get_e(pr);
  x = nf_to_scalar_or_basis(nf, x);
  if (typ(x) != t_COL) {
    w = Q_pvalrem(x,p, py);
    if (!w) { *py = gerepilecopy(av, x); return 0; }
    *py = gerepileupto(av, gmul(powp(nf, pr, w), *py));
    return e*w;
  }
  x = Q_primitive_part(x, &cx);
  w = ZC_nfvalrem(x,pr, py);
  if (cx)
  {
    long v = Q_pvalrem(cx,p, &t);
    *py = nfmul(nf, *py, gmul(powp(nf,pr,v), t));
    *py = gerepileupto(av, *py);
    w += e*v;
  }
  else
    *py = gerepilecopy(av, *py);
  return w;
}
GEN
gpnfvalrem(GEN nf, GEN x, GEN pr, GEN *py)
{
  long v = nfvalrem(nf,x,pr,py);
  return v == LONG_MAX? mkoo(): stoi(v);
}

/* true nf */
GEN
coltoalg(GEN nf, GEN x)
{
  return mkpolmod( nf_to_scalar_or_alg(nf, x), nf_get_pol(nf) );
}

GEN
basistoalg(GEN nf, GEN x)
{
  GEN T;

  nf = checknf(nf);
  switch(typ(x))
  {
    case t_COL: {
      pari_sp av = avma;
      return gerepilecopy(av, coltoalg(nf, x));
    }
    case t_POLMOD:
      T = nf_get_pol(nf);
      if (!RgX_equal_var(T,gel(x,1)))
        pari_err_MODULUS("basistoalg", T,gel(x,1));
      return gcopy(x);
    case t_POL:
      T = nf_get_pol(nf);
      if (varn(T) != varn(x)) pari_err_VAR("basistoalg",x,T);
      retmkpolmod(RgX_rem(x, T), ZX_copy(T));
    case t_INT:
    case t_FRAC:
      T = nf_get_pol(nf);
      retmkpolmod(gcopy(x), ZX_copy(T));
    default:
      pari_err_TYPE("basistoalg",x);
      return NULL; /* LCOV_EXCL_LINE */
  }
}

/* true nf, x a t_POL */
static GEN
pol_to_scalar_or_basis(GEN nf, GEN x)
{
  GEN T = nf_get_pol(nf);
  long l = lg(x);
  if (varn(x) != varn(T)) pari_err_VAR("nf_to_scalar_or_basis", x,T);
  if (l >= lg(T)) { x = RgX_rem(x, T); l = lg(x); }
  if (l == 2) return gen_0;
  if (l == 3)
  {
    x = gel(x,2);
    if (!is_rational_t(typ(x))) pari_err_TYPE("nf_to_scalar_or_basis",x);
    return x;
  }
  return poltobasis(nf,x);
}
/* Assume nf is a genuine nf. */
GEN
nf_to_scalar_or_basis(GEN nf, GEN x)
{
  switch(typ(x))
  {
    case t_INT: case t_FRAC:
      return x;
    case t_POLMOD:
      x = checknfelt_mod(nf,x,"nf_to_scalar_or_basis");
      switch(typ(x))
      {
        case t_INT: case t_FRAC: return x;
        case t_POL: return pol_to_scalar_or_basis(nf,x);
      }
      break;
    case t_POL: return pol_to_scalar_or_basis(nf,x);
    case t_COL:
      if (lg(x)-1 != nf_get_degree(nf)) break;
      return QV_isscalar(x)? gel(x,1): x;
  }
  pari_err_TYPE("nf_to_scalar_or_basis",x);
  return NULL; /* LCOV_EXCL_LINE */
}
/* Let x be a polynomial with coefficients in Q or nf. Return the same
 * polynomial with coefficients expressed as vectors (on the integral basis).
 * No consistency checks, not memory-clean. */
GEN
RgX_to_nfX(GEN nf, GEN x)
{
  long i, l;
  GEN y = cgetg_copy(x, &l); y[1] = x[1];
  for (i=2; i<l; i++) gel(y,i) = nf_to_scalar_or_basis(nf, gel(x,i));
  return y;
}

/* Assume nf is a genuine nf. */
GEN
nf_to_scalar_or_alg(GEN nf, GEN x)
{
  switch(typ(x))
  {
    case t_INT: case t_FRAC:
      return x;
    case t_POLMOD:
      x = checknfelt_mod(nf,x,"nf_to_scalar_or_alg");
      if (typ(x) != t_POL) return x;
      /* fall through */
    case t_POL:
    {
      GEN T = nf_get_pol(nf);
      long l = lg(x);
      if (varn(x) != varn(T)) pari_err_VAR("nf_to_scalar_or_alg", x,T);
      if (l >= lg(T)) { x = RgX_rem(x, T); l = lg(x); }
      if (l == 2) return gen_0;
      if (l == 3) return gel(x,2);
      return x;
    }
    case t_COL:
    {
      GEN dx;
      if (lg(x)-1 != nf_get_degree(nf)) break;
      if (QV_isscalar(x)) return gel(x,1);
      x = Q_remove_denom(x, &dx);
      x = RgV_RgC_mul(nf_get_zkprimpart(nf), x);
      dx = mul_denom(dx, nf_get_zkden(nf));
      return gdiv(x,dx);
    }
  }
  pari_err_TYPE("nf_to_scalar_or_alg",x);
  return NULL; /* LCOV_EXCL_LINE */
}

/* gmul(A, RgX_to_RgC(x)), A t_MAT of compatible dimensions */
GEN
RgM_RgX_mul(GEN A, GEN x)
{
  long i, l = lg(x)-1;
  GEN z;
  if (l == 1) return zerocol(nbrows(A));
  z = gmul(gel(x,2), gel(A,1));
  for (i = 2; i < l; i++)
    if (!gequal0(gel(x,i+1))) z = gadd(z, gmul(gel(x,i+1), gel(A,i)));
  return z;
}
GEN
ZM_ZX_mul(GEN A, GEN x)
{
  long i, l = lg(x)-1;
  GEN z;
  if (l == 1) return zerocol(nbrows(A));
  z = ZC_Z_mul(gel(A,1), gel(x,2));
  for (i = 2; i < l ; i++)
    if (signe(gel(x,i+1))) z = ZC_add(z, ZC_Z_mul(gel(A,i), gel(x,i+1)));
  return z;
}
/* x a t_POL, nf a genuine nf. No garbage collecting. No check.  */
GEN
poltobasis(GEN nf, GEN x)
{
  GEN d, T = nf_get_pol(nf);
  if (varn(x) != varn(T)) pari_err_VAR( "poltobasis", x,T);
  if (degpol(x) >= degpol(T)) x = RgX_rem(x,T);
  x = Q_remove_denom(x, &d);
  if (!RgX_is_ZX(x)) pari_err_TYPE("poltobasis",x);
  x = ZM_ZX_mul(nf_get_invzk(nf), x);
  if (d) x = RgC_Rg_div(x, d);
  return x;
}

GEN
algtobasis(GEN nf, GEN x)
{
  pari_sp av;

  nf = checknf(nf);
  switch(typ(x))
  {
    case t_POLMOD:
      if (!RgX_equal_var(nf_get_pol(nf),gel(x,1)))
        pari_err_MODULUS("algtobasis", nf_get_pol(nf),gel(x,1));
      x = gel(x,2);
      switch(typ(x))
      {
        case t_INT:
        case t_FRAC: return scalarcol(x, nf_get_degree(nf));
        case t_POL:
          av = avma;
          return gerepileupto(av,poltobasis(nf,x));
      }
      break;

    case t_POL:
      av = avma;
      return gerepileupto(av,poltobasis(nf,x));

    case t_COL:
      if (!RgV_is_QV(x)) pari_err_TYPE("nfalgtobasis",x);
      if (lg(x)-1 != nf_get_degree(nf)) pari_err_DIM("nfalgtobasis");
      return gcopy(x);

    case t_INT:
    case t_FRAC: return scalarcol(x, nf_get_degree(nf));
  }
  pari_err_TYPE("algtobasis",x);
  return NULL; /* LCOV_EXCL_LINE */
}

GEN
rnfbasistoalg(GEN rnf,GEN x)
{
  const char *f = "rnfbasistoalg";
  long lx, i;
  pari_sp av = avma;
  GEN z, nf, relpol, T;

  checkrnf(rnf);
  nf = rnf_get_nf(rnf);
  T = nf_get_pol(nf);
  relpol = QXQX_to_mod_shallow(rnf_get_pol(rnf), T);
  switch(typ(x))
  {
    case t_COL:
      z = cgetg_copy(x, &lx);
      for (i=1; i<lx; i++)
      {
        GEN c = nf_to_scalar_or_alg(nf, gel(x,i));
        if (typ(c) == t_POL) c = mkpolmod(c,T);
        gel(z,i) = c;
      }
      z = RgV_RgC_mul(gel(rnf_get_zk(rnf),1), z);
      return gerepileupto(av, gmodulo(z,relpol));

    case t_POLMOD:
      x = polmod_nffix(f, rnf, x, 0);
      if (typ(x) != t_POL) break;
      retmkpolmod(RgX_copy(x), RgX_copy(relpol));
    case t_POL:
      if (varn(x) == varn(T)) { RgX_check_QX(x,f); x = gmodulo(x,T); break; }
      if (varn(x) == varn(relpol))
      {
        x = RgX_nffix(f,nf_get_pol(nf),x,0);
        return gmodulo(x, relpol);
      }
      pari_err_VAR(f, x,relpol);
  }
  retmkpolmod(scalarpol(x, varn(relpol)), RgX_copy(relpol));
}

GEN
matbasistoalg(GEN nf,GEN x)
{
  long i, j, li, lx;
  GEN z = cgetg_copy(x, &lx);

  if (lx == 1) return z;
  switch(typ(x))
  {
    case t_VEC: case t_COL:
      for (i=1; i<lx; i++) gel(z,i) = basistoalg(nf, gel(x,i));
      return z;
    case t_MAT: break;
    default: pari_err_TYPE("matbasistoalg",x);
  }
  li = lgcols(x);
  for (j=1; j<lx; j++)
  {
    GEN c = cgetg(li,t_COL), xj = gel(x,j);
    gel(z,j) = c;
    for (i=1; i<li; i++) gel(c,i) = basistoalg(nf, gel(xj,i));
  }
  return z;
}

GEN
matalgtobasis(GEN nf,GEN x)
{
  long i, j, li, lx;
  GEN z = cgetg_copy(x, &lx);

  if (lx == 1) return z;
  switch(typ(x))
  {
    case t_VEC: case t_COL:
      for (i=1; i<lx; i++) gel(z,i) = algtobasis(nf, gel(x,i));
      return z;
    case t_MAT: break;
    default: pari_err_TYPE("matalgtobasis",x);
  }
  li = lgcols(x);
  for (j=1; j<lx; j++)
  {
    GEN c = cgetg(li,t_COL), xj = gel(x,j);
    gel(z,j) = c;
    for (i=1; i<li; i++) gel(c,i) = algtobasis(nf, gel(xj,i));
  }
  return z;
}
GEN
RgM_to_nfM(GEN nf,GEN x)
{
  long i, j, li, lx;
  GEN z = cgetg_copy(x, &lx);

  if (lx == 1) return z;
  li = lgcols(x);
  for (j=1; j<lx; j++)
  {
    GEN c = cgetg(li,t_COL), xj = gel(x,j);
    gel(z,j) = c;
    for (i=1; i<li; i++) gel(c,i) = nf_to_scalar_or_basis(nf, gel(xj,i));
  }
  return z;
}
GEN
RgC_to_nfC(GEN nf, GEN x)
{ pari_APPLY_type(t_COL, nf_to_scalar_or_basis(nf, gel(x,i))) }

/* x a t_POLMOD, supposedly in rnf = K[z]/(T), K = Q[y]/(Tnf) */
GEN
polmod_nffix(const char *f, GEN rnf, GEN x, int lift)
{ return polmod_nffix2(f, rnf_get_nfpol(rnf), rnf_get_pol(rnf), x,lift); }
GEN
polmod_nffix2(const char *f, GEN T, GEN relpol, GEN x, int lift)
{
  if (RgX_equal_var(gel(x,1),relpol))
  {
    x = gel(x,2);
    if (typ(x) == t_POL && varn(x) == varn(relpol))
    {
      x = RgX_nffix(f, T, x, lift);
      switch(lg(x))
      {
        case 2: return gen_0;
        case 3: return gel(x,2);
      }
      return x;
    }
  }
  return Rg_nffix(f, T, x, lift);
}
GEN
rnfalgtobasis(GEN rnf,GEN x)
{
  const char *f = "rnfalgtobasis";
  pari_sp av = avma;
  GEN T, relpol;

  checkrnf(rnf);
  relpol = rnf_get_pol(rnf);
  T = rnf_get_nfpol(rnf);
  switch(typ(x))
  {
    case t_COL:
      if (lg(x)-1 != rnf_get_degree(rnf)) pari_err_DIM(f);
      x = RgV_nffix(f, T, x, 0);
      return gerepilecopy(av, x);

    case t_POLMOD:
      x = polmod_nffix(f, rnf, x, 0);
      if (typ(x) != t_POL) break;
      return gerepileupto(av, RgM_RgX_mul(rnf_get_invzk(rnf), x));
    case t_POL:
      if (varn(x) == varn(T))
      {
        RgX_check_QX(x,f);
        if (degpol(x) >= degpol(T)) x = RgX_rem(x,T);
        x = mkpolmod(x,T); break;
      }
      x = RgX_nffix(f, T, x, 0);
      if (degpol(x) >= degpol(relpol)) x = RgX_rem(x,relpol);
      return gerepileupto(av, RgM_RgX_mul(rnf_get_invzk(rnf), x));
  }
  return gerepileupto(av, scalarcol(x, rnf_get_degree(rnf)));
}

/* Given a and b in nf, gives an algebraic integer y in nf such that a-b.y
 * is "small" */
GEN
nfdiveuc(GEN nf, GEN a, GEN b)
{
  pari_sp av = avma;
  a = nfdiv(nf,a,b);
  return gerepileupto(av, ground(a));
}

/* Given a and b in nf, gives a "small" algebraic integer r in nf
 * of the form a-b.y */
GEN
nfmod(GEN nf, GEN a, GEN b)
{
  pari_sp av = avma;
  GEN p1 = gneg_i(nfmul(nf,b,ground(nfdiv(nf,a,b))));
  return gerepileupto(av, nfadd(nf,a,p1));
}

/* Given a and b in nf, gives a two-component vector [y,r] in nf such
 * that r=a-b.y is "small". */
GEN
nfdivrem(GEN nf, GEN a, GEN b)
{
  pari_sp av = avma;
  GEN p1,z, y = ground(nfdiv(nf,a,b));

  p1 = gneg_i(nfmul(nf,b,y));
  z = cgetg(3,t_VEC);
  gel(z,1) = gcopy(y);
  gel(z,2) = nfadd(nf,a,p1); return gerepileupto(av, z);
}

/*************************************************************************/
/**                                                                     **/
/**                        REAL EMBEDDINGS                              **/
/**                                                                     **/
/*************************************************************************/
static GEN
sarch_get_cyc(GEN sarch) { return gel(sarch,1); }
static GEN
sarch_get_archp(GEN sarch) { return gel(sarch,2); }
static GEN
sarch_get_MI(GEN sarch) { return gel(sarch,3); }
static GEN
sarch_get_lambda(GEN sarch) { return gel(sarch,4); }
static GEN
sarch_get_F(GEN sarch) { return gel(sarch,5); }

/* true nf, return number of positive roots of char_x */
static long
num_positive(GEN nf, GEN x)
{
  GEN T = nf_get_pol(nf);
  GEN charx = ZXQ_charpoly(nf_to_scalar_or_alg(nf,x), T, 0);
  long np;
  charx = ZX_radical(charx);
  np = ZX_sturmpart(charx, mkvec2(gen_0,mkoo()));
  return np * (degpol(T) / degpol(charx));
}

/* x a QC: return sigma_k(x) where 1 <= k <= r1+r2; correct but inefficient
 * if x in Q. M = nf_get_M(nf) */
static GEN
nfembed_i(GEN M, GEN x, long k)
{
  long i, l = lg(M);
  GEN z = gel(x,1);
  for (i = 2; i < l; i++) z = gadd(z, gmul(gcoeff(M,k,i), gel(x,i)));
  return z;
}
GEN
nfembed(GEN nf, GEN x, long k)
{
  pari_sp av = avma;
  nf = checknf(nf);
  x = nf_to_scalar_or_basis(nf,x);
  if (typ(x) != t_COL) return gerepilecopy(av, x);
  return gerepileupto(av, nfembed_i(nf_get_M(nf),x,k));
}

/* x a ZC */
static GEN
zk_embed(GEN M, GEN x, long k)
{
  long i, l = lg(x);
  GEN z = gel(x,1); /* times M[k,1], which is 1 */
  for (i = 2; i < l; i++) z = mpadd(z, mpmul(gcoeff(M,k,i), gel(x,i)));
  return z;
}

/* Given floating point approximation z of sigma_k(x), decide its sign
 * [0/+, 1/- and -1 for FAIL] */
static long
eval_sign_embed(GEN z)
{ /* dubious, fail */
  if (typ(z) == t_REAL && realprec(z) <= LOWDEFAULTPREC) return -1;
  return (signe(z) < 1)? 1: 0;
}
/* return v such that (-1)^v = sign(sigma_k(x)), x primitive ZC */
static long
eval_sign(GEN M, GEN x, long k)
{ return eval_sign_embed( zk_embed(M, x, k) ); }

/* check that signs[i..#signs] == s; signs = NULL encodes "totally positive" */
static int
oksigns(long l, GEN signs, long i, long s)
{
  if (!signs) return s == 0;
  for (; i < l; i++)
    if (signs[i] != s) return 0;
  return 1;
}
/* check that signs[i] = s and signs[i+1..#signs] = 1-s */
static int
oksigns2(long l, GEN signs, long i, long s)
{
  if (!signs) return s == 0 && i == l-1;
  return signs[i] == s && oksigns(l, signs, i+1, 1-s);
}

/* true nf, x a ZC (primitive for efficiency), embx its embeddings or NULL */
static int
nfchecksigns_i(GEN nf, GEN x, GEN embx, GEN signs, GEN archp)
{
  long l = lg(archp), i;
  GEN M = nf_get_M(nf), sarch = NULL;
  long np = -1;
  for (i = 1; i < l; i++)
  {
    long s;
    if (embx)
      s = eval_sign_embed(gel(embx,i));
    else
      s = eval_sign(M, x, archp[i]);
    /* 0 / + or 1 / -; -1 for FAIL */
    if (s < 0) /* failure */
    {
      long ni, r1 = nf_get_r1(nf);
      GEN xi;
      if (np < 0)
      {
        np = num_positive(nf, x);
        if (np == 0)  return oksigns(l, signs, i, 1);
        if (np == r1) return oksigns(l, signs, i, 0);
        sarch = nfarchstar(nf, NULL, identity_perm(r1));
      }
      xi = set_sign_mod_divisor(nf, vecsmall_ei(r1, archp[i]), gen_1, sarch);
      xi = Q_primpart(xi);
      ni = num_positive(nf, nfmuli(nf,x,xi));
      if (ni == 0)  return oksigns2(l, signs, i, 0);
      if (ni == r1) return oksigns2(l, signs, i, 1);
      s = ni < np? 0: 1;
    }
    if (s != (signs? signs[i]: 0)) return 0;
  }
  return 1;
}
static void
pl_convert(GEN pl, GEN *psigns, GEN *parchp)
{
  long i, j, l = lg(pl);
  GEN signs = cgetg(l, t_VECSMALL);
  GEN archp = cgetg(l, t_VECSMALL);
  for (i = j = 1; i < l; i++)
  {
    if (!pl[i]) continue;
    archp[j] = i;
    signs[j] = (pl[i] < 0)? 1: 0;
    j++;
  }
  setlg(archp, j); *parchp = archp;
  setlg(signs, j); *psigns = signs;
}
/* pl : requested signs for real embeddings, 0 = no sign constraint */
int
nfchecksigns(GEN nf, GEN x, GEN pl)
{
  pari_sp av = avma;
  GEN signs, archp;
  int res;
  nf = checknf(nf);
  x = nf_to_scalar_or_basis(nf,x);
  if (typ(x) != t_COL)
  {
    long i, l = lg(pl), s = gsigne(x);
    for (i = 1; i < l; i++)
      if (pl[i] && pl[i] != s) { avma = av; return 0; }
    avma = av; return 1;
  }
  pl_convert(pl, &signs, &archp);
  res = nfchecksigns_i(nf, x, NULL, signs, archp);
  avma = av; return res;
}

/* signs = NULL: totally positive, else sign[i] = 0 (+) or 1 (-) */
static GEN
get_C(GEN lambda, long l, GEN signs)
{
  long i;
  GEN C, mlambda;
  if (!signs) return const_vec(l-1, lambda);
  C = cgetg(l, t_COL); mlambda = gneg(lambda);
  for (i = 1; i < l; i++) gel(C,i) = signs[i]? mlambda: lambda;
  return C;
}
/* signs = NULL: totally positive at archp */
static GEN
nfsetsigns(GEN nf, GEN signs, GEN x, GEN sarch)
{
  long i, l = lg(sarch_get_archp(sarch));
  GEN ex;
  /* Is signature already correct ? */
  if (typ(x) != t_COL)
  {
    long s = gsigne(x);
    if (!s) i = 1;
    else if (!signs)
      i = (s < 0)? 1: l;
    else
    {
      s = s < 0? 1: 0;
      for (i = 1; i < l; i++)
        if (signs[i] != s) break;
    }
    ex = (i < l)? const_col(l-1, x): NULL;
  }
  else
  {
    pari_sp av = avma;
    GEN cex, M = nf_get_M(nf), archp = sarch_get_archp(sarch);
    GEN xp = Q_primitive_part(x,&cex);
    ex = cgetg(l,t_COL);
    for (i = 1; i < l; i++) gel(ex,i) = zk_embed(M,xp,archp[i]);
    if (nfchecksigns_i(nf, xp, ex, signs, archp)) { ex = NULL; avma = av; }
    else if (cex) ex = RgC_Rg_mul(ex, cex); /* put back content */
  }
  if (ex)
  { /* If no, fix it */
    GEN MI = sarch_get_MI(sarch), F = sarch_get_F(sarch);
    GEN lambda = sarch_get_lambda(sarch);
    GEN t = RgC_sub(get_C(lambda, l, signs), ex);
    long e;
    t = grndtoi(RgM_RgC_mul(MI,t), &e);
    if (lg(F) != 1) t = ZM_ZC_mul(F, t);
    x = typ(x) == t_COL? RgC_add(t, x): RgC_Rg_add(t, x);
  }
  return x;
}
/* - sarch = nfarchstar(nf, F);
 * - x encodes a vector of signs at arch.archp: either a t_VECSMALL
 *   (vector of signs as {0,1}-vector), NULL (totally positive at archp),
 *   or a non-zero number field element (replaced by its signature at archp);
 * - y is a non-zero number field element
 * Return z = y (mod F) with signs(y, archp) = signs(x) (a {0,1}-vector) */
GEN
set_sign_mod_divisor(GEN nf, GEN x, GEN y, GEN sarch)
{
  GEN archp = sarch_get_archp(sarch);
  if (lg(archp) == 1) return y;
  nf = checknf(nf);
  if (x && typ(x) != t_VECSMALL) x = nfsign_arch(nf, x, archp);
  y = nf_to_scalar_or_basis(nf,y);
  return nfsetsigns(nf, x, y, sarch);
}

static GEN
setsigns_init(GEN nf, GEN archp, GEN F, GEN DATA)
{
  GEN lambda, Mr = rowpermute(nf_get_M(nf), archp), MI = F? RgM_mul(Mr,F): Mr;
  lambda = gmul2n(matrixnorm(MI,DEFAULTPREC), -1);
  if (typ(lambda) != t_REAL) lambda = gmul(lambda, sstoQ(1001,1000));
  if (lg(archp) < lg(MI))
  {
    GEN perm = gel(indexrank(MI), 2);
    if (!F) F = matid(nf_get_degree(nf));
    MI = vecpermute(MI, perm);
    F = vecpermute(F, perm);
  }
  if (!F) F = cgetg(1,t_MAT);
  MI = RgM_inv(MI);
  return mkvec5(DATA, archp, MI, lambda, F);
}
/* F non-0 integral ideal in HNF (or NULL: Z_K), compute elements in 1+F
 * whose sign matrix at archp is identity; archp in 'indices' format */
GEN
nfarchstar(GEN nf, GEN F, GEN archp)
{
  long nba = lg(archp) - 1;
  if (!nba) return mkvec2(cgetg(1,t_VEC), archp);
  if (F && equali1(gcoeff(F,1,1))) F = NULL;
  if (F) F = idealpseudored(F, nf_get_roundG(nf));
  return setsigns_init(nf, archp, F, const_vec(nba, gen_2));
}

/*************************************************************************/
/**                                                                     **/
/**                         IDEALCHINESE                                **/
/**                                                                     **/
/*************************************************************************/
static int
isprfact(GEN x)
{
  long i, l;
  GEN L, E;
  if (typ(x) != t_MAT || lg(x) != 3) return 0;
  L = gel(x,1); l = lg(L);
  E = gel(x,2);
  for(i=1; i<l; i++)
  {
    checkprid(gel(L,i));
    if (typ(gel(E,i)) != t_INT) return 0;
  }
  return 1;
}

/* initialize projectors mod pr[i]^e[i] for idealchinese */
static GEN
pr_init(GEN nf, GEN fa, GEN w, GEN dw)
{
  GEN U, E, F, L = gel(fa,1), E0 = gel(fa,2);
  long i, r = lg(L);

  if (w && lg(w) != r) pari_err_TYPE("idealchinese", w);
  if (r == 1 && !dw) return cgetg(1,t_VEC);
  E = leafcopy(E0); /* do not destroy fa[2] */
  for (i = 1; i < r; i++)
    if (signe(gel(E,i)) < 0) gel(E,i) = gen_0;
  F = factorbackprime(nf, L, E);
  if (dw)
  {
    F = ZM_Z_mul(F, dw);
    for (i = 1; i < r; i++)
    {
      GEN pr = gel(L,i);
      long e = itos(gel(E0,i)), v = idealval(nf, dw, pr);
      if (e >= 0)
        gel(E,i) = addiu(gel(E,i), v);
      else if (v + e <= 0)
        F = idealmulpowprime(nf, F, pr, stoi(-v)); /* coprime to pr */
      else
      {
        F = idealmulpowprime(nf, F, pr, stoi(e));
        gel(E,i) = stoi(v + e);
      }
    }
  }
  U = cgetg(r, t_VEC);
  for (i = 1; i < r; i++)
  {
    GEN u;
    if (w && gequal0(gel(w,i))) u = gen_0; /* unused */
    else
    {
      GEN pr = gel(L,i), e = gel(E,i), t;
      t = idealdivpowprime(nf,F, pr, e);
      u = hnfmerge_get_1(t, idealpow(nf, pr, e));
      if (!u) pari_err_COPRIME("idealchinese", t,pr);
    }
    gel(U,i) = u;
  }
  F = idealpseudored(F, nf_get_roundG(nf));
  return mkvec2(F, U);
}

static GEN
pl_normalize(GEN nf, GEN pl)
{
  const char *fun = "idealchinese";
  if (lg(pl)-1 != nf_get_r1(nf)) pari_err_TYPE(fun,pl);
  switch(typ(pl))
  {
    case t_VEC: RgV_check_ZV(pl,fun); pl = ZV_to_zv(pl);
      /* fall through */
    case t_VECSMALL: break;
    default: pari_err_TYPE(fun,pl);
  }
  return pl;
}

static int
is_chineseinit(GEN x)
{
  GEN fa, pl;
  long l;
  if (typ(x) != t_VEC || lg(x)!=3) return 0;
  fa = gel(x,1);
  pl = gel(x,2);
  if (typ(fa) != t_VEC || typ(pl) != t_VEC) return 0;
  l = lg(fa);
  if (l != 1)
  {
    if (l != 3 || typ(gel(fa,1)) != t_MAT || typ(gel(fa,2)) != t_VEC)
      return 0;
  }
  l = lg(pl);
  if (l != 1)
  {
    if (l != 6 || typ(gel(pl,3)) != t_MAT || typ(gel(pl,1)) != t_VECSMALL
                                          || typ(gel(pl,2)) != t_VECSMALL)
      return 0;
  }
  return 1;
}

/* nf a true 'nf' */
static GEN
chineseinit_i(GEN nf, GEN fa, GEN w, GEN dw)
{
  const char *fun = "idealchineseinit";
  GEN archp = NULL, pl = NULL;
  switch(typ(fa))
  {
    case t_VEC:
      if (is_chineseinit(fa))
      {
        if (dw) pari_err_DOMAIN(fun, "denom(y)", "!=", gen_1, w);
        return fa;
      }
      if (lg(fa) != 3) pari_err_TYPE(fun, fa);
      /* of the form [x,s] */
      pl = pl_normalize(nf, gel(fa,2));
      fa = gel(fa,1);
      archp = vecsmall01_to_indices(pl);
      /* keep pr_init, reset pl */
      if (is_chineseinit(fa)) { fa = gel(fa,1); break; }
      /* fall through */
    case t_MAT: /* factorization? */
      if (isprfact(fa)) { fa = pr_init(nf, fa, w, dw); break; }
    default: pari_err_TYPE(fun,fa);
  }

  if (!pl) pl = cgetg(1,t_VEC);
  else
  {
    long r = lg(archp);
    if (r == 1) pl = cgetg(1, t_VEC);
    else
    {
      GEN F = (lg(fa) == 1)? NULL: gel(fa,1), signs = cgetg(r, t_VECSMALL);
      long i;
      for (i = 1; i < r; i++) signs[i] = (pl[archp[i]] < 0)? 1: 0;
      pl = setsigns_init(nf, archp, F, signs);
    }
  }
  return mkvec2(fa, pl);
}

/* Given a prime ideal factorization x, possibly with 0 or negative exponents,
 * and a vector w of elements of nf, gives b such that
 * v_p(b-w_p)>=v_p(x) for all prime ideals p in the ideal factorization
 * and v_p(b)>=0 for all other p, using the standard proof given in GTM 138. */
GEN
idealchinese(GEN nf, GEN x, GEN w)
{
  const char *fun = "idealchinese";
  pari_sp av = avma;
  GEN x1, x2, s, dw, F;

  nf = checknf(nf);
  if (!w) return gerepilecopy(av, chineseinit_i(nf,x,NULL,NULL));

  if (typ(w) != t_VEC) pari_err_TYPE(fun,w);
  w = Q_remove_denom(matalgtobasis(nf,w), &dw);
  if (!is_chineseinit(x)) x = chineseinit_i(nf,x,w,dw);
  /* x is a 'chineseinit' */
  x1 = gel(x,1); s = NULL;
  x2 = gel(x,2);
  if (lg(x1) == 1) F = NULL;
  else
  {
    GEN  U = gel(x1,2);
    long i, r = lg(w);
    F = gel(x1,1);
    for (i=1; i<r; i++)
      if (!gequal0(gel(w,i)))
      {
        GEN t = nfmuli(nf, gel(U,i), gel(w,i));
        s = s? ZC_add(s,t): t;
      }
    if (s) s = ZC_reducemodmatrix(s, F);
  }
  if (lg(x2) != 1) s = nfsetsigns(nf, gel(x2,1), s? s: gen_0, x2);
  if (!s) { s = zerocol(nf_get_degree(nf)); dw = NULL; }

  if (dw) s = RgC_Rg_div(s,dw);
  return gerepileupto(av, s);
}

/*************************************************************************/
/**                                                                     **/
/**                           (Z_K/I)^*                                 **/
/**                                                                     **/
/*************************************************************************/
GEN
vecsmall01_to_indices(GEN v)
{
  long i, k, l = lg(v);
  GEN p = new_chunk(l) + l;
  for (k=1, i=l-1; i; i--)
    if (v[i]) { *--p = i; k++; }
  *--p = evallg(k) | evaltyp(t_VECSMALL);
  avma = (pari_sp)p; return p;
}
GEN
vec01_to_indices(GEN v)
{
  long i, k, l;
  GEN p;

  switch (typ(v))
  {
   case t_VECSMALL: return v;
   case t_VEC: break;
   default: pari_err_TYPE("vec01_to_indices",v);
  }
  l = lg(v);
  p = new_chunk(l) + l;
  for (k=1, i=l-1; i; i--)
    if (signe(gel(v,i))) { *--p = i; k++; }
  *--p = evallg(k) | evaltyp(t_VECSMALL);
  avma = (pari_sp)p; return p;
}
GEN
indices_to_vec01(GEN p, long r)
{
  long i, l = lg(p);
  GEN v = zerovec(r);
  for (i = 1; i < l; i++) gel(v, p[i]) = gen_1;
  return v;
}

/* return (column) vector of R1 signatures of x (0 or 1) */
GEN
nfsign_arch(GEN nf, GEN x, GEN arch)
{
  GEN sarch, M, V, archp = vec01_to_indices(arch);
  long i, s, np, n = lg(archp)-1;
  pari_sp av;

  if (!n) return cgetg(1,t_VECSMALL);
  nf = checknf(nf);
  if (typ(x) == t_MAT)
  { /* factorisation */
    GEN g = gel(x,1), e = gel(x,2);
    V = zero_zv(n);
    for (i=1; i<lg(g); i++)
      if (mpodd(gel(e,i)))
        Flv_add_inplace(V, nfsign_arch(nf,gel(g,i),archp), 2);
    avma = (pari_sp)V; return V;
  }
  av = avma; V = cgetg(n+1,t_VECSMALL);
  x = nf_to_scalar_or_basis(nf, x);
  switch(typ(x))
  {
    case t_INT:
      s = signe(x);
      if (!s) pari_err_DOMAIN("nfsign_arch","element","=",gen_0,x);
      avma = av; return const_vecsmall(n, (s < 0)? 1: 0);
    case t_FRAC:
      s = signe(gel(x,1));
      avma = av; return const_vecsmall(n, (s < 0)? 1: 0);
  }
  x = Q_primpart(x); M = nf_get_M(nf); sarch = NULL; np = -1;
  for (i = 1; i <= n; i++)
  {
    long s = eval_sign(M, x, archp[i]);
    if (s < 0) /* failure */
    {
      long ni, r1 = nf_get_r1(nf);
      GEN xi;
      if (np < 0)
      {
        np = num_positive(nf, x);
        if (np == 0) { avma = av; return const_vecsmall(n, 1); }
        if (np == r1){ avma = av; return const_vecsmall(n, 0); }
        sarch = nfarchstar(nf, NULL, identity_perm(r1));
      }
      xi = set_sign_mod_divisor(nf, vecsmall_ei(r1, archp[i]), gen_1, sarch);
      xi = Q_primpart(xi);
      ni = num_positive(nf, nfmuli(nf,x,xi));
      if (ni == 0) { avma = av; V = const_vecsmall(n, 1); V[i] = 0; return V; }
      if (ni == r1){ avma = av; V = const_vecsmall(n, 0); V[i] = 1; return V; }
      s = ni < np? 0: 1;
    }
    V[i] = s;
  }
  avma = (pari_sp)V; return V;
}
static void
chk_ind(const char *s, long i, long r1)
{
  if (i <= 0) pari_err_DOMAIN(s, "index", "<=", gen_0, stoi(i));
  if (i > r1) pari_err_DOMAIN(s, "index", ">", utoi(r1), utoi(i));
}
static GEN
parse_embed(GEN ind, long r, const char *f)
{
  long l, i;
  if (!ind) return identity_perm(r);
  switch(typ(ind))
  {
    case t_INT: case t_VEC: case t_COL: ind = gtovecsmall(ind); break;
    case t_VECSMALL: break;
    default: pari_err_TYPE(f, ind);
  }
  l = lg(ind);
  for (i = 1; i < l; i++) chk_ind(f, ind[i], r);
  return ind;
}
GEN
nfeltsign(GEN nf, GEN x, GEN ind0)
{
  pari_sp av = avma;
  long i, l, r1;
  GEN v, ind;
  nf = checknf(nf); r1 = nf_get_r1(nf);
  x = nf_to_scalar_or_basis(nf, x);
  ind = parse_embed(ind0, r1, "nfeltsign");
  l = lg(ind);
  if (typ(x) != t_COL)
  {
    GEN s;
    switch(gsigne(x))
    {
      case -1:s = gen_m1; break;
      case 1: s = gen_1; break;
      default: s = gen_0; break;
    }
    avma = av;
    return (ind0 && typ(ind0) == t_INT)? s: const_vec(l-1, s);
  }
  v = nfsign_arch(nf, x, ind);
  if (ind0 && typ(ind0) == t_INT) { avma = av; return v[1]? gen_m1: gen_1; }
  settyp(v, t_VEC);
  for (i = 1; i < l; i++) gel(v,i) = v[i]? gen_m1: gen_1;
  return gerepileupto(av, v);
}

GEN
nfeltembed(GEN nf, GEN x, GEN ind0, long prec0)
{
  pari_sp av = avma;
  long i, e, l, r1, r2, prec, prec1;
  GEN v, ind, cx;
  nf = checknf(nf); nf_get_sign(nf,&r1,&r2);
  x = nf_to_scalar_or_basis(nf, x);
  ind = parse_embed(ind0, r1+r2, "nfeltembed");
  l = lg(ind);
  if (typ(x) != t_COL)
  {
    if (!(ind0 && typ(ind0) == t_INT)) x = const_vec(l-1, x);
    return gerepilecopy(av, x);
  }
  x = Q_primitive_part(x, &cx);
  prec1 = prec0; e = gexpo(x);
  if (e > 8) prec1 += nbits2extraprec(e);
  prec = prec1;
  if (nf_get_prec(nf) < prec) nf = nfnewprec_shallow(nf, prec);
  v = cgetg(l, t_VEC);
  for(;;)
  {
    GEN M = nf_get_M(nf);
    for (i = 1; i < l; i++)
    {
      GEN t = nfembed_i(M, x, ind[i]);
      long e = gexpo(t);
      if (gequal0(t) || precision(t) < prec0
                     || (e < 0 && prec < prec1 + nbits2extraprec(-e)) ) break;
      if (cx) t = gmul(t, cx);
      gel(v,i) = t;
    }
    if (i == l) break;
    prec = precdbl(prec);
    if (DEBUGLEVEL>1) pari_warn(warnprec,"eltnfembed", prec);
    nf = nfnewprec_shallow(nf, prec);
  }
  if (ind0 && typ(ind0) == t_INT) v = gel(v,1);
  return gerepilecopy(av, v);
}

/* number of distinct roots of sigma(f) */
GEN
nfpolsturm(GEN nf, GEN f, GEN ind0)
{
  pari_sp av = avma;
  long d, l, r1, single;
  GEN ind, u, v, vr1, T, s, t;

  nf = checknf(nf); T = nf_get_pol(nf); r1 = nf_get_r1(nf);
  ind = parse_embed(ind0, r1, "nfpolsturm");
  single = ind0 && typ(ind0) == t_INT;
  l = lg(ind);

  if (gequal0(f)) pari_err_ROOTS0("nfpolsturm");
  if (typ(f) == t_POL && varn(f) != varn(T))
  {
    f = RgX_nffix("nfsturn", T, f,1);
    if (lg(f) == 3) f = NULL;
  }
  else
  {
    (void)Rg_nffix("nfpolsturm", T, f, 0);
    f = NULL;
  }
  if (!f) { avma = av; return single? gen_0: zerovec(l-1); }
  d = degpol(f);
  if (d == 1) { avma = av; return single? gen_1: const_vec(l-1,gen_1); }

  vr1 = const_vecsmall(l-1, 1);
  u = Q_primpart(f); s = ZV_to_zv(nfeltsign(nf, gel(u,d+2), ind));
  v = RgX_deriv(u); t = odd(d)? leafcopy(s): zv_neg(s);
  for(;;)
  {
    GEN r = RgX_neg( Q_primpart(RgX_pseudorem(u, v)) ), sr;
    long i, dr = degpol(r);
    if (dr < 0) break;
    sr = ZV_to_zv(nfeltsign(nf, gel(r,dr+2), ind));
    for (i = 1; i < l; i++)
      if (sr[i] != s[i]) { s[i] = sr[i], vr1[i]--; }
    if (odd(dr)) sr = zv_neg(sr);
    for (i = 1; i < l; i++)
      if (sr[i] != t[i]) { t[i] = sr[i], vr1[i]++; }
    if (!dr) break;
    u = v; v = r;
  }
  if (single) { avma = av; return stoi(vr1[1]); }
  return gerepileupto(av, zv_to_ZV(vr1));
}


/* return the vector of signs of x; the matrix of such if x is a vector
 * of nf elements */
GEN
nfsign(GEN nf, GEN x)
{
  long i, l;
  GEN archp, S;

  nf = checknf(nf);
  archp = identity_perm( nf_get_r1(nf) );
  if (typ(x) != t_VEC) return nfsign_arch(nf, x, archp);
  l = lg(x); S = cgetg(l, t_MAT);
  for (i=1; i<l; i++) gel(S,i) = nfsign_arch(nf, gel(x,i), archp);
  return S;
}

/* x integral elt, A integral ideal in HNF; reduce x mod A */
static GEN
zk_modHNF(GEN x, GEN A)
{ return (typ(x) == t_COL)?  ZC_hnfrem(x, A): modii(x, gcoeff(A,1,1)); }

/* given an element x in Z_K and an integral ideal y in HNF, coprime with x,
   outputs an element inverse of x modulo y */
GEN
nfinvmodideal(GEN nf, GEN x, GEN y)
{
  pari_sp av = avma;
  GEN a, yZ = gcoeff(y,1,1);

  if (equali1(yZ)) return gen_0;
  x = nf_to_scalar_or_basis(nf, x);
  if (typ(x) == t_INT) return gerepileupto(av, Fp_inv(x, yZ));

  a = hnfmerge_get_1(idealhnf_principal(nf,x), y);
  if (!a) pari_err_INV("nfinvmodideal", x);
  return gerepileupto(av, zk_modHNF(nfdiv(nf,a,x), y));
}

static GEN
nfsqrmodideal(GEN nf, GEN x, GEN id)
{ return zk_modHNF(nfsqri(nf,x), id); }
static GEN
nfmulmodideal(GEN nf, GEN x, GEN y, GEN id)
{ return x? zk_modHNF(nfmuli(nf,x,y), id): y; }
/* assume x integral, k integer, A in HNF */
GEN
nfpowmodideal(GEN nf,GEN x,GEN k,GEN A)
{
  long s = signe(k);
  pari_sp av;
  GEN y;

  if (!s) return gen_1;
  av = avma;
  x = nf_to_scalar_or_basis(nf, x);
  if (typ(x) != t_COL) return Fp_pow(x, k, gcoeff(A,1,1));
  if (s < 0) { x = nfinvmodideal(nf, x,A); k = negi(k); }
  for(y = NULL;;)
  {
    if (mpodd(k)) y = nfmulmodideal(nf,y,x,A);
    k = shifti(k,-1); if (!signe(k)) break;
    x = nfsqrmodideal(nf,x,A);
  }
  return gerepileupto(av, y);
}

/* a * g^n mod id */
static GEN
nfmulpowmodideal(GEN nf, GEN a, GEN g, GEN n, GEN id)
{
  return nfmulmodideal(nf, a, nfpowmodideal(nf,g,n,id), id);
}

/* assume (num(g[i]), id) = 1 for all i. Return prod g[i]^e[i] mod id.
 * EX = multiple of exponent of (O_K/id)^* */
GEN
famat_to_nf_modideal_coprime(GEN nf, GEN g, GEN e, GEN id, GEN EX)
{
  GEN EXo2, plus = NULL, minus = NULL, idZ = gcoeff(id,1,1);
  long i, lx = lg(g);

  if (equali1(idZ)) return gen_1; /* id = Z_K */
  EXo2 = (expi(EX) > 10)? shifti(EX,-1): NULL;
  for (i = 1; i < lx; i++)
  {
    GEN h, n = centermodii(gel(e,i), EX, EXo2);
    long sn = signe(n);
    if (!sn) continue;

    h = nf_to_scalar_or_basis(nf, gel(g,i));
    switch(typ(h))
    {
      case t_INT: break;
      case t_FRAC:
        h = Fp_div(gel(h,1), gel(h,2), idZ); break;
      default:
      {
        GEN dh;
        h = Q_remove_denom(h, &dh);
        if (dh) h = FpC_Fp_mul(h, Fp_inv(dh,idZ), idZ);
      }
    }
    if (sn > 0)
      plus = nfmulpowmodideal(nf, plus, h, n, id);
    else /* sn < 0 */
      minus = nfmulpowmodideal(nf, minus, h, negi(n), id);
  }
  if (minus) plus = nfmulmodideal(nf, plus, nfinvmodideal(nf,minus,id), id);
  return plus? plus: gen_1;
}

/* given 2 integral ideals x, y in HNF s.t x | y | x^2, compute (1+x)/(1+y) in
 * the form [[cyc],[gen], U], where U := ux^-1 as a pair [ZM, denom(U)] */
static GEN
zidealij(GEN x, GEN y)
{
  GEN U, G, cyc, xp = gcoeff(x,1,1), xi = hnf_invscale(x, xp);
  long j, N;

  /* x^(-1) y = relations between the 1 + x_i (HNF) */
  cyc = ZM_snf_group(ZM_Z_divexact(ZM_mul(xi, y), xp), &U, &G);
  N = lg(cyc); G = ZM_mul(x,G); settyp(G, t_VEC); /* new generators */
  for (j=1; j<N; j++)
  {
    GEN c = gel(G,j);
    gel(c,1) = addiu(gel(c,1), 1); /* 1 + g_j */
    if (ZV_isscalar(c)) gel(G,j) = gel(c,1);
  }
  return mkvec4(cyc, G, ZM_mul(U,xi), xp);
}

/* lg(x) > 1, x + 1; shallow */
static GEN
ZC_add1(GEN x)
{
  long i, l = lg(x);
  GEN y = cgetg(l, t_COL);
  for (i = 2; i < l; i++) gel(y,i) = gel(x,i);
  gel(y,1) = addiu(gel(x,1), 1); return y;
}
/* lg(x) > 1, x - 1; shallow */
static GEN
ZC_sub1(GEN x)
{
  long i, l = lg(x);
  GEN y = cgetg(l, t_COL);
  for (i = 2; i < l; i++) gel(y,i) = gel(x,i);
  gel(y,1) = subiu(gel(x,1), 1); return y;
}

/* x,y are t_INT or ZC */
static GEN
zkadd(GEN x, GEN y)
{
  long tx = typ(x);
  if (tx == typ(y))
    return tx == t_INT? addii(x,y): ZC_add(x,y);
  else
    return tx == t_INT? ZC_Z_add(y,x): ZC_Z_add(x,y);
}
/* x a t_INT or ZC, x+1; shallow */
static GEN
zkadd1(GEN x)
{
  long tx = typ(x);
  return tx == t_INT? addiu(x,1): ZC_add1(x);
}
/* x a t_INT or ZC, x-1; shallow */
static GEN
zksub1(GEN x)
{
  long tx = typ(x);
  return tx == t_INT? subiu(x,1): ZC_sub1(x);
}
/* x,y are t_INT or ZC; x - y */
static GEN
zksub(GEN x, GEN y)
{
  long tx = typ(x), ty = typ(y);
  if (tx == ty)
    return tx == t_INT? subii(x,y): ZC_sub(x,y);
  else
    return tx == t_INT? Z_ZC_sub(x,y): ZC_Z_sub(x,y);
}
/* x is t_INT or ZM (mult. map), y is t_INT or ZC; x * y */
static GEN
zkmul(GEN x, GEN y)
{
  long tx = typ(x), ty = typ(y);
  if (ty == t_INT)
    return tx == t_INT? mulii(x,y): ZC_Z_mul(gel(x,1),y);
  else
    return tx == t_INT? ZC_Z_mul(y,x): ZM_ZC_mul(x,y);
}

/* (U,V) = 1 coprime ideals. Want z = x mod U, = y mod V; namely
 * z =vx + uy = v(x-y) + y, where u + v = 1, u in U, v in V.
 * zkc = [v, UV], v a t_INT or ZM (mult. by v map), UV a ZM (ideal in HNF);
 * shallow */
GEN
zkchinese(GEN zkc, GEN x, GEN y)
{
  GEN v = gel(zkc,1), UV = gel(zkc,2), z = zkadd(zkmul(v, zksub(x,y)), y);
  return zk_modHNF(z, UV);
}
/* special case z = x mod U, = 1 mod V; shallow */
GEN
zkchinese1(GEN zkc, GEN x)
{
  GEN v = gel(zkc,1), UV = gel(zkc,2), z = zkadd1(zkmul(v, zksub1(x)));
  return (typ(z) == t_INT)? z: ZC_hnfrem(z, UV);
}
static GEN
zkVchinese1(GEN zkc, GEN v)
{
  long i, ly;
  GEN y = cgetg_copy(v, &ly);
  for (i=1; i<ly; i++) gel(y,i) = zkchinese1(zkc, gel(v,i));
  return y;
}

/* prepare to solve z = x (mod A), z = y mod (B) [zkchinese or zkchinese1] */
GEN
zkchineseinit(GEN nf, GEN A, GEN B, GEN AB)
{
  GEN v;
  long e;
  nf = checknf(nf);
  v = idealaddtoone_raw(nf, A, B);
  if ((e = gexpo(v)) > 5)
  {
    GEN b = (typ(v) == t_COL)? v: scalarcol_shallow(v, nf_get_degree(nf));
    b= ZC_reducemodlll(b, AB);
    if (gexpo(b) < e) v = b;
  }
  return mkvec2(zk_scalar_or_multable(nf,v), AB);
}
/* prepare to solve z = x (mod A), z = 1 mod (B)
 * and then         z = 1 (mod A), z = y mod (B) [zkchinese1 twice] */
static GEN
zkchinese1init2(GEN nf, GEN A, GEN B, GEN AB)
{
  GEN zkc = zkchineseinit(nf, A, B, AB);
  GEN mv = gel(zkc,1), mu;
  if (typ(mv) == t_INT) return mkvec2(zkc, mkvec2(subui(1,mv),AB));
  mu = RgM_Rg_add_shallow(ZM_neg(mv), gen_1);
  return mkvec2(mkvec2(mv,AB), mkvec2(mu,AB));
}

static GEN
apply_U(GEN L, GEN a)
{
  GEN e, U = gel(L,3), dU = gel(L,4);
  if (typ(a) == t_INT)
    e = ZC_Z_mul(gel(U,1), subiu(a, 1));
  else
  { /* t_COL */
    GEN t = gel(a,1);
    gel(a,1) = subiu(gel(a,1), 1); /* a -= 1 */
    e = ZM_ZC_mul(U, a);
    gel(a,1) = t; /* restore */
  }
  return gdiv(e, dU);
}

/* true nf; vectors of [[cyc],[g],U.X^-1]. Assume k > 1. */
static GEN
principal_units(GEN nf, GEN pr, long k, GEN prk)
{
  GEN list, prb;
  ulong mask = quadratic_prec_mask(k);
  long a = 1;

  if (DEBUGLEVEL>3) err_printf("treating pr^%ld, pr = %Ps\n",k,pr);
  prb = pr_hnf(nf,pr);
  list = vectrunc_init(k);
  while (mask > 1)
  {
    GEN pra = prb;
    long b = a << 1;

    if (mask & 1) b--;
    mask >>= 1;
    /* compute 1 + pr^a / 1 + pr^b, 2a <= b */
    if(DEBUGLEVEL>3) err_printf("  treating a = %ld, b = %ld\n",a,b);
    prb = (b >= k)? prk: idealpows(nf,pr,b);
    vectrunc_append(list, zidealij(pra, prb));
    a = b;
  }
  return list;
}
/* a = 1 mod (pr) return log(a) on local-gens of 1+pr/1+pr^k */
static GEN
log_prk1(GEN nf, GEN a, long nh, GEN L2, GEN prk)
{
  GEN y = cgetg(nh+1, t_COL);
  long j, iy, c = lg(L2)-1;
  for (j = iy = 1; j <= c; j++)
  {
    GEN L = gel(L2,j), cyc = gel(L,1), gen = gel(L,2), E = apply_U(L,a);
    long i, nc = lg(cyc)-1;
    int last = (j == c);
    for (i = 1; i <= nc; i++, iy++)
    {
      GEN t, e = gel(E,i);
      if (typ(e) != t_INT) pari_err_COPRIME("zlog_prk1", a, prk);
      t = Fp_neg(e, gel(cyc,i));
      gel(y,iy) = negi(t);
      if (!last && signe(t)) a = nfmulpowmodideal(nf, a, gel(gen,i), t, prk);
    }
  }
  return y;
}
/* true nf */
static GEN
principal_units_relations(GEN nf, GEN L2, GEN prk, long nh)
{
  GEN h = cgetg(nh+1,t_MAT);
  long ih, j, c = lg(L2)-1;
  for (j = ih = 1; j <= c; j++)
  {
    GEN L = gel(L2,j), F = gel(L,1), G = gel(L,2);
    long k, lG = lg(G);
    for (k = 1; k < lG; k++,ih++)
    { /* log(g^f) mod pr^e */
      GEN a = nfpowmodideal(nf,gel(G,k),gel(F,k),prk);
      gel(h,ih) = ZC_neg(log_prk1(nf, a, nh, L2, prk));
      gcoeff(h,ih,ih) = gel(F,k);
    }
  }
  return h;
}
/* true nf; e > 1; multiplicative group (1 + pr) / (1 + pr^k),
 * prk = pr^k or NULL */
static GEN
idealprincipalunits_i(GEN nf, GEN pr, long k, GEN *pU)
{
  GEN cyc, gen, L2, prk = idealpows(nf, pr, k);

  L2 = principal_units(nf, pr, k, prk);
  if (k == 2)
  {
    GEN L = gel(L2,1);
    cyc = gel(L,1);
    gen = gel(L,2);
    if (pU) *pU = matid(lg(gen)-1);
  }
  else
  {
    long c = lg(L2), j;
    GEN EX, h, Ui, vg = cgetg(c, t_VEC);
    for (j = 1; j < c; j++) gel(vg, j) = gmael(L2,j,2);
    vg = shallowconcat1(vg);
    h = principal_units_relations(nf, L2, prk, lg(vg)-1);
    h = ZM_hnfall_i(h, NULL, 0);
    cyc = ZM_snf_group(h, pU, &Ui);
    c = lg(Ui); gen = cgetg(c, t_VEC); EX = gel(cyc,1);
    for (j = 1; j < c; j++)
      gel(gen,j) = famat_to_nf_modideal_coprime(nf, vg, gel(Ui,j), prk, EX);
  }
  return mkvec4(cyc, gen, prk, L2);
}
GEN
idealprincipalunits(GEN nf, GEN pr, long k)
{
  pari_sp av;
  GEN v;
  nf = checknf(nf);
  if (k == 1) { checkprid(pr); retmkvec3(gen_1,cgetg(1,t_VEC),cgetg(1,t_VEC)); }
  av = avma; v = idealprincipalunits_i(nf, pr, k, NULL);
  return gerepilecopy(av, mkvec3(powiu(pr_norm(pr), k-1), gel(v,1), gel(v,2)));
}

/* true nf; given an ideal pr^k dividing an integral ideal x (in HNF form)
 * compute an 'sprk', the structure of G = (Z_K/pr^k)^* [ x = NULL for x=pr^k ]
 * Return a vector with at least 4 components [cyc],[gen],[HNF pr^k,pr,k],ff,
 * where
 * cyc : type of G as abelian group (SNF)
 * gen : generators of G, coprime to x
 * pr^k: in HNF
 * ff  : data for log_g in (Z_K/pr)^*
 * Two extra components are present iff k > 1: L2, U
 * L2  : list of data structures to compute local DL in (Z_K/pr)^*,
 *       and 1 + pr^a/ 1 + pr^b for various a < b <= min(2a, k)
 * U   : base change matrices to convert a vector of local DL to DL wrt gen */
static GEN
sprkinit(GEN nf, GEN pr, GEN gk, GEN x)
{
  GEN T, p, modpr, cyc, gen, g, g0, ord0, A, prk, U, L2;
  long k = itos(gk), f = pr_get_f(pr);

  if(DEBUGLEVEL>3) err_printf("treating pr^%ld, pr = %Ps\n",k,pr);
  modpr = nf_to_Fq_init(nf, &pr,&T,&p);
  /* (Z_K / pr)^* */
  if (f == 1)
  {
    g0 = g = pgener_Fp(p);
    ord0 = get_arith_ZZM(subiu(p,1));
  }
  else
  {
    g0 = g = gener_FpXQ(T,p, &ord0);
    g = Fq_to_nf(g, modpr);
    if (typ(g) == t_POL) g = poltobasis(nf, g);
  }
  A = gel(ord0, 1); /* Norm(pr)-1 */
  if (k == 1)
  {
    cyc = mkvec(A);
    gen = mkvec(g);
    prk = pr_hnf(nf,pr);
    L2 = U = NULL;
  }
  else
  { /* local-gens of (1 + pr)/(1 + pr^k) = SNF-gens * U */
    GEN AB, B, u, v, w;
    long j, l;
    w = idealprincipalunits_i(nf, pr, k, &U);
    /* incorporate (Z_K/pr)^*, order A coprime to B = expo(1+pr/1+pr^k)*/
    cyc = leafcopy(gel(w,1)); B = gel(cyc,1); AB = mulii(A,B);
    gen = leafcopy(gel(w,2));
    prk = gel(w,3);
    g = nfpowmodideal(nf, g, B, prk);
    g0 = Fq_pow(g0, modii(B,A), T, p); /* update primitive root */
    L2 = mkvec3(A, g, gel(w,4));
    gel(cyc,1) = AB;
    gel(gen,1) = nfmulmodideal(nf, gel(gen,1), g, prk);
    u = mulii(Fp_inv(A,B), A);
    v = subui(1, u); l = lg(U);
    for (j = 1; j < l; j++) gcoeff(U,1,j) = Fp_mul(u, gcoeff(U,1,j), AB);
    U = mkvec2(Rg_col_ei(v, lg(gen)-1, 1), U);
  }
  /* local-gens of (Z_K/pr^k)^* = SNF-gens * U */
  if (x)
  {
    GEN uv = zkchineseinit(nf, idealdivpowprime(nf,x,pr,gk), prk, x);
    gen = zkVchinese1(uv, gen);
  }
  return mkvecn(U? 6: 4, cyc, gen, prk, mkvec3(modpr,g0,ord0), L2, U);
}
static GEN
sprk_get_cyc(GEN s) { return gel(s,1); }
static GEN
sprk_get_expo(GEN s)
{
  GEN cyc = sprk_get_cyc(s);
  return lg(cyc) == 1? gen_1: gel(cyc, 1);
}
static GEN
sprk_get_gen(GEN s) { return gel(s,2); }
static GEN
sprk_get_prk(GEN s) { return gel(s,3); }
static GEN
sprk_get_ff(GEN s) { return gel(s,4); }
static GEN
sprk_get_pr(GEN s) { GEN ff = gel(s,4); return modpr_get_pr(gel(ff,1)); }
/* A = Npr-1, <g> = (Z_K/pr)^*, L2 to 1 + pr / 1 + pr^k */
static void
sprk_get_L2(GEN s, GEN *A, GEN *g, GEN *L2)
{ GEN v = gel(s,5); *A = gel(v,1); *g = gel(v,2); *L2 = gel(v,3); }
static void
sprk_get_U2(GEN s, GEN *U1, GEN *U2)
{ GEN v = gel(s,6); *U1 = gel(v,1); *U2 = gel(v,2); }
static int
sprk_is_prime(GEN s) { return lg(s) == 5; }

static GEN
famat_zlog_pr(GEN nf, GEN g, GEN e, GEN sprk)
{
  GEN pr = sprk_get_pr(sprk);
  GEN prk = sprk_get_prk(sprk);
  GEN x = famat_makecoprime(nf, g, e, pr, prk, sprk_get_expo(sprk));
  return zlog_pr(nf, x, sprk);
}
/* log_g(a) in (Z_K/pr)^* */
static GEN
nf_log(GEN nf, GEN a, GEN ff)
{
  GEN pr = gel(ff,1), g = gel(ff,2), ord = gel(ff,3);
  GEN T,p, modpr = nf_to_Fq_init(nf, &pr, &T, &p);
  return Fq_log(nf_to_Fq(nf,a,modpr), g, ord, T, p);
}
/* a in Z_K (t_COL or t_INT), pr prime ideal, sprk = sprkinit(nf,pr,k,x).
 * return log(a) on SNF-generators of (Z_K/pr^k)^**/
GEN
zlog_pr(GEN nf, GEN a, GEN sprk)
{
  GEN e, prk, A, g, L2, U1, U2, y;

  if (typ(a) == t_MAT) return famat_zlog_pr(nf, gel(a,1), gel(a,2), sprk);

  e = nf_log(nf, a, sprk_get_ff(sprk));
  if (sprk_is_prime(sprk)) return mkcol(e); /* k = 1 */
  prk = sprk_get_prk(sprk);
  sprk_get_L2(sprk, &A,&g,&L2);
  if (signe(e))
  {
    e = Fp_neg(e, A);
    a = nfmulpowmodideal(nf, a, g, e, prk);
  }
  sprk_get_U2(sprk, &U1,&U2);
  y = ZM_ZC_mul(U2, log_prk1(nf, a, lg(U2)-1, L2, prk));
  if (signe(e)) y = ZC_sub(y, ZC_Z_mul(U1,e));
  return vecmodii(y, sprk_get_cyc(sprk));
}
GEN
zlog_pr_init(GEN nf, GEN pr, long k)
{ return sprkinit(checknf(nf),pr,utoipos(k),NULL);}
GEN
vzlog_pr(GEN nf, GEN v, GEN sprk)
{
  long l = lg(v), i;
  GEN w = cgetg(l, t_MAT);
  for (i = 1; i < l; i++) gel(w,i) = zlog_pr(nf, gel(v,i), sprk);
  return w;
}

static GEN
famat_zlog(GEN nf, GEN fa, GEN sgn, zlog_S *S)
{
  long i, n0, n = lg(S->U)-1;
  GEN g, e, y;
  if (lg(fa) == 1) return zerocol(n);
  g = gel(fa,1);
  e = gel(fa,2);
  y = cgetg(n+1, t_COL);
  n0 = lg(S->sprk)-1; /* n0 = n (trivial arch. part), or n-1 */
  for (i=1; i <= n0; i++) gel(y,i) = famat_zlog_pr(nf, g, e, gel(S->sprk,i));
  if (n0 != n)
  {
    if (!sgn) sgn = nfsign_arch(nf, fa, S->archp);
    gel(y,n) = Flc_to_ZC(sgn);
  }
  return y;
}

/* assume that cyclic factors are normalized, in particular != [1] */
static GEN
split_U(GEN U, GEN Sprk)
{
  long t = 0, k, n, l = lg(Sprk);
  GEN vU = cgetg(l+1, t_VEC);
  for (k = 1; k < l; k++)
  {
    n = lg(sprk_get_cyc(gel(Sprk,k))) - 1; /* > 0 */
    gel(vU,k) = vecslice(U, t+1, t+n);
    t += n;
  }
  /* t+1 .. lg(U)-1 */
  n = lg(U) - t - 1; /* can be 0 */
  if (!n) setlg(vU,l); else gel(vU,l) = vecslice(U, t+1, t+n);
  return vU;
}

void
init_zlog(zlog_S *S, GEN bid)
{
  GEN fa2 = bid_get_fact2(bid);
  S->U = bid_get_U(bid);
  S->hU = lg(bid_get_cyc(bid))-1;
  S->archp = bid_get_archp(bid);
  S->sprk = bid_get_sprk(bid);
  S->bid = bid;
  S->P = gel(fa2,1);
  S->k = gel(fa2,2);
  S->no2 = lg(S->P) == lg(gel(bid_get_fact(bid),1));
}

/* a a t_FRAC/t_INT, reduce mod bid */
static GEN
Q_mod_bid(GEN bid, GEN a)
{
  GEN xZ = gcoeff(bid_get_ideal(bid),1,1);
  GEN b = Rg_to_Fp(a, xZ);
  if (gsigne(a) < 0) b = subii(b, xZ);
  return signe(b)? b: xZ;
}
/* Return decomposition of a on the CRT generators blocks attached to the
 * S->sprk and sarch; sgn = sign(a, S->arch), NULL if unknown */
static GEN
zlog(GEN nf, GEN a, GEN sgn, zlog_S *S)
{
  long k, l;
  GEN y;
  a = nf_to_scalar_or_basis(nf, a);
  switch(typ(a))
  {
    case t_INT: break;
    case t_FRAC: a = Q_mod_bid(S->bid, a); break;
    default: /* case t_COL: */
    {
      GEN den;
      check_nfelt(a, &den);
      if (den)
      {
        a = Q_muli_to_int(a, den);
        a = mkmat2(mkcol2(a, den), mkcol2(gen_1, gen_m1));
        return famat_zlog(nf, a, sgn, S);
      }
    }
  }
  if (sgn)
    sgn = (lg(sgn) == 1)? NULL: leafcopy(sgn);
  else
    sgn = (lg(S->archp) == 1)? NULL: nfsign_arch(nf, a, S->archp);
  l = lg(S->sprk);
  y = cgetg(sgn? l+1: l, t_COL);
  for (k = 1; k < l; k++)
  {
    GEN sprk = gel(S->sprk,k);
    gel(y,k) = zlog_pr(nf, a, sprk);
  }
  if (sgn) gel(y,l) = Flc_to_ZC(sgn);
  return y;
}

/* true nf */
GEN
pr_basis_perm(GEN nf, GEN pr)
{
  long f = pr_get_f(pr);
  GEN perm;
  if (f == nf_get_degree(nf)) return identity_perm(f);
  perm = cgetg(f+1, t_VECSMALL);
  perm[1] = 1;
  if (f > 1)
  {
    GEN H = pr_hnf(nf,pr);
    long i, k;
    for (i = k = 2; k <= f; i++)
      if (!equali1(gcoeff(H,i,i))) perm[k++] = i;
  }
  return perm;
}

/* \sum U[i]*y[i], U[i] ZM, y[i] ZC. We allow lg(y) > lg(U). */
static GEN
ZMV_ZCV_mul(GEN U, GEN y)
{
  long i, l = lg(U);
  GEN z = NULL;
  if (l == 1) return cgetg(1,t_COL);
  for (i = 1; i < l; i++)
  {
    GEN u = ZM_ZC_mul(gel(U,i), gel(y,i));
    z = z? ZC_add(z, u): u;
  }
  return z;
}
/* A * (U[1], ..., U[d] */
static GEN
ZM_ZMV_mul(GEN A, GEN U)
{
  long i, l;
  GEN V = cgetg_copy(U,&l);
  for (i = 1; i < l; i++) gel(V,i) = ZM_mul(A,gel(U,i));
  return V;
}

/* Log on bid.gen of generators of P_{1,I pr^{e-1}} / P_{1,I pr^e} (I,pr) = 1,
 * defined implicitly via CRT. 'ind' is the index of pr in modulus
 * factorization */
GEN
log_gen_pr(zlog_S *S, long ind, GEN nf, long e)
{
  GEN A, sprk = gel(S->sprk,ind), Uind = gel(S->U, ind);

  if (e == 1) retmkmat( gel(Uind,1) );
  else
  {
    GEN G, pr = sprk_get_pr(sprk);
    long i, l;
    if (e == 2)
    {
      GEN A, g, L, L2; sprk_get_L2(sprk,&A,&g,&L2); L = gel(L2,1);
      G = gel(L,2); l = lg(G);
    }
    else
    {
      GEN perm = pr_basis_perm(nf,pr), PI = nfpow_u(nf, pr_get_gen(pr), e-1);
      l = lg(perm);
      G = cgetg(l, t_VEC);
      if (typ(PI) == t_INT)
      { /* zk_ei_mul doesn't allow t_INT */
        long N = nf_get_degree(nf);
        gel(G,1) = addiu(PI,1);
        for (i = 2; i < l; i++)
        {
          GEN z = col_ei(N, 1);
          gel(G,i) = z; gel(z, perm[i]) = PI;
        }
      }
      else
      {
        gel(G,1) = nfadd(nf, gen_1, PI);
        for (i = 2; i < l; i++)
          gel(G,i) = nfadd(nf, gen_1, zk_ei_mul(nf, PI, perm[i]));
      }
    }
    A = cgetg(l, t_MAT);
    for (i = 1; i < l; i++)
      gel(A,i) = ZM_ZC_mul(Uind, zlog_pr(nf, gel(G,i), sprk));
    return A;
  }
}
/* Log on bid.gen of generator of P_{1,f} / P_{1,f v[index]}
 * v = vector of r1 real places */
GEN
log_gen_arch(zlog_S *S, long index)
{
  GEN U = gel(S->U, lg(S->U)-1);
  return gel(U, index);
}

/* compute bid.clgp: [h,cyc] or [h,cyc,gen] */
static GEN
bid_grp(GEN nf, GEN U, GEN cyc, GEN g, GEN F, GEN sarch)
{
  GEN G, h = ZV_prod(cyc);
  long c;
  if (!U) return mkvec2(h,cyc);
  c = lg(U);
  G = cgetg(c,t_VEC);
  if (c > 1)
  {
    GEN U0, Uoo, EX = gel(cyc,1); /* exponent of bid */
    long i, hU = nbrows(U), nba = lg(sarch_get_cyc(sarch))-1; /* #f_oo */
    if (!nba) { U0 = U; Uoo = NULL; }
    else if (nba == hU) { U0 = NULL; Uoo = U; }
    else
    {
      U0 = rowslice(U, 1, hU-nba);
      Uoo = rowslice(U, hU-nba+1, hU);
    }
    for (i = 1; i < c; i++)
    {
      GEN t = gen_1;
      if (U0) t = famat_to_nf_modideal_coprime(nf, g, gel(U0,i), F, EX);
      if (Uoo) t = set_sign_mod_divisor(nf, ZV_to_Flv(gel(Uoo,i),2), t, sarch);
      gel(G,i) = t;
    }
  }
  return mkvec3(h, cyc, G);
}

/* remove prime ideals of norm 2 with exponent 1 from factorization */
static GEN
famat_strip2(GEN fa)
{
  GEN P = gel(fa,1), E = gel(fa,2), Q, F;
  long l = lg(P), i, j;
  Q = cgetg(l, t_COL);
  F = cgetg(l, t_COL);
  for (i = j = 1; i < l; i++)
  {
    GEN pr = gel(P,i), e = gel(E,i);
    if (!absequaliu(pr_get_p(pr), 2) || itou(e) != 1 || pr_get_f(pr) != 1)
    {
      gel(Q,j) = pr;
      gel(F,j) = e; j++;
    }
  }
  setlg(Q,j);
  setlg(F,j); return mkmat2(Q,F);
}

/* Compute [[ideal,arch], [h,[cyc],[gen]], idealfact, [liste], U]
   flag may include nf_GEN | nf_INIT */
static GEN
Idealstar_i(GEN nf, GEN ideal, long flag)
{
  long i, k, nbp, R1;
  GEN y, cyc, U, u1 = NULL, fa, fa2, sprk, x, arch, archp, E, P, sarch, gen;

  nf = checknf(nf);
  R1 = nf_get_r1(nf);
  if (typ(ideal) == t_VEC && lg(ideal) == 3)
  {
    arch = gel(ideal,2);
    ideal= gel(ideal,1);
    switch(typ(arch))
    {
      case t_VEC:
        if (lg(arch) != R1+1)
          pari_err_TYPE("Idealstar [incorrect archimedean component]",arch);
        archp = vec01_to_indices(arch);
        break;
      case t_VECSMALL:
        archp = arch;
        k = lg(archp)-1;
        if (k && archp[k] > R1)
          pari_err_TYPE("Idealstar [incorrect archimedean component]",arch);
        arch = indices_to_vec01(archp, R1);
        break;
      default:
        pari_err_TYPE("Idealstar [incorrect archimedean component]",arch);
        return NULL;
    }
  }
  else
  {
    arch = zerovec(R1);
    archp = cgetg(1, t_VECSMALL);
  }
  if (is_nf_factor(ideal))
  {
    fa = ideal;
    x = idealfactorback(nf, gel(fa,1), gel(fa,2), 0);
  }
  else
  {
    fa = idealfactor(nf, ideal);
    x = ideal;
  }
  if (typ(x) != t_MAT)  x = idealhnf_shallow(nf, x);
  if (lg(x) == 1) pari_err_DOMAIN("Idealstar", "ideal","=",gen_0,x);
  if (typ(gcoeff(x,1,1)) != t_INT)
    pari_err_DOMAIN("Idealstar","denominator(ideal)", "!=",gen_1,x);
  sarch = nfarchstar(nf, x, archp);
  fa2 = famat_strip2(fa);
  P = gel(fa2,1);
  E = gel(fa2,2);
  nbp = lg(P)-1;
  sprk = cgetg(nbp+1,t_VEC);
  if (nbp)
  {
    GEN t = (lg(gel(fa,1))==2)? NULL: x; /* beware fa != fa2 */
    cyc = cgetg(nbp+2,t_VEC);
    gen = cgetg(nbp+1,t_VEC);
    for (i = 1; i <= nbp; i++)
    {
      GEN L = sprkinit(nf, gel(P,i), gel(E,i), t);
      gel(sprk,i) = L;
      gel(cyc,i) = sprk_get_cyc(L);
      /* true gens are congruent to those mod x AND positive at archp */
      gel(gen,i) = sprk_get_gen(L);
    }
    gel(cyc,i) = sarch_get_cyc(sarch);
    cyc = shallowconcat1(cyc);
    gen = shallowconcat1(gen);
    cyc = ZV_snf_group(cyc, &U, (flag & nf_GEN)? &u1: NULL);
  }
  else
  {
    cyc = sarch_get_cyc(sarch);
    gen = cgetg(1,t_VEC);
    U = matid(lg(cyc)-1);
    if (flag & nf_GEN) u1 = U;
  }
  y = bid_grp(nf, u1, cyc, gen, x, sarch);
  if (!(flag & nf_INIT)) return y;
  U = split_U(U, sprk);
  return mkvec5(mkvec2(x, arch), y, mkvec2(fa,fa2), mkvec2(sprk, sarch), U);
}
GEN
Idealstar(GEN nf, GEN ideal, long flag)
{
  pari_sp av = avma;
  if (!nf) nf = nfinit(pol_x(0), DEFAULTPREC);
  return gerepilecopy(av, Idealstar_i(nf, ideal, flag));
}
GEN
Idealstarprk(GEN nf, GEN pr, long k, long flag)
{
  pari_sp av = avma;
  GEN z = Idealstar_i(nf, mkmat2(mkcol(pr),mkcols(k)), flag);
  return gerepilecopy(av, z);
}

/* FIXME: obsolete */
GEN
zidealstarinitgen(GEN nf, GEN ideal)
{ return Idealstar(nf,ideal, nf_INIT|nf_GEN); }
GEN
zidealstarinit(GEN nf, GEN ideal)
{ return Idealstar(nf,ideal, nf_INIT); }
GEN
zidealstar(GEN nf, GEN ideal)
{ return Idealstar(nf,ideal, nf_GEN); }

GEN
idealstar0(GEN nf, GEN ideal,long flag)
{
  switch(flag)
  {
    case 0: return Idealstar(nf,ideal, nf_GEN);
    case 1: return Idealstar(nf,ideal, nf_INIT);
    case 2: return Idealstar(nf,ideal, nf_INIT|nf_GEN);
    default: pari_err_FLAG("idealstar");
  }
  return NULL; /* LCOV_EXCL_LINE */
}

void
check_nfelt(GEN x, GEN *den)
{
  long l = lg(x), i;
  GEN t, d = NULL;
  if (typ(x) != t_COL) pari_err_TYPE("check_nfelt", x);
  for (i=1; i<l; i++)
  {
    t = gel(x,i);
    switch (typ(t))
    {
      case t_INT: break;
      case t_FRAC:
        if (!d) d = gel(t,2); else d = lcmii(d, gel(t,2));
        break;
      default: pari_err_TYPE("check_nfelt", x);
    }
  }
  *den = d;
}

GEN
vecmodii(GEN x, GEN y)
{ pari_APPLY_same(modii(gel(x,i), gel(y,i))) }

GEN
vecmoduu(GEN x, GEN y)
{ pari_APPLY_ulong(uel(x,i) % uel(y,i)) }

static GEN
ideallog_i(GEN nf, GEN x, GEN sgn, zlog_S *S)
{
  pari_sp av = avma;
  GEN y, cyc;
  if (!S->hU) return cgetg(1, t_COL);
  cyc = bid_get_cyc(S->bid);
  if (typ(x) == t_MAT)
  {
    if (lg(x) == 1) return zerocol(lg(cyc)-1);
    y = famat_zlog(nf, x, sgn, S);
  }
  else
    y = zlog(nf, x, sgn, S);
  y = ZMV_ZCV_mul(S->U, y);
  return gerepileupto(av, vecmodii(y, cyc));
}

/* Given x (not necessarily integral), and bid as output by zidealstarinit,
 * compute the vector of components on the generators bid[2].
 * Assume (x,bid) = 1 and sgn is either NULL or nfsign_arch(x, bid) */
GEN
ideallog_sgn(GEN nf, GEN x, GEN sgn, GEN bid)
{
  zlog_S S;
  nf = checknf(nf); checkbid(bid);
  init_zlog(&S, bid);
  if (sgn && typ(x) == t_VEC) /* vector of elements and signatures */
  {
    long i, l = lg(x);
    GEN y = cgetg(l, t_MAT);
    for (i = 1; i < l; i++) gel(y,i) = ideallog_i(nf, gel(x,i), gel(sgn,i), &S);
    return y;
  }
  return ideallog_i(nf, x, sgn, &S);
}
GEN
ideallog(GEN nf, GEN x, GEN bid)
{
  if (!nf) return Zideallog(bid, x);
  return ideallog_sgn(nf, x, NULL, bid);
}

/*************************************************************************/
/**                                                                     **/
/**               JOIN BID STRUCTURES, IDEAL LISTS                      **/
/**                                                                     **/
/*************************************************************************/
/* bid1, bid2: for coprime modules m1 and m2 (without arch. part).
 * Output: bid for m1 m2 */
static GEN
join_bid(GEN nf, GEN bid1, GEN bid2)
{
  pari_sp av = avma;
  long nbgen, l1,l2;
  GEN I1,I2, G1,G2, sprk1,sprk2, cyc1,cyc2, sarch;
  GEN sprk, fa,fa2, U, cyc, y, u1 = NULL, x, gen;

  I1 = bid_get_ideal(bid1);
  I2 = bid_get_ideal(bid2);
  if (gequal1(gcoeff(I1,1,1))) return bid2; /* frequent trivial case */
  G1 = bid_get_grp(bid1);
  G2 = bid_get_grp(bid2);
  x = idealmul(nf, I1,I2);
  fa = famat_mul_shallow(bid_get_fact(bid1), bid_get_fact(bid2));
  fa2= famat_mul_shallow(bid_get_fact2(bid1), bid_get_fact2(bid2));
  sprk1 = bid_get_sprk(bid1);
  sprk2 = bid_get_sprk(bid2);
  sprk = shallowconcat(sprk1, sprk2);

  cyc1 = abgrp_get_cyc(G1); l1 = lg(cyc1);
  cyc2 = abgrp_get_cyc(G2); l2 = lg(cyc2);
  gen = (lg(G1)>3 && lg(G2)>3)? gen_1: NULL;
  nbgen = l1+l2-2;
  cyc = ZV_snf_group(shallowconcat(cyc1,cyc2), &U, gen? &u1: NULL);
  if (nbgen)
  {
    GEN U1 = bid_get_U(bid1), U2 = bid_get_U(bid2);
    U1 = l1==1? const_vec(lg(sprk1), cgetg(1,t_MAT))
              : ZM_ZMV_mul(vecslice(U, 1, l1-1),   U1);
    U2 = l2==1? const_vec(lg(sprk2), cgetg(1,t_MAT))
              : ZM_ZMV_mul(vecslice(U, l1, nbgen), U2);
    U = shallowconcat(U1, U2);
  }
  else
    U = const_vec(lg(sprk), cgetg(1,t_MAT));

  if (gen)
  {
    GEN uv = zkchinese1init2(nf, I2, I1, x);
    gen = shallowconcat(zkVchinese1(gel(uv,1), abgrp_get_gen(G1)),
                        zkVchinese1(gel(uv,2), abgrp_get_gen(G2)));
  }
  sarch = bid_get_sarch(bid1); /* trivial */
  y = bid_grp(nf, u1, cyc, gen, x, sarch);
  x = mkvec2(x, bid_get_arch(bid1));
  y = mkvec5(x, y, mkvec2(fa, fa2), mkvec2(sprk, sarch), U);
  return gerepilecopy(av,y);
}

typedef struct _ideal_data {
  GEN nf, emb, L, pr, prL, sgnU, archp;
} ideal_data;

/* z <- ( z | f(v[i])_{i=1..#v} ) */
static void
concat_join(GEN *pz, GEN v, GEN (*f)(ideal_data*,GEN), ideal_data *data)
{
  long i, nz, lv = lg(v);
  GEN z, Z;
  if (lv == 1) return;
  z = *pz; nz = lg(z)-1;
  *pz = Z = cgetg(lv + nz, typ(z));
  for (i = 1; i <=nz; i++) gel(Z,i) = gel(z,i);
  Z += nz;
  for (i = 1; i < lv; i++) gel(Z,i) = f(data, gel(v,i));
}
static GEN
join_idealinit(ideal_data *D, GEN x)
{ return join_bid(D->nf, x, D->prL); }
static GEN
join_ideal(ideal_data *D, GEN x)
{ return idealmulpowprime(D->nf, x, D->pr, D->L); }
static GEN
join_unit(ideal_data *D, GEN x)
{
  GEN bid = join_idealinit(D, gel(x,1)), u = gel(x,2), v = mkvec(D->emb);
  if (lg(u) != 1) v = shallowconcat(u, v);
  return mkvec2(bid, v);
}

/*  flag & nf_GEN : generators, otherwise no
 *  flag &2 : units, otherwise no
 *  flag &4 : ideals in HNF, otherwise bid
 *  flag &8 : omit ideals which cannot be conductors (pr^1 with Npr=2) */
static GEN
Ideallist(GEN bnf, ulong bound, long flag)
{
  const long cond = flag & 8;
  const long do_units = flag & 2, big_id = !(flag & 4);
  const long istar_flag = (flag & nf_GEN) | nf_INIT;
  pari_sp av, av0 = avma;
  long i, j;
  GEN nf, z, p, fa, id, BOUND, U, empty = cgetg(1,t_VEC);
  forprime_t S;
  ideal_data ID;
  GEN (*join_z)(ideal_data*, GEN) =
    do_units? &join_unit
              : (big_id? &join_idealinit: &join_ideal);

  nf = checknf(bnf);
  if ((long)bound <= 0) return empty;
  id = matid(nf_get_degree(nf));
  if (big_id) id = Idealstar(nf,id, istar_flag);

  /* z[i] will contain all "objects" of norm i. Depending on flag, this means
   * an ideal, a bid, or a couple [bid, log(units)]. Such objects are stored
   * in vectors, computed one primary component at a time; join_z
   * reconstructs the global object */
  BOUND = utoipos(bound);
  z = cgetg(bound+1,t_VEC);
  if (do_units) {
    U = bnf_build_units(bnf);
    gel(z,1) = mkvec( mkvec2(id, cgetg(1,t_VEC)) );
  } else {
    U = NULL; /* -Wall */
    gel(z,1) = mkvec(id);
  }
  for (i=2; i<=(long)bound; i++) gel(z,i) = empty;
  ID.nf = nf;

  p = cgetipos(3);
  u_forprime_init(&S, 2, bound);
  av = avma;
  while ((p[2] = u_forprime_next(&S)))
  {
    if (DEBUGLEVEL>1) { err_printf("%ld ",p[2]); err_flush(); }
    fa = idealprimedec_limit_norm(nf, p, BOUND);
    for (j=1; j<lg(fa); j++)
    {
      GEN pr = gel(fa,j), z2 = leafcopy(z);
      ulong Q, q = upr_norm(pr);
      long l = (cond && q == 2)? 2: 1;

      ID.pr = ID.prL = pr;
      for (Q = q; Q <= bound; l++, Q *= q) /* add pr^l */
      {
        ulong iQ;
        ID.L = utoipos(l);
        if (big_id) {
          ID.prL = Idealstarprk(nf, pr, l, istar_flag);
          if (do_units)
          {
            GEN sprk = bid_get_sprk(ID.prL);
            ID.emb = lg(sprk) == 1? cgetg(1,t_VEC)
                                  : vzlog_pr(nf, U, gel(sprk,1));
          }
        }
        for (iQ = Q,i = 1; iQ <= bound; iQ += Q,i++)
          concat_join(&gel(z,iQ), gel(z2,i), join_z, &ID);
      }
    }
    if (gc_needed(av,1))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"Ideallist");
      z = gerepilecopy(av, z);
    }
  }
  return gerepilecopy(av0, z);
}
GEN
ideallist0(GEN bnf,long bound, long flag) {
  if (flag<0 || flag>15) pari_err_FLAG("ideallist");
  return Ideallist(bnf,bound,flag);
}
GEN
ideallist(GEN bnf,long bound) { return Ideallist(bnf,bound,4); }

/* bid = for module m (without arch. part), arch = archimedean part.
 * Output: bid for [m,arch] */
static GEN
join_bid_arch(GEN nf, GEN bid, GEN archp)
{
  pari_sp av = avma;
  GEN G, U;
  GEN sprk, cyc, y, u1 = NULL, x, sarch, gen;

  checkbid(bid);
  G = bid_get_grp(bid);
  x = bid_get_ideal(bid);
  sarch = nfarchstar(nf, bid_get_ideal(bid), archp);
  sprk = bid_get_sprk(bid);

  gen = (lg(G)>3)? gel(G,3): NULL;
  cyc = diagonal_shallow(shallowconcat(gel(G,2), sarch_get_cyc(sarch)));
  cyc = ZM_snf_group(cyc, &U, gen? &u1: NULL);
  y = bid_grp(nf, u1, cyc, gen, x, sarch);
  U = split_U(U, sprk);
  y = mkvec5(mkvec2(x, archp), y, gel(bid,3), mkvec2(sprk, sarch), U);
  return gerepilecopy(av,y);
}
static GEN
join_arch(ideal_data *D, GEN x) {
  return join_bid_arch(D->nf, x, D->archp);
}
static GEN
join_archunit(ideal_data *D, GEN x) {
  GEN bid = join_arch(D, gel(x,1)), u = gel(x,2), v = mkvec(D->emb);
  if (lg(u) != 1) v = shallowconcat(u, v);
  return mkvec2(bid, v);
}

/* L from ideallist, add archimedean part */
GEN
ideallistarch(GEN bnf, GEN L, GEN arch)
{
  pari_sp av;
  long i, j, l = lg(L), lz;
  GEN v, z, V;
  ideal_data ID;
  GEN (*join_z)(ideal_data*, GEN);

  if (typ(L) != t_VEC) pari_err_TYPE("ideallistarch",L);
  if (l == 1) return cgetg(1,t_VEC);
  z = gel(L,1);
  if (typ(z) != t_VEC) pari_err_TYPE("ideallistarch",z);
  z = gel(z,1); /* either a bid or [bid,U] */
  ID.nf = checknf(bnf);
  ID.archp = vec01_to_indices(arch);
  if (lg(z) == 3) { /* the latter: do units */
    if (typ(z) != t_VEC) pari_err_TYPE("ideallistarch",z);
    ID.emb = zm_to_ZM( rowpermute(nfsign_units(bnf,NULL,1), ID.archp) );
    join_z = &join_archunit;
  } else
    join_z = &join_arch;
  av = avma; V = cgetg(l, t_VEC);
  for (i = 1; i < l; i++)
  {
    z = gel(L,i); lz = lg(z);
    gel(V,i) = v = cgetg(lz,t_VEC);
    for (j=1; j<lz; j++) gel(v,j) = join_z(&ID, gel(z,j));
  }
  return gerepilecopy(av,V);
}
