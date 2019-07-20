/* Copyright (C) 2000-2003  The PARI group.

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

/*************************************************************************/
/**                                                                     **/
/**                   Routines for handling VEC/COL                     **/
/**                                                                     **/
/*************************************************************************/
int
vec_isconst(GEN v)
{
  long i, l = lg(v);
  GEN w;
  if (l==1) return 1;
  w = gel(v,1);
  for(i=2;i<l;i++)
    if (!gequal(gel(v,i), w)) return 0;
  return 1;
}

/* Check if all the elements of v are different.
 * Use a quadratic algorithm. Could be done in n*log(n) by sorting. */
int
vec_is1to1(GEN v)
{
  long i, j, l = lg(v);
  for (i=1; i<l; i++)
  {
    GEN w = gel(v,i);
    for(j=i+1; j<l; j++)
      if (gequal(gel(v,j), w)) return 0;
  }
  return 1;
}

GEN
vec_insert(GEN v, long n, GEN x)
{
  long i, l=lg(v);
  GEN V = cgetg(l+1,t_VEC);
  for(i=1; i<n; i++) gel(V,i) = gel(v,i);
  gel(V,n) = x;
  for(i=n+1; i<=l; i++) gel(V,i) = gel(v,i-1);
  return V;
}
/*************************************************************************/
/**                                                                     **/
/**                   Routines for handling VECSMALL                    **/
/**                                                                     **/
/*************************************************************************/
/* Sort v[0]...v[n-1] and put result in w[0]...w[n-1].
 * We accept v==w. w must be allocated. */
static void
vecsmall_sortspec(GEN v, long n, GEN w)
{
  pari_sp ltop=avma;
  long nx=n>>1, ny=n-nx;
  long m, ix, iy;
  GEN x, y;
  if (n<=2)
  {
    if (n==1)
      w[0]=v[0];
    else if (n==2)
    {
      long v0=v[0], v1=v[1];
      if (v0<=v1) { w[0]=v0; w[1]=v1; }
      else        { w[0]=v1; w[1]=v0; }
    }
    return;
  }
  x=new_chunk(nx); y=new_chunk(ny);
  vecsmall_sortspec(v,nx,x);
  vecsmall_sortspec(v+nx,ny,y);
  for (m=0, ix=0, iy=0; ix<nx && iy<ny; )
    if (x[ix]<=y[iy])
      w[m++]=x[ix++];
    else
      w[m++]=y[iy++];
  for(;ix<nx;) w[m++]=x[ix++];
  for(;iy<ny;) w[m++]=y[iy++];
  avma=ltop;
}

/*in place sort.*/
void
vecsmall_sort(GEN V)
{
  long l = lg(V)-1;
  if (l<=1) return;
  vecsmall_sortspec(V+1,l,V+1);
}

/* cf gen_sortspec */
static GEN
vecsmall_indexsortspec(GEN v, long n)
{
  long nx, ny, m, ix, iy;
  GEN x, y, w;
  switch(n)
  {
    case 1: return mkvecsmall(1);
    case 2: return (v[1] <= v[2])? mkvecsmall2(1,2): mkvecsmall2(2,1);
    case 3:
      if (v[1] <= v[2]) {
        if (v[2] <= v[3]) return mkvecsmall3(1,2,3);
        return (v[1] <= v[3])? mkvecsmall3(1,3,2)
                             : mkvecsmall3(3,1,2);
      } else {
        if (v[1] <= v[3]) return mkvecsmall3(2,1,3);
        return (v[2] <= v[3])? mkvecsmall3(2,3,1)
                             : mkvecsmall3(3,2,1);
      }
  }
  nx = n>>1; ny = n-nx;
  w = cgetg(n+1,t_VECSMALL);
  x = vecsmall_indexsortspec(v,nx);
  y = vecsmall_indexsortspec(v+nx,ny);
  for (m=1, ix=1, iy=1; ix<=nx && iy<=ny; )
    if (v[x[ix]] <= v[y[iy]+nx])
      w[m++] = x[ix++];
    else
      w[m++] = y[iy++]+nx;
  for(;ix<=nx;) w[m++] = x[ix++];
  for(;iy<=ny;) w[m++] = y[iy++]+nx;
  avma = (pari_sp)w; return w;
}

/*indirect sort.*/
GEN
vecsmall_indexsort(GEN V)
{
  long l=lg(V)-1;
  if (l==0) return cgetg(1, t_VECSMALL);
  return vecsmall_indexsortspec(V,l);
}

/* assume V sorted */
GEN
vecsmall_uniq_sorted(GEN V)
{
  GEN W;
  long i,j, l = lg(V);
  if (l == 1) return vecsmall_copy(V);
  W = cgetg(l,t_VECSMALL);
  W[1] = V[1];
  for(i=j=2; i<l; i++)
    if (V[i] != W[j-1]) W[j++] = V[i];
  stackdummy((pari_sp)(W + l), (pari_sp)(W + j));
  setlg(W, j); return W;
}

GEN
vecsmall_uniq(GEN V)
{
  pari_sp av = avma;
  V = zv_copy(V); vecsmall_sort(V);
  return gerepileuptoleaf(av, vecsmall_uniq_sorted(V));
}

/* assume x sorted */
long
vecsmall_duplicate_sorted(GEN x)
{
  long i,k,l=lg(x);
  if (l==1) return 0;
  for (k=x[1],i=2; i<l; k=x[i++])
    if (x[i] == k) return i;
  return 0;
}

long
vecsmall_duplicate(GEN x)
{
  pari_sp av=avma;
  GEN p=vecsmall_indexsort(x);
  long k,i,r=0,l=lg(x);
  if (l==1) return 0;
  for (k=x[p[1]],i=2; i<l; k=x[p[i++]])
    if (x[p[i]] == k) { r=p[i]; break; }
  avma=av;
  return r;
}

/*************************************************************************/
/**                                                                     **/
/**             Routines for handling vectors of VECSMALL               **/
/**                                                                     **/
/*************************************************************************/

GEN
vecvecsmall_sort(GEN x)
{
  return gen_sort(x, (void*)&vecsmall_lexcmp, cmp_nodata);
}

GEN
vecvecsmall_sort_uniq(GEN x)
{
  return gen_sort_uniq(x, (void*)&vecsmall_lexcmp, cmp_nodata);
}

GEN
vecvecsmall_indexsort(GEN x)
{
  return gen_indexsort(x, (void*)&vecsmall_lexcmp, cmp_nodata);
}

long
vecvecsmall_search(GEN x, GEN y, long flag)
{
  return gen_search(x,y,flag,(void*)vecsmall_prefixcmp, cmp_nodata);
}

/* assume x non empty */
long
vecvecsmall_max(GEN x)
{
  long i, l = lg(x), m = vecsmall_max(gel(x,1));
  for (i = 2; i < l; i++)
  {
    long t = vecsmall_max(gel(x,i));
    if (t > m) m = t;
  }
  return m;
}

/*************************************************************************/
/**                                                                     **/
/**                  Routines for handling permutations                 **/
/**                                                                     **/
/*************************************************************************/

/* Permutations may be given by
 * perm (VECSMALL): a bijection from 1...n to 1...n i-->perm[i]
 * cyc (VEC of VECSMALL): a product of disjoint cycles. */

/* Multiply (compose) two permutations, putting the result in the second one. */
static void
perm_mul_inplace2(GEN s, GEN t)
{
  long i, l = lg(s);
  for (i = 1; i < l; i++) t[i] = s[t[i]];
}

/* Orbits of the subgroup generated by v on {1,..,n} */
static GEN
vecperm_orbits_i(GEN v, long n)
{
  long mj = 1, lv = lg(v), k, l;
  GEN cycle = cgetg(n+1, t_VEC), bit = const_vecsmall(n, 0);
  for (k = 1, l = 1; k <= n;)
  {
    long m = 1;
    GEN cy = cgetg(n+1, t_VECSMALL);
    for (  ; bit[mj]; mj++) /*empty*/;
    k++; cy[m++] = mj;
    bit[mj++] = 1;
    for(;;)
    {
      long o, mold = m;
      for (o = 1; o < lv; o++)
      {
        GEN vo = gel(v,o);
        long p;
        for (p = 1; p < m; p++) /* m increases! */
        {
          long j = vo[ cy[p] ];
          if (!bit[j]) cy[m++] = j;
          bit[j] = 1;
        }
      }
      if (m == mold) break;
      k += m - mold;
    }
    setlg(cy, m); gel(cycle,l++) = cy;
  }
  setlg(cycle, l); return cycle;
}
/* memory clean version */
GEN
vecperm_orbits(GEN v, long n)
{
  pari_sp av = avma;
  return gerepilecopy(av, vecperm_orbits_i(v, n));
}

/* Compute the cyclic decomposition of a permutation */
GEN
perm_cycles(GEN v)
{
  pari_sp av = avma;
  return gerepilecopy(av, vecperm_orbits_i(mkvec(v), lg(v)-1));
}

static long
isperm(GEN v)
{
  pari_sp av = avma;
  long i, n = lg(v)-1;
  GEN w;
  if (typ(v) != t_VECSMALL) return 0;
  w = zero_zv(n);
  for (i=1; i<=n; i++)
  {
    long d = v[i];
    if (d < 1 || d > n || w[d]) { avma = av; return 0; }
    w[d] = 1;
  }
  avma = av; return 1;
}

/* Output the order of p */
long
perm_order(GEN v)
{
  pari_sp ltop = avma;
  GEN c = vecperm_orbits_i(mkvec(v), lg(v)-1);
  long i, d;
  for(i=1, d=1; i<lg(c); i++) d = ulcm(d, lg(gel(c,i))-1);
  avma = ltop; return d;
}

long
permorder(GEN v)
{
  if (!isperm(v)) pari_err_TYPE("permorder",v);
  return perm_order(v);
}

/* sign of a permutation */
long
perm_sign(GEN v)
{
  pari_sp av = avma;
  GEN c = vecperm_orbits_i(mkvec(v), lg(v)-1);
  long i, l = lg(c), s = 1;
  for (i = 1; i < l; i++)
    if (odd(lg(gel(c, i)))) s = -s;
  avma = av; return s;
}

long
permsign(GEN v)
{
  if (!isperm(v)) pari_err_TYPE("permsign",v);
  return perm_sign(v);
}

GEN
Z_to_perm(long n, GEN x)
{
  pari_sp av;
  ulong i, r;
  GEN v = cgetg(n+1, t_VECSMALL);
  if (n==0) return v;
  uel(v,n) = 1; av = avma;
  if (signe(x) <= 0) x = modii(x, mpfact(n));
  for (r=n-1; r>=1; r--)
  {
    ulong a;
    x = absdiviu_rem(x, n+1-r, &a);
    for (i=r+1; i<=(ulong)n; i++)
      if (uel(v,i) > a) uel(v,i)++;
    uel(v,r) = a+1;
  }
  avma = av; return v;
}
GEN
numtoperm(long n, GEN x)
{
  if (n < 0) pari_err_DOMAIN("numtoperm", "n", "<", gen_0, stoi(n));
  if (typ(x) != t_INT) pari_err_TYPE("numtoperm",x);
  return Z_to_perm(n, x);
}

/* destroys v */
static GEN
perm_to_Z_inplace(GEN v)
{
  long l = lg(v), i, r;
  GEN x = gen_0;
  if (!isperm(v)) pari_err_TYPE("permsign",v);
  for (i = 1; i < l; i++)
  {
    long vi = v[i];
    if (vi <= 0) return NULL;
    x = i==1 ? utoi(vi-1): addiu(muliu(x,l-i), vi-1);
    for (r = i+1; r < l; r++)
      if (v[r] > vi) v[r]--;
  }
  return x;
}
GEN
perm_to_Z(GEN v)
{
  pari_sp av = avma;
  GEN x = perm_to_Z_inplace(leafcopy(v));
  if (!x) pari_err_TYPE("permtonum",v);
  return gerepileuptoint(av, x);
}
GEN
permtonum(GEN p)
{
  pari_sp av = avma;
  GEN v, x;
  switch(typ(p))
  {
    case t_VECSMALL: return perm_to_Z(p);
    case t_VEC: case t_COL:
      if (RgV_is_ZV(p)) { v = ZV_to_zv(p); break; }
    default: pari_err_TYPE("permtonum",p); return NULL;
  }
  x = perm_to_Z_inplace(v);
  if (!x) pari_err_TYPE("permtonum",p);
  return gerepileuptoint(av, x);
}


GEN
cyc_pow(GEN cyc, long exp)
{
  long i, j, k, l, r;
  GEN c;
  for (r = j = 1; j < lg(cyc); j++)
  {
    long n = lg(gel(cyc,j)) - 1;
    r += cgcd(n, exp);
  }
  c = cgetg(r, t_VEC);
  for (r = j = 1; j < lg(cyc); j++)
  {
    GEN v = gel(cyc,j);
    long n = lg(v) - 1, e = smodss(exp,n), g = (long)ugcd(n, e), m = n / g;
    for (i = 0; i < g; i++)
    {
      GEN p = cgetg(m+1, t_VECSMALL);
      gel(c,r++) = p;
      for (k = 1, l = i; k <= m; k++)
      {
        p[k] = v[l+1];
        l += e; if (l >= n) l -= n;
      }
    }
  }
  return c;
}

/* Compute the power of a permutation given by product of cycles
 * Ouput a perm, not a cyc */
GEN
cyc_pow_perm(GEN cyc, long exp)
{
  long e, j, k, l, n;
  GEN p;
  for (n = 0, j = 1; j < lg(cyc); j++) n += lg(gel(cyc,j))-1;
  p = cgetg(n + 1, t_VECSMALL);
  for (j = 1; j < lg(cyc); j++)
  {
    GEN v = gel(cyc,j);
    n = lg(v) - 1; e = smodss(exp, n);
    for (k = 1, l = e; k <= n; k++)
    {
      p[v[k]] = v[l+1];
      if (++l == n) l = 0;
    }
  }
  return p;
}

GEN
perm_pow(GEN perm, long exp)
{
  long i, r = lg(perm)-1;
  GEN p = zero_zv(r);
  pari_sp av = avma;
  GEN v = cgetg(r+1, t_VECSMALL);
  for (i=1; i<=r; i++)
  {
    long e, n, k, l;
    if (p[i]) continue;
    v[1] = i;
    for (n=1, k=perm[i]; k!=i; k=perm[k], n++)
      v[n+1] = k;
    e = smodss(exp, n);
    for (k = 1, l = e; k <= n; k++)
    {
      p[v[k]] = v[l+1];
      if (++l == n) l = 0;
    }
  }
  avma = av; return p;
}

static GEN
perm_to_GAP(GEN p)
{
  pari_sp ltop=avma;
  GEN gap;
  GEN x;
  long i;
  long nb, c=0;
  char *s;
  long sz;
  long lp=lg(p)-1;
  if (typ(p) != t_VECSMALL)  pari_err_TYPE("perm_to_GAP",p);
  x = perm_cycles(p);
  sz = (long) ((bfffo(lp)+1) * LOG10_2 + 1);
  /*Dry run*/
  for (i = 1, nb = 1; i < lg(x); ++i)
  {
    GEN z = gel(x,i);
    long lz = lg(z)-1;
    nb += 1+lz*(sz+2);
  }
  nb++;
  /*Real run*/
  gap = cgetg(nchar2nlong(nb) + 1, t_STR);
  s = GSTR(gap);
  for (i = 1; i < lg(x); ++i)
  {
    long j;
    GEN z = gel(x,i);
    if (lg(z) > 2)
    {
      s[c++] = '(';
      for (j = 1; j < lg(z); ++j)
      {
        if (j > 1)
        {
          s[c++] = ','; s[c++] = ' ';
        }
        sprintf(s+c,"%ld",z[j]);
        while(s[c++]) /* empty */;
        c--;
      }
      s[c++] = ')';
    }
  }
  if (!c) { s[c++]='('; s[c++]=')'; }
  s[c] = '\0';
  return gerepileupto(ltop,gap);
}

int
perm_commute(GEN s, GEN t)
{
  long i, l = lg(t);
  for (i = 1; i < l; i++)
    if (t[ s[i] ] != s[ t[i] ]) return 0;
  return 1;
}

/*************************************************************************/
/**                                                                     **/
/**                  Routines for handling groups                       **/
/**                                                                     **/
/*************************************************************************/
/* A Group is a t_VEC [gen,orders]
 * gen (vecvecsmall): list of generators given by permutations
 * orders (vecsmall): relatives orders of generators. */
INLINE GEN grp_get_gen(GEN G) { return gel(G,1); }
INLINE GEN grp_get_ord(GEN G) { return gel(G,2); }

/* A Quotient Group is a t_VEC [gen,coset]
 * gen (vecvecsmall): coset generators
 * coset (vecsmall): gen[coset[p[1]]] generate the p-coset.
 */
INLINE GEN quo_get_gen(GEN C) { return gel(C,1); }
INLINE GEN quo_get_coset(GEN C) { return gel(C,2); }

static GEN
trivialsubgroups(void)
{ GEN L = cgetg(2, t_VEC); gel(L,1) = trivialgroup(); return L; }

/* Compute the order of p modulo the group given by a set */
long
perm_relorder(GEN p, GEN set)
{
  pari_sp ltop = avma;
  long n = 1;
  long q = p[1];
  while (!F2v_coeff(set,q)) { q = p[q]; n++; }
  avma = ltop; return n;
}

GEN
perm_generate(GEN S, GEN H, long o)
{
  long i, n = lg(H)-1;
  GEN L = cgetg(n*o + 1, t_VEC);
  for(i=1; i<=n;     i++) gel(L,i) = vecsmall_copy(gel(H,i));
  for(   ; i <= n*o; i++) gel(L,i) = perm_mul(gel(L,i-n), S);
  return L;
}

/*Return the order (cardinality) of a group */
long
group_order(GEN G)
{
  return zv_prod(grp_get_ord(G));
}

/* G being a subgroup of S_n, output n */
long
group_domain(GEN G)
{
  GEN gen = grp_get_gen(G);
  if (lg(gen) < 2) pari_err_DOMAIN("group_domain", "#G", "=", gen_1,G);
  return lg(gel(gen,1)) - 1;
}

/*Left coset of g mod G: gG*/
GEN
group_leftcoset(GEN G, GEN g)
{
  GEN gen = grp_get_gen(G), ord = grp_get_ord(G);
  GEN res = cgetg(group_order(G)+1, t_VEC);
  long i, j, k;
  gel(res,1) = vecsmall_copy(g);
  k = 1;
  for (i = 1; i < lg(gen); i++)
  {
    long c = k * (ord[i] - 1);
    for (j = 1; j <= c; j++) gel(res,++k) = perm_mul(gel(res,j), gel(gen,i));
  }
  return res;
}
/*Right coset of g mod G: Gg*/
GEN
group_rightcoset(GEN G, GEN g)
{
  GEN gen = grp_get_gen(G), ord = grp_get_ord(G);
  GEN res = cgetg(group_order(G)+1, t_VEC);
  long i, j, k;
  gel(res,1) = vecsmall_copy(g);
  k = 1;
  for (i = 1; i < lg(gen); i++)
  {
    long c = k * (ord[i] - 1);
    for (j = 1; j <= c; j++) gel(res,++k) = perm_mul(gel(gen,i), gel(res,j));
  }
  return res;
}
/*Elements of a group from the generators, cf group_leftcoset*/
GEN
group_elts(GEN G, long n)
{
  GEN gen = grp_get_gen(G), ord = grp_get_ord(G);
  GEN res = cgetg(group_order(G)+1, t_VEC);
  long i, j, k;
  gel(res,1) = identity_perm(n);
  k = 1;
  for (i = 1; i < lg(gen); i++)
  {
    long c = k * (ord[i] - 1);
    /* j = 1, use res[1] = identity */
    gel(res,++k) = vecsmall_copy(gel(gen,i));
    for (j = 2; j <= c; j++) gel(res,++k) = perm_mul(gel(res,j), gel(gen,i));
  }
  return res;
}

GEN
groupelts_set(GEN elts, long n)
{
  GEN res = zero_F2v(n);
  long i, l = lg(elts);
  for(i=1; i<l; i++)
    F2v_set(res,mael(elts,i,1));
  return res;
}

/*Elements of a group from the generators, returned as a set (bitmap)*/
GEN
group_set(GEN G, long n)
{
  GEN res = zero_F2v(n);
  pari_sp av = avma;
  GEN elts = group_elts(G, n);
  long i, l = lg(elts);
  for(i=1; i<l; i++)
    F2v_set(res,mael(elts,i,1));
  avma = av;
  return res;
}

static int
sgcmp(GEN a, GEN b) { return vecsmall_lexcmp(gel(a,1),gel(b,1)); }

GEN
subgroups_tableset(GEN S, long n)
{
  long i, l = lg(S);
  GEN  v = cgetg(l, t_VEC);
  for(i=1; i<l; i++)
    gel(v,i) = mkvec2(group_set(gel(S,i), n), mkvecsmall(i));
  gen_sort_inplace(v,(void*)sgcmp,cmp_nodata, NULL);
  return v;
}

long
tableset_find_index(GEN tbl, GEN set)
{
  long i = tablesearch(tbl,mkvec2(set,mkvecsmall(0)),sgcmp);
  if (!i) return 0;
  return mael3(tbl,i,2,1);
}

GEN
trivialgroup(void) { retmkvec2(cgetg(1,t_VEC), cgetg(1,t_VECSMALL)); }
/*Cyclic group generated by g of order s*/
GEN
cyclicgroup(GEN g, long s)
{ retmkvec2(mkvec( vecsmall_copy(g) ),
            mkvecsmall(s)); }
/*Return the group generated by g1,g2 of relative orders s1,s2*/
GEN
dicyclicgroup(GEN g1, GEN g2, long s1, long s2)
{ retmkvec2( mkvec2(vecsmall_copy(g1), vecsmall_copy(g2)),
             mkvecsmall2(s1, s2) ); }

/* return the quotient map G --> G/H */
/*The ouput is [gen,hash]*/
/* gen (vecvecsmall): coset generators
 * coset (vecsmall): vecsmall of coset number) */
GEN
group_quotient(GEN G, GEN H)
{
  pari_sp ltop = avma;
  GEN  p2, p3;
  long i, j, a = 1;
  long n = group_domain(G), o = group_order(H);
  GEN  elt = group_elts(G,n), el;
  long le = lg(elt)-1;
  GEN used = zero_F2v(le+1);
  long l = le/o;
  p2 = cgetg(l+1, t_VEC);
  p3 = zero_zv(n);
  el = zero_zv(n);
  for (i = 1; i<=le; i++)
    el[mael(elt,i,1)]=i;
  for (i = 1; i <= l; ++i)
  {
    GEN V;
    while(F2v_coeff(used,a)) a++;
    V = group_leftcoset(H,gel(elt,a));
    gel(p2,i) = gel(V,1);
    for(j=1;j<lg(V);j++)
    {
      long b = el[mael(V,j,1)];
      if (b==0) pari_err_IMPL("group_quotient for a non-WSS group");
      F2v_set(used,b);
    }
    for (j = 1; j <= o; j++)
      p3[mael(V, j, 1)] = i;
  }
  return gerepilecopy(ltop,mkvec2(p2,p3));
}

/*Compute the image of a permutation by a quotient map.*/
GEN
quotient_perm(GEN C, GEN p)
{
  GEN gen = quo_get_gen(C);
  GEN coset = quo_get_coset(C);
  long j, l = lg(gen);
  GEN p3 = cgetg(l, t_VECSMALL);
  for (j = 1; j < l; ++j)
  {
    p3[j] = coset[p[mael(gen,j,1)]];
    if (p3[j]==0) pari_err_IMPL("quotient_perm for a non-WSS group");
  }
  return p3;
}

/* H is a subgroup of G, C is the quotient map G --> G/H
 *
 * Lift a subgroup S of G/H to a subgroup of G containing H */
GEN
quotient_subgroup_lift(GEN C, GEN H, GEN S)
{
  GEN genH = grp_get_gen(H);
  GEN genS = grp_get_gen(S);
  GEN genC = quo_get_gen(C);
  long l1 = lg(genH)-1;
  long l2 = lg(genS)-1, j;
  GEN p1 = cgetg(3, t_VEC), L = cgetg(l1+l2+1, t_VEC);
  for (j = 1; j <= l1; ++j) gel(L,j) = gel(genH,j);
  for (j = 1; j <= l2; ++j) gel(L,l1+j) = gel(genC, mael(genS,j,1));
  gel(p1,1) = L;
  gel(p1,2) = vecsmall_concat(grp_get_ord(H), grp_get_ord(S));
  return p1;
}

/* Let G a group and C a quotient map G --> G/H
 * Assume H is normal, return the group G/H */
GEN
quotient_group(GEN C, GEN G)
{
  pari_sp ltop = avma;
  GEN Qgen, Qord, Qelt, Qset, Q;
  GEN Cgen = quo_get_gen(C);
  GEN Ggen = grp_get_gen(G);
  long i,j, n = lg(Cgen)-1, l = lg(Ggen);
  Qord = cgetg(l, t_VECSMALL);
  Qgen = cgetg(l, t_VEC);
  Qelt = mkvec(identity_perm(n));
  Qset = groupelts_set(Qelt, n);
  for (i = 1, j = 1; i < l; ++i)
  {
    GEN  g = quotient_perm(C, gel(Ggen,i));
    long o = perm_relorder(g, Qset);
    gel(Qgen,j) = g;
    Qord[j] = o;
    if (o != 1)
    {
      Qelt = perm_generate(g, Qelt, o);
      Qset = groupelts_set(Qelt, n);
      j++;
    }
  }
  setlg(Qgen,j);
  setlg(Qord,j); Q = mkvec2(Qgen, Qord);
  return gerepilecopy(ltop,Q);
}

/* Return 1 if g normalizes N, 0 otherwise */
long
group_perm_normalize(GEN N, GEN g)
{
  pari_sp ltop = avma;
  long r = gequal(vecvecsmall_sort(group_leftcoset(N, g)),
                  vecvecsmall_sort(group_rightcoset(N, g)));
  avma = ltop; return r;
}

/* L is a list of subgroups, C is a coset and r a relative order.*/
static GEN
liftlistsubgroups(GEN L, GEN C, long r)
{
  pari_sp ltop = avma;
  long c = lg(C)-1, l = lg(L)-1, n = lg(gel(C,1))-1, i, k;
  GEN R;
  if (!l) return cgetg(1,t_VEC);
  R = cgetg(l*c+1, t_VEC);
  for (i = 1, k = 1; i <= l; ++i)
  {
    GEN S = gel(L,i), Selt = group_set(S,n);
    GEN gen = grp_get_gen(S);
    GEN ord = grp_get_ord(S);
    long j;
    for (j = 1; j <= c; ++j)
    {
      GEN p = gel(C,j);
      if (perm_relorder(p, Selt) == r && group_perm_normalize(S, p))
        gel(R,k++) = mkvec2(vec_append(gen, p),
                            vecsmall_append(ord, r));
    }
  }
  setlg(R, k);
  return gerepilecopy(ltop, R);
}

/* H is a normal subgroup, C is the quotient map G -->G/H,
 * S is a subgroup of G/H, and G is embedded in Sym(l)
 * Return all the subgroups K of G such that
 * S= K mod H and K inter H={1} */
static GEN
liftsubgroup(GEN C, GEN H, GEN S)
{
  pari_sp ltop = avma;
  GEN V = trivialsubgroups();
  GEN Sgen = grp_get_gen(S);
  GEN Sord = grp_get_ord(S);
  GEN Cgen = quo_get_gen(C);
  long n = lg(Sgen), i;
  for (i = 1; i < n; ++i)
  { /*loop over generators of S*/
    GEN W = group_leftcoset(H, gel(Cgen, mael(Sgen, i, 1)));
    V = liftlistsubgroups(V, W, Sord[i]);
  }
  return gerepilecopy(ltop,V);
}

/* 1:A4 2:S4 0: other */
long
group_isA4S4(GEN G)
{
  GEN elt = grp_get_gen(G);
  GEN ord = grp_get_ord(G);
  long n = lg(ord);
  if (n != 4 && n != 5) return 0;
  if (ord[1]!=2 || ord[2]!=2 || ord[3]!=3) return 0;
  if (perm_commute(gel(elt,1),gel(elt,3))) return 0;
  if (n==4) return 1;
  if (ord[4]!=2) return 0;
  if (perm_commute(gel(elt,3),gel(elt,4))) return 0;
  return 2;
}
/* compute all the subgroups of a group G */
GEN
group_subgroups(GEN G)
{
  pari_sp ltop = avma;
  GEN p1, H, C, Q, M, sg1, sg2, sg3;
  GEN gen = grp_get_gen(G);
  GEN ord = grp_get_ord(G);
  long lM, i, j, n = lg(gen);
  if (n == 1) return trivialsubgroups();
  if (group_isA4S4(G))
  {
    GEN s = gel(gen,1);       /*s = (1,2)(3,4) */
    GEN t = gel(gen,2);       /*t = (1,3)(2,4) */
    GEN st = perm_mul(s, t); /*st = (1,4)(2,3) */
    H = dicyclicgroup(s, t, 2, 2);
    /* sg3 is the list of subgroups intersecting only partially with H*/
    sg3 = cgetg((n==4)?4: 10, t_VEC);
    gel(sg3,1) = cyclicgroup(s, 2);
    gel(sg3,2) = cyclicgroup(t, 2);
    gel(sg3,3) = cyclicgroup(st, 2);
    if (n==5)
    {
      GEN u = gel(gen,3);
      GEN v = gel(gen,4), w, u2;
      if (zv_equal(perm_conj(u,s), t)) /*u=(2,3,4)*/
        u2 = perm_mul(u,u);
      else
      {
        u2 = u;
        u = perm_mul(u,u);
      }
      if (perm_order(v)==2)
      {
        if (!perm_commute(s,v)) /*v=(1,2)*/
        {
          v = perm_conj(u,v);
          if (!perm_commute(s,v)) v = perm_conj(u,v);
        }
        w = perm_mul(v,t); /*w=(1,4,2,3)*/
      }
      else
      {
        w = v;
        if (!zv_equal(perm_mul(w,w), s)) /*w=(1,4,2,3)*/
        {
          w = perm_conj(u,w);
          if (!zv_equal(perm_mul(w,w), s)) w = perm_conj(u,w);
        }
        v = perm_mul(w,t); /*v=(1,2)*/
      }
      gel(sg3,4) = dicyclicgroup(s,v,2,2);
      gel(sg3,5) = dicyclicgroup(t,perm_conj(u,v),2,2);
      gel(sg3,6) = dicyclicgroup(st,perm_conj(u2,v),2,2);
      gel(sg3,7) = dicyclicgroup(s,w,2,2);
      gel(sg3,8) = dicyclicgroup(t,perm_conj(u,w),2,2);
      gel(sg3,9) = dicyclicgroup(st,perm_conj(u2,w),2,2);
    }
  }
  else
  {
    long osig = mael(factoru(ord[1]), 1, 1);
    GEN sig = perm_pow(gel(gen,1), ord[1]/osig);
    H = cyclicgroup(sig,osig);
    sg3 = NULL;
  }
  C = group_quotient(G,H);
  Q = quotient_group(C,G);
  M = group_subgroups(Q); lM = lg(M);
  /* sg1 is the list of subgroups containing H*/
  sg1 = cgetg(lM, t_VEC);
  for (i = 1; i < lM; ++i) gel(sg1,i) = quotient_subgroup_lift(C,H,gel(M,i));
  /*sg2 is a list of lists of subgroups not intersecting with H*/
  sg2 = cgetg(lM, t_VEC);
  /* Loop over all subgroups of G/H */
  for (j = 1; j < lM; ++j) gel(sg2,j) = liftsubgroup(C, H, gel(M,j));
  p1 = gconcat(sg1, shallowconcat1(sg2));
  if (sg3)
  {
    p1 = gconcat(p1, sg3);
    if (n==5) /*ensure that the D4 subgroups of S4 are in supersolvable format*/
      for(j = 3; j <= 5; j++)
      {
        GEN c = gmael(p1,j,1);
        if (!perm_commute(gel(c,1),gel(c,3)))
        {
          if (perm_commute(gel(c,2),gel(c,3))) { swap(gel(c,1), gel(c,2)); }
          else
            perm_mul_inplace2(gel(c,2), gel(c,1));
        }
      }
  }
  return gerepileupto(ltop,p1);
}

/*return 1 if G is abelian, else 0*/
long
group_isabelian(GEN G)
{
  GEN g = grp_get_gen(G);
  long i, j, n = lg(g);
  for(i=2; i<n; i++)
    for(j=1; j<i; j++)
      if (!perm_commute(gel(g,i), gel(g,j))) return 0;
  return 1;
}

/*If G is abelian, return its HNF matrix*/
GEN
group_abelianHNF(GEN G, GEN S)
{
  GEN M, g = grp_get_gen(G), o = grp_get_ord(G);
  long i, j, k, n = lg(g);
  if (!group_isabelian(G)) return NULL;
  if (n==1) return cgetg(1,t_MAT);
  if (!S) S = group_elts(G, group_domain(G));
  M = cgetg(n,t_MAT);
  for(i=1; i<n; i++)
  {
    GEN P, C = cgetg(n,t_COL);
    pari_sp av = avma;
    gel(M,i) = C;
    P = perm_pow(gel(g,i), o[i]);
    for(j=1; j<lg(S); j++)
      if (zv_equal(P, gel(S,j))) break;
    avma = av;
    if (j==lg(S)) pari_err_BUG("galoisisabelian [inconsistent group]");
    j--;
    for(k=1; k<i; k++)
    {
      long q = j / o[k];
      gel(C,k) = stoi(j - q*o[k]);
      j = q;
    }
    gel(C,k) = stoi(o[i]);
    for (k++; k<n; k++) gel(C,k) = gen_0;
  }
  return M;
}

/*If G is abelian, return its abstract SNF matrix*/
GEN
group_abelianSNF(GEN G, GEN L)
{
  pari_sp ltop = avma;
  GEN H = group_abelianHNF(G,L);
  if (!H) return NULL;
  return gerepileupto(ltop, smithclean( ZM_snf(H) ));
}

GEN
abelian_group(GEN v)
{
  long card = zv_prod(v), i, d = 1, l = lg(v);
  GEN G = cgetg(3,t_VEC), gen = cgetg(l,t_VEC);
  gel(G,1) = gen;
  gel(G,2) = vecsmall_copy(v);
  for(i=1; i<l; i++)
  {
    GEN p = cgetg(card+1, t_VECSMALL);
    long o = v[i], u = d*(o-1), j, k, l;
    gel(gen, i) = p;
    /* The following loop is over-optimized. Remember that I wrote it for
     * testpermutation. Something has survived... BA */
    for(j=1;j<=card;)
    {
      for(k=1;k<o;k++)
        for(l=1;l<=d; l++,j++) p[j] = j+d;
      for (l=1; l<=d; l++,j++) p[j] = j-u;
    }
    d += u;
  }
  return G;
}

/*return 1 if H is a normal subgroup of G*/
long
group_subgroup_isnormal(GEN G, GEN H)
{
  GEN g = grp_get_gen(G);
  long i, n = lg(g);
  if (lg(grp_get_gen(H)) > 1 && group_domain(G) != group_domain(H))
    pari_err_DOMAIN("group_subgroup_isnormal","domain(H)","!=",
                    strtoGENstr("domain(G)"), H);
  for(i=1; i<n; i++)
    if (!group_perm_normalize(H, gel(g,i))) return 0;
  return 1;
}

long
groupelts_exponent(GEN elts)
{
  long i, n = lg(elts)-1, expo = 1;
  for(i=1; i<=n; i++) expo = ulcm(expo, perm_order(gel(elts,i)));
  return expo;
}

GEN
groupelts_center(GEN S)
{
  pari_sp ltop = avma;
  long i, j, n = lg(S)-1, l = n;
  GEN V, elts = zero_F2v(n+1);
  for(i=1; i<=n; i++)
  {
    if (F2v_coeff(elts,i)) { l--;  continue; }
    for(j=1; j<=n; j++)
      if (!perm_commute(gel(S,i),gel(S,j)))
      {
        F2v_set(elts,i);
        F2v_set(elts,j); l--; break;
      }
  }
  V = cgetg(l+1,t_VEC);
  for (i=1, j=1; i<=n ;i++)
    if (!F2v_coeff(elts,i)) gel(V,j++) = vecsmall_copy(gel(S,i));
  return gerepileupto(ltop,V);
}

GEN
groupelts_conjclasses(GEN elts, long *pnbcl)
{
  long i, j, cl = 0, n = lg(elts)-1;
  GEN c = const_vecsmall(n,0);
  pari_sp av = avma;
  for (i=1; i<=n; i++)
  {
    GEN g = gel(elts,i);
    if (c[i]) continue;
    c[i] = ++cl;
    for(j=1; j<=n; j++)
      if (j != i)
      {
        GEN h = perm_conj(gel(elts,j), g);
        long i2 = gen_search(elts,h,0,(void*)&vecsmall_lexcmp,&cmp_nodata);
        c[i2] = cl;
        avma = av;
      }
  }
  if (pnbcl) *pnbcl = cl;
  return c;
}

GEN
conjclasses_repr(GEN conj, long nb)
{
  long i, l = lg(conj);
  GEN e = const_vecsmall(nb, 0);
  for(i=1; i<l; i++)
  {
    long ci = conj[i];
    if (!e[ci]) e[ci] = i;
  }
  return e;
}

/* elts of G sorted wrt vecsmall_lexcmp order: g in G is determined by g[1]
 * so sort by increasing g[1] */
static GEN
galois_elts_sorted(GEN gal)
{
  long i, l;
  GEN elts = gal_get_group(gal), v = cgetg_copy(elts, &l);
  for (i = 1; i < l; i++) { GEN g = gel(elts,i); gel(v, g[1]) = g; }
  return v;
}
GEN
group_to_cc(GEN G)
{
  GEN elts = checkgroupelts(G), z = cgetg(5,t_VEC);
  long n, flag = 1;
  if (typ(gel(G,1)) == t_POL)
    elts = galois_elts_sorted(G); /* galoisinit */
  else
  {
    long i, l = lg(elts);
    elts = gen_sort(elts,(void*)vecsmall_lexcmp,cmp_nodata); /* general case */
    for (i = 1; i < l; i++)
      if (gel(elts,i)[1] != i) { flag = 0; break; }
  }
  gel(z,1) = elts;
  gel(z,2) = groupelts_conjclasses(elts,&n);
  gel(z,3) = conjclasses_repr(gel(z,2),n);
  gel(z,4) = utoi(flag); return z;
}

/* S a list of generators */
GEN
groupelts_abelian_group(GEN S)
{
  pari_sp ltop = avma;
  GEN Qgen, Qord, Qelt;
  long i, j, n = lg(gel(S,1))-1, l = lg(S);
  Qord = cgetg(l, t_VECSMALL);
  Qgen = cgetg(l, t_VEC);
  Qelt = mkvec(identity_perm(n));
  for (i = 1, j = 1; i < l; ++i)
  {
    GEN  g = gel(S,i);
    long o = perm_relorder(g, groupelts_set(Qelt, n));
    gel(Qgen,j) = g;
    Qord[j] = o;
    if (o != 1) { Qelt = perm_generate(g, Qelt, o); j++; }
  }
  setlg(Qgen,j);
  setlg(Qord,j);
  return gerepilecopy(ltop, mkvec2(Qgen, Qord));
}

GEN
group_export_GAP(GEN G)
{
  pari_sp av = avma;
  GEN s, comma, g = grp_get_gen(G);
  long i, k, l = lg(g);
  if (l == 1) return strtoGENstr("Group(())");
  s = cgetg(2*l, t_VEC);
  comma = strtoGENstr(", ");
  gel(s,1) = strtoGENstr("Group(");
  for (i=1, k=2; i < l; ++i)
  {
    if (i > 1) gel(s,k++) = comma;
    gel(s,k++) = perm_to_GAP(gel(g,i));
  }
  gel(s,k++) = strtoGENstr(")");
  return gerepilecopy(av, shallowconcat1(s));
}

GEN
group_export_MAGMA(GEN G)
{
  pari_sp av = avma;
  GEN s, comma, g = grp_get_gen(G);
  long i, k, l = lg(g);
  if (l == 1) return strtoGENstr("PermutationGroup<1|>");
  s = cgetg(2*l, t_VEC);
  comma = strtoGENstr(", ");
  gel(s,1) = gsprintf("PermutationGroup<%ld|",group_domain(G));
  for (i=1, k=2; i < l; ++i)
  {
    if (i > 1) gel(s,k++) = comma;
    gel(s,k++) = GENtoGENstr( vecsmall_to_vec(gel(g,i)) );
  }
  gel(s,k++) = strtoGENstr(">");
  return gerepilecopy(av, shallowconcat1(s));
}

GEN
group_export(GEN G, long format)
{
  switch(format)
  {
  case 0: return group_export_GAP(G);
  case 1: return group_export_MAGMA(G);
  }
  pari_err_FLAG("galoisexport");
  return NULL; /*-Wall*/
}
