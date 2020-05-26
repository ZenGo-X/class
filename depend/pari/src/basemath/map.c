/* Copyright (C) 2015  The PARI group.

This file is part of the PARI package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

#include "pari.h"
#include "paripriv.h"

#define tvalue(i)  gmael(t,(i),1)
#define tleft(i)   mael3(t,(i),2,1)
#define tright(i)  mael3(t,(i),2,2)
#define theight(i) mael3(t,(i),2,3)

static GEN
treesearch(GEN T, GEN x, long mode)
{
  long i = 1;
  GEN t = list_data(T);
  if (!t || lg(t)==1) return NULL;
  while(i)
  {
    long c = mode == 0 ? cmp_universal(x, tvalue(i)):
                         cmp_universal(x, gel(tvalue(i),1));
    if (c)
      i = c < 0 ? tleft(i): tright(i);
    else
      return tvalue(i);
  }
  return NULL;
}

static long
treeparent_r(GEN t, GEN x, long i, long mode, long parent)
{
  long c;
  if (i==0) return parent;
  c = mode == 0 ? cmp_universal(x, tvalue(i)):
                  cmp_universal(x, gel(tvalue(i),1));
  if (c < 0)
    return treeparent_r(t,x,tleft(i),mode,i);
  else if (c > 0)
    return treeparent_r(t,x,tright(i),mode,i);
  else
    return parent;
}

static long
treeparent(GEN T, GEN x, long mode)
{
  GEN t = list_data(T);
  return t ? treeparent_r(t, x, 1, mode, 0): 0;
}

static void
treekeys_r(GEN t, long i, GEN V, long *n, long mode)
{
  if (i==0) return;
  treekeys_r(t, tleft(i), V, n, mode);
  gel(V, ++*n) = gcopy(mode == 0 ? tvalue(i): gel(tvalue(i),1));
  treekeys_r(t, tright(i), V, n, mode);
}

static GEN
treekeys(GEN T, long mode)
{
  long n = 0;
  GEN t = list_data(T);
  GEN V;
  if (!t || lg(t)==1) return cgetg(1, t_VEC);
  V = cgetg(lg(t), t_VEC);
  treekeys_r(t, 1, V, &n, mode);
  return V;
}

static void
treekeys_i_r(GEN t, long i, GEN V, long *n, long mode)
{
  if (i==0) return;
  treekeys_i_r(t, tleft(i), V, n, mode);
  gel(V, ++*n) = mode == 0 ? tvalue(i): gel(tvalue(i),1);
  treekeys_r(t, tright(i), V, n, mode);
}

static GEN
treekeys_i(GEN T, long mode)
{
  long n = 0;
  GEN t = list_data(T);
  GEN V;
  if (!t || lg(t)==1) return cgetg(1, t_VEC);
  V = cgetg(lg(t), t_VEC);
  treekeys_i_r(t, 1, V, &n, mode);
  return V;
}

static void
treemat_r(GEN t, long i, GEN V, long *n)
{
  if (i==0) return;
  treemat_r(t, tleft(i), V, n);
  ++*n;
  gmael(V, 1, *n) = gcopy(gel(tvalue(i), 1));
  gmael(V, 2, *n) = gcopy(gel(tvalue(i), 2));
  treemat_r(t, tright(i), V, n);
}

static GEN
treemat(GEN T)
{
  long n = 0;
  GEN t = list_data(T);
  GEN V;
  if (!t || lg(t)==1) return cgetg(1, t_MAT);
  V = cgetg(3, t_MAT);
  gel(V,1) = cgetg(lg(t), t_COL);
  gel(V,2) = cgetg(lg(t), t_COL);
  treemat_r(t, 1, V, &n);
  return V;
}

static void
treemat_i_r(GEN t, long i, GEN V, long *n)
{
  if (i==0) return;
  treemat_i_r(t, tleft(i), V, n);
  ++*n;
  gmael(V, 1, *n) = gel(tvalue(i), 1);
  gmael(V, 2, *n) = gel(tvalue(i), 2);
  treemat_r(t, tright(i), V, n);
}

static GEN
treemat_i(GEN T)
{
  long n = 0;
  GEN t = list_data(T);
  GEN V;
  if (!t || lg(t)==1) return cgetg(1, t_MAT);
  V = cgetg(3, t_MAT);
  gel(V,1) = cgetg(lg(t), t_COL);
  gel(V,2) = cgetg(lg(t), t_COL);
  treemat_i_r(t, 1, V, &n);
  return V;
}

static void
treemap_i_r(GEN t, long i, long a, long c, GEN p, GEN M)
{
  long b = (a+c)>>1;
  GEN x = mkvec2(gcopy(gmael(M, 1, p[b])), gcopy(gmael(M, 2, p[b])));
  if (a == c)
    gel(t, i) = mkvec2(x, mkvecsmall3(0, 0, 1));
  else if (a+1 == c)
  {
    treemap_i_r(t, i+1, a+1, c, p, M);
    gel(t, i) = mkvec2(x, mkvecsmall3(0, i+1, theight(i+1) + 1));
  }
  else
  {
    long l = i+1, r = l + b - a, h;
    treemap_i_r(t, l, a, b-1, p, M);
    treemap_i_r(t, r, b+1, c, p, M);
    h = maxss(theight(l), theight(r))+1;
    gel(t, i) = mkvec2(x, mkvecsmall3(l, r, h));
  }
}

static void
treemap_i(GEN t, GEN p, GEN M)
{
  treemap_i_r(t, 1, 1, lg(p)-1, p, M);
}

#define value(i)  gmael(list_data(T),(i),1)
#define left(i)   mael3(list_data(T),(i),2,1)
#define right(i)  mael3(list_data(T),(i),2,2)
#define height(i) mael3(list_data(T),(i),2,3)

static long
treeheight(GEN T, long i)
{ return i? height(i): 0; }

static void
change_leaf(GEN T, GEN x, long p)
{
  pari_sp av = avma;
  listput(T, mkvec2(x, gmael(list_data(T), p, 2)), p);
  avma = av;
}

static long
new_leaf(GEN T, GEN x)
{
  pari_sp av = avma;
  listput(T, mkvec2(x, mkvecsmall3(0,0,1)), 0);
  avma = av;
  return lg(list_data(T))-1;
}

static void
fix_height(GEN T, long x)
{
  height(x) = maxss(treeheight(T,left(x)), treeheight(T,right(x)))+1;
}
static long
treebalance(GEN T, long i)
{
  return i ? treeheight(T,left(i)) - treeheight(T,right(i)): 0;
}

static long
rotright(GEN T, long y)
{
  long x = left(y);
  long t = right(x);
  right(x) = y;
  left(y)  = t;
  fix_height(T, y);
  fix_height(T, x);
  return x;
}

static long
rotleft(GEN T, long x)
{
  long y = right(x);
  long t = left(y);
  left(y)  = x;
  right(x) = t;
  fix_height(T, x);
  fix_height(T, y);
  return y;
}

static long
treeinsert_r(GEN T, GEN x, long i, long *d, long mode)
{
  long b, c;
  if (i==0 || !list_data(T) || lg(list_data(T))==1)
    return new_leaf(T, x);
  c = mode == 0 ? cmp_universal(x, value(i)):
                  cmp_universal(gel(x,1), gel(value(i),1));
  if (c < 0)
  {
    long s = treeinsert_r(T, x, left(i), d, mode);
    if (s < 0) return s;
    left(i) = s;
  }
  else if (c > 0)
  {
    long s = treeinsert_r(T, x, right(i), d, mode);
    if (s < 0) return s;
    right(i) = s;
  }
  else return -i;
  fix_height(T, i);
  b = treebalance(T, i);
  if (b > 1)
  {
    if (*d > 0)
      left(i) = rotleft(T, left(i));
    return rotright(T, i);
  }
  if (b < -1)
  {
    if (*d < 0)
      right(i) = rotright(T, right(i));
    return rotleft(T, i);
  }
  *d = c;
  return i;
}

static long
treeinsert(GEN T, GEN x, long mode)
{
  GEN d;
  long c = 0;
  long r = treeinsert_r(T, x, 1, &c, mode);
  if (r < 0) return -r;
  if (r == 1) return 0;
  d = list_data(T);
  /* By convention we want the root to be 1 */
  swap(gel(d,1), gel(d,r));
  if (left(1) == 1) left(1)=r;
  else if (right(1) == 1) right(1)=r;
  else pari_err_BUG("treeadd");
  return 0;
}

static long
treedelete_r(GEN T, GEN x, long i, long mode, long *dead)
{
  long b, c;
  if (i==0 || !list_data(T) || lg(list_data(T))==1)
    return -1;
  c = mode == 0 ? cmp_universal(x, value(i)):
                  cmp_universal(x, gel(value(i),1));
  if (c < 0)
  {
    long s = treedelete_r(T, x, left(i), mode, dead);
    if (s < 0) return s;
    left(i) = s;
  }
  else if (c > 0)
  {
    long s = treedelete_r(T, x, right(i), mode, dead);
    if (s < 0) return s;
    right(i) = s;
  }
  else
  {
    *dead = i;
    if (left(i)==0 && right(i)==0)
      return 0;
    else if (left(i)==0)
      return right(i);
    else if (right(i)==0)
      return left(i);
    else
    {
      GEN v;
      GEN d = list_data(T);
      long j = right(i);
      while (left(j)) j = left(j);
      v = mode == 0 ? value(j): gel(value(j), 1);
      right(i) = treedelete_r(T, v, right(i), mode, dead);
      swap(gel(d,i), gel(d,j));
      lswap(left(i),left(j));
      lswap(right(i),right(j));
      lswap(height(i),height(j));
    }
  }
  fix_height(T, i);
  b = treebalance(T, i);
  if (b > 1 && treebalance(T, left(i)) >= 0)
    return rotright(T, i);
  if (b > 1 && treebalance(T, left(i)) < 0)
  {
    left(i) = rotleft(T, left(i));
    return rotright(T, i);
  }
  if (b < -1 && treebalance(T, right(i)) <= 0)
    return rotleft(T,i);
  if (b < -1 && treebalance(T, right(i)) > 0)
  {
    right(i) = rotright(T, right(i));
    return rotleft(T, i);
  }
  return i;
}

static long
treedelete(GEN T, GEN x, long mode)
{
  GEN  d = list_data(T);
  long dead, l;
  long r = treedelete_r(T, x, 1, mode, &dead);
  if (r < 0) return 0;
  if (r > 1)
  {
    /* By convention we want the root to be 1 */
    swap(gel(d,1), gel(d,r));
    if (left(1) == 1) left(1) = r;
    else if (right(1) == 1) right(1) = r;
    else dead = r;
  }
  /* We want the dead to be last */
  l = lg(d)-1;
  if (dead != l)
  {
    long p = treeparent(T, gel(value(l), 1), mode);
    if (left(p) == l) left(p) = dead;
    else if (right(p) == l) right(p) = dead;
    else pari_err_BUG("treedelete2");
    swap(gel(d, dead),gel(d, l));
  }
  listpop(T, 0);
  return 1;
}

void
mapput(GEN T, GEN a, GEN b)
{
  pari_sp av = avma;
  long i;
  GEN p;
  if (typ(T)!=t_LIST || list_typ(T)!=t_LIST_MAP)
    pari_err_TYPE("mapput",T);
  p = mkvec2(a, b);
  i = treeinsert(T, p, 1);
  if (i) change_leaf(T, p, i);
  avma = av;
}

void
mapdelete(GEN T, GEN a)
{
  pari_sp av = avma;
  long s;
  if (typ(T)!=t_LIST || list_typ(T)!=t_LIST_MAP)
    pari_err_TYPE("mapdelete",T);
  s = treedelete(T, a, 1);
  if (!s) pari_err_COMPONENT("mapdelete", "not in", strtoGENstr("map"), a);
  avma = av;
}

GEN
mapget(GEN T, GEN a)
{
  GEN x;
  if (typ(T)!=t_LIST || list_typ(T)!=t_LIST_MAP)
    pari_err_TYPE("mapget",T);
  x = treesearch(T, a, 1);
  if (!x) pari_err_COMPONENT("mapget", "not in", strtoGENstr("map"), a);
  return gcopy(gel(x, 2));
}

int
mapisdefined(GEN T, GEN a, GEN *pt_z)
{
  GEN x;
  if (typ(T)!=t_LIST || list_typ(T)!=t_LIST_MAP)
    pari_err_TYPE("mapisdefined",T);
  x = treesearch(T, a, 1);
  if (!x) return 0;
  if (pt_z) *pt_z = gcopy(gel(x, 2));
  return 1;
}

GEN
mapdomain(GEN T)
{
  if (typ(T)!=t_LIST || list_typ(T)!=t_LIST_MAP)
    pari_err_TYPE("mapdomain",T);
  return treekeys(T,1);
}

GEN
mapdomain_shallow(GEN T)
{
  if (typ(T)!=t_LIST || list_typ(T)!=t_LIST_MAP)
    pari_err_TYPE("mapdomain_shallow",T);
  return treekeys_i(T,1);
}

GEN
maptomat(GEN T)
{
  if (typ(T)!=t_LIST || list_typ(T)!=t_LIST_MAP)
    pari_err_TYPE("maptomat",T);
  return treemat(T);
}

GEN
maptomat_shallow(GEN T)
{
  if (typ(T)!=t_LIST || list_typ(T)!=t_LIST_MAP)
    pari_err_TYPE("maptomap_shallow",T);
  return treemat_i(T);
}

GEN
gtomap(GEN x)
{
  if (!x) return mkmap();
  switch(typ(x))
  {
  case t_MAT:
    {
      long n, l = lg(x);
      GEN M, p;
      if (l == 1 || lgcols(x)==1) return mkmap();
      if (l != 3) pari_err_TYPE("Map",x);
      p = gen_indexsort_uniq(gel(x,1),(void*)&cmp_universal, cmp_nodata);
      if (lg(p) != lgcols(x))
        pari_err_DOMAIN("Map","x","is not",strtoGENstr("one-to-one"),x);
      n = lg(p)-1;
      M = cgetg(3, t_LIST);
      M[1] = evaltyp(t_LIST_MAP)|evallg(n);
      list_data(M) = cgetg(n+1, t_VEC);
      treemap_i(list_data(M), p, x);
      return M;
    }
  default:
    pari_err_TYPE("Map",x);
  }
  return NULL; /* LCOV_EXCL_LINE */
}
