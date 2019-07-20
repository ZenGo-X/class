/* Copyright (C) 2011  The PARI group.

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

static int
cmp_G(void *E, GEN x, GEN y) { (void)E; return cmp_universal(x,y); }

/* a ZG is either a t_INT or a t_VEC of pairs [g,e] representing
 * \sum e_i [g_i], e_i in Z, g_i in G. */
GEN
ZG_normalize(GEN x)
{
  if (typ(x) == t_INT) return x;
  return sort_factor(shallowcopy(x), NULL, &cmp_G);
}
GEN
ZG_add(GEN x, GEN y)
{
  if (typ(x) == t_INT)
  {
    if (!signe(x)) return y;
    if (typ(y) == t_INT)
    {
      if (!signe(y)) return x;
      return addii(x,y);
    }
    x = to_famat_shallow(gen_1,x);
  }
  else if (typ(y) == t_INT)
  {
    if (!signe(y)) return x;
    y = to_famat_shallow(gen_1,y);
  }
  x = merge_factor(x, y, NULL, &cmp_G);
  if (lg(gel(x,1)) == 1) return gen_0;
  return x;
}
GEN
ZG_neg(GEN x)
{
  if (typ(x) == t_INT) return negi(x);
  return mkmat2(gel(x,1),ZC_neg(gel(x,2)));
}
GEN
ZG_sub(GEN x, GEN y) { return ZG_add(x, ZG_neg(y)); }

/* x * c.[1], x in Z[G] */
GEN
ZG_Z_mul(GEN x, GEN c)
{
  if (is_pm1(c)) return signe(c) > 0? x: ZG_neg(x);
  if (typ(x) == t_INT) return mulii(x,c);
  return mkmat2(gel(x,1), ZC_Z_mul(gel(x,2), c));
}

GEN
ZG_mul(GEN x, GEN y)
{
  pari_sp av;
  GEN z, XG, XE;
  long i, l;
  if (typ(x) == t_INT) return ZG_Z_mul(y, x);
  if (typ(y) == t_INT) return ZG_Z_mul(x, y);
  av = avma;
  XG = gel(x,1); XE = gel(x,2); l = lg(XG);
  z = ZG_Z_mul(G_ZG_mul(gel(XG,1), y), gel(XE,1));
  for (i = 2; i < l; i++)
  {
    z = ZG_add(z, ZG_Z_mul(G_ZG_mul(gel(XG,i), y), gel(XE,i)));
    if (gc_needed(av,3))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"ZG_mul, i = %ld/%ld",i,l-1);
      z = gerepilecopy(av, z);
    }
  }
  return z;
}
GEN
ZGCs_add(GEN x, GEN y)
{
  GEN xi = gel(x,1), xv = gel(x,2);
  GEN yi = gel(y,1), yv = gel(y,2);
  long i = 1, j = 1, k = 1, lx = lg(xi), ly = lg(yi), l = lx+ly-1;
  GEN zi = cgetg(l, t_VECSMALL), zv = cgetg(l, t_VEC);
  while (i < lx && j < ly)
  {
    if      (xi[i] < yi[j]) { zi[k] = xi[i]; gel(zv,k) = gel(xv,i); i++; }
    else if (xi[i] > yi[j]) { zi[k] = yi[j]; gel(zv,k) = gel(yv,j); j++; }
    else { zi[k] = xi[i]; gel(zv,k) = ZG_add(gel(xv,i),gel(yv,j)); i++; j++; }
    k++;
  }
  for(; i < lx; i++,k++) { zi[k] = xi[i]; gel(zv,k) = gel(xv,i); }
  for(; j < ly; j++,k++) { zi[k] = yi[j]; gel(zv,k) = gel(yv,j); }
  setlg(zi,k);
  setlg(zv,k); return mkvec2(zi, zv);
}
GEN
ZG_G_mul(GEN x, GEN y)
{
  long i, l;
  GEN z, X;
  if (typ(x) == t_INT) return signe(x)? to_famat_shallow(y, x): gen_0;
  X = gel(x,1);
  z = cgetg_copy(X, &l);
  for (i = 1; i < l; i++) gel(z,i) = gmul(gel(X,i), y);
  return ZG_normalize( mkmat2(z, gel(x,2)) );
}
GEN
G_ZG_mul(GEN x, GEN y)
{
  long i, l;
  GEN z, Y;
  if (typ(y) == t_INT) return to_famat_shallow(x, y);
  Y = gel(y,1);
  z = cgetg_copy(Y, &l);
  for (i = 1; i < l; i++) gel(z,i) = gmul(x, gel(Y,i));
  return ZG_normalize( mkmat2(z, gel(y,2)) );
}
void
ZGC_G_mul_inplace(GEN v, GEN x)
{
  long i, l = lg(v);
  for (i = 1; i < l; i++) gel(v,i) = ZG_G_mul(gel(v,i), x);
}
GEN
ZGC_G_mul(GEN v, GEN x)
{ pari_APPLY_same(ZG_G_mul(gel(v,i), x)); }
GEN
G_ZGC_mul(GEN x, GEN v)
{ pari_APPLY_same(G_ZG_mul(gel(v,i), x)); }
GEN
ZGC_Z_mul(GEN v, GEN x)
{ pari_APPLY_same(ZG_Z_mul(gel(v,i), x)); }
