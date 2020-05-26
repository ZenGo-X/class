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
/*                          CONCATENATION                          */
/*                                                                 */
/*******************************************************************/
#include "pari.h"
#include "paripriv.h"

/* assume A or B is a t_LIST */
static GEN
listconcat(GEN A, GEN B)
{
  long i, l1, lx;
  GEN L, z, L1, L2;

  if (typ(A) != t_LIST) {
    if (list_typ(B)!=t_LIST_RAW) pari_err_TYPE("listconcat",B);
    L2 = list_data(B);
    if (!L2) return mklistcopy(A);
    lx = lg(L2) + 1;
    z = mklist();
    list_data(z) = L = cgetg(lx, t_VEC);
    for (i = 2; i < lx; i++) gel(L,i) = gcopy(gel(L2,i-1));
    gel(L,1) = gcopy(A); return z;
  } else if (typ(B) != t_LIST) {
    if (list_typ(A)!=t_LIST_RAW) pari_err_TYPE("listconcat",A);
    L1 = list_data(A);
    if (!L1) return mklistcopy(B);
    lx = lg(L1) + 1;
    z = mklist();
    list_data(z) = L = cgetg(lx, t_VEC);
    for (i = 1; i < lx-1; i++) gel(L,i) = gcopy(gel(L1,i));
    gel(L,i) = gcopy(B); return z;
  }
  /* A, B both t_LISTs */
  if (list_typ(A)!=t_LIST_RAW) pari_err_TYPE("listconcat",A);
  if (list_typ(B)!=t_LIST_RAW) pari_err_TYPE("listconcat",B);
  L1 = list_data(A); if (!L1) return listcopy(B);
  L2 = list_data(B); if (!L2) return listcopy(A);

  l1 = lg(L1);
  lx = l1-1 + lg(L2);
  z = cgetg(3, t_LIST);
  z[1] = 0UL;
  list_data(z) = L = cgetg(lx, t_VEC);
  L2 -= l1-1;
  for (i=1; i<l1; i++) gel(L,i) = gclone(gel(L1,i));
  for (   ; i<lx; i++) gel(L,i) = gclone(gel(L2,i));
  return z;
}

/* assume A or B is a t_STR */
static GEN
strconcat(GEN x, GEN y)
{
  size_t l, lx;
  char *sx = GENtostr_unquoted(x);
  char *sy = GENtostr_unquoted(y), *str;
  lx = strlen(sx);
  l = nchar2nlong(lx + strlen(sy) + 1);
  x = cgetg(l + 1, t_STR); str = GSTR(x);
  strcpy(str,   sx);
  strcpy(str+lx,sy); return x;
}

/* concat A and B vertically. Internal */
GEN
vconcat(GEN A, GEN B)
{
  long la, ha, hb, hc, i, j, T;
  GEN M, a, b, c;

  if (!A) return B;
  if (!B) return A;
  la = lg(A); if (la==1) return B;
  T = typ(gel(A,1)); /* t_COL or t_VECSMALL */
  ha = lgcols(A); M = cgetg(la,t_MAT);
  hb = lgcols(B); hc = ha+hb-1;
  for (j=1; j<la; j++)
  {
    c = cgetg(hc, T); gel(M, j) = c;
    a = gel(A,j);
    b = gel(B,j);
    for (i=1; i<ha; i++) *++c = *++a;
    for (i=1; i<hb; i++) *++c = *++b;
  }
  return M;
}

static void
err_cat(GEN x, GEN y) { pari_err_OP("concatenation",x,y); }

GEN
shallowconcat(GEN x, GEN y)
{
  long tx=typ(x),ty=typ(y),lx=lg(x),ly=lg(y),i;
  GEN z,p1;

  if (tx==t_STR  || ty==t_STR)  return strconcat(x,y);
  if (tx==t_LIST || ty==t_LIST) return listconcat(x,y);

  if (tx==t_MAT && lx==1)
  {
    if (ty!=t_VEC) return gtomat(y);
    if (ly==1) return cgetg(1, t_MAT);
    err_cat(x,y);
  }
  if (ty==t_MAT && ly==1)
  {
    if (tx!=t_VEC) return gtomat(x);
    if (lx==1) return cgetg(1, t_MAT);
    err_cat(x,y);
  }

  if (tx == ty)
  {
    if (tx == t_MAT)
    { if (lgcols(x) != lgcols(y)) err_cat(x,y); }
    else
      if (!is_matvec_t(tx) && tx != t_VECSMALL) return mkvec2(x, y);
    z=cgetg(lx+ly-1,tx);
    for (i=1; i<lx; i++) z[i]     = x[i];
    for (i=1; i<ly; i++) z[lx+i-1]= y[i];
    return z;
  }

  if (! is_matvec_t(tx))
  {
    if (! is_matvec_t(ty)) return mkvec2(x, y);
    z=cgetg(ly+1,ty);
    if (ty != t_MAT) p1 = x;
    else
    {
      if (lgcols(y)!=2) err_cat(x,y);
      p1 = mkcol(x);
    }
    for (i=2; i<=ly; i++) z[i] = y[i-1];
    gel(z, 1) = p1; return z;
  }
  if (! is_matvec_t(ty))
  {
    z=cgetg(lx+1,tx);
    if (tx != t_MAT) p1 = y;
    else
    {
      if (lgcols(x)!=2) err_cat(x,y);
      p1 = mkcol(y);
    }
    for (i=1; i<lx; i++) z[i]=x[i];
    gel(z, lx) = p1; return z;
  }

  switch(tx)
  {
    case t_VEC:
      switch(ty)
      {
        case t_COL:
          if (lx<=2) return (lx==1)? y: shallowconcat(gel(x,1),y);
          if (ly>=3) break;
          return (ly==1)? x: shallowconcat(x,gel(y,1));
        case t_MAT:
          z=cgetg(ly,t_MAT); if (lx != ly) break;
          for (i=1; i<ly; i++) gel(z,i) = shallowconcat(gel(x,i),gel(y,i));
          return z;
      }
      break;

    case t_COL:
      switch(ty)
      {
        case t_VEC:
          if (lx<=2) return (lx==1)? y: shallowconcat(gel(x,1), y);
          if (ly>=3) break;
          return (ly==1)? x: shallowconcat(x, gel(y,1));
        case t_MAT:
          if (lx != lgcols(y)) break;
          z=cgetg(ly+1,t_MAT);  gel(z,1) = x;
          for (i=2; i<=ly; i++) gel(z,i) = gel(y,i-1);
          return z;
      }
      break;

    case t_MAT:
      switch(ty)
      {
        case t_VEC:
          z=cgetg(lx, t_MAT); if (ly != lx) break;
          for (i=1; i<lx; i++) gel(z,i) = shallowconcat(gel(x,i), gel(y,i));
          return z;
        case t_COL:
          if (ly != lgcols(x)) break;
          z=cgetg(lx+1,t_MAT); gel(z,lx) = y;
          for (i=1; i<lx; i++) z[i]=x[i];
          return z;
      }
      break;
  }
  err_cat(x,y);
  return NULL; /* LCOV_EXCL_LINE */
}

/* see catmany() */
static GEN
catmanyMAT(GEN y1, GEN y2)
{
  long i, h = 0, L = 1;
  GEN z, y;
  for (y = y2; y >= y1; y--)
  {
    GEN c = gel(y,0);
    long nc = lg(c)-1;
    if (nc == 0) continue;
    if (h != lgcols(c))
    {
      if (h) err_cat(gel(y2,0), c);
      h = lgcols(c);
    }
    L += nc;
    z = new_chunk(nc) - 1;
    for (i=1; i<=nc; i++) gel(z,i) = gel(c,i);
  }
  z = new_chunk(1);
  *z = evaltyp(t_MAT) | evallg(L);
  return z;
}
static GEN
catmanySTR(GEN y1, GEN y2)
{
  long L = 1; /* final \0 */
  GEN z, y;
  char *s;
  for (y = y1; y <= y2; y++)
  {
    char *c = GSTR( gel(y,0) );
    L += strlen(c);
  }
  z = cgetg(nchar2nlong(L)+1, t_STR);
  s = GSTR(z);
  for (y = y1; y <= y2; y++)
  {
    char *c = GSTR( gel(y,0) );
    long nc = strlen(c);
    if (nc) { (void)memcpy(s, c, nc); s += nc; }
  }
  *s = 0; return z;
}

/* all entries in y have the same type t = t_VEC, COL, MAT or VECSMALL
 * concatenate y[k1..k2], with yi = y + ki, k1 <= k2 */
static GEN
catmany(GEN y1, GEN y2, long t)
{
  long i, L;
  GEN z, y;
  if (y1 == y2) return gel(y1,0);
  if (t == t_MAT) return catmanyMAT(y1, y2);
  if (t == t_STR) return catmanySTR(y1, y2);
  L = 1;
  for (y = y2; y >= y1; y--)
  {
    GEN c = gel(y,0);
    long nc = lg(c)-1;
    if (nc == 0) continue;
    L += nc;
    z = new_chunk(nc) - 1;
    for (i=1; i<=nc; i++) gel(z,i) = gel(c,i);
  }
  z = new_chunk(1);
  *z = evaltyp(t) | evallg(L);
  return z;
}

GEN
shallowconcat1(GEN x)
{
  pari_sp av = avma;
  long lx, t, i;
  GEN z;
  switch(typ(x))
  {
    case t_VEC:
      lx = lg(x);
      if (lx==1) pari_err_DOMAIN("concat","vector","=",x,x);
      break;
    case t_LIST:
      if (list_typ(x)!=t_LIST_RAW) pari_err_TYPE("concat",x);
      if (!list_data(x)) pari_err_DOMAIN("concat","vector","=",x,x);
      x = list_data(x); lx = lg(x);
      break;
    default:
      pari_err_TYPE("concat",x);
      return NULL; /* LCOV_EXCL_LINE */
  }
  if (lx==2) return gel(x,1);
  z = gel(x,1); t = typ(z); i = 2;
  if (is_matvec_t(t) || t == t_VECSMALL || t == t_STR)
  { /* detect a "homogeneous" object: catmany is faster */
    for (; i<lx; i++)
      if (typ(gel(x,i)) != t) break;
    z = catmany(x + 1, x + i-1, t);
  }
  for (; i<lx; i++) {
    z = shallowconcat(z, gel(x,i));
    if (gc_needed(av,3))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"concat: i = %ld", i);
      z = gerepilecopy(av, z);
    }
  }
  return z;
}

GEN
gconcat1(GEN x)
{
  pari_sp av = avma;
  return gerepilecopy(av, shallowconcat1(x));
}

/* fill M[xoff+i, yoff+j] with the contents of c ( c * Id_n if scalar ) */
static void
matfill(GEN M, GEN c, long xoff, long yoff, long n)
{
  long i, j, h, l;
  l = lg(c); if (l == 1) return;
  switch(typ(c))
  {
    case t_VEC:
      for (i = 1; i < l; i++)
        gcoeff(M,xoff+1,yoff+i) = gel(c,i);
      break;
    case t_COL:
      for (i = 1; i < l; i++)
        gcoeff(M,xoff+i,yoff+1) = gel(c,i);
      break;
    case t_MAT:
      h = lgcols(c);
      for (j = 1; j < l; j++)
        for (i = 1; i < h; i++) gcoeff(M,xoff+i,yoff+j) = gcoeff(c,i,j);
      break;
    default:
      for (i = 1; i <= n; i++)
        gcoeff(M, xoff+i, yoff+i) = c;
      break;
  }
}

static GEN
_matsize(GEN x)
{
  long t = typ(x), L = lg(x) - 1;
  switch(t)
  { /* matsize */
    case t_VEC: return mkvecsmall2(1, L);
    case t_COL: return mkvecsmall2(L, 1);
    case t_MAT: return mkvecsmall2(L? nbrows(x): 0, L);
    default:
      if (is_noncalc_t(t)) pari_err_TYPE("_matsize", x);
      return mkvecsmall2(1, 1);
  }
}

GEN
shallowmatconcat(GEN v)
{
  long i, j, h, l = lg(v), L = 0, H = 0;
  GEN M, maxh, maxl;
  if (l == 1) return cgetg(1,t_MAT);
  switch(typ(v))
  {
    case t_VEC:
      for (i = 1; i < l; i++)
      {
        GEN c = gel(v,i);
        GEN s = _matsize(c);
        H = maxss(H, s[1]);
        L += s[2];
      }
      M = zeromatcopy(H, L);
      L = 0;
      for (i = 1; i < l; i++)
      {
        GEN c = gel(v,i);
        GEN s = _matsize(c);
        matfill(M, c, 0, L, 1);
        L += s[2];
      }
      return M;

    case t_COL:
      for (i = 1; i < l; i++)
      {
        GEN c = gel(v,i);
        GEN s = _matsize(c);
        H += s[1];
        L = maxss(L, s[2]);
      }
      M = zeromatcopy(H, L);
      H = 0;
      for (i = 1; i < l; i++)
      {
        GEN c = gel(v,i);
        GEN s = _matsize(c);
        matfill(M, c, H, 0, 1);
        H += s[1];
      }
      return M;
    case t_MAT:
      h = lgcols(v);
      maxh = zero_zv(h-1);
      maxl = zero_zv(l-1);
      for (j = 1; j < l; j++)
        for (i = 1; i < h; i++)
        {
          GEN c = gcoeff(v,i,j);
          GEN s = _matsize(c);
          if (s[1] > maxh[i]) maxh[i] = s[1];
          if (s[2] > maxl[j]) maxl[j] = s[2];
        }
      for (i = 1, H = 0; i < h; i++) H += maxh[i];
      for (j = 1, L = 0; j < l; j++) L += maxl[j];
      M = zeromatcopy(H, L);
      for (j = 1, L = 0; j < l; j++)
      {
        for (i = 1, H = 0; i < h; i++)
        {
          GEN c = gcoeff(v,i,j);
          matfill(M, c, H, L, minss(maxh[i], maxl[j]));
          H += maxh[i];
        }
        L += maxl[j];
      }
      return M;
    default:
      pari_err_TYPE("shallowmatconcat", v);
      return NULL;
  }
}
GEN
matconcat(GEN v)
{
  pari_sp av = avma;
  return gerepilecopy(av, shallowmatconcat(v));
}

GEN
gconcat(GEN x, GEN y)
{
  long tx, lx,ty,ly,i;
  GEN z,p1;

  if (!y) return gconcat1(x);
  tx = typ(x);
  ty = typ(y);
  if (tx==t_STR  || ty==t_STR)
  {
    pari_sp av = avma;
    return gerepileuptoleaf(av, strconcat(x,y));
  }
  if (tx==t_LIST || ty==t_LIST) return listconcat(x,y);
  lx=lg(x); ly=lg(y);

  if (tx==t_MAT && lx==1)
  {
    if (ty!=t_VEC) return gtomat(y);
    if (ly==1) return cgetg(1, t_MAT);
    err_cat(x,y);
  }
  if (ty==t_MAT && ly==1)
  {
    if (tx!=t_VEC) return gtomat(x);
    if (lx==1) return cgetg(1, t_MAT);
    err_cat(x,y);
  }

  if (tx == ty)
  {
    if (tx == t_MAT && lgcols(x) != lgcols(y)) err_cat(x,y);
    if (!is_matvec_t(tx))
    {
      if (tx != t_VECSMALL) return mkvec2copy(x, y);
      z = cgetg(lx+ly-1,t_VECSMALL);
      for (i=1; i<lx; i++) z[i]     = x[i];
      for (i=1; i<ly; i++) z[lx+i-1]= y[i];
      return z;
    }
    z=cgetg(lx+ly-1,tx);
    for (i=1; i<lx; i++) gel(z,i)     = gcopy(gel(x,i));
    for (i=1; i<ly; i++) gel(z,lx+i-1)= gcopy(gel(y,i));
    return z;
  }

  if (! is_matvec_t(tx))
  {
    if (! is_matvec_t(ty)) return mkvec2copy(x, y);
    z=cgetg(ly+1,ty);
    if (ty != t_MAT) p1 = gcopy(x);
    else
    {
      if (lgcols(y)!=2) err_cat(x,y);
      p1 = mkcolcopy(x);
    }
    for (i=2; i<=ly; i++) gel(z,i) = gcopy(gel(y,i-1));
    gel(z,1) = p1; return z;
  }
  if (! is_matvec_t(ty))
  {
    z=cgetg(lx+1,tx);
    if (tx != t_MAT) p1 = gcopy(y);
    else
    {
      if (lgcols(x)!=2) err_cat(x,y);
      p1 = mkcolcopy(y);
    }
    for (i=1; i<lx; i++) gel(z,i) = gcopy(gel(x,i));
    gel(z,lx) = p1; return z;
  }

  switch(tx)
  {
    case t_VEC:
      switch(ty)
      {
        case t_COL:
          if (lx<=2) return (lx==1)? gcopy(y): gconcat(gel(x,1),y);
          if (ly>=3) break;
          return (ly==1)? gcopy(x): gconcat(x,gel(y,1));
        case t_MAT:
          z=cgetg(ly,t_MAT); if (lx != ly) break;
          for (i=1; i<ly; i++) gel(z,i) = gconcat(gel(x,i),gel(y,i));
          return z;
      }
      break;

    case t_COL:
      switch(ty)
      {
        case t_VEC:
          if (lx<=2) return (lx==1)? gcopy(y): gconcat(gel(x,1),y);
          if (ly>=3) break;
          return (ly==1)? gcopy(x): gconcat(x,gel(y,1));
        case t_MAT:
          if (lx != lgcols(y)) break;
          z=cgetg(ly+1,t_MAT); gel(z,1) = gcopy(x);
          for (i=2; i<=ly; i++) gel(z,i) = gcopy(gel(y,i-1));
          return z;
      }
      break;

    case t_MAT:
      switch(ty)
      {
        case t_VEC:
          z=cgetg(lx,t_MAT); if (ly != lx) break;
          for (i=1; i<lx; i++) gel(z,i) = gconcat(gel(x,i),gel(y,i));
          return z;
        case t_COL:
          if (ly != lgcols(x)) break;
          z=cgetg(lx+1,t_MAT); gel(z,lx) = gcopy(y);
          for (i=1; i<lx; i++) gel(z,i) = gcopy(gel(x,i));
          return z;
      }
      break;
  }
  err_cat(x,y);
  return NULL; /* LCOV_EXCL_LINE */
}
