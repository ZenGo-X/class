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
/**                      GENERIC OPERATIONS                        **/
/**                        (second part)                           **/
/**                                                                **/
/********************************************************************/
#include "pari.h"
#include "paripriv.h"

/*********************************************************************/
/**                                                                 **/
/**                MAP FUNCTIONS WITH GIVEN PROTOTYPES              **/
/**                                                                 **/
/*********************************************************************/
GEN
map_proto_G(GEN (*f)(GEN), GEN x)
{
  if (is_matvec_t(typ(x)))
  {
    long lx, i;
    GEN y = cgetg_copy(x, &lx);
    for (i=1; i<lx; i++) gel(y,i) = map_proto_G(f, gel(x,i));
    return y;
  }
  return f(x);
}

GEN
map_proto_lG(long (*f)(GEN), GEN x)
{
  if (is_matvec_t(typ(x)))
  {
    long lx, i;
    GEN y = cgetg_copy(x, &lx);
    for (i=1; i<lx; i++) gel(y,i) = map_proto_lG(f, gel(x,i));
    return y;
  }
  return stoi(f(x));
}

GEN
map_proto_lGL(long (*f)(GEN,long), GEN x, long y)
{
  if (is_matvec_t(typ(x)))
  {
    long l, i;
    GEN t = cgetg_copy(x, &l);
    for (i=1; i<l; i++) gel(t,i) = map_proto_lGL(f,gel(x,i),y);
    return t;
  }
  return stoi(f(x,y));
}

static GEN
_domul(void *data, GEN x, GEN y)
{
  GEN (*mul)(GEN,GEN)=(GEN (*)(GEN,GEN)) data;
  return mul(x,y);
}

GEN
gassoc_proto(GEN (*f)(GEN,GEN), GEN x, GEN y)
{
  if (!y)
  {
    pari_sp av = avma;
    switch(typ(x))
    {
      case t_LIST:
        x = list_data(x); if (!x) return gen_1;
      case t_VEC:
      case t_COL: break;
      default: pari_err_TYPE("association",x);
    }
    return gerepileupto(av, gen_product(x, (void *)f, _domul));

  }
  return f(x,y);
}
/*******************************************************************/
/*                                                                 */
/*                    CREATION OF A P-ADIC GEN                     */
/*                                                                 */
/*******************************************************************/
GEN
cgetp(GEN x)
{
  GEN y = cgetg(5,t_PADIC);
  y[1] = (x[1]&PRECPBITS) | _evalvalp(0);
  gel(y,2) = icopy(gel(x,2));
  gel(y,3) = icopy(gel(x,3));
  gel(y,4) = cgeti(lgefint(gel(x,3))); return y;
}

/*******************************************************************/
/*                                                                 */
/*                            SIZES                                */
/*                                                                 */
/*******************************************************************/

long
glength(GEN x)
{
  long tx = typ(x);
  switch(tx)
  {
    case t_INT:  return lgefint(x)-2;
    case t_LIST: {
      GEN L = list_data(x);
      return L? lg(L)-1: 0;
    }
    case t_REAL: return signe(x)? lg(x)-2: 0;
    case t_STR:  return strlen( GSTR(x) );
    case t_VECSMALL: return lg(x)-1;
  }
  return lg(x) - lontyp[tx];
}

GEN
matsize(GEN x)
{
  long L = lg(x) - 1;
  switch(typ(x))
  {
    case t_VEC: return mkvec2s(1, L);
    case t_COL: return mkvec2s(L, 1);
    case t_MAT: return mkvec2s(L? nbrows(x): 0, L);
  }
  pari_err_TYPE("matsize",x);
  return NULL; /* LCOV_EXCL_LINE */
}

/*******************************************************************/
/*                                                                 */
/*                 CONVERSION GEN --> long                         */
/*                                                                 */
/*******************************************************************/

long
gtolong(GEN x)
{
  switch(typ(x))
  {
    case t_INT:
      return itos(x);
    case t_REAL:
      return (long)(rtodbl(x) + 0.5);
    case t_FRAC: {
      pari_sp av = avma;
      long y = itos(ground(x));
      avma = av; return y;
    }
    case t_COMPLEX:
      if (gequal0(gel(x,2))) return gtolong(gel(x,1)); break;
    case t_QUAD:
      if (gequal0(gel(x,3))) return gtolong(gel(x,2)); break;
  }
  pari_err_TYPE("gtolong",x);
  return 0; /* LCOV_EXCL_LINE */
}

/*******************************************************************/
/*                                                                 */
/*                         COMPARISONS                             */
/*                                                                 */
/*******************************************************************/
int
isexactzero(GEN g)
{
  long i, lx;
  switch (typ(g))
  {
    case t_INT:
      return !signe(g);
    case t_INTMOD:
      return !signe(gel(g,2));
    case t_COMPLEX:
      return isexactzero(gel(g,1)) && isexactzero(gel(g,2));
    case t_FFELT:
      return FF_equal0(g);
    case t_QUAD:
      return isexactzero(gel(g,2)) && isexactzero(gel(g,3));
    case t_POLMOD:
      return isexactzero(gel(g,2));
    case t_POL:
      lx = lg(g); /* cater for Mod(0,2)*x^0 */
      return lx == 2 || (lx == 3 && isexactzero(gel(g,2)));
    case t_RFRAC:
      return isexactzero(gel(g,1)); /* may occur: Mod(0,2)/x */
    case t_VEC: case t_COL: case t_MAT:
      for (i=lg(g)-1; i; i--)
        if (!isexactzero(gel(g,i))) return 0;
      return 1;
  }
  return 0;
}
GEN
gisexactzero(GEN g)
{
  long i, lx;
  GEN a, b;
  switch (typ(g))
  {
    case t_INT:
      return !signe(g)? g: NULL;
    case t_INTMOD:
      return !signe(gel(g,2))? g: NULL;
    case t_COMPLEX:
      a = gisexactzero(gel(g,1)); if (!a) return NULL;
      b = gisexactzero(gel(g,2)); if (!b) return NULL;
      return ggcd(a,b);
    case t_FFELT:
      return FF_equal0(g)? g: NULL;
    case t_QUAD:
      a = gisexactzero(gel(g,2)); if (!a) return NULL;
      b = gisexactzero(gel(g,3)); if (!b) return NULL;
      return ggcd(a,b);
    case t_POLMOD:
      return gisexactzero(gel(g,2));
    case t_POL:
      lx = lg(g); /* cater for Mod(0,2)*x^0 */
      if (lx == 2) return gen_0;
      if (lx == 3) return gisexactzero(gel(g,2));
      return NULL;
    case t_RFRAC:
      return gisexactzero(gel(g,1)); /* may occur: Mod(0,2)/x */
    case t_VEC: case t_COL: case t_MAT:
      a = gen_0;
      for (i=lg(g)-1; i; i--)
      {
        b = gisexactzero(gel(g,i));
        if (!b) return NULL;
        a = ggcd(a, b);
      }
      return a;
  }
  return NULL;
}

int
isrationalzero(GEN g)
{
  long i;
  switch (typ(g))
  {
    case t_INT:
      return !signe(g);
    case t_COMPLEX:
      return isintzero(gel(g,1)) && isintzero(gel(g,2));
    case t_QUAD:
      return isintzero(gel(g,2)) && isintzero(gel(g,3));
    case t_POLMOD:
      return isrationalzero(gel(g,2));
    case t_POL: return lg(g) == 2;
    case t_VEC: case t_COL: case t_MAT:
      for (i=lg(g)-1; i; i--)
        if (!isrationalzero(gel(g,i))) return 0;
      return 1;
  }
  return 0;
}

int
gequal0(GEN x)
{
  switch(typ(x))
  {
    case t_INT: case t_REAL: case t_POL: case t_SER:
      return !signe(x);

    case t_INTMOD:
      return !signe(gel(x,2));

    case t_FFELT:
      return FF_equal0(x);

    case t_COMPLEX:
     /* is 0 iff norm(x) would be 0 (can happen with Re(x) and Im(x) != 0
      * only if Re(x) and Im(x) are of type t_REAL). See mp.c:addrr().
      */
      if (gequal0(gel(x,1)))
      {
        if (gequal0(gel(x,2))) return 1;
        if (typ(gel(x,1))!=t_REAL || typ(gel(x,2))!=t_REAL) return 0;
        return (expo(gel(x,1))>=expo(gel(x,2)));
      }
      if (gequal0(gel(x,2)))
      {
        if (typ(gel(x,1))!=t_REAL || typ(gel(x,2))!=t_REAL) return 0;
        return (expo(gel(x,2))>=expo(gel(x,1)));
      }
      return 0;

    case t_PADIC:
      return !signe(gel(x,4));

    case t_QUAD:
      return gequal0(gel(x,2)) && gequal0(gel(x,3));

    case t_POLMOD:
      return gequal0(gel(x,2));

    case t_RFRAC:
      return gequal0(gel(x,1));

    case t_VEC: case t_COL: case t_MAT:
    {
      long i;
      for (i=lg(x)-1; i; i--)
        if (!gequal0(gel(x,i))) return 0;
      return 1;
    }
  }
  return 0;
}

/* x a t_POL or t_SER, considered as having valuation v; let X(t) = t^(-v) x(t)
 * return 1 (true) if coeff(X,i) = 0 for all i != 0 and test(coeff(X, 0))
 * is true. Return 0 (false) otherwise, or if x == 0 */
static int
is_monomial_test(GEN x, long v, int(*test)(GEN))
{
  long d, i, l;
  if (!signe(x)) return (typ(x) == t_SER && v <= 0);
  if (v > 0) return 0;
  l = lg(x); d = 2-v;
  if (l <= d) return 0;
  /* 2 <= d < l */
  if (!test(gel(x,d))) return 0;
  for (i = 2; i < d; i++)
    if (!gequal0(gel(x,i))) return 0;
  for (i = d+1; i < l; i++)
    if (!gequal0(gel(x,i))) return 0;
  return 1;
}
static int
col_test(GEN x, int(*test)(GEN))
{
  long i, l = lg(x);
  if (l == 1 || !test(gel(x,1))) return 0;
  for (i = 2; i < l; i++)
    if (!gequal0(gel(x,i))) return 0;
  return 1;
}
static int
mat_test(GEN x, int(*test)(GEN))
{
  long i, j, l = lg(x);
  if (l == 1) return 1;
  if (l != lgcols(x)) return 0;
  for (i = 1; i < l; i++)
    for (j = 1; j < l; j++)
      if (i == j) {
        if (!test(gcoeff(x,i,i))) return 0;
      } else {
        if (!gequal0(gcoeff(x,i,j))) return 0;
      }
  return 1;
}

/* returns 1 whenever x = 1, and 0 otherwise */
int
gequal1(GEN x)
{
  switch(typ(x))
  {
    case t_INT:
      return equali1(x);

    case t_REAL:
    {
      long s = signe(x);
      if (!s) return expo(x) >= 0;
      return s > 0 ? absrnz_equal1(x): 0;
    }
    case t_INTMOD:
      return is_pm1(gel(x,2)) || is_pm1(gel(x,1));
    case t_POLMOD:
      return gequal1(gel(x,2)) || gequal1(gel(x,1));

    case t_FFELT:
      return FF_equal1(x);

    case t_FRAC:
      return 0;

    case t_COMPLEX:
      return gequal1(gel(x,1)) && gequal0(gel(x,2));

    case t_PADIC:
      return !valp(x) && gequal1(gel(x,4));

    case t_QUAD:
      return gequal1(gel(x,2)) && gequal0(gel(x,3));

    case t_POL: return is_monomial_test(x, 0, &gequal1);
    case t_SER: return is_monomial_test(x, valp(x), &gequal1);

    case t_RFRAC: return gequal(gel(x,1), gel(x,2));
    case t_COL: return col_test(x, &gequal1);
    case t_MAT: return mat_test(x, &gequal1);
  }
  return 0;
}

/* returns 1 whenever the x = -1, 0 otherwise */
int
gequalm1(GEN x)
{
  pari_sp av;
  long y;
  GEN p1;

  switch(typ(x))
  {
    case t_INT:
      return equalim1(x);

    case t_REAL:
    {
      long s = signe(x);
      if (!s) return expo(x) >= 0;
      return s < 0 ? absrnz_equal1(x): 0;
    }
    case t_INTMOD:
      av=avma; y=equalii(addui(1,gel(x,2)), gel(x,1)); avma=av; return y;

    case t_FRAC:
      return 0;

    case t_FFELT:
      return FF_equalm1(x);

    case t_COMPLEX:
      return gequalm1(gel(x,1)) && gequal0(gel(x,2));

    case t_QUAD:
      return gequalm1(gel(x,2)) && gequal0(gel(x,3));

    case t_PADIC:
      av=avma; y=equalii(addui(1,gel(x,4)), gel(x,3)); avma=av; return y;

    case t_POLMOD:
      av=avma; p1 = gaddgs(gel(x,2), 1);
      y = gequal0(p1) || gequal(p1,gel(x,1)); avma=av; return y;

    case t_POL: return is_monomial_test(x, 0, &gequalm1);
    case t_SER: return is_monomial_test(x, valp(x), &gequalm1);

    case t_RFRAC:
      av=avma; y=gequal(gel(x,1), gneg_i(gel(x,2))); avma=av; return y;
    case t_COL: return col_test(x, &gequalm1);
    case t_MAT: return mat_test(x, &gequalm1);
  }
  return 0;
}

int
gequalX(GEN x) { return typ(x) == t_POL && lg(x) == 4
                      && isintzero(gel(x,2)) && isint1(gel(x,3)); }

static int
cmp_str(const char *x, const char *y)
{
  int f = strcmp(x, y);
  return f > 0? 1
              : f? -1: 0;
}

static int
cmp_universal_rec(GEN x, GEN y, long i0)
{
  long i, lx = lg(x), ly = lg(y);
  if (lx < ly) return -1;
  if (lx > ly) return 1;
  for (i = i0; i < lx; i++)
  {
    int f = cmp_universal(gel(x,i), gel(y,i));
    if (f) return f;
  }
  return 0;
}
/* Universal "meaningless" comparison function. Transitive, returns 0 iff
 * gidentical(x,y) */
int
cmp_universal(GEN x, GEN y)
{
  long lx, ly, i, tx = typ(x), ty = typ(y);

  if (tx < ty) return -1;
  if (ty < tx) return 1;
  switch(tx)
  {
    case t_INT: return cmpii(x,y);
    case t_STR: return cmp_str(GSTR(x),GSTR(y));
    case t_REAL:
    case t_VECSMALL:
      lx = lg(x);
      ly = lg(y);
      if (lx < ly) return -1;
      if (lx > ly) return 1;
      for (i = 1; i < lx; i++)
      {
        if (x[i] < y[i]) return -1;
        if (x[i] > y[i]) return 1;
      }
      return 0;

    case t_POL:
    case t_SER:
    case t_FFELT:
    case t_CLOSURE:
      if (x[1] < y[1]) return -1;
      if (x[1] > y[1]) return 1;
      return cmp_universal_rec(x, y, 2);

    case t_LIST:
      {
        long tx = list_typ(x), ty = list_typ(y);
        GEN vx, vy;
        if (tx < ty) return -1;
        if (tx > ty) return 1;
        vx = list_data(x);
        vy = list_data(y);
        if (!vx) return vy? -1: 0;
        if (!vy) return 1;
        switch (tx)
        {
        case t_LIST_MAP:
          {
            pari_sp av = avma;
            int ret = cmp_universal_rec(maptomat_shallow(x), maptomat_shallow(y),1);
            avma = av; return ret;
          }
        default:
          return cmp_universal_rec(vx, vy, 1);
        }
      }
    default:
      return cmp_universal_rec(x, y, lontyp[tx]);
  }
}

static int
cmpfrac(GEN x, GEN y)
{
  pari_sp av = avma;
  GEN a = gel(x,1), b = gel(x,2);
  GEN c = gel(y,1), d = gel(y,2);
  int r = cmpii(mulii(a, d), mulii(b, c));
  avma = av; return r;
}
static int
cmpifrac(GEN a, GEN y)
{
  pari_sp av = avma;
  GEN c = gel(y,1), d = gel(y,2);
  int r = cmpii(mulii(a, d), c);
  avma = av; return r;
}
static int
cmprfrac(GEN a, GEN y)
{
  pari_sp av = avma;
  GEN c = gel(y,1), d = gel(y,2);
  int r = cmpri(mulri(a, d), c);
  avma = av; return r;
}
static int
cmpgen(GEN x, GEN y)
{
  pari_sp av = avma;
  int s = gsigne(gsub(x,y));
  avma = av; return s;
}

/* returns the sign of x - y when it makes sense. 0 otherwise */
int
gcmp(GEN x, GEN y)
{
  long tx = typ(x), ty = typ(y);

  if (tx == ty) /* generic case */
    switch(tx)
    {
      case t_INT:  return cmpii(x, y);
      case t_REAL: return cmprr(x, y);
      case t_FRAC: return cmpfrac(x, y);
      case t_QUAD: return cmpgen(x, y);
      case t_STR:  return cmp_str(GSTR(x), GSTR(y));
      case t_INFINITY:
      {
        long sx = inf_get_sign(x), sy = inf_get_sign(y);
        if (sx < sy) return -1;
        if (sx > sy) return 1;
        return 0;
      }
    }
  if (ty == t_INFINITY) return -inf_get_sign(y);
  switch(tx)
  {
    case t_INT:
      switch(ty)
      {
        case t_REAL: return cmpir(x, y);
        case t_FRAC: return cmpifrac(x, y);
        case t_QUAD: return cmpgen(x, y);
      }
      break;
    case t_REAL:
      switch(ty)
      {
        case t_INT:  return cmpri(x, y);
        case t_FRAC: return cmprfrac(x, y);
        case t_QUAD: return cmpgen(x, y);
      }
      break;
    case t_FRAC:
      switch(ty)
      {
        case t_INT:  return -cmpifrac(y, x);
        case t_REAL: return -cmprfrac(y, x);
        case t_QUAD: return cmpgen(x, y);
      }
      break;
    case t_QUAD:
      return cmpgen(x, y);
    case t_INFINITY: return inf_get_sign(x);
  }
  pari_err_TYPE2("comparison",x,y);
  return 0;/*LCOV_EXCL_LINE*/
}

int
gcmpsg(long s, GEN y)
{
  switch(typ(y))
  {
    case t_INT:  return cmpsi(s,y);
    case t_REAL: return cmpsr(s,y);
    case t_FRAC: {
      pari_sp av = avma;
      GEN n = gel(y,1), d = gel(y,2);
      int f = cmpii(mulsi(s,d), n); avma = av; return f;
    }
    case t_QUAD: {
      pari_sp av = avma;
      int f = gsigne(gsubsg(s, y)); avma = av; return f;
    }
    case t_INFINITY: return -inf_get_sign(y);
  }
  pari_err_TYPE2("comparison",stoi(s),y);
  return 0; /* LCOV_EXCL_LINE */
}

static long
roughtype(GEN x)
{
  switch(typ(x))
  {
    case t_MAT: return t_MAT;
    case t_VEC: case t_COL: return t_VEC;
    case t_VECSMALL: return t_VECSMALL;
    default: return t_INT;
  }
}

static int lexcmpsg(long x, GEN y);
static int lexcmpgs(GEN x, long y) { return -lexcmpsg(y,x); }
/* lexcmp(stoi(x),y), y t_VEC/t_COL/t_MAT */
static int
lexcmp_s_matvec(long x, GEN y)
{
  int fl;
  if (lg(y)==1) return 1;
  fl = lexcmpsg(x,gel(y,1));
  if (fl) return fl;
  return -1;
}
/* x a scalar, y a t_VEC/t_COL/t_MAT */
static int
lexcmp_scal_matvec(GEN x, GEN y)
{
  int fl;
  if (lg(y)==1) return 1;
  fl = lexcmp(x,gel(y,1));
  if (fl) return fl;
  return -1;
}
/* x a scalar, y a t_VECSMALL */
static int
lexcmp_scal_vecsmall(GEN x, GEN y)
{
  int fl;
  if (lg(y)==1) return 1;
  fl = lexcmpgs(x, y[1]);
  if (fl) return fl;
  return -1;
}

/* tx = ty = t_MAT, or x and y are both vect_t */
static int
lexcmp_similar(GEN x, GEN y)
{
  long i, lx = lg(x), ly = lg(y), l = minss(lx,ly);
  for (i=1; i<l; i++)
  {
    int fl = lexcmp(gel(x,i),gel(y,i));
    if (fl) return fl;
  }
  if (lx == ly) return 0;
  return (lx < ly)? -1 : 1;
}
/* x a t_VECSMALL, y a t_VEC/t_COL ~ lexcmp_similar */
static int
lexcmp_vecsmall_vec(GEN x, GEN y)
{
  long i, lx = lg(x), ly = lg(y), l = minss(lx,ly);
  for (i=1; i<l; i++)
  {
    int fl = lexcmpsg(x[i], gel(y,i));
    if (fl) return fl;
  }
  if (lx == ly) return 0;
  return (lx < ly)? -1 : 1;
}

/* x t_VEC/t_COL, y t_MAT */
static int
lexcmp_vec_mat(GEN x, GEN y)
{
  int fl;
  if (lg(x)==1) return -1;
  if (lg(y)==1) return 1;
  fl = lexcmp_similar(x,gel(y,1));
  if (fl) return fl;
  return -1;
}
/* x t_VECSMALl, y t_MAT ~ lexcmp_vec_mat */
static int
lexcmp_vecsmall_mat(GEN x, GEN y)
{
  int fl;
  if (lg(x)==1) return -1;
  if (lg(y)==1) return 1;
  fl = lexcmp_vecsmall_vec(x, gel(y,1));
  if (fl) return fl;
  return -1;
}

/* x a t_VECSMALL, not y */
static int
lexcmp_vecsmall_other(GEN x, GEN y, long ty)
{
  switch(ty)
  {
    case t_MAT: return lexcmp_vecsmall_mat(x, y);
    case t_VEC: return lexcmp_vecsmall_vec(x, y);
    default: return -lexcmp_scal_vecsmall(y, x); /*y scalar*/
  }
}

/* lexcmp(stoi(s), y) */
static int
lexcmpsg(long x, GEN y)
{
  switch(roughtype(y))
  {
    case t_MAT:
    case t_VEC:
      return lexcmp_s_matvec(x,y);
    case t_VECSMALL: /* ~ lexcmp_scal_matvec */
      if (lg(y)==1) return 1;
      return (x > y[1])? 1: -1;
    default: return gcmpsg(x,y);
  }
}

/* as gcmp for vector/matrices, using lexicographic ordering on components */
int
lexcmp(GEN x, GEN y)
{
  const long tx = roughtype(x), ty = roughtype(y);
  if (tx == ty)
    switch(tx)
    {
      case t_MAT:
      case t_VEC:
        return lexcmp_similar(x,y);
      case t_VECSMALL:
        return vecsmall_lexcmp(x,y);
      default:
        return gcmp(x,y);
    }
  if (tx == t_VECSMALL) return  lexcmp_vecsmall_other(x,y,ty);
  if (ty == t_VECSMALL) return -lexcmp_vecsmall_other(y,x,tx);

  if (tx == t_INT) return  lexcmp_scal_matvec(x,y); /*scalar*/
  if (ty == t_INT) return -lexcmp_scal_matvec(y,x);

  if (ty==t_MAT) return  lexcmp_vec_mat(x,y);
  /*tx==t_MAT*/  return -lexcmp_vec_mat(y,x);
}

/*****************************************************************/
/*                                                               */
/*                          EQUALITY                             */
/*                returns 1 if x == y, 0 otherwise               */
/*                                                               */
/*****************************************************************/
/* x,y t_POL */
static int
polidentical(GEN x, GEN y)
{
  long lx;
  if (x[1] != y[1]) return 0;
  lx = lg(x); if (lg(y) != lg(x)) return 0;
  for (lx--; lx >= 2; lx--) if (!gidentical(gel(x,lx), gel(y,lx))) return 0;
  return 1;
}
/* x,y t_SER */
static int
seridentical(GEN x, GEN y) { return polidentical(x,y); }
/* typ(x) = typ(y) = t_VEC/COL/MAT */
static int
vecidentical(GEN x, GEN y)
{
  long i;
  if ((x[0] ^ y[0]) & (TYPBITS|LGBITS)) return 0;
  for (i = lg(x)-1; i; i--)
    if (! gidentical(gel(x,i),gel(y,i)) ) return 0;
  return 1;
}
static int
identicalrr(GEN x, GEN y)
{
  long i, lx = lg(x);
  if (lg(y) != lx) return 0;
  if (x[1] != y[1]) return 0;
  i=2; while (i<lx && x[i]==y[i]) i++;
  return (i == lx);
}

static int
closure_identical(GEN x, GEN y)
{
  if (lg(x)!=lg(y) || x[1]!=y[1]) return 0;
  if (!gidentical(gel(x,2),gel(y,2)) || !gidentical(gel(x,3),gel(y,3))
   || !gidentical(gel(x,4),gel(y,4))) return 0;
  if (lg(x)<8) return 1;
  return gidentical(gel(x,7),gel(y,7));
}

static int
list_cmp(GEN x, GEN y, int cmp(GEN x, GEN y))
{
  int t = list_typ(x);
  GEN vx, vy;
  if (list_typ(y)!=t) return 0;
  vx = list_data(x);
  vy = list_data(y);
  if (!vx) return vy? 0: 1;
  if (!vy) return 0;
  if (lg(vx) != lg(vy)) return 0;
  switch (t)
  {
  case t_LIST_MAP:
    {
      pari_sp av = avma;
      GEN mx  = maptomat_shallow(x), my = maptomat_shallow(y);
      int ret = gidentical(gel(mx, 1), gel(my, 1)) && cmp(gel(mx, 2), gel(my, 2));
      avma = av; return ret;
    }
  default:
    return cmp(vx, vy);
  }
}

int
gidentical(GEN x, GEN y)
{
  long tx;

  if (x == y) return 1;
  tx = typ(x); if (typ(y) != tx) return 0;
  switch(tx)
  {
    case t_INT:
      return equalii(x,y);

    case t_REAL:
      return identicalrr(x,y);

    case t_FRAC: case t_INTMOD:
      return equalii(gel(x,2), gel(y,2)) && equalii(gel(x,1), gel(y,1));

    case t_COMPLEX:
      return gidentical(gel(x,2),gel(y,2)) && gidentical(gel(x,1),gel(y,1));
    case t_PADIC:
      return valp(x) == valp(y)
        && equalii(gel(x,2),gel(y,2))
        && equalii(gel(x,3),gel(y,3))
        && equalii(gel(x,4),gel(y,4));
    case t_POLMOD:
      return gidentical(gel(x,2),gel(y,2)) && polidentical(gel(x,1),gel(y,1));
    case t_POL:
      return polidentical(x,y);
    case t_SER:
      return seridentical(x,y);
    case t_FFELT:
      return FF_equal(x,y);

    case t_QFR:
          if (!identicalrr(gel(x,4),gel(y,4))) return 0; /* fall through */
    case t_QFI:
      return equalii(gel(x,1),gel(y,1))
          && equalii(gel(x,2),gel(y,2))
          && equalii(gel(x,3),gel(y,3));

    case t_QUAD:
      return ZX_equal(gel(x,1),gel(y,1))
          && gidentical(gel(x,2),gel(y,2))
          && gidentical(gel(x,3),gel(y,3));

    case t_RFRAC:
      return gidentical(gel(x,1),gel(y,1)) && gidentical(gel(x,2),gel(y,2));

    case t_STR:
      return !strcmp(GSTR(x),GSTR(y));
    case t_VEC: case t_COL: case t_MAT:
      return vecidentical(x,y);
    case t_VECSMALL:
      return zv_equal(x,y);
    case t_CLOSURE:
      return closure_identical(x,y);
    case t_LIST:
      return list_cmp(x, y, gidentical);
    case t_INFINITY: return gidentical(gel(x,1),gel(y,1));
  }
  return 0;
}
/* x,y t_POL */
static int
polequal(GEN x, GEN y)
{
  long lx, ly;
  if ((x[1] ^ y[1]) & (VARNBITS | SIGNBITS)) return 0;
  lx = lg(x); ly = lg(y);
  while (lx > ly) if (!gequal0(gel(x,--lx))) return 0;
  while (ly > lx) if (!gequal0(gel(y,--ly))) return 0;
  for (lx--; lx >= 2; lx--) if (!gequal(gel(x,lx), gel(y,lx))) return 0;
  return 1;
}

/* x,y t_POL */
static int
serequal(GEN x, GEN y)
{
  long lx;
  if (varn(x) != varn(y)) return 0;
  if (!signe(x))
  {
    if (!signe(y)) return 1;
    return valp(y) >= valp(x);
  }
  if (!signe(y))
    return valp(x) >= valp(y);
  if ((x[1] ^ y[1]) & VALPBITS) return 0;
  lx = minss(lg(x), lg(y));
  for (lx--; lx >= 2; lx--) if (!gequal(gel(x,lx), gel(y,lx))) return 0;
  return 1;
}

/* typ(x) = typ(y) = t_VEC/COL/MAT */
static int
vecequal(GEN x, GEN y)
{
  long i;
  if ((x[0] ^ y[0]) & (TYPBITS|LGBITS)) return 0;
  for (i = lg(x)-1; i; i--)
    if (! gequal(gel(x,i),gel(y,i)) ) return 0;
  return 1;
}

static int
gequal_try(GEN x, GEN y)
{
  int i;
  pari_CATCH(CATCH_ALL) {
    GEN E = pari_err_last();
    switch(err_get_num(E))
    {
      case e_STACK: case e_MEM: case e_ALARM:
        pari_err(0, E); /* rethrow */
    }
    return 0;
  } pari_TRY {
    i = gequal0(gadd(x, gneg_i(y)));
  } pari_ENDCATCH;
  return i;
}

int
gequal(GEN x, GEN y)
{
  pari_sp av;
  long tx, ty;
  long i;

  if (x == y) return 1;
  tx = typ(x);
  ty = typ(y);
  if (tx == ty)
    switch(tx)
    {
      case t_INT:
        return equalii(x,y);

      case t_REAL:
        return equalrr(x,y);

      case t_FRAC: case t_INTMOD:
        return equalii(gel(x,2), gel(y,2)) && equalii(gel(x,1), gel(y,1));

      case t_COMPLEX:
        return gequal(gel(x,2),gel(y,2)) && gequal(gel(x,1),gel(y,1));
      case t_PADIC:
        if (!equalii(gel(x,2),gel(y,2))) return 0;
        av = avma; i = gequal0(gsub(x,y)); avma = av;
        return i;
      case t_POLMOD:
        if (varn(gel(x,1)) != varn(gel(y,1))) break;
        return gequal(gel(x,2),gel(y,2)) && RgX_equal_var(gel(x,1),gel(y,1));
      case t_POL:
        return polequal(x,y);
      case t_SER:
        return serequal(x,y);

      case t_FFELT:
        return FF_equal(x,y);

      case t_QFR:
      case t_QFI:
        return equalii(gel(x,1),gel(y,1))
            && equalii(gel(x,2),gel(y,2))
            && equalii(gel(x,3),gel(y,3));

      case t_QUAD:
        return ZX_equal(gel(x,1),gel(y,1))
            && gequal(gel(x,2),gel(y,2))
            && gequal(gel(x,3),gel(y,3));

      case t_RFRAC:
      {
        GEN a = gel(x,1), b = gel(x,2), c = gel(y,1), d = gel(y,2);
        if (gequal(b,d)) return gequal(a,c); /* simple case */
        av = avma;
        i = gequal(simplify_shallow(gmul(a,d)), simplify_shallow(gmul(b,c)));
        avma = av; return i;
      }

      case t_STR:
        return !strcmp(GSTR(x),GSTR(y));
      case t_VEC: case t_COL: case t_MAT:
        return vecequal(x,y);
      case t_VECSMALL:
        return zv_equal(x,y);
      case t_LIST:
        return list_cmp(x, y, gequal);
      case t_CLOSURE:
        return closure_identical(x,y);
      case t_INFINITY:
        return gequal(gel(x,1),gel(y,1));
    }
  (void)&av; /* emulate volatile */
  av = avma; i = gequal_try(x, y);
  avma = av; return i;
}

int
gequalsg(long s, GEN x)
{
  pari_sp av = avma;
  int f = gequal(stoi(s), x);
  avma = av; return f;
}

/* a and b are t_INT, t_FRAC, t_REAL or t_COMPLEX of those. Check whether
 * a-b is invertible */
int
cx_approx_equal(GEN a, GEN b)
{
  pari_sp av = avma;
  GEN d;
  int r;
  if (a == b) return 1;
  d = gsub(a,b);
  r = (gequal0(d) || (typ(d) == t_COMPLEX && gequal0(cxnorm(d))));
  avma = av; return r;
}
/*******************************************************************/
/*                                                                 */
/*                          VALUATION                              */
/*             p is either a t_INT or a t_POL.                     */
/*  returns the largest exponent of p dividing x when this makes   */
/*  sense : error for types real, integermod and polymod if p does */
/*  not divide the modulus, q-adic if q!=p.                        */
/*                                                                 */
/*******************************************************************/

static long
minval(GEN x, GEN p)
{
  long i,k, val = LONG_MAX, lx = lg(x);
  for (i=lontyp[typ(x)]; i<lx; i++)
  {
    k = gvaluation(gel(x,i),p);
    if (k < val) val = k;
  }
  return val;
}

static int
intdvd(GEN x, GEN y, GEN *z) { GEN r; *z = dvmdii(x,y,&r); return (r==gen_0); }

/* x t_FRAC, p t_INT, return v_p(x) */
static long
ratval(GEN x, GEN p) {
  long v = Z_pval(gel(x,2),p);
  if (v) return -v;
  return Z_pval(gel(x,1),p);
}

long
Q_pval(GEN x, GEN p) { return (typ(x) == t_INT)? Z_pval(x, p): ratval(x, p); }

long
Q_pvalrem(GEN x, GEN p, GEN *y)
{
  GEN a, b;
  long v;
  if (typ(x) == t_INT) return Z_pvalrem(x, p, y);
  a = gel(x,1);
  b = gel(x,2);
  v = Z_pvalrem(b, p, &b);
  if (v) { *y = isint1(b)? a: mkfrac(a, b); return -v; }
  v = Z_pvalrem(a, p, &a);
  *y = mkfrac(a, b); return v;
}

long
gvaluation(GEN x, GEN p)
{
  long tx = typ(x), tp = typ(p);
  pari_sp av;

  switch(tp)
  {
    case t_INT:
      if (signe(p) && !is_pm1(p)) break;
      pari_err_DOMAIN("gvaluation", "p", "=", p, p);
    case t_POL:
      if (degpol(p) > 0) break;
    default:
      pari_err_DOMAIN("gvaluation", "p", "=", p, p);
  }

  switch(tx)
  {
    case t_INT:
      if (!signe(x)) return LONG_MAX;
      if (tp == t_POL) return 0;
      return Z_pval(x,p);

    case t_REAL:
      if (tp == t_POL) return 0;
      break;

    case t_FFELT:
      if (tp == t_POL) return FF_equal0(x)? LONG_MAX: 0;
      break;

    case t_INTMOD: {
      GEN a = gel(x,1), b = gel(x,2);
      long val;
      if (tp == t_POL) return signe(b)? 0: LONG_MAX;
      av = avma;
      if (!intdvd(a, p, &a)) break;
      if (!intdvd(b, p, &b)) { avma = av; return 0; }
      val = 1; while (intdvd(a,p,&a) && intdvd(b,p,&b)) val++;
      avma = av; return val;
    }

    case t_FRAC:
      if (tp == t_POL) return 0;
      return ratval(x, p);

    case t_PADIC:
      if (tp == t_POL) return 0;
      if (!equalii(p,gel(x,2))) break;
      return valp(x);

    case t_POLMOD: {
      GEN a = gel(x,1), b = gel(x,2);
      long v, val;
      if (tp == t_INT) return gvaluation(b,p);
      v = varn(p);
      if (varn(a) != v) return 0;
      av = avma;
      a = RgX_divrem(a, p, ONLY_DIVIDES);
      if (!a) break;
      if (typ(b) != t_POL || varn(b) != v ||
          !(b = RgX_divrem(b, p, ONLY_DIVIDES)) ) { avma = av; return 0; }
      val = 1;
      while ((a = RgX_divrem(a, p, ONLY_DIVIDES)) &&
             (b = RgX_divrem(b, p, ONLY_DIVIDES)) ) val++;
      avma = av; return val;
    }
    case t_POL: {
      if (tp == t_POL) {
        long vp = varn(p), vx = varn(x);
        if (vp == vx)
        {
          long val;
          if (RgX_is_monomial(p)) return RgX_val(x) / degpol(p);
          av = avma;
          for (val=0; ; val++)
          {
            x = RgX_divrem(x,p,ONLY_DIVIDES);
            if (!x) { avma = av; return val; }
            if (gc_needed(av,1))
            {
              if(DEBUGMEM>1) pari_warn(warnmem,"gvaluation");
              x = gerepilecopy(av, x);
            }
          }
        }
        if (varncmp(vx, vp) > 0) return 0;
      }
      return minval(x,p);
    }

    case t_SER: {
      if (tp == t_POL) {
        long vp = varn(p), vx = varn(x);
        if (vp == vx)
        {
          long val = RgX_val(p);
          if (!val) pari_err_DOMAIN("gvaluation", "p", "=", p, p);
          return (long)(valp(x) / val);
        }
        if (varncmp(vx, vp) > 0) return 0;
      }
      return minval(x,p);
    }

    case t_RFRAC:
      return gvaluation(gel(x,1),p) - gvaluation(gel(x,2),p);

    case t_COMPLEX: case t_QUAD: case t_VEC: case t_COL: case t_MAT:
      return minval(x,p);
  }
  pari_err_OP("valuation", x,p);
  return 0; /* LCOV_EXCL_LINE */
}
GEN
gpvaluation(GEN x, GEN p)
{
  long v = gvaluation(x,p);
  return v == LONG_MAX? mkoo(): stoi(v);
}

/* x is non-zero */
long
u_lvalrem(ulong x, ulong p, ulong *py)
{
  ulong vx;
  if (p == 2) { vx = vals(x); *py = x >> vx; return vx; }
  for(vx = 0;;)
  {
    if (x % p) { *py = x; return vx; }
    x /= p; /* gcc is smart enough to make a single div */
    vx++;
  }
}
long
u_lval(ulong x, ulong p)
{
  ulong vx;
  if (p == 2) return vals(x);
  for(vx = 0;;)
  {
    if (x % p) return vx;
    x /= p; /* gcc is smart enough to make a single div */
    vx++;
  }
}

long
z_lval(long s, ulong p) { return u_lval(labs(s), p); }
long
z_lvalrem(long s, ulong p, long *py)
{
  long v;
  if (s < 0)
  {
    ulong u = (ulong)-s;
    v = u_lvalrem(u, p, &u);
    *py = -(long)u;
  }
  else
  {
    ulong u = (ulong)s;
    v = u_lvalrem(u, p, &u);
    *py = (long)u;
  }
  return v;
}
/* assume |p| > 1 */
long
z_pval(long s, GEN p)
{
  if (lgefint(p) > 3) return 0;
  return z_lval(s, uel(p,2));
}
/* assume |p| > 1 */
long
z_pvalrem(long s, GEN p, long *py)
{
  if (lgefint(p) > 3) { *py = s; return 0; }
  return z_lvalrem(s, uel(p,2), py);
}

/* return v_q(x) and set *py = x / q^v_q(x), using divide & conquer */
static long
Z_pvalrem_DC(GEN x, GEN q, GEN *py)
{
  GEN r, z = dvmdii(x, q, &r);
  long v;
  if (r != gen_0) { *py = x; return 0; }
  if (2 * lgefint(q) <= lgefint(z)+3) /* avoid squaring if pointless */
    v = Z_pvalrem_DC(z, sqri(q), py) << 1;
  else
  { v = 0; *py = z; }
  z = dvmdii(*py, q, &r);
  if (r != gen_0) return v + 1;
  *py = z; return v + 2;
}

static const long VAL_DC_THRESHOLD = 16;

long
Z_lval(GEN x, ulong p)
{
  long vx;
  pari_sp av;
  if (p == 2) return vali(x);
  if (lgefint(x) == 3) return u_lval(uel(x,2), p);
  av = avma;
  for(vx = 0;;)
  {
    ulong r;
    GEN q = absdiviu_rem(x, p, &r);
    if (r) break;
    vx++; x = q;
    if (vx == VAL_DC_THRESHOLD) {
      if (p == 1) pari_err_DOMAIN("Z_lval", "p", "=", gen_1, gen_1);
      vx += Z_pvalrem_DC(x, sqru(p), &x) << 1;
      q = absdiviu_rem(x, p, &r); if (!r) vx++;
      break;
    }
  }
  avma = av; return vx;
}
long
Z_lvalrem(GEN x, ulong p, GEN *py)
{
  long vx, sx;
  pari_sp av;
  if (p == 2) { vx = vali(x); *py = shifti(x, -vx); return vx; }
  if (lgefint(x) == 3) {
    ulong u;
    vx = u_lvalrem(uel(x,2), p, &u);
    *py = signe(x) < 0? utoineg(u): utoipos(u);
    return vx;
  }
  av = avma; (void)new_chunk(lgefint(x));
  sx = signe(x);
  for(vx = 0;;)
  {
    ulong r;
    GEN q = absdiviu_rem(x, p, &r);
    if (r) break;
    vx++; x = q;
    if (vx == VAL_DC_THRESHOLD) {
      if (p == 1) pari_err_DOMAIN("Z_lvalrem", "p", "=", gen_1, gen_1);
      vx += Z_pvalrem_DC(x, sqru(p), &x) << 1;
      q = absdiviu_rem(x, p, &r); if (!r) { vx++; x = q; }
      break;
    }
  }
  avma = av; *py = icopy(x); setsigne(*py, sx); return vx;
}

/* Is |q| <= p ? */
static int
isless_iu(GEN q, ulong p) {
  long l = lgefint(q);
  return l==2 || (l == 3 && uel(q,2) <= p);
}

long
u_lvalrem_stop(ulong *n, ulong p, int *stop)
{
  ulong N = *n, q = N / p, r = N % p; /* gcc makes a single div */
  long v = 0;
  if (!r)
  {
    do { v++; N = q; q = N / p; r = N % p; } while (!r);
    *n = N;
  }
  *stop = q <= p; return v;
}
/* Assume n > 0. Return v_p(n), set *n := n/p^v_p(n). Set 'stop' if now
 * n < p^2 [implies n prime if no prime < p divides n] */
long
Z_lvalrem_stop(GEN *n, ulong p, int *stop)
{
  pari_sp av;
  long v;
  ulong r;
  GEN N, q;

  if (lgefint(*n) == 3)
  {
    r = (*n)[2];
    v = u_lvalrem_stop(&r, p, stop);
    if (v) *n = utoipos(r);
    return v;
  }
  av = avma; v = 0; q = absdiviu_rem(*n, p, &r);
  if (r) avma = av;
  else
  {
    do {
      v++; N = q;
      if (v == VAL_DC_THRESHOLD)
      {
        v += Z_pvalrem_DC(N,sqru(p),&N) << 1;
        q = absdiviu_rem(N, p, &r); if (!r) { v++; N = q; }
        break;
      }
      q = absdiviu_rem(N, p, &r);
    } while (!r);
    *n = N;
  }
  *stop = isless_iu(q,p); return v;
}

/* x is a non-zero integer, |p| > 1 */
long
Z_pvalrem(GEN x, GEN p, GEN *py)
{
  long vx;
  pari_sp av;

  if (lgefint(p) == 3) return Z_lvalrem(x, uel(p,2), py);
  if (lgefint(x) == 3) { *py = icopy(x); return 0; }
  av = avma; vx = 0; (void)new_chunk(lgefint(x));
  for(;;)
  {
    GEN r, q = dvmdii(x,p,&r);
    if (r != gen_0) { avma = av; *py = icopy(x); return vx; }
    vx++; x = q;
  }
}
long
u_pvalrem(ulong x, GEN p, ulong *py)
{
  if (lgefint(p) == 3) return u_lvalrem(x, uel(p,2), py);
  *py = x; return 0;
}
long
u_pval(ulong x, GEN p)
{
  if (lgefint(p) == 3) return u_lval(x, uel(p,2));
  return 0;
}
long
Z_pval(GEN x, GEN p) {
  long vx;
  pari_sp av;

  if (lgefint(p) == 3) return Z_lval(x, uel(p,2));
  if (lgefint(x) == 3) return 0;
  av = avma; vx = 0;
  for(;;)
  {
    GEN r, q = dvmdii(x,p,&r);
    if (r != gen_0) { avma = av; return vx; }
    vx++; x = q;
  }
}

/* return v_p(n!) = [n/p] + [n/p^2] + ... */
long
factorial_lval(ulong n, ulong p)
{
  ulong q = p, v = 0;
  do { v += n/q; q *= p; } while (n >= q);
  return (long)v;
}

/********** Same for "containers" ZX / ZV / ZC **********/

/* If the t_INT q divides the ZX/ZV x, return the quotient. Otherwise NULL.
 * Stack clean; assumes lg(x) > 1 */
static GEN
gen_Z_divides(GEN x, GEN q, long imin)
{
  long i, l;
  GEN y = cgetg_copy(x, &l);

  y[1] = x[1]; /* Needed for ZX; no-op if ZV, overwritten in first iteration */
  for (i = imin; i < l; i++)
  {
    GEN r, xi = gel(x,i);
    if (!signe(xi)) { gel(y,i) = xi; continue; }
    gel(y,i) = dvmdii(xi, q, &r);
    if (r != gen_0) { avma = (pari_sp)(y+l); return NULL; }
  }
  return y;
}
/* If q divides the ZX/ZV x, return the quotient. Otherwise NULL.
 * Stack clean; assumes lg(x) > 1 */
static GEN
gen_z_divides(GEN x, ulong q, long imin)
{
  long i, l;
  GEN y = cgetg_copy(x, &l);

  y[1] = x[1]; /* Needed for ZX; no-op if ZV, overwritten in first iteration */
  for (i = imin; i < l; i++)
  {
    ulong r;
    GEN xi = gel(x,i);
    if (!signe(xi)) { gel(y,i) = xi; continue; }
    gel(y,i) = absdiviu_rem(xi, q, &r);
    if (r) { avma = (pari_sp)(y+l); return NULL; }
    affectsign_safe(xi, &gel(y,i));
  }
  return y;
}

/* return v_q(x) and set *py = x / q^v_q(x), using divide & conquer */
static long
gen_pvalrem_DC(GEN x, GEN q, GEN *py, long imin)
{

  pari_sp av = avma;
  long v, i, l, lz = LONG_MAX;
  GEN y = cgetg_copy(x, &l);

  y[1] = x[1];
  for (i = imin; i < l; i++)
  {
    GEN r, xi = gel(x,i);
    if (!signe(xi)) { gel(y,i) = xi; continue; }
    gel(y,i) = dvmdii(xi, q, &r);
    if (r != gen_0) { avma = av; *py = x; return 0; }
    lz = minss(lz, lgefint(gel(y,i)));
  }
  if (2 * lgefint(q) <= lz+3) /* avoid squaring if pointless */
    v = gen_pvalrem_DC(y, sqri(q), py, imin) << 1;
  else
  { v = 0; *py = y; }

  y = gen_Z_divides(*py, q, imin);
  if (!y) return v+1;
  *py = y; return v+2;
}

static long
gen_2val(GEN x, long imin)
{
  long i, lx = lg(x), v = LONG_MAX;
  for (i = imin; i < lx; i++)
  {
    GEN c = gel(x,i);
    long w;
    if (!signe(c)) continue;
    w = vali(c);
    if (w < v) { v = w; if (!v) break; }
  }
  return v;
}
static long
gen_lval(GEN x, ulong p, long imin)
{
  long i, lx, v;
  pari_sp av;
  GEN y;
  if (p == 2) return gen_2val(x, imin);
  av = avma;
  lx = lg(x); y = leafcopy(x);
  for(v = 0;; v++)
    for (i = imin; i < lx; i++)
    {
      ulong r; gel(y,i) = absdiviu_rem(gel(y,i), p, &r);
      if (r) { avma = av; return v; }
    }
}
long
ZX_lval(GEN x, ulong p) { return gen_lval(x, p, 2); }
long
ZV_lval(GEN x, ulong p) { return gen_lval(x, p, 1); }

static long
gen_pval(GEN x, GEN p, long imin)
{
  long i, lx, v;
  pari_sp av;
  GEN y;
  if (lgefint(p) == 3) return gen_lval(x, p[2], imin);
  av = avma;
  lx = lg(x); y = leafcopy(x);
  for(v = 0;; v++)
  {
    if (v == VAL_DC_THRESHOLD)
    {
      if (is_pm1(p)) pari_err_DOMAIN("gen_pval", "p", "=", p, p);
      v += gen_pvalrem_DC(y, p, &y, imin);
      avma = av; return v;
    }

    for (i = imin; i < lx; i++)
    {
      GEN r; gel(y,i) = dvmdii(gel(y,i), p, &r);
      if (r != gen_0) { avma = av; return v; }
    }
  }
}
long
ZX_pval(GEN x, GEN p) { return gen_pval(x, p, 2); }
long
ZV_pval(GEN x, GEN p) { return gen_pval(x, p, 1); }
/* v = 0 (mod p) */
int
ZV_Z_dvd(GEN v, GEN p)
{
  pari_sp av = avma;
  long i, l = lg(v);
  for (i=1; i<l; i++)
    if (!dvdii(gel(v,i), p)) { avma = av; return 0; }
  avma = av; return 1;
}

static long
gen_2valrem(GEN x, GEN *px, long imin)
{
  long i, lx = lg(x), v = LONG_MAX;
  GEN z;
  for (i = imin; i < lx; i++)
  {
    GEN c = gel(x,i);
    long w;
    if (!signe(c)) continue;
    w = vali(c);
    if (w < v) {
      v = w;
      if (!v) { *px = x; return 0; } /* early abort */
    }
  }
  z = cgetg_copy(x, &lx); z[1] = x[1];
  for (i=imin; i<lx; i++) gel(z,i) = shifti(gel(x,i), -v);
  *px = z; return v;
}
static long
gen_lvalrem(GEN x, ulong p, GEN *px, long imin)
{
  long i, lx, v;
  GEN y;
  if (p == 2) return gen_2valrem(x, px, imin);
  y = cgetg_copy(x, &lx);
  y[1] = x[1];
  x = leafcopy(x);
  for(v = 0;; v++)
  {
    if (v == VAL_DC_THRESHOLD)
    {
      if (p == 1) pari_err_DOMAIN("gen_lvalrem", "p", "=", gen_1, gen_1);
      v += gen_pvalrem_DC(x, sqru(p), px, imin) << 1;
      x = gen_z_divides(*px, p, imin);
      if (x) { *px = x; v++; }
      return v;
    }

    for (i = imin; i < lx; i++)
    {
      ulong r; gel(y,i) = absdiviu_rem(gel(x,i), p, &r);
      if (r) { *px = x; return v; }
      affectsign_safe(gel(x,i), &gel(y,i));
    }
    swap(x, y);
  }
}
long
ZX_lvalrem(GEN x, ulong p, GEN *px) { return gen_lvalrem(x,p,px, 2); }
long
ZV_lvalrem(GEN x, ulong p, GEN *px) { return gen_lvalrem(x,p,px, 1); }

static long
gen_pvalrem(GEN x, GEN p, GEN *px, long imin)
{
  long i, lx, v;
  GEN y;
  if (lgefint(p) == 3) return gen_lvalrem(x, p[2], px, imin);
  y = cgetg_copy(x, &lx);
  y[1] = x[1];
  x = leafcopy(x);
  for(v = 0;; v++)
  {
    if (v == VAL_DC_THRESHOLD)
    {
      if (is_pm1(p)) pari_err_DOMAIN("gen_pvalrem", "p", "=", p, p);
      return v + gen_pvalrem_DC(x, p, px, imin);
    }

    for (i = imin; i < lx; i++)
    {
      GEN r; gel(y,i) = dvmdii(gel(x,i), p, &r);
      if (r != gen_0) { *px = x; return v; }
    }
    swap(x, y);
  }
}
long
ZX_pvalrem(GEN x, GEN p, GEN *px) { return gen_pvalrem(x,p,px, 2); }
long
ZV_pvalrem(GEN x, GEN p, GEN *px) { return gen_pvalrem(x,p,px, 1); }

/*******************************************************************/
/*                                                                 */
/*                       NEGATION: Create -x                       */
/*                                                                 */
/*******************************************************************/

GEN
gneg(GEN x)
{
  long lx, i;
  GEN y;

  switch(typ(x))
  {
    case t_INT:
      return signe(x)? negi(x): gen_0;
    case t_REAL:
      return mpneg(x);

    case t_INTMOD: y=cgetg(3,t_INTMOD);
      gel(y,1) = icopy(gel(x,1));
      gel(y,2) = signe(gel(x,2))? subii(gel(y,1),gel(x,2)): gen_0;
      break;

    case t_FRAC:
      y = cgetg(3, t_FRAC);
      gel(y,1) = negi(gel(x,1));
      gel(y,2) = icopy(gel(x,2)); break;

    case t_COMPLEX:
      y=cgetg(3, t_COMPLEX);
      gel(y,1) = gneg(gel(x,1));
      gel(y,2) = gneg(gel(x,2));
      break;

    case t_POLMOD:
      retmkpolmod(gneg(gel(x,2)), RgX_copy(gel(x,1)));

    case t_RFRAC:
      y = cgetg(3, t_RFRAC);
      gel(y,1) = gneg(gel(x,1));
      gel(y,2) = RgX_copy(gel(x,2)); break;

    case t_PADIC:
      if (!signe(gel(x,4))) return gcopy(x);
      y = cgetg(5, t_PADIC);
      y[1] = x[1];
      gel(y,2) = icopy(gel(x,2));
      gel(y,3) = icopy(gel(x,3));
      gel(y,4) = subii(gel(x,3),gel(x,4));
      break;

    case t_QUAD:
      y=cgetg(4,t_QUAD);
      gel(y,1) = ZX_copy(gel(x,1));
      gel(y,2) = gneg(gel(x,2));
      gel(y,3) = gneg(gel(x,3)); break;

    case t_FFELT: return FF_neg(x);
    case t_POL: return RgX_neg(x);
    case t_SER:
      y = cgetg_copy(x, &lx); y[1] = x[1];
      for (i=2; i<lx; i++) gel(y,i) = gneg(gel(x,i));
      break;
    case t_VEC: return RgV_neg(x);
    case t_COL: return RgC_neg(x);
    case t_MAT: return RgM_neg(x);
    case t_INFINITY: return inf_get_sign(x) == 1? mkmoo(): mkoo();
    default:
      pari_err_TYPE("gneg",x);
      return NULL; /* LCOV_EXCL_LINE */
  }
  return y;
}

GEN
gneg_i(GEN x)
{
  long lx, i;
  GEN y;

  switch(typ(x))
  {
    case t_INT:
      return signe(x)? negi(x): gen_0;
    case t_REAL:
      return mpneg(x);

    case t_INTMOD: y=cgetg(3,t_INTMOD);
      gel(y,1) = gel(x,1);
      gel(y,2) = signe(gel(x,2))? subii(gel(y,1),gel(x,2)): gen_0;
      break;

    case t_FRAC:
      y = cgetg(3, t_FRAC);
      gel(y,1) = negi(gel(x,1));
      gel(y,2) = gel(x,2); break;

    case t_COMPLEX:
      y = cgetg(3, t_COMPLEX);
      gel(y,1) = gneg_i(gel(x,1));
      gel(y,2) = gneg_i(gel(x,2)); break;

    case t_PADIC: y = cgetg(5,t_PADIC);
      y[1] = x[1];
      gel(y,2) = gel(x,2);
      gel(y,3) = gel(x,3);
      gel(y,4) = signe(gel(x,4))? subii(gel(x,3),gel(x,4)): gen_0; break;

    case t_POLMOD:
      retmkpolmod(gneg_i(gel(x,2)), RgX_copy(gel(x,1)));

    case t_FFELT: return FF_neg_i(x);

    case t_QUAD: y=cgetg(4,t_QUAD);
      gel(y,1) = gel(x,1);
      gel(y,2) = gneg_i(gel(x,2));
      gel(y,3) = gneg_i(gel(x,3)); break;

    case t_VEC: case t_COL: case t_MAT:
      y = cgetg_copy(x, &lx);
      for (i=1; i<lx; i++) gel(y,i) = gneg_i(gel(x,i));
      break;

    case t_POL: case t_SER:
      y = cgetg_copy(x, &lx); y[1]=x[1];
      for (i=2; i<lx; i++) gel(y,i) = gneg_i(gel(x,i));
      break;

    case t_RFRAC:
      y = cgetg(3, t_RFRAC);
      gel(y,1) = gneg_i(gel(x,1));
      gel(y,2) = gel(x,2); break;

    default:
      pari_err_TYPE("gneg_i",x);
      return NULL; /* LCOV_EXCL_LINE */
  }
  return y;
}

/******************************************************************/
/*                                                                */
/*                       ABSOLUTE VALUE                           */
/*    Create abs(x) if x is integer, real, fraction or complex.   */
/*                       Error otherwise.                         */
/*                                                                */
/******************************************************************/
static int
is_negative(GEN x) {
  switch(typ(x))
  {
    case t_INT: case t_REAL:
      return (signe(x) < 0);
    case t_FRAC:
      return (signe(gel(x,1)) < 0);
  }
  return 0;
}

GEN
gabs(GEN x, long prec)
{
  long lx, i;
  pari_sp av, tetpil;
  GEN y,p1;

  switch(typ(x))
  {
    case t_INT: case t_REAL:
      return mpabs(x);

    case t_FRAC:
      return absfrac(x);

    case t_COMPLEX:
      av=avma; p1=cxnorm(x);
      switch(typ(p1))
      {
        case t_INT:
          if (!Z_issquareall(p1, &y)) break;
          return gerepileupto(av, y);
        case t_FRAC: {
          GEN a,b;
          if (!Z_issquareall(gel(p1,1), &a)) break;
          if (!Z_issquareall(gel(p1,2), &b)) break;
          return gerepileupto(av, gdiv(a,b));
        }
      }
      tetpil=avma;
      return gerepile(av,tetpil,gsqrt(p1,prec));

    case t_QUAD:
      av = avma;
      return gerepileuptoleaf(av, gabs(quadtofp(x, prec), prec));

    case t_POL:
      lx = lg(x); if (lx<=2) return RgX_copy(x);
      return is_negative(gel(x,lx-1))? gneg(x): RgX_copy(x);

    case t_SER:
     if (!signe(x)) pari_err_DOMAIN("abs", "argument", "=", gen_0, x);
     if (valp(x)) pari_err_DOMAIN("abs", "series valuation", "!=", gen_0, x);
     return is_negative(gel(x,2))? gneg(x): gcopy(x);

    case t_VEC: case t_COL: case t_MAT:
      y = cgetg_copy(x, &lx);
      for (i=1; i<lx; i++) gel(y,i) = gabs(gel(x,i),prec);
      return y;
  }
  pari_err_TYPE("gabs",x);
  return NULL; /* LCOV_EXCL_LINE */
}

GEN
gmax(GEN x, GEN y) { return gcopy(gmax_shallow(x,y)); }
GEN
gmaxgs(GEN x, long s) { return (gcmpsg(s,x)>=0)? stoi(s): gcopy(x); }

GEN
gmin(GEN x, GEN y) { return gcopy(gmin_shallow(x,y)); }
GEN
gmings(GEN x, long s) { return (gcmpsg(s,x)>0)? gcopy(x): stoi(s); }

long
vecindexmax(GEN x)
{
  long lx = lg(x), i0, i;
  GEN s;

  if (lx==1) pari_err_DOMAIN("vecindexmax", "empty argument", "=", x,x);
  switch(typ(x))
  {
    case t_VEC: case t_COL:
      s = gel(x,i0=1);
      for (i=2; i<lx; i++)
        if (gcmp(gel(x,i),s) > 0) s = gel(x,i0=i);
      return i0;
    case t_VECSMALL:
      return vecsmall_indexmax(x);
    default: pari_err_TYPE("vecindexmax",x);
  }
  /* LCOV_EXCL_LINE */
  return 0;
}
long
vecindexmin(GEN x)
{
  long lx = lg(x), i0, i;
  GEN s;

  if (lx==1) pari_err_DOMAIN("vecindexmin", "empty argument", "=", x,x);
  switch(typ(x))
  {
    case t_VEC: case t_COL:
      s = gel(x,i0=1);
      for (i=2; i<lx; i++)
        if (gcmp(gel(x,i),s) < 0) s = gel(x,i0=i);
      return i0;
    case t_VECSMALL:
      return vecsmall_indexmin(x);
    default: pari_err_TYPE("vecindexmin",x);
  }
  /* LCOV_EXCL_LINE */
  return 0;
}

GEN
vecmax0(GEN x, GEN *pi)
{
  long i, lx = lg(x), tx = typ(x);
  if (!is_matvec_t(tx) && tx != t_VECSMALL) return gcopy(x);
  if (lx==1) pari_err_DOMAIN("vecmax", "empty argument", "=", x,x);
  switch(typ(x))
  {
    case t_VEC: case t_COL:
      i = vecindexmax(x); if (pi) *pi = utoipos(i);
      return gcopy(gel(x,i));
    case t_MAT: {
      long j, i0 = 1, j0 = 1, lx2 = lgcols(x);
      GEN s;
      if (lx2 == 1) pari_err_DOMAIN("vecmax", "empty argument", "=", x,x);
      s = gcoeff(x,i0,j0); i = 2;
      for (j=1; j<lx; j++,i=1)
      {
        GEN c = gel(x,j);
        for (; i<lx2; i++)
          if (gcmp(gel(c,i),s) > 0) { s = gel(c,i); j0=j; i0=i; }
      }
      if (pi) *pi = mkvec2(utoipos(i0), utoipos(j0));
      return gcopy(s);
    }
    case t_VECSMALL:
      i = vecsmall_indexmax(x); if (pi) *pi = utoipos(i);
      return stoi(x[i]);
  }
  return NULL;/*LCOV_EXCL_LINE*/
}
GEN
vecmin0(GEN x, GEN *pi)
{
  long i, lx = lg(x), tx = typ(x);
  if (!is_matvec_t(tx) && tx != t_VECSMALL) return gcopy(x);
  if (lx==1) pari_err_DOMAIN("vecmin", "empty argument", "=", x,x);
  switch(typ(x))
  {
    case t_VEC: case t_COL:
      i = vecindexmin(x); if (pi) *pi = utoipos(i);
      return gcopy(gel(x,i));
    case t_MAT: {
      long j, i0 = 1, j0 = 1, lx2 = lgcols(x);
      GEN s;
      if (lx2 == 1) pari_err_DOMAIN("vecmin", "empty argument", "=", x,x);
      s = gcoeff(x,i0,j0); i = 2;
      for (j=1; j<lx; j++,i=1)
      {
        GEN c = gel(x,j);
        for (; i<lx2; i++)
          if (gcmp(gel(c,i),s) < 0) { s = gel(c,i); j0=j; i0=i; }
      }
      if (pi) *pi = mkvec2(utoipos(i0), utoipos(j0));
      return gcopy(s);
    }
    case t_VECSMALL:
      i = vecsmall_indexmin(x); if (pi) *pi = utoipos(i);
      return stoi(x[i]);
  }
  return NULL;/*LCOV_EXCL_LINE*/
}

GEN
vecmax(GEN x) { return vecmax0(x, NULL); }
GEN
vecmin(GEN x) { return vecmin0(x, NULL); }

/*******************************************************************/
/*                                                                 */
/*                      AFFECT long --> GEN                        */
/*         affect long s to GEN x. Useful for initialization.      */
/*                                                                 */
/*******************************************************************/

static void
padicaff0(GEN x)
{
  if (signe(gel(x,4)))
  {
    x[1] = evalvalp(valp(x)+precp(x));
    affsi(0,gel(x,4));
  }
}

void
gaffsg(long s, GEN x)
{
  switch(typ(x))
  {
    case t_INT: affsi(s,x); break;
    case t_REAL: affsr(s,x); break;
    case t_INTMOD: modsiz(s,gel(x,1),gel(x,2)); break;
    case t_FRAC: affsi(s,gel(x,1)); affsi(1,gel(x,2)); break;
    case t_COMPLEX: gaffsg(s,gel(x,1)); gaffsg(0,gel(x,2)); break;
    case t_PADIC: {
      long vx;
      GEN y;
      if (!s) { padicaff0(x); break; }
      vx = Z_pvalrem(stoi(s), gel(x,2), &y);
      setvalp(x,vx); modiiz(y,gel(x,3),gel(x,4));
      break;
    }
    case t_QUAD: gaffsg(s,gel(x,2)); gaffsg(0,gel(x,3)); break;
    default: pari_err_TYPE2("=",stoi(s),x);
  }
}

/*******************************************************************/
/*                                                                 */
/*                     GENERIC AFFECTATION                         */
/*         Affect the content of x to y, whenever possible         */
/*                                                                 */
/*******************************************************************/
/* x PADIC, Y INT, return lift(x * Mod(1,Y)) */
GEN
padic_to_Fp(GEN x, GEN Y) {
  pari_sp av = avma;
  GEN p = gel(x,2), z;
  long vy, vx = valp(x);
  if (!signe(Y)) pari_err_INV("padic_to_Fp",Y);
  vy = Z_pvalrem(Y,p, &z);
  if (vx < 0 || !gequal1(z)) pari_err_OP("",x, mkintmod(gen_1,Y));
  if (vx >= vy) { avma = av; return gen_0; }
  z = gel(x,4);
  if (!signe(z) || vy > vx + precp(x)) pari_err_OP("",x, mkintmod(gen_1,Y));
  if (vx) z = mulii(z, powiu(p,vx));
  return gerepileuptoint(av, remii(z, Y));
}
ulong
padic_to_Fl(GEN x, ulong Y) {
  GEN p = gel(x,2);
  ulong u, z;
  long vy, vx = valp(x);
  vy = u_pvalrem(Y,p, &u);
  if (vx < 0 || u != 1) pari_err_OP("",x, mkintmodu(1,Y));
  /* Y = p^vy */
  if (vx >= vy) return 0;
  z = umodiu(gel(x,4), Y);
  if (!z || vy > vx + precp(x)) pari_err_OP("",x, mkintmodu(1,Y));
  if (vx) {
    ulong pp = p[2];
    z = Fl_mul(z, upowuu(pp,vx), Y); /* p^vx < p^vy = Y */
  }
  return z;
}

static void
croak(const char *s) {
  char *t;
  t = stack_sprintf("gaffect [overwriting universal object: %s]",s);
  pari_err_BUG(t);
}

void
gaffect(GEN x, GEN y)
{
  long vx, i, lx, ly, tx = typ(x), ty = typ(y);
  pari_sp av;
  GEN p1, num, den;

  if (tx == ty) switch(tx) {
    case t_INT:
      if (!is_universal_constant(y)) { affii(x,y); return; }
      /* y = gen_0, gnil, gen_1 or gen_2 */
      if (y==gen_0)  croak("gen_0");
      if (y==gen_1)  croak("gen_1");
      if (y==gen_m1) croak("gen_m1");
      if (y==gen_m2) croak("gen_m2");
      if (y==gen_2)  croak("gen_2");
      croak("gnil)");
    case t_REAL: affrr(x,y); return;
    case t_INTMOD:
      if (!dvdii(gel(x,1),gel(y,1))) pari_err_OP("",x,y);
      modiiz(gel(x,2),gel(y,1),gel(y,2)); return;
    case t_FRAC:
      affii(gel(x,1),gel(y,1));
      affii(gel(x,2),gel(y,2)); return;
    case t_COMPLEX:
      gaffect(gel(x,1),gel(y,1));
      gaffect(gel(x,2),gel(y,2)); return;
    case t_PADIC:
      if (!equalii(gel(x,2),gel(y,2))) pari_err_OP("",x,y);
      modiiz(gel(x,4),gel(y,3),gel(y,4));
      setvalp(y,valp(x)); return;
    case t_QUAD:
      if (! ZX_equal(gel(x,1),gel(y,1))) pari_err_OP("",x,y);
      affii(gel(x,2),gel(y,2));
      affii(gel(x,3),gel(y,3)); return;
    case t_VEC: case t_COL: case t_MAT:
      lx = lg(x); if (lx != lg(y)) pari_err_DIM("gaffect");
      for (i=1; i<lx; i++) gaffect(gel(x,i),gel(y,i));
      return;
  }

  /* Various conversions. Avoid them, use specialized routines ! */

  if (!is_const_t(ty)) pari_err_TYPE2("=",x,y);
  switch(tx)
  {
    case t_INT:
      switch(ty)
      {
        case t_REAL:
          affir(x,y); break;

        case t_INTMOD:
          modiiz(x,gel(y,1),gel(y,2)); break;

        case t_COMPLEX:
          gaffect(x,gel(y,1)); gaffsg(0,gel(y,2)); break;

        case t_PADIC:
          if (!signe(x)) { padicaff0(y); break; }
          av = avma;
          setvalp(y, Z_pvalrem(x,gel(y,2),&p1));
          affii(modii(p1,gel(y,3)), gel(y,4));
          avma = av; break;

        case t_QUAD: gaffect(x,gel(y,2)); gaffsg(0,gel(y,3)); break;
        default: pari_err_TYPE2("=",x,y);
      }
      break;

    case t_REAL:
      switch(ty)
      {
        case t_COMPLEX: gaffect(x,gel(y,1)); gaffsg(0,gel(y,2)); break;
        default: pari_err_TYPE2("=",x,y);
      }
      break;

    case t_FRAC:
      switch(ty)
      {
        case t_REAL: rdiviiz(gel(x,1),gel(x,2), y); break;
        case t_INTMOD: av = avma;
          p1 = Fp_inv(gel(x,2),gel(y,1));
          affii(modii(mulii(gel(x,1),p1),gel(y,1)), gel(y,2));
          avma = av; break;
        case t_COMPLEX: gaffect(x,gel(y,1)); gaffsg(0,gel(y,2)); break;
        case t_PADIC:
          if (!signe(gel(x,1))) { padicaff0(y); break; }
          num = gel(x,1);
          den = gel(x,2);
          av = avma; vx = Z_pvalrem(num, gel(y,2), &num);
          if (!vx) vx = -Z_pvalrem(den,gel(y,2),&den);
          setvalp(y,vx);
          p1 = mulii(num,Fp_inv(den,gel(y,3)));
          affii(modii(p1,gel(y,3)), gel(y,4)); avma = av; break;
        case t_QUAD: gaffect(x,gel(y,2)); gaffsg(0,gel(y,3)); break;
        default: pari_err_TYPE2("=",x,y);
      }
      break;

    case t_COMPLEX:
      if (!gequal0(gel(x,2))) pari_err_TYPE2("=",x,y);
      gaffect(gel(x,1), y);
      break;

    case t_PADIC:
      switch(ty)
      {
        case t_INTMOD:
          av = avma; affii(padic_to_Fp(x, gel(y,1)), gel(y,2));
          avma = av; break;
        default: pari_err_TYPE2("=",x,y);
      }
      break;

    case t_QUAD:
      switch(ty)
      {
        case t_INT: case t_INTMOD: case t_FRAC: case t_PADIC:
          pari_err_TYPE2("=",x,y);

        case t_REAL:
          av = avma; affgr(quadtofp(x,realprec(y)), y); avma = av; break;
        case t_COMPLEX:
          ly = precision(y); if (!ly) pari_err_TYPE2("=",x,y);
          av = avma; gaffect(quadtofp(x,ly), y); avma = av; break;
        default: pari_err_TYPE2("=",x,y);
      }
    default: pari_err_TYPE2("=",x,y);
  }
}

/*******************************************************************/
/*                                                                 */
/*           CONVERSION QUAD --> REAL, COMPLEX OR P-ADIC           */
/*                                                                 */
/*******************************************************************/
GEN
quadtofp(GEN x, long prec)
{
  GEN z, Q, u = gel(x,2), v = gel(x,3);
  pari_sp av;
  if (prec < LOWDEFAULTPREC) prec = LOWDEFAULTPREC;
  if (isintzero(v)) return cxcompotor(u, prec);
  av = avma; Q = gel(x,1);
  z = itor(quad_disc(x), prec);
  if (signe(gel(Q,2)) < 0) /* Q[2] = -D/4 or (1-D)/4 */
  {
    z = subri(sqrtr(z), gel(Q,3));
    shiftr_inplace(z, -1);
  }
  else
  {
    z = sqrtr_abs(z); shiftr_inplace(z, -1);
    z = mkcomplex(gmul2n(negi(gel(Q,3)),-1), z);
  }/* z = (-b + sqrt(D)) / 2 */
  return gerepileupto(av, gadd(u, gmul(v,z)));
}

static GEN
qtop(GEN x, GEN p, long d)
{
  GEN z, D, P, b, u = gel(x,2), v = gel(x,3);
  pari_sp av;
  if (gequal0(v)) return cvtop(u, p, d);
  P = gel(x,1);
  b = gel(P,3);
  av = avma; D = quad_disc(x);
  if (absequaliu(p,2)) d += 2;
  z = Qp_sqrt(cvtop(D,p,d));
  if (!z) pari_err_SQRTN("Qp_sqrt",D);
  z = gmul2n(gsub(z, b), -1);

  z = gadd(u, gmul(v, z));
  if (typ(z) != t_PADIC) /* t_INTMOD for t_QUAD of t_INTMODs... */
    z = cvtop(z, p, d);
  return gerepileupto(av, z);
}
static GEN
ctop(GEN x, GEN p, long d)
{
  pari_sp av = avma;
  GEN z, u = gel(x,1), v = gel(x,2);
  if (isrationalzero(v)) return cvtop(u, p, d);
  z = Qp_sqrt(cvtop(gen_m1, p, d - gvaluation(v, p))); /* = I */
  if (!z) pari_err_SQRTN("Qp_sqrt",gen_m1);

  z = gadd(u, gmul(v, z));
  if (typ(z) != t_PADIC) /* t_INTMOD for t_COMPLEX of t_INTMODs... */
    z = cvtop(z, p, d);
  return gerepileupto(av, z);
}

/* cvtop2(stoi(s), y) */
GEN
cvstop2(long s, GEN y)
{
  GEN z, p = gel(y,2);
  long v, d = signe(gel(y,4))? precp(y): 0;
  if (!s) return zeropadic(p, d);
  v = z_pvalrem(s, p, &s);
  if (d <= 0) return zeropadic(p, v);
  z = cgetg(5, t_PADIC);
  z[1] = evalprecp(d) | evalvalp(v);
  gel(z,2) = p;
  gel(z,3) = gel(y,3);
  gel(z,4) = modsi(s, gel(y,3)); return z;
}

/* cvtop(x, gel(y,2), precp(y)), shallow */
GEN
cvtop2(GEN x, GEN y)
{
  GEN z, p = gel(y,2);
  long v, d = signe(gel(y,4))? precp(y): 0;
  switch(typ(x))
  {
    case t_INT:
      if (!signe(x)) return zeropadic(p, d);
      if (d <= 0) return zeropadic(p, Z_pval(x,p));
      v = Z_pvalrem(x, p, &x);
      z = cgetg(5, t_PADIC);
      z[1] = evalprecp(d) | evalvalp(v);
      gel(z,2) = p;
      gel(z,3) = gel(y,3);
      gel(z,4) = modii(x, gel(y,3)); return z;

    case t_INTMOD:
      v = Z_pval(gel(x,1),p); if (v > d) v = d;
      return cvtop(gel(x,2), p, v);

    case t_FRAC:
    {
      GEN num, den;
      if (d <= 0) return zeropadic(p, Q_pval(x,p));
      num = gel(x,1); v = Z_pvalrem(num, p, &num);
      den = gel(x,2); if (!v) v = -Z_pvalrem(den, p, &den);
      z = cgetg(5, t_PADIC);
      z[1] = evalprecp(d) | evalvalp(v);
      gel(z,2) = p;
      gel(z,3) = gel(y,3);
      if (!is_pm1(den)) num = mulii(num, Fp_inv(den, gel(y,3)));
      gel(z,4) = modii(num, gel(y,3)); return z;
    }
    case t_COMPLEX: return ctop(x, p, d);
    case t_QUAD:    return qtop(x, p, d);
  }
  pari_err_TYPE("cvtop2",x);
  return NULL; /* LCOV_EXCL_LINE */
}

/* assume is_const_t(tx) */
GEN
cvtop(GEN x, GEN p, long d)
{
  GEN z;
  long v;

  if (typ(p) != t_INT) pari_err_TYPE("cvtop",p);
  switch(typ(x))
  {
    case t_INT:
      if (!signe(x)) return zeropadic(p, d);
      if (d <= 0) return zeropadic(p, Z_pval(x,p));
      v = Z_pvalrem(x, p, &x);
      z = cgetg(5, t_PADIC);
      z[1] = evalprecp(d) | evalvalp(v);
      gel(z,2) = icopy(p);
      gel(z,3) = powiu(p, d);
      gel(z,4) = modii(x, gel(z,3)); return z; /* not memory-clean */

    case t_INTMOD:
      v = Z_pval(gel(x,1),p); if (v > d) v = d;
      return cvtop(gel(x,2), p, v);

    case t_FRAC:
    {
      GEN num, den;
      if (d <= 0) return zeropadic(p, Q_pval(x,p));
      num = gel(x,1); v = Z_pvalrem(num, p, &num);
      den = gel(x,2); if (!v) v = -Z_pvalrem(den, p, &den);
      z = cgetg(5, t_PADIC);
      z[1] = evalprecp(d) | evalvalp(v);
      gel(z,2) = icopy(p);
      gel(z,3) = powiu(p, d);
      if (!is_pm1(den)) num = mulii(num, Fp_inv(den, gel(z,3)));
      gel(z,4) = modii(num, gel(z,3)); return z; /* not memory-clean */
    }
    case t_COMPLEX: return ctop(x, p, d);
    case t_PADIC:
      p = gel(x,2); /* override */
      if (!signe(gel(x,4))) return zeropadic(p, d);
      z = cgetg(5,t_PADIC);
      z[1] = x[1]; setprecp(z,d);
      gel(z,2) = icopy(p);
      gel(z,3) = powiu(p, d);
      gel(z,4) = modii(gel(x,4), gel(z,3)); return z;

    case t_QUAD: return qtop(x, p, d);
  }
  pari_err_TYPE("cvtop",x);
  return NULL; /* LCOV_EXCL_LINE */
}

GEN
gcvtop(GEN x, GEN p, long r)
{
  long i, lx;
  GEN y;

  switch(typ(x))
  {
    case t_POL: case t_SER:
      y = cgetg_copy(x, &lx); y[1] = x[1];
      for (i=2; i<lx; i++) gel(y,i) = gcvtop(gel(x,i),p,r);
      return y;
    case t_POLMOD: case t_RFRAC: case t_VEC: case t_COL: case t_MAT:
      y = cgetg_copy(x, &lx);
      for (i=1; i<lx; i++) gel(y,i) = gcvtop(gel(x,i),p,r);
      return y;
  }
  return cvtop(x,p,r);
}

long
gexpo_safe(GEN x)
{
  long tx = typ(x), lx, e, f, i;

  switch(tx)
  {
    case t_INT:
      return expi(x);

    case t_FRAC:
      return expi(gel(x,1)) - expi(gel(x,2));

    case t_REAL:
      return expo(x);

    case t_COMPLEX:
      e = gexpo(gel(x,1));
      f = gexpo(gel(x,2)); return maxss(e, f);

    case t_QUAD: {
      GEN p = gel(x,1); /* mod = X^2 + {0,1}* X - {D/4, (1-D)/4})*/
      long d = 1 + expi(gel(p,2))/2; /* ~ expo(sqrt(D)) */
      e = gexpo(gel(x,2));
      f = gexpo(gel(x,3)) + d; return maxss(e, f);
    }
    case t_POL: case t_SER:
      lx = lg(x); f = -(long)HIGHEXPOBIT;
      for (i=2; i<lx; i++) { e=gexpo(gel(x,i)); if (e>f) f=e; }
      return f;
    case t_VEC: case t_COL: case t_MAT:
      lx = lg(x); f = -(long)HIGHEXPOBIT;
      for (i=1; i<lx; i++) { e=gexpo(gel(x,i)); if (e>f) f=e; }
      return f;
  }
  return -1-(long)HIGHEXPOBIT;
}
long
gexpo(GEN x)
{
  long e = gexpo_safe(x);
  if (e < -(long)HIGHEXPOBIT) pari_err_TYPE("gexpo",x);
  return e;
}
GEN
gpexponent(GEN x)
{
  long e = gexpo(x);
  return e == -(long)HIGHEXPOBIT? mkmoo(): stoi(e);
}

long
sizedigit(GEN x)
{
  return gequal0(x)? 0: (long) ((gexpo(x)+1) * LOG10_2) + 1;
}

/* normalize series. avma is not updated */
GEN
normalize(GEN x)
{
  long i, lx = lg(x), vx=varn(x), vp=valp(x);
  GEN y, z;

  if (typ(x) != t_SER) pari_err_TYPE("normalize",x);
  if (lx == 2) { setsigne(x,0); return x; }
  if (lx == 3) {
    z = gel(x,2);
    if (!gequal0(z)) { setsigne(x,1); return x; }
    if (isrationalzero(z)) return zeroser(vx,vp+1);
    if (isexactzero(z)) {
      /* dangerous case: already normalized ? */
      if (!signe(x)) return x;
      setvalp(x,vp+1); /* no: normalize */
    }
    setsigne(x,0); return x;
  }
  for (i=2; i<lx; i++)
    if (! isrationalzero(gel(x,i))) break;
  if (i == lx) return zeroser(vx,lx-2+vp);
  z = gel(x,i);
  while (i<lx && isexactzero(gel(x,i))) i++;
  if (i == lx)
  {
    i -= 3; y = x + i;
    stackdummy((pari_sp)y, (pari_sp)x);
    gel(y,2) = z;
    y[1] = evalsigne(0) | evalvalp(lx-2+vp) | evalvarn(vx);
    y[0] = evaltyp(t_SER) | _evallg(3);
    return y;
  }

  i -= 2; y = x + i; lx -= i;
  y[1] = evalsigne(1) | evalvalp(vp+i) | evalvarn(vx);
  y[0] = evaltyp(t_SER) | evallg(lx);

  stackdummy((pari_sp)y, (pari_sp)x);
  for (i = 2; i < lx; i++)
    if (!gequal0(gel(y, i))) return y;
  setsigne(y, 0); return y;
}

GEN
normalizepol_approx(GEN x, long lx)
{
  long i;
  for (i = lx-1; i>1; i--)
    if (! gequal0(gel(x,i))) break;
  stackdummy((pari_sp)(x + lg(x)), (pari_sp)(x + i+1));
  setlg(x, i+1); setsigne(x, i!=1); return x;
}

GEN
normalizepol_lg(GEN x, long lx)
{
  long i, LX = 0;
  GEN KEEP = NULL;

  for (i = lx-1; i>1; i--)
  {
    GEN z = gel(x,i);
    if (! gequal0(z) ) {
      if (!LX) LX = i+1;
      stackdummy((pari_sp)(x + lg(x)), (pari_sp)(x + LX));
      x[0] = evaltyp(t_POL) | evallg(LX);
      setsigne(x,1); return x;
    } else if (!isexactzero(z)) {
      if (!LX) LX = i+1; /* to be kept as leading coeff */
    } else if (!isrationalzero(z))
      KEEP = z; /* to be kept iff all other coeffs are exact 0s */
  }
  if (!LX) {
    if (KEEP) { /* e.g. Pol(Mod(0,2)) */
      gel(x,2) = KEEP;
      LX = 3;
    } else
      LX = 2; /* Pol(0) */
  }
  stackdummy((pari_sp)(x + lg(x)), (pari_sp)(x + LX));
  x[0] = evaltyp(t_POL) | evallg(LX);
  setsigne(x,0); return x;
}

/* normalize polynomial x in place */
GEN
normalizepol(GEN x)
{
  return normalizepol_lg(x, lg(x));
}

int
gsigne(GEN x)
{
  switch(typ(x))
  {
    case t_INT: case t_REAL: return signe(x);
    case t_FRAC: return signe(gel(x,1));
    case t_QUAD:
    {
      pari_sp av = avma;
      GEN T = gel(x,1), a = gel(x,2), b = gel(x,3);
      long sa, sb;
      if (signe(gel(T,2)) > 0) break;
      a = gmul2n(a,1);
      if (signe(gel(T,3))) a = gadd(a,b);
      /* a + b sqrt(D) > 0 ? */
      sa = gsigne(a);
      sb = gsigne(b); if (sa == sb) { avma = av; return sa; }
      if (sa == 0) { avma = av; return sb; }
      if (sb == 0) { avma = av; return sa; }
      /* different signs, take conjugate expression */
      sb = gsigne(gsub(gsqr(a), gmul(quad_disc(x), gsqr(b))));
      avma = av; return sb * sa;
    }
    case t_INFINITY: return inf_get_sign(x);
  }
  pari_err_TYPE("gsigne",x);
  return 0; /* LCOV_EXCL_LINE */
}

/*******************************************************************/
/*                                                                 */
/*                              LISTS                              */
/*                                                                 */
/*******************************************************************/
/* make sure L can hold l elements, at least doubling the previous max number
 * of components. */
static void
ensure_nb(GEN L, long l)
{
  long nmax = list_nmax(L), i, lw;
  GEN v, w;
  if (l <= nmax) return;
  if (nmax)
  {
    nmax <<= 1;
    if (l > nmax) nmax = l;
    w = list_data(L); lw = lg(w);
    v = newblock(nmax+1);
    v[0] = w[0];
    for (i=1; i < lw; i++) gel(v,i) = gel(w, i);
    killblock(w);
  }
  else /* unallocated */
  {
    nmax = 32;
    if (list_data(L))
      pari_err(e_MISC, "store list in variable before appending elements");
    v = newblock(nmax+1);
    v[0] = evaltyp(t_VEC) | _evallg(1);
  }
  list_data(L) = v;
  L[1] = evaltyp(list_typ(L))|evallg(nmax);
}

void
listkill(GEN L)
{

  if (typ(L) != t_LIST) pari_err_TYPE("listkill",L);
  if (list_nmax(L)) {
    GEN v = list_data(L);
    long i, l = lg(v);
    for (i=1; i<l; i++) gunclone_deep(gel(v,i));
    killblock(v);
    L[1] = evaltyp(list_typ(L));
    list_data(L) = NULL;
  }
}

GEN
mklist_typ(long t)
{
  GEN L = cgetg(3,t_LIST);
  L[1] = evaltyp(t);
  list_data(L) = NULL; return L;
}

GEN
mklist(void)
{
  return mklist_typ(t_LIST_RAW);
}

GEN
mkmap(void)
{
  return mklist_typ(t_LIST_MAP);
}

/* return a list with single element x, allocated on stack */
GEN
mklistcopy(GEN x)
{
  GEN y = mklist();
  list_data(y) = mkveccopy(x);
  return y;
}

GEN
listcreate_gp(long n)
{
  (void) n; return mklist();
}

GEN
listput(GEN L, GEN x, long index)
{
  long l;
  GEN z;

  if (index < 0) pari_err_COMPONENT("listput", "<", gen_0, stoi(index));
  z = list_data(L);
  l = z? lg(z): 1;

  x = gclone(x);
  if (!index || index >= l)
  {
    ensure_nb(L, l);
    z = list_data(L); /* it may change ! */
    index = l;
    l++;
  } else
    gunclone_deep( gel(z, index) );
  gel(z,index) = x;
  z[0] = evaltyp(t_VEC) | evallg(l); /*must be after gel(z,index) is set*/
  return gel(z,index);
}

GEN
listput0(GEN L, GEN x, long index)
{
  if (typ(L) != t_LIST || list_typ(L) != t_LIST_RAW)
    pari_err_TYPE("listput",L);
  return listput(L, x, index);
}

GEN
listinsert(GEN L, GEN x, long index)
{
  long l, i;
  GEN z;

  if (typ(L) != t_LIST || list_typ(L) != t_LIST_RAW)
    pari_err_TYPE("listinsert",L);
  z = list_data(L); l = z? lg(z): 1;
  if (index <= 0) pari_err_COMPONENT("listinsert", "<=", gen_0, stoi(index));
  if (index > l) pari_err_COMPONENT("listinsert", ">", stoi(l), stoi(index));
  ensure_nb(L, l);
  BLOCK_SIGINT_START
  z = list_data(L);
  for (i=l; i > index; i--) gel(z,i) = gel(z,i-1);
  z[0] = evaltyp(t_VEC) | evallg(l+1);
  gel(z,index) = gclone(x);
  BLOCK_SIGINT_END
  return gel(z,index);
}

void
listpop(GEN L, long index)
{
  long l, i;
  GEN z;

  if (typ(L) != t_LIST) pari_err_TYPE("listinsert",L);
  if (index < 0) pari_err_COMPONENT("listpop", "<", gen_0, stoi(index));
  z = list_data(L);
  if (!z || (l = lg(z)-1) == 0) return;

  if (!index || index > l) index = l;
  BLOCK_SIGINT_START
  gunclone_deep( gel(z, index) );
  z[0] = evaltyp(t_VEC) | evallg(l);
  for (i=index; i < l; i++) z[i] = z[i+1];
  BLOCK_SIGINT_END
}

void
listpop0(GEN L, long index)
{
  if (typ(L) != t_LIST || list_typ(L) != t_LIST_RAW)
    pari_err_TYPE("listpop",L);
  listpop(L, index);
}

/* return a copy fully allocated on stack. gclone from changevalue is
 * supposed to malloc() it */
GEN
gtolist(GEN x)
{
  GEN y;

  if (!x) return mklist();
  switch(typ(x))
  {
    case t_VEC: case t_COL:
      y = mklist();
      if (lg(x) == 1) return y;
      list_data(y) = gcopy(x);
      settyp(list_data(y), t_VEC);
      return y;
    case t_LIST:
      y = mklist();
      list_data(y) = list_data(x)? gcopy(list_data(x)): NULL;
      return y;
    default:
      return mklistcopy(x);
  }
}

void
listsort(GEN L, long flag)
{
  long i, l;
  pari_sp av = avma;
  GEN perm, v, vnew;

  if (typ(L) != t_LIST) pari_err_TYPE("listsort",L);
  v = list_data(L); l = v? lg(v): 1;
  if (l < 3) return;
  if (flag)
  {
    long lnew;
    perm = gen_indexsort_uniq(L, (void*)&cmp_universal, cmp_nodata);
    lnew = lg(perm); /* may have changed since 'uniq' */
    vnew = cgetg(lnew,t_VEC);
    for (i=1; i<lnew; i++) {
      long c = perm[i];
      gel(vnew,i) = gel(v,c);
      gel(v,c) = NULL;
    }
    if (l != lnew) { /* was shortened */
      for (i=1; i<l; i++)
        if (gel(v,i)) gunclone_deep(gel(v,i));
      l = lnew;
    }
  }
  else
  {
    perm = gen_indexsort(L, (void*)&cmp_universal, cmp_nodata);
    vnew = cgetg(l,t_VEC);
    for (i=1; i<l; i++) gel(vnew,i) = gel(v,perm[i]);
  }
  for (i=1; i<l; i++) gel(v,i) = gel(vnew,i);
  v[0] = vnew[0]; avma = av;
}
