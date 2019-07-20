#line 2 "../src/kernel/none/cmp.c"
/* Copyright (C) 2002-2003  The PARI group.

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
/**                      Comparison routines                       **/
/**                                                                **/
/********************************************************************/

/*They depend on cmpiispec and equaliispec in mp.c*/

int
equalii(GEN x, GEN y)
{
  if ((x[1] & (LGBITS|SIGNBITS)) != (y[1] & (LGBITS|SIGNBITS))) return 0;
  return equaliispec(x+2, y+2, lgefint(x)-2, lgefint(y)-2);
}

int
cmpii(GEN x, GEN y)
{
  const long sx = signe(x), sy = signe(y);
  if (sx<sy) return -1;
  if (sx>sy) return 1;
  if (!sx) return 0;
  if (sx>0)
    return cmpiispec(x+2, y+2, lgefint(x)-2, lgefint(y)-2);
  else
    return -cmpiispec(x+2, y+2, lgefint(x)-2, lgefint(y)-2);
}

int
equalrr(GEN x, GEN y)
{
  long lx, ly, i;

  if (!signe(x)) {
    if (!signe(y)) return 1; /* all zeroes are equal */
    return expo(x) >= expo(y);
  }
  if (!signe(y))
    return expo(y) >= expo(x);

  if (x[1] != y[1]) return 0;

  lx = lg(x);
  ly = lg(y);
  if (lx < ly)
  {
    i=2; while (i<lx && x[i]==y[i]) i++;
    if (i<lx) return 0;
    for (; i < ly; i++) if (y[i]) return 0;
  }
  else
  {
    i=2; while (i<ly && x[i]==y[i]) i++;
    if (i<ly) return 0;
    for (; i < lx; i++) if (x[i]) return 0;
  }
  return 1;
}

int
cmprr(GEN x, GEN y)
{
  const long sx = signe(x), sy = signe(y);
  long ex,ey,lx,ly,lz,i;

  if (!sx) {
    if (!sy || expo(x) >= expo(y)) return 0;
    return sy > 0? -1: 1;
  }
  if (!sy) {
    if (expo(y) >= expo(x)) return 0;
    return sx > 0? 1: -1;
  }
  if (sx<sy) return -1;
  if (sx>sy) return 1;

  ex=expo(x); ey=expo(y);
  if (ex>ey) return sx;
  if (ex<ey) return -sx;

  lx=lg(x); ly=lg(y); lz = (lx<ly)?lx:ly;
  i=2; while (i<lz && x[i]==y[i]) i++;
  if (i<lz) return ((ulong)x[i] > (ulong)y[i]) ? sx : -sx;
  if (lx>=ly)
  {
    while (i<lx && !x[i]) i++;
    return (i==lx) ? 0 : sx;
  }
  while (i<ly && !y[i]) i++;
  return (i==ly) ? 0 : -sx;
}

/* x and y are integers. Return 1 if |x| == |y|, 0 otherwise */
int
absequalii(GEN x, GEN y)
{
  if (!signe(x)) return !signe(y);
  if (!signe(y)) return 0;
  return equaliispec(x+2, y+2, lgefint(x)-2, lgefint(y)-2);
}

/* x and y are integers. Return sign(|x| - |y|) */
int
abscmpii(GEN x, GEN y)
{
  if (!signe(x)) return signe(y)? -1: 0;
  if (!signe(y)) return 1;
  return cmpiispec(x+2, y+2, lgefint(x)-2, lgefint(y)-2);
}

/* x and y are reals. Return sign(|x| - |y|) */
int
abscmprr(GEN x, GEN y)
{
  long ex,ey,lx,ly,lz,i;

  if (!signe(x)) return signe(y)? -1: 0;
  if (!signe(y)) return 1;

  ex=expo(x); ey=expo(y);
  if (ex>ey) return  1;
  if (ex<ey) return -1;

  lx=lg(x); ly=lg(y); lz = (lx<ly)?lx:ly;
  i=2; while (i<lz && x[i]==y[i]) i++;
  if (i<lz) return ((ulong)x[i] > (ulong)y[i])? 1: -1;
  if (lx>=ly)
  {
    while (i<lx && !x[i]) i++;
    return (i==lx)? 0: 1;
  }
  while (i<ly && !y[i]) i++;
  return (i==ly)? 0: -1;
}

