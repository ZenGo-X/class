#line 2 "../src/kernel/none/add.c"
/* Copyright (C) 2002-2003  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

INLINE GEN
icopy_sign(GEN x, long sx)
{
  GEN y=icopy(x);
  setsigne(y,sx);
  return y;
}

GEN
addsi_sign(long x, GEN y, long sy)
{
  long sx,ly;
  GEN z;

  if (!x) return icopy_sign(y, sy);
  if (!sy) return stoi(x);
  if (x<0) { sx=-1; x=-x; } else sx=1;
  if (sx==sy)
  {
    z = adduispec(x,y+2, lgefint(y)-2);
    setsigne(z,sy); return z;
  }
  ly=lgefint(y);
  if (ly==3)
  {
    const long d = (long)(uel(y,2) - (ulong)x);
    if (!d) return gen_0;
    z=cgeti(3);
    if (y[2] < 0 || d > 0) {
      z[1] = evalsigne(sy) | evallgefint(3);
      z[2] = d;
    }
    else {
      z[1] = evalsigne(-sy) | evallgefint(3);
      z[2] =-d;
    }
    return z;
  }
  z = subiuspec(y+2,x, ly-2);
  setsigne(z,sy); return z;
}
GEN
addui_sign(ulong x, GEN y, long sy)
{
  long ly;
  GEN z;

  if (!x) return icopy_sign(y, sy);
  if (!sy) return utoipos(x);
  if (sy == 1) return adduispec(x,y+2, lgefint(y)-2);
  ly=lgefint(y);
  if (ly==3)
  {
    const ulong t = y[2];
    if (x == t) return gen_0;
    z=cgeti(3);
    if (x < t) {
      z[1] = evalsigne(-1) | evallgefint(3);
      z[2] = t - x;
    }
    else {
      z[1] = evalsigne(1) | evallgefint(3);
      z[2] = x - t;
    }
    return z;
  }
  z = subiuspec(y+2,x, ly-2);
  setsigne(z,-1); return z;
}

/* return gen_0 when the sign is 0 */
GEN
addii_sign(GEN x, long sx, GEN y, long sy)
{
  long lx,ly;
  GEN z;

  if (!sx) return sy? icopy_sign(y, sy): gen_0;
  if (!sy) return icopy_sign(x, sx);
  lx = lgefint(x);
  ly = lgefint(y);
  if (sx==sy)
    z = addiispec(x+2,y+2,lx-2,ly-2);
  else
  { /* sx != sy */
    long i = cmpiispec(x+2,y+2,lx-2,ly-2);
    if (!i) return gen_0;
    /* we must ensure |x| > |y| for subiispec */
    if (i < 0) {
      sx = sy;
      z = subiispec(y+2,x+2,ly-2,lx-2);
    }
    else
      z = subiispec(x+2,y+2,lx-2,ly-2);
  }
  setsigne(z,sx); return z;
}

INLINE GEN
rcopy_sign(GEN x, long sx) { GEN y = rcopy(x); setsigne(y,sx); return y; }

GEN
addir_sign(GEN x, long sx, GEN y, long sy)
{
  long e, l, ly;
  GEN z;

  if (!sx) return rcopy_sign(y, sy);
  e = expo(y) - expi(x);
  if (!sy)
  {
    if (e >= 0) return rcopy_sign(y, sy);
    z = itor(x, nbits2prec(-e));
    setsigne(z, sx); return z;
  }

  ly = lg(y);
  if (e > 0)
  {
    l = ly - divsBIL(e);
    if (l < 3) return rcopy_sign(y, sy);
  }
  else l = ly + nbits2extraprec(-e);
  z = (GEN)avma;
  y = addrr_sign(itor(x,l), sx, y, sy);
  ly = lg(y); while (ly--) *--z = y[ly];
  avma = (pari_sp)z; return z;
}

static GEN
addsr_sign(long x, GEN y, long sy)
{
  long e, l, ly, sx;
  GEN z;

  if (!x) return rcopy_sign(y, sy);
  if (x < 0) { sx = -1; x = -x; } else sx = 1;
  e = expo(y) - expu(x);
  if (!sy)
  {
    if (e >= 0) return rcopy_sign(y, sy);
    if (sx == -1) x = -x;
    return stor(x, nbits2prec(-e));
  }

  ly = lg(y);
  if (e > 0)
  {
    l = ly - divsBIL(e);
    if (l < 3) return rcopy_sign(y, sy);
  }
  else l = ly + nbits2extraprec(-e);
  z = (GEN)avma;
  y = addrr_sign(stor(x,l), sx, y, sy);
  ly = lg(y); while (ly--) *--z = y[ly];
  avma = (pari_sp)z; return z;
}

GEN
addsr(long x, GEN y) { return addsr_sign(x, y, signe(y)); }

GEN
subsr(long x, GEN y) { return addsr_sign(x, y, -signe(y)); }

GEN
addrr_sign(GEN x, long sx, GEN y, long sy)
{
  long lx, ex = expo(x);
  long ly, ey = expo(y), e = ey - ex;
  long i, j, lz, ez, m;
  int extend, f2;
  GEN z;
  LOCAL_OVERFLOW;

  if (!sy)
  {
    if (!sx)
    {
      if (e > 0) ex = ey;
      return real_0_bit(ex);
    }
    if (e >= 0) return real_0_bit(ey);
    lz = nbits2prec(-e);
    lx = lg(x); if (lz > lx) lz = lx;
    z = cgetr(lz); while(--lz) z[lz] = x[lz];
    setsigne(z,sx); return z;
  }
  if (!sx)
  {
    if (e <= 0) return real_0_bit(ex);
    lz = nbits2prec(e);
    ly = lg(y); if (lz > ly) lz = ly;
    z = cgetr(lz); while (--lz) z[lz] = y[lz];
    setsigne(z,sy); return z;
  }

  if (e < 0) { swap(x,y); lswap(sx,sy); ey=ex; e=-e; }
  /* now ey >= ex */
  lx = lg(x);
  ly = lg(y);
  /* If exponents differ, need to shift one argument, here x. If
   * extend = 1: extension of x,z by m < BIL bits (round to 1 word) */
  /* in this case, lz = lx + d + 1, otherwise lx + d */
  extend = 0;
  if (e)
  {
    long d = dvmdsBIL(e, &m), l = ly-d;
    if (l <= 2) return rcopy_sign(y, sy);
    if (l > lx) { lz = lx + d + 1; extend = 1; }
    else        { lz = ly; lx = l; }
    if (m)
    { /* shift x right m bits */
      const pari_sp av = avma;
      const ulong sh = BITS_IN_LONG-m;
      GEN p1 = x; x = new_chunk(lx + lz + 1);
      shift_right(x,p1,2,lx, 0,m);
      if (extend) uel(x,lx) = uel(p1,lx-1) << sh;
      avma = av; /* HACK: cgetr(lz) will not overwrite x */
    }
  }
  else
  { /* d = 0 */
    m = 0;
    if (lx > ly) lx = ly;
    lz = lx;
  }

  if (sx == sy)
  { /* addition */
    i = lz-1;
    j = lx-1;
    if (extend) {
      ulong garde = addll(x[lx], y[i]);
      if (m < 4) /* don't extend for few correct bits */
        z = cgetr(--lz);
      else
      {
        z = cgetr(lz);
        z[i] = garde;
      }
    }
    else
    {
      z = cgetr(lz);
      z[i] = addll(x[j], y[i]); j--;
    }
    i--;
    for (; j>=2; i--,j--) z[i] = addllx(x[j],y[i]);
    if (overflow)
    {
      z[1] = 1; /* stops since z[1] != 0 */
      for (;;) { z[i] = uel(y,i)+1; if (z[i--]) break; }
      if (i <= 0)
      {
        shift_right(z,z, 2,lz, 1,1);
        z[1] = evalsigne(sx) | evalexpo(ey+1); return z;
      }
    }
    for (; i>=2; i--) z[i] = y[i];
    z[1] = evalsigne(sx) | evalexpo(ey); return z;
  }

  /* subtraction */
  if (e) f2 = 1;
  else
  {
    i = 2; while (i < lx && x[i] == y[i]) i++;
    if (i==lx) return real_0_bit(ey+1 - prec2nbits(lx));
    f2 = (uel(y,i) > uel(x,i));
  }
  /* result is non-zero. f2 = (y > x) */
  i = lz-1; z = cgetr(lz);
  if (f2)
  {
    j = lx-1;
    if (extend) z[i] = subll(y[i], x[lx]);
    else        z[i] = subll(y[i], x[j--]);
    for (i--; j>=2; i--) z[i] = subllx(y[i], x[j--]);
    if (overflow) /* stops since y[1] != 0 */
      for (;;) { z[i] = uel(y,i)-1; if (y[i--]) break; }
    for (; i>=2; i--) z[i] = y[i];
    sx = sy;
  }
  else
  {
    if (extend) z[i] = subll(x[lx], y[i]);
    else        z[i] = subll(x[i],  y[i]);
    for (i--; i>=2; i--) z[i] = subllx(x[i], y[i]);
  }

  x = z+2; i = 0; while (!x[i]) i++;
  lz -= i; z += i;
  j = bfffo(z[2]); /* need to shift left by j bits to normalize mantissa */
  ez = ey - (j | (i * BITS_IN_LONG));
  if (extend)
  { /* z was extended by d+1 words [should be e bits = d words + m bits] */
    /* not worth keeping extra word if less than 5 significant bits in there */
    if (m - j < 5 && lz > 3)
    { /* shorten z */
      ulong last = (ulong)z[--lz]; /* cancelled word */

      /* if we need to shift anyway, shorten from left
       * If not, shorten from right, neutralizing last word of z */
      if (j == 0)
        /* stackdummy((pari_sp)(z + lz+1), (pari_sp)(z + lz)); */
        z[lz] = evaltyp(t_VECSMALL) | _evallg(1);
      else
      {
        GEN t = z;
        z++; shift_left(z,t,2,lz-1, last,j);
      }
      if ((last<<j) & HIGHBIT)
      { /* round up */
        i = lz-1;
        while (++((ulong*)z)[i] == 0 && i > 1) i--;
        if (i == 1) { ez++; z[2] = (long)HIGHBIT; }
      }
    }
    else if (j) shift_left(z,z,2,lz-1, 0,j);
  }
  else if (j) shift_left(z,z,2,lz-1, 0,j);
  z[1] = evalsigne(sx) | evalexpo(ez);
  z[0] = evaltyp(t_REAL) | evallg(lz);
  avma = (pari_sp)z; return z;
}
