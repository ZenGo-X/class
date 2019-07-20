#line 2 "../src/kernel/none/gcd.c"
/* Copyright (C) 2003  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/* assume y > x > 0. return y mod x */
static ulong
resiu(GEN y, ulong x)
{
  long i, ly = lgefint(y);
  ulong xi = get_Fl_red(x);
  LOCAL_HIREMAINDER;

  hiremainder = 0;
  for (i=2; i<ly; i++) (void)divll_pre(y[i],x,xi);
  return hiremainder;
}

/* Assume x>y>0, both of them odd. return x-y if x=y mod 4, x+y otherwise */
static void
gcd_plus_minus(GEN x, GEN y, GEN res)
{
  pari_sp av = avma;
  long lx = lgefint(x)-1;
  long ly = lgefint(y)-1, lt,m,i;
  GEN t;

  if ((x[lx]^y[ly]) & 3) /* x != y mod 4*/
    t = addiispec(x+2,y+2,lx-1,ly-1);
  else
    t = subiispec(x+2,y+2,lx-1,ly-1);

  lt = lgefint(t)-1; while (!t[lt]) lt--;
  m = vals(t[lt]); lt++;
  if (m == 0) /* 2^32 | t */
  {
    for (i = 2; i < lt; i++) res[i] = t[i];
  }
  else if (t[2] >> m)
  {
    shift_right(res,t, 2,lt, 0,m);
  }
  else
  {
    lt--; t++;
    shift_right(res,t, 2,lt, t[1],m);
  }
  res[1] = evalsigne(1)|evallgefint(lt);
  avma = av;
}

/* uses modified right-shift binary algorithm now --GN 1998Jul23 */
GEN
gcdii(GEN a, GEN b)
{
  long v, w;
  pari_sp av;
  GEN t, p1;

  switch (abscmpii(a,b))
  {
    case 0: return absi(a);
    case -1: swap(a,b);
  }
  if (!signe(b)) return absi(a);
  /* here |a|>|b|>0. Try single precision first */
  if (lgefint(a)==3)
    return igcduu((ulong)a[2], (ulong)b[2]);
  if (lgefint(b)==3)
  {
    ulong u = resiu(a,(ulong)b[2]);
    if (!u) return absi(b);
    return igcduu((ulong)b[2], u);
  }

  /* larger than gcd: "avma=av" gerepile (erasing t) is valid */
  av = avma; (void)new_chunk(lgefint(b)); /* HACK */
  t = remii(a,b);
  if (!signe(t)) { avma = av; return absi(b); }

  a = b; b = t;
  v = vali(a); a = shifti(a,-v); setabssign(a);
  w = vali(b); b = shifti(b,-w); setabssign(b);
  if (w < v) v = w;
  switch(abscmpii(a,b))
  {
    case  0: avma = av; a = shifti(a,v); return a;
    case -1: swap(a,b);
  }
  if (is_pm1(b)) { avma = av; return int2n(v); }

  /* we have three consecutive memory locations: a,b,t.
   * All computations are done in place */

  /* a and b are odd now, and a>b>1 */
  while (lgefint(a) > 3)
  {
    /* if a=b mod 4 set t=a-b, otherwise t=a+b, then strip powers of 2 */
    /* so that t <= (a+b)/4 < a/2 */
    gcd_plus_minus(a,b, t);
    if (is_pm1(t)) { avma = av; return int2n(v); }
    switch(abscmpii(t,b))
    {
      case -1: p1 = a; a = b; b = t; t = p1; break;
      case  1: swap(a,t); break;
      case  0: avma = av; b = shifti(b,v); return b;
    }
  }
  {
    long r[] = {evaltyp(t_INT)|_evallg(3), evalsigne(1)|evallgefint(3), 0};
    r[2] = (long) gcduodd((ulong)b[2], (ulong)a[2]);
    avma = av; return shifti(r,v);
  }
}
