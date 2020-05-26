#line 2 "../src/kernel/none/mp_indep.c"
/* Copyright (C) 2000  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/* Find c such that 1=c*b mod 2^BITS_IN_LONG, assuming b odd (unchecked) */
ulong
invmod2BIL(ulong b)
{
  static int tab[] = { 0, 0, 0, 8, 0, 8, 0, 0 };
  ulong x = b + tab[b & 7]; /* b^(-1) mod 2^4 */

  /* Newton applied to 1/x - b = 0 */
#ifdef LONG_IS_64BIT
  x = x*(2-b*x); /* one more pass necessary */
#endif
  x = x*(2-b*x);
  x = x*(2-b*x); return x*(2-b*x);
}

void
affrr(GEN x, GEN y)
{
  long i, lx, ly = lg(y);
  if (!signe(x))
  {
    y[1] = evalexpo(minss(expo(x), -bit_accuracy(ly)));
    return;
  }
  y[1] = x[1]; lx = lg(x);
  if (lx <= ly)
  {
    for (i=2; i<lx; i++) y[i]=x[i];
    for (   ; i<ly; i++) y[i]=0;
    return;
  }
  for (i=2; i<ly; i++) y[i]=x[i];
  /* lx > ly: round properly */
  if (x[ly] & HIGHBIT) roundr_up_ip(y, ly);
}

GEN
trunc2nr(GEN x, long n)
{
  long ex;
  if (!signe(x)) return gen_0;
  ex = expo(x) + n; if (ex < 0) return gen_0;
  return mantissa2nr(x, ex - bit_prec(x) + 1);
}

/* x a t_REAL, x = i/2^e, i a t_INT */
GEN
mantissa_real(GEN x, long *e)
{
  *e = bit_prec(x)-1-expo(x);
  return mantissa2nr(x, 0);
}

GEN
mului(ulong x, GEN y)
{
  long s = signe(y);
  GEN z;

  if (!s || !x) return gen_0;
  z = muluispec(x, y+2, lgefint(y)-2);
  setsigne(z,s); return z;
}

GEN
mulsi(long x, GEN y)
{
  long s = signe(y);
  GEN z;

  if (!s || !x) return gen_0;
  if (x<0) { s = -s; x = -x; }
  z = muluispec((ulong)x, y+2, lgefint(y)-2);
  setsigne(z,s); return z;
}

GEN
mulss(long x, long y)
{
  long p1;
  LOCAL_HIREMAINDER;

  if (!x || !y) return gen_0;
  if (x<0) {
    x = -x;
    if (y<0) { y = -y; p1 = mulll(x,y); return uutoi(hiremainder, p1); }
    p1 = mulll(x,y); return uutoineg(hiremainder, p1);
  } else {
    if (y<0) { y = -y; p1 = mulll(x,y); return uutoineg(hiremainder, p1); }
    p1 = mulll(x,y); return uutoi(hiremainder, p1);
  }
}
GEN
sqrs(long x)
{
  long p1;
  LOCAL_HIREMAINDER;

  if (!x) return gen_0;
  if (x<0) x = -x;
  p1 = mulll(x,x); return uutoi(hiremainder, p1);
}
GEN
muluu(ulong x, ulong y)
{
  long p1;
  LOCAL_HIREMAINDER;

  if (!x || !y) return gen_0;
  p1 = mulll(x,y); return uutoi(hiremainder, p1);
}
GEN
sqru(ulong x)
{
  long p1;
  LOCAL_HIREMAINDER;

  if (!x) return gen_0;
  p1 = mulll(x,x); return uutoi(hiremainder, p1);
}

/* assume x > 1, y != 0. Return u * y with sign s */
static GEN
mulur_2(ulong x, GEN y, long s)
{
  long m, sh, i, lx = lg(y), e = expo(y);
  GEN z = cgetr(lx);
  ulong garde;
  LOCAL_HIREMAINDER;

  y--; garde = mulll(x,y[lx]);
  for (i=lx-1; i>=3; i--) z[i]=addmul(x,y[i]);
  z[2]=hiremainder; /* != 0 since y normalized and |x| > 1 */
  sh = bfffo(hiremainder); m = BITS_IN_LONG-sh;
  if (sh) shift_left(z,z, 2,lx-1, garde,sh);
  z[1] = evalsigne(s) | evalexpo(m+e);
  if ((garde << sh) & HIGHBIT) roundr_up_ip(z, lx);
  return z;
}

INLINE GEN
mul0r(GEN x)
{
  long l = lg(x), e = expo(x);
  e = (l > 2)? -prec2nbits(l) + e: (e < 0? 2*e: 0);
  return real_0_bit(e);
}
/* lg(x) > 2 */
INLINE GEN
div0r(GEN x) {
  long l = lg(x), e = expo(x);
  return real_0_bit(-prec2nbits(l) - e);
}

GEN
mulsr(long x, GEN y)
{
  long s;

  if (!x) return mul0r(y);
  s = signe(y);
  if (!s)
  {
    if (x < 0) x = -x;
    return real_0_bit( expo(y) + expu(x) );
  }
  if (x==1)  return rcopy(y);
  if (x==-1) return negr(y);
  if (x < 0)
    return mulur_2((ulong)-x, y, -s);
  else
    return mulur_2((ulong)x, y, s);
}

GEN
mulur(ulong x, GEN y)
{
  long s;

  if (!x) return mul0r(y);
  s = signe(y);
  if (!s) return real_0_bit( expo(y) + expu(x) );
  if (x==1) return rcopy(y);
  return mulur_2(x, y, s);
}

INLINE void
mulrrz_end(GEN z, GEN hi, long lz, long sz, long ez, ulong garde)
{
  long i;
  if (hi[2] < 0)
  {
    if (z != hi)
      for (i=2; i<lz ; i++) z[i] = hi[i];
    ez++;
  }
  else
  {
    shift_left(z,hi,2,lz-1, garde, 1);
    garde <<= 1;
  }
  if (garde & HIGHBIT)
  { /* round to nearest */
    i = lz; do ((ulong*)z)[--i]++; while (i>1 && z[i]==0);
    if (i == 1) { z[2] = (long)HIGHBIT; ez++; }
  }
  z[1] = evalsigne(sz)|evalexpo(ez);
}
/* mulrrz_end for lz = 3, minor simplifications. z[2]=hiremainder from mulll */
INLINE void
mulrrz_3end(GEN z, long sz, long ez, ulong garde)
{
  if (z[2] < 0)
  { /* z2 < (2^BIL-1)^2 / 2^BIL, hence z2+1 != 0 */
    if (garde & HIGHBIT) z[2]++; /* round properly */
    ez++;
  }
  else
  {
    uel(z,2) = (uel(z,2)<<1) | (garde>>(BITS_IN_LONG-1));
    if (garde & (1UL<<(BITS_IN_LONG-2)))
    {
      uel(z,2)++; /* round properly, z2+1 can overflow */
      if (!uel(z,2)) { uel(z,2) = HIGHBIT; ez++; }
    }
  }
  z[1] = evalsigne(sz)|evalexpo(ez);
}

/* set z <-- x^2 != 0, floating point multiplication.
 * lz = lg(z) = lg(x) */
INLINE void
sqrz_i(GEN z, GEN x, long lz)
{
  long ez = 2*expo(x);
  long i, j, lzz, p1;
  ulong garde;
  GEN x1;
  LOCAL_HIREMAINDER;
  LOCAL_OVERFLOW;

  if (lz > SQRR_SQRI_LIMIT)
  {
    pari_sp av = avma;
    GEN hi = sqrispec_mirror(x+2, lz-2);
    mulrrz_end(z, hi, lz, 1, ez, hi[lz]);
    avma = av; return;
  }
  if (lz == 3)
  {
    garde = mulll(x[2],x[2]);
    z[2] = hiremainder;
    mulrrz_3end(z, 1, ez, garde);
    return;
  }

  lzz = lz-1; p1 = x[lzz];
  if (p1)
  {
    (void)mulll(p1,x[3]);
    garde = addmul(p1,x[2]);
    z[lzz] = hiremainder;
  }
  else
  {
    garde = 0;
    z[lzz] = 0;
  }
  for (j=lz-2, x1=x-j; j>=3; j--)
  {
    p1 = x[j]; x1++;
    if (p1)
    {
      (void)mulll(p1,x1[lz+1]);
      garde = addll(addmul(p1,x1[lz]), garde);
      for (i=lzz; i>j; i--)
      {
        hiremainder += overflow;
        z[i] = addll(addmul(p1,x1[i]), z[i]);
      }
      z[j] = hiremainder+overflow;
    }
    else z[j]=0;
  }
  p1 = x[2]; x1++;
  garde = addll(mulll(p1,x1[lz]), garde);
  for (i=lzz; i>2; i--)
  {
    hiremainder += overflow;
    z[i] = addll(addmul(p1,x1[i]), z[i]);
  }
  z[2] = hiremainder+overflow;
  mulrrz_end(z, z, lz, 1, ez, garde);
}

/* lz "large" = lg(y) = lg(z), lg(x) > lz if flag = 1 and >= if flag = 0 */
INLINE void
mulrrz_int(GEN z, GEN x, GEN y, long lz, long flag, long sz)
{
  pari_sp av = avma;
  GEN hi = muliispec_mirror(y+2, x+2, lz+flag-2, lz-2);
  mulrrz_end(z, hi, lz, sz, expo(x)+expo(y), hi[lz]);
  avma = av;
}

/* lz = 3 */
INLINE void
mulrrz_3(GEN z, GEN x, GEN y, long flag, long sz)
{
  ulong garde;
  LOCAL_HIREMAINDER;
  if (flag)
  {
    (void)mulll(x[2],y[3]);
    garde = addmul(x[2],y[2]);
  }
  else
    garde = mulll(x[2],y[2]);
  z[2] = hiremainder;
  mulrrz_3end(z, sz, expo(x)+expo(y), garde);
}

/* set z <-- x*y, floating point multiplication. Trailing 0s for x are
 * treated efficiently (important application: mulir).
 * lz = lg(z) = lg(x) <= ly <= lg(y), sz = signe(z). flag = lg(x) < lg(y) */
INLINE void
mulrrz_i(GEN z, GEN x, GEN y, long lz, long flag, long sz)
{
  long ez, i, j, lzz, p1;
  ulong garde;
  GEN y1;
  LOCAL_HIREMAINDER;
  LOCAL_OVERFLOW;

  if (x == y) { sqrz_i(z,x,lz); return; }
  if (lz > MULRR_MULII_LIMIT) { mulrrz_int(z,x,y,lz,flag,sz); return; }
  if (lz == 3) { mulrrz_3(z,x,y,flag,sz); return; }
  ez = expo(x) + expo(y);
  if (flag) { (void)mulll(x[2],y[lz]); garde = hiremainder; } else garde = 0;
  lzz=lz-1; p1=x[lzz];
  if (p1)
  {
    (void)mulll(p1,y[3]);
    garde = addll(addmul(p1,y[2]), garde);
    z[lzz] = overflow+hiremainder;
  }
  else z[lzz]=0;
  for (j=lz-2, y1=y-j; j>=3; j--)
  {
    p1 = x[j]; y1++;
    if (p1)
    {
      (void)mulll(p1,y1[lz+1]);
      garde = addll(addmul(p1,y1[lz]), garde);
      for (i=lzz; i>j; i--)
      {
        hiremainder += overflow;
        z[i] = addll(addmul(p1,y1[i]), z[i]);
      }
      z[j] = hiremainder+overflow;
    }
    else z[j]=0;
  }
  p1 = x[2]; y1++;
  garde = addll(mulll(p1,y1[lz]), garde);
  for (i=lzz; i>2; i--)
  {
    hiremainder += overflow;
    z[i] = addll(addmul(p1,y1[i]), z[i]);
  }
  z[2] = hiremainder+overflow;
  mulrrz_end(z, z, lz, sz, ez, garde);
}

GEN
mulrr(GEN x, GEN y)
{
  long flag, ly, lz, sx, sy;
  GEN z;

  if (x == y) return sqrr(x);
  sx = signe(x); if (!sx) return real_0_bit(expo(x) + expo(y));
  sy = signe(y); if (!sy) return real_0_bit(expo(x) + expo(y));
  if (sy < 0) sx = -sx;
  lz = lg(x);
  ly = lg(y);
  if (lz > ly) { lz = ly; swap(x, y); flag = 1; } else flag = (lz != ly);
  z = cgetr(lz);
  mulrrz_i(z, x,y, lz,flag, sx);
  return z;
}

GEN
sqrr(GEN x)
{
  long lz, sx = signe(x);
  GEN z;

  if (!sx) return real_0_bit(2*expo(x));
  lz = lg(x); z = cgetr(lz);
  sqrz_i(z, x, lz);
  return z;
}

GEN
mulir(GEN x, GEN y)
{
  long sx = signe(x), sy;
  if (!sx) return mul0r(y);
  if (lgefint(x) == 3) {
    GEN z = mulur(uel(x,2), y);
    if (sx < 0) togglesign(z);
    return z;
  }
  sy = signe(y);
  if (!sy) return real_0_bit(expi(x) + expo(y));
  if (sy < 0) sx = -sx;
  {
    long lz = lg(y), lx = lgefint(x);
    GEN hi, z = cgetr(lz);
    pari_sp av = avma;
    if (lx < (lz>>1) || (lx < lz && lz > MULRR_MULII_LIMIT))
    { /* size mantissa of x < half size of mantissa z, or lx < lz so large
       * that mulrr will call mulii anyway: mulii */
      x = itor(x, lx);
      hi = muliispec_mirror(y+2, x+2, lz-2, lx-2);
      mulrrz_end(z, hi, lz, sx, expo(x)+expo(y), hi[lz]);
    }
    else /* dubious: complete x with 0s and call mulrr */
      mulrrz_i(z, itor(x,lz), y, lz, 0, sx);
    avma = av; return z;
  }
}

/* x + y*z, generic. If lgefint(z) <= 3, caller should use faster variants  */
static GEN
addmulii_gen(GEN x, GEN y, GEN z, long lz)
{
  long lx = lgefint(x), ly;
  pari_sp av;
  GEN t;
  if (lx == 2) return mulii(z,y);
  ly = lgefint(y);
  if (ly == 2) return icopy(x); /* y = 0, wasteful copy */
  av = avma; (void)new_chunk(lx+ly+lz); /*HACK*/
  t = mulii(z, y);
  avma = av; return addii(t,x);
}
/* x + y*z, lgefint(z) == 3 */
static GEN
addmulii_lg3(GEN x, GEN y, GEN z)
{
  long s = signe(z), lx, ly;
  ulong w = z[2];
  pari_sp av;
  GEN t;
  if (w == 1) return (s > 0)? addii(x,y): subii(x,y); /* z = +- 1 */
  lx = lgefint(x);
  ly = lgefint(y);
  if (lx == 2)
  { /* x = 0 */
    if (ly == 2) return gen_0;
    t = muluispec(w, y+2, ly-2);
    if (signe(y) < 0) s = -s;
    setsigne(t, s); return t;
  }
  if (ly == 2) return icopy(x); /* y = 0, wasteful copy */
  av = avma; (void)new_chunk(1+lx+ly);/*HACK*/
  t = muluispec(w, y+2, ly-2);
  if (signe(y) < 0) s = -s;
  setsigne(t, s);
  avma = av; return addii(x,t);
}
/* x + y*z */
GEN
addmulii(GEN x, GEN y, GEN z)
{
  long lz = lgefint(z);
  switch(lz)
  {
    case 2: return icopy(x); /* z = 0, wasteful copy */
    case 3: return addmulii_lg3(x, y, z);
    default:return addmulii_gen(x, y, z, lz);
  }
}
/* x + y*z, returns x itself and not a copy when y*z = 0 */
GEN
addmulii_inplace(GEN x, GEN y, GEN z)
{
  long lz;
  if (lgefint(y) == 2) return x;
  lz = lgefint(z);
  switch(lz)
  {
    case 2: return x;
    case 3: return addmulii_lg3(x, y, z);
    default:return addmulii_gen(x, y, z, lz);
  }
}

/* written by Bruno Haible following an idea of Robert Harley */
long
vals(ulong z)
{
  static char tab[64]={-1,0,1,12,2,6,-1,13,3,-1,7,-1,-1,-1,-1,14,10,4,-1,-1,8,-1,-1,25,-1,-1,-1,-1,-1,21,27,15,31,11,5,-1,-1,-1,-1,-1,9,-1,-1,24,-1,-1,20,26,30,-1,-1,-1,-1,23,-1,19,29,-1,22,18,28,17,16,-1};
#ifdef LONG_IS_64BIT
  long s;
#endif

  if (!z) return -1;
#ifdef LONG_IS_64BIT
  if (! (z&0xffffffff)) { s = 32; z >>=32; } else s = 0;
#endif
  z |= ~z + 1;
  z += z << 4;
  z += z << 6;
  z ^= z << 16; /* or  z -= z<<16 */
#ifdef LONG_IS_64BIT
  return s + tab[(z&0xffffffff)>>26];
#else
  return tab[z>>26];
#endif
}

GEN
divsi(long x, GEN y)
{
  long p1, s = signe(y);
  LOCAL_HIREMAINDER;

  if (!s) pari_err_INV("divsi",gen_0);
  if (!x || lgefint(y)>3 || ((long)y[2])<0) return gen_0;
  hiremainder=0; p1=divll(labs(x),y[2]);
  if (x<0) { hiremainder = -((long)hiremainder); p1 = -p1; }
  if (s<0) p1 = -p1;
  return stoi(p1);
}

GEN
divir(GEN x, GEN y)
{
  GEN z;
  long ly = lg(y), lx = lgefint(x);
  pari_sp av;

  if (ly == 2) pari_err_INV("divir",y);
  if (lx == 2) return div0r(y);
  if (lx == 3) {
    z = divur(x[2], y);
    if (signe(x) < 0) togglesign(z);
    return z;
  }
  z = cgetr(ly); av = avma;
  affrr(divrr(itor(x, ly+1), y), z);
  avma = av; return z;
}

GEN
divur(ulong x, GEN y)
{
  pari_sp av;
  long ly = lg(y);
  GEN z;

  if (ly == 2) pari_err_INV("divur",y);
  if (!x) return div0r(y);
  if (ly > INVNEWTON_LIMIT) {
    av = avma; z = invr(y);
    if (x == 1) return z;
    return gerepileuptoleaf(av, mulur(x, z));
  }
  z = cgetr(ly); av = avma;
  affrr(divrr(utor(x,ly+1), y), z);
  avma = av; return z;
}

GEN
divsr(long x, GEN y)
{
  pari_sp av;
  long ly = lg(y);
  GEN z;

  if (ly == 2) pari_err_INV("divsr",y);
  if (!x) return div0r(y);
  if (ly > INVNEWTON_LIMIT) {
    av = avma; z = invr(y);
    if (x == 1) return z;
    if (x ==-1) { togglesign(z); return z; }
    return gerepileuptoleaf(av, mulsr(x, z));
  }
  z = cgetr(ly); av = avma;
  affrr(divrr(stor(x,ly+1), y), z);
  avma = av; return z;
}

/* returns 1/y, assume y != 0 */
static GEN
invr_basecase(GEN y)
{
  long ly = lg(y);
  GEN z = cgetr(ly);
  pari_sp av = avma;
  affrr(divrr(real_1(ly+1), y), z);
  avma = av; return z;
}
/* returns 1/b, Newton iteration */
GEN
invr(GEN b)
{
  const long s = 6;
  long i, p, l = lg(b);
  GEN x, a;
  ulong mask;

  if (l <= maxss(INVNEWTON_LIMIT, (1L<<s) + 2)) {
    if (l == 2) pari_err_INV("invr",b);
    return invr_basecase(b);
  }
  mask = quadratic_prec_mask(l-2);
  for(i=0, p=1; i<s; i++) { p <<= 1; if (mask & 1) p--; mask >>= 1; }
  x = cgetr(l);
  a = rcopy(b); a[1] = _evalexpo(0) | evalsigne(1);
  affrr(invr_basecase(rtor(a, p+2)), x);
  while (mask > 1)
  {
    p <<= 1; if (mask & 1) p--;
    mask >>= 1;
    setlg(a, p + 2);
    setlg(x, p + 2);
    /* TODO: mulrr(a,x) should be a half product (the higher half is known).
     * mulrr(x, ) already is */
    affrr(addrr(x, mulrr(x, subsr(1, mulrr(a,x)))), x);
    avma = (pari_sp)a;
  }
  x[1] = (b[1] & SIGNBITS) | evalexpo(expo(x)-expo(b));
  avma = (pari_sp)x; return x;
}

GEN
modii(GEN x, GEN y)
{
  switch(signe(x))
  {
    case 0: return gen_0;
    case 1: return remii(x,y);
    default:
    {
      pari_sp av = avma;
      (void)new_chunk(lgefint(y));
      x = remii(x,y); avma=av;
      if (x==gen_0) return x;
      return subiispec(y+2,x+2,lgefint(y)-2,lgefint(x)-2);
    }
  }
}

void
modiiz(GEN x, GEN y, GEN z)
{
  const pari_sp av = avma;
  affii(modii(x,y),z); avma=av;
}

GEN
divrs(GEN x, long y)
{
  GEN z;
  if (y < 0)
  {
    z = divru(x, (ulong)-y);
    togglesign(z);
  }
  else
    z = divru(x, (ulong)y);
  return z;
}

GEN
divru(GEN x, ulong y)
{
  long i, lx, sh, e, s = signe(x);
  ulong garde;
  GEN z;
  LOCAL_HIREMAINDER;

  if (!y) pari_err_INV("divru",gen_0);
  if (!s) return real_0_bit(expo(x) - expu(y));
  if (!(y & (y-1))) /* power of 2 */
  {
    if (y == 1) return rcopy(x);
    return shiftr(x, -expu(y));
  }
  e = expo(x);
  lx = lg(x);
  z = cgetr(lx);
  if (lx == 3)
  {
    if (y <= uel(x,2))
    {
      hiremainder = 0;
      z[2] = divll(x[2],y);
      /* we may have hiremainder != 0 ==> garde */
      garde = divll(0,y);
    }
    else
    {
      hiremainder = x[2];
      z[2] = divll(0,y);
      garde = hiremainder;
      e -= BITS_IN_LONG;
    }
  }
  else
  {
    ulong yp = get_Fl_red(y);
    if (y <= uel(x,2))
    {
      hiremainder = 0;
      for (i=2; i<lx; i++) z[i] = divll_pre(x[i],y,yp);
      /* we may have hiremainder != 0 ==> garde */
      garde = divll_pre(0,y,yp);
    }
    else
    {
      long l = lx-1;
      hiremainder = x[2];
      for (i=2; i<l; i++) z[i] = divll_pre(x[i+1],y,yp);
      z[i] = divll_pre(0,y,yp);
      garde = hiremainder;
      e -= BITS_IN_LONG;
    }
  }
  sh=bfffo(z[2]); /* z[2] != 0 */
  if (sh) shift_left(z,z, 2,lx-1, garde,sh);
  z[1] = evalsigne(s) | evalexpo(e-sh);
  if ((garde << sh) & HIGHBIT) roundr_up_ip(z, lx);
  return z;
}

GEN
truedvmdii(GEN x, GEN y, GEN *z)
{
  pari_sp av;
  GEN r, q, *gptr[2];
  if (!is_bigint(y)) return truedvmdis(x, itos(y), z);
  if (z == ONLY_REM) return modii(x,y);

  av = avma;
  q = dvmdii(x,y,&r); /* assume that r is last on stack */
  switch(signe(r))
  {
    case 0:
      if (z) *z = gen_0;
      return q;
    case 1:
      if (z) *z = r; else cgiv(r);
      return q;
    case -1: break;
  }
  q = addis(q, -signe(y));
  if (!z) return gerepileuptoint(av, q);

  *z = subiispec(y+2,r+2, lgefint(y)-2,lgefint(r)-2);
  gptr[0]=&q; gptr[1]=z; gerepilemanysp(av,(pari_sp)r,gptr,2);
  return q;
}
GEN
truedvmdis(GEN x, long y, GEN *z)
{
  pari_sp av = avma;
  long r;
  GEN q;

  if (z == ONLY_REM) return modis(x, y);
  q = divis_rem(x,y,&r);

  if (r >= 0)
  {
    if (z) *z = utoi(r);
    return q;
  }
  q = gerepileuptoint(av, addis(q, (y < 0)? 1: -1));
  if (z) *z = utoi(r + labs(y));
  return q;
}
GEN
truedvmdsi(long x, GEN y, GEN *z)
{
  long q, r;
  if (z == ONLY_REM) return modsi(x, y);
  q = sdivsi_rem(x,y,&r);
  if (r >= 0) {
    if (z) *z = utoi(r);
    return stoi(q);
  }
  q = q - signe(y);
  if (!z) return stoi(q);

  *z = subiuspec(y+2,(ulong)-r, lgefint(y)-2);
  return stoi(q);
}

/* 2^n = shifti(gen_1, n) */
GEN
int2n(long n) {
  long i, m, l;
  GEN z;
  if (n < 0) return gen_0;
  if (n == 0) return gen_1;

  l = dvmdsBIL(n, &m) + 3;
  z = cgetipos(l);
  for (i = 2; i < l; i++) z[i] = 0;
  *int_MSW(z) = 1UL << m; return z;
}
/* To avoid problems when 2^(BIL-1) < n. Overflow cleanly, where int2n
 * returns gen_0 */
GEN
int2u(ulong n) {
  ulong i, m, l;
  GEN z;
  if (n == 0) return gen_1;

  l = dvmduBIL(n, &m) + 3;
  z = cgetipos(l);
  for (i = 2; i < l; i++) z[i] = 0;
  *int_MSW(z) = 1UL << m; return z;
}
/* 2^n - 1 */
GEN
int2um1(ulong n) {
  ulong i, m, l;
  GEN z;
  if (n == 0) return gen_0;

  l = dvmduBIL(n, &m);
  l += m? 3: 2;
  z = cgetipos(l);
  for (i = 2; i < l; i++) z[i] = ~0UL;
  if (m) *int_MSW(z) = (1UL << m) - 1;
  return z;
}

GEN
shifti(GEN x, long n)
{
  long s = signe(x);
  GEN y;

  if(s == 0) return gen_0;
  y = shiftispec(x + 2, lgefint(x) - 2, n);
  if (signe(y)) setsigne(y, s);
  return y;
}

/* actual operations will take place on a+2 and b+2: we strip the codewords */
GEN
mulii(GEN a,GEN b)
{
  long sa,sb;
  GEN z;

  sa=signe(a); if (!sa) return gen_0;
  sb=signe(b); if (!sb) return gen_0;
  if (sb<0) sa = -sa;
  z = muliispec(a+2,b+2, lgefint(a)-2,lgefint(b)-2);
  setsigne(z,sa); return z;
}

GEN
sqri(GEN a) { return sqrispec(a+2, lgefint(a)-2); }

/* sqrt()'s result may be off by 1 when a is not representable exactly as a
 * double [64bit machine] */
ulong
usqrt(ulong a)
{
  ulong x = (ulong)sqrt((double)a);
#ifdef LONG_IS_64BIT
  if (x > LOWMASK || x*x > a) x--;
#endif
  return x;
}

/********************************************************************/
/**                                                                **/
/**              EXPONENT / CONVERSION t_REAL --> double           **/
/**                                                                **/
/********************************************************************/

#ifdef LONG_IS_64BIT
long
dblexpo(double x)
{
  union { double f; ulong i; } fi;
  const int mant_len = 52;  /* mantissa bits (excl. hidden bit) */
  const int exp_mid = 0x3ff;/* exponent bias */

  if (x==0.) return -exp_mid;
  fi.f = x;
  return ((fi.i & (HIGHBIT-1)) >> mant_len) - exp_mid;
}

ulong
dblmantissa(double x)
{
  union { double f; ulong i; } fi;
  const int expo_len = 11; /* number of bits of exponent */

  if (x==0.) return 0;
  fi.f = x;
  return (fi.i << expo_len) | HIGHBIT;
}

GEN
dbltor(double x)
{
  GEN z;
  long e;
  union { double f; ulong i; } fi;
  const int mant_len = 52;  /* mantissa bits (excl. hidden bit) */
  const int exp_mid = 0x3ff;/* exponent bias */
  const int expo_len = 11; /* number of bits of exponent */

  if (x==0.) return real_0_bit(-exp_mid);
  fi.f = x; z = cgetr(DEFAULTPREC);
  {
    const ulong a = fi.i;
    ulong A;
    e = ((a & (HIGHBIT-1)) >> mant_len) - exp_mid;
    if (e == exp_mid+1) pari_err_OVERFLOW("dbltor [NaN or Infinity]");
    A = a << expo_len;
    if (e == -exp_mid)
    { /* unnormalized values */
      int sh = bfffo(A);
      e -= sh-1;
      z[2] = A << sh;
    }
    else
      z[2] = HIGHBIT | A;
    z[1] = _evalexpo(e) | evalsigne(x<0? -1: 1);
  }
  return z;
}

double
rtodbl(GEN x)
{
  long ex,s=signe(x);
  ulong a;
  union { double f; ulong i; } fi;
  const int mant_len = 52;  /* mantissa bits (excl. hidden bit) */
  const int exp_mid = 0x3ff;/* exponent bias */
  const int expo_len = 11; /* number of bits of exponent */

  if (!s || (ex=expo(x)) < - exp_mid) return 0.0;

  /* start by rounding to closest */
  a = (x[2] & (HIGHBIT-1)) + 0x400;
  if (a & HIGHBIT) { ex++; a=0; }
  if (ex >= exp_mid) pari_err_OVERFLOW("t_REAL->double conversion");
  fi.i = ((ex + exp_mid) << mant_len) | (a >> expo_len);
  if (s<0) fi.i |= HIGHBIT;
  return fi.f;
}

#else /* LONG_IS_64BIT */

#if   PARI_DOUBLE_FORMAT == 1
#  define INDEX0 1
#  define INDEX1 0
#elif PARI_DOUBLE_FORMAT == 0
#  define INDEX0 0
#  define INDEX1 1
#endif

long
dblexpo(double x)
{
  union { double f; ulong i[2]; } fi;
  const int mant_len = 52;  /* mantissa bits (excl. hidden bit) */
  const int exp_mid = 0x3ff;/* exponent bias */
  const int shift = mant_len-32;

  if (x==0.) return -exp_mid;
  fi.f = x;
  {
    const ulong a = fi.i[INDEX0];
    return ((a & (HIGHBIT-1)) >> shift) - exp_mid;
  }
}

ulong
dblmantissa(double x)
{
  union { double f; ulong i[2]; } fi;
  const int expo_len = 11; /* number of bits of exponent */

  if (x==0.) return 0;
  fi.f = x;
  {
    const ulong a = fi.i[INDEX0];
    const ulong b = fi.i[INDEX1];
    return HIGHBIT | b >> (BITS_IN_LONG-expo_len) | (a << expo_len);
  }
}

GEN
dbltor(double x)
{
  GEN z;
  long e;
  union { double f; ulong i[2]; } fi;
  const int mant_len = 52;  /* mantissa bits (excl. hidden bit) */
  const int exp_mid = 0x3ff;/* exponent bias */
  const int expo_len = 11; /* number of bits of exponent */
  const int shift = mant_len-32;

  if (x==0.) return real_0_bit(-exp_mid);
  fi.f = x; z = cgetr(DEFAULTPREC);
  {
    const ulong a = fi.i[INDEX0];
    const ulong b = fi.i[INDEX1];
    ulong A, B;
    e = ((a & (HIGHBIT-1)) >> shift) - exp_mid;
    if (e == exp_mid+1) pari_err_OVERFLOW("dbltor [NaN or Infinity]");
    A = b >> (BITS_IN_LONG-expo_len) | (a << expo_len);
    B = b << expo_len;
    if (e == -exp_mid)
    { /* unnormalized values */
      int sh;
      if (A)
      {
        sh = bfffo(A);
        e -= sh-1;
        z[2] = (A << sh) | (B >> (32-sh));
        z[3] = B << sh;
      }
      else
      {
        sh = bfffo(B); /* B != 0 */
        e -= sh-1 + 32;
        z[2] = B << sh;
        z[3] = 0;
      }
    }
    else
    {
      z[3] = B;
      z[2] = HIGHBIT | A;
    }
    z[1] = _evalexpo(e) | evalsigne(x<0? -1: 1);
  }
  return z;
}

double
rtodbl(GEN x)
{
  long ex,s=signe(x),lx=lg(x);
  ulong a,b,k;
  union { double f; ulong i[2]; } fi;
  const int mant_len = 52;  /* mantissa bits (excl. hidden bit) */
  const int exp_mid = 0x3ff;/* exponent bias */
  const int expo_len = 11; /* number of bits of exponent */
  const int shift = mant_len-32;

  if (!s || (ex=expo(x)) < - exp_mid) return 0.0;

  /* start by rounding to closest */
  a = x[2] & (HIGHBIT-1);
  if (lx > 3)
  {
    b = x[3] + 0x400UL; if (b < 0x400UL) a++;
    if (a & HIGHBIT) { ex++; a=0; }
  }
  else b = 0;
  if (ex >= exp_mid) pari_err_OVERFLOW("t_REAL->double conversion");
  ex += exp_mid;
  k = (a >> expo_len) | (ex << shift);
  if (s<0) k |= HIGHBIT;
  fi.i[INDEX0] = k;
  fi.i[INDEX1] = (a << (BITS_IN_LONG-expo_len)) | (b >> expo_len);
  return fi.f;
}
#endif /* LONG_IS_64BIT */

