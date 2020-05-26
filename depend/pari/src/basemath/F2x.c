/* Copyright (C) 2007  The PARI group.

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

/* Not so fast arithmetic with polynomials over F_2 */

/***********************************************************************/
/**                                                                   **/
/**                             F2x                                   **/
/**                                                                   **/
/***********************************************************************/
/* F2x objects are defined as follows:
   An F2x is a t_VECSMALL:
   x[0] = codeword
   x[1] = evalvarn(variable number)  (signe is not stored).
   x[2] = a_0...a_31 x[3] = a_32..a_63, etc.  on 32bit
   x[2] = a_0...a_63 x[3] = a_64..a_127, etc. on 64bit

   where the a_i are bits.

   signe(x) is not valid. Use lgpol(x)!=0 instead.
   Note: pol0_F2x=pol0_Flx and pol1_F2x=pol1_Flx
*/

INLINE long
F2x_degree_lg(GEN x, long l)
{
  return (l==2)?-1:bit_accuracy(l)-bfffo(x[l-1])-1;
}

long
F2x_degree(GEN x)
{
  return F2x_degree_lg(x, lg(x));
}

GEN
monomial_F2x(long d, long vs)
{
  long l=nbits2lg(d+1);
  GEN z = zero_zv(l-1);
  z[1] = vs;
  F2x_set(z,d);
  return z;
}

GEN
F2x_to_ZX(GEN x)
{
  long l=3+F2x_degree(x);
  GEN z=cgetg(l,t_POL);
  long i,j,k;
  for(i=2,k=2;i<lg(x);i++)
    for(j=0; j<BITS_IN_LONG && k<l; j++,k++)
      gel(z,k)=(x[i]&(1UL<<j))?gen_1:gen_0;
  z[1]=evalsigne(l>=3)|x[1];
  return z;
}

GEN
F2x_to_Flx(GEN x)
{
  long l=3+F2x_degree(x);
  GEN z=cgetg(l,t_VECSMALL);
  long i,j,k;
  z[1]=x[1];
  for(i=2,k=2;i<lg(x);i++)
    for(j=0;j<BITS_IN_LONG && k<l; j++,k++)
      z[k]=(x[i]>>j)&1UL;
  return z;
}

GEN
F2x_to_F2xX(GEN z, long sv)
{
  long i, d = F2x_degree(z);
  GEN x = cgetg(d+3,t_POL);
  for (i=0; i<=d; i++)
    gel(x,i+2) = F2x_coeff(z,i) ? pol1_F2x(sv): pol0_F2x(sv);
  x[1] = evalsigne(d+1!=0)| z[1]; return x;
}

GEN
Z_to_F2x(GEN x, long v)
{
  long sv = evalvarn(v);
  return mpodd(x) ? pol1_F2x(sv): pol0_F2x(sv);
}

GEN
ZX_to_F2x(GEN x)
{
  long l=nbits2lg(lgpol(x));
  GEN z=cgetg(l,t_VECSMALL);
  long i,j,k;
  z[1]=((ulong)x[1])&VARNBITS;
  for(i=2, k=1,j=BITS_IN_LONG;i<lg(x);i++,j++)
  {
    if (j==BITS_IN_LONG)
    {
      j=0; k++; z[k]=0;
    }
    if (mpodd(gel(x,i)))
      z[k]|=1UL<<j;
  }
  return F2x_renormalize(z,l);
}

GEN
Flx_to_F2x(GEN x)
{
  long l=nbits2lg(lgpol(x));
  GEN z=cgetg(l,t_VECSMALL);
  long i,j,k;
  z[1]=x[1];
  for(i=2, k=1,j=BITS_IN_LONG;i<lg(x);i++,j++)
  {
    if (j==BITS_IN_LONG)
    {
      j=0; k++; z[k]=0;
    }
    if (x[i]&1UL)
      z[k]|=1UL<<j;
  }
  return F2x_renormalize(z,l);
}

GEN
F2x_to_F2v(GEN x, long N)
{
  long i, l = lg(x);
  long n = nbits2lg(N);
  GEN z = cgetg(n,t_VECSMALL);
  z[1] = N;
  for (i=2; i<l ; i++) z[i]=x[i];
  for (   ; i<n; i++) z[i]=0;
  return z;
}

GEN
RgX_to_F2x(GEN x)
{
  long l=nbits2lg(lgpol(x));
  GEN z=cgetg(l,t_VECSMALL);
  long i,j,k;
  z[1]=((ulong)x[1])&VARNBITS;
  for(i=2, k=1,j=BITS_IN_LONG;i<lg(x);i++,j++)
  {
    if (j==BITS_IN_LONG)
    {
      j=0; k++; z[k]=0;
    }
    if (Rg_to_F2(gel(x,i)))
      z[k]|=1UL<<j;
  }
  return F2x_renormalize(z,l);
}

/* If x is a POLMOD, assume modulus is a multiple of T. */
GEN
Rg_to_F2xq(GEN x, GEN T)
{
  long ta, tx = typ(x), v = T[1];
  GEN a, b;
  if (is_const_t(tx))
  {
    if (tx == t_FFELT) return FF_to_F2xq(x);
    return Rg_to_F2(x)? pol1_F2x(v): pol0_F2x(v);
  }
  switch(tx)
  {
    case t_POLMOD:
      b = gel(x,1);
      a = gel(x,2); ta = typ(a);
      if (is_const_t(ta)) return Rg_to_F2(a)? pol1_F2x(v): pol0_F2x(v);
      b = RgX_to_F2x(b); if (b[1] != v) break;
      a = RgX_to_F2x(a); if (F2x_equal(b,T)) return a;
      if (lgpol(F2x_rem(b,T))==0) return F2x_rem(a, T);
      break;
    case t_POL:
      x = RgX_to_F2x(x);
      if (x[1] != v) break;
      return F2x_rem(x, T);
    case t_RFRAC:
      a = Rg_to_F2xq(gel(x,1), T);
      b = Rg_to_F2xq(gel(x,2), T);
      return F2xq_div(a,b, T);
  }
  pari_err_TYPE("Rg_to_F2xq",x);
  return NULL; /* LCOV_EXCL_LINE */
}

ulong
F2x_eval(GEN P, ulong x)
{
  if (odd(x))
  {
    long i, lP = lg(P);
    ulong c = 0;
    for (i=2; i<lP; i++)
      c ^= P[i];
#ifdef LONG_IS_64BIT
    c ^= c >> 32;
#endif
    c ^= c >> 16;
    c ^= c >>  8;
    c ^= c >>  4;
    c ^= c >>  2;
    c ^= c >>  1;
    return c & 1;
  }
  else return F2x_coeff(P,0);
}

GEN
F2x_add(GEN x, GEN y)
{
  long i,lz;
  GEN z;
  long lx=lg(x);
  long ly=lg(y);
  if (ly>lx) swapspec(x,y, lx,ly);
  lz = lx; z = cgetg(lz, t_VECSMALL); z[1]=x[1];
  for (i=2; i<ly; i++) z[i] = x[i]^y[i];
  for (   ; i<lx; i++) z[i] = x[i];
  return F2x_renormalize(z, lz);
}

static GEN
F2x_addspec(GEN x, GEN y, long lx, long ly)
{
  long i,lz;
  GEN z;

  if (ly>lx) swapspec(x,y, lx,ly);
  lz = lx+2; z = cgetg(lz, t_VECSMALL) + 2;
  for (i=0; i<ly-3; i+=4)
  {
    z[i] = x[i]^y[i];
    z[i+1] = x[i+1]^y[i+1];
    z[i+2] = x[i+2]^y[i+2];
    z[i+3] = x[i+3]^y[i+3];
  }
  for (; i<ly; i++)
    z[i] = x[i]^y[i];
  for (   ; i<lx; i++) z[i] = x[i];
  z -= 2; return F2x_renormalize(z, lz);
}

GEN
F2x_1_add(GEN y)
{
  GEN z;
  long lz, i;
  if (!lgpol(y))
    return pol1_F2x(y[1]);
  lz=lg(y);
  z=cgetg(lz,t_VECSMALL);
  z[1] = y[1];
  z[2] = y[2]^1UL;
  for(i=3;i<lz;i++)
    z[i] = y[i];
  if (lz==3) z = F2x_renormalize(z,lz);
  return z;
}

INLINE void
F2x_addshiftipspec(GEN x, GEN y, long ny, ulong db)
{
  long i;
  if (db)
  {
    ulong dc=BITS_IN_LONG-db;
    ulong r=0, yi;
    for(i=0; i<ny-3; i+=4)
    {
      yi = uel(y,i);   x[i]   ^= (yi<<db)|r; r = yi>>dc;
      yi = uel(y,i+1); x[i+1] ^= (yi<<db)|r; r = yi>>dc;
      yi = uel(y,i+2); x[i+2] ^= (yi<<db)|r; r = yi>>dc;
      yi = uel(y,i+3); x[i+3] ^= (yi<<db)|r; r = yi>>dc;
    }
    for(  ; i<ny; i++)
    {
      ulong yi = uel(y,i); x[i] ^= (yi<<db)|r; r = yi>>dc;
    }
    if (r) x[i] ^= r;
  }
  else
  {
    for(i=0; i<ny-3; i+=4)
    {
      x[i]   ^= y[i];
      x[i+1] ^= y[i+1];
      x[i+2] ^= y[i+2];
      x[i+3] ^= y[i+3];
    }
    for(   ; i<ny; i++)
      x[i] ^= y[i];
  }
}

INLINE void
F2x_addshiftip(GEN x, GEN y, ulong d)
{
  ulong db, dl=dvmduBIL(d, &db);
  F2x_addshiftipspec(x+2+dl, y+2, lgpol(y), db);
}

static GEN
F2x_mul1(ulong x, ulong y)
{
  ulong x1=(x&HIGHMASK)>>BITS_IN_HALFULONG;
  ulong x2=x&LOWMASK;
  ulong y1=(y&HIGHMASK)>>BITS_IN_HALFULONG;
  ulong y2=y&LOWMASK;
  ulong r1,r2,rr;
  GEN z;
  ulong i;
  rr=r1=r2=0UL;
  if (x2)
    for(i=0;i<BITS_IN_HALFULONG;i++)
      if (x2&(1UL<<i))
      {
        r2^=y2<<i;
        rr^=y1<<i;
      }
  if (x1)
    for(i=0;i<BITS_IN_HALFULONG;i++)
      if (x1&(1UL<<i))
      {
        r1^=y1<<i;
        rr^=y2<<i;
      }
  r2^=(rr&LOWMASK)<<BITS_IN_HALFULONG;
  r1^=(rr&HIGHMASK)>>BITS_IN_HALFULONG;
  z=cgetg((r1?4:3),t_VECSMALL);
  z[2]=r2;
  if (r1) z[3]=r1;
  return z;
}

static GEN
F2x_mulspec_basecase(GEN x, GEN y, long nx, long ny)
{
  long l, i, j;
  GEN z;
  l = nx + ny;
  z = zero_Flv(l+1);
  for(i=0; i < ny-1; i++)
  {
    GEN zi = z+2+i;
    ulong yi = uel(y,i);
    if (yi)
      for(j=0; j < BITS_IN_LONG; j++)
        if (yi&(1UL<<j)) F2x_addshiftipspec(zi,x,nx,j);
  }
  {
    GEN zi = z+2+i;
    ulong yi = uel(y,i);
    long c = BITS_IN_LONG-bfffo(yi);
    for(j=0; j < c; j++)
      if (yi&(1UL<<j)) F2x_addshiftipspec(zi,x,nx,j);
  }
  return F2x_renormalize(z, l+2);
}

static GEN
F2x_addshift(GEN x, GEN y, long d)
{
  GEN xd,yd,zd = (GEN)avma;
  long a,lz,ny = lgpol(y), nx = lgpol(x);
  long vs = x[1];

  x += 2; y += 2; a = ny-d;
  if (a <= 0)
  {
    lz = (a>nx)? ny+2: nx+d+2;
    (void)new_chunk(lz); xd = x+nx; yd = y+ny;
    while (xd > x) *--zd = *--xd;
    x = zd + a;
    while (zd > x) *--zd = 0;
  }
  else
  {
    xd = new_chunk(d); yd = y+d;
    x = F2x_addspec(x,yd,nx,a);
    lz = (a>nx)? ny+2: lg(x)+d;
    x += 2; while (xd > x) *--zd = *--xd;
  }
  while (yd > y) *--zd = *--yd;
  *--zd = vs;
  *--zd = evaltyp(t_VECSMALL) | evallg(lz); return zd;
}

/* shift polynomial + gerepile */
/* Do not set evalvarn. Cf Flx_shiftip */
static GEN
F2x_shiftip(pari_sp av, GEN x, long v)
{
  long i, lx = lg(x), ly;
  GEN y;
  if (!v || lx==2) return gerepileuptoleaf(av, x);
  ly = lx + v;
  (void)new_chunk(ly); /* check that result fits */
  x += lx; y = (GEN)av;
  for (i = 2; i<lx; i++) *--y = *--x;
  for (i = 0; i< v; i++) *--y = 0;
  y -= 2; y[0] = evaltyp(t_VECSMALL) | evallg(ly);
  avma = (pari_sp)y; return y;
}

/* fast product (Karatsuba) of polynomials a,b. These are not real GENs, a+2,
 * b+2 were sent instead. na, nb = number of terms of a, b.
 * Only c, c0, c1, c2 are genuine GEN.
 */
static GEN
F2x_mulspec(GEN a, GEN b, long na, long nb)
{
  GEN a0,c,c0;
  long n0, n0a, i, v = 0;
  pari_sp av;

  while (na && !a[0]) { a++; na-=1; v++; }
  while (nb && !b[0]) { b++; nb-=1; v++; }
  if (na < nb) swapspec(a,b, na,nb);
  if (!nb) return pol0_F2x(0);

  av = avma;
  if (na == 1)
    return F2x_shiftip(av, F2x_mul1(*a,*b), v);
  if (na < F2x_MUL_KARATSUBA_LIMIT)
    return F2x_shiftip(av, F2x_mulspec_basecase(a, b, na, nb), v);
  i=(na>>1); n0=na-i; na=i;
  a0=a+n0; n0a=n0;
  while (n0a && !a[n0a-1]) n0a--;

  if (nb > n0)
  {
    GEN b0,c1,c2;
    long n0b;

    nb -= n0; b0 = b+n0; n0b = n0;
    while (n0b && !b[n0b-1]) n0b--;
    c =  F2x_mulspec(a,b,n0a,n0b);
    c0 = F2x_mulspec(a0,b0,na,nb);

    c2 = F2x_addspec(a0,a,na,n0a);
    c1 = F2x_addspec(b0,b,nb,n0b);

    c1 = F2x_mul(c1,c2);
    c2 = F2x_add(c0,c);

    c2 = F2x_add(c1,c2);
    c0 = F2x_addshift(c0,c2,n0);
  }
  else
  {
    c  = F2x_mulspec(a,b,n0a,nb);
    c0 = F2x_mulspec(a0,b,na,nb);
  }
  c0 = F2x_addshift(c0,c,n0);
  return F2x_shiftip(av,c0, v);
}

GEN
F2x_mul(GEN x, GEN y)
{
  GEN z = F2x_mulspec(x+2,y+2, lgpol(x),lgpol(y));
  z[1] = x[1]; return z;
}

GEN
F2x_sqr(GEN x)
{
  const ulong sq[]={0,1,4,5,16,17,20,21,64,65,68,69,80,81,84,85};
  long i,ii,j,jj;
  long lx=lg(x), lz=2+((lx-2)<<1);
  GEN z;
  z = cgetg(lz, t_VECSMALL); z[1]=x[1];
  for (j=2,jj=2;j<lx;j++,jj++)
  {
    ulong x1=((ulong)x[j]&HIGHMASK)>>BITS_IN_HALFULONG;
    ulong x2=(ulong)x[j]&LOWMASK;
    z[jj]=0;
    if (x2)
      for(i=0,ii=0;i<BITS_IN_HALFULONG;i+=4,ii+=8)
        z[jj]|=sq[(x2>>i)&15UL]<<ii;
    z[++jj]=0;
    if (x1)
      for(i=0,ii=0;i<BITS_IN_HALFULONG;i+=4,ii+=8)
        z[jj]|=sq[(x1>>i)&15UL]<<ii;
  }
  return F2x_renormalize(z, lz);
}

static GEN
F2x_pow2n(GEN x, long n)
{
  long i;
  for(i=1;i<=n;i++)
    x = F2x_sqr(x);
  return x;
}

int
F2x_issquare(GEN x)
{
  const ulong mask = (ULONG_MAX/3UL)*2;
  ulong i, lx = lg(x);
  for (i=2; i<lx; i++)
    if ((x[i]&mask)) return 0;
  return 1;
}

/* Assume x is a perfect square */
GEN
F2x_sqrt(GEN x)
{
  const ulong sq[]={0,1,4,5,2,3,6,7,8,9,12,13,10,11,14,15};
  long i,ii,j,jj;
  long lx=lg(x), lz=2+((lx-1)>>1);
  GEN z;
  z = cgetg(lz, t_VECSMALL); z[1]=x[1];
  for (j=2,jj=2;jj<lz;j++,jj++)
  {
    ulong x2=x[j++];
    z[jj]=0;
    if (x2)
      for(i=0,ii=0;ii<BITS_IN_HALFULONG;i+=8,ii+=4)
      {
        ulong rl = (x2>>i)&15UL, rh = (x2>>(i+4))&15UL;
        z[jj]|=sq[rl|(rh<<1)]<<ii;
      }
    if (j<lx)
    {
      x2 = x[j];
      if (x2)
        for(i=0,ii=0;ii<BITS_IN_HALFULONG;i+=8,ii+=4)
        {
          ulong rl = (x2>>i)&15UL, rh = (x2>>(i+4))&15UL;
          z[jj]|=(sq[rl|(rh<<1)]<<ii)<<BITS_IN_HALFULONG;
        }
    }
  }
  return F2x_renormalize(z, lz);
}

static GEN
F2x_shiftneg(GEN y, ulong d)
{
  long db, dl=dvmdsBIL(d, &db);
  long i, ly = lg(y), lx = ly-dl;
  GEN x = cgetg(lx, t_VECSMALL);
  x[1] = y[1];
  if (db)
  {
    ulong dc=BITS_IN_LONG-db;
    ulong r=0;
    for(i=lx-1; i>=2; i--)
    {
      x[i] = (((ulong)y[i+dl])>>db)|r;
      r = ((ulong)y[i+dl])<<dc;
    }
  }
  else
    for(i=2; i<lx; i++)
      x[i] = y[i+dl];
  return F2x_renormalize(x,lx);
}

static GEN
F2x_shiftpos(GEN y, ulong d)
{
  long db, dl=dvmdsBIL(d, &db);
  long i, ly = lg(y), lx = ly+dl+(!!db);
  GEN x = cgetg(lx, t_VECSMALL);
  x[1] = y[1]; for(i=0; i<dl; i++) x[i+2] = 0;
  if (db)
  {
    ulong dc=BITS_IN_LONG-db;
    ulong r=0;
    for(i=2; i<ly; i++)
    {
      x[i+dl] = (((ulong)y[i])<<db)|r;
      r = ((ulong)y[i])>>dc;
    }
    x[i+dl] = r;
  }
  else
    for(i=2; i<ly; i++)
      x[i+dl] = y[i];
  return F2x_renormalize(x,lx);
}

GEN
F2x_shift(GEN y, long d)
{
  return d<0 ? F2x_shiftneg(y,-d): F2x_shiftpos(y,d);
}

GEN
F2x_get_red(GEN T)
{
  return T;
}

/* separate from F2x_divrem for maximal speed. */
GEN
F2x_rem(GEN x, GEN y)
{
  long dx,dy;
  long lx=lg(x);
  dy = F2x_degree(y); if (!dy) return pol0_F2x(x[1]);
  dx = F2x_degree_lg(x,lx);
  x  = F2x_copy(x);
  while (dx>=dy)
  {
    F2x_addshiftip(x,y,dx-dy);
    while (lx>2 && x[lx-1]==0) lx--;
    dx = F2x_degree_lg(x,lx);
  }
  return F2x_renormalize(x, lx);
}

GEN
F2x_divrem(GEN x, GEN y, GEN *pr)
{
  long dx, dy, dz, lx = lg(x), vs = x[1];
  GEN z;

  dy = F2x_degree(y);
  if (dy<0) pari_err_INV("F2x_divrem",y);
  if (pr == ONLY_REM) return F2x_rem(x, y);
  if (!dy)
  {
    z = F2x_copy(x);
    if (pr && pr != ONLY_DIVIDES) *pr = pol0_F2x(vs);
    return z;
  }
  dx = F2x_degree_lg(x,lx);
  dz = dx-dy;
  if (dz < 0)
  {
    if (pr == ONLY_DIVIDES) return dx < 0? F2x_copy(x): NULL;
    z = pol0_F2x(vs);
    if (pr) *pr = F2x_copy(x);
    return z;
  }
  z = zero_zv(lg(x)-lg(y)+2); z[1] = vs;
  x = F2x_copy(x);
  while (dx>=dy)
  {
    F2x_set(z,dx-dy);
    F2x_addshiftip(x,y,dx-dy);
    while (lx>2 && x[lx-1]==0) lx--;
    dx = F2x_degree_lg(x,lx);
  }
  z = F2x_renormalize(z, lg(z));
  if (!pr) { cgiv(x); return z; }
  x = F2x_renormalize(x, lx);
  if (pr == ONLY_DIVIDES) {
    if (lg(x) == 2) { cgiv(x); return z; }
    avma = (pari_sp)(z + lg(z)); return NULL;
  }
  *pr = x; return z;
}

long
F2x_valrem(GEN x, GEN *Z)
{
  long v, v2, i, l=lg(x);
  GEN y;
  if (l==2) { *Z = F2x_copy(x); return LONG_MAX; }
  for (i=2; i<l && x[i]==0; i++) /*empty*/;
  v = i-2;
  v2 = (i < l)? vals(x[i]): 0;
  if (v+v2 == 0) { *Z = x; return 0; }
  l -= i-2;
  y = cgetg(l, t_VECSMALL); y[1] = x[1];
  if (v2 == 0)
    for (i=2; i<l; i++) y[i] = x[i+v];
  else if (l == 3)
    y[2] = ((ulong)x[2+v]) >> v2;
  else
  {
    const ulong sh = BITS_IN_LONG - v2;
    ulong r = x[2+v];
    for (i=3; i<l; i++)
    {
      y[i-1] = (x[i+v] << sh) | (r >> v2);
      r = x[i+v];
    }
    y[l-1] = r >> v2;
    (void)F2x_renormalize(y,l);
  }
  *Z = y; return (v << TWOPOTBITS_IN_LONG) + v2;
}

GEN
F2x_deflate(GEN x, long d)
{
  GEN y;
  long i,id, dy, dx = F2x_degree(x);
  if (d <= 1) return F2x_copy(x);
  if (dx < 0) return F2x_copy(x);
  dy = dx/d; /* dy+1 coefficients + 1 extra word for variable */
  y = zero_zv(nbits2lg(dy+1)-1); y[1] = x[1];
  for (i=id=0; i<=dy; i++,id+=d)
    if (F2x_coeff(x,id)) F2x_set(y, i);
  return y;
}

/* write p(X) = e(X^2) + Xo(X^2), shallow function */
void
F2x_even_odd(GEN p, GEN *pe, GEN *po)
{
  long n = F2x_degree(p), n0, n1, i;
  GEN p0, p1;

  if (n <= 0) { *pe = F2x_copy(p); *po = pol0_F2x(p[1]); return; }

  n0 = (n>>1)+1; n1 = n+1 - n0; /* n1 <= n0 <= n1+1 */
  p0 = zero_zv(nbits2lg(n0+1)-1); p0[1] = p[1];
  p1 = zero_zv(nbits2lg(n1+1)-1); p1[1] = p[1];
  for (i=0; i<n1; i++)
  {
    if (F2x_coeff(p,i<<1)) F2x_set(p0,i);
    if (F2x_coeff(p,1+(i<<1))) F2x_set(p1,i);
  }
  if (n1 != n0 && F2x_coeff(p,i<<1)) F2x_set(p0,i);
  *pe = F2x_renormalize(p0,lg(p0));
  *po = F2x_renormalize(p1,lg(p1));
}

GEN
F2x_deriv(GEN z)
{
  const ulong mask = ULONG_MAX/3UL;
  long i,l = lg(z);
  GEN x = cgetg(l, t_VECSMALL); x[1] = z[1];
  for (i=2; i<l; i++) x[i] = (((ulong)z[i])>>1)&mask;
  return F2x_renormalize(x,l);
}

GEN
F2x_gcd(GEN a, GEN b)
{
  pari_sp av = avma;
  if (lg(b) > lg(a)) swap(a, b);
  while (lgpol(b))
  {
    GEN c = F2x_rem(a,b);
    a = b; b = c;
    if (gc_needed(av,2))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"F2x_gcd (d = %ld)",F2x_degree(c));
      gerepileall(av,2, &a,&b);
    }
  }
  if (gc_needed(av,2)) a = gerepileuptoleaf(av, a);
  return a;
}

GEN
F2x_extgcd(GEN a, GEN b, GEN *ptu, GEN *ptv)
{
  pari_sp av=avma;
  GEN u,v,d,d1,v1;
  long vx = a[1];
  d = a; d1 = b;
  v = pol0_F2x(vx); v1 = pol1_F2x(vx);
  while (lgpol(d1))
  {
    GEN r, q = F2x_divrem(d,d1, &r);
    v = F2x_add(v,F2x_mul(q,v1));
    u=v; v=v1; v1=u;
    u=r; d=d1; d1=u;
    if (gc_needed(av,2))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"F2x_extgcd (d = %ld)",F2x_degree(d));
      gerepileall(av,5, &d,&d1,&u,&v,&v1);
    }
  }
  if (ptu) *ptu = F2x_div(F2x_add(d, F2x_mul(b,v)), a);
  *ptv = v;
  if (gc_needed(av,2)) gerepileall(av,ptu?3:2,&d,ptv,ptu);
  return d;
}

static GEN
F2x_halfgcd_i(GEN a, GEN b)
{
  pari_sp av=avma;
  GEN u,u1,v,v1;
  long vx = a[1];
  long n = (F2x_degree(a)+1)>>1;
  u1 = v = pol0_F2x(vx);
  u = v1 = pol1_F2x(vx);
  while (F2x_degree(b)>=n)
  {
    GEN r, q = F2x_divrem(a,b, &r);
    a = b; b = r; swap(u,u1); swap(v,v1);
    u1 = F2x_add(u1, F2x_mul(u, q));
    v1 = F2x_add(v1, F2x_mul(v, q));
    if (gc_needed(av,2))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"F2x_halfgcd (d = %ld)",F2x_degree(b));
      gerepileall(av,6, &a,&b,&u1,&v1,&u,&v);
    }
  }
  return gerepilecopy(av, mkmat2(mkcol2(u,u1), mkcol2(v,v1)));
}

GEN
F2x_halfgcd(GEN x, GEN y)
{
  pari_sp av;
  GEN M,q,r;
  if (F2x_degree(y)<F2x_degree(x)) return F2x_halfgcd_i(x,y);
  av = avma;
  q = F2x_divrem(y,x,&r);
  M = F2x_halfgcd_i(x,r);
  gcoeff(M,1,1) = F2x_add(gcoeff(M,1,1), F2x_mul(q, gcoeff(M,1,2)));
  gcoeff(M,2,1) = F2x_add(gcoeff(M,2,1), F2x_mul(q, gcoeff(M,2,2)));
  return gerepilecopy(av, M);
}

GEN
F2xq_mul(GEN x,GEN y,GEN pol)
{
  GEN z = F2x_mul(x,y);
  return F2x_rem(z,pol);
}

GEN
F2xq_sqr(GEN x,GEN pol)
{
  GEN z = F2x_sqr(x);
  return F2x_rem(z,pol);
}

GEN
F2xq_invsafe(GEN x, GEN T)
{
  GEN V, z = F2x_extgcd(T, x, NULL, &V);
  if (F2x_degree(z)) return NULL;
  return V;
}

GEN
F2xq_inv(GEN x,GEN T)
{
  pari_sp av=avma;
  GEN U = F2xq_invsafe(x, T);
  if (!U) pari_err_INV("F2xq_inv", F2x_to_ZX(x));
  return gerepileuptoleaf(av, U);
}

GEN
F2xq_div(GEN x,GEN y,GEN T)
{
  pari_sp av = avma;
  return gerepileuptoleaf(av, F2xq_mul(x,F2xq_inv(y,T),T));
}

static GEN
_F2xq_red(void *E, GEN x)
{ return F2x_rem(x, (GEN)E); }
static GEN
_F2xq_add(void *E, GEN x, GEN y)
{ (void)E; return F2x_add(x,y); }

static GEN
_F2xq_cmul(void *E, GEN P, long a, GEN x)
{
  GEN pol = (GEN) E;
  return F2x_coeff(P,a) ? x: pol0_F2x(pol[1]);
}
static GEN
_F2xq_sqr(void *E, GEN x)
{ return F2xq_sqr(x, (GEN) E); }

static GEN
_F2xq_mul(void *E, GEN x, GEN y)
{ return F2xq_mul(x,y, (GEN) E); }

static GEN
_F2xq_one(void *E)
{
  GEN pol = (GEN) E;
  return pol1_F2x(pol[1]);
}
static GEN
_F2xq_zero(void *E)
{
  GEN pol = (GEN) E;
  return pol0_F2x(pol[1]);
}

GEN
F2xq_pow(GEN x, GEN n, GEN pol)
{
  pari_sp av=avma;
  GEN y;

  if (!signe(n)) return pol1_F2x(x[1]);
  if (is_pm1(n)) /* +/- 1 */
    return (signe(n) < 0)? F2xq_inv(x,pol): F2x_copy(x);

  if (signe(n) < 0) x = F2xq_inv(x,pol);
  y = gen_pow(x, n, (void*)pol, &_F2xq_sqr, &_F2xq_mul);
  return gerepileupto(av, y);
}

GEN
F2xq_powu(GEN x, ulong n, GEN pol)
{
  pari_sp av=avma;
  GEN y;
  switch(n)
  {
    case 0: return pol1_F2x(x[1]);
    case 1: return F2x_copy(x);
    case 2: return F2xq_sqr(x,pol);
  }
  y = gen_powu(x, n, (void*)pol, &_F2xq_sqr, &_F2xq_mul);
  return gerepileupto(av, y);
}

GEN
F2xq_pow_init(GEN x, GEN n, long k,  GEN T)
{
  return gen_pow_init(x, n, k, (void*)T, &_F2xq_sqr, &_F2xq_mul);
}

GEN
F2xq_pow_table(GEN R, GEN n, GEN T)
{
  return gen_pow_table(R, n, (void*)T, &_F2xq_one, &_F2xq_mul);
}

/* generates the list of powers of x of degree 0,1,2,...,l*/
GEN
F2xq_powers(GEN x, long l, GEN T)
{
  int use_sqr = 2*F2x_degree(x) >= F2x_degree(T);
  return gen_powers(x, l, use_sqr, (void*)T, &_F2xq_sqr, &_F2xq_mul, &_F2xq_one);
}

GEN
F2xq_matrix_pow(GEN y, long n, long m, GEN P)
{
  return F2xV_to_F2m(F2xq_powers(y,m-1,P),n);
}

GEN
F2x_Frobenius(GEN T)
{
  return F2xq_sqr(polx_F2x(T[1]), T);
}

GEN
F2x_matFrobenius(GEN T)
{
  long n = F2x_degree(T);
  return F2xq_matrix_pow(F2x_Frobenius(T), n, n, T);
}

static struct bb_algebra F2xq_algebra = { _F2xq_red, _F2xq_add, _F2xq_add,
              _F2xq_mul, _F2xq_sqr, _F2xq_one, _F2xq_zero};

GEN
F2x_F2xqV_eval(GEN Q, GEN x, GEN T)
{
  long d = F2x_degree(Q);
  return gen_bkeval_powers(Q,d,x,(void*)T,&F2xq_algebra,_F2xq_cmul);
}

GEN
F2x_F2xq_eval(GEN Q, GEN x, GEN T)
{
  long d = F2x_degree(Q);
  int use_sqr = 2*F2x_degree(x) >= F2x_degree(T);
  return gen_bkeval(Q, d, x, use_sqr, (void*)T, &F2xq_algebra, _F2xq_cmul);
}

static GEN
F2xq_autpow_sqr(void * T, GEN x) { return F2x_F2xq_eval(x, x, (GEN) T); }

static GEN
F2xq_autpow_mul(void * T, GEN x, GEN y) { return F2x_F2xq_eval(x, y, (GEN) T); }

GEN
F2xq_autpow(GEN x, long n, GEN T)
{
  if (n==0) return F2x_rem(polx_F2x(x[1]), T);
  if (n==1) return F2x_rem(x, T);
  return gen_powu(x,n,(void*)T,F2xq_autpow_sqr,F2xq_autpow_mul);
}

ulong
F2xq_trace(GEN x, GEN T)
{
  pari_sp av = avma;
  ulong t;
  long n = F2x_degree(T)-1;
  GEN z = F2x_mul(x, F2x_deriv(T));
  z = F2x_rem(z, T);
  t = F2x_degree(z)<n ? 0 : 1;
  avma = av; return t;
}

GEN
F2xq_conjvec(GEN x, GEN T)
{
  long i, l = F2x_degree(T);
  GEN z = cgetg(l,t_COL);
  gel(z,1) = F2x_copy(x);
  for (i=2; i<l; i++) gel(z,i) = F2xq_sqr(gel(z,i-1), T);
  return z;
}

static GEN
_F2xq_pow(void *data, GEN x, GEN n)
{
  GEN pol = (GEN) data;
  return F2xq_pow(x,n, pol);
}

static GEN
_F2xq_rand(void *data)
{
  pari_sp av=avma;
  GEN pol = (GEN) data;
  long d = F2x_degree(pol);
  GEN z;
  do
  {
    avma = av;
    z = random_F2x(d,pol[1]);
  } while (lgpol(z)==0);
  return z;
}

static GEN F2xq_easylog(void* E, GEN a, GEN g, GEN ord);

static const struct bb_group F2xq_star={_F2xq_mul,_F2xq_pow,_F2xq_rand,hash_GEN,F2x_equal,F2x_equal1,F2xq_easylog};

GEN
F2xq_order(GEN a, GEN ord, GEN T)
{
  return gen_order(a,ord,(void*)T,&F2xq_star);
}

static long
F2x_is_smooth_squarefree(GEN f, long r)
{
  pari_sp av = avma;
  long i;
  GEN sx = polx_F2x(f[1]), a = sx;
  for(i=1;  ;i++)
  {
    a = F2xq_sqr(F2x_rem(a,f),f);
    if (F2x_equal(a, F2x_rem(sx,f))) {avma = av; return 1;}
    if (i==r) {avma = av; return 0;}
    f = F2x_div(f, F2x_gcd(F2x_add(a,sx),f));
  }
}

static long
F2x_is_smooth(GEN g, long r)
{
  GEN f = gen_0;
  if (lgpol(g)==0) return 0;
  while (1)
  {
    f = F2x_gcd(g, F2x_deriv(g));
    if (!F2x_is_smooth_squarefree(F2x_div(g, f), r))
      return 0;
    if (F2x_degree(f)==0) return 1;
    g = F2x_issquare(f) ? F2x_sqrt(f): f;
  }
}

static GEN
F2x_factorel(GEN h)
{
  GEN F = F2x_factor(h);
  GEN F1 = gel(F, 1), F2 = gel(F, 2);
  long i, l1 = lg(F1)-1;
  GEN p2 = cgetg(l1+1, t_VECSMALL);
  GEN e2 = cgetg(l1+1, t_VECSMALL);
  for (i = 1; i <= l1; ++i)
  {
    p2[i] = mael(F1, i, 2);
    e2[i] = F2[i];
  }
  return mkmat2(p2, e2);
}

static GEN
mkF2(ulong x, long v) { return mkvecsmall2(v, x); }

static GEN F2xq_log_Coppersmith_d(GEN W, GEN g, long r, long n, GEN T, GEN mo);

static GEN
F2xq_log_from_rel(GEN W, GEN rel, long r, long n, GEN T, GEN m)
{
  pari_sp av = avma;
  GEN F = gel(rel,1), E = gel(rel,2), o = gen_0;
  long i, l = lg(F);
  for(i=1; i<l; i++)
  {
    GEN R = gel(W, F[i]);
    if (signe(R)==0) /* Already failed */
      return NULL;
    else if (signe(R)<0) /* Not yet tested */
    {
      setsigne(gel(W,F[i]),0);
      R = F2xq_log_Coppersmith_d(W, mkF2(F[i],T[1]), r, n, T, m);
      if (!R) return NULL;
    }
    o = Fp_add(o, mulis(R, E[i]), m);
  }
  return gerepileuptoint(av, o);
}

static GEN
F2xq_log_Coppersmith_d(GEN W, GEN g, long r, long n, GEN T, GEN mo)
{
  pari_sp av = avma, av2;
  long dg = F2x_degree(g), k = r-1, m = maxss((dg-k)/2,0);
  long i, j, l = dg-m, N;
  GEN v = cgetg(k+m+1,t_MAT);
  long dT = F2x_degree(T);
  long h = dT>>n, d = dT-(h<<n);
  GEN R = F2x_add(F2x_shift(pol1_F2x(T[1]), dT), T);
  GEN z = F2x_rem(F2x_shift(pol1_F2x(T[1]),h), g);
  for(i=1; i<=k+m; i++)
  {
    gel(v,i) = F2x_to_F2v(F2x_shift(z,-l),m);
    z = F2x_rem(F2x_shift(z,1),g);
  }
  v = F2m_ker(v);
  for(i=1; i<=k; i++)
    gel(v,i) = F2v_to_F2x(gel(v,i),T[1]);
  N = 1<<k;
  av2 = avma;
  for (i=1; i<N; i++)
  {
    GEN p,q,qh,a,b;
    avma = av2;
    q = pol0_F2x(T[1]);
    for(j=0; j<k; j++)
      if (i&(1UL<<j))
        q = F2x_add(q, gel(v,j+1));
    qh= F2x_shift(q,h);
    p = F2x_rem(qh,g);
    b = F2x_add(F2x_mul(R, F2x_pow2n(q, n)), F2x_shift(F2x_pow2n(p, n), d));
    if (lgpol(b)==0 || !F2x_is_smooth(b, r)) continue;
    a = F2x_div(F2x_add(qh,p),g);
    if (F2x_degree(F2x_gcd(a,q)) &&  F2x_degree(F2x_gcd(a,p))) continue;
    if (!(lgpol(a)==0 || !F2x_is_smooth(a, r)))
    {
      GEN F = F2x_factorel(b);
      GEN G = F2x_factorel(a);
      GEN FG = vecsmall_concat(vecsmall_append(gel(F, 1), 2), gel(G, 1));
      GEN E  = vecsmall_concat(vecsmall_append(gel(F, 2), -d),
                               zv_z_mul(gel(G, 2),-(1L<<n)));
      GEN R  = famatsmall_reduce(mkmat2(FG, E));
      GEN l  = F2xq_log_from_rel(W, R, r, n, T, mo);
      if (!l) continue;
      l = Fp_div(l,int2n(n),mo);
      if (dg <= r)
      {
        affii(l,gel(W,g[2]));
        if (DEBUGLEVEL>1) err_printf("Found %lu\n", g[2]);
      }
      return gerepileuptoint(av, l);
    }
  }
  avma = av;
  return NULL;
}

static GEN
F2xq_log_find_rel(GEN b, long r, GEN T, GEN *g, ulong *e)
{
  pari_sp av = avma;
  while (1)
  {
    GEN M;
    *g = F2xq_mul(*g, b, T); (*e)++;
    M = F2x_halfgcd(*g,T);
    if (F2x_is_smooth(gcoeff(M,1,1), r))
    {
      GEN z = F2x_add(F2x_mul(gcoeff(M,1,1),*g), F2x_mul(gcoeff(M,1,2),T));
      if (F2x_is_smooth(z, r))
      {
        GEN F = F2x_factorel(z);
        GEN G = F2x_factorel(gcoeff(M,1,1));
        GEN rel = mkmat2(vecsmall_concat(gel(F, 1),gel(G, 1)),
                         vecsmall_concat(gel(F, 2),zv_neg(gel(G, 2))));
        gerepileall(av, 2, g, &rel);
        return rel;
      }
    }
    if (gc_needed(av,2))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"F2xq_log_find_rel");
      *g = gerepileuptoleaf(av, *g);
    }
  }
}

static GEN
F2xq_log_Coppersmith_rec(GEN W, long r2, GEN a, long r, long n, GEN T, GEN m)
{
  GEN b = polx_F2x(T[1]);
  ulong AV = 0;
  GEN g = a, bad = pol0_F2x(T[1]);
  pari_timer ti;
  while(1)
  {
    long i, l;
    GEN V, F, E, Ao;
    timer_start(&ti);
    V = F2xq_log_find_rel(b, r2, T, &g, &AV);
    if (DEBUGLEVEL>1) timer_printf(&ti,"%ld-smooth element",r2);
    F = gel(V,1); E = gel(V,2);
    l = lg(F);
    Ao = gen_0;
    for(i=1; i<l; i++)
    {
      GEN Fi = mkF2(F[i], T[1]);
      GEN R;
      if (F2x_degree(Fi) <= r)
      {
        if (signe(gel(W,F[i]))==0)
          break;
        else if (signe(gel(W,F[i]))<0)
        {
          setsigne(gel(W,F[i]),0);
          R = F2xq_log_Coppersmith_d(W,Fi,r,n,T,m);
        } else
          R = gel(W,F[i]);
      }
      else
      {
        if (F2x_equal(Fi,bad)) break;
        R = F2xq_log_Coppersmith_d(W,Fi,r,n,T,m);
        if (!R) bad = Fi;
      }
      if (!R) break;
      Ao = Fp_add(Ao, mulis(R, E[i]), m);
    }
    if (i==l) return subiu(Ao,AV);
  }
}

/* Coppersmith:
 T*X^e = X^(h*2^n)-R
 (u*x^h + v)^(2^n) = u^(2^n)*X^(h*2^n)+v^(2^n)
 (u*x^h + v)^(2^n) = u^(2^n)*R+v^(2^n)
*/

static GEN
rel_Coppersmith(GEN u, GEN v, long h, GEN R, long r, long n, long d)
{
  GEN b, F, G, M;
  GEN a = F2x_add(F2x_shift(u, h), v);
  if (!F2x_is_smooth(a, r)) return NULL;
  b = F2x_add(F2x_mul(R, F2x_pow2n(u, n)), F2x_shift(F2x_pow2n(v, n),d));
  if (!F2x_is_smooth(b, r)) return NULL;
  F = F2x_factorel(a);
  G = F2x_factorel(b);
  M = mkmat2(vecsmall_concat(gel(F, 1), vecsmall_append(gel(G, 1), 2)),
             vecsmall_concat(zv_z_mul(gel(F, 2),1UL<<n), vecsmall_append(zv_neg(gel(G, 2)),d)));
  return famatsmall_reduce(M);
}

GEN
F2xq_log_Coppersmith_worker(GEN u, long i, GEN V, GEN R)
{
  long r = V[1], h = V[2], n = V[3], d = V[4];
  pari_sp ltop = avma;
  GEN v = mkF2(0,u[1]);
  GEN L = cgetg(2*i+1, t_VEC);
  pari_sp av = avma;
  long j;
  long nbtest=0, rel = 1;
  for(j=1; j<=i; j++)
  {
    v[2] = j;
    avma = av;
    if (F2x_degree(F2x_gcd(u,v))==0)
    {
      GEN z = rel_Coppersmith(u, v, h, R, r, n, d);
      nbtest++;
      if (z) { gel(L, rel++) = z; av = avma; }
      if (i==j) continue;
      z = rel_Coppersmith(v, u, h, R, r, n, d);
      nbtest++;
      if (z) { gel(L, rel++) = z; av = avma; }
    }
  }
  setlg(L,rel);
  return gerepilecopy(ltop, mkvec2(stoi(nbtest), L));
}

static GEN
F2xq_log_Coppersmith(long nbrel, long r, long n, GEN T)
{
  long dT = F2x_degree(T);
  long h = dT>>n, d = dT-(h<<n);
  GEN R = F2x_add(F2x_shift(pol1_F2x(T[1]), dT), T);
  GEN u = mkF2(0,T[1]);
  long rel = 1, nbtest = 0;
  GEN M = cgetg(nbrel+1, t_VEC);
  long i = 0;
  GEN worker = snm_closure(is_entry("_F2xq_log_Coppersmith_worker"),
               mkvec2(mkvecsmall4(r, h, n, d), R));
  struct pari_mt pt;
  long running, pending = 0, stop=0;
  mt_queue_start(&pt, worker);
  if (DEBUGLEVEL) err_printf("Coppersmith (R = %ld): ",F2x_degree(R));
  while ((running = !stop) || pending)
  {
    GEN L, done;
    long j, l;
    u[2] = i;
    mt_queue_submit(&pt, 0, running ? mkvec2(u, stoi(i)): NULL);
    done = mt_queue_get(&pt, NULL, &pending);
    if (!done) continue;
    L = gel(done, 2); nbtest += itos(gel(done,1));
    l = lg(L);
    if (l > 1)
    {
      for (j=1; j<l; j++)
      {
        if (rel>nbrel) break;
        gel(M,rel++) = gel(L,j);
        if (DEBUGLEVEL && (rel&511UL)==0)
          err_printf("%ld%%[%ld] ",rel*100/nbrel,i);
      }
    }
    if (rel>nbrel) stop=1;
    i++;
  }
  mt_queue_end(&pt);
  if (DEBUGLEVEL) err_printf(": %ld tests\n", nbtest);
  return M;
}

static GEN
smallirred_F2x(ulong n, long sv)
{
  GEN a = zero_zv(nbits2lg(n+1)-1);
  a[1] = sv; F2x_set(a,n); a[2]++;
  while (!F2x_is_irred(a)) a[2]+=2;
  return a;
}

static GEN
check_kernel(long N, GEN M, long nbi, GEN T, GEN m)
{
  pari_sp av = avma;
  GEN K = FpMs_leftkernel_elt(M, N, m);
  long i, f=0, tbs;
  long l = lg(K), lm = lgefint(m);
  GEN idx = diviiexact(int2um1(F2x_degree(T)),m);
  GEN g = F2xq_pow(polx_F2x(T[1]), idx, T);
  GEN tab;
  pari_timer ti;
  if (DEBUGLEVEL) timer_start(&ti);
  K = FpC_Fp_mul(K, Fp_inv(gel(K,2), m), m);
  tbs = maxss(1, expu(nbi/expi(m)));
  tab = F2xq_pow_init(g, int2n(F2x_degree(T)), tbs, T);
  for(i=1; i<l; i++)
  {
    GEN k = gel(K,i);
    if (signe(k)==0 || !F2x_equal(F2xq_pow_table(tab, k, T),
                                  F2xq_pow(mkF2(i,T[1]), idx, T)))
      gel(K,i) = cgetineg(lm);
    else
      f++;
  }
  if (DEBUGLEVEL) timer_printf(&ti,"found %ld/%ld logs", f, nbi);
  return gerepileupto(av, K);
}

static GEN
F2xq_log_index(GEN a0, GEN b0, GEN m, GEN T0)
{
  pari_sp av = avma;
  GEN  M, S, a, b, Ao=NULL, Bo=NULL, W, e;
  pari_timer ti;
  long n = F2x_degree(T0), r = (long) (sqrt((double) 2*n))-(n>100);
  GEN T = smallirred_F2x(n,T0[1]);
  long d = 2, r2 = 3*r/2, d2 = 2;
  long N = (1UL<<(r+1))-1UL;
  long nbi = itos(ffsumnbirred(gen_2, r)), nbrel=nbi*5/4;
  if (DEBUGLEVEL)
  {
    err_printf("F2xq_log: Parameters r=%ld r2=%ld\n", r,r2);
    err_printf("F2xq_log: Size FB=%ld rel. needed=%ld\n", nbi, nbrel);
    timer_start(&ti);
  }
  S = Flx_to_F2x(Flx_ffisom(F2x_to_Flx(T0),F2x_to_Flx(T),2));
  a = F2x_F2xq_eval(a0, S, T);
  b = F2x_F2xq_eval(b0, S, T);
  if (DEBUGLEVEL) timer_printf(&ti,"model change");
  M = F2xq_log_Coppersmith(nbrel,r,d,T);
  if(DEBUGLEVEL)
    timer_printf(&ti,"relations");
  W = check_kernel(N, M, nbi, T, m);
  timer_start(&ti);
  Ao = F2xq_log_Coppersmith_rec(W, r2, a, r, d2, T, m);
  if (DEBUGLEVEL) timer_printf(&ti,"smooth element");
  Bo = F2xq_log_Coppersmith_rec(W, r2, b, r, d2, T, m);
  if (DEBUGLEVEL) timer_printf(&ti,"smooth generator");
  e = Fp_div(Ao, Bo, m);
  if (!F2x_equal(F2xq_pow(b0,e,T0),a0)) pari_err_BUG("F2xq_log");
  return gerepileupto(av, e);
}

static GEN
F2xq_easylog(void* E, GEN a, GEN g, GEN ord)
{
  if (F2x_equal1(a)) return gen_0;
  if (F2x_equal(a,g)) return gen_1;
  if (typ(ord)!=t_INT) return NULL;
  if (expi(ord)<28) return NULL;
  return F2xq_log_index(a,g,ord,(GEN)E);
}

GEN
F2xq_log(GEN a, GEN g, GEN ord, GEN T)
{
  GEN z, v = get_arith_ZZM(ord);
  ord = mkvec2(gel(v,1),ZM_famat_limit(gel(v,2),int2n(28)));
  z = gen_PH_log(a,g,ord,(void*)T,&F2xq_star);
  return z? z: cgetg(1,t_VEC);
}

GEN
F2xq_Artin_Schreier(GEN a, GEN T)
{
  pari_sp ltop=avma;
  long j,N = F2x_degree(T);
  GEN Q = F2x_matFrobenius(T);
  for (j=1; j<=N; j++)
    F2m_flip(Q,j,j);
  F2v_add_inplace(gel(Q,1),a);
  Q = F2m_ker_sp(Q,0);
  if (lg(Q)!=2) return NULL;
  Q = gel(Q,1);
  Q[1] = T[1];
  return gerepileuptoleaf(ltop, F2x_renormalize(Q, lg(Q)));
}

GEN
F2xq_sqrt_fast(GEN c, GEN sqx, GEN T)
{
  GEN c0, c1;
  F2x_even_odd(c, &c0, &c1);
  return F2x_add(c0, F2xq_mul(c1, sqx, T));
}

static int
F2x_is_x(GEN a) { return lg(a)==3 && a[2]==2; }

GEN
F2xq_sqrt(GEN a, GEN T)
{
  pari_sp av = avma;
  long n = F2x_degree(T);
  GEN sqx;
  if (n==1) return F2x_copy(a);
  if (n==2) return F2xq_sqr(a,T);
  sqx = F2xq_autpow(mkF2(4, T[1]), n-1, T);
  return gerepileuptoleaf(av, F2x_is_x(a)? sqx: F2xq_sqrt_fast(a,sqx,T));
}

GEN
F2xq_sqrtn(GEN a, GEN n, GEN T, GEN *zeta)
{
  if (!lgpol(a))
  {
    if (signe(n) < 0) pari_err_INV("F2xq_sqrtn",a);
    if (zeta)
      *zeta=pol1_F2x(T[1]);
    return pol0_F2x(T[1]);
  }
  return gen_Shanks_sqrtn(a,n,subiu(powuu(2,F2x_degree(T)),1),zeta,(void*)T,&F2xq_star);
}

GEN
gener_F2xq(GEN T, GEN *po)
{
  long i, j, vT = T[1], f = F2x_degree(T);
  pari_sp av0 = avma, av;
  GEN g, L2, o, q;

  if (f == 1) {
    if (po) *po = mkvec2(gen_1, trivial_fact());
    return pol1_F2x(vT);
  }
  q = int2um1(f);
  o = factor_pn_1(gen_2,f);
  L2 = leafcopy( gel(o, 1) );
  for (i = j = 1; i < lg(L2); i++)
  {
    if (absequaliu(gel(L2,i),2)) continue;
    gel(L2,j++) = diviiexact(q, gel(L2,i));
  }
  setlg(L2, j);
  for (av = avma;; avma = av)
  {
    g = random_F2x(f, vT);
    if (F2x_degree(g) < 1) continue;
    for (i = 1; i < j; i++)
    {
      GEN a = F2xq_pow(g, gel(L2,i), T);
      if (F2x_equal1(a)) break;
    }
    if (i == j) break;
  }
  if (!po) g = gerepilecopy(av0, g);
  else {
    *po = mkvec2(int2um1(f), o);
    gerepileall(av0, 2, &g, po);
  }
  return g;
}

static GEN
_F2xq_neg(void *E, GEN x)
{ (void) E; return F2x_copy(x); }

static GEN
_F2xq_rmul(void *E, GEN x, GEN y)
{ (void) E; return F2x_mul(x,y); }

static GEN
_F2xq_inv(void *E, GEN x)
{ return F2xq_inv(x, (GEN) E); }

static int
_F2xq_equal0(GEN x) { return lgpol(x)==0; }

static GEN
_F2xq_s(void *E, long x)
{ GEN T = (GEN) E;
  long v = get_F2x_var(T);
  return odd(x)? pol1_F2x(v): pol0_F2x(v);
}

static const struct bb_field F2xq_field={_F2xq_red,_F2xq_add,_F2xq_rmul,_F2xq_neg,
                                         _F2xq_inv,_F2xq_equal0,_F2xq_s};

const struct bb_field *get_F2xq_field(void **E, GEN T)
{
  *E = (void *) T;
  return &F2xq_field;
}

/***********************************************************************/
/**                                                                   **/
/**                             F2v                                   **/
/**                                                                   **/
/***********************************************************************/
/* F2v objects are defined as follows:
   An F2v is a t_VECSMALL:
   v[0] = codeword
   v[1] = number of components
   x[2] = a_0...a_31 x[3] = a_32..a_63, etc.  on 32bit
   x[2] = a_0...a_63 x[3] = a_64..a_127, etc. on 64bit

   where the a_i are bits.
*/

GEN
F2c_to_ZC(GEN x)
{
  long l=x[1]+1;
  GEN  z = cgetg(l, t_COL);
  long i,j,k;
  for (i=2,k=1; i<lg(x); i++)
    for (j=0; j<BITS_IN_LONG && k<l; j++,k++)
      gel(z,k) = (x[i]&(1UL<<j))? gen_1: gen_0;
  return z;
}
GEN
F2c_to_mod(GEN x)
{
  long l=x[1]+1;
  GEN  z = cgetg(l, t_COL);
  GEN _0 = mkintmod(gen_0,gen_2);
  GEN _1 = mkintmod(gen_1,gen_2);
  long i,j,k;
  for (i=2,k=1; i<lg(x); i++)
    for (j=0; j<BITS_IN_LONG && k<l; j++,k++)
      gel(z,k) = (x[i]&(1UL<<j))? _1: _0;
  return z;
}

/* x[a..b], a <= b */
GEN
F2v_slice(GEN x, long a, long b)
{
  long i,j,k, l = b-a+1;
  GEN z = cgetg(nbits2lg(l), t_VECSMALL);
  z[1] = l;
  for(i=a,k=1,j=BITS_IN_LONG; i<=b; i++,j++)
  {
    if (j==BITS_IN_LONG) { j=0; z[++k]=0; }
    if (F2v_coeff(x,i)) z[k] |= 1UL<<j;
  }
  return z;
}
/* x[a..b,], a <= b */
GEN
F2m_rowslice(GEN x, long a, long b)
{
  long i, l;
  GEN y = cgetg_copy(x, &l);
  for (i = 1; i < l; i++) gel(y,i) = F2v_slice(gel(x,i),a,b);
  return y;
}

GEN
F2m_to_ZM(GEN z)
{
  long i, l = lg(z);
  GEN x = cgetg(l,t_MAT);
  for (i=1; i<l; i++) gel(x,i) = F2c_to_ZC(gel(z,i));
  return x;
}
GEN
F2m_to_mod(GEN z)
{
  long i, l = lg(z);
  GEN x = cgetg(l,t_MAT);
  for (i=1; i<l; i++) gel(x,i) = F2c_to_mod(gel(z,i));
  return x;
}

GEN
F2v_to_Flv(GEN x)
{
  long l=x[1]+1;
  GEN  z=cgetg(l, t_VECSMALL);
  long i,j,k;
  for (i=2,k=1; i<lg(x); i++)
    for (j=0; j<BITS_IN_LONG && k<l; j++,k++)
      z[k] = (x[i]>>j)&1UL;
  return z;
}

GEN
F2m_to_Flm(GEN z)
{
  long i, l = lg(z);
  GEN x = cgetg(l,t_MAT);
  for (i=1; i<l; i++) gel(x,i) = F2v_to_Flv(gel(z,i));
  return x;
}

GEN
ZV_to_F2v(GEN x)
{
  long l = lg(x)-1;
  GEN z = cgetg(nbits2lg(l), t_VECSMALL);
  long i,j,k;
  z[1] = l;
  for(i=1,k=1,j=BITS_IN_LONG; i<=l; i++,j++)
  {
    if (j==BITS_IN_LONG) { j=0; z[++k]=0; }
    if (mpodd(gel(x,i))) z[k] |= 1UL<<j;
  }
  return z;
}

GEN
RgV_to_F2v(GEN x)
{
  long l = lg(x)-1;
  GEN z = cgetg(nbits2lg(l), t_VECSMALL);
  long i,j,k;
  z[1] = l;
  for(i=1,k=1,j=BITS_IN_LONG; i<=l; i++,j++)
  {
    if (j==BITS_IN_LONG) { j=0; z[++k]=0; }
    if (Rg_to_F2(gel(x,i))) z[k] |= 1UL<<j;
  }
  return z;
}

GEN
Flv_to_F2v(GEN x)
{
  long l = lg(x)-1;
  GEN z = cgetg(nbits2lg(l), t_VECSMALL);
  long i,j,k;
  z[1] = l;
  for(i=1,k=1,j=BITS_IN_LONG; i<=l; i++,j++)
  {
    if (j==BITS_IN_LONG) { j=0; z[++k]=0; }
    if (x[i]&1L) z[k] |= 1UL<<j;
  }
  return z;
}

GEN
ZM_to_F2m(GEN x)
{ pari_APPLY_same(ZV_to_F2v(gel(x,i))) }

GEN
RgM_to_F2m(GEN x)
{ pari_APPLY_same(RgV_to_F2v(gel(x,i))) }

GEN
Flm_to_F2m(GEN x)
{ pari_APPLY_same(Flv_to_F2v(gel(x,i))) }

GEN
const_F2v(long m)
{
  long i, l = nbits2lg(m);
  GEN c = cgetg(l, t_VECSMALL);
  c[1] = m;
  for (i = 2; i < l; i++) uel(c,i) = -1UL;
  if (remsBIL(m)) uel(c,l-1) = (1UL<<remsBIL(m))-1UL;
  return c;
}

/* Allow lg(y)<lg(x) */
void
F2v_add_inplace(GEN x, GEN y)
{
  long n = lg(y);
  long r = (n-2)&7L, q = n-r, i;
  for (i = 2; i < q; i += 8)
  {
    x[  i] ^= y[  i]; x[1+i] ^= y[1+i]; x[2+i] ^= y[2+i]; x[3+i] ^= y[3+i];
    x[4+i] ^= y[4+i]; x[5+i] ^= y[5+i]; x[6+i] ^= y[6+i]; x[7+i] ^= y[7+i];
  }
  switch (r)
  {
    case 7: x[i] ^= y[i]; i++; case 6: x[i] ^= y[i]; i++;
    case 5: x[i] ^= y[i]; i++; case 4: x[i] ^= y[i]; i++;
    case 3: x[i] ^= y[i]; i++; case 2: x[i] ^= y[i]; i++;
    case 1: x[i] ^= y[i]; i++;
  }
}

/***********************************************************************/
/**                                                                   **/
/**                               F2xV                                **/
/**                                                                   **/
/***********************************************************************/
/* F2xV are t_VEC with F2x coefficients. */

GEN
FlxC_to_F2xC(GEN x)
{ pari_APPLY_type(t_COL, Flx_to_F2x(gel(x,i))) }

GEN
F2xC_to_FlxC(GEN x)
{ pari_APPLY_type(t_COL, F2x_to_Flx(gel(x,i))) }

GEN
F2xC_to_ZXC(GEN x)
{ pari_APPLY_type(t_COL, F2x_to_ZX(gel(x,i))) }

GEN
F2xV_to_F2m(GEN x, long n)
{ pari_APPLY_type(t_MAT, F2x_to_F2v(gel(x,i), n)) }

/***********************************************************************/
/**                                                                   **/
/**                             F2xX                                  **/
/**                                                                   **/
/***********************************************************************/

GEN
F2xX_renormalize(GEN /*in place*/ x, long lx)
{ return FlxX_renormalize(x, lx); }

GEN
pol1_F2xX(long v, long sv) { return pol1_FlxX(v, sv); }

GEN
polx_F2xX(long v, long sv) { return polx_FlxX(v, sv); }

long
F2xY_degreex(GEN b)
{
  long deg = 0, i;
  if (!signe(b)) return -1;
  for (i = 2; i < lg(b); ++i)
    deg = maxss(deg, F2x_degree(gel(b, i)));
  return deg;
}

GEN
FlxX_to_F2xX(GEN B)
{
  long lb=lg(B);
  long i;
  GEN b=cgetg(lb,t_POL);
  b[1]=evalsigne(1)|(((ulong)B[1])&VARNBITS);
  for (i=2; i<lb; i++)
    gel(b,i) = Flx_to_F2x(gel(B,i));
  return F2xX_renormalize(b, lb);
}

GEN
ZXX_to_F2xX(GEN B, long v)
{
  long lb=lg(B);
  long i;
  GEN b=cgetg(lb,t_POL);
  b[1]=evalsigne(1)|(((ulong)B[1])&VARNBITS);
  for (i=2; i<lb; i++)
    switch (typ(gel(B,i)))
    {
    case t_INT:
      gel(b,i) = Z_to_F2x(gel(B,i), v);
      break;
    case t_POL:
      gel(b,i) = ZX_to_F2x(gel(B,i));
      break;
    }
  return F2xX_renormalize(b, lb);
}

GEN
F2xX_to_ZXX(GEN B)
{
  long i, lb = lg(B);
  GEN b = cgetg(lb,t_POL);
  for (i=2; i<lb; i++)
  {
    GEN c = gel(B,i);
    gel(b,i) = lgpol(c) ?  F2x_equal1(c) ? gen_1 : F2x_to_ZX(c) : gen_0;
  }
  b[1] = B[1]; return b;
}

GEN
F2xX_deriv(GEN z)
{
  long i,l = lg(z)-1;
  GEN x;
  if (l < 2) l = 2;
  x = cgetg(l, t_POL); x[1] = z[1];
  for (i=2; i<l; i++) gel(x,i) = odd(i) ? pol0_F2x(mael(z,i+1,1)): gel(z,i+1);
  return F2xX_renormalize(x,l);
}

static GEN
F2xX_addspec(GEN x, GEN y, long lx, long ly)
{
  long i,lz;
  GEN z;
  if (ly>lx) swapspec(x,y, lx,ly);
  lz = lx+2; z = cgetg(lz, t_POL);
  for (i=0; i<ly; i++) gel(z,i+2) = F2x_add(gel(x,i), gel(y,i));
  for (   ; i<lx; i++) gel(z,i+2) = F2x_copy(gel(x,i));
  return F2xX_renormalize(z, lz);
}

GEN
F2xX_add(GEN x, GEN y)
{
  long i,lz;
  GEN z;
  long lx=lg(x);
  long ly=lg(y);
  if (ly>lx) swapspec(x,y, lx,ly);
  lz = lx; z = cgetg(lz, t_POL); z[1]=x[1];
  for (i=2; i<ly; i++) gel(z,i) = F2x_add(gel(x,i), gel(y,i));
  for (   ; i<lx; i++) gel(z,i) = F2x_copy(gel(x,i));
  return F2xX_renormalize(z, lz);
}

GEN
F2xX_F2x_add(GEN x, GEN y)
{
  long i, lz = lg(y);
  GEN z;
  if (signe(y) == 0) return scalarpol(x, varn(y));
  z = cgetg(lz,t_POL); z[1] = y[1];
  gel(z,2) = F2x_add(gel(y,2), x);
  if (lz == 3) z = F2xX_renormalize(z,lz);
  else
    for(i=3;i<lz;i++) gel(z,i) = F2x_copy(gel(y,i));
  return z;
}

GEN
F2xX_F2x_mul(GEN P, GEN U)
{
  long i, lP = lg(P);
  GEN res = cgetg(lP,t_POL);
  res[1] = P[1];
  for(i=2; i<lP; i++)
    gel(res,i) = F2x_mul(U,gel(P,i));
  return F2xX_renormalize(res, lP);
}

GEN
F2xY_F2xqV_evalx(GEN P, GEN x, GEN T)
{
  long i, lP = lg(P);
  GEN res = cgetg(lP,t_POL);
  res[1] = P[1];
  for(i=2; i<lP; i++)
    gel(res,i) = F2x_F2xqV_eval(gel(P,i), x, T);
  return F2xX_renormalize(res, lP);
}

GEN
F2xY_F2xq_evalx(GEN P, GEN x, GEN T)
{
  pari_sp av = avma;
  long n = brent_kung_optpow(F2x_degree(T)-1,lgpol(P),1);
  GEN xp = F2xq_powers(x, n, T);
  return gerepileupto(av, F2xY_F2xqV_evalx(P, xp, T));
}

static GEN
F2xX_to_Kronecker_spec(GEN P, long n, long d)
{
  long i, k, l, N = 2*d + 1;
  long dP = n+1;
  GEN x;
  if (n == 0) return pol0_Flx(P[1]&VARNBITS);
  l = nbits2nlong(N*dP+d+1);
  x = zero_zv(l+1);
  for (k=i=0; i<n; i++, k+=N)
  {
    GEN c = gel(P,i);
    F2x_addshiftip(x, c, k);
  }
  x[1] = P[1]&VARNBITS; return F2x_renormalize(x, l+2);
}

GEN
F2xX_to_Kronecker(GEN P, long d)
{
  long i, k, l, N = 2*d + 1;
  long dP = degpol(P);
  GEN x;
  if (dP < 0) return pol0_Flx(P[1]&VARNBITS);
  l = nbits2nlong(N*dP+d+1);
  x = zero_zv(l+1);
  for (k=i=0; i<=dP; i++, k+=N)
  {
    GEN c = gel(P,i+2);
    F2x_addshiftip(x, c, k);
  }
  x[1] = P[1]&VARNBITS; return F2x_renormalize(x, l+2);
}

static GEN
F2x_slice(GEN x, long n, long d)
{
  ulong ib, il=dvmduBIL(n, &ib);
  ulong db, dl=dvmduBIL(d, &db);
  long lN = dl+2+(db?1:0);
  GEN t = cgetg(lN,t_VECSMALL);
  t[1] = x[1];
  if (ib)
  {
    ulong i, ic = BITS_IN_LONG-ib;
    ulong r = uel(x,2+il)>>ib;
    for(i=0; i<dl; i++)
    {
      uel(t,2+i) = (uel(x,3+il+i)<<ic)|r;
      r = uel(x,3+il+i)>>ib;
    }
    if (db)
      uel(t,2+i) = (uel(x,3+il+i)<<ic)|r;
  }
  else
  {
    long i;
    for(i=2; i<lN; i++)
      uel(t,i) = uel(x,il+i);
  }
  if (db) uel(t,lN-1) &= (1UL<<db)-1;
  return F2x_renormalize(t, lN);
}

GEN
Kronecker_to_F2xqX(GEN z, GEN T)
{
  long lz = F2x_degree(z)+1;
  long i, j, N = F2x_degree(T)*2 + 1;
  long lx = lz / (N-2);
  GEN x = cgetg(lx+3,t_POL);
  x[1] = z[1];
  for (i=0, j=2; i<lz; i+=N, j++)
  {
    GEN t = F2x_slice(z,i,minss(lz-i,N));
    t[1] = T[1];
    gel(x,j) = F2x_rem(t, T);
  }
  return F2xX_renormalize(x, j);
}

/***********************************************************************/
/**                                                                   **/
/**                             F2xXV/F2xXC                           **/
/**                                                                   **/
/***********************************************************************/

GEN
FlxXC_to_F2xXC(GEN x)
{ pari_APPLY_type(t_COL, FlxX_to_F2xX(gel(x,i))); }

GEN
F2xXC_to_ZXXC(GEN x)
{ pari_APPLY_type(t_COL, F2xX_to_ZXX(gel(x,i))); }

/***********************************************************************/
/**                                                                   **/
/**                             F2xqX                                 **/
/**                                                                   **/
/***********************************************************************/

static GEN
get_F2xqX_red(GEN T, GEN *B)
{
  if (typ(T)!=t_VEC) { *B=NULL; return T; }
  *B = gel(T,1); return gel(T,2);
}

GEN
random_F2xqX(long d1, long v, GEN T)
{
  long dT = F2x_degree(T), vT = T[1];
  long i, d = d1+2;
  GEN y = cgetg(d,t_POL); y[1] = evalsigne(1) | evalvarn(v);
  for (i=2; i<d; i++) gel(y,i) = random_F2x(dT, vT);
  return FlxX_renormalize(y,d);
}

GEN
F2xqX_red(GEN z, GEN T)
{
  GEN res;
  long i, l = lg(z);
  res = cgetg(l,t_POL); res[1] = z[1];
  for(i=2;i<l;i++) gel(res,i) = F2x_rem(gel(z,i),T);
  return F2xX_renormalize(res,l);
}

GEN
F2xqX_F2xq_mul(GEN P, GEN U, GEN T)
{
  long i, lP = lg(P);
  GEN res = cgetg(lP,t_POL);
  res[1] = P[1];
  for(i=2; i<lP; i++)
    gel(res,i) = F2xq_mul(U,gel(P,i), T);
  return F2xX_renormalize(res, lP);
}

GEN
F2xqX_F2xq_mul_to_monic(GEN P, GEN U, GEN T)
{
  long i, lP = lg(P);
  GEN res = cgetg(lP,t_POL);
  res[1] = P[1];
  for(i=2; i<lP-1; i++) gel(res,i) = F2xq_mul(U,gel(P,i), T);
  gel(res,lP-1) = pol1_F2x(T[1]);
  return F2xX_renormalize(res, lP);
}

GEN
F2xqX_normalize(GEN z, GEN T)
{
  GEN p1 = leading_coeff(z);
  if (!lgpol(z) || (!degpol(p1) && p1[1] == 1)) return z;
  return F2xqX_F2xq_mul_to_monic(z, F2xq_inv(p1,T), T);
}

GEN
F2xqX_mul(GEN x, GEN y, GEN T)
{
  pari_sp ltop=avma;
  GEN z,kx,ky;
  kx= F2xX_to_Kronecker(x, F2x_degree(T));
  ky= F2xX_to_Kronecker(y, F2x_degree(T));
  z = F2x_mul(ky, kx);
  z = Kronecker_to_F2xqX(z,T);
  return gerepileupto(ltop,z);
}

static GEN
F2xqX_mulspec(GEN x, GEN y, GEN T, long nx, long ny)
{
  pari_sp ltop=avma;
  GEN z,kx,ky;
  kx= F2xX_to_Kronecker_spec(x, nx, F2x_degree(T));
  ky= F2xX_to_Kronecker_spec(y, ny, F2x_degree(T));
  z = F2x_mul(ky, kx);
  z = Kronecker_to_F2xqX(z,T);
  return gerepileupto(ltop,z);
}

GEN
F2xqX_sqr(GEN x, GEN T)
{
  long d = degpol(x), l = 2*d+3;
  GEN z;
  if (!signe(x)) return pol_0(varn(x));
  z = cgetg(l,t_POL);
  z[1] = x[1];
  if (d > 0)
  {
    GEN u = pol0_F2x(T[1]);
    long i,j;
    for (i=2,j=2; i<d+2; i++,j+=2)
    {
      gel(z, j) = F2xq_sqr(gel(x, i), T);
      gel(z, j+1) = u;
    }
  }
  gel(z, 2+2*d) = F2xq_sqr(gel(x, 2+d), T);
  return FlxX_renormalize(z, l);
}

static GEN
F2xqX_divrem_basecase(GEN x, GEN y, GEN T, GEN *pr)
{
  long vx, dx, dy, dz, i, j, sx, lr;
  pari_sp av0, av, tetpil;
  GEN z,p1,rem,lead;

  if (!signe(y)) pari_err_INV("F2xqX_divrem",y);
  vx=varn(x); dy=degpol(y); dx=degpol(x);
  if (dx < dy)
  {
    if (pr)
    {
      av0 = avma; x = F2xqX_red(x, T);
      if (pr == ONLY_DIVIDES) { avma=av0; return signe(x)? NULL: pol_0(vx); }
      if (pr == ONLY_REM) return x;
      *pr = x;
    }
    return pol_0(vx);
  }
  lead = leading_term(y);
  if (!dy) /* y is constant */
  {
    if (pr && pr != ONLY_DIVIDES)
    {
      if (pr == ONLY_REM) return pol_0(vx);
      *pr = pol_0(vx);
    }
    if (F2x_equal1(lead)) return gcopy(x);
    av0 = avma; x = F2xqX_F2xq_mul(x,F2xq_inv(lead,T),T);
    return gerepileupto(av0,x);
  }
  av0 = avma; dz = dx-dy;
  lead = F2x_equal1(lead)? NULL: gclone(F2xq_inv(lead,T));
  avma = av0;
  z = cgetg(dz+3,t_POL); z[1] = x[1];
  x += 2; y += 2; z += 2;

  p1 = gel(x,dx); av = avma;
  gel(z,dz) = lead? gerepileupto(av, F2xq_mul(p1,lead, T)): leafcopy(p1);
  for (i=dx-1; i>=dy; i--)
  {
    av=avma; p1=gel(x,i);
    for (j=i-dy+1; j<=i && j<=dz; j++)
      p1 = F2x_add(p1, F2x_mul(gel(z,j),gel(y,i-j)));
    if (lead) p1 = F2x_mul(p1, lead);
    tetpil=avma; gel(z,i-dy) = gerepile(av,tetpil,F2x_rem(p1,T));
  }
  if (!pr) { if (lead) gunclone(lead); return z-2; }

  rem = (GEN)avma; av = (pari_sp)new_chunk(dx+3);
  for (sx=0; ; i--)
  {
    p1 = gel(x,i);
    for (j=0; j<=i && j<=dz; j++)
      p1 = F2x_add(p1, F2x_mul(gel(z,j),gel(y,i-j)));
    tetpil=avma; p1 = F2x_rem(p1, T); if (lgpol(p1)) { sx = 1; break; }
    if (!i) break;
    avma=av;
  }
  if (pr == ONLY_DIVIDES)
  {
    if (lead) gunclone(lead);
    if (sx) { avma=av0; return NULL; }
    avma = (pari_sp)rem; return z-2;
  }
  lr=i+3; rem -= lr;
  rem[0] = evaltyp(t_POL) | evallg(lr);
  rem[1] = z[-1];
  p1 = gerepile((pari_sp)rem,tetpil,p1);
  rem += 2; gel(rem,i) = p1;
  for (i--; i>=0; i--)
  {
    av=avma; p1 = gel(x,i);
    for (j=0; j<=i && j<=dz; j++)
      p1 = F2x_add(p1, F2x_mul(gel(z,j),gel(y,i-j)));
    tetpil=avma; gel(rem,i) = gerepile(av,tetpil, F2x_rem(p1, T));
  }
  rem -= 2;
  if (lead) gunclone(lead);
  if (!sx) (void)F2xX_renormalize(rem, lr);
  if (pr == ONLY_REM) return gerepileupto(av0,rem);
  *pr = rem; return z-2;
}

static GEN
F2xX_recipspec(GEN x, long l, long n, long vs)
{
  long i;
  GEN z = cgetg(n+2,t_POL);
  z[1] = 0; z += 2;
  for(i=0; i<l; i++)
    gel(z,n-i-1) = F2x_copy(gel(x,i));
  for(   ; i<n; i++)
    gel(z,n-i-1) = pol0_F2x(vs);
  return F2xX_renormalize(z-2,n+2);
}

static GEN
F2xqX_invBarrett_basecase(GEN T, GEN Q)
{
  long i, l=lg(T)-1, lr = l-1, k;
  long sv=Q[1];
  GEN r=cgetg(lr,t_POL); r[1]=T[1];
  gel(r,2) = pol1_F2x(sv);
  for (i=3;i<lr;i++)
  {
    pari_sp ltop=avma;
    GEN u = gel(T,l-i+2);
    for (k=3;k<i;k++)
      u = F2x_add(u, F2xq_mul(gel(T,l-i+k),gel(r,k),Q));
    gel(r,i) = gerepileupto(ltop, u);
  }
  r = F2xX_renormalize(r,lr);
  return r;
}

/* Return new lgpol */
static long
F2xX_lgrenormalizespec(GEN x, long lx)
{
  long i;
  for (i = lx-1; i>=0; i--)
    if (lgpol(gel(x,i))) break;
  return i+1;
}

static GEN
F2xqX_invBarrett_Newton(GEN S, GEN T)
{
  pari_sp av = avma;
  long nold, lx, lz, lq, l = degpol(S), i, lQ;
  GEN q, y, z, x = cgetg(l+2, t_POL) + 2;
  long dT = F2x_degree(T);
  ulong mask = quadratic_prec_mask(l-2); /* assume l > 2 */
  for (i=0;i<l;i++) gel(x,i) = pol0_F2x(T[1]);
  q = F2xX_recipspec(S+2,l+1,l+1,dT);
  lQ = lgpol(q); q+=2;
  /* We work on _spec_ FlxX's, all the l[xzq] below are lgpol's */

  /* initialize */
  gel(x,0) = F2xq_inv(gel(q,0),T);
  if (lQ>1 && F2x_degree(gel(q,1)) >= dT)
    gel(q,1) = F2x_rem(gel(q,1), T);
  if (lQ>1 && lgpol(gel(q,1)))
  {
    GEN u = gel(q, 1);
    if (!F2x_equal1(gel(x,0))) u = F2xq_mul(u, F2xq_sqr(gel(x,0), T), T);
    else u = F2x_copy(u);
    gel(x,1) = u; lx = 2;
  }
  else
    lx = 1;
  nold = 1;
  for (; mask > 1; )
  { /* set x -= x(x*q - 1) + O(t^(nnew + 1)), knowing x*q = 1 + O(t^(nold+1)) */
    long i, lnew, nnew = nold << 1;

    if (mask & 1) nnew--;
    mask >>= 1;

    lnew = nnew + 1;
    lq = F2xX_lgrenormalizespec(q, minss(lQ,lnew));
    z = F2xqX_mulspec(x, q, T, lx, lq); /* FIXME: high product */
    lz = lgpol(z); if (lz > lnew) lz = lnew;
    z += 2;
    /* subtract 1 [=>first nold words are 0]: renormalize so that z(0) != 0 */
    for (i = nold; i < lz; i++) if (lgpol(gel(z,i))) break;
    nold = nnew;
    if (i >= lz) continue; /* z-1 = 0(t^(nnew + 1)) */

    /* z + i represents (x*q - 1) / t^i */
    lz = F2xX_lgrenormalizespec (z+i, lz-i);
    z = F2xqX_mulspec(x, z+i, T, lx, lz); /* FIXME: low product */
    lz = lgpol(z); z += 2;
    if (lz > lnew-i) lz = F2xX_lgrenormalizespec(z, lnew-i);

    lx = lz+ i;
    y  = x + i; /* x -= z * t^i, in place */
    for (i = 0; i < lz; i++) gel(y,i) = gel(z,i);
  }
  x -= 2; setlg(x, lx + 2); x[1] = S[1];
  return gerepilecopy(av, x);
}

/* x/polrecip(P)+O(x^n) */
GEN
F2xqX_invBarrett(GEN T, GEN Q)
{
  pari_sp ltop=avma;
  long l=lg(T), v = varn(T);
  GEN r;
  GEN c = gel(T,l-1);
  if (l<5) return pol_0(v);
  if (l<=F2xqX_INVBARRETT_LIMIT)
  {
    if (!F2x_equal1(c))
    {
      GEN ci = F2xq_inv(c,Q);
      T = F2xqX_F2xq_mul(T, ci, Q);
      r = F2xqX_invBarrett_basecase(T,Q);
      r = F2xqX_F2xq_mul(r,ci,Q);
    } else
      r = F2xqX_invBarrett_basecase(T,Q);
  } else
    r = F2xqX_invBarrett_Newton(T,Q);
  return gerepileupto(ltop, r);
}

GEN
F2xqX_get_red(GEN S, GEN T)
{
  if (typ(S)==t_POL && lg(S)>F2xqX_BARRETT_LIMIT)
    retmkvec2(F2xqX_invBarrett(S, T), S);
  return S;
}

/* Compute x mod S where 2 <= degpol(S) <= l+1 <= 2*(degpol(S)-1)
 *  * and mg is the Barrett inverse of S. */
static GEN
F2xqX_divrem_Barrettspec(GEN x, long l, GEN mg, GEN S, GEN T, GEN *pr)
{
  GEN q, r;
  long lt = degpol(S); /*We discard the leading term*/
  long ld, lm, lT, lmg;
  ld = l-lt;
  lm = minss(ld, lgpol(mg));
  lT  = F2xX_lgrenormalizespec(S+2,lt);
  lmg = F2xX_lgrenormalizespec(mg+2,lm);
  q = F2xX_recipspec(x+lt,ld,ld,0);               /* q = rec(x)     lq<=ld*/
  q = F2xqX_mulspec(q+2,mg+2,T,lgpol(q),lmg);   /* q = rec(x) * mg lq<=ld+lm*/
  q = F2xX_recipspec(q+2,minss(ld,lgpol(q)),ld,0);/* q = rec (rec(x) * mg) lq<=ld*/
  if (!pr) return q;
  r = F2xqX_mulspec(q+2,S+2,T,lgpol(q),lT);     /* r = q*pol        lr<=ld+lt*/
  r = F2xX_addspec(x,r+2,lt,minss(lt,lgpol(r)));/* r = x - r   lr<=lt */
  if (pr == ONLY_REM) return r;
  *pr = r; return q;
}

static GEN
F2xqX_divrem_Barrett_noGC(GEN x, GEN mg, GEN S, GEN T, GEN *pr)
{
  long l = lgpol(x), lt = degpol(S), lm = 2*lt-1;
  GEN q = NULL, r;
  long i;
  if (l <= lt)
  {
    if (pr == ONLY_REM) return RgX_copy(x);
    if (pr == ONLY_DIVIDES) return signe(x)? NULL: pol_0(varn(x));
    if (pr) *pr =  RgX_copy(x);
    return pol_0(varn(x));
  }
  if (lt <= 1)
    return F2xqX_divrem_basecase(x,S,T,pr);
  if (pr != ONLY_REM && l>lm)
  {
    long vT = get_F2x_var(T);
    q = cgetg(l-lt+2, t_POL);
    for (i=0;i<l-lt;i++) gel(q+2,i) = pol0_F2x(vT);
  }
  r = l>lm ? shallowcopy(x): x;
  while (l>lm)
  {
    GEN zr, zq = F2xqX_divrem_Barrettspec(r+2+l-lm,lm,mg,S,T,&zr);
    long lz = lgpol(zr);
    if (pr != ONLY_REM)
    {
      long lq = lgpol(zq);
      for(i=0; i<lq; i++) gel(q+2+l-lm,i) = gel(zq,2+i);
    }
    for(i=0; i<lz; i++) gel(r+2+l-lm,i) = gel(zr,2+i);
    l = l-lm+lz;
  }
  if (pr != ONLY_REM)
  {
    if (l > lt)
    {
      GEN zq = F2xqX_divrem_Barrettspec(r+2,l,mg,S,T,&r);
      if (!q) q = zq;
      else
      {
        long lq = lgpol(zq);
        for(i=0; i<lq; i++) gel(q+2,i) = gel(zq,2+i);
      }
    }
    else
    { setlg(r, l+2); r = RgX_copy(r); }
  }
  else
  {
    if (l > lt)
      (void) F2xqX_divrem_Barrettspec(r+2,l,mg,S,T,&r);
    else
    { setlg(r, l+2); r = RgX_copy(r); }
    r[1] = x[1]; return F2xX_renormalize(r, lg(r));
  }
  if (pr) { r[1] = x[1]; r = F2xX_renormalize(r, lg(r)); }
  q[1] = x[1]; q = F2xX_renormalize(q, lg(q));
  if (pr == ONLY_DIVIDES) return signe(r)? NULL: q;
  if (pr) *pr = r;
  return q;
}

GEN
F2xqX_divrem(GEN x, GEN S, GEN T, GEN *pr)
{
  GEN B, y = get_F2xqX_red(S, &B);
  long dy = degpol(y), dx = degpol(x), d = dx-dy;
  if (pr==ONLY_REM) return F2xqX_rem(x, y, T);
  if (!B && d+3 < F2xqX_DIVREM_BARRETT_LIMIT)
    return F2xqX_divrem_basecase(x,y,T,pr);
  else
  {
    pari_sp av=avma;
    GEN mg = B? B: F2xqX_invBarrett(y, T);
    GEN q = F2xqX_divrem_Barrett_noGC(x,mg,y,T,pr);
    if (!q) {avma=av; return NULL;}
    if (!pr || pr==ONLY_DIVIDES) return gerepilecopy(av, q);
    gerepileall(av,2,&q,pr);
    return q;
  }
}

GEN
F2xqX_rem(GEN x, GEN S, GEN T)
{
  GEN B, y = get_F2xqX_red(S, &B);
  long dy = degpol(y), dx = degpol(x), d = dx-dy;
  if (d < 0) return F2xqX_red(x, T);
  if (!B && d+3 < F2xqX_REM_BARRETT_LIMIT)
    return F2xqX_divrem_basecase(x,y, T, ONLY_REM);
  else
  {
    pari_sp av=avma;
    GEN mg = B? B: F2xqX_invBarrett(y, T);
    GEN r = F2xqX_divrem_Barrett_noGC(x, mg, y, T, ONLY_REM);
    return gerepileupto(av, r);
  }
}

GEN
F2xqX_gcd(GEN a, GEN b, GEN T)
{
  pari_sp av = avma, av0=avma;
  while (signe(b))
  {
    GEN c;
    if (gc_needed(av0,2))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"F2xqX_gcd (d = %ld)",degpol(b));
      gerepileall(av0,2, &a,&b);
    }
    av = avma; c = F2xqX_rem(a, b, T); a=b; b=c;
  }
  avma = av; return a;
}

GEN
F2xqX_extgcd(GEN a, GEN b, GEN T,  GEN *ptu, GEN *ptv)
{
  pari_sp av=avma;
  GEN u,v,d,d1,v1;
  long vx = varn(a);
  d = a; d1 = b;
  v = pol_0(vx); v1 = pol1_F2xX(vx, get_F2x_var(T));
  while (signe(d1))
  {
    GEN r, q = F2xqX_divrem(d, d1, T, &r);
    v = F2xX_add(v,F2xqX_mul(q,v1,T));
    u=v; v=v1; v1=u;
    u=r; d=d1; d1=u;
    if (gc_needed(av,2))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"F2xqX_extgcd (d = %ld)",degpol(d));
      gerepileall(av,5, &d,&d1,&u,&v,&v1);
    }
  }
  if (ptu) *ptu = F2xqX_div(F2xX_add(d,F2xqX_mul(b,v, T)), a, T);
  *ptv = v; return d;
}

static GEN
_F2xqX_mul(void *data,GEN a,GEN b)
{ return F2xqX_mul(a,b, (GEN) data); }

static GEN
_F2xqX_sqr(void *data,GEN a)
{ return F2xqX_sqr(a, (GEN) data); }

GEN
F2xqX_powu(GEN x, ulong n, GEN T)
{
  return gen_powu(x, n, (void*)T, &_F2xqX_sqr, &_F2xqX_mul);
}

/***********************************************************************/
/**                                                                   **/
/**                             F2xqXQ                                **/
/**                                                                   **/
/***********************************************************************/

GEN
F2xqXQ_mul(GEN x, GEN y, GEN S, GEN T) {
  return F2xqX_rem(F2xqX_mul(x,y,T),S,T);
}

GEN
F2xqXQ_sqr(GEN x, GEN S, GEN T) {
  return F2xqX_rem(F2xqX_sqr(x,T),S,T);
}

GEN
F2xqXQ_invsafe(GEN x, GEN S, GEN T)
{
  GEN V, z = F2xqX_extgcd(get_F2xqX_mod(S), x, T, NULL, &V);
  if (degpol(z)) return NULL;
  z = F2xq_invsafe(gel(z,2),T);
  if (!z) return NULL;
  return F2xqX_F2xq_mul(V, z, T);
}

GEN
F2xqXQ_inv(GEN x, GEN S, GEN T)
{
  pari_sp av = avma;
  GEN U = F2xqXQ_invsafe(x, S, T);
  if (!U) pari_err_INV("F2xqXQ_inv",x);
  return gerepileupto(av, U);
}

struct _F2xqXQ {
  GEN T, S;
};

static GEN
_F2xqXQ_add(void *data, GEN x, GEN y) {
  (void) data;
  return F2xX_add(x,y);
}
static GEN
_F2xqXQ_cmul(void *data, GEN P, long a, GEN x) {
  (void) data;
  return F2xX_F2x_mul(x,gel(P,a+2));
}
static GEN
_F2xqXQ_red(void *data, GEN x) {
  struct _F2xqXQ *d = (struct _F2xqXQ*) data;
  return F2xqX_red(x, d->T);
}
static GEN
_F2xqXQ_mul(void *data, GEN x, GEN y) {
  struct _F2xqXQ *d = (struct _F2xqXQ*) data;
  return F2xqXQ_mul(x,y, d->S,d->T);
}
static GEN
_F2xqXQ_sqr(void *data, GEN x) {
  struct _F2xqXQ *d = (struct _F2xqXQ*) data;
  return F2xqXQ_sqr(x, d->S,d->T);
}
static GEN
_F2xqXQ_zero(void *data) {
  struct _F2xqXQ *d = (struct _F2xqXQ*) data;
  return pol_0(get_F2xqX_var(d->S));
}
static GEN
_F2xqXQ_one(void *data) {
  struct _F2xqXQ *d = (struct _F2xqXQ*) data;
  return pol1_F2xX(get_F2xqX_var(d->S),get_F2x_var(d->T));
}

static struct bb_algebra F2xqXQ_algebra = { _F2xqXQ_red,
 _F2xqXQ_add, _F2xqXQ_add, _F2xqXQ_mul,_F2xqXQ_sqr,_F2xqXQ_one,_F2xqXQ_zero };

GEN
F2xqXQ_pow(GEN x, GEN n, GEN S, GEN T)
{
  struct _F2xqXQ D;
  long s = signe(n);
  if (!s) return pol1_F2xX(get_F2xqX_var(S), get_F2x_var(T));
  if (s < 0) x = F2xqXQ_inv(x,S,T);
  if (is_pm1(n)) return s < 0 ? x : gcopy(x);
  if (degpol(x) >= get_F2xqX_degree(S)) x = F2xqX_rem(x,S,T);
  D.S = S; D.T = T;
  return gen_pow(x, n, (void*)&D, &_F2xqXQ_sqr, &_F2xqXQ_mul);
}

GEN
F2xqXQ_powers(GEN x, long l, GEN S, GEN T)
{
  struct _F2xqXQ D;
  int use_sqr = 2*degpol(x) >= get_F2xqX_degree(S);
  D.S = S; D.T = T;
  return gen_powers(x, l, use_sqr, (void*)&D, &_F2xqXQ_sqr, &_F2xqXQ_mul,&_F2xqXQ_one);
}

GEN
F2xqX_F2xqXQV_eval(GEN P, GEN V, GEN S, GEN T)
{
  struct _F2xqXQ D;
  D.S = S; D.T = T;
  return gen_bkeval_powers(P, degpol(P), V, (void*)&D, &F2xqXQ_algebra,
                                                   _F2xqXQ_cmul);
}

GEN
F2xqX_F2xqXQ_eval(GEN Q, GEN x, GEN S, GEN T)
{
  struct _F2xqXQ D;
  int use_sqr = 2*degpol(x) >= get_F2xqX_degree(S);
  D.S = S; D.T = T;
  return gen_bkeval(Q, degpol(Q), x, use_sqr, (void*)&D, &F2xqXQ_algebra,
                                                    _F2xqXQ_cmul);
}

static GEN
F2xqXQ_autpow_sqr(void * E, GEN x)
{
  struct _F2xqXQ *D = (struct _F2xqXQ *)E;
  GEN T = D->T;
  GEN phi = gel(x,1), S = gel(x,2);
  long n = brent_kung_optpow(F2x_degree(T)-1,lgpol(S)+1,1);
  GEN V = F2xq_powers(phi, n, T);
  GEN phi2 = F2x_F2xqV_eval(phi, V, T);
  GEN Sphi = F2xY_F2xqV_evalx(S, V, T);
  GEN S2 = F2xqX_F2xqXQ_eval(Sphi, S, D->S, T);
  return mkvec2(phi2, S2);
}

static GEN
F2xqXQ_autpow_mul(void * E, GEN x, GEN y)
{
  struct _F2xqXQ *D = (struct _F2xqXQ *)E;
  GEN T = D->T;
  GEN phi1 = gel(x,1), S1 = gel(x,2);
  GEN phi2 = gel(y,1), S2 = gel(y,2);
  long n = brent_kung_optpow(F2x_degree(T)-1,lgpol(S1)+1,1);
  GEN V = F2xq_powers(phi2, n, T);
  GEN phi3 = F2x_F2xqV_eval(phi1,V,T);
  GEN Sphi = F2xY_F2xqV_evalx(S1,V,T);
  GEN S3 = F2xqX_F2xqXQ_eval(Sphi, S2, D->S, T);
  return mkvec2(phi3, S3);
}

GEN
F2xqXQ_autpow(GEN aut, long n, GEN S, GEN T)
{
  struct _F2xqXQ D;
  D.S = S; D.T = T;
  return gen_powu(aut,n,&D,F2xqXQ_autpow_sqr,F2xqXQ_autpow_mul);
}

static GEN
F2xqXQ_auttrace_mul(void *E, GEN x, GEN y)
{
  struct _F2xqXQ *D = (struct _F2xqXQ *) E;
  GEN T = D->T;
  GEN phi1 = gel(x,1), S1 = gel(x,2), a1 = gel(x,3);
  GEN phi2 = gel(y,1), S2 = gel(y,2), a2 = gel(y,3);
  long n2 = brent_kung_optpow(F2x_degree(T)-1, lgpol(S1)+lgpol(a1)+1, 1);
  GEN V2 = F2xq_powers(phi2, n2, T);
  GEN phi3 = F2x_F2xqV_eval(phi1, V2, T);
  GEN Sphi = F2xY_F2xqV_evalx(S1, V2, T);
  GEN aphi = F2xY_F2xqV_evalx(a1, V2, T);
  long n = brent_kung_optpow(maxss(degpol(Sphi),degpol(aphi)),2,1);
  GEN V = F2xqXQ_powers(S2, n, D->S, T);
  GEN S3 = F2xqX_F2xqXQV_eval(Sphi, V, D->S, T);
  GEN aS = F2xqX_F2xqXQV_eval(aphi, V, D->S, T);
  GEN a3 = F2xX_add(aS, a2);
  return mkvec3(phi3, S3, a3);
}

static GEN
F2xqXQ_auttrace_sqr(void *E, GEN x)
{ return F2xqXQ_auttrace_mul(E, x, x); }

GEN
F2xqXQ_auttrace(GEN aut, long n, GEN S, GEN T)
{
  struct _F2xqXQ D;
  D.S = S; D.T = T;
  return gen_powu(aut,n,&D,F2xqXQ_auttrace_sqr,F2xqXQ_auttrace_mul);
}

GEN
F2xqXQV_red(GEN x, GEN S, GEN T)
{ pari_APPLY_type(t_VEC, F2xqX_rem(gel(x,i), S, T)) }
