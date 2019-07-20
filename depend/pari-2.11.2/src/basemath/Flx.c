/* Copyright (C) 2004  The PARI group.

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

/* Not so fast arithmetic with polynomials with small coefficients. */

static GEN
get_Flx_red(GEN T, GEN *B)
{
  if (typ(T)!=t_VEC) { *B=NULL; return T; }
  *B = gel(T,1); return gel(T,2);
}

/***********************************************************************/
/**                                                                   **/
/**               Flx                                                 **/
/**                                                                   **/
/***********************************************************************/
/* Flx objects are defined as follows:
   Let l an ulong. An Flx is a t_VECSMALL:
   x[0] = codeword
   x[1] = evalvarn(variable number)  (signe is not stored).
   x[2] = a_0 x[3] = a_1, etc.
   With 0 <= a_i < l

   signe(x) is not valid. Use degpol(x)>=0 instead.
*/
/***********************************************************************/
/**                                                                   **/
/**          Conversion from Flx                                      **/
/**                                                                   **/
/***********************************************************************/

GEN
Flx_to_ZX(GEN z)
{
  long i, l = lg(z);
  GEN x = cgetg(l,t_POL);
  for (i=2; i<l; i++) gel(x,i) = utoi(z[i]);
  x[1] = evalsigne(l-2!=0)| z[1]; return x;
}

GEN
Flx_to_FlxX(GEN z, long sv)
{
  long i, l = lg(z);
  GEN x = cgetg(l,t_POL);
  for (i=2; i<l; i++) gel(x,i) = Fl_to_Flx(z[i], sv);
  x[1] = evalsigne(l-2!=0)| z[1]; return x;
}

GEN
Flv_to_ZV(GEN x)
{ pari_APPLY_type(t_VEC, utoi(x[i])) }

GEN
Flc_to_ZC(GEN x)
{ pari_APPLY_type(t_COL, utoi(x[i])) }

GEN
Flm_to_ZM(GEN x)
{ pari_APPLY_type(t_MAT, Flc_to_ZC(gel(x,i))) }

GEN
Flc_to_ZC_inplace(GEN z)
{
  long i, l = lg(z);
  for (i=1; i<l; i++) gel(z,i) = utoi(z[i]);
  settyp(z, t_COL);
  return z;
}

GEN
Flm_to_ZM_inplace(GEN z)
{
  long i, l = lg(z);
  for (i=1; i<l; i++) Flc_to_ZC_inplace(gel(z, i));
  return z;
}

/* same as Flx_to_ZX, in place */
GEN
Flx_to_ZX_inplace(GEN z)
{
  long i, l = lg(z);
  for (i=2; i<l; i++) gel(z,i) = utoi(z[i]);
  settyp(z, t_POL); z[1]=evalsigne(l-2!=0)|z[1]; return z;
}

/*Flx_to_Flv=zx_to_zv*/
GEN
Flx_to_Flv(GEN x, long N)
{
  long i, l;
  GEN z = cgetg(N+1,t_VECSMALL);
  if (typ(x) != t_VECSMALL) pari_err_TYPE("Flx_to_Flv",x);
  l = lg(x)-1; x++;
  for (i=1; i<l ; i++) z[i]=x[i];
  for (   ; i<=N; i++) z[i]=0;
  return z;
}

/*Flv_to_Flx=zv_to_zx*/
GEN
Flv_to_Flx(GEN x, long sv)
{
  long i, l=lg(x)+1;
  GEN z = cgetg(l,t_VECSMALL); z[1]=sv;
  x--;
  for (i=2; i<l ; i++) z[i]=x[i];
  return Flx_renormalize(z,l);
}

/*Flm_to_FlxV=zm_to_zxV*/
GEN
Flm_to_FlxV(GEN x, long sv)
{ pari_APPLY_type(t_VEC, Flv_to_Flx(gel(x,i), sv)) }

/*FlxC_to_ZXC=zxC_to_ZXC*/
GEN
FlxC_to_ZXC(GEN x)
{ pari_APPLY_type(t_COL, Flx_to_ZX(gel(x,i))) }

/*FlxC_to_ZXC=zxV_to_ZXV*/
GEN
FlxV_to_ZXV(GEN x)
{ pari_APPLY_type(t_VEC, Flx_to_ZX(gel(x,i))) }

/*FlxM_to_ZXM=zxM_to_ZXM*/
GEN
FlxM_to_ZXM(GEN x)
{ pari_APPLY_same(FlxC_to_ZXC(gel(x,i))) }

GEN
FlxM_Flx_add_shallow(GEN x, GEN y, ulong p)
{
  long l = lg(x), i, j;
  GEN z = cgetg(l,t_MAT);

  if (l==1) return z;
  if (l != lgcols(x)) pari_err_OP( "+", x, y);
  for (i=1; i<l; i++)
  {
    GEN zi = cgetg(l,t_COL), xi = gel(x,i);
    gel(z,i) = zi;
    for (j=1; j<l; j++) gel(zi,j) = gel(xi,j);
    gel(zi,i) = Flx_add(gel(zi,i), y, p);
  }
  return z;
}

/***********************************************************************/
/**                                                                   **/
/**          Conversion to Flx                                        **/
/**                                                                   **/
/***********************************************************************/
/* Take an integer and return a scalar polynomial mod p,  with evalvarn=vs */
GEN
Fl_to_Flx(ulong x, long sv)
{
  return x? mkvecsmall2(sv, x): pol0_Flx(sv);
}

/* a X^d */
GEN
monomial_Flx(ulong a, long d, long vs)
{
  GEN P;
  if (a==0) return pol0_Flx(vs);
  P = const_vecsmall(d+2, 0);
  P[1] = vs; P[d+2] = a;
  return P;
}

GEN
Z_to_Flx(GEN x, ulong p, long sv)
{
  long u = umodiu(x,p);
  return u? mkvecsmall2(sv, u): pol0_Flx(sv);
}

/* return x[0 .. dx] mod p as t_VECSMALL. Assume x a t_POL*/
GEN
ZX_to_Flx(GEN x, ulong p)
{
  long i, lx = lg(x);
  GEN a = cgetg(lx, t_VECSMALL);
  a[1]=((ulong)x[1])&VARNBITS;
  for (i=2; i<lx; i++) a[i] = umodiu(gel(x,i), p);
  return Flx_renormalize(a,lx);
}

/* return x[0 .. dx] mod p as t_VECSMALL. Assume x a t_POL*/
GEN
zx_to_Flx(GEN x, ulong p)
{
  long i, lx = lg(x);
  GEN a = cgetg(lx, t_VECSMALL);
  a[1] = x[1];
  for (i=2; i<lx; i++) uel(a,i) = umodsu(x[i], p);
  return Flx_renormalize(a,lx);
}

ulong
Rg_to_Fl(GEN x, ulong p)
{
  switch(typ(x))
  {
    case t_INT: return umodiu(x, p);
    case t_FRAC: {
      ulong z = umodiu(gel(x,1), p);
      if (!z) return 0;
      return Fl_div(z, umodiu(gel(x,2), p), p);
    }
    case t_PADIC: return padic_to_Fl(x, p);
    case t_INTMOD: {
      GEN q = gel(x,1), a = gel(x,2);
      if (absequaliu(q, p)) return itou(a);
      if (!dvdiu(q,p)) pari_err_MODULUS("Rg_to_Fl", q, utoi(p));
      return umodiu(a, p);
    }
    default: pari_err_TYPE("Rg_to_Fl",x);
      return 0; /* LCOV_EXCL_LINE */
  }
}

ulong
Rg_to_F2(GEN x)
{
  switch(typ(x))
  {
    case t_INT: return mpodd(x);
    case t_FRAC:
      if (!mpodd(gel(x,2))) (void)Fl_inv(0,2); /* error */
      return mpodd(gel(x,1));
    case t_PADIC:
      if (!absequaliu(gel(x,2),2)) pari_err_OP("",x, mkintmodu(1,2));
      if (valp(x) < 0) (void)Fl_inv(0,2);
      return valp(x) & 1;
    case t_INTMOD: {
      GEN q = gel(x,1), a = gel(x,2);
      if (mpodd(q)) pari_err_MODULUS("Rg_to_F2", q, gen_2);
      return mpodd(a);
    }
    default: pari_err_TYPE("Rg_to_F2",x);
      return 0; /* LCOV_EXCL_LINE */
  }
}

GEN
RgX_to_Flx(GEN x, ulong p)
{
  long i, lx = lg(x);
  GEN a = cgetg(lx, t_VECSMALL);
  a[1]=((ulong)x[1])&VARNBITS;
  for (i=2; i<lx; i++) a[i] = Rg_to_Fl(gel(x,i), p);
  return Flx_renormalize(a,lx);
}

/* If x is a POLMOD, assume modulus is a multiple of T. */
GEN
Rg_to_Flxq(GEN x, GEN T, ulong p)
{
  long ta, tx = typ(x), v = T[1];
  GEN a, b;
  if (is_const_t(tx))
  {
    if (tx == t_FFELT) return FF_to_Flxq(x);
    return Fl_to_Flx(Rg_to_Fl(x, p), v);
  }
  switch(tx)
  {
    case t_POLMOD:
      b = gel(x,1);
      a = gel(x,2); ta = typ(a);
      if (is_const_t(ta)) return Fl_to_Flx(Rg_to_Fl(a, p), v);
      b = RgX_to_Flx(b, p); if (b[1] != v) break;
      a = RgX_to_Flx(a, p); if (Flx_equal(b,T)) return a;
      if (lgpol(Flx_rem(b,T,p))==0) return Flx_rem(a, T, p);
      break;
    case t_POL:
      x = RgX_to_Flx(x,p);
      if (x[1] != v) break;
      return Flx_rem(x, T, p);
    case t_RFRAC:
      a = Rg_to_Flxq(gel(x,1), T,p);
      b = Rg_to_Flxq(gel(x,2), T,p);
      return Flxq_div(a,b, T,p);
  }
  pari_err_TYPE("Rg_to_Flxq",x);
  return NULL; /* LCOV_EXCL_LINE */
}

/***********************************************************************/
/**                                                                   **/
/**          Basic operation on Flx                                   **/
/**                                                                   **/
/***********************************************************************/
/* = zx_renormalize. Similar to normalizepol, in place */
GEN
Flx_renormalize(GEN /*in place*/ x, long lx)
{
  long i;
  for (i = lx-1; i>1; i--)
    if (x[i]) break;
  stackdummy((pari_sp)(x + lg(x)), (pari_sp)(x + i+1));
  setlg(x, i+1); return x;
}

GEN
Flx_red(GEN z, ulong p)
{
  long i, l = lg(z);
  GEN x = cgetg(l, t_VECSMALL);
  x[1] = z[1];
  for (i=2; i<l; i++) x[i] = uel(z,i)%p;
  return Flx_renormalize(x,l);
}

GEN
random_Flx(long d1, long vs, ulong p)
{
  long i, d = d1+2;
  GEN y = cgetg(d,t_VECSMALL); y[1] = vs;
  for (i=2; i<d; i++) y[i] = random_Fl(p);
  return Flx_renormalize(y,d);
}

static GEN
Flx_addspec(GEN x, GEN y, ulong p, long lx, long ly)
{
  long i,lz;
  GEN z;

  if (ly>lx) swapspec(x,y, lx,ly);
  lz = lx+2; z = cgetg(lz, t_VECSMALL) + 2;
  for (i=0; i<ly; i++) z[i] = Fl_add(x[i], y[i], p);
  for (   ; i<lx; i++) z[i] = x[i];
  z -= 2; return Flx_renormalize(z, lz);
}

GEN
Flx_add(GEN x, GEN y, ulong p)
{
  long i,lz;
  GEN z;
  long lx=lg(x);
  long ly=lg(y);
  if (ly>lx) swapspec(x,y, lx,ly);
  lz = lx; z = cgetg(lz, t_VECSMALL); z[1]=x[1];
  for (i=2; i<ly; i++) z[i] = Fl_add(x[i], y[i], p);
  for (   ; i<lx; i++) z[i] = x[i];
  return Flx_renormalize(z, lz);
}

GEN
Flx_Fl_add(GEN y, ulong x, ulong p)
{
  GEN z;
  long lz, i;
  if (!lgpol(y))
    return Fl_to_Flx(x,y[1]);
  lz=lg(y);
  z=cgetg(lz,t_VECSMALL);
  z[1]=y[1];
  z[2] = Fl_add(y[2],x,p);
  for(i=3;i<lz;i++)
    z[i] = y[i];
  if (lz==3) z = Flx_renormalize(z,lz);
  return z;
}

static GEN
Flx_subspec(GEN x, GEN y, ulong p, long lx, long ly)
{
  long i,lz;
  GEN z;

  if (ly <= lx)
  {
    lz = lx+2; z = cgetg(lz, t_VECSMALL)+2;
    for (i=0; i<ly; i++) z[i] = Fl_sub(x[i],y[i],p);
    for (   ; i<lx; i++) z[i] = x[i];
  }
  else
  {
    lz = ly+2; z = cgetg(lz, t_VECSMALL)+2;
    for (i=0; i<lx; i++) z[i] = Fl_sub(x[i],y[i],p);
    for (   ; i<ly; i++) z[i] = Fl_neg(y[i],p);
  }
 return Flx_renormalize(z-2, lz);
}

GEN
Flx_sub(GEN x, GEN y, ulong p)
{
  long i,lz,lx = lg(x), ly = lg(y);
  GEN z;

  if (ly <= lx)
  {
    lz = lx; z = cgetg(lz, t_VECSMALL);
    for (i=2; i<ly; i++) z[i] = Fl_sub(x[i],y[i],p);
    for (   ; i<lx; i++) z[i] = x[i];
  }
  else
  {
    lz = ly; z = cgetg(lz, t_VECSMALL);
    for (i=2; i<lx; i++) z[i] = Fl_sub(x[i],y[i],p);
    for (   ; i<ly; i++) z[i] = y[i]? (long)(p - y[i]): y[i];
  }
  z[1]=x[1]; return Flx_renormalize(z, lz);
}

static GEN
Flx_negspec(GEN x, ulong p, long l)
{
  long i;
  GEN z = cgetg(l+2, t_VECSMALL) + 2;
  for (i=0; i<l; i++) z[i] = Fl_neg(x[i], p);
  return z-2;
}


GEN
Flx_neg(GEN x, ulong p)
{
  GEN z = Flx_negspec(x+2, p, lgpol(x));
  z[1] = x[1];
  return z;
}

GEN
Flx_neg_inplace(GEN x, ulong p)
{
  long i, l = lg(x);
  for (i=2; i<l; i++)
    if (x[i]) x[i] = p - x[i];
  return x;
}

GEN
Flx_double(GEN y, ulong p)
{
  long i, l;
  GEN z = cgetg_copy(y, &l); z[1] = y[1];
  for(i=2; i<l; i++) z[i] = Fl_double(y[i], p);
  return Flx_renormalize(z, l);
}
GEN
Flx_triple(GEN y, ulong p)
{
  long i, l;
  GEN z = cgetg_copy(y, &l); z[1] = y[1];
  for(i=2; i<l; i++) z[i] = Fl_triple(y[i], p);
  return Flx_renormalize(z, l);
}
GEN
Flx_Fl_mul(GEN y, ulong x, ulong p)
{
  GEN z;
  long i, l;
  if (!x) return pol0_Flx(y[1]);
  z = cgetg_copy(y, &l); z[1] = y[1];
  if (HIGHWORD(x | p))
    for(i=2; i<l; i++) z[i] = Fl_mul(y[i], x, p);
  else
    for(i=2; i<l; i++) z[i] = (y[i] * x) % p;
  return Flx_renormalize(z, l);
}
GEN
Flx_Fl_mul_to_monic(GEN y, ulong x, ulong p)
{
  GEN z;
  long i, l;
  z = cgetg_copy(y, &l); z[1] = y[1];
  if (HIGHWORD(x | p))
    for(i=2; i<l-1; i++) z[i] = Fl_mul(y[i], x, p);
  else
    for(i=2; i<l-1; i++) z[i] = (y[i] * x) % p;
  z[l-1] = 1; return z;
}

/* Return a*x^n if n>=0 and a\x^(-n) if n<0 */
GEN
Flx_shift(GEN a, long n)
{
  long i, l = lg(a);
  GEN  b;
  if (l==2 || !n) return Flx_copy(a);
  if (l+n<=2) return pol0_Flx(a[1]);
  b = cgetg(l+n, t_VECSMALL);
  b[1] = a[1];
  if (n < 0)
    for (i=2-n; i<l; i++) b[i+n] = a[i];
  else
  {
    for (i=0; i<n; i++) b[2+i] = 0;
    for (i=2; i<l; i++) b[i+n] = a[i];
  }
  return b;
}

GEN
Flx_normalize(GEN z, ulong p)
{
  long l = lg(z)-1;
  ulong p1 = z[l]; /* leading term */
  if (p1 == 1) return z;
  return Flx_Fl_mul_to_monic(z, Fl_inv(p1,p), p);
}

/* return (x * X^d) + y. Assume d > 0, x > 0 and y >= 0 */
static GEN
Flx_addshift(GEN x, GEN y, ulong p, long d)
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
    x = Flx_addspec(x,yd,p, nx,a);
    lz = (a>nx)? ny+2: lg(x)+d;
    x += 2; while (xd > x) *--zd = *--xd;
  }
  while (yd > y) *--zd = *--yd;
  *--zd = vs;
  *--zd = evaltyp(t_VECSMALL) | evallg(lz); return zd;
}

/* shift polynomial + gerepile */
/* Do not set evalvarn*/
static GEN
Flx_shiftip(pari_sp av, GEN x, long v)
{
  long i, lx = lg(x), ly;
  GEN y;
  if (!v || lx==2) return gerepileuptoleaf(av, x);
  ly = lx + v; /* result length */
  (void)new_chunk(ly); /* check that result fits */
  x += lx; y = (GEN)av;
  for (i = 2; i<lx; i++) *--y = *--x;
  for (i = 0; i< v; i++) *--y = 0;
  y -= 2; y[0] = evaltyp(t_VECSMALL) | evallg(ly);
  avma = (pari_sp)y; return y;
}

#define BITS_IN_QUARTULONG (BITS_IN_HALFULONG >> 1)
#define QUARTMASK ((1UL<<BITS_IN_QUARTULONG)-1UL)
#define LLQUARTWORD(x) ((x) & QUARTMASK)
#define HLQUARTWORD(x) (((x) >> BITS_IN_QUARTULONG) & QUARTMASK)
#define LHQUARTWORD(x) (((x) >> (2*BITS_IN_QUARTULONG)) & QUARTMASK)
#define HHQUARTWORD(x) (((x) >> (3*BITS_IN_QUARTULONG)) & QUARTMASK)
INLINE long
maxlengthcoeffpol(ulong p, long n)
{
  pari_sp ltop = avma;
  GEN z = muliu(sqru(p-1), n);
  long l = lgefint(z);
  avma = ltop;
  if (l==3 && HIGHWORD(z[2])==0)
  {
    if (HLQUARTWORD(z[2]) == 0) return -1;
    else return 0;
  }
  return l-2;
}

INLINE ulong
Flx_mullimb_ok(GEN x, GEN y, ulong p, long a, long b)
{ /* Assume OK_ULONG*/
  ulong p1 = 0;
  long i;
  for (i=a; i<b; i++)
    if (y[i])
    {
      p1 += y[i] * x[-i];
      if (p1 & HIGHBIT) p1 %= p;
    }
  return p1 % p;
}

INLINE ulong
Flx_mullimb(GEN x, GEN y, ulong p, ulong pi, long a, long b)
{
  ulong p1 = 0;
  long i;
  for (i=a; i<b; i++)
    if (y[i])
      p1 = Fl_addmul_pre(p1, y[i], x[-i], p, pi);
  return p1;
}

/* assume nx >= ny > 0 */
static GEN
Flx_mulspec_basecase(GEN x, GEN y, ulong p, long nx, long ny)
{
  long i,lz,nz;
  GEN z;

  lz = nx+ny+1; nz = lz-2;
  z = cgetg(lz, t_VECSMALL) + 2; /* x:y:z [i] = term of degree i */
  if (SMALL_ULONG(p))
  {
    for (i=0; i<ny; i++)z[i] = Flx_mullimb_ok(x+i,y,p,0,i+1);
    for (  ; i<nx; i++) z[i] = Flx_mullimb_ok(x+i,y,p,0,ny);
    for (  ; i<nz; i++) z[i] = Flx_mullimb_ok(x+i,y,p,i-nx+1,ny);
  }
  else
  {
    ulong pi = get_Fl_red(p);
    for (i=0; i<ny; i++)z[i] = Flx_mullimb(x+i,y,p,pi,0,i+1);
    for (  ; i<nx; i++) z[i] = Flx_mullimb(x+i,y,p,pi,0,ny);
    for (  ; i<nz; i++) z[i] = Flx_mullimb(x+i,y,p,pi,i-nx+1,ny);
  }
  z -= 2; return Flx_renormalize(z, lz);
}

static GEN
int_to_Flx(GEN z, ulong p)
{
  long i, l = lgefint(z);
  GEN x = cgetg(l, t_VECSMALL);
  for (i=2; i<l; i++) x[i] = uel(z,i)%p;
  return Flx_renormalize(x, l);
}

INLINE GEN
Flx_mulspec_mulii(GEN a, GEN b, ulong p, long na, long nb)
{
  GEN z=muliispec(a,b,na,nb);
  return int_to_Flx(z,p);
}

static GEN
Flx_to_int_halfspec(GEN a, long na)
{
  long j;
  long n = (na+1)>>1UL;
  GEN V = cgetipos(2+n);
  GEN w;
  for (w = int_LSW(V), j=0; j+1<na; j+=2, w=int_nextW(w))
    *w = a[j]|(a[j+1]<<BITS_IN_HALFULONG);
  if (j<na)
    *w = a[j];
  return V;
}

static GEN
int_to_Flx_half(GEN z, ulong p)
{
  long i;
  long lx = (lgefint(z)-2)*2+2;
  GEN w, x = cgetg(lx, t_VECSMALL);
  for (w = int_LSW(z), i=2; i<lx; i+=2, w=int_nextW(w))
  {
    x[i]   = LOWWORD((ulong)*w)%p;
    x[i+1] = HIGHWORD((ulong)*w)%p;
  }
  return Flx_renormalize(x, lx);
}

static GEN
Flx_mulspec_halfmulii(GEN a, GEN b, ulong p, long na, long nb)
{
  GEN A = Flx_to_int_halfspec(a,na);
  GEN B = Flx_to_int_halfspec(b,nb);
  GEN z = mulii(A,B);
  return int_to_Flx_half(z,p);
}

static GEN
Flx_to_int_quartspec(GEN a, long na)
{
  long j;
  long n = (na+3)>>2UL;
  GEN V = cgetipos(2+n);
  GEN w;
  for (w = int_LSW(V), j=0; j+3<na; j+=4, w=int_nextW(w))
    *w = a[j]|(a[j+1]<<BITS_IN_QUARTULONG)|(a[j+2]<<(2*BITS_IN_QUARTULONG))|(a[j+3]<<(3*BITS_IN_QUARTULONG));
  switch (na-j)
  {
  case 3:
    *w = a[j]|(a[j+1]<<BITS_IN_QUARTULONG)|(a[j+2]<<(2*BITS_IN_QUARTULONG));
    break;
  case 2:
    *w = a[j]|(a[j+1]<<BITS_IN_QUARTULONG);
    break;
  case 1:
    *w = a[j];
    break;
  case 0:
    break;
  }
  return V;
}

static GEN
int_to_Flx_quart(GEN z, ulong p)
{
  long i;
  long lx = (lgefint(z)-2)*4+2;
  GEN w, x = cgetg(lx, t_VECSMALL);
  for (w = int_LSW(z), i=2; i<lx; i+=4, w=int_nextW(w))
  {
    x[i]   = LLQUARTWORD((ulong)*w)%p;
    x[i+1] = HLQUARTWORD((ulong)*w)%p;
    x[i+2] = LHQUARTWORD((ulong)*w)%p;
    x[i+3] = HHQUARTWORD((ulong)*w)%p;
  }
  return Flx_renormalize(x, lx);
}

static GEN
Flx_mulspec_quartmulii(GEN a, GEN b, ulong p, long na, long nb)
{
  GEN A = Flx_to_int_quartspec(a,na);
  GEN B = Flx_to_int_quartspec(b,nb);
  GEN z = mulii(A,B);
  return int_to_Flx_quart(z,p);
}

/*Eval x in 2^(k*BIL) in linear time, k==2 or 3*/
static GEN
Flx_eval2BILspec(GEN x, long k, long l)
{
  long i, lz = k*l, ki;
  GEN pz = cgetipos(2+lz);
  for (i=0; i < lz; i++)
    *int_W(pz,i) = 0UL;
  for (i=0, ki=0; i<l; i++, ki+=k)
    *int_W(pz,ki) = x[i];
  return int_normalize(pz,0);
}

static GEN
Z_mod2BIL_Flx_2(GEN x, long d, ulong p)
{
  long i, offset, lm = lgefint(x)-2, l = d+3;
  ulong pi = get_Fl_red(p);
  GEN pol = cgetg(l, t_VECSMALL);
  pol[1] = 0;
  for (i=0, offset=0; offset+1 < lm; i++, offset += 2)
    pol[i+2] = remll_pre(*int_W(x,offset+1), *int_W(x,offset), p, pi);
  if (offset < lm)
    pol[i+2] = (*int_W(x,offset)) % p;
  return Flx_renormalize(pol,l);
}

static GEN
Z_mod2BIL_Flx_3(GEN x, long d, ulong p)
{
  long i, offset, lm = lgefint(x)-2, l = d+3;
  ulong pi = get_Fl_red(p);
  GEN pol = cgetg(l, t_VECSMALL);
  pol[1] = 0;
  for (i=0, offset=0; offset+2 < lm; i++, offset += 3)
    pol[i+2] = remlll_pre(*int_W(x,offset+2), *int_W(x,offset+1),
                          *int_W(x,offset), p, pi);
  if (offset+1 < lm)
    pol[i+2] = remll_pre(*int_W(x,offset+1), *int_W(x,offset), p, pi);
  else if (offset < lm)
    pol[i+2] = (*int_W(x,offset)) % p;
  return Flx_renormalize(pol,l);
}

static GEN
Z_mod2BIL_Flx(GEN x, long bs, long d, ulong p)
{
  return bs==2 ? Z_mod2BIL_Flx_2(x, d, p): Z_mod2BIL_Flx_3(x, d, p);
}

static GEN
Flx_mulspec_mulii_inflate(GEN x, GEN y, long N, ulong p, long nx, long ny)
{
  pari_sp av = avma;
  GEN z = mulii(Flx_eval2BILspec(x,N,nx), Flx_eval2BILspec(y,N,ny));
  return gerepileupto(av, Z_mod2BIL_Flx(z, N, nx+ny-2, p));
}

/* fast product (Karatsuba) of polynomials a,b. These are not real GENs, a+2,
 * b+2 were sent instead. na, nb = number of terms of a, b.
 * Only c, c0, c1, c2 are genuine GEN.
 */
static GEN
Flx_mulspec(GEN a, GEN b, ulong p, long na, long nb)
{
  GEN a0,c,c0;
  long n0, n0a, i, v = 0;
  pari_sp av;

  while (na && !a[0]) { a++; na--; v++; }
  while (nb && !b[0]) { b++; nb--; v++; }
  if (na < nb) swapspec(a,b, na,nb);
  if (!nb) return pol0_Flx(0);

  av = avma;
  switch (maxlengthcoeffpol(p,nb))
  {
  case -1:
    if (na>=Flx_MUL_QUARTMULII_LIMIT)
      return Flx_shiftip(av,Flx_mulspec_quartmulii(a,b,p,na,nb), v);
    break;
  case 0:
    if (na>=Flx_MUL_HALFMULII_LIMIT)
      return Flx_shiftip(av,Flx_mulspec_halfmulii(a,b,p,na,nb), v);
    break;
  case 1:
    if (na>=Flx_MUL_MULII_LIMIT)
      return Flx_shiftip(av,Flx_mulspec_mulii(a,b,p,na,nb), v);
    break;
  case 2:
    if (na>=Flx_MUL_MULII2_LIMIT)
      return Flx_shiftip(av,Flx_mulspec_mulii_inflate(a,b,2,p,na,nb), v);
    break;
  case 3:
    if (na>70)
      return Flx_shiftip(av,Flx_mulspec_mulii_inflate(a,b,3,p,na,nb), v);
    break;
  }
  if (nb < Flx_MUL_KARATSUBA_LIMIT)
    return Flx_shiftip(av,Flx_mulspec_basecase(a,b,p,na,nb), v);
  i=(na>>1); n0=na-i; na=i;
  a0=a+n0; n0a=n0;
  while (n0a && !a[n0a-1]) n0a--;

  if (nb > n0)
  {
    GEN b0,c1,c2;
    long n0b;

    nb -= n0; b0 = b+n0; n0b = n0;
    while (n0b && !b[n0b-1]) n0b--;
    c =  Flx_mulspec(a,b,p,n0a,n0b);
    c0 = Flx_mulspec(a0,b0,p,na,nb);

    c2 = Flx_addspec(a0,a,p,na,n0a);
    c1 = Flx_addspec(b0,b,p,nb,n0b);

    c1 = Flx_mul(c1,c2,p);
    c2 = Flx_add(c0,c,p);

    c2 = Flx_neg_inplace(c2,p);
    c2 = Flx_add(c1,c2,p);
    c0 = Flx_addshift(c0,c2 ,p, n0);
  }
  else
  {
    c  = Flx_mulspec(a,b,p,n0a,nb);
    c0 = Flx_mulspec(a0,b,p,na,nb);
  }
  c0 = Flx_addshift(c0,c,p,n0);
  return Flx_shiftip(av,c0, v);
}


GEN
Flx_mul(GEN x, GEN y, ulong p)
{
 GEN z = Flx_mulspec(x+2,y+2,p, lgpol(x),lgpol(y));
 z[1] = x[1]; return z;
}

static GEN
Flx_sqrspec_basecase(GEN x, ulong p, long nx)
{
  long i, lz, nz;
  ulong p1;
  GEN z;

  if (!nx) return pol0_Flx(0);
  lz = (nx << 1) + 1, nz = lz-2;
  z = cgetg(lz, t_VECSMALL) + 2;
  if (SMALL_ULONG(p))
  {
    z[0] = x[0]*x[0]%p;
    for (i=1; i<nx; i++)
    {
      p1 = Flx_mullimb_ok(x+i,x,p,0, (i+1)>>1);
      p1 <<= 1;
      if ((i&1) == 0) p1 += x[i>>1] * x[i>>1];
      z[i] = p1 % p;
    }
    for (  ; i<nz; i++)
    {
      p1 = Flx_mullimb_ok(x+i,x,p,i-nx+1, (i+1)>>1);
      p1 <<= 1;
      if ((i&1) == 0) p1 += x[i>>1] * x[i>>1];
      z[i] = p1 % p;
    }
  }
  else
  {
    ulong pi = get_Fl_red(p);
    z[0] = Fl_sqr_pre(x[0], p, pi);
    for (i=1; i<nx; i++)
    {
      p1 = Flx_mullimb(x+i,x,p,pi,0, (i+1)>>1);
      p1 = Fl_add(p1, p1, p);
      if ((i&1) == 0) p1 = Fl_add(p1, Fl_sqr_pre(x[i>>1], p, pi), p);
      z[i] = p1;
    }
    for (  ; i<nz; i++)
    {
      p1 = Flx_mullimb(x+i,x,p,pi,i-nx+1, (i+1)>>1);
      p1 = Fl_add(p1, p1, p);
      if ((i&1) == 0) p1 = Fl_add(p1, Fl_sqr_pre(x[i>>1], p, pi), p);
      z[i] = p1;
    }
  }
  z -= 2; return Flx_renormalize(z, lz);
}

static GEN
Flx_sqrspec_sqri(GEN a, ulong p, long na)
{
  GEN z=sqrispec(a,na);
  return int_to_Flx(z,p);
}

static GEN
Flx_sqrspec_halfsqri(GEN a, ulong p, long na)
{
  GEN z = sqri(Flx_to_int_halfspec(a,na));
  return int_to_Flx_half(z,p);
}

static GEN
Flx_sqrspec_quartsqri(GEN a, ulong p, long na)
{
  GEN z = sqri(Flx_to_int_quartspec(a,na));
  return int_to_Flx_quart(z,p);
}

static GEN
Flx_sqrspec_sqri_inflate(GEN x, long N, ulong p, long nx)
{
  pari_sp av = avma;
  GEN  z = sqri(Flx_eval2BILspec(x,N,nx));
  return gerepileupto(av, Z_mod2BIL_Flx(z, N, (nx-1)*2, p));
}

static GEN
Flx_sqrspec(GEN a, ulong p, long na)
{
  GEN a0, c, c0;
  long n0, n0a, i, v = 0;
  pari_sp av;

  while (na && !a[0]) { a++; na--; v += 2; }
  if (!na) return pol0_Flx(0);

  av = avma;
  switch(maxlengthcoeffpol(p,na))
  {
  case -1:
    if (na>=Flx_SQR_QUARTSQRI_LIMIT)
      return Flx_shiftip(av, Flx_sqrspec_quartsqri(a,p,na), v);
    break;
  case 0:
    if (na>=Flx_SQR_HALFSQRI_LIMIT)
      return Flx_shiftip(av, Flx_sqrspec_halfsqri(a,p,na), v);
    break;
  case 1:
    if (na>=Flx_SQR_SQRI_LIMIT)
      return Flx_shiftip(av, Flx_sqrspec_sqri(a,p,na), v);
    break;
  case 2:
    if (na>=Flx_SQR_SQRI2_LIMIT)
      return Flx_shiftip(av, Flx_sqrspec_sqri_inflate(a,2,p,na), v);
    break;
  case 3:
    if (na>70)
      return Flx_shiftip(av, Flx_sqrspec_sqri_inflate(a,3,p,na), v);
    break;
  }
  if (na < Flx_SQR_KARATSUBA_LIMIT)
    return Flx_shiftip(av, Flx_sqrspec_basecase(a,p,na), v);
  i=(na>>1); n0=na-i; na=i;
  a0=a+n0; n0a=n0;
  while (n0a && !a[n0a-1]) n0a--;

  c = Flx_sqrspec(a,p,n0a);
  c0= Flx_sqrspec(a0,p,na);
  if (p == 2) n0 *= 2;
  else
  {
    GEN c1, t = Flx_addspec(a0,a,p,na,n0a);
    t = Flx_sqr(t,p);
    c1= Flx_add(c0,c, p);
    c1= Flx_sub(t, c1, p);
    c0 = Flx_addshift(c0,c1,p,n0);
  }
  c0 = Flx_addshift(c0,c,p,n0);
  return Flx_shiftip(av,c0,v);
}

GEN
Flx_sqr(GEN x, ulong p)
{
  GEN z = Flx_sqrspec(x+2,p, lgpol(x));
  z[1] = x[1]; return z;
}

GEN
Flx_powu(GEN x, ulong n, ulong p)
{
  GEN y = pol1_Flx(x[1]), z;
  ulong m;
  if (n == 0) return y;
  m = n; z = x;
  for (;;)
  {
    if (m&1UL) y = Flx_mul(y,z, p);
    m >>= 1; if (!m) return y;
    z = Flx_sqr(z, p);
  }
}

GEN
Flx_halve(GEN y, ulong p)
{
  GEN z;
  long i, l;
  z = cgetg_copy(y, &l); z[1] = y[1];
  for(i=2; i<l; i++) uel(z,i) = Fl_halve(uel(y,i), p);
  return z;
}

static GEN
Flx_recipspec(GEN x, long l, long n)
{
  long i;
  GEN z=cgetg(n+2,t_VECSMALL)+2;
  for(i=0; i<l; i++)
    z[n-i-1] = x[i];
  for(   ; i<n; i++)
    z[n-i-1] = 0;
  return Flx_renormalize(z-2,n+2);
}

GEN
Flx_recip(GEN x)
{
  GEN z=Flx_recipspec(x+2,lgpol(x),lgpol(x));
  z[1]=x[1];
  return z;
}

/* Return h^degpol(P) P(x / h) */
GEN
Flx_rescale(GEN P, ulong h, ulong p)
{
  long i, l = lg(P);
  GEN Q = cgetg(l,t_VECSMALL);
  ulong hi = h;
  Q[l-1] = P[l-1];
  for (i=l-2; i>=2; i--)
  {
    Q[i] = Fl_mul(P[i], hi, p);
    if (i == 2) break;
    hi = Fl_mul(hi,h, p);
  }
  Q[1] = P[1]; return Q;
}

static long
Flx_multhreshold(GEN T, ulong p, long quart, long half, long mul, long mul2, long kara)
{
  long na = lgpol(T);
  switch (maxlengthcoeffpol(p,na))
  {
  case -1:
    if (na>=Flx_MUL_QUARTMULII_LIMIT)
      return na>=quart;
    break;
  case 0:
    if (na>=Flx_MUL_HALFMULII_LIMIT)
      return na>=half;
    break;
  case 1:
    if (na>=Flx_MUL_MULII_LIMIT)
      return na>=mul;
    break;
  case 2:
    if (na>=Flx_MUL_MULII2_LIMIT)
      return na>=mul2;
    break;
  case 3:
    if (na>=70)
      return na>=70;
    break;
  }
  return na>=kara;
}

/*
 * x/polrecip(P)+O(x^n)
 */
static GEN
Flx_invBarrett_basecase(GEN T, ulong p)
{
  long i, l=lg(T)-1, lr=l-1, k;
  GEN r=cgetg(lr,t_VECSMALL); r[1] = T[1];
  r[2] = 1;
  if (SMALL_ULONG(p))
    for (i=3;i<lr;i++)
    {
      ulong u = uel(T, l-i+2);
      for (k=3; k<i; k++)
        { u += uel(T,l-i+k) * uel(r, k); if (u & HIGHBIT) u %= p; }
      r[i] = Fl_neg(u % p, p);
    }
  else
    for (i=3;i<lr;i++)
    {
      ulong u = Fl_neg(uel(T,l-i+2), p);
      for (k=3; k<i; k++)
        u = Fl_sub(u, Fl_mul(uel(T,l-i+k), uel(r,k), p), p);
      r[i] = u;
    }
  return Flx_renormalize(r,lr);
}

/* Return new lgpol */
static long
Flx_lgrenormalizespec(GEN x, long lx)
{
  long i;
  for (i = lx-1; i>=0; i--)
    if (x[i]) break;
  return i+1;
}
static GEN
Flx_invBarrett_Newton(GEN T, ulong p)
{
  long nold, lx, lz, lq, l = degpol(T), lQ;
  GEN q, y, z, x = zero_zv(l+1) + 2;
  ulong mask = quadratic_prec_mask(l-2); /* assume l > 2 */
  pari_sp av;

  y = T+2;
  q = Flx_recipspec(y,l+1,l+1); lQ = lgpol(q); q+=2;
  av = avma;
  /* We work on _spec_ Flx's, all the l[xzq12] below are lgpol's */

  /* initialize */
  x[0] = Fl_inv(q[0], p);
  if (lQ>1 && q[1])
  {
    ulong u = q[1];
    if (x[0] != 1) u = Fl_mul(u, Fl_sqr(x[0],p), p);
    x[1] = p - u; lx = 2;
  }
  else
    lx = 1;
  nold = 1;
  for (; mask > 1; avma = av)
  { /* set x -= x(x*q - 1) + O(t^(nnew + 1)), knowing x*q = 1 + O(t^(nold+1)) */
    long i, lnew, nnew = nold << 1;

    if (mask & 1) nnew--;
    mask >>= 1;

    lnew = nnew + 1;
    lq = Flx_lgrenormalizespec(q, minss(lQ, lnew));
    z = Flx_mulspec(x, q, p, lx, lq); /* FIXME: high product */
    lz = lgpol(z); if (lz > lnew) lz = lnew;
    z += 2;
    /* subtract 1 [=>first nold words are 0]: renormalize so that z(0) != 0 */
    for (i = nold; i < lz; i++) if (z[i]) break;
    nold = nnew;
    if (i >= lz) continue; /* z-1 = 0(t^(nnew + 1)) */

    /* z + i represents (x*q - 1) / t^i */
    lz = Flx_lgrenormalizespec (z+i, lz-i);
    z = Flx_mulspec(x, z+i, p, lx, lz); /* FIXME: low product */
    lz = lgpol(z); z += 2;
    if (lz > lnew-i) lz = Flx_lgrenormalizespec(z, lnew-i);

    lx = lz+ i;
    y  = x + i; /* x -= z * t^i, in place */
    for (i = 0; i < lz; i++) y[i] = Fl_neg(z[i], p);
  }
  x -= 2; setlg(x, lx + 2); x[1] = T[1];
  return x;
}

/* x/polrecip(T)+O(x^deg(T)) */
GEN
Flx_invBarrett(GEN T, ulong p)
{
  pari_sp ltop=avma;
  long l=lg(T);
  GEN r;
  if (l<5) return pol0_Flx(T[1]);
  if (!Flx_multhreshold(T,p, Flx_INVBARRETT_QUARTMULII_LIMIT,
                             Flx_INVBARRETT_HALFMULII_LIMIT,
                             Flx_INVBARRETT_MULII_LIMIT,
                             Flx_INVBARRETT_MULII2_LIMIT,
                             Flx_INVBARRETT_KARATSUBA_LIMIT))
  {
    ulong c = T[l-1];
    if (c!=1)
    {
      ulong ci = Fl_inv(c,p);
      T=Flx_Fl_mul(T, ci, p);
      r=Flx_invBarrett_basecase(T,p);
      r=Flx_Fl_mul(r,ci,p);
    }
    else
      r=Flx_invBarrett_basecase(T,p);
  }
  else
    r = Flx_invBarrett_Newton(T,p);
  return gerepileuptoleaf(ltop, r);
}

GEN
Flx_get_red(GEN T, ulong p)
{
  if (typ(T)!=t_VECSMALL || !Flx_multhreshold(T,p,
                         Flx_BARRETT_QUARTMULII_LIMIT,
                         Flx_BARRETT_HALFMULII_LIMIT,
                         Flx_BARRETT_MULII_LIMIT,
                         Flx_BARRETT_MULII2_LIMIT,
                         Flx_BARRETT_KARATSUBA_LIMIT))
    return T;
  retmkvec2(Flx_invBarrett(T,p),T);
}

/* separate from Flx_divrem for maximal speed. */
static GEN
Flx_rem_basecase(GEN x, GEN y, ulong p)
{
  pari_sp av;
  GEN z, c;
  long dx,dy,dy1,dz,i,j;
  ulong p1,inv;
  long vs=x[1];

  dy = degpol(y); if (!dy) return pol0_Flx(x[1]);
  dx = degpol(x);
  dz = dx-dy; if (dz < 0) return Flx_copy(x);
  x += 2; y += 2;
  inv = y[dy];
  if (inv != 1UL) inv = Fl_inv(inv,p);
  for (dy1=dy-1; dy1>=0 && !y[dy1]; dy1--);

  c = cgetg(dy+3, t_VECSMALL); c[1]=vs; c += 2; av=avma;
  z = cgetg(dz+3, t_VECSMALL); z[1]=vs; z += 2;

  if (SMALL_ULONG(p))
  {
    z[dz] = (inv*x[dx]) % p;
    for (i=dx-1; i>=dy; --i)
    {
      p1 = p - x[i]; /* compute -p1 instead of p1 (pb with ulongs otherwise) */
      for (j=i-dy1; j<=i && j<=dz; j++)
      {
        p1 += z[j]*y[i-j];
        if (p1 & HIGHBIT) p1 %= p;
      }
      p1 %= p;
      z[i-dy] = p1? ((p - p1)*inv) % p: 0;
    }
    for (i=0; i<dy; i++)
    {
      p1 = z[0]*y[i];
      for (j=maxss(1,i-dy1); j<=i && j<=dz; j++)
      {
        p1 += z[j]*y[i-j];
        if (p1 & HIGHBIT) p1 %= p;
      }
      c[i] = Fl_sub(x[i], p1%p, p);
    }
  }
  else
  {
    ulong pi = get_Fl_red(p);
    z[dz] = Fl_mul_pre(inv, x[dx], p, pi);
    for (i=dx-1; i>=dy; --i)
    {
      p1 = p - x[i]; /* compute -p1 instead of p1 (pb with ulongs otherwise) */
      for (j=i-dy1; j<=i && j<=dz; j++)
        p1 = Fl_addmul_pre(p1, z[j], y[i - j], p, pi);
      z[i-dy] = p1? Fl_mul_pre(p - p1, inv, p, pi): 0;
    }
    for (i=0; i<dy; i++)
    {
      p1 = Fl_mul_pre(z[0],y[i],p,pi);
      for (j=maxss(1,i-dy1); j<=i && j<=dz; j++)
        p1 = Fl_addmul_pre(p1, z[j], y[i - j], p, pi);
      c[i] = Fl_sub(x[i], p1, p);
    }
  }
  i = dy-1; while (i>=0 && !c[i]) i--;
  avma=av;
  return Flx_renormalize(c-2, i+3);
}

/* as FpX_divrem but working only on ulong types.
 * if relevant, *pr is the last object on stack */
static GEN
Flx_divrem_basecase(GEN x, GEN y, ulong p, GEN *pr)
{
  GEN z,q,c;
  long dx,dy,dy1,dz,i,j;
  ulong p1,inv;
  long sv=x[1];

  dy = degpol(y);
  if (dy<0) pari_err_INV("Flx_divrem",y);
  if (pr == ONLY_REM) return Flx_rem_basecase(x, y, p);
  if (!dy)
  {
    if (pr && pr != ONLY_DIVIDES) *pr = pol0_Flx(sv);
    if (y[2] == 1UL) return Flx_copy(x);
    return Flx_Fl_mul(x, Fl_inv(y[2], p), p);
  }
  dx = degpol(x);
  dz = dx-dy;
  if (dz < 0)
  {
    q = pol0_Flx(sv);
    if (pr && pr != ONLY_DIVIDES) *pr = Flx_copy(x);
    return q;
  }
  x += 2;
  y += 2;
  z = cgetg(dz + 3, t_VECSMALL); z[1] = sv; z += 2;
  inv = uel(y, dy);
  if (inv != 1UL) inv = Fl_inv(inv,p);
  for (dy1=dy-1; dy1>=0 && !y[dy1]; dy1--);

  if (SMALL_ULONG(p))
  {
    z[dz] = (inv*x[dx]) % p;
    for (i=dx-1; i>=dy; --i)
    {
      p1 = p - x[i]; /* compute -p1 instead of p1 (pb with ulongs otherwise) */
      for (j=i-dy1; j<=i && j<=dz; j++)
      {
        p1 += z[j]*y[i-j];
        if (p1 & HIGHBIT) p1 %= p;
      }
      p1 %= p;
      z[i-dy] = p1? (long) ((p - p1)*inv) % p: 0;
    }
  }
  else
  {
    z[dz] = Fl_mul(inv, x[dx], p);
    for (i=dx-1; i>=dy; --i)
    { /* compute -p1 instead of p1 (pb with ulongs otherwise) */
      p1 = p - uel(x,i);
      for (j=i-dy1; j<=i && j<=dz; j++)
        p1 = Fl_add(p1, Fl_mul(z[j],y[i-j],p), p);
      z[i-dy] = p1? Fl_mul(p - p1, inv, p): 0;
    }
  }
  q = Flx_renormalize(z-2, dz+3);
  if (!pr) return q;

  c = cgetg(dy + 3, t_VECSMALL); c[1] = sv; c += 2;
  if (SMALL_ULONG(p))
  {
    for (i=0; i<dy; i++)
    {
      p1 = (ulong)z[0]*y[i];
      for (j=maxss(1,i-dy1); j<=i && j<=dz; j++)
      {
        p1 += (ulong)z[j]*y[i-j];
        if (p1 & HIGHBIT) p1 %= p;
      }
      c[i] = Fl_sub(x[i], p1%p, p);
    }
  }
  else
  {
    for (i=0; i<dy; i++)
    {
      p1 = Fl_mul(z[0],y[i],p);
      for (j=maxss(1,i-dy1); j<=i && j<=dz; j++)
        p1 = Fl_add(p1, Fl_mul(z[j],y[i-j],p), p);
      c[i] = Fl_sub(x[i], p1, p);
    }
  }
  i=dy-1; while (i>=0 && !c[i]) i--;
  c = Flx_renormalize(c-2, i+3);
  if (pr == ONLY_DIVIDES)
  { if (lg(c) != 2) return NULL; }
  else
    *pr = c;
  return q;
}


/* Compute x mod T where 2 <= degpol(T) <= l+1 <= 2*(degpol(T)-1)
 * and mg is the Barrett inverse of T. */
static GEN
Flx_divrem_Barrettspec(GEN x, long l, GEN mg, GEN T, ulong p, GEN *pr)
{
  GEN q, r;
  long lt = degpol(T); /*We discard the leading term*/
  long ld, lm, lT, lmg;
  ld = l-lt;
  lm = minss(ld, lgpol(mg));
  lT  = Flx_lgrenormalizespec(T+2,lt);
  lmg = Flx_lgrenormalizespec(mg+2,lm);
  q = Flx_recipspec(x+lt,ld,ld);               /* q = rec(x)      lz<=ld*/
  q = Flx_mulspec(q+2,mg+2,p,lgpol(q),lmg);    /* q = rec(x) * mg lz<=ld+lm*/
  q = Flx_recipspec(q+2,minss(ld,lgpol(q)),ld);/* q = rec (rec(x) * mg) lz<=ld*/
  if (!pr) return q;
  r = Flx_mulspec(q+2,T+2,p,lgpol(q),lT);      /* r = q*pol       lz<=ld+lt*/
  r = Flx_subspec(x,r+2,p,lt,minss(lt,lgpol(r)));/* r = x - q*pol lz<=lt */
  if (pr == ONLY_REM) return r;
  *pr = r; return q;
}

static GEN
Flx_divrem_Barrett_noGC(GEN x, GEN mg, GEN T, ulong p, GEN *pr)
{
  long l = lgpol(x), lt = degpol(T), lm = 2*lt-1;
  GEN q = NULL, r;
  long i;
  if (l <= lt)
  {
    if (pr == ONLY_REM) return Flx_copy(x);
    if (pr == ONLY_DIVIDES) return lgpol(x)? NULL: pol0_Flx(x[1]);
    if (pr) *pr = Flx_copy(x);
    return pol0_Flx(x[1]);
  }
  if (lt <= 1)
    return Flx_divrem_basecase(x,T,p,pr);
  if (pr != ONLY_REM && l>lm)
    q = zero_zv(l-lt+1);
  r = Flx_copy(x);
  while (l>lm)
  {
    GEN zr, zq = Flx_divrem_Barrettspec(r+2+l-lm,lm,mg,T,p,&zr);
    long lz = lgpol(zr);
    if (pr != ONLY_REM)
    {
      long lq = lgpol(zq);
      for(i=0; i<lq; i++) q[2+l-lm+i] = zq[2+i];
    }
    for(i=0; i<lz; i++)   r[2+l-lm+i] = zr[2+i];
    l = l-lm+lz;
  }
  if (pr != ONLY_REM)
  {
    if (l > lt)
    {
      GEN zq = Flx_divrem_Barrettspec(r+2,l,mg,T,p,&r);
      if (!q) q = zq;
      else
      {
        long lq = lgpol(zq);
        for(i=0; i<lq; i++) q[2+i] = zq[2+i];
      }
    }
    else
      r = Flx_renormalize(r, l+2);
  }
  else
  {
    if (l > lt)
      r = Flx_divrem_Barrettspec(r+2,l,mg,T,p,ONLY_REM);
    else
      r = Flx_renormalize(r, l+2);
    r[1] = x[1]; return Flx_renormalize(r, lg(r));
  }
  if (pr) { r[1] = x[1]; r = Flx_renormalize(r, lg(r)); }
  q[1] = x[1]; q = Flx_renormalize(q, lg(q));
  if (pr == ONLY_DIVIDES) return lgpol(r)? NULL: q;
  if (pr) *pr = r;
  return q;
}

GEN
Flx_divrem(GEN x, GEN T, ulong p, GEN *pr)
{
  GEN B, y = get_Flx_red(T, &B);
  long dy = degpol(y), dx = degpol(x), d = dx-dy;
  if (pr==ONLY_REM) return Flx_rem(x, y, p);
  if (!B && d+3 < Flx_DIVREM_BARRETT_LIMIT)
    return Flx_divrem_basecase(x,y,p,pr);
  else
  {
    pari_sp av=avma;
    GEN mg = B? B: Flx_invBarrett(y, p);
    GEN q1 = Flx_divrem_Barrett_noGC(x,mg,y,p,pr);
    if (!q1) {avma=av; return NULL;}
    if (!pr || pr==ONLY_DIVIDES) return gerepileuptoleaf(av, q1);
    gerepileall(av,2,&q1,pr);
    return q1;
  }
}

GEN
Flx_rem(GEN x, GEN T, ulong p)
{
  GEN B, y = get_Flx_red(T, &B);
  long dy = degpol(y), dx = degpol(x), d = dx-dy;
  if (d < 0) return Flx_copy(x);
  if (!B && d+3 < Flx_REM_BARRETT_LIMIT)
    return Flx_rem_basecase(x,y,p);
  else
  {
    pari_sp av=avma;
    GEN mg = B ? B: Flx_invBarrett(y, p);
    GEN r  = Flx_divrem_Barrett_noGC(x, mg, y, p, ONLY_REM);
    return gerepileuptoleaf(av, r);
  }
}

/* reduce T mod (X^n - 1, p). Shallow function */
GEN
Flx_mod_Xnm1(GEN T, ulong n, ulong p)
{
  long i, j, L = lg(T), l = n+2;
  GEN S;
  if (L <= l || n & ~LGBITS) return T;
  S = cgetg(l, t_VECSMALL);
  S[1] = T[1];
  for (i = 2; i < l; i++) S[i] = T[i];
  for (j = 2; i < L; i++) {
    S[j] = Fl_add(S[j], T[i], p);
    if (++j == l) j = 2;
  }
  return Flx_renormalize(S, l);
}
/* reduce T mod (X^n + 1, p). Shallow function */
GEN
Flx_mod_Xn1(GEN T, ulong n, ulong p)
{
  long i, j, L = lg(T), l = n+2;
  GEN S;
  if (L <= l || n & ~LGBITS) return T;
  S = cgetg(l, t_VECSMALL);
  S[1] = T[1];
  for (i = 2; i < l; i++) S[i] = T[i];
  for (j = 2; i < L; i++) {
    S[j] = Fl_sub(S[j], T[i], p);
    if (++j == l) j = 2;
  }
  return Flx_renormalize(S, l);
}

struct _Flxq {
  GEN aut;
  GEN T;
  ulong p;
};

static GEN
_Flx_divrem(void * E, GEN x, GEN y, GEN *r)
{
  struct _Flxq *D = (struct _Flxq*) E;
  return Flx_divrem(x, y, D->p, r);
}
static GEN
_Flx_add(void * E, GEN x, GEN y) {
  struct _Flxq *D = (struct _Flxq*) E;
  return Flx_add(x, y, D->p);
}
static GEN
_Flx_mul(void *E, GEN x, GEN y) {
  struct _Flxq *D = (struct _Flxq*) E;
  return Flx_mul(x, y, D->p);
}
static GEN
_Flx_sqr(void *E, GEN x) {
  struct _Flxq *D = (struct _Flxq*) E;
  return Flx_sqr(x, D->p);
}

static struct bb_ring Flx_ring = { _Flx_add,_Flx_mul,_Flx_sqr };

GEN
Flx_digits(GEN x, GEN T, ulong p)
{
  pari_sp av = avma;
  struct _Flxq D;
  long d = degpol(T), n = (lgpol(x)+d-1)/d;
  GEN z;
  D.p = p;
  z = gen_digits(x,T,n,(void *)&D, &Flx_ring, _Flx_divrem);
  return gerepileupto(av, z);
}

GEN
FlxV_Flx_fromdigits(GEN x, GEN T, ulong p)
{
  pari_sp av = avma;
  struct _Flxq D;
  GEN z;
  D.p = p;
  z = gen_fromdigits(x,T,(void *)&D, &Flx_ring);
  return gerepileupto(av, z);
}

long
Flx_val(GEN x)
{
  long i, l=lg(x);
  if (l==2)  return LONG_MAX;
  for (i=2; i<l && x[i]==0; i++) /*empty*/;
  return i-2;
}
long
Flx_valrem(GEN x, GEN *Z)
{
  long v, i, l=lg(x);
  GEN y;
  if (l==2) { *Z = Flx_copy(x); return LONG_MAX; }
  for (i=2; i<l && x[i]==0; i++) /*empty*/;
  v = i-2;
  if (v == 0) { *Z = x; return 0; }
  l -= v;
  y = cgetg(l, t_VECSMALL); y[1] = x[1];
  for (i=2; i<l; i++) y[i] = x[i+v];
  *Z = y; return v;
}

GEN
Flx_deriv(GEN z, ulong p)
{
  long i,l = lg(z)-1;
  GEN x;
  if (l < 2) l = 2;
  x = cgetg(l, t_VECSMALL); x[1] = z[1]; z++;
  if (HIGHWORD(l | p))
    for (i=2; i<l; i++) x[i] = Fl_mul((ulong)i-1, z[i], p);
  else
    for (i=2; i<l; i++) x[i] = ((i-1) * z[i]) % p;
  return Flx_renormalize(x,l);
}

GEN
Flx_translate1(GEN P, ulong p)
{
  long i, k, n = degpol(P);
  GEN R = Flx_copy(P);
  for (i=1; i<=n; i++)
    for (k=n-i; k<n; k++)
      uel(R,k+2) = Fl_add(uel(R,k+2), uel(R,k+3), p);
  return R;
}

GEN
Flx_diff1(GEN P, ulong p)
{
  return Flx_sub(Flx_translate1(P, p), P, p);
}

GEN
Flx_deflate(GEN x0, long d)
{
  GEN z, y, x;
  long i,id, dy, dx = degpol(x0);
  if (d == 1 || dx <= 0) return Flx_copy(x0);
  dy = dx/d;
  y = cgetg(dy+3, t_VECSMALL); y[1] = x0[1];
  z = y + 2;
  x = x0+ 2;
  for (i=id=0; i<=dy; i++,id+=d) z[i] = x[id];
  return y;
}

GEN
Flx_inflate(GEN x0, long d)
{
  long i, id, dy, dx = degpol(x0);
  GEN x = x0 + 2, z, y;
  if (dx <= 0) return Flx_copy(x0);
  dy = dx*d;
  y = cgetg(dy+3, t_VECSMALL); y[1] = x0[1];
  z = y + 2;
  for (i=0; i<=dy; i++) z[i] = 0;
  for (i=id=0; i<=dx; i++,id+=d) z[id] = x[i];
  return y;
}

/* write p(X) = a_0(X^k) + X*a_1(X^k) + ... + X^(k-1)*a_{k-1}(X^k) */
GEN
Flx_splitting(GEN p, long k)
{
  long n = degpol(p), v = p[1], m, i, j, l;
  GEN r;

  m = n/k;
  r = cgetg(k+1,t_VEC);
  for(i=1; i<=k; i++)
  {
    gel(r,i) = cgetg(m+3, t_VECSMALL);
    mael(r,i,1) = v;
  }
  for (j=1, i=0, l=2; i<=n; i++)
  {
    mael(r,j,l) = p[2+i];
    if (j==k) { j=1; l++; } else j++;
  }
  for(i=1; i<=k; i++)
    gel(r,i) = Flx_renormalize(gel(r,i),i<j?l+1:l);
  return r;
}
static GEN
Flx_halfgcd_basecase(GEN a, GEN b, ulong p)
{
  pari_sp av=avma;
  GEN u,u1,v,v1;
  long vx = a[1];
  long n = lgpol(a)>>1;
  u1 = v = pol0_Flx(vx);
  u = v1 = pol1_Flx(vx);
  while (lgpol(b)>n)
  {
    GEN r, q = Flx_divrem(a,b,p, &r);
    a = b; b = r; swap(u,u1); swap(v,v1);
    u1 = Flx_sub(u1, Flx_mul(u, q, p), p);
    v1 = Flx_sub(v1, Flx_mul(v, q ,p), p);
    if (gc_needed(av,2))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"Flx_halfgcd (d = %ld)",degpol(b));
      gerepileall(av,6, &a,&b,&u1,&v1,&u,&v);
    }
  }
  return gerepilecopy(av, mkmat2(mkcol2(u,u1), mkcol2(v,v1)));
}
/* ux + vy */
static GEN
Flx_addmulmul(GEN u, GEN v, GEN x, GEN y, ulong p)
{ return Flx_add(Flx_mul(u,x, p), Flx_mul(v,y, p), p); }

static GEN
FlxM_Flx_mul2(GEN M, GEN x, GEN y, ulong p)
{
  GEN res = cgetg(3, t_COL);
  gel(res, 1) = Flx_addmulmul(gcoeff(M,1,1), gcoeff(M,1,2), x, y, p);
  gel(res, 2) = Flx_addmulmul(gcoeff(M,2,1), gcoeff(M,2,2), x, y, p);
  return res;
}

#if 0
static GEN
FlxM_mul2_old(GEN M, GEN N, ulong p)
{
  GEN res = cgetg(3, t_MAT);
  gel(res, 1) = FlxM_Flx_mul2(M,gcoeff(N,1,1),gcoeff(N,2,1),p);
  gel(res, 2) = FlxM_Flx_mul2(M,gcoeff(N,1,2),gcoeff(N,2,2),p);
  return res;
}
#endif
/* A,B are 2x2 matrices, Flx entries. Return A x B using Strassen 7M formula */
static GEN
FlxM_mul2(GEN A, GEN B, ulong p)
{
  GEN A11=gcoeff(A,1,1),A12=gcoeff(A,1,2), B11=gcoeff(B,1,1),B12=gcoeff(B,1,2);
  GEN A21=gcoeff(A,2,1),A22=gcoeff(A,2,2), B21=gcoeff(B,2,1),B22=gcoeff(B,2,2);
  GEN M1 = Flx_mul(Flx_add(A11,A22, p), Flx_add(B11,B22, p), p);
  GEN M2 = Flx_mul(Flx_add(A21,A22, p), B11, p);
  GEN M3 = Flx_mul(A11, Flx_sub(B12,B22, p), p);
  GEN M4 = Flx_mul(A22, Flx_sub(B21,B11, p), p);
  GEN M5 = Flx_mul(Flx_add(A11,A12, p), B22, p);
  GEN M6 = Flx_mul(Flx_sub(A21,A11, p), Flx_add(B11,B12, p), p);
  GEN M7 = Flx_mul(Flx_sub(A12,A22, p), Flx_add(B21,B22, p), p);
  GEN T1 = Flx_add(M1,M4, p), T2 = Flx_sub(M7,M5, p);
  GEN T3 = Flx_sub(M1,M2, p), T4 = Flx_add(M3,M6, p);
  retmkmat2(mkcol2(Flx_add(T1,T2, p), Flx_add(M2,M4, p)),
            mkcol2(Flx_add(M3,M5, p), Flx_add(T3,T4, p)));
}

/* Return [0,1;1,-q]*M */
static GEN
Flx_FlxM_qmul(GEN q, GEN M, ulong p)
{
  GEN u, v, res = cgetg(3, t_MAT);
  u = Flx_sub(gcoeff(M,1,1), Flx_mul(gcoeff(M,2,1), q, p), p);
  gel(res,1) = mkcol2(gcoeff(M,2,1), u);
  v = Flx_sub(gcoeff(M,1,2), Flx_mul(gcoeff(M,2,2), q, p), p);
  gel(res,2) = mkcol2(gcoeff(M,2,2), v);
  return res;
}

static GEN
matid2_FlxM(long v)
{
  return mkmat2(mkcol2(pol1_Flx(v),pol0_Flx(v)),
                mkcol2(pol0_Flx(v),pol1_Flx(v)));
}

static GEN
Flx_halfgcd_split(GEN x, GEN y, ulong p)
{
  pari_sp av=avma;
  GEN R, S, V;
  GEN y1, r, q;
  long l = lgpol(x), n = l>>1, k;
  if (lgpol(y)<=n) return matid2_FlxM(x[1]);
  R = Flx_halfgcd(Flx_shift(x,-n),Flx_shift(y,-n),p);
  V = FlxM_Flx_mul2(R,x,y,p); y1 = gel(V,2);
  if (lgpol(y1)<=n) return gerepilecopy(av, R);
  q = Flx_divrem(gel(V,1), y1, p, &r);
  k = 2*n-degpol(y1);
  S = Flx_halfgcd(Flx_shift(y1,-k), Flx_shift(r,-k),p);
  return gerepileupto(av, FlxM_mul2(S,Flx_FlxM_qmul(q,R,p),p));
}

/* Return M in GL_2(Fl[X]) such that:
if [a',b']~=M*[a,b]~ then degpol(a')>= (lgpol(a)>>1) >degpol(b')
*/

static GEN
Flx_halfgcd_i(GEN x, GEN y, ulong p)
{
  if (!Flx_multhreshold(x,p,
                             Flx_HALFGCD_QUARTMULII_LIMIT,
                             Flx_HALFGCD_HALFMULII_LIMIT,
                             Flx_HALFGCD_MULII_LIMIT,
                             Flx_HALFGCD_MULII2_LIMIT,
                             Flx_HALFGCD_KARATSUBA_LIMIT))
    return Flx_halfgcd_basecase(x,y,p);
  return Flx_halfgcd_split(x,y,p);
}

GEN
Flx_halfgcd(GEN x, GEN y, ulong p)
{
  pari_sp av;
  GEN M,q,r;
  long lx=lgpol(x), ly=lgpol(y);
  if (!lx)
  {
      long v = x[1];
      retmkmat2(mkcol2(pol0_Flx(v),pol1_Flx(v)),
                mkcol2(pol1_Flx(v),pol0_Flx(v)));
  }
  if (ly < lx) return Flx_halfgcd_i(x,y,p);
  av = avma;
  q = Flx_divrem(y,x,p,&r);
  M = Flx_halfgcd_i(x,r,p);
  gcoeff(M,1,1) = Flx_sub(gcoeff(M,1,1), Flx_mul(q, gcoeff(M,1,2), p), p);
  gcoeff(M,2,1) = Flx_sub(gcoeff(M,2,1), Flx_mul(q, gcoeff(M,2,2), p), p);
  return gerepilecopy(av, M);
}

/*Do not garbage collect*/
static GEN
Flx_gcd_basecase(GEN a, GEN b, ulong p)
{
  pari_sp av = avma;
  ulong iter = 0;
  if (lg(b) > lg(a)) swap(a, b);
  while (lgpol(b))
  {
    GEN c = Flx_rem(a,b,p);
    iter++; a = b; b = c;
    if (gc_needed(av,2))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"Flx_gcd (d = %ld)",degpol(c));
      gerepileall(av,2, &a,&b);
    }
  }
  return iter < 2 ? Flx_copy(a) : a;
}

GEN
Flx_gcd(GEN x, GEN y, ulong p)
{
  pari_sp av = avma;
  if (!lgpol(x)) return Flx_copy(y);
  while (lg(y)>Flx_GCD_LIMIT)
  {
    GEN c;
    if (lgpol(y)<=(lgpol(x)>>1))
    {
      GEN r = Flx_rem(x, y, p);
      x = y; y = r;
    }
    c = FlxM_Flx_mul2(Flx_halfgcd(x,y, p), x, y, p);
    x = gel(c,1); y = gel(c,2);
    if (gc_needed(av,2))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"Flx_gcd (y = %ld)",degpol(y));
      gerepileall(av,2,&x,&y);
    }
  }
  return gerepileuptoleaf(av, Flx_gcd_basecase(x,y,p));
}

int
Flx_is_squarefree(GEN z, ulong p)
{
  pari_sp av = avma;
  GEN d = Flx_gcd(z, Flx_deriv(z,p) , p);
  long res= (degpol(d) == 0);
  avma = av; return res;
}

static long
Flx_is_smooth_squarefree(GEN f, long r, ulong p)
{
  pari_sp av = avma;
  long i;
  GEN sx = polx_Flx(f[1]), a = sx;
  for(i=1;;i++)
  {
    if (degpol(f)<=r) {avma = av; return 1;}
    a = Flxq_powu(Flx_rem(a,f,p), p, f, p);
    if (Flx_equal(a, sx)) {avma = av; return 1;}
    if (i==r) {avma = av; return 0;}
    f = Flx_div(f, Flx_gcd(Flx_sub(a,sx,p),f,p),p);
  }
}

static long
Flx_is_l_pow(GEN x, ulong p)
{
  ulong i, lx = lgpol(x);
  for (i=1; i<lx; i++)
    if (x[i+2] && i%p) return 0;
  return 1;
}

int
Flx_is_smooth(GEN g, long r, ulong p)
{
  GEN f = gen_0;
  while (1)
  {
    f = Flx_gcd(g, Flx_deriv(g, p), p);
    if (!Flx_is_smooth_squarefree(Flx_div(g, f, p), r, p))
      return 0;
    if (degpol(f)==0) return 1;
    g = Flx_is_l_pow(f,p) ? Flx_deflate(f, p): f;
  }
}

static GEN
Flx_extgcd_basecase(GEN a, GEN b, ulong p, GEN *ptu, GEN *ptv)
{
  pari_sp av=avma;
  GEN u,v,d,d1,v1;
  long vx = a[1];
  d = a; d1 = b;
  v = pol0_Flx(vx); v1 = pol1_Flx(vx);
  while (lgpol(d1))
  {
    GEN r, q = Flx_divrem(d,d1,p, &r);
    v = Flx_sub(v,Flx_mul(q,v1,p),p);
    u=v; v=v1; v1=u;
    u=r; d=d1; d1=u;
    if (gc_needed(av,2))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"Flx_extgcd (d = %ld)",degpol(d));
      gerepileall(av,5, &d,&d1,&u,&v,&v1);
    }
  }
  if (ptu) *ptu = Flx_div(Flx_sub(d, Flx_mul(b,v,p), p), a, p);
  *ptv = v; return d;
}

static GEN
Flx_extgcd_halfgcd(GEN x, GEN y, ulong p, GEN *ptu, GEN *ptv)
{
  pari_sp av=avma;
  GEN u,v,R = matid2_FlxM(x[1]);
  while (lg(y)>Flx_EXTGCD_LIMIT)
  {
    GEN M, c;
    if (lgpol(y)<=(lgpol(x)>>1))
    {
      GEN r, q = Flx_divrem(x, y, p, &r);
      x = y; y = r;
      R = Flx_FlxM_qmul(q, R, p);
    }
    M = Flx_halfgcd(x,y, p);
    c = FlxM_Flx_mul2(M, x,y, p);
    R = FlxM_mul2(M, R, p);
    x = gel(c,1); y = gel(c,2);
    gerepileall(av,3,&x,&y,&R);
  }
  y = Flx_extgcd_basecase(x,y,p,&u,&v);
  if (ptu) *ptu = Flx_addmulmul(u,v,gcoeff(R,1,1),gcoeff(R,2,1),p);
  *ptv = Flx_addmulmul(u,v,gcoeff(R,1,2),gcoeff(R,2,2),p);
  return y;
}

/* x and y in Z[X], return lift(gcd(x mod p, y mod p)). Set u and v st
 * ux + vy = gcd (mod p) */
GEN
Flx_extgcd(GEN x, GEN y, ulong p, GEN *ptu, GEN *ptv)
{
  GEN d;
  pari_sp ltop=avma;
  if (lg(y)>Flx_EXTGCD_LIMIT)
    d = Flx_extgcd_halfgcd(x, y, p, ptu, ptv);
  else
    d = Flx_extgcd_basecase(x, y, p, ptu, ptv);
  gerepileall(ltop,ptu?3:2,&d,ptv,ptu);
  return d;
}

ulong
Flx_resultant(GEN a, GEN b, ulong p)
{
  long da,db,dc,cnt;
  ulong lb, res = 1UL;
  pari_sp av;
  GEN c;

  if (lgpol(a)==0 || lgpol(b)==0) return 0;
  da = degpol(a);
  db = degpol(b);
  if (db > da)
  {
    swapspec(a,b, da,db);
    if (both_odd(da,db)) res = p-res;
  }
  else if (!da) return 1; /* = res * a[2] ^ db, since 0 <= db <= da = 0 */
  cnt = 0; av = avma;
  while (db)
  {
    lb = b[db+2];
    c = Flx_rem(a,b, p);
    a = b; b = c; dc = degpol(c);
    if (dc < 0) { avma = av; return 0; }

    if (both_odd(da,db)) res = p - res;
    if (lb != 1) res = Fl_mul(res, Fl_powu(lb, da - dc, p), p);
    if (++cnt == 100) { cnt = 0; gerepileall(av, 2, &a, &b); }
    da = db; /* = degpol(a) */
    db = dc; /* = degpol(b) */
  }
  avma = av; return Fl_mul(res, Fl_powu(b[2], da, p), p);
}

/* If resultant is 0, *ptU and *ptU are not set */
ulong
Flx_extresultant(GEN a, GEN b, ulong p, GEN *ptU, GEN *ptV)
{
  GEN z,q,u,v, x = a, y = b;
  ulong lb, res = 1UL;
  pari_sp av = avma;
  long dx, dy, dz;
  long vs=a[1];

  dx = degpol(x);
  dy = degpol(y);
  if (dy > dx)
  {
    swap(x,y); lswap(dx,dy); pswap(ptU, ptV);
    a = x; b = y;
    if (both_odd(dx,dy)) res = p-res;
  }
  /* dx <= dy */
  if (dx < 0) return 0;

  u = pol0_Flx(vs);
  v = pol1_Flx(vs); /* v = 1 */
  while (dy)
  { /* b u = x (a), b v = y (a) */
    lb = y[dy+2];
    q = Flx_divrem(x,y, p, &z);
    x = y; y = z; /* (x,y) = (y, x - q y) */
    dz = degpol(z); if (dz < 0) { avma = av; return 0; }
    z = Flx_sub(u, Flx_mul(q,v, p), p);
    u = v; v = z; /* (u,v) = (v, u - q v) */

    if (both_odd(dx,dy)) res = p - res;
    if (lb != 1) res = Fl_mul(res, Fl_powu(lb, dx-dz, p), p);
    dx = dy; /* = degpol(x) */
    dy = dz; /* = degpol(y) */
  }
  res = Fl_mul(res, Fl_powu(y[2], dx, p), p);
  lb = Fl_mul(res, Fl_inv(y[2],p), p);
  v = gerepileuptoleaf(av, Flx_Fl_mul(v, lb, p));
  av = avma;
  u = Flx_sub(Fl_to_Flx(res,vs), Flx_mul(b,v,p), p);
  u = gerepileuptoleaf(av, Flx_div(u,a,p)); /* = (res - b v) / a */
  *ptU = u;
  *ptV = v; return res;
}

ulong
Flx_eval_powers_pre(GEN x, GEN y, ulong p, ulong pi)
{
  ulong l0, l1, h0, h1, v1,  i = 1, lx = lg(x)-1;
  LOCAL_OVERFLOW;
  LOCAL_HIREMAINDER;
  x++;

  if (lx == 1)
    return 0;
  l1 = mulll(uel(x,i), uel(y,i)); h1 = hiremainder; v1 = 0;
  while (++i < lx) {
    l0 = mulll(uel(x,i), uel(y,i)); h0 = hiremainder;
    l1 = addll(l0, l1); h1 = addllx(h0, h1); v1 += overflow;
  }
  if (v1 == 0) return remll_pre(h1, l1, p, pi);
  else return remlll_pre(v1, h1, l1, p, pi);
}

INLINE ulong
Flx_eval_pre_i(GEN x, ulong y, ulong p, ulong pi)
{
  ulong p1;
  long i=lg(x)-1;
  if (i<=2)
    return (i==2)? x[2]: 0;
  p1 = x[i];
  for (i--; i>=2; i--)
    p1 = Fl_addmul_pre(uel(x, i), p1, y, p, pi);
  return p1;
}

ulong
Flx_eval_pre(GEN x, ulong y, ulong p, ulong pi)
{
  if (degpol(x) > 15)
  {
    pari_sp av = avma;
    GEN v = Fl_powers_pre(y, degpol(x), p, pi);
    ulong r =  Flx_eval_powers_pre(x, v, p, pi);
    avma = av;
    return r;
  }
  else
    return Flx_eval_pre_i(x, y, p, pi);
}

ulong
Flx_eval(GEN x, ulong y, ulong p)
{
  return Flx_eval_pre(x, y, p, get_Fl_red(p));
}

ulong
Flv_prod_pre(GEN x, ulong p, ulong pi)
{
  pari_sp ltop = avma;
  GEN v;
  long i,k,lx = lg(x);
  ulong r;
  if (lx == 1) return 1UL;
  if (lx == 2) return uel(x,1);
  v = cgetg(1+(lx << 1), t_VECSMALL);
  k = 1;
  for (i=1; i<lx-1; i+=2)
    uel(v,k++) = Fl_mul_pre(uel(x,i), uel(x,i+1), p, pi);
  if (i < lx) uel(v,k++) = uel(x,i);
  while (k > 2)
  {
    lx = k; k = 1;
    for (i=1; i<lx-1; i+=2)
      uel(v,k++) = Fl_mul_pre(uel(v,i), uel(v,i+1), p, pi);
    if (i < lx) uel(v,k++) = uel(v,i);
  }
  r = uel(v,1);
  avma = ltop; return r;
}

ulong
Flv_prod(GEN v, ulong p)
{
  return Flv_prod_pre(v, p, get_Fl_red(p));
}

GEN
FlxV_prod(GEN V, ulong p)
{
  struct _Flxq D;
  D.T = NULL; D.aut = NULL; D.p = p;
  return gen_product(V, (void *)&D, &_Flx_mul);
}

/* compute prod (x - a[i]) */
GEN
Flv_roots_to_pol(GEN a, ulong p, long vs)
{
  struct _Flxq D;
  long i,k,lx = lg(a);
  GEN p1;
  if (lx == 1) return pol1_Flx(vs);
  p1 = cgetg(lx, t_VEC);
  for (k=1,i=1; i<lx-1; i+=2)
    gel(p1,k++) = mkvecsmall4(vs, Fl_mul(a[i], a[i+1], p),
                              Fl_neg(Fl_add(a[i],a[i+1],p),p), 1);
  if (i < lx)
    gel(p1,k++) = mkvecsmall3(vs, Fl_neg(a[i],p), 1);
  D.T = NULL; D.aut = NULL; D.p = p;
  setlg(p1, k); return gen_product(p1, (void *)&D, _Flx_mul);
}

INLINE void
Flv_inv_pre_indir(GEN w, GEN v, ulong p, ulong pi)
{
  pari_sp av = avma;
  GEN c;
  register ulong u;
  register long n = lg(w), i;

  if (n == 1)
    return;

  c = cgetg(n, t_VECSMALL);
  c[1] = w[1];
  for (i = 2; i < n; ++i)
    c[i] = Fl_mul_pre(w[i], c[i - 1], p, pi);

  i = n - 1;
  u = Fl_inv(c[i], p);
  for ( ; i > 1; --i) {
    ulong t = Fl_mul_pre(u, c[i - 1], p, pi);
    u = Fl_mul_pre(u, w[i], p, pi);
    v[i] = t;
  }
  v[1] = u;
  avma = av;
}

void
Flv_inv_pre_inplace(GEN v, ulong p, ulong pi)
{
  Flv_inv_pre_indir(v, v, p, pi);
}

GEN
Flv_inv_pre(GEN w, ulong p, ulong pi)
{
  GEN v = cgetg(lg(w), t_VECSMALL);
  Flv_inv_pre_indir(w, v, p, pi);
  return v;
}

INLINE void
Flv_inv_indir(GEN w, GEN v, ulong p)
{
  pari_sp av = avma;
  GEN c;
  register ulong u;
  register long n = lg(w), i;

  if (n == 1)
    return;

  c = cgetg(n, t_VECSMALL);
  c[1] = w[1];
  for (i = 2; i < n; ++i)
    c[i] = Fl_mul(w[i], c[i - 1], p);

  i = n - 1;
  u = Fl_inv(c[i], p);
  for ( ; i > 1; --i) {
    ulong t = Fl_mul(u, c[i - 1], p);
    u = Fl_mul(u, w[i], p);
    v[i] = t;
  }
  v[1] = u;
  avma = av;
}

void
Flv_inv_inplace(GEN v, ulong p)
{
  if (SMALL_ULONG(p))
    Flv_inv_indir(v, v, p);
  else
    Flv_inv_pre_indir(v, v, p, get_Fl_red(p));
}

GEN
Flv_inv(GEN w, ulong p)
{
  GEN v = cgetg(lg(w), t_VECSMALL);
  if (SMALL_ULONG(p))
    Flv_inv_indir(w, v, p);
  else
    Flv_inv_pre_indir(w, v, p, get_Fl_red(p));
  return v;
}

GEN
Flx_div_by_X_x(GEN a, ulong x, ulong p, ulong *rem)
{
  long l = lg(a), i;
  GEN a0, z0;
  GEN z = cgetg(l-1,t_VECSMALL);
  z[1] = a[1];
  a0 = a + l-1;
  z0 = z + l-2; *z0 = *a0--;
  if (SMALL_ULONG(p))
  {
    for (i=l-3; i>1; i--) /* z[i] = (a[i+1] + x*z[i+1]) % p */
    {
      ulong t = (*a0-- + x *  *z0--) % p;
      *z0 = (long)t;
    }
    if (rem) *rem = (*a0 + x *  *z0) % p;
  }
  else
  {
    for (i=l-3; i>1; i--)
    {
      ulong t = Fl_add((ulong)*a0--, Fl_mul(x, *z0--, p), p);
      *z0 = (long)t;
    }
    if (rem) *rem = Fl_add((ulong)*a0, Fl_mul(x, *z0, p), p);
  }
  return z;
}

/* xa, ya = t_VECSMALL */
static GEN
Flv_producttree(GEN xa, GEN s, ulong p, long vs)
{
  long n = lg(xa)-1;
  long m = n==1 ? 1: expu(n-1)+1;
  long i, j, k, ls = lg(s);
  GEN T = cgetg(m+1, t_VEC);
  GEN t = cgetg(ls, t_VEC);
  for (j=1, k=1; j<ls; k+=s[j++])
    gel(t, j) = s[j] == 1 ?
             mkvecsmall3(vs, Fl_neg(xa[k], p), 1):
             mkvecsmall4(vs, Fl_mul(xa[k], xa[k+1], p),
                 Fl_neg(Fl_add(xa[k],xa[k+1],p),p), 1);
  gel(T,1) = t;
  for (i=2; i<=m; i++)
  {
    GEN u = gel(T, i-1);
    long n = lg(u)-1;
    GEN t = cgetg(((n+1)>>1)+1, t_VEC);
    for (j=1, k=1; k<n; j++, k+=2)
      gel(t, j) = Flx_mul(gel(u, k), gel(u, k+1), p);
    gel(T, i) = t;
  }
  return T;
}

static GEN
Flx_Flv_multieval_tree(GEN P, GEN xa, GEN T, ulong p)
{
  long i,j,k;
  long m = lg(T)-1;
  GEN t;
  GEN R = cgetg(lg(xa), t_VECSMALL);
  GEN Tp = cgetg(m+1, t_VEC);
  gel(Tp, m) = mkvec(P);
  for (i=m-1; i>=1; i--)
  {
    GEN u = gel(T, i);
    GEN v = gel(Tp, i+1);
    long n = lg(u)-1;
    t = cgetg(n+1, t_VEC);
    for (j=1, k=1; k<n; j++, k+=2)
    {
      gel(t, k)   = Flx_rem(gel(v, j), gel(u, k), p);
      gel(t, k+1) = Flx_rem(gel(v, j), gel(u, k+1), p);
    }
    gel(Tp, i) = t;
  }
  {
    GEN u = gel(T, i+1);
    GEN v = gel(Tp, i+1);
    long n = lg(u)-1;
    for (j=1, k=1; j<=n; j++)
    {
      long c, d = degpol(gel(u,j));
      for (c=1; c<=d; c++, k++)
        R[k] = Flx_eval(gel(v, j), xa[k], p);
    }
    avma = (pari_sp) R;
    return R;
  }
}

static GEN
FlvV_polint_tree(GEN T, GEN R, GEN s, GEN xa, GEN ya, ulong p, long vs)
{
  pari_sp av = avma;
  long m = lg(T)-1;
  long i, j, k, ls = lg(s);
  GEN Tp = cgetg(m+1, t_VEC);
  GEN t = cgetg(ls, t_VEC);
  for (j=1, k=1; j<ls; k+=s[j++])
    if (s[j]==2)
    {
      ulong a = Fl_mul(ya[k], R[k], p);
      ulong b = Fl_mul(ya[k+1], R[k+1], p);
      gel(t, j) = mkvecsmall3(vs, Fl_neg(Fl_add(Fl_mul(xa[k], b, p ),
                  Fl_mul(xa[k+1], a, p), p), p), Fl_add(a, b, p));
      gel(t, j) = Flx_renormalize(gel(t, j), 4);
    }
    else
      gel(t, j) = Fl_to_Flx(Fl_mul(ya[k], R[k], p), vs);
  gel(Tp, 1) = t;
  for (i=2; i<=m; i++)
  {
    GEN u = gel(T, i-1);
    GEN t = cgetg(lg(gel(T,i)), t_VEC);
    GEN v = gel(Tp, i-1);
    long n = lg(v)-1;
    for (j=1, k=1; k<n; j++, k+=2)
      gel(t, j) = Flx_add(Flx_mul(gel(u, k), gel(v, k+1), p),
                          Flx_mul(gel(u, k+1), gel(v, k), p), p);
    gel(Tp, i) = t;
  }
  return gerepileuptoleaf(av, gmael(Tp,m,1));
}

GEN
Flx_Flv_multieval(GEN P, GEN xa, ulong p)
{
  pari_sp av = avma;
  GEN s = producttree_scheme(lg(xa)-1);
  GEN T = Flv_producttree(xa, s, p, P[1]);
  return gerepileuptoleaf(av, Flx_Flv_multieval_tree(P, xa, T, p));
}

GEN
Flv_polint(GEN xa, GEN ya, ulong p, long vs)
{
  pari_sp av = avma;
  GEN s = producttree_scheme(lg(xa)-1);
  GEN T = Flv_producttree(xa, s, p, vs);
  long m = lg(T)-1;
  GEN P = Flx_deriv(gmael(T, m, 1), p);
  GEN R = Flv_inv(Flx_Flv_multieval_tree(P, xa, T, p), p);
  return gerepileuptoleaf(av, FlvV_polint_tree(T, R, s, xa, ya, p, vs));
}

GEN
Flv_Flm_polint(GEN xa, GEN ya, ulong p, long vs)
{
  pari_sp av = avma;
  GEN s = producttree_scheme(lg(xa)-1);
  GEN T = Flv_producttree(xa, s, p, vs);
  long i, m = lg(T)-1, l = lg(ya)-1;
  GEN P = Flx_deriv(gmael(T, m, 1), p);
  GEN R = Flv_inv(Flx_Flv_multieval_tree(P, xa, T, p), p);
  GEN M = cgetg(l+1, t_VEC);
  for (i=1; i<=l; i++)
    gel(M,i) = FlvV_polint_tree(T, R, s, xa, gel(ya,i), p, vs);
  return gerepileupto(av, M);
}

GEN
Flv_invVandermonde(GEN L, ulong den, ulong p)
{
  pari_sp av = avma;
  long i, n = lg(L);
  GEN M, R;
  GEN s = producttree_scheme(n-1);
  GEN tree = Flv_producttree(L, s, p, 0);
  long m = lg(tree)-1;
  GEN T = gmael(tree, m, 1);
  R = Flv_inv(Flx_Flv_multieval_tree(Flx_deriv(T, p), L, tree, p), p);
  if (den!=1) R = Flv_Fl_mul(R, den, p);
  M = cgetg(n, t_MAT);
  for (i = 1; i < n; i++)
  {
    GEN P = Flx_Fl_mul(Flx_div_by_X_x(T, uel(L,i), p, NULL), uel(R,i), p);
    gel(M,i) = Flx_to_Flv(P, n-1);
  }
  return gerepilecopy(av, M);
}

/***********************************************************************/
/**                                                                   **/
/**                               Flxq                                **/
/**                                                                   **/
/***********************************************************************/
/* Flxq objects are defined as follows:
   They are Flx modulo another Flx called q.
*/

/* Product of y and x in Z/pZ[X]/(T), as t_VECSMALL. */
GEN
Flxq_mul(GEN x,GEN y,GEN T,ulong p)
{
  return Flx_rem(Flx_mul(x,y,p),T,p);
}

/* Square of y in Z/pZ[X]/(T), as t_VECSMALL. */
GEN
Flxq_sqr(GEN x,GEN T,ulong p)
{
  return Flx_rem(Flx_sqr(x,p),T,p);
}

static GEN
_Flxq_red(void *E, GEN x)
{ struct _Flxq *s = (struct _Flxq *)E;
  return Flx_rem(x, s->T, s->p); }
static GEN
_Flx_sub(void *E, GEN x, GEN y)
{ struct _Flxq *s = (struct _Flxq *)E;
  return Flx_sub(x,y,s->p); }
static GEN
_Flxq_sqr(void *data, GEN x)
{
  struct _Flxq *D = (struct _Flxq*)data;
  return Flxq_sqr(x, D->T, D->p);
}
static GEN
_Flxq_mul(void *data, GEN x, GEN y)
{
  struct _Flxq *D = (struct _Flxq*)data;
  return Flxq_mul(x,y, D->T, D->p);
}
static GEN
_Flxq_one(void *data)
{
  struct _Flxq *D = (struct _Flxq*)data;
  return pol1_Flx(get_Flx_var(D->T));
}
static GEN
_Flxq_zero(void *data)
{
  struct _Flxq *D = (struct _Flxq*)data;
  return pol0_Flx(get_Flx_var(D->T));
}
static GEN
_Flxq_cmul(void *data, GEN P, long a, GEN x)
{
  struct _Flxq *D = (struct _Flxq*)data;
  return Flx_Fl_mul(x, P[a+2], D->p);
}

/* n-Power of x in Z/pZ[X]/(T), as t_VECSMALL. */
GEN
Flxq_powu(GEN x, ulong n, GEN T, ulong p)
{
  pari_sp av = avma;
  struct _Flxq D;
  GEN y;
  switch(n)
  {
    case 0: return pol1_Flx(T[1]);
    case 1: return Flx_copy(x);
    case 2: return Flxq_sqr(x, T, p);
  }
  D.T = Flx_get_red(T, p); D.p = p;
  y = gen_powu_i(x, n, (void*)&D, &_Flxq_sqr, &_Flxq_mul);
  return gerepileuptoleaf(av, y);
}

/* n-Power of x in Z/pZ[X]/(T), as t_VECSMALL. */
GEN
Flxq_pow(GEN x, GEN n, GEN T, ulong p)
{
  pari_sp av = avma;
  struct _Flxq D;
  GEN y;
  long s = signe(n);
  if (!s) return pol1_Flx(get_Flx_var(T));
  if (s < 0)
    x = Flxq_inv(x,T,p);
  if (is_pm1(n)) return s < 0 ? x : Flx_copy(x);
  D.T = Flx_get_red(T, p); D.p = p;
  y = gen_pow_i(x, n, (void*)&D, &_Flxq_sqr, &_Flxq_mul);
  return gerepileuptoleaf(av, y);
}

GEN
Flxq_pow_init(GEN x, GEN n, long k,  GEN T, ulong p)
{
  struct _Flxq D;
  D.T = Flx_get_red(T, p); D.p = p;
  return gen_pow_init(x, n, k, (void*)&D, &_Flxq_sqr, &_Flxq_mul);
}

GEN
Flxq_pow_table(GEN R, GEN n, GEN T, ulong p)
{
  struct _Flxq D;
  D.T = Flx_get_red(T, p); D.p = p;
  return gen_pow_table(R, n, (void*)&D, &_Flxq_one, &_Flxq_mul);
}

/* Inverse of x in Z/lZ[X]/(T) or NULL if inverse doesn't exist
 * not stack clean.
 */
GEN
Flxq_invsafe(GEN x, GEN T, ulong p)
{
  GEN V, z = Flx_extgcd(get_Flx_mod(T), x, p, NULL, &V);
  ulong iz;
  if (degpol(z)) return NULL;
  iz = Fl_inv (uel(z,2), p);
  return Flx_Fl_mul(V, iz, p);
}

GEN
Flxq_inv(GEN x,GEN T,ulong p)
{
  pari_sp av=avma;
  GEN U = Flxq_invsafe(x, T, p);
  if (!U) pari_err_INV("Flxq_inv",Flx_to_ZX(x));
  return gerepileuptoleaf(av, U);
}

GEN
Flxq_div(GEN x,GEN y,GEN T,ulong p)
{
  pari_sp av = avma;
  return gerepileuptoleaf(av, Flxq_mul(x,Flxq_inv(y,T,p),T,p));
}

GEN
Flxq_powers(GEN x, long l, GEN T, ulong p)
{
  struct _Flxq D;
  int use_sqr = 2*degpol(x) >= get_Flx_degree(T);
  D.T = Flx_get_red(T, p); D.p = p;
  return gen_powers(x, l, use_sqr, (void*)&D, &_Flxq_sqr, &_Flxq_mul, &_Flxq_one);
}

GEN
Flxq_matrix_pow(GEN y, long n, long m, GEN P, ulong l)
{
  return FlxV_to_Flm(Flxq_powers(y,m-1,P,l),n);
}

GEN
Flx_Frobenius(GEN T, ulong p)
{
  return Flxq_powu(polx_Flx(get_Flx_var(T)), p, T, p);
}

GEN
Flx_matFrobenius(GEN T, ulong p)
{
  long n = get_Flx_degree(T);
  return Flxq_matrix_pow(Flx_Frobenius(T, p), n, n, T, p);
}

static struct bb_algebra Flxq_algebra = { _Flxq_red, _Flx_add, _Flx_sub,
              _Flxq_mul, _Flxq_sqr, _Flxq_one, _Flxq_zero};

GEN
Flx_FlxqV_eval(GEN Q, GEN x, GEN T, ulong p)
{
  struct _Flxq D;
  D.T = Flx_get_red(T, p); D.p=p;
  return gen_bkeval_powers(Q,degpol(Q),x,(void*)&D,&Flxq_algebra,_Flxq_cmul);
}

GEN
Flx_Flxq_eval(GEN Q, GEN x, GEN T, ulong p)
{
  int use_sqr = 2*degpol(x) >= get_Flx_degree(T);
  struct _Flxq D;
  D.T = Flx_get_red(T, p); D.p=p;
  return gen_bkeval(Q,degpol(Q),x,use_sqr,(void*)&D,&Flxq_algebra,_Flxq_cmul);
}

static GEN
Flxq_autpow_sqr(void *E, GEN x)
{
  struct _Flxq *D = (struct _Flxq*)E;
  return Flx_Flxq_eval(x, x, D->T, D->p);
}
static GEN
Flxq_autpow_mul(void *E, GEN x, GEN y)
{
  struct _Flxq *D = (struct _Flxq*)E;
  return Flx_Flxq_eval(x, y, D->T, D->p);
}

GEN
Flxq_autpow(GEN x, ulong n, GEN T, ulong p)
{
  struct _Flxq D;
  if (n==0) return Flx_rem(polx_Flx(x[1]), T, p);
  if (n==1) return Flx_rem(x, T, p);
  D.T = Flx_get_red(T, p); D.p = p;
  return gen_powu(x,n,(void*)&D,Flxq_autpow_sqr,Flxq_autpow_mul);
}

static GEN
Flxq_autsum_mul(void *E, GEN x, GEN y)
{
  struct _Flxq *D = (struct _Flxq*)E;
  GEN T = D->T;
  ulong p = D->p;
  GEN phi1 = gel(x,1), a1 = gel(x,2);
  GEN phi2 = gel(y,1), a2 = gel(y,2);
  ulong d = brent_kung_optpow(maxss(degpol(phi1),degpol(a1)),2,1);
  GEN V2 = Flxq_powers(phi2, d, T, p);
  GEN phi3 = Flx_FlxqV_eval(phi1, V2, T, p);
  GEN aphi = Flx_FlxqV_eval(a1, V2, T, p);
  GEN a3 = Flxq_mul(aphi, a2, T, p);
  return mkvec2(phi3, a3);
}
static GEN
Flxq_autsum_sqr(void *E, GEN x)
{ return Flxq_autsum_mul(E, x, x); }

GEN
Flxq_autsum(GEN x, ulong n, GEN T, ulong p)
{
  struct _Flxq D;
  D.T = Flx_get_red(T, p); D.p = p;
  return gen_powu(x,n,(void*)&D,Flxq_autsum_sqr,Flxq_autsum_mul);
}

static GEN
Flxq_auttrace_mul(void *E, GEN x, GEN y)
{
  struct _Flxq *D = (struct _Flxq*)E;
  GEN T = D->T;
  ulong p = D->p;
  GEN phi1 = gel(x,1), a1 = gel(x,2);
  GEN phi2 = gel(y,1), a2 = gel(y,2);
  ulong d = brent_kung_optpow(maxss(degpol(phi1),degpol(a1)),2,1);
  GEN V1 = Flxq_powers(phi1, d, T, p);
  GEN phi3 = Flx_FlxqV_eval(phi2, V1, T, p);
  GEN aphi = Flx_FlxqV_eval(a2, V1, T, p);
  GEN a3 = Flx_add(a1, aphi, p);
  return mkvec2(phi3, a3);
}

static GEN
Flxq_auttrace_sqr(void *E, GEN x)
{ return Flxq_auttrace_mul(E, x, x); }

GEN
Flxq_auttrace(GEN x, ulong n, GEN T, ulong p)
{
  struct _Flxq D;
  D.T = Flx_get_red(T, p); D.p = p;
  return gen_powu(x,n,(void*)&D,Flxq_auttrace_sqr,Flxq_auttrace_mul);
}

static long
bounded_order(ulong p, GEN b, long k)
{
  long i;
  GEN a=modii(utoi(p),b);
  for(i=1;i<k;i++)
  {
    if (equali1(a))
      return i;
    a = modii(muliu(a,p),b);
  }
  return 0;
}

/*
  n = (p^d-a)\b
  b = bb*p^vb
  p^k = 1 [bb]
  d = m*k+r+vb
  u = (p^k-1)/bb;
  v = (p^(r+vb)-a)/b;
  w = (p^(m*k)-1)/(p^k-1)
  n = p^r*w*u+v
  w*u = p^vb*(p^(m*k)-1)/b
  n = p^(r+vb)*(p^(m*k)-1)/b+(p^(r+vb)-a)/b
*/

static GEN
Flxq_pow_Frobenius(GEN x, GEN n, GEN aut, GEN T, ulong p)
{
  pari_sp av=avma;
  long d = get_Flx_degree(T);
  GEN an = absi_shallow(n), z, q;
  if (abscmpiu(an,p)<0 || cmpis(an,d)<=0) return Flxq_pow(x, n, T, p);
  q = powuu(p, d);
  if (dvdii(q, n))
  {
    long vn = logint(an,utoi(p));
    GEN autvn = vn==1 ? aut: Flxq_autpow(aut,vn,T,p);
    z = Flx_Flxq_eval(x,autvn,T,p);
  } else
  {
    GEN b = diviiround(q, an), a = subii(q, mulii(an,b));
    GEN bb, u, v, autk;
    long vb = Z_lvalrem(b,p,&bb);
    long m, r, k = is_pm1(bb) ? 1 : bounded_order(p,bb,d);
    if (!k || d-vb<k) return Flxq_pow(x,n, T, p);
    m = (d-vb)/k; r = (d-vb)%k;
    u = diviiexact(subiu(powuu(p,k),1),bb);
    v = diviiexact(subii(powuu(p,r+vb),a),b);
    autk = k==1 ? aut: Flxq_autpow(aut,k,T,p);
    if (r)
    {
      GEN autr = r==1 ? aut: Flxq_autpow(aut,r,T,p);
      z = Flx_Flxq_eval(x,autr,T,p);
    } else z = x;
    if (m > 1) z = gel(Flxq_autsum(mkvec2(autk, z), m, T, p), 2);
    if (!is_pm1(u)) z = Flxq_pow(z, u, T, p);
    if (signe(v)) z = Flxq_mul(z, Flxq_pow(x, v, T, p), T, p);
  }
  return gerepileupto(av,signe(n)>0 ? z : Flxq_inv(z,T,p));
}

static GEN
_Flxq_pow(void *data, GEN x, GEN n)
{
  struct _Flxq *D = (struct _Flxq*)data;
  return Flxq_pow_Frobenius(x, n, D->aut, D->T, D->p);
}

static GEN
_Flxq_rand(void *data)
{
  pari_sp av=avma;
  struct _Flxq *D = (struct _Flxq*)data;
  GEN z;
  do
  {
    avma = av;
    z = random_Flx(get_Flx_degree(D->T),get_Flx_var(D->T),D->p);
  } while (lgpol(z)==0);
  return z;
}

/* discrete log in FpXQ for a in Fp^*, g in FpXQ^* of order ord */
static GEN
Fl_Flxq_log(ulong a, GEN g, GEN o, GEN T, ulong p)
{
  pari_sp av = avma;
  GEN q,n_q,ord,ordp, op;

  if (a == 1UL) return gen_0;
  /* p > 2 */

  ordp = utoi(p - 1);
  ord  = get_arith_Z(o);
  if (!ord) ord = T? subiu(powuu(p, get_FpX_degree(T)), 1): ordp;
  if (a == p - 1) /* -1 */
    return gerepileuptoint(av, shifti(ord,-1));
  ordp = gcdii(ordp, ord);
  op = typ(o)==t_MAT ? famat_Z_gcd(o, ordp) : ordp;

  q = NULL;
  if (T)
  { /* we want < g > = Fp^* */
    if (!equalii(ord,ordp)) {
      q = diviiexact(ord,ordp);
      g = Flxq_pow(g,q,T,p);
    }
  }
  n_q = Fp_log(utoi(a), utoi(uel(g,2)), op, utoi(p));
  if (lg(n_q)==1) return gerepileuptoleaf(av, n_q);
  if (q) n_q = mulii(q, n_q);
  return gerepileuptoint(av, n_q);
}

static GEN
Flxq_easylog(void* E, GEN a, GEN g, GEN ord)
{
  struct _Flxq *f = (struct _Flxq *)E;
  GEN T = f->T;
  ulong p = f->p;
  long d = get_Flx_degree(T);
  if (Flx_equal1(a)) return gen_0;
  if (Flx_equal(a,g)) return gen_1;
  if (!degpol(a))
    return Fl_Flxq_log(uel(a,2), g, ord, T, p);
  if (typ(ord)!=t_INT || d <= 4 || d == 6 || abscmpiu(ord,1UL<<27)<0)
    return NULL;
  return Flxq_log_index(a, g, ord, T, p);
}

int
Flx_equal(GEN V, GEN W)
{
  long l = lg(V);
  if (lg(W) != l) return 0;
  while (--l > 1) /* do not compare variables, V[1] */
    if (V[l] != W[l]) return 0;
  return 1;
}

static const struct bb_group Flxq_star={_Flxq_mul,_Flxq_pow,_Flxq_rand,hash_GEN,Flx_equal,Flx_equal1,Flxq_easylog};

const struct bb_group *
get_Flxq_star(void **E, GEN T, ulong p)
{
  struct _Flxq *e = (struct _Flxq *) stack_malloc(sizeof(struct _Flxq));
  e->T = T; e->p  = p; e->aut =  Flx_Frobenius(T, p);
  *E = (void*)e; return &Flxq_star;
}

GEN
Flxq_order(GEN a, GEN ord, GEN T, ulong p)
{
  void *E;
  const struct bb_group *S = get_Flxq_star(&E,T,p);
  return gen_order(a,ord,E,S);
}

GEN
Flxq_log(GEN a, GEN g, GEN ord, GEN T, ulong p)
{
  void *E;
  pari_sp av = avma;
  const struct bb_group *S = get_Flxq_star(&E,T,p);
  GEN v = get_arith_ZZM(ord), F = gmael(v,2,1);
  if (Flxq_log_use_index(gel(F,lg(F)-1), T, p))
    v = mkvec2(gel(v, 1), ZM_famat_limit(gel(v, 2), int2n(27)));
  return gerepileuptoleaf(av, gen_PH_log(a, g, v, E, S));
}

GEN
Flxq_sqrtn(GEN a, GEN n, GEN T, ulong p, GEN *zeta)
{
  if (!lgpol(a))
  {
    if (signe(n) < 0) pari_err_INV("Flxq_sqrtn",a);
    if (zeta)
      *zeta=pol1_Flx(get_Flx_var(T));
    return pol0_Flx(get_Flx_var(T));
  }
  else
  {
    void *E;
    pari_sp av = avma;
    const struct bb_group *S = get_Flxq_star(&E,T,p);
    GEN o = subiu(powuu(p,get_Flx_degree(T)), 1);
    GEN s = gen_Shanks_sqrtn(a,n,o,zeta,E,S);
    if (s) gerepileall(av, zeta?2:1, &s, zeta);
    return s;
  }
}

GEN
Flxq_sqrt(GEN a, GEN T, ulong p)
{
  return Flxq_sqrtn(a, gen_2, T, p, NULL);
}

/* assume T irreducible mod p */
int
Flxq_issquare(GEN x, GEN T, ulong p)
{
  if (lgpol(x) == 0 || p == 2) return 1;
  return krouu(Flxq_norm(x,T,p), p) == 1;
}

/* assume T irreducible mod p */
int
Flxq_is2npower(GEN x, long n, GEN T, ulong p)
{
  pari_sp av;
  GEN m;
  int z;
  if (n==1) return Flxq_issquare(x, T, p);
  if (lgpol(x) == 0 || p == 2) return 1;
  av = avma;
  m = shifti(subiu(powuu(p, get_Flx_degree(T)), 1), -n);
  z = Flx_equal1(Flxq_pow(x, m, T, p));
  avma = av; return z;
}

GEN
Flxq_lroot_fast(GEN a, GEN sqx, GEN T, long p)
{
  pari_sp av=avma;
  GEN A = Flx_splitting(a,p);
  return gerepileuptoleaf(av, FlxqV_dotproduct(A,sqx,T,p));
}

GEN
Flxq_lroot(GEN a, GEN T, long p)
{
  pari_sp av=avma;
  long n = get_Flx_degree(T), d = degpol(a);
  GEN sqx, V;
  if (n==1) return leafcopy(a);
  if (n==2) return Flxq_powu(a, p, T, p);
  sqx = Flxq_autpow(Flx_Frobenius(T, p), n-1, T, p);
  if (d==1 && a[2]==0 && a[3]==1) return gerepileuptoleaf(av, sqx);
  if (d>=p)
  {
    V = Flxq_powers(sqx,p-1,T,p);
    return gerepileuptoleaf(av, Flxq_lroot_fast(a,V,T,p));
  } else
    return gerepileuptoleaf(av, Flx_Flxq_eval(a,sqx,T,p));
}

ulong
Flxq_norm(GEN x, GEN TB, ulong p)
{
  GEN T = get_Flx_mod(TB);
  ulong y = Flx_resultant(T, x, p);
  ulong L = Flx_lead(T);
  if ( L==1 || lgpol(x)==0) return y;
  return Fl_div(y, Fl_powu(L, (ulong)degpol(x), p), p);
}

ulong
Flxq_trace(GEN x, GEN TB, ulong p)
{
  pari_sp av = avma;
  ulong t;
  GEN T = get_Flx_mod(TB);
  long n = degpol(T)-1;
  GEN z = Flxq_mul(x, Flx_deriv(T, p), TB, p);
  t = degpol(z)<n ? 0 : Fl_div(z[2+n],T[3+n],p);
  avma=av;
  return t;
}

/*x must be reduced*/
GEN
Flxq_charpoly(GEN x, GEN TB, ulong p)
{
  pari_sp ltop=avma;
  GEN T = get_Flx_mod(TB);
  long vs = evalvarn(fetch_var());
  GEN xm1 = deg1pol_shallow(pol1_Flx(x[1]),Flx_neg(x,p),vs);
  GEN r = Flx_FlxY_resultant(T, xm1, p);
  r[1] = x[1];
  (void)delete_var(); return gerepileupto(ltop, r);
}

/* Computing minimal polynomial :                         */
/* cf Shoup 'Efficient Computation of Minimal Polynomials */
/*          in Algebraic Extensions of Finite Fields'     */

GEN
Flxn_mul(GEN a, GEN b, long n, ulong p)
{
  GEN c = Flx_mul(a, b, p);
  return vecsmall_shorten(c, minss(lg(c)-1,n+1));
}

/* Let v a linear form, return the linear form z->v(tau*z)
   that is, v*(M_tau) */

static GEN
Flxq_transmul_init(GEN tau, GEN T, ulong p)
{
  GEN bht;
  GEN h, Tp = get_Flx_red(T, &h);
  long n = degpol(Tp), vT = Tp[1];
  GEN ft = Flx_recipspec(Tp+2, n+1, n+1);
  GEN bt = Flx_recipspec(tau+2, lgpol(tau), n);
  ft[1] = vT; bt[1] = vT;
  if (h)
    bht = Flxn_mul(bt, h, n-1, p);
  else
  {
    GEN bh = Flx_div(Flx_shift(tau, n-1), T, p);
    bht = Flx_recipspec(bh+2, lgpol(bh), n-1);
    bht[1] = vT;
  }
  return mkvec3(bt, bht, ft);
}

static GEN
Flxq_transmul(GEN tau, GEN a, long n, ulong p)
{
  pari_sp ltop = avma;
  GEN t1, t2, t3, vec;
  GEN bt = gel(tau, 1), bht = gel(tau, 2), ft = gel(tau, 3);
  if (lgpol(a)==0) return pol0_Flx(a[1]);
  t2  = Flx_shift(Flx_mul(bt, a, p),1-n);
  if (lgpol(bht)==0) return gerepileuptoleaf(ltop, t2);
  t1  = Flx_shift(Flx_mul(ft, a, p),-n);
  t3  = Flxn_mul(t1, bht, n-1, p);
  vec = Flx_sub(t2, Flx_shift(t3, 1), p);
  return gerepileuptoleaf(ltop, vec);
}

GEN
Flxq_minpoly(GEN x, GEN T, ulong p)
{
  pari_sp ltop = avma;
  long vT = get_Flx_var(T), n = get_Flx_degree(T);
  GEN v_x;
  GEN g = pol1_Flx(vT), tau = pol1_Flx(vT);
  T = Flx_get_red(T, p);
  v_x = Flxq_powers(x, usqrt(2*n), T, p);
  while (lgpol(tau) != 0)
  {
    long i, j, m, k1;
    GEN M, v, tr;
    GEN g_prime, c;
    if (degpol(g) == n) { tau = pol1_Flx(vT); g = pol1_Flx(vT); }
    v = random_Flx(n, vT, p);
    tr = Flxq_transmul_init(tau, T, p);
    v = Flxq_transmul(tr, v, n, p);
    m = 2*(n-degpol(g));
    k1 = usqrt(m);
    tr = Flxq_transmul_init(gel(v_x,k1+1), T, p);
    c = cgetg(m+2,t_VECSMALL);
    c[1] = T[1];
    for (i=0; i<m; i+=k1)
    {
      long mj = minss(m-i, k1);
      for (j=0; j<mj; j++)
        uel(c,m+1-(i+j)) = Flx_dotproduct(v, gel(v_x,j+1), p);
      v = Flxq_transmul(tr, v, n, p);
    }
    c = Flx_renormalize(c, m+2);
    /* now c contains <v,x^i> , i = 0..m-1  */
    M = Flx_halfgcd(monomial_Flx(1, m, vT), c, p);
    g_prime = gmael(M, 2, 2);
    if (degpol(g_prime) < 1) continue;
    g = Flx_mul(g, g_prime, p);
    tau = Flxq_mul(tau, Flx_FlxqV_eval(g_prime, v_x, T, p), T, p);
  }
  g = Flx_normalize(g,p);
  return gerepileuptoleaf(ltop,g);
}

/* return (x % X^n). Shallow */
static GEN
Flxn_red_shallow(GEN a, long n)
{
  long i, L, l = lg(a);
  GEN  b;
  if (l == 2 || !n) return zero_Flx(a[1]);
  L = n+2; if (L > l) L = l;
  b = cgetg(L, t_VECSMALL); b[1] = a[1];
  for (i=2; i<L; i++) b[i] = a[i];
  return Flx_renormalize(b,L);
}
GEN
Flxn_inv(GEN f, long e, ulong p)
{
  pari_sp av = avma, av2;
  ulong mask;
  GEN W;
  long n=1;
  if (lg(f)==2) pari_err_INV("Flxn_inv",f);
  W = Fl_to_Flx(Fl_inv(f[2],p), f[1]);
  mask = quadratic_prec_mask(e);
  av2 = avma;
  for (;mask>1;)
  {
    GEN u, fr;
    long n2 = n;
    n<<=1; if (mask & 1) n--;
    mask >>= 1;
    fr = Flxn_red_shallow(f, n);
    u = Flx_shift(Flxn_mul(W, fr, n, p), -n2);
    W = Flx_sub(W, Flx_shift(Flxn_mul(u, W, n-n2, p), n2), p);
    if (gc_needed(av2,2))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"RgXn_inv, e = %ld", n);
      W = gerepileupto(av2, W);
    }
  }
  return gerepileupto(av, W);
}

GEN
Flxq_conjvec(GEN x, GEN T, ulong p)
{
  long i, l = 1+get_Flx_degree(T);
  GEN z = cgetg(l,t_COL);
  T = Flx_get_red(T,p);
  gel(z,1) = Flx_copy(x);
  for (i=2; i<l; i++) gel(z,i) = Flxq_powu(gel(z,i-1), p, T, p);
  return z;
}

GEN
gener_Flxq(GEN T, ulong p, GEN *po)
{
  long i, j;
  long vT = get_Flx_var(T), f =get_Flx_degree(T);
  ulong p_1;
  GEN g, L, L2, o, q, F;
  pari_sp av0, av;

  if (f == 1) {
    GEN fa;
    o = utoipos(p-1);
    fa = Z_factor(o);
    L = gel(fa,1);
    L = vecslice(L, 2, lg(L)-1); /* remove 2 for efficiency */
    g = Fl_to_Flx(pgener_Fl_local(p, vec_to_vecsmall(L)), vT);
    if (po) *po = mkvec2(o, fa);
    return g;
  }

  av0 = avma; p_1 = p - 1;
  q = diviuexact(subiu(powuu(p,f), 1), p_1);

  L = cgetg(1, t_VECSMALL);
  if (p > 3)
  {
    ulong t;
    (void)u_lvalrem(p_1, 2, &t);
    L = gel(factoru(t),1);
    for (i=lg(L)-1; i; i--) L[i] = p_1 / L[i];
  }
  o = factor_pn_1(utoipos(p),f);
  L2 = leafcopy( gel(o, 1) );
  for (i = j = 1; i < lg(L2); i++)
  {
    if (umodui(p_1, gel(L2,i)) == 0) continue;
    gel(L2,j++) = diviiexact(q, gel(L2,i));
  }
  setlg(L2, j);
  F = Flx_Frobenius(T, p);
  for (av = avma;; avma = av)
  {
    GEN tt;
    g = random_Flx(f, vT, p);
    if (degpol(g) < 1) continue;
    if (p == 2) tt = g;
    else
    {
      ulong t = Flxq_norm(g, T, p);
      if (t == 1 || !is_gener_Fl(t, p, p_1, L)) continue;
      tt = Flxq_powu(g, p_1>>1, T, p);
    }
    for (i = 1; i < j; i++)
    {
      GEN a = Flxq_pow_Frobenius(tt, gel(L2,i), F, T, p);
      if (!degpol(a) && uel(a,2) == p_1) break;
    }
    if (i == j) break;
  }
  if (!po)
  {
    avma = (pari_sp)g;
    g = gerepileuptoleaf(av0, g);
  }
  else {
    *po = mkvec2(subiu(powuu(p,f), 1), o);
    gerepileall(av0, 2, &g, po);
  }
  return g;
}

static GEN
_Flxq_neg(void *E, GEN x)
{ struct _Flxq *s = (struct _Flxq *)E;
  return Flx_neg(x,s->p); }

static GEN
_Flxq_rmul(void *E, GEN x, GEN y)
{ struct _Flxq *s = (struct _Flxq *)E;
  return Flx_mul(x,y,s->p); }

static GEN
_Flxq_inv(void *E, GEN x)
{ struct _Flxq *s = (struct _Flxq *)E;
  return Flxq_inv(x,s->T,s->p); }

static int
_Flxq_equal0(GEN x) { return lgpol(x)==0; }

static GEN
_Flxq_s(void *E, long x)
{ struct _Flxq *s = (struct _Flxq *)E;
  ulong u = x<0 ? s->p+x: (ulong)x;
  return Fl_to_Flx(u, get_Flx_var(s->T));
}

static const struct bb_field Flxq_field={_Flxq_red,_Flx_add,_Flxq_rmul,_Flxq_neg,
                                         _Flxq_inv,_Flxq_equal0,_Flxq_s};

const struct bb_field *get_Flxq_field(void **E, GEN T, ulong p)
{
  GEN z = new_chunk(sizeof(struct _Flxq));
  struct _Flxq *e = (struct _Flxq *) z;
  e->T = Flx_get_red(T, p); e->p  = p; *E = (void*)e;
  return &Flxq_field;
}

/***********************************************************************/
/**                                                                   **/
/**                               Fl2                                 **/
/**                                                                   **/
/***********************************************************************/
/* Fl2 objects are Flv of length 2 [a,b] representing a+bsqrt(D) for
   a non-square D.
*/

INLINE GEN
mkF2(ulong a, ulong b) { return mkvecsmall2(a,b); }

GEN
Fl2_mul_pre(GEN x, GEN y, ulong D, ulong p, ulong pi)
{
  ulong xaya, xbyb, Db2, mid;
  ulong z1, z2;
  ulong x1 = x[1], x2 = x[2], y1 = y[1], y2 = y[2];
  xaya = Fl_mul_pre(x1,y1,p,pi);
  if (x2==0 && y2==0) return mkF2(xaya,0);
  if (x2==0) return mkF2(xaya,Fl_mul_pre(x1,y2,p,pi));
  if (y2==0) return mkF2(xaya,Fl_mul_pre(x2,y1,p,pi));
  xbyb = Fl_mul_pre(x2,y2,p,pi);
  mid = Fl_mul_pre(Fl_add(x1,x2,p), Fl_add(y1,y2,p),p,pi);
  Db2 = Fl_mul_pre(D, xbyb, p,pi);
  z1 = Fl_add(xaya,Db2,p);
  z2 = Fl_sub(mid,Fl_add(xaya,xbyb,p),p);
  return mkF2(z1,z2);
}

GEN
Fl2_sqr_pre(GEN x, ulong D, ulong p, ulong pi)
{
  ulong a = x[1], b = x[2];
  ulong a2, Db2, ab;
  a2 = Fl_sqr_pre(a,p,pi);
  if (b==0) return mkF2(a2,0);
  Db2= Fl_mul_pre(D, Fl_sqr_pre(b,p,pi), p,pi);
  ab = Fl_mul_pre(a,b,p,pi);
  return mkF2(Fl_add(a2,Db2,p), Fl_double(ab,p));
}

ulong
Fl2_norm_pre(GEN x, ulong D, ulong p, ulong pi)
{
  ulong a2 = Fl_sqr_pre(x[1],p,pi);
  return x[2]? Fl_sub(a2, Fl_mul_pre(D, Fl_sqr_pre(x[2], p,pi), p,pi), p): a2;
}

GEN
Fl2_inv_pre(GEN x, ulong D, ulong p, ulong pi)
{
  ulong n, ni;
  if (x[2] == 0) return mkF2(Fl_inv(x[1],p),0);
  n = Fl_sub(Fl_sqr_pre(x[1], p,pi),
             Fl_mul_pre(D, Fl_sqr_pre(x[2], p,pi), p,pi), p);
  ni = Fl_inv(n,p);
  return mkF2(Fl_mul_pre(x[1], ni, p,pi),
               Fl_neg(Fl_mul_pre(x[2], ni, p,pi), p));
}

int
Fl2_equal1(GEN x) { return x[1]==1 && x[2]==0; }

struct _Fl2 {
  ulong p, pi, D;
};


static GEN
_Fl2_sqr(void *data, GEN x)
{
  struct _Fl2 *D = (struct _Fl2*)data;
  return Fl2_sqr_pre(x, D->D, D->p, D->pi);
}
static GEN
_Fl2_mul(void *data, GEN x, GEN y)
{
  struct _Fl2 *D = (struct _Fl2*)data;
  return Fl2_mul_pre(x,y, D->D, D->p, D->pi);
}

/* n-Power of x in Z/pZ[X]/(T), as t_VECSMALL. */
GEN
Fl2_pow_pre(GEN x, GEN n, ulong D, ulong p, ulong pi)
{
  pari_sp av = avma;
  struct _Fl2 d;
  GEN y;
  long s = signe(n);
  if (!s) return mkF2(1,0);
  if (s < 0)
    x = Fl2_inv_pre(x,D,p,pi);
  if (is_pm1(n)) return s < 0 ? x : zv_copy(x);
  d.p = p; d.pi = pi; d.D=D;
  y = gen_pow_i(x, n, (void*)&d, &_Fl2_sqr, &_Fl2_mul);
  return gerepileuptoleaf(av, y);
}

static GEN
_Fl2_pow(void *data, GEN x, GEN n)
{
  struct _Fl2 *D = (struct _Fl2*)data;
  return Fl2_pow_pre(x, n, D->D, D->p, D->pi);
}

static GEN
_Fl2_rand(void *data)
{
  struct _Fl2 *D = (struct _Fl2*)data;
  ulong a = random_Fl(D->p), b=random_Fl(D->p-1)+1;
  return mkF2(a,b);
}

static const struct bb_group Fl2_star={_Fl2_mul, _Fl2_pow, _Fl2_rand,
       hash_GEN, zv_equal, Fl2_equal1, NULL};

GEN
Fl2_sqrtn_pre(GEN a, GEN n, ulong D, ulong p, ulong pi, GEN *zeta)
{
  struct _Fl2 E;
  GEN o;
  if (a[1]==0 && a[2]==0)
  {
    if (signe(n) < 0) pari_err_INV("Flxq_sqrtn",a);
    if (zeta) *zeta=mkF2(1,0);
    return zv_copy(a);
  }
  E.p=p; E.pi = pi; E.D = D;
  o = subiu(powuu(p,2), 1);
  return gen_Shanks_sqrtn(a,n,o,zeta,(void*)&E,&Fl2_star);
}

GEN
Flx_Fl2_eval_pre(GEN x, GEN y, ulong D, ulong p, ulong pi)
{
  GEN p1;
  long i = lg(x)-1;
  if (i <= 2)
    return mkF2(i == 2? x[2]: 0, 0);
  p1 = mkF2(x[i], 0);
  for (i--; i>=2; i--)
  {
    p1 = Fl2_mul_pre(p1, y, D, p, pi);
    uel(p1,1) = Fl_add(uel(p1,1), uel(x,i), p);
  }
  return p1;
}


/***********************************************************************/
/**                                                                   **/
/**                               FlxV                                **/
/**                                                                   **/
/***********************************************************************/
/* FlxV are t_VEC with Flx coefficients. */

GEN
FlxV_Flc_mul(GEN V, GEN W, ulong p)
{
  pari_sp ltop=avma;
  long i;
  GEN z = Flx_Fl_mul(gel(V,1),W[1],p);
  for(i=2;i<lg(V);i++)
    z=Flx_add(z,Flx_Fl_mul(gel(V,i),W[i],p),p);
  return gerepileuptoleaf(ltop,z);
}

GEN
ZXV_to_FlxV(GEN x, ulong p)
{ pari_APPLY_type(t_VEC, ZX_to_Flx(gel(x,i), p)) }

GEN
ZXT_to_FlxT(GEN x, ulong p)
{
  if (typ(x) == t_POL)
    return ZX_to_Flx(x, p);
  else
    pari_APPLY_type(t_VEC, ZXT_to_FlxT(gel(x,i), p))
}

GEN
FlxV_to_Flm(GEN x, long n)
{ pari_APPLY_type(t_MAT, Flx_to_Flv(gel(x,i), n)) }

GEN
FlxV_red(GEN x, ulong p)
{ pari_APPLY_type(t_VEC, Flx_red(gel(x,i), p)) }

GEN
FlxT_red(GEN x, ulong p)
{
  if (typ(x) == t_VECSMALL)
    return Flx_red(x, p);
  else
    pari_APPLY_type(t_VEC, FlxT_red(gel(x,i), p))
}

GEN
FlxqV_dotproduct(GEN x, GEN y, GEN T, ulong p)
{
  long i, lx = lg(x);
  pari_sp av;
  GEN c;
  if (lx == 1) return pol0_Flx(get_Flx_var(T));
  av = avma; c = Flx_mul(gel(x,1),gel(y,1), p);
  for (i=2; i<lx; i++) c = Flx_add(c, Flx_mul(gel(x,i),gel(y,i), p), p);
  return gerepileuptoleaf(av, Flx_rem(c,T,p));
}

GEN
FlxqX_dotproduct(GEN x, GEN y, GEN T, ulong p)
{
  long i, l = minss(lg(x), lg(y));
  pari_sp av;
  GEN c;
  if (l == 2) return pol0_Flx(get_Flx_var(T));
  av = avma; c = Flx_mul(gel(x,2),gel(y,2), p);
  for (i=3; i<l; i++) c = Flx_add(c, Flx_mul(gel(x,i),gel(y,i), p), p);
  return gerepileuptoleaf(av, Flx_rem(c,T,p));
}

GEN
FlxC_eval_powers_pre(GEN z, GEN x, ulong p, ulong pi)
{
  long i, l = lg(z);
  GEN y = cgetg(l, t_VECSMALL);
  for (i=1; i<l; i++)
    uel(y,i) = Flx_eval_powers_pre(gel(z,i), x, p, pi);
  return y;
}

/***********************************************************************/
/**                                                                   **/
/**                               FlxM                                **/
/**                                                                   **/
/***********************************************************************/

GEN
FlxM_eval_powers_pre(GEN z, GEN x, ulong p, ulong pi)
{
  long i, l = lg(z);
  GEN y = cgetg(l, t_MAT);
  for (i=1; i<l; i++)
    gel(y,i) = FlxC_eval_powers_pre(gel(z,i), x, p, pi);
  return y;
}

GEN
zero_FlxC(long n, long sv)
{
  long i;
  GEN x = cgetg(n + 1, t_COL);
  GEN z = zero_Flx(sv);
  for (i = 1; i <= n; i++)
    gel(x, i) = z;
  return x;
}

GEN
FlxC_neg(GEN x, ulong p)
{ pari_APPLY_type(t_COL, Flx_neg(gel(x, i), p)) }

GEN
FlxC_sub(GEN x, GEN y, ulong p)
{ pari_APPLY_type(t_COL, Flx_sub(gel(x, i), gel(y, i), p)) }

GEN
zero_FlxM(long r, long c, long sv)
{
  long j;
  GEN x = cgetg(c + 1, t_MAT);
  GEN z = zero_FlxC(r, sv);
  for (j = 1; j <= c; j++)
    gel(x, j) = z;
  return x;
}

GEN
FlxM_neg(GEN x, ulong p)
{ pari_APPLY_same(FlxC_neg(gel(x, i), p)) }

GEN
FlxM_sub(GEN x, GEN y, ulong p)
{ pari_APPLY_same(FlxC_sub(gel(x, i), gel(y,i), p)) }

/***********************************************************************/
/**                                                                   **/
/**                               FlxX                                **/
/**                                                                   **/
/***********************************************************************/

/* FlxX are t_POL with Flx coefficients.
 * Normally the variable ordering should be respected.*/

/*Similar to normalizepol, in place*/
/*FlxX_renormalize=zxX_renormalize */
GEN
FlxX_renormalize(GEN /*in place*/ x, long lx)
{
  long i;
  for (i = lx-1; i>1; i--)
    if (lgpol(gel(x,i))) break;
  stackdummy((pari_sp)(x + lg(x)), (pari_sp)(x + i+1));
  setlg(x, i+1); setsigne(x, i!=1); return x;
}

GEN
pol1_FlxX(long v, long sv)
{
  GEN z = cgetg(3, t_POL);
  z[1] = evalsigne(1) | evalvarn(v);
  gel(z,2) = pol1_Flx(sv); return z;
}

GEN
polx_FlxX(long v, long sv)
{
  GEN z = cgetg(4, t_POL);
  z[1] = evalsigne(1) | evalvarn(v);
  gel(z,2) = pol0_Flx(sv);
  gel(z,3) = pol1_Flx(sv); return z;
}

long
FlxY_degreex(GEN b)
{
  long deg = -1, i;
  if (!signe(b)) return -1;
  for (i = 2; i < lg(b); ++i)
    deg = maxss(deg, degpol(gel(b, i)));
  return deg;
}

/*Lift coefficient of B to constant Flx, to give a FlxY*/
GEN
Fly_to_FlxY(GEN B, long sv)
{
  long lb=lg(B);
  long i;
  GEN b=cgetg(lb,t_POL);
  b[1]=evalsigne(1)|(((ulong)B[1])&VARNBITS);
  for (i=2; i<lb; i++)
    gel(b,i) = Fl_to_Flx(B[i], sv);
  return FlxX_renormalize(b, lb);
}

GEN
zxX_to_FlxX(GEN B, ulong p)
{
  long i, lb = lg(B);
  GEN b = cgetg(lb,t_POL);
  for (i=2; i<lb; i++)
    gel(b,i) = zx_to_Flx(gel(B,i), p);
  b[1] = B[1]; return FlxX_renormalize(b, lb);
}

GEN
FlxX_to_ZXX(GEN B)
{
  long i, lb = lg(B);
  GEN b = cgetg(lb,t_POL);
  for (i=2; i<lb; i++)
  {
    GEN c = gel(B,i);
    switch(lgpol(c))
    {
      case 0:  c = gen_0; break;
      case 1:  c = utoi(c[2]); break;
      default: c = Flx_to_ZX(c); break;
    }
    gel(b,i) = c;
  }
  b[1] = B[1]; return b;
}

GEN
FlxXC_to_ZXXC(GEN x)
{ pari_APPLY_type(t_COL, FlxX_to_ZXX(gel(x,i))) }

GEN
FlxXM_to_ZXXM(GEN x)
{ pari_APPLY_same(FlxXC_to_ZXXC(gel(x,i))) }

/* Note: v is used _only_ for the t_INT. It must match
 * the variable of any t_POL coefficients. */
GEN
ZXX_to_FlxX(GEN B, ulong p, long v)
{
  long lb=lg(B);
  long i;
  GEN b=cgetg(lb,t_POL);
  b[1]=evalsigne(1)|(((ulong)B[1])&VARNBITS);
  for (i=2; i<lb; i++)
    switch (typ(gel(B,i)))
    {
    case t_INT:
      gel(b,i) = Z_to_Flx(gel(B,i), p, evalvarn(v));
      break;
    case t_POL:
      gel(b,i) = ZX_to_Flx(gel(B,i), p);
      break;
    }
  return FlxX_renormalize(b, lb);
}

GEN
ZXXV_to_FlxXV(GEN x, ulong p, long v)
{ pari_APPLY_type(t_VEC, ZXX_to_FlxX(gel(x,i), p, v)) }

GEN
ZXXT_to_FlxXT(GEN x, ulong p, long v)
{
  if (typ(x) == t_POL)
    return ZXX_to_FlxX(x, p, v);
  else
    pari_APPLY_type(t_VEC, ZXXT_to_FlxXT(gel(x,i), p, v))
}

GEN
FlxX_to_FlxC(GEN x, long N, long sv)
{
  long i, l;
  GEN z;
  l = lg(x)-1; x++;
  if (l > N+1) l = N+1; /* truncate higher degree terms */
  z = cgetg(N+1,t_COL);
  for (i=1; i<l ; i++) gel(z,i) = gel(x,i);
  for (   ; i<=N; i++) gel(z,i) = pol0_Flx(sv);
  return z;
}

GEN
FlxXV_to_FlxM(GEN v, long n, long sv)
{
  long j, N = lg(v);
  GEN y = cgetg(N, t_MAT);
  for (j=1; j<N; j++) gel(y,j) = FlxX_to_FlxC(gel(v,j), n, sv);
  return y;
}

/* matrix whose entries are given by the coeffs of the polynomial v in
 * two variables (considered as degree n polynomials) */
GEN
FlxX_to_Flm(GEN v, long n)
{
  long j, N = lg(v)-1;
  GEN y = cgetg(N, t_MAT);
  v++;
  for (j=1; j<N; j++) gel(y,j) = Flx_to_Flv(gel(v,j), n);
  return y;
}

GEN
FlxX_to_Flx(GEN f)
{
  long i, l = lg(f);
  GEN V = cgetg(l, t_VECSMALL);
  V[1] = ((ulong)f[1])&VARNBITS;
  for(i=2; i<l; i++)
    V[i] = lgpol(gel(f,i)) ? mael(f,i,2): 0L;
  return V;
}

GEN
Flm_to_FlxX(GEN x, long v,long w)
{
  long j, lx = lg(x);
  GEN y = cgetg(lx+1, t_POL);
  y[1]=evalsigne(1) | v;
  y++;
  for (j=1; j<lx; j++) gel(y,j) = Flv_to_Flx(gel(x,j), w);
  return FlxX_renormalize(--y, lx+1);
}

/* P(X,Y) --> P(Y,X), n-1 is the degree in Y */
GEN
FlxX_swap(GEN x, long n, long ws)
{
  long j, lx = lg(x), ly = n+3;
  GEN y = cgetg(ly, t_POL);
  y[1] = x[1];
  for (j=2; j<ly; j++)
  {
    long k;
    GEN p1 = cgetg(lx, t_VECSMALL);
    p1[1] = ws;
    for (k=2; k<lx; k++)
      if (j<lg(gel(x,k)))
        p1[k] = mael(x,k,j);
      else
        p1[k] = 0;
    gel(y,j) = Flx_renormalize(p1,lx);
  }
  return FlxX_renormalize(y,ly);
}

static GEN
zxX_to_Kronecker_spec(GEN P, long lp, long n)
{ /* P(X) = sum Pi(Y) * X^i, return P( Y^(2n-1) ) */
  long i, j, k, l, N = (n<<1) + 1;
  GEN y = cgetg((N-2)*lp + 2, t_VECSMALL) + 2;
  for (k=i=0; i<lp; i++)
  {
    GEN c = gel(P,i);
    l = lg(c);
    if (l-3 >= n)
      pari_err_BUG("zxX_to_Kronecker, P is not reduced mod Q");
    for (j=2; j < l; j++) y[k++] = c[j];
    if (i == lp-1) break;
    for (   ; j < N; j++) y[k++] = 0;
  }
  y -= 2;
  y[1] = P[1]; setlg(y, k+2); return y;
}

GEN
zxX_to_Kronecker(GEN P, GEN Q)
{
  GEN z = zxX_to_Kronecker_spec(P+2, lg(P)-2, degpol(Q));
  z[1] = P[1]; return z;
}

GEN
FlxX_add(GEN x, GEN y, ulong p)
{
  long i,lz;
  GEN z;
  long lx=lg(x);
  long ly=lg(y);
  if (ly>lx) swapspec(x,y, lx,ly);
  lz = lx; z = cgetg(lz, t_POL); z[1]=x[1];
  for (i=2; i<ly; i++) gel(z,i) = Flx_add(gel(x,i), gel(y,i), p);
  for (   ; i<lx; i++) gel(z,i) = Flx_copy(gel(x,i));
  return FlxX_renormalize(z, lz);
}

GEN
FlxX_Flx_add(GEN y, GEN x, ulong p)
{
  long i, lz = lg(y);
  GEN z;
  if (signe(y) == 0) return scalarpol(x, varn(y));
  z = cgetg(lz,t_POL); z[1] = y[1];
  gel(z,2) = Flx_add(gel(y,2), x, p);
  if (lz == 3) z = FlxX_renormalize(z,lz);
  else
    for(i=3;i<lz;i++) gel(z,i) = Flx_copy(gel(y,i));
  return z;
}

GEN
FlxX_Flx_sub(GEN y, GEN x, ulong p)
{
  long i, lz = lg(y);
  GEN z;
  if (signe(y) == 0) return scalarpol(x, varn(y));
  z = cgetg(lz,t_POL); z[1] = y[1];
  gel(z,2) = Flx_sub(gel(y,2), x, p);
  if (lz == 3) z = FlxX_renormalize(z,lz);
  else
    for(i=3;i<lz;i++) gel(z,i) = Flx_copy(gel(y,i));
  return z;
}

GEN
FlxX_neg(GEN x, ulong p)
{
  long i, lx=lg(x);
  GEN z = cgetg(lx, t_POL);
  z[1]=x[1];
  for (i=2; i<lx; i++) gel(z,i) = Flx_neg(gel(x,i), p);
  return z;
}

GEN
FlxX_Fl_mul(GEN x, ulong y, ulong p)
{
  long i, lx=lg(x);
  GEN z = cgetg(lx, t_POL);
  z[1]=x[1];
  for (i=2; i<lx; i++) gel(z,i) = Flx_Fl_mul(gel(x,i), y, p);
  return FlxX_renormalize(z, lx);
}

GEN
FlxX_triple(GEN x, ulong p)
{
  long i, lx=lg(x);
  GEN z = cgetg(lx, t_POL);
  z[1]=x[1];
  for (i=2; i<lx; i++) gel(z,i) = Flx_triple(gel(x,i), p);
  return FlxX_renormalize(z, lx);
}

GEN
FlxX_double(GEN x, ulong p)
{
  long i, lx=lg(x);
  GEN z = cgetg(lx, t_POL);
  z[1]=x[1];
  for (i=2; i<lx; i++) gel(z,i) = Flx_double(gel(x,i), p);
  return FlxX_renormalize(z, lx);
}

GEN
FlxX_deriv(GEN z, ulong p)
{
  long i,l = lg(z)-1;
  GEN x;
  if (l < 2) l = 2;
  x = cgetg(l, t_POL); x[1] = z[1];
  for (i=2; i<l; i++) gel(x,i) = Flx_mulu(gel(z,i+1), (ulong) i-1, p);
  return FlxX_renormalize(x,l);
}

static GEN
FlxX_subspec(GEN x, GEN y, ulong p, long lx, long ly)
{
  long i,lz;
  GEN z;

  if (ly <= lx)
  {
    lz = lx+2; z = cgetg(lz, t_POL)+2;
    for (i=0; i<ly; i++) gel(z,i) = Flx_sub(gel(x,i),gel(y,i),p);
    for (   ; i<lx; i++) gel(z,i) = Flx_copy(gel(x,i));
  }
  else
  {
    lz = ly+2; z = cgetg(lz, t_POL)+2;
    for (i=0; i<lx; i++) gel(z,i) = Flx_sub(gel(x,i),gel(y,i),p);
    for (   ; i<ly; i++) gel(z,i) = Flx_neg(gel(y,i),p);
  }
 return FlxX_renormalize(z-2, lz);
}

GEN
FlxX_sub(GEN x, GEN y, ulong p)
{
  long lx,ly,i,lz;
  GEN z;
  lx = lg(x); ly = lg(y);
  lz=maxss(lx,ly);
  z = cgetg(lz,t_POL);
  if (lx >= ly)
  {
    z[1] = x[1];
    for (i=2; i<ly; i++) gel(z,i) = Flx_sub(gel(x,i),gel(y,i),p);
    for (   ; i<lx; i++) gel(z,i) = Flx_copy(gel(x,i));
    if (lx==ly) z = FlxX_renormalize(z, lz);
  }
  else
  {
    z[1] = y[1];
    for (i=2; i<lx; i++) gel(z,i) = Flx_sub(gel(x,i),gel(y,i),p);
    for (   ; i<ly; i++) gel(z,i) = Flx_neg(gel(y,i),p);
  }
  if (!lgpol(z)) { avma = (pari_sp)(z + lz); z = pol_0(varn(x)); }
  return z;
}

GEN
FlxX_Flx_mul(GEN P, GEN U, ulong p)
{
  long i, lP = lg(P);
  GEN res = cgetg(lP,t_POL);
  res[1] = P[1];
  for(i=2; i<lP; i++)
    gel(res,i) = Flx_mul(U,gel(P,i), p);
  return FlxX_renormalize(res, lP);
}

GEN
FlxY_evalx(GEN Q, ulong x, ulong p)
{
  GEN z;
  long i, lb = lg(Q);
  z = cgetg(lb,t_VECSMALL); z[1] = evalvarn(varn(Q));
  for (i=2; i<lb; i++) z[i] = Flx_eval(gel(Q,i), x, p);
  return Flx_renormalize(z, lb);
}

GEN
FlxY_Flx_translate(GEN P, GEN c, ulong p)
{
  pari_sp av = avma;
  GEN Q;
  long i, k, n;

  if (!signe(P) || gequal0(c)) return RgX_copy(P);
  Q = leafcopy(P); n = degpol(P);
  for (i=1; i<=n; i++)
  {
    for (k=n-i; k<n; k++)
      gel(Q,2+k) = Flx_add(gel(Q,2+k), Flx_mul(gel(Q,2+k+1), c, p), p);
    if (gc_needed(av,2))
    {
      if(DEBUGMEM>1)
        pari_warn(warnmem,"FlxY_Flx_translate, i = %ld/%ld", i,n);
      Q = gerepilecopy(av, Q);
    }
  }
  return gerepilecopy(av, Q);
}

GEN
FlxY_evalx_powers_pre(GEN pol, GEN ypowers, ulong p, ulong pi)
{
  long i, len = lg(pol);
  GEN res = cgetg(len, t_VECSMALL);
  res[1] = pol[1] & VARNBITS;
  for (i = 2; i < len; ++i)
    res[i] = Flx_eval_powers_pre(gel(pol, i), ypowers, p, pi);
  return Flx_renormalize(res, len);
}

ulong
FlxY_eval_powers_pre(GEN pol, GEN ypowers, GEN xpowers, ulong p, ulong pi)
{
  pari_sp av = avma;
  GEN t = FlxY_evalx_powers_pre(pol, ypowers, p, pi);
  ulong out = Flx_eval_powers_pre(t, xpowers, p, pi);
  avma = av;
  return out;
}

GEN
FlxY_FlxqV_evalx(GEN P, GEN x, GEN T, ulong p)
{
  long i, lP = lg(P);
  GEN res = cgetg(lP,t_POL);
  res[1] = P[1];
  for(i=2; i<lP; i++)
    gel(res,i) = Flx_FlxqV_eval(gel(P,i), x, T, p);
  return FlxX_renormalize(res, lP);
}

GEN
FlxY_Flxq_evalx(GEN P, GEN x, GEN T, ulong p)
{
  pari_sp av = avma;
  long n = brent_kung_optpow(get_Flx_degree(T)-1,lgpol(P),1);
  GEN xp = Flxq_powers(x, n, T, p);
  return gerepileupto(av, FlxY_FlxqV_evalx(P, xp, T, p));
}

GEN
FlxY_Flx_div(GEN x, GEN y, ulong p)
{
  long i, l;
  GEN z;
  if (degpol(y) == 0)
  {
    ulong t = uel(y,2);
    if (t == 1) return x;
    t = Fl_inv(t, p);
    z = cgetg_copy(x, &l); z[1] = x[1];
    for (i=2; i<l; i++) gel(z,i) = Flx_Fl_mul(gel(x,i),t,p);
  }
  else
  {
    z = cgetg_copy(x, &l); z[1] = x[1];
    for (i=2; i<l; i++) gel(z,i) = Flx_div(gel(x,i),y,p);
  }
  return z;
}

GEN
FlxX_shift(GEN a, long n, long vs)
{
  long i, l = lg(a);
  GEN  b;
  if (l == 2 || !n) return a;
  l += n;
  if (n < 0)
  {
    if (l <= 2) return pol_0(varn(a));
    b = cgetg(l, t_POL); b[1] = a[1];
    a -= n;
    for (i=2; i<l; i++) gel(b,i) = gel(a,i);
  } else {
    b = cgetg(l, t_POL); b[1] = a[1];
    a -= n; n += 2;
    for (i=2; i<n; i++) gel(b,i) = pol0_Flx(vs);
    for (   ; i<l; i++) gel(b,i) = gel(a,i);
  }
  return b;
}

static GEN
FlxX_recipspec(GEN x, long l, long n, long vs)
{
  long i;
  GEN z = cgetg(n+2,t_POL);
  z[1] = 0; z += 2;
  for(i=0; i<l; i++)
    gel(z,n-i-1) = Flx_copy(gel(x,i));
  for(   ; i<n; i++)
    gel(z,n-i-1) = pol0_Flx(vs);
  return FlxX_renormalize(z-2,n+2);
}

/***********************************************************************/
/**                                                                   **/
/**                               FlxqX                               **/
/**                                                                   **/
/***********************************************************************/

static GEN
get_FlxqX_red(GEN T, GEN *B)
{
  if (typ(T)!=t_VEC) { *B=NULL; return T; }
  *B = gel(T,1); return gel(T,2);
}

GEN
RgX_to_FlxqX(GEN x, GEN T, ulong p)
{
  long i, l = lg(x);
  GEN z = cgetg(l, t_POL); z[1] = x[1];
  for (i = 2; i < l; i++)
    gel(z,i) = Rg_to_Flxq(gel(x,i), T, p);
  return FlxX_renormalize(z, l);
}

/* FlxqX are t_POL with Flxq coefficients.
 * Normally the variable ordering should be respected.*/

GEN
random_FlxqX(long d1, long v, GEN T, ulong p)
{
  long dT = get_Flx_degree(T), vT = get_Flx_var(T);
  long i, d = d1+2;
  GEN y = cgetg(d,t_POL); y[1] = evalsigne(1) | evalvarn(v);
  for (i=2; i<d; i++) gel(y,i) = random_Flx(dT, vT, p);
  return FlxX_renormalize(y,d);
}

/*Not stack clean*/
GEN
Kronecker_to_FlxqX(GEN z, GEN T, ulong p)
{
  long i,j,lx,l, N = (get_Flx_degree(T)<<1) + 1;
  GEN x, t = cgetg(N,t_VECSMALL);
  t[1] = get_Flx_var(T);
  l = lg(z); lx = (l-2) / (N-2);
  x = cgetg(lx+3,t_POL);
  x[1] = z[1];
  for (i=2; i<lx+2; i++)
  {
    for (j=2; j<N; j++) t[j] = z[j];
    z += (N-2);
    gel(x,i) = Flx_rem(Flx_renormalize(t,N), T,p);
  }
  N = (l-2) % (N-2) + 2;
  for (j=2; j<N; j++) t[j] = z[j];
  gel(x,i) = Flx_rem(Flx_renormalize(t,N), T,p);
  return FlxX_renormalize(x, i+1);
}

GEN
FlxqX_red(GEN z, GEN T, ulong p)
{
  GEN res;
  long i, l = lg(z);
  res = cgetg(l,t_POL); res[1] = z[1];
  for(i=2;i<l;i++) gel(res,i) = Flx_rem(gel(z,i),T,p);
  return FlxX_renormalize(res,l);
}

static GEN
FlxqX_mulspec(GEN x, GEN y, GEN T, ulong p, long lx, long ly)
{
  pari_sp ltop=avma;
  GEN z,kx,ky;
  long dT =  get_Flx_degree(T);
  kx= zxX_to_Kronecker_spec(x,lx,dT);
  ky= zxX_to_Kronecker_spec(y,ly,dT);
  z = Flx_mul(ky, kx, p);
  z = Kronecker_to_FlxqX(z,T,p);
  return gerepileupto(ltop,z);
}

GEN
FlxqX_mul(GEN x, GEN y, GEN T, ulong p)
{
  pari_sp ltop=avma;
  GEN z,kx,ky;
  kx= zxX_to_Kronecker(x,get_Flx_mod(T));
  ky= zxX_to_Kronecker(y,get_Flx_mod(T));
  z = Flx_mul(ky, kx, p);
  z = Kronecker_to_FlxqX(z,T,p);
  return gerepileupto(ltop,z);
}

GEN
FlxqX_sqr(GEN x, GEN T, ulong p)
{
  pari_sp ltop=avma;
  GEN z,kx;
  kx= zxX_to_Kronecker(x,get_Flx_mod(T));
  z = Flx_sqr(kx, p);
  z = Kronecker_to_FlxqX(z,T,p);
  return gerepileupto(ltop,z);
}

GEN
FlxqX_Flxq_mul(GEN P, GEN U, GEN T, ulong p)
{
  long i, lP = lg(P);
  GEN res = cgetg(lP,t_POL);
  res[1] = P[1];
  for(i=2; i<lP; i++)
    gel(res,i) = Flxq_mul(U,gel(P,i), T,p);
  return FlxX_renormalize(res, lP);
}
GEN
FlxqX_Flxq_mul_to_monic(GEN P, GEN U, GEN T, ulong p)
{
  long i, lP = lg(P);
  GEN res = cgetg(lP,t_POL);
  res[1] = P[1];
  for(i=2; i<lP-1; i++) gel(res,i) = Flxq_mul(U,gel(P,i), T,p);
  gel(res,lP-1) = pol1_Flx(get_Flx_var(T));
  return FlxX_renormalize(res, lP);
}

GEN
FlxqX_normalize(GEN z, GEN T, ulong p)
{
  GEN p1 = leading_coeff(z);
  if (!lgpol(z) || (!degpol(p1) && p1[1] == 1)) return z;
  return FlxqX_Flxq_mul_to_monic(z, Flxq_inv(p1,T,p), T,p);
}

/* x and y in Z[Y][X]. Assume T irreducible mod p */
static GEN
FlxqX_divrem_basecase(GEN x, GEN y, GEN T, ulong p, GEN *pr)
{
  long vx, dx, dy, dz, i, j, sx, lr;
  pari_sp av0, av, tetpil;
  GEN z,p1,rem,lead;

  if (!signe(y)) pari_err_INV("FlxqX_divrem",y);
  vx=varn(x); dy=degpol(y); dx=degpol(x);
  if (dx < dy)
  {
    if (pr)
    {
      av0 = avma; x = FlxqX_red(x, T, p);
      if (pr == ONLY_DIVIDES) { avma=av0; return signe(x)? NULL: pol_0(vx); }
      if (pr == ONLY_REM) return x;
      *pr = x;
    }
    return pol_0(vx);
  }
  lead = leading_coeff(y);
  if (!dy) /* y is constant */
  {
    if (pr && pr != ONLY_DIVIDES)
    {
      if (pr == ONLY_REM) return pol_0(vx);
      *pr = pol_0(vx);
    }
    if (Flx_equal1(lead)) return gcopy(x);
    av0 = avma; x = FlxqX_Flxq_mul(x,Flxq_inv(lead,T,p),T,p);
    return gerepileupto(av0,x);
  }
  av0 = avma; dz = dx-dy;
  lead = Flx_equal1(lead)? NULL: gclone(Flxq_inv(lead,T,p));
  avma = av0;
  z = cgetg(dz+3,t_POL); z[1] = x[1];
  x += 2; y += 2; z += 2;

  p1 = gel(x,dx); av = avma;
  gel(z,dz) = lead? gerepileupto(av, Flxq_mul(p1,lead, T, p)): gcopy(p1);
  for (i=dx-1; i>=dy; i--)
  {
    av=avma; p1=gel(x,i);
    for (j=i-dy+1; j<=i && j<=dz; j++)
      p1 = Flx_sub(p1, Flx_mul(gel(z,j),gel(y,i-j),p),p);
    if (lead) p1 = Flx_mul(p1, lead,p);
    tetpil=avma; gel(z,i-dy) = gerepile(av,tetpil,Flx_rem(p1,T,p));
  }
  if (!pr) { if (lead) gunclone(lead); return z-2; }

  rem = (GEN)avma; av = (pari_sp)new_chunk(dx+3);
  for (sx=0; ; i--)
  {
    p1 = gel(x,i);
    for (j=0; j<=i && j<=dz; j++)
      p1 = Flx_sub(p1, Flx_mul(gel(z,j),gel(y,i-j),p),p);
    tetpil=avma; p1 = Flx_rem(p1, T, p); if (lgpol(p1)) { sx = 1; break; }
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
      p1 = Flx_sub(p1, Flx_mul(gel(z,j),gel(y,i-j),p), p);
    tetpil=avma; gel(rem,i) = gerepile(av,tetpil, Flx_rem(p1, T, p));
  }
  rem -= 2;
  if (lead) gunclone(lead);
  if (!sx) (void)FlxX_renormalize(rem, lr);
  if (pr == ONLY_REM) return gerepileupto(av0,rem);
  *pr = rem; return z-2;
}

static GEN
FlxqX_invBarrett_basecase(GEN T, GEN Q, ulong p)
{
  long i, l=lg(T)-1, lr = l-1, k;
  long sv=Q[1];
  GEN r=cgetg(lr,t_POL); r[1]=T[1];
  gel(r,2) = pol1_Flx(sv);
  for (i=3;i<lr;i++)
  {
    pari_sp ltop=avma;
    GEN u = Flx_neg(gel(T,l-i+2),p);
    for (k=3;k<i;k++)
      u = Flx_sub(u, Flxq_mul(gel(T,l-i+k),gel(r,k),Q,p),p);
    gel(r,i) = gerepileupto(ltop, u);
  }
  r = FlxX_renormalize(r,lr);
  return r;
}

/* Return new lgpol */
static long
FlxX_lgrenormalizespec(GEN x, long lx)
{
  long i;
  for (i = lx-1; i>=0; i--)
    if (lgpol(gel(x,i))) break;
  return i+1;
}

static GEN
FlxqX_invBarrett_Newton(GEN S, GEN T, ulong p)
{
  pari_sp av = avma;
  long nold, lx, lz, lq, l = degpol(S), i, lQ;
  GEN q, y, z, x = cgetg(l+2, t_POL) + 2;
  long dT = get_Flx_degree(T);
  ulong mask = quadratic_prec_mask(l-2); /* assume l > 2 */
  for (i=0;i<l;i++) gel(x,i) = pol0_Flx(T[1]);
  q = FlxX_recipspec(S+2,l+1,l+1,dT);
  lQ = lgpol(q); q+=2;
  /* We work on _spec_ FlxX's, all the l[xzq] below are lgpol's */

  /* initialize */
  gel(x,0) = Flxq_inv(gel(q,0),T, p);
  if (lQ>1 && degpol(gel(q,1)) >= dT)
    gel(q,1) = Flx_rem(gel(q,1), T, p);
  if (lQ>1 && lgpol(gel(q,1)))
  {
    GEN u = gel(q, 1);
    if (!Flx_equal1(gel(x,0))) u = Flxq_mul(u, Flxq_sqr(gel(x,0), T,p), T,p);
    gel(x,1) = Flx_neg(u, p); lx = 2;
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
    lq = FlxX_lgrenormalizespec(q, minss(lQ,lnew));
    z = FlxqX_mulspec(x, q, T, p, lx, lq); /* FIXME: high product */
    lz = lgpol(z); if (lz > lnew) lz = lnew;
    z += 2;
    /* subtract 1 [=>first nold words are 0]: renormalize so that z(0) != 0 */
    for (i = nold; i < lz; i++) if (lgpol(gel(z,i))) break;
    nold = nnew;
    if (i >= lz) continue; /* z-1 = 0(t^(nnew + 1)) */

    /* z + i represents (x*q - 1) / t^i */
    lz = FlxX_lgrenormalizespec (z+i, lz-i);
    z = FlxqX_mulspec(x, z+i, T,p, lx, lz); /* FIXME: low product */
    lz = lgpol(z); z += 2;
    if (lz > lnew-i) lz = FlxX_lgrenormalizespec(z, lnew-i);

    lx = lz+ i;
    y  = x + i; /* x -= z * t^i, in place */
    for (i = 0; i < lz; i++) gel(y,i) = Flx_neg(gel(z,i), p);
  }
  x -= 2; setlg(x, lx + 2); x[1] = S[1];
  return gerepilecopy(av, x);
}

/* x/polrecip(P)+O(x^n) */
GEN
FlxqX_invBarrett(GEN T, GEN Q, ulong p)
{
  pari_sp ltop=avma;
  long l=lg(T), v = varn(T);
  GEN r;
  GEN c = gel(T,l-1);
  if (l<5) return pol_0(v);
  if (l<=FlxqX_INVBARRETT_LIMIT)
  {
    if (!Flx_equal1(c))
    {
      GEN ci = Flxq_inv(c,Q,p);
      T = FlxqX_Flxq_mul(T, ci, Q, p);
      r = FlxqX_invBarrett_basecase(T,Q,p);
      r = FlxqX_Flxq_mul(r,ci,Q,p);
    } else
      r = FlxqX_invBarrett_basecase(T,Q,p);
  } else
    r = FlxqX_invBarrett_Newton(T,Q,p);
  return gerepileupto(ltop, r);
}

GEN
FlxqX_get_red(GEN S, GEN T, ulong p)
{
  if (typ(S)==t_POL && lg(S)>FlxqX_BARRETT_LIMIT)
    retmkvec2(FlxqX_invBarrett(S, T, p), S);
  return S;
}

/* Compute x mod S where 2 <= degpol(S) <= l+1 <= 2*(degpol(S)-1)
 *  * and mg is the Barrett inverse of S. */
static GEN
FlxqX_divrem_Barrettspec(GEN x, long l, GEN mg, GEN S, GEN T, ulong p, GEN *pr)
{
  GEN q, r;
  long lt = degpol(S); /*We discard the leading term*/
  long ld, lm, lT, lmg;
  ld = l-lt;
  lm = minss(ld, lgpol(mg));
  lT  = FlxX_lgrenormalizespec(S+2,lt);
  lmg = FlxX_lgrenormalizespec(mg+2,lm);
  q = FlxX_recipspec(x+lt,ld,ld,0);               /* q = rec(x)     lq<=ld*/
  q = FlxqX_mulspec(q+2,mg+2,T,p,lgpol(q),lmg);   /* q = rec(x) * mg lq<=ld+lm*/
  q = FlxX_recipspec(q+2,minss(ld,lgpol(q)),ld,0);/* q = rec (rec(x) * mg) lq<=ld*/
  if (!pr) return q;
  r = FlxqX_mulspec(q+2,S+2,T,p,lgpol(q),lT);     /* r = q*pol        lr<=ld+lt*/
  r = FlxX_subspec(x,r+2,p,lt,minss(lt,lgpol(r)));/* r = x - r   lr<=lt */
  if (pr == ONLY_REM) return r;
  *pr = r; return q;
}

static GEN
FlxqX_divrem_Barrett_noGC(GEN x, GEN mg, GEN S, GEN T, ulong p, GEN *pr)
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
    return FlxqX_divrem_basecase(x,S,T,p,pr);
  if (pr != ONLY_REM && l>lm)
  {
    long vT = get_Flx_var(T);
    q = cgetg(l-lt+2, t_POL);
    for (i=0;i<l-lt;i++) gel(q+2,i) = pol0_Flx(vT);
  }
  r = l>lm ? shallowcopy(x): x;
  while (l>lm)
  {
    GEN zr, zq = FlxqX_divrem_Barrettspec(r+2+l-lm,lm,mg,S,T,p,&zr);
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
      GEN zq = FlxqX_divrem_Barrettspec(r+2,l,mg,S,T,p,&r);
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
      (void) FlxqX_divrem_Barrettspec(r+2,l,mg,S,T,p,&r);
    else
    { setlg(r, l+2); r = RgX_copy(r); }
    r[1] = x[1]; return FlxX_renormalize(r, lg(r));
  }
  if (pr) { r[1] = x[1]; r = FlxX_renormalize(r, lg(r)); }
  q[1] = x[1]; q = FlxX_renormalize(q, lg(q));
  if (pr == ONLY_DIVIDES) return signe(r)? NULL: q;
  if (pr) *pr = r;
  return q;
}

GEN
FlxqX_divrem(GEN x, GEN S, GEN T, ulong p, GEN *pr)
{
  GEN B, y = get_FlxqX_red(S, &B);
  long dy = degpol(y), dx = degpol(x), d = dx-dy;
  if (pr==ONLY_REM) return FlxqX_rem(x, y, T, p);
  if (!B && d+3 < FlxqX_DIVREM_BARRETT_LIMIT)
    return FlxqX_divrem_basecase(x,y,T,p,pr);
  else
  {
    pari_sp av=avma;
    GEN mg = B? B: FlxqX_invBarrett(y, T, p);
    GEN q = FlxqX_divrem_Barrett_noGC(x,mg,y,T,p,pr);
    if (!q) {avma=av; return NULL;}
    if (!pr || pr==ONLY_DIVIDES) return gerepilecopy(av, q);
    gerepileall(av,2,&q,pr);
    return q;
  }
}

GEN
FlxqX_rem(GEN x, GEN S, GEN T, ulong p)
{
  GEN B, y = get_FlxqX_red(S, &B);
  long dy = degpol(y), dx = degpol(x), d = dx-dy;
  if (d < 0) return FlxqX_red(x, T, p);
  if (!B && d+3 < FlxqX_REM_BARRETT_LIMIT)
    return FlxqX_divrem_basecase(x,y, T, p, ONLY_REM);
  else
  {
    pari_sp av=avma;
    GEN mg = B? B: FlxqX_invBarrett(y, T, p);
    GEN r = FlxqX_divrem_Barrett_noGC(x, mg, y, T, p, ONLY_REM);
    return gerepileupto(av, r);
  }
}

static GEN
FlxqX_halfgcd_basecase(GEN a, GEN b, GEN T, ulong p)
{
  pari_sp av=avma;
  GEN u,u1,v,v1;
  long vx = varn(a);
  long n = lgpol(a)>>1;
  u1 = v = pol_0(vx);
  u = v1 = pol1_FlxX(vx, get_Flx_var(T));
  while (lgpol(b)>n)
  {
    GEN r, q = FlxqX_divrem(a,b, T, p, &r);
    a = b; b = r; swap(u,u1); swap(v,v1);
    u1 = FlxX_sub(u1, FlxqX_mul(u, q, T, p), p);
    v1 = FlxX_sub(v1, FlxqX_mul(v, q ,T, p), p);
    if (gc_needed(av,2))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"FlxqX_halfgcd (d = %ld)",degpol(b));
      gerepileall(av,6, &a,&b,&u1,&v1,&u,&v);
    }
  }
  return gerepilecopy(av, mkmat2(mkcol2(u,u1), mkcol2(v,v1)));
}
static GEN
FlxqX_addmulmul(GEN u, GEN v, GEN x, GEN y, GEN T, ulong p)
{
  return FlxX_add(FlxqX_mul(u, x, T, p),FlxqX_mul(v, y, T, p), p);
}

static GEN
FlxqXM_FlxqX_mul2(GEN M, GEN x, GEN y, GEN T, ulong p)
{
  GEN res = cgetg(3, t_COL);
  gel(res, 1) = FlxqX_addmulmul(gcoeff(M,1,1), gcoeff(M,1,2), x, y, T, p);
  gel(res, 2) = FlxqX_addmulmul(gcoeff(M,2,1), gcoeff(M,2,2), x, y, T, p);
  return res;
}

static GEN
FlxqXM_mul2(GEN A, GEN B, GEN T, ulong p)
{
  GEN A11=gcoeff(A,1,1),A12=gcoeff(A,1,2), B11=gcoeff(B,1,1),B12=gcoeff(B,1,2);
  GEN A21=gcoeff(A,2,1),A22=gcoeff(A,2,2), B21=gcoeff(B,2,1),B22=gcoeff(B,2,2);
  GEN M1 = FlxqX_mul(FlxX_add(A11,A22, p), FlxX_add(B11,B22, p), T, p);
  GEN M2 = FlxqX_mul(FlxX_add(A21,A22, p), B11, T, p);
  GEN M3 = FlxqX_mul(A11, FlxX_sub(B12,B22, p), T, p);
  GEN M4 = FlxqX_mul(A22, FlxX_sub(B21,B11, p), T, p);
  GEN M5 = FlxqX_mul(FlxX_add(A11,A12, p), B22, T, p);
  GEN M6 = FlxqX_mul(FlxX_sub(A21,A11, p), FlxX_add(B11,B12, p), T, p);
  GEN M7 = FlxqX_mul(FlxX_sub(A12,A22, p), FlxX_add(B21,B22, p), T, p);
  GEN T1 = FlxX_add(M1,M4, p), T2 = FlxX_sub(M7,M5, p);
  GEN T3 = FlxX_sub(M1,M2, p), T4 = FlxX_add(M3,M6, p);
  retmkmat2(mkcol2(FlxX_add(T1,T2, p), FlxX_add(M2,M4, p)),
            mkcol2(FlxX_add(M3,M5, p), FlxX_add(T3,T4, p)));
}

/* Return [0,1;1,-q]*M */
static GEN
FlxqX_FlxqXM_qmul(GEN q, GEN M, GEN T, ulong p)
{
  GEN u, v, res = cgetg(3, t_MAT);
  u = FlxX_sub(gcoeff(M,1,1), FlxqX_mul(gcoeff(M,2,1), q, T, p), p);
  gel(res,1) = mkcol2(gcoeff(M,2,1), u);
  v = FlxX_sub(gcoeff(M,1,2), FlxqX_mul(gcoeff(M,2,2), q, T, p), p);
  gel(res,2) = mkcol2(gcoeff(M,2,2), v);
  return res;
}

static GEN
matid2_FlxXM(long v, long sv)
{
  retmkmat2(mkcol2(pol1_FlxX(v, sv),pol_0(v)),
            mkcol2(pol_0(v),pol1_FlxX(v, sv)));
}

static GEN
FlxqX_halfgcd_split(GEN x, GEN y, GEN T, ulong p)
{
  pari_sp av=avma;
  GEN R, S, V;
  GEN y1, r, q;
  long l = lgpol(x), n = l>>1, k;
  if (lgpol(y)<=n) return matid2_FlxXM(varn(x),T[1]);
  R = FlxqX_halfgcd(RgX_shift_shallow(x,-n),RgX_shift_shallow(y,-n), T, p);
  V = FlxqXM_FlxqX_mul2(R,x,y, T, p); y1 = gel(V,2);
  if (lgpol(y1)<=n) return gerepilecopy(av, R);
  q = FlxqX_divrem(gel(V,1), y1, T, p, &r);
  k = 2*n-degpol(y1);
  S = FlxqX_halfgcd(RgX_shift_shallow(y1,-k), RgX_shift_shallow(r,-k), T, p);
  return gerepileupto(av, FlxqXM_mul2(S,FlxqX_FlxqXM_qmul(q,R, T, p), T, p));
}

/* Return M in GL_2(Fp[X]) such that:
if [a',b']~=M*[a,b]~ then degpol(a')>= (lgpol(a)>>1) >degpol(b')
*/

static GEN
FlxqX_halfgcd_i(GEN x, GEN y, GEN T, ulong p)
{
  if (lg(x)<=FlxqX_HALFGCD_LIMIT) return FlxqX_halfgcd_basecase(x, y, T, p);
  return FlxqX_halfgcd_split(x, y, T, p);
}

GEN
FlxqX_halfgcd(GEN x, GEN y, GEN T, ulong p)
{
  pari_sp av = avma;
  GEN M,q,r;
  if (!signe(x))
  {
    long v = varn(x), vT = get_Flx_var(T);
    retmkmat2(mkcol2(pol_0(v),pol1_FlxX(v,vT)),
        mkcol2(pol1_FlxX(v,vT),pol_0(v)));
  }
  if (degpol(y)<degpol(x)) return FlxqX_halfgcd_i(x, y, T, p);
  q = FlxqX_divrem(y, x, T, p, &r);
  M = FlxqX_halfgcd_i(x, r, T, p);
  gcoeff(M,1,1) = FlxX_sub(gcoeff(M,1,1), FlxqX_mul(q, gcoeff(M,1,2), T, p), p);
  gcoeff(M,2,1) = FlxX_sub(gcoeff(M,2,1), FlxqX_mul(q, gcoeff(M,2,2), T, p), p);
  return gerepilecopy(av, M);
}

static GEN
FlxqX_gcd_basecase(GEN a, GEN b, GEN T, ulong p)
{
  pari_sp av = avma, av0=avma;
  while (signe(b))
  {
    GEN c;
    if (gc_needed(av0,2))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"FlxqX_gcd (d = %ld)",degpol(b));
      gerepileall(av0,2, &a,&b);
    }
    av = avma; c = FlxqX_rem(a, b, T, p); a=b; b=c;
  }
  avma = av; return a;
}

GEN
FlxqX_gcd(GEN x, GEN y, GEN T, ulong p)
{
  pari_sp av = avma;
  x = FlxqX_red(x, T, p);
  y = FlxqX_red(y, T, p);
  if (!signe(x)) return gerepileupto(av, y);
  while (lg(y)>FlxqX_GCD_LIMIT)
  {
    GEN c;
    if (lgpol(y)<=(lgpol(x)>>1))
    {
      GEN r = FlxqX_rem(x, y, T, p);
      x = y; y = r;
    }
    c = FlxqXM_FlxqX_mul2(FlxqX_halfgcd(x,y, T, p), x, y, T, p);
    x = gel(c,1); y = gel(c,2);
    gerepileall(av,2,&x,&y);
  }
  return gerepileupto(av, FlxqX_gcd_basecase(x, y, T, p));
}

static GEN
FlxqX_extgcd_basecase(GEN a, GEN b, GEN T, ulong p, GEN *ptu, GEN *ptv)
{
  pari_sp av=avma;
  GEN u,v,d,d1,v1;
  long vx = varn(a);
  d = a; d1 = b;
  v = pol_0(vx); v1 = pol1_FlxX(vx, get_Flx_var(T));
  while (signe(d1))
  {
    GEN r, q = FlxqX_divrem(d, d1, T, p, &r);
    v = FlxX_sub(v,FlxqX_mul(q,v1,T, p),p);
    u=v; v=v1; v1=u;
    u=r; d=d1; d1=u;
    if (gc_needed(av,2))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"FlxqX_extgcd (d = %ld)",degpol(d));
      gerepileall(av,5, &d,&d1,&u,&v,&v1);
    }
  }
  if (ptu) *ptu = FlxqX_div(FlxX_sub(d,FlxqX_mul(b,v, T, p), p), a, T, p);
  *ptv = v; return d;
}

static GEN
FlxqX_extgcd_halfgcd(GEN x, GEN y, GEN T, ulong p, GEN *ptu, GEN *ptv)
{
  pari_sp av=avma;
  GEN u,v,R = matid2_FlxXM(varn(x), get_Flx_var(T));
  while (lg(y)>FlxqX_EXTGCD_LIMIT)
  {
    GEN M, c;
    if (lgpol(y)<=(lgpol(x)>>1))
    {
      GEN r, q = FlxqX_divrem(x, y, T, p, &r);
      x = y; y = r;
      R = FlxqX_FlxqXM_qmul(q, R, T, p);
    }
    M = FlxqX_halfgcd(x,y, T, p);
    c = FlxqXM_FlxqX_mul2(M, x,y, T, p);
    R = FlxqXM_mul2(M, R, T, p);
    x = gel(c,1); y = gel(c,2);
    gerepileall(av,3,&x,&y,&R);
  }
  y = FlxqX_extgcd_basecase(x,y, T, p, &u,&v);
  if (ptu) *ptu = FlxqX_addmulmul(u,v,gcoeff(R,1,1),gcoeff(R,2,1), T, p);
  *ptv = FlxqX_addmulmul(u,v,gcoeff(R,1,2),gcoeff(R,2,2), T, p);
  return y;
}

/* x and y in Z[Y][X], return lift(gcd(x mod T,p, y mod T,p)). Set u and v st
 * ux + vy = gcd (mod T,p) */
GEN
FlxqX_extgcd(GEN x, GEN y, GEN T, ulong p, GEN *ptu, GEN *ptv)
{
  GEN d;
  pari_sp ltop=avma;
  x = FlxqX_red(x, T, p);
  y = FlxqX_red(y, T, p);
  if (lg(y)>FlxqX_EXTGCD_LIMIT)
    d = FlxqX_extgcd_halfgcd(x, y, T, p, ptu, ptv);
  else
    d = FlxqX_extgcd_basecase(x, y, T, p, ptu, ptv);
  gerepileall(ltop,ptu?3:2,&d,ptv,ptu);
  return d;
}

GEN
FlxqX_safegcd(GEN P, GEN Q, GEN T, ulong p)
{
  pari_sp av = avma;
  GEN U;
  if (!signe(P)) return gcopy(Q);
  if (!signe(Q)) return gcopy(P);
  for(;;)
  {
    U = Flxq_invsafe(leading_coeff(Q), T, p);
    if (!U) { avma = av; return NULL; }
    Q = FlxqX_Flxq_mul_to_monic(Q,U,T,p);
    P = FlxqX_rem(P,Q,T,p);
    if (!signe(P)) break;
    if (gc_needed(av, 1))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"FlxqX_safegcd");
      gerepileall(av, 2, &P,&Q);
    }
    swap(P, Q);
  }
  U = Flxq_invsafe(leading_coeff(Q), T, p);
  if (!U) { avma = av; return NULL; }
  Q = FlxqX_Flxq_mul_to_monic(Q,U,T,p);
  return gerepileupto(av, Q);
}

struct _FlxqX {ulong p; GEN T;};
static GEN _FlxqX_mul(void *data,GEN a,GEN b)
{
  struct _FlxqX *d=(struct _FlxqX*)data;
  return FlxqX_mul(a,b,d->T,d->p);
}
static GEN _FlxqX_sqr(void *data,GEN a)
{
  struct _FlxqX *d=(struct _FlxqX*)data;
  return FlxqX_sqr(a,d->T,d->p);
}

GEN
FlxqX_powu(GEN V, ulong n, GEN T, ulong p)
{
  struct _FlxqX d; d.p=p; d.T=T;
  return gen_powu(V, n, (void*)&d, &_FlxqX_sqr, &_FlxqX_mul);
}

GEN
FlxqXV_prod(GEN V, GEN T, ulong p)
{
  struct _FlxqX d; d.p=p; d.T=T;
  return gen_product(V, (void*)&d, &_FlxqX_mul);
}

static GEN
FlxqV_roots_to_deg1(GEN x, GEN T, ulong p, long v)
{
  long sv = get_Flx_var(T);
  pari_APPLY_same(deg1pol_shallow(pol1_Flx(sv),Flx_neg(gel(x,i),p),v))
}

GEN
FlxqV_roots_to_pol(GEN V, GEN T, ulong p, long v)
{
  pari_sp ltop = avma;
  GEN W = FlxqV_roots_to_deg1(V, T, p, v);
  return gerepileupto(ltop, FlxqXV_prod(W, T, p));
}

/*** FlxqM ***/

GEN
FlxqC_Flxq_mul(GEN x, GEN y, GEN T, ulong p)
{ pari_APPLY_type(t_COL, Flxq_mul(gel(x, i), y, T, p)) }

GEN
FlxqM_Flxq_mul(GEN x, GEN y, GEN T, ulong p)
{ pari_APPLY_same(FlxqC_Flxq_mul(gel(x, i), y, T, p)) }

static GEN
kron_pack_Flx_spec_half(GEN x, long l) {
  if (l == 0)
    return gen_0;
  return Flx_to_int_halfspec(x, l);
}

static GEN
kron_pack_Flx_spec(GEN x, long l) {
  long i;
  GEN w, y;
  if (l == 0)
    return gen_0;
  y = cgetipos(l + 2);
  for (i = 0, w = int_LSW(y); i < l; i++, w = int_nextW(w))
    *w = x[i];
  return y;
}

static GEN
kron_pack_Flx_spec_2(GEN x, long l) {
  return Flx_eval2BILspec(x, 2, l);
}

static GEN
kron_pack_Flx_spec_3(GEN x, long l) {
  return Flx_eval2BILspec(x, 3, l);
}

static GEN
kron_pack_Flx_spec_bits(GEN x, long b, long l) {
  GEN y;
  long i;
  if (l == 0)
    return gen_0;
  y = cgetg(l + 1, t_VECSMALL);
  for(i = 1; i <= l; i++)
    y[i] = x[l - i];
  return nv_fromdigits_2k(y, b);
}

static GEN
kron_unpack_Flx(GEN z, ulong p)
{
  long i, l = lgefint(z);
  GEN x = cgetg(l, t_VECSMALL), w;
  for (w = int_LSW(z), i = 2; i < l; w = int_nextW(w), i++)
    x[i] = ((ulong) *w) % p;
  return Flx_renormalize(x, l);
}

static GEN
kron_unpack_Flx_2(GEN x, ulong p) {
  long d = (lgefint(x)-1)/2 - 1;
  return Z_mod2BIL_Flx_2(x, d, p);
}

static GEN
kron_unpack_Flx_3(GEN x, ulong p) {
  long d = lgefint(x)/3 - 1;
  return Z_mod2BIL_Flx_3(x, d, p);
}

/* assume b < BITS_IN_LONG */
static GEN
kron_unpack_Flx_bits_narrow(GEN z, long b, ulong p) {
  GEN v = binary_2k_nv(z, b), x;
  long i, l = lg(v) + 1;
  x = cgetg(l, t_VECSMALL);
  for (i = 2; i < l; i++)
    x[i] = v[l - i] % p;
  return Flx_renormalize(x, l);
}

static GEN
kron_unpack_Flx_bits_wide(GEN z, long b, ulong p, ulong pi) {
  GEN v = binary_2k(z, b), x, y;
  long i, l = lg(v) + 1, ly;
  x = cgetg(l, t_VECSMALL);
  for (i = 2; i < l; i++) {
    y = gel(v, l - i);
    ly = lgefint(y);
    switch (ly) {
    case 2: x[i] = 0; break;
    case 3: x[i] = *int_W_lg(y, 0, ly) % p; break;
    case 4: x[i] = remll_pre(*int_W_lg(y, 1, ly), *int_W_lg(y, 0, ly), p, pi); break;
    case 5: x[i] = remlll_pre(*int_W_lg(y, 2, ly), *int_W_lg(y, 1, ly),
                              *int_W_lg(y, 0, ly), p, pi); break;
    default: x[i] = umodiu(gel(v, l - i), p);
    }
  }
  return Flx_renormalize(x, l);
}

static GEN
FlxM_pack_ZM(GEN M, GEN (*pack)(GEN, long)) {
  long i, j, l, lc;
  GEN N = cgetg_copy(M, &l), x;
  if (l == 1)
    return N;
  lc = lgcols(M);
  for (j = 1; j < l; j++) {
    gel(N, j) = cgetg(lc, t_COL);
    for (i = 1; i < lc; i++) {
      x = gcoeff(M, i, j);
      gcoeff(N, i, j) = pack(x + 2, lgpol(x));
    }
  }
  return N;
}

static GEN
FlxM_pack_ZM_bits(GEN M, long b)
{
  long i, j, l, lc;
  GEN N = cgetg_copy(M, &l), x;
  if (l == 1)
    return N;
  lc = lgcols(M);
  for (j = 1; j < l; j++) {
    gel(N, j) = cgetg(lc, t_COL);
    for (i = 1; i < lc; i++) {
      x = gcoeff(M, i, j);
      gcoeff(N, i, j) = kron_pack_Flx_spec_bits(x + 2, b, lgpol(x));
    }
  }
  return N;
}

static GEN
ZM_unpack_FlxqM(GEN M, GEN T, ulong p, GEN (*unpack)(GEN, ulong))
{
  long i, j, l, lc, sv = get_Flx_var(T);
  GEN N = cgetg_copy(M, &l), x;
  if (l == 1)
    return N;
  lc = lgcols(M);
  for (j = 1; j < l; j++) {
    gel(N, j) = cgetg(lc, t_COL);
    for (i = 1; i < lc; i++) {
      x = unpack(gcoeff(M, i, j), p);
      x[1] = sv;
      gcoeff(N, i, j) = Flx_rem(x, T, p);
    }
  }
  return N;
}

static GEN
ZM_unpack_FlxqM_bits(GEN M, long b, GEN T, ulong p)
{
  long i, j, l, lc, sv = get_Flx_var(T);
  GEN N = cgetg_copy(M, &l), x;
  if (l == 1)
    return N;
  lc = lgcols(M);
  if (b < BITS_IN_LONG) {
    for (j = 1; j < l; j++) {
      gel(N, j) = cgetg(lc, t_COL);
      for (i = 1; i < lc; i++) {
        x = kron_unpack_Flx_bits_narrow(gcoeff(M, i, j), b, p);
        x[1] = sv;
        gcoeff(N, i, j) = Flx_rem(x, T, p);
      }
    }
  } else {
    ulong pi = get_Fl_red(p);
    for (j = 1; j < l; j++) {
      gel(N, j) = cgetg(lc, t_COL);
      for (i = 1; i < lc; i++) {
        x = kron_unpack_Flx_bits_wide(gcoeff(M, i, j), b, p, pi);
        x[1] = sv;
        gcoeff(N, i, j) = Flx_rem(x, T, p);
      }
    }
  }
  return N;
}

GEN
FlxqM_mul_Kronecker(GEN A, GEN B, GEN T, ulong p)
{
  pari_sp av = avma;
  long b, d = degpol(T), n = lg(A) - 1;
  GEN C, D, z;
  GEN (*pack)(GEN, long), (*unpack)(GEN, ulong);
  int is_sqr = A==B;

  z = muliu(muliu(sqru(p - 1), d), n);
  b = expi(z) + 1;
  /* only do expensive bit-packing if it saves at least 1 limb */
  if (b <= BITS_IN_HALFULONG) {
    if (nbits2lg(d*b) - 2 == (d + 1)/2)
      b = BITS_IN_HALFULONG;
  } else {
    long l = lgefint(z) - 2;
    if (nbits2lg(d*b) - 2 == d*l)
      b = l*BITS_IN_LONG;
  }
  avma = av;

  switch (b) {
  case BITS_IN_HALFULONG:
    pack = kron_pack_Flx_spec_half;
    unpack = int_to_Flx_half;
    break;
  case BITS_IN_LONG:
    pack = kron_pack_Flx_spec;
    unpack = kron_unpack_Flx;
    break;
  case 2*BITS_IN_LONG:
    pack = kron_pack_Flx_spec_2;
    unpack = kron_unpack_Flx_2;
    break;
  case 3*BITS_IN_LONG:
    pack = kron_pack_Flx_spec_3;
    unpack = kron_unpack_Flx_3;
    break;
  default:
    A = FlxM_pack_ZM_bits(A, b);
    B = is_sqr? A: FlxM_pack_ZM_bits(B, b);
    C = ZM_mul(A, B);
    D = ZM_unpack_FlxqM_bits(C, b, T, p);
    return gerepilecopy(av, D);
  }
  A = FlxM_pack_ZM(A, pack);
  B = is_sqr? A: FlxM_pack_ZM(B, pack);
  C = ZM_mul(A, B);
  D = ZM_unpack_FlxqM(C, T, p, unpack);
  return gerepilecopy(av, D);
}

/*******************************************************************/
/*                                                                 */
/*                       (Fl[X]/T(X))[Y] / S(Y)                    */
/*                                                                 */
/*******************************************************************/

GEN
FlxqXQ_mul(GEN x, GEN y, GEN S, GEN T, ulong p) {
  return FlxqX_rem(FlxqX_mul(x,y,T,p),S,T,p);
}

GEN
FlxqXQ_sqr(GEN x, GEN S, GEN T, ulong p) {
  return FlxqX_rem(FlxqX_sqr(x,T,p),S,T,p);
}

GEN
FlxqXQ_invsafe(GEN x, GEN S, GEN T, ulong p)
{
  GEN V, z = FlxqX_extgcd(get_FlxqX_mod(S), x, T, p, NULL, &V);
  if (degpol(z)) return NULL;
  z = Flxq_invsafe(gel(z,2),T,p);
  if (!z) return NULL;
  return FlxqX_Flxq_mul(V, z, T, p);
}

GEN
FlxqXQ_inv(GEN x, GEN S, GEN T,ulong p)
{
  pari_sp av = avma;
  GEN U = FlxqXQ_invsafe(x, S, T, p);
  if (!U) pari_err_INV("FlxqXQ_inv",x);
  return gerepileupto(av, U);
}

GEN
FlxqXQ_div(GEN x, GEN y, GEN S, GEN T, ulong p) {
  return FlxqXQ_mul(x, FlxqXQ_inv(y,S,T,p),S,T,p);
}

struct _FlxqXQ {
  GEN T, S;
  ulong p;
};
static GEN
_FlxqXQ_add(void *data, GEN x, GEN y) {
  struct _FlxqXQ *d = (struct _FlxqXQ*) data;
  return FlxX_add(x,y, d->p);
}
static GEN
_FlxqXQ_sub(void *data, GEN x, GEN y) {
  struct _FlxqXQ *d = (struct _FlxqXQ*) data;
  return FlxX_sub(x,y, d->p);
}
static GEN
_FlxqXQ_cmul(void *data, GEN P, long a, GEN x) {
  struct _FlxqXQ *d = (struct _FlxqXQ*) data;
  return FlxX_Flx_mul(x,gel(P,a+2), d->p);
}
static GEN
_FlxqXQ_red(void *data, GEN x) {
  struct _FlxqXQ *d = (struct _FlxqXQ*) data;
  return FlxqX_red(x, d->T, d->p);
}
static GEN
_FlxqXQ_mul(void *data, GEN x, GEN y) {
  struct _FlxqXQ *d = (struct _FlxqXQ*) data;
  return FlxqXQ_mul(x,y, d->S,d->T, d->p);
}
static GEN
_FlxqXQ_sqr(void *data, GEN x) {
  struct _FlxqXQ *d = (struct _FlxqXQ*) data;
  return FlxqXQ_sqr(x, d->S,d->T, d->p);
}

static GEN
_FlxqXQ_one(void *data) {
  struct _FlxqXQ *d = (struct _FlxqXQ*) data;
  return pol1_FlxX(get_FlxqX_var(d->S),get_Flx_var(d->T));
}

static GEN
_FlxqXQ_zero(void *data) {
  struct _FlxqXQ *d = (struct _FlxqXQ*) data;
  return pol_0(get_FlxqX_var(d->S));
}

static struct bb_algebra FlxqXQ_algebra = { _FlxqXQ_red, _FlxqXQ_add,
       _FlxqXQ_sub, _FlxqXQ_mul, _FlxqXQ_sqr, _FlxqXQ_one, _FlxqXQ_zero };

const struct bb_algebra *
get_FlxqXQ_algebra(void **E, GEN S, GEN T, ulong p)
{
  GEN z = new_chunk(sizeof(struct _FlxqXQ));
  struct _FlxqXQ *e = (struct _FlxqXQ *) z;
  e->T = Flx_get_red(T, p);
  e->S = FlxqX_get_red(S, e->T, p);
  e->p  = p; *E = (void*)e;
  return &FlxqXQ_algebra;
}

/* x over Fq, return lift(x^n) mod S */
GEN
FlxqXQ_pow(GEN x, GEN n, GEN S, GEN T, ulong p)
{
  struct _FlxqXQ D;
  long s = signe(n);
  if (!s) return pol1_FlxX(get_FlxqX_var(S),get_Flx_var(T));
  if (s < 0) x = FlxqXQ_inv(x,S,T,p);
  if (is_pm1(n)) return s < 0 ? x : gcopy(x);
  if (degpol(x) >= get_FlxqX_degree(S)) x = FlxqX_rem(x,S,T,p);
  T = Flx_get_red(T, p);
  S = FlxqX_get_red(S, T, p);
  D.S = S;
  D.T = T;
  D.p = p;
  return gen_pow(x, n, (void*)&D, &_FlxqXQ_sqr, &_FlxqXQ_mul);
}

/* x over Fq, return lift(x^n) mod S */
GEN
FlxqXQ_powu(GEN x, ulong n, GEN S, GEN T, ulong p)
{
  struct _FlxqXQ D;
  switch(n)
  {
    case 0: return pol1_FlxX(get_FlxqX_var(S),get_Flx_var(T));
    case 1: return gcopy(x);
    case 2: return FlxqXQ_sqr(x, S, T, p);
  }
  T = Flx_get_red(T, p);
  S = FlxqX_get_red(S, T, p);
  D.S = S; D.T = T; D.p = p;
  return gen_powu(x, n, (void*)&D, &_FlxqXQ_sqr, &_FlxqXQ_mul);
}

GEN
FlxqXQ_powers(GEN x, long l, GEN S, GEN T, ulong p)
{
  struct _FlxqXQ D;
  int use_sqr = 2*degpol(x) >= get_FlxqX_degree(S);
  T = Flx_get_red(T, p);
  S = FlxqX_get_red(S, T, p);
  D.S = S; D.T = T; D.p = p;
  return gen_powers(x, l, use_sqr, (void*)&D, &_FlxqXQ_sqr, &_FlxqXQ_mul,&_FlxqXQ_one);
}

static GEN
FlxqXn_mul(GEN a, GEN b, long n, GEN T, ulong p)
{
  return RgXn_red_shallow(FlxqX_mul(a, b, T, p), n);
}

/* Let v a linear form, return the linear form z->v(tau*z)
   that is, v*(M_tau) */

static GEN
FlxqXQ_transmul_init(GEN tau, GEN S, GEN T, ulong p)
{
  GEN bht;
  GEN h, Sp = get_FlxqX_red(S, &h);
  long n = degpol(Sp), vS = varn(Sp), vT = get_Flx_var(T);
  GEN ft = FlxX_recipspec(Sp+2, n+1, n+1, vT);
  GEN bt = FlxX_recipspec(tau+2, lgpol(tau), n, vT);
  setvarn(ft, vS); setvarn(bt, vS);
  if (h)
    bht = FlxqXn_mul(bt, h, n-1, T, p);
  else
  {
    GEN bh = FlxqX_div(RgX_shift_shallow(tau, n-1), S, T, p);
    bht = FlxX_recipspec(bh+2, lgpol(bh), n-1, vT);
    setvarn(bht, vS);
  }
  return mkvec3(bt, bht, ft);
}

static GEN
FlxqXQ_transmul(GEN tau, GEN a, long n, GEN T, ulong p)
{
  pari_sp ltop = avma;
  GEN t1, t2, t3, vec;
  GEN bt = gel(tau, 1), bht = gel(tau, 2), ft = gel(tau, 3);
  if (signe(a)==0) return pol_0(varn(a));
  t2 = RgX_shift_shallow(FlxqX_mul(bt, a, T, p),1-n);
  if (signe(bht)==0) return gerepilecopy(ltop, t2);
  t1 = RgX_shift_shallow(FlxqX_mul(ft, a, T, p),-n);
  t3 = FlxqXn_mul(t1, bht, n-1, T, p);
  vec = FlxX_sub(t2, RgX_shift_shallow(t3, 1), p);
  return gerepileupto(ltop, vec);
}

static GEN
polxn_FlxX(long n, long v, long vT)
{
  long i, a = n+2;
  GEN p = cgetg(a+1, t_POL);
  p[1] = evalsigne(1)|evalvarn(v);
  for (i = 2; i < a; i++) gel(p,i) = pol0_Flx(vT);
  gel(p,a) = pol1_Flx(vT); return p;
}

GEN
FlxqXQ_minpoly(GEN x, GEN S, GEN T, ulong p)
{
  pari_sp ltop = avma;
  long vS, vT, n;
  GEN v_x, g, tau;
  vS = get_FlxqX_var(S);
  vT = get_Flx_var(T);
  n = get_FlxqX_degree(S);
  g = pol1_FlxX(vS,vT);
  tau = pol1_FlxX(vS,vT);
  S = FlxqX_get_red(S, T, p);
  v_x = FlxqXQ_powers(x, usqrt(2*n), S, T, p);
  while(signe(tau) != 0)
  {
    long i, j, m, k1;
    GEN M, v, tr;
    GEN g_prime, c;
    if (degpol(g) == n) { tau = pol1_FlxX(vS, vT); g = pol1_FlxX(vS, vT); }
    v = random_FlxqX(n, vS, T, p);
    tr = FlxqXQ_transmul_init(tau, S, T, p);
    v = FlxqXQ_transmul(tr, v, n, T, p);
    m = 2*(n-degpol(g));
    k1 = usqrt(m);
    tr = FlxqXQ_transmul_init(gel(v_x,k1+1), S, T, p);
    c = cgetg(m+2,t_POL);
    c[1] = evalsigne(1)|evalvarn(vS);
    for (i=0; i<m; i+=k1)
    {
      long mj = minss(m-i, k1);
      for (j=0; j<mj; j++)
        gel(c,m+1-(i+j)) = FlxqX_dotproduct(v, gel(v_x,j+1), T, p);
      v = FlxqXQ_transmul(tr, v, n, T, p);
    }
    c = FlxX_renormalize(c, m+2);
    /* now c contains <v,x^i> , i = 0..m-1  */
    M = FlxqX_halfgcd(polxn_FlxX(m, vS, vT), c, T, p);
    g_prime = gmael(M, 2, 2);
    if (degpol(g_prime) < 1) continue;
    g = FlxqX_mul(g, g_prime, T, p);
    tau = FlxqXQ_mul(tau, FlxqX_FlxqXQV_eval(g_prime, v_x, S, T, p), S, T, p);
  }
  g = FlxqX_normalize(g,T, p);
  return gerepilecopy(ltop,g);
}

GEN
FlxqXQ_matrix_pow(GEN y, long n, long m, GEN S, GEN T, ulong p)
{
  return FlxXV_to_FlxM(FlxqXQ_powers(y,m-1,S,T,p), n, T[1]);
}

GEN
FlxqX_FlxqXQV_eval(GEN P, GEN V, GEN S, GEN T, ulong p)
{
  struct _FlxqXQ D;
  T = Flx_get_red(T, p);
  S = FlxqX_get_red(S, T, p);
  D.S=S; D.T=T; D.p=p;
  return gen_bkeval_powers(P, degpol(P), V, (void*)&D, &FlxqXQ_algebra,
                                                   _FlxqXQ_cmul);
}

GEN
FlxqX_FlxqXQ_eval(GEN Q, GEN x, GEN S, GEN T, ulong p)
{
  struct _FlxqXQ D;
  int use_sqr = 2*degpol(x) >= get_FlxqX_degree(S);
  T = Flx_get_red(T, p);
  S = FlxqX_get_red(S, T, p);
  D.S=S; D.T=T; D.p=p;
  return gen_bkeval(Q, degpol(Q), x, use_sqr, (void*)&D, &FlxqXQ_algebra,
                                                    _FlxqXQ_cmul);
}

static GEN
FlxqXQ_autpow_sqr(void * E, GEN x)
{
  struct _FlxqXQ *D = (struct _FlxqXQ *)E;
  GEN S = D->S, T = D->T;
  ulong p = D->p;
  GEN phi = gel(x,1), S1 = gel(x,2);
  long n = brent_kung_optpow(get_Flx_degree(T)-1,lgpol(S1)+1,1);
  GEN V = Flxq_powers(phi, n, T, p);
  GEN phi2 = Flx_FlxqV_eval(phi, V, T, p);
  GEN Sphi = FlxY_FlxqV_evalx(S1, V, T, p);
  GEN S2 = FlxqX_FlxqXQ_eval(Sphi, S1, S, T, p);
  return mkvec2(phi2, S2);
}

static GEN
FlxqXQ_autpow_mul(void * E, GEN x, GEN y)
{
  struct _FlxqXQ *D = (struct _FlxqXQ *)E;
  GEN S = D->S, T = D->T;
  ulong p = D->p;
  GEN phi1 = gel(x,1), S1 = gel(x,2);
  GEN phi2 = gel(y,1), S2 = gel(y,2);
  long n = brent_kung_optpow(get_Flx_degree(T)-1,lgpol(S1)+1,1);
  GEN V = Flxq_powers(phi2, n, T, p);
  GEN phi3 = Flx_FlxqV_eval(phi1, V, T, p);
  GEN Sphi = FlxY_FlxqV_evalx(S1, V, T, p);
  GEN S3 = FlxqX_FlxqXQ_eval(Sphi, S2, S, T, p);
  return mkvec2(phi3, S3);
}

GEN
FlxqXQ_autpow(GEN aut, long n, GEN S, GEN T, ulong p)
{
  struct _FlxqXQ D;
  T = Flx_get_red(T, p);
  S = FlxqX_get_red(S, T, p);
  D.S=S; D.T=T; D.p=p;
  return gen_powu(aut,n,&D,FlxqXQ_autpow_sqr,FlxqXQ_autpow_mul);
}

static GEN
FlxqXQ_autsum_mul(void *E, GEN x, GEN y)
{
  struct _FlxqXQ *D = (struct _FlxqXQ *)E;
  GEN S = D->S, T = D->T;
  ulong p = D->p;
  GEN phi1 = gel(x,1), S1 = gel(x,2), a1 = gel(x,3);
  GEN phi2 = gel(y,1), S2 = gel(y,2), a2 = gel(y,3);
  long n2 = brent_kung_optpow(get_Flx_degree(T)-1, lgpol(S1)+lgpol(a1)+1,1);
  GEN V2 = Flxq_powers(phi2, n2, T, p);
  GEN phi3 = Flx_FlxqV_eval(phi1, V2, T, p);
  GEN Sphi = FlxY_FlxqV_evalx(S1, V2, T, p);
  GEN aphi = FlxY_FlxqV_evalx(a1, V2, T, p);
  long n = brent_kung_optpow(maxss(degpol(Sphi),degpol(aphi)),2,1);
  GEN V = FlxqXQ_powers(S2, n, S, T, p);
  GEN S3 = FlxqX_FlxqXQV_eval(Sphi, V, S, T, p);
  GEN aS = FlxqX_FlxqXQV_eval(aphi, V, S, T, p);
  GEN a3 = FlxqXQ_mul(aS, a2, S, T, p);
  return mkvec3(phi3, S3, a3);
}

static GEN
FlxqXQ_autsum_sqr(void * T, GEN x)
{ return FlxqXQ_autsum_mul(T, x, x); }

GEN
FlxqXQ_autsum(GEN aut, long n, GEN S, GEN T, ulong p)
{
  struct _FlxqXQ D;
  T = Flx_get_red(T, p);
  S = FlxqX_get_red(S, T, p);
  D.S=S; D.T=T; D.p=p;
  return gen_powu(aut,n,&D,FlxqXQ_autsum_sqr,FlxqXQ_autsum_mul);
}

static GEN
FlxqXQ_auttrace_mul(void *E, GEN x, GEN y)
{
  struct _FlxqXQ *D = (struct _FlxqXQ *)E;
  GEN S = D->S, T = D->T;
  ulong p = D->p;
  GEN S1 = gel(x,1), a1 = gel(x,2);
  GEN S2 = gel(y,1), a2 = gel(y,2);
  long n = brent_kung_optpow(maxss(degpol(S1),degpol(a1)),2,1);
  GEN V = FlxqXQ_powers(S2, n, S, T, p);
  GEN S3 = FlxqX_FlxqXQV_eval(S1, V, S, T, p);
  GEN aS = FlxqX_FlxqXQV_eval(a1, V, S, T, p);
  GEN a3 = FlxX_add(aS, a2, p);
  return mkvec2(S3, a3);
}

static GEN
FlxqXQ_auttrace_sqr(void *E, GEN x)
{ return FlxqXQ_auttrace_mul(E, x, x); }

GEN
FlxqXQ_auttrace(GEN x, ulong n, GEN S, GEN T, ulong p)
{
  struct _FlxqXQ D;
  T = Flx_get_red(T, p);
  S = FlxqX_get_red(S, T, p);
  D.S=S; D.T=T; D.p=p;
  return gen_powu(x,n,(void*)&D,FlxqXQ_auttrace_sqr,FlxqXQ_auttrace_mul);
}

/*******************************************************************/
/*                                                                 */
/*                      FlxYqQ                                     */
/*                                                                 */
/*******************************************************************/

/*Preliminary implementation to speed up FpX_ffisom*/
typedef struct {
  GEN S, T;
  ulong p;
} FlxYqq_muldata;

/* reduce x in Fl[X, Y] in the algebra Fl[X, Y]/ (P(X),Q(Y)) */
static GEN
FlxYqq_redswap(GEN x, GEN S, GEN T, ulong p)
{
  pari_sp ltop=avma;
  long n = get_Flx_degree(S);
  long m = get_Flx_degree(T);
  long w = get_Flx_var(T);
  GEN V = FlxX_swap(x,m,w);
  V = FlxqX_red(V,S,p);
  V = FlxX_swap(V,n,w);
  return gerepilecopy(ltop,V);
}
static GEN
FlxYqq_sqr(void *data, GEN x)
{
  FlxYqq_muldata *D = (FlxYqq_muldata*)data;
  return FlxYqq_redswap(FlxqX_sqr(x, D->T, D->p),D->S,D->T,D->p);
}

static GEN
FlxYqq_mul(void *data, GEN x, GEN y)
{
  FlxYqq_muldata *D = (FlxYqq_muldata*)data;
  return FlxYqq_redswap(FlxqX_mul(x,y, D->T, D->p),D->S,D->T,D->p);
}

/* x in Z[X,Y], S in Z[X] over Fq = Z[Y]/(p,T); compute lift(x^n mod (S,T,p)) */
GEN
FlxYqq_pow(GEN x, GEN n, GEN S, GEN T, ulong p)
{
  pari_sp av = avma;
  FlxYqq_muldata D;
  GEN y;
  D.S = S;
  D.T = T;
  D.p = p;
  y = gen_pow(x, n, (void*)&D, &FlxYqq_sqr, &FlxYqq_mul);
  return gerepileupto(av, y);
}
