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

/*******************************************************************/
/*                                                                 */
/*                                ZX                               */
/*                                                                 */
/*******************************************************************/
void
RgX_check_QX(GEN x, const char *s)
{ if (!RgX_is_QX(x)) pari_err_TYPE(stack_strcat(s," [not in Q[X]]"), x); }
void
RgX_check_ZX(GEN x, const char *s)
{ if (!RgX_is_ZX(x)) pari_err_TYPE(stack_strcat(s," [not in Z[X]]"), x); }
long
ZX_max_lg(GEN x)
{
  long i, prec = 0, lx = lg(x);

  for (i=2; i<lx; i++) { long l = lgefint(gel(x,i)); if (l > prec) prec = l; }
  return prec;
}

GEN
ZX_add(GEN x, GEN y)
{
  long lx,ly,i;
  GEN z;
  lx = lg(x); ly = lg(y); if (lx < ly) swapspec(x,y, lx,ly);
  z = cgetg(lx,t_POL); z[1] = x[1];
  for (i=2; i<ly; i++) gel(z,i) = addii(gel(x,i),gel(y,i));
  for (   ; i<lx; i++) gel(z,i) = icopy(gel(x,i));
  if (lx == ly) z = ZX_renormalize(z, lx);
  if (!lgpol(z)) { avma = (pari_sp)(z + lx); return pol_0(varn(x)); }
  return z;
}

GEN
ZX_sub(GEN x,GEN y)
{
  long i, lx = lg(x), ly = lg(y);
  GEN z;
  if (lx >= ly)
  {
    z = cgetg(lx,t_POL); z[1] = x[1];
    for (i=2; i<ly; i++) gel(z,i) = subii(gel(x,i),gel(y,i));
    if (lx == ly)
    {
      z = ZX_renormalize(z, lx);
      if (!lgpol(z)) { avma = (pari_sp)(z + lx); z = pol_0(varn(x)); }
    }
    else
      for (   ; i<lx; i++) gel(z,i) = icopy(gel(x,i));
  }
  else
  {
    z = cgetg(ly,t_POL); z[1] = y[1];
    for (i=2; i<lx; i++) gel(z,i) = subii(gel(x,i),gel(y,i));
    for (   ; i<ly; i++) gel(z,i) = negi(gel(y,i));
  }
  return z;
}

GEN
ZX_neg(GEN x)
{
  long i, l = lg(x);
  GEN y = cgetg(l,t_POL);
  y[1] = x[1]; for(i=2; i<l; i++) gel(y,i) = negi(gel(x,i));
  return y;
}
GEN
ZX_copy(GEN x)
{
  long i, l = lg(x);
  GEN y = cgetg(l, t_POL);
  y[1] = x[1];
  for (i=2; i<l; i++)
  {
    GEN c = gel(x,i);
    gel(y,i) = lgefint(c) == 2? gen_0: icopy(c);
  }
  return y;
}

GEN
scalar_ZX(GEN x, long v)
{
  GEN z;
  if (!signe(x)) return pol_0(v);
  z = cgetg(3, t_POL);
  z[1] = evalsigne(1) | evalvarn(v);
  gel(z,2) = icopy(x); return z;
}

GEN
scalar_ZX_shallow(GEN x, long v)
{
  GEN z;
  if (!signe(x)) return pol_0(v);
  z = cgetg(3, t_POL);
  z[1] = evalsigne(1) | evalvarn(v);
  gel(z,2) = x; return z;
}

GEN
ZX_Z_add(GEN y, GEN x)
{
  long lz, i;
  GEN z = cgetg_copy(y, &lz);
  if (lz == 2) { avma = (pari_sp)(z + 2); return scalar_ZX(x,varn(y)); }
  z[1] = y[1];
  gel(z,2) = addii(gel(y,2),x);
  for(i=3; i<lz; i++) gel(z,i) = icopy(gel(y,i));
  if (lz==3) z = ZX_renormalize(z,lz);
  return z;
}
GEN
ZX_Z_add_shallow(GEN y, GEN x)
{
  long lz, i;
  GEN z = cgetg_copy(y, &lz);
  if (lz == 2) { avma = (pari_sp)(z + 2); return scalar_ZX_shallow(x,varn(y)); }
  z[1] = y[1];
  gel(z,2) = addii(gel(y,2),x);
  for(i=3; i<lz; i++) gel(z,i) = gel(y,i);
  if (lz==3) z = ZX_renormalize(z,lz);
  return z;
}

GEN
ZX_Z_sub(GEN y, GEN x)
{
  long lz, i;
  GEN z = cgetg_copy(y, &lz);
  if (lz == 2)
  { /* scalarpol(negi(x), v) */
    long v = varn(y);
    avma = (pari_sp)(z + 2);
    if (!signe(x)) return pol_0(v);
    z = cgetg(3,t_POL);
    z[1] = evalvarn(v) | evalsigne(1);
    gel(z,2) = negi(x); return z;
  }
  z[1] = y[1];
  gel(z,2) = subii(gel(y,2),x);
  for(i=3; i<lz; i++) gel(z,i) = icopy(gel(y,i));
  if (lz==3) z = ZX_renormalize(z,lz);
  return z;
}

GEN
Z_ZX_sub(GEN x, GEN y)
{
  long lz, i;
  GEN z = cgetg_copy(y, &lz);
  if (lz == 2) { avma = (pari_sp)(z + 2); return scalar_ZX(x,varn(y)); }
  z[1] = y[1];
  gel(z,2) = subii(x, gel(y,2));
  for(i=3; i<lz; i++) gel(z,i) = negi(gel(y,i));
  if (lz==3) z = ZX_renormalize(z,lz);
  return z;
}

GEN
ZX_Z_divexact(GEN y,GEN x)
{
  long i, l = lg(y);
  GEN z = cgetg(l,t_POL); z[1] = y[1];
  for(i=2; i<l; i++) gel(z,i) = diviiexact(gel(y,i),x);
  return z;
}

GEN
ZX_Z_mul(GEN y,GEN x)
{
  GEN z;
  long i, l;
  if (!signe(x)) return pol_0(varn(y));
  l = lg(y); z = cgetg(l,t_POL); z[1] = y[1];
  for(i=2; i<l; i++) gel(z,i) = mulii(gel(y,i),x);
  return z;
}

GEN
ZX_mulu(GEN y, ulong x)
{
  GEN z;
  long i, l;
  if (!x) return pol_0(varn(y));
  l = lg(y); z = cgetg(l,t_POL); z[1] = y[1];
  for(i=2; i<l; i++) gel(z,i) = mului(x,gel(y,i));
  return z;
}

GEN
ZX_shifti(GEN y, long n)
{
  GEN z;
  long i, l;
  l = lg(y); z = cgetg(l,t_POL); z[1] = y[1];
  for(i=2; i<l; i++) gel(z,i) = shifti(gel(y,i),n);
  return ZX_renormalize(z,l);
}

GEN
ZX_remi2n(GEN y, long n)
{
  GEN z;
  long i, l;
  l = lg(y); z = cgetg(l,t_POL); z[1] = y[1];
  for(i=2; i<l; i++) gel(z,i) = remi2n(gel(y,i),n);
  return ZX_renormalize(z,l);
}

GEN
ZXT_remi2n(GEN z, long n)
{
  if (typ(z) == t_POL)
    return ZX_remi2n(z, n);
  else
  {
    long i,l = lg(z);
    GEN x = cgetg(l, t_VEC);
    for (i=1; i<l; i++) gel(x,i) = ZXT_remi2n(gel(z,i), n);
    return x;
  }
}

GEN
zx_to_ZX(GEN z)
{
  long i, l = lg(z);
  GEN x = cgetg(l,t_POL);
  for (i=2; i<l; i++) gel(x,i) = stoi(z[i]);
  x[1] = evalsigne(l-2!=0)| z[1]; return x;
}

GEN
ZX_deriv(GEN x)
{
  long i,lx = lg(x)-1;
  GEN y;

  if (lx<3) return pol_0(varn(x));
  y = cgetg(lx,t_POL);
  for (i=2; i<lx ; i++) gel(y,i) = mului(i-1,gel(x,i+1));
  y[1] = x[1]; return y;
}

int
ZX_equal(GEN V, GEN W)
{
  long i, l = lg(V);
  if (lg(W) != l) return 0;
  for (i = 2; i < l; i++)
    if (!equalii(gel(V,i), gel(W,i))) return 0;
  return 1;
}

static long
ZX_valspec(GEN x, long nx)
{
  long vx;
  for (vx = 0; vx<nx ; vx++)
    if (signe(gel(x,vx))) break;
  return vx;
}

long
ZX_val(GEN x)
{
  long vx;
  if (!signe(x)) return LONG_MAX;
  for (vx = 0;; vx++)
    if (signe(gel(x,2+vx))) break;
  return vx;
}
long
ZX_valrem(GEN x, GEN *Z)
{
  long vx;
  if (!signe(x)) { *Z = pol_0(varn(x)); return LONG_MAX; }
  for (vx = 0;; vx++)
    if (signe(gel(x,2+vx))) break;
  *Z = RgX_shift_shallow(x, -vx);
  return vx;
}

GEN
ZX_div_by_X_1(GEN a, GEN *r)
{
  long l = lg(a), i;
  GEN a0, z0, z = cgetg(l-1, t_POL);
  z[1] = a[1];
  a0 = a + l-1;
  z0 = z + l-2; *z0 = *a0--;
  for (i=l-3; i>1; i--) /* z[i] = a[i+1] + z[i+1] */
  {
    GEN t = addii(gel(a0--,0), gel(z0--,0));
    gel(z0,0) = t;
  }
  if (r) *r = addii(gel(a0,0), gel(z0,0));
  return z;
}

/* Return 2^(n degpol(P))  P(x >> n), not memory clean if P is a ZX */
GEN
ZX_rescale2n(GEN P, long n)
{
  long i, l = lg(P), ni = n;
  GEN Q = cgetg(l,t_POL);
  Q[l-1] = P[l-1];
  for (i=l-2; i>=2; i--)
  {
    gel(Q,i) = shifti(gel(P,i), ni);
    ni += n;
  }
  Q[1] = P[1]; return Q;
}

/* Return h^deg(P) P(x / h), not memory clean. h integer, P ZX */
GEN
ZX_rescale(GEN P, GEN h)
{
  long l = lg(P);
  GEN Q = cgetg(l,t_POL);
  if (l != 2)
  {
    long i = l-1;
    GEN hi = h;
    gel(Q,i) = gel(P,i);
    if (l != 3) { i--; gel(Q,i) = mulii(gel(P,i), h); }
    for (i--; i>=2; i--) { hi = mulii(hi,h); gel(Q,i) = mulii(gel(P,i), hi); }
  }
  Q[1] = P[1]; return Q;
}
/* Return h^(deg(P)-1) P(x / h), P!=0, h=lt(P), memory unclean; monic result */
GEN
ZX_rescale_lt(GEN P)
{
  long l = lg(P);
  GEN Q = cgetg(l,t_POL);
  gel(Q,l-1) = gen_1;
  if (l != 3)
  {
    long i = l-1;
    GEN h = gel(P,i), hi = h;
    i--; gel(Q,i) = gel(P,i);
    if (l != 4) { i--; gel(Q,i) = mulii(gel(P,i), h); }
    for (i--; i>=2; i--) { hi = mulii(hi,h); gel(Q,i) = mulii(gel(P,i), hi); }
  }
  Q[1] = P[1]; return Q;
}


/*Eval x in 2^(k*BIL) in linear time*/
static GEN
ZX_eval2BILspec(GEN x, long k, long nx)
{
  pari_sp av = avma;
  long i,j, lz = k*nx, ki;
  GEN pz = cgetipos(2+lz);
  GEN nz = cgetipos(2+lz);
  for(i=0; i < lz; i++)
  {
    *int_W(pz,i) = 0UL;
    *int_W(nz,i) = 0UL;
  }
  for(i=0, ki=0; i<nx; i++, ki+=k)
  {
    GEN c = gel(x,i);
    long lc = lgefint(c)-2;
    if (signe(c)==0) continue;
    if (signe(c) > 0)
      for (j=0; j<lc; j++) *int_W(pz,j+ki) = *int_W(c,j);
    else
      for (j=0; j<lc; j++) *int_W(nz,j+ki) = *int_W(c,j);
  }
  pz = int_normalize(pz,0);
  nz = int_normalize(nz,0); return gerepileuptoint(av, subii(pz,nz));
}

static long
ZX_expispec(GEN x, long nx)
{
  long i, m = 0;
  for(i = 0; i < nx; i++)
  {
    long e = expi(gel(x,i));
    if (e > m) m = e;
  }
  return m;
}

static GEN
Z_mod2BIL_ZX(GEN x, long bs, long d, long vx)
{
  long i, offset, lm = lgefint(x)-2, l = d+vx+3, sx = signe(x);
  GEN s1 = int2n(bs*BITS_IN_LONG), pol = cgetg(l, t_POL);
  int carry = 0;
  pol[1] = evalsigne(1);
  for (i=0; i<vx; i++) gel(pol,i+2) = gen_0;
  for (offset=0; i <= d+vx; i++, offset += bs)
  {
    pari_sp av = avma;
    long lz = minss(bs, lm-offset);
    GEN z = lz > 0 ?adduispec_offset(carry, x, offset, lz): utoi(carry);
    if (lgefint(z) == 3+bs) { carry = 1; z = gen_0;}
    else
    {
      carry = (lgefint(z) == 2+bs && (HIGHBIT & *int_W(z,bs-1)));
      if (carry)
        z = gerepileuptoint(av, (sx==-1)? subii(s1,z): subii(z,s1));
      else if (sx==-1) togglesign(z);
    }
    gel(pol,i+2) = z;
  }
  return ZX_renormalize(pol,l);
}

static GEN
ZX_sqrspec_sqri(GEN x, long nx, long ex, long v)
{
  long e = 2*ex + expu(nx) + 3;
  long N = divsBIL(e)+1;
  GEN  z = sqri(ZX_eval2BILspec(x,N,nx));
  return Z_mod2BIL_ZX(z, N, nx*2-2, v);
}

static GEN
ZX_mulspec_mulii(GEN x, GEN y, long nx, long ny, long ex, long ey, long v)
{
  long e = ex + ey + expu(minss(nx,ny)) + 3;
  long N = divsBIL(e)+1;
  GEN  z = mulii(ZX_eval2BILspec(x,N,nx), ZX_eval2BILspec(y,N,ny));
  return Z_mod2BIL_ZX(z, N, nx+ny-2, v);
}

INLINE GEN
ZX_sqrspec_basecase_limb(GEN x, long a, long i)
{
  pari_sp av = avma;
  GEN s = gen_0;
  long j, l = (i+1)>>1;
  for (j=a; j<l; j++)
  {
    GEN xj = gel(x,j), xx = gel(x,i-j);
    if (signe(xj) && signe(xx))
      s = addii(s, mulii(xj, xx));
  }
  s = shifti(s,1);
  if ((i&1) == 0)
  {
    GEN t = gel(x, i>>1);
    if (signe(t))
      s = addii(s, sqri(t));
  }
  return gerepileuptoint(av,s);
}

static GEN
ZX_sqrspec_basecase(GEN x, long nx, long v)
{
  long i, lz, nz;
  GEN z;

  lz = (nx << 1) + 1; nz = lz-2;
  lz += v;
  z = cgetg(lz,t_POL); z[1] = evalsigne(1); z += 2;
  for (i=0; i<v; i++) gel(z++, 0) = gen_0;
  for (i=0; i<nx; i++)
    gel(z,i) = ZX_sqrspec_basecase_limb(x, 0, i);
  for (  ; i<nz; i++) gel(z,i) = ZX_sqrspec_basecase_limb(x, i-nx+1, i);
  z -= v+2; return z;
}

static GEN
Z_sqrshiftspec_ZX(GEN x, long vx)
{
  long i, nz = 2*vx+1;
  GEN z = cgetg(2+nz, t_POL);
  z[1] = evalsigne(1);
  for(i=2;i<nz+1;i++) gel(z,i) = gen_0;
  gel(z,nz+1) = sqri(x);
  return z;
}

static GEN
Z_ZX_mulshiftspec(GEN x, GEN y, long ny, long vz)
{
  long i, nz = vz+ny;
  GEN z = cgetg(2+nz, t_POL);
  z[1] = evalsigne(1);
  for (i=0; i<vz; i++)   gel(z,i+2)    = gen_0;
  for (i=0; i<ny; i++) gel(z,i+vz+2) = mulii(x, gel(y,i));
  return z;
}

GEN
ZX_sqrspec(GEN x, long nx)
{
#ifdef PARI_KERNEL_GMP
  const long low[]={ 17, 32, 96, 112, 160, 128, 128, 160, 160, 160, 160, 160, 176, 192, 192, 192, 192, 192, 224, 224, 224, 240, 240, 240, 272, 288, 288, 240, 288, 304, 304, 304, 304, 304, 304, 352, 352, 368, 352, 352, 352, 368, 368, 432, 432, 496, 432, 496, 496};
  const long high[]={ 102860, 70254, 52783, 27086, 24623, 18500, 15289, 13899, 12635, 11487, 10442, 9493, 8630, 7845, 7132, 7132, 6484, 6484, 5894, 5894, 4428, 4428, 3660, 4428, 3660, 3660, 2749, 2499, 2272, 2066, 1282, 1282, 1166, 1166, 1166, 1166, 1166, 1166, 1166, 963, 963, 724, 658, 658, 658, 528, 528, 528, 528};
#else
  const long low[]={ 17, 17, 32, 32, 96, 96, 96, 96, 96, 96, 96, 96, 96, 96, 112, 112, 128, 112, 112, 112, 112, 112, 128, 128, 160, 160, 112, 128, 128, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 176, 160, 160, 176, 160, 160, 176, 176, 208, 176, 176, 176, 192, 192, 176, 176, 224, 176, 224, 224, 176, 224, 224, 224, 176, 176, 176, 176, 176, 176, 176, 176, 224, 176, 176, 224, 224, 224, 224, 224, 224, 224, 240, 288, 240, 288, 288, 240, 288, 288, 240, 240, 304, 304};
  const long high[]={ 165657, 85008, 52783, 43622, 32774, 27086, 22385, 15289, 13899, 12635, 11487, 10442, 9493, 7845, 6484, 6484, 5894, 5894, 4871, 4871, 4428, 4026, 3660, 3660, 3660, 3327, 3327, 3024, 2749, 2749, 2272, 2749, 2499, 2499, 2272, 1878, 1878, 1878, 1707, 1552, 1552, 1552, 1552, 1552, 1411, 1411, 1411, 1282, 1282, 1282, 1282, 1282, 1166, 1166, 1166, 1166, 1166, 1166, 1166, 1166, 1060, 1060, 963, 963, 963, 963, 963, 963, 963, 963, 963, 963, 963, 876, 876, 876, 876, 796, 658, 724, 658, 724, 658, 658, 658, 658, 658, 658, 658, 658, 658, 658, 658, 658, 336, 658, 658, 592, 336, 336};
#endif
  const long nblow = numberof(low);
  pari_sp av;
  long ex, vx;
  GEN z;
  if (!nx) return pol_0(0);
  vx = ZX_valspec(x,nx); nx-=vx; x+=vx;
  if (nx==1) return Z_sqrshiftspec_ZX(gel(x, 0), vx);
  av = avma;
  ex = ZX_expispec(x,nx);
  if (nx-2 < nblow && low[nx-2]<=ex && ex<=high[nx-2])
    z = ZX_sqrspec_basecase(x, nx, 2*vx);
  else
    z = ZX_sqrspec_sqri(x, nx, ex, 2*vx);
  return gerepileupto(av, z);
}

GEN
ZX_sqr(GEN x)
{
  GEN z = ZX_sqrspec(x+2, lgpol(x));
  z[1] = x[1];
  return z;
}

GEN
ZX_mulspec(GEN x, GEN y, long nx, long ny)
{
  pari_sp av;
  long ex, ey, vx, vy;
  GEN z;
  if (!nx || !ny) return pol_0(0);
  vx = ZX_valspec(x,nx); nx-=vx; x += vx;
  vy = ZX_valspec(y,ny); ny-=vy; y += vy;
  if (nx==1) return Z_ZX_mulshiftspec(gel(x,0), y, ny, vx+vy);
  if (ny==1) return Z_ZX_mulshiftspec(gel(y,0), x, nx, vy+vx);
  av = avma;
  ex = ZX_expispec(x, nx); ey = ZX_expispec(y, ny);
  z  = ZX_mulspec_mulii(x,y,nx,ny,ex,ey,vx+vy);
  return gerepileupto(av, z);
}
GEN
ZX_mul(GEN x, GEN y)
{
  GEN z;
  if (x == y) return ZX_sqr(x);
  z = ZX_mulspec(x+2,y+2,lgpol(x),lgpol(y));
  z[1] = x[1];
  if (!signe(y)) z[1] &= VARNBITS;
  return z;
}

/* x,y two ZX in the same variable; assume y is monic */
GEN
ZX_rem(GEN x, GEN y)
{
  long vx, dx, dy, dz, i, j, sx, lr;
  pari_sp av0, av;
  GEN z,p1,rem;

  vx = varn(x);
  dy = degpol(y);
  dx = degpol(x);
  if (dx < dy) return ZX_copy(x);
  if (!dy) return pol_0(vx); /* y is constant */
  av0 = avma; dz = dx-dy;
  z=cgetg(dz+3,t_POL); z[1] = x[1];
  x += 2; y += 2; z += 2;

  p1 = gel(x,dx);
  gel(z,dz) = icopy(p1);
  for (i=dx-1; i>=dy; i--)
  {
    av=avma; p1=gel(x,i);
    for (j=i-dy+1; j<=i && j<=dz; j++)
      p1 = subii(p1, mulii(gel(z,j),gel(y,i-j)));
    gel(z,i-dy) = avma == av? icopy(p1): gerepileuptoint(av, p1);
  }
  rem = (GEN)avma; av = (pari_sp)new_chunk(dx+3);
  for (sx=0; ; i--)
  {
    p1 = gel(x,i);
    for (j=0; j<=i && j<=dz; j++)
      p1 = subii(p1, mulii(gel(z,j),gel(y,i-j)));
    if (signe(p1)) { sx = 1; break; }
    if (!i) break;
    avma=av;
  }
  lr=i+3; rem -= lr;
  rem[0] = evaltyp(t_POL) | evallg(lr);
  rem[1] = z[-1];
  p1 = gerepileuptoint((pari_sp)rem, p1);
  rem += 2; gel(rem,i) = p1;
  for (i--; i>=0; i--)
  {
    av=avma; p1 = gel(x,i);
    for (j=0; j<=i && j<=dz; j++)
      p1 = subii(p1, mulii(gel(z,j),gel(y,i-j)));
    gel(rem,i) = avma == av? icopy(p1): gerepileuptoint(av, p1);
  }
  rem -= 2;
  if (!sx) (void)ZX_renormalize(rem, lr);
  return gerepileupto(av0,rem);
}

/* return x(1) */
GEN
ZX_eval1(GEN x)
{
  pari_sp av = avma;
  long i = lg(x)-1;
  GEN s;
  if (i < 2) return gen_0;
  s = gel(x,i); i--;
  if (i == 1) return icopy(s);
  for ( ; i>=2; i--)
  {
    GEN c = gel(x,i);
    if (signe(c)) s = addii(s, c);
  }
  return gerepileuptoint(av,s);
}

/* reduce T mod X^n - 1. Shallow function */
GEN
ZX_mod_Xnm1(GEN T, ulong n)
{
  long i, j, L = lg(T), l = n+2;
  GEN S;
  if (L <= l) return T;
  S = cgetg(l, t_POL);
  S[1] = T[1];
  for (i = 2; i < l; i++) gel(S,i) = gel(T,i);
  for (j = 2; i < L; i++) {
    gel(S,j) = addii(gel(S,j), gel(T,i));
    if (++j == l) j = 2;
  }
  return normalizepol_lg(S, l);
}

/*******************************************************************/
/*                                                                 */
/*                                ZXV                              */
/*                                                                 */
/*******************************************************************/

int
ZXV_equal(GEN V, GEN W)
{
  long l = lg(V);
  if (l!=lg(W)) return 0;
  while (--l > 0)
    if (!ZX_equal(gel(V,l), gel(W,l))) return 0;
  return 1;
}

GEN
ZXV_Z_mul(GEN x, GEN y)
{ pari_APPLY_same(ZX_Z_mul(gel(x,i), y)) }

GEN
ZXV_remi2n(GEN x, long N)
{ pari_APPLY_same(ZX_remi2n(gel(x,i), N)) }

GEN
ZXV_dotproduct(GEN x, GEN y)
{
  pari_sp av = avma;
  long i, lx = lg(x);
  GEN c;
  if (lx == 1) return pol_0(varn(x));
  c = ZX_mul(gel(x,1), gel(y,1));
  for (i = 2; i < lx; i++)
  {
    GEN t = ZX_mul(gel(x,i), gel(y,i));
    if (signe(t)) c = ZX_add(c, t);
  }
  return gerepileupto(av, c);
}

/*******************************************************************/
/*                                                                 */
/*                                ZXQM                             */
/*                                                                 */
/*******************************************************************/

GEN
ZXn_mul(GEN x, GEN y, long n)
{ return RgXn_red_shallow(ZX_mul(x, y), n); }

GEN
ZXn_sqr(GEN x, long n)
{ return RgXn_red_shallow(ZX_sqr(x), n); }

/*******************************************************************/
/*                                                                 */
/*                                ZXQM                             */
/*                                                                 */
/*******************************************************************/

static long
ZX_expi(GEN x)
{
  if (signe(x)==0) return 0;
  if (typ(x)==t_INT) return expi(x);
  return ZX_expispec(x+2, lgpol(x));
}

static long
ZXC_expi(GEN x)
{
  long i, l = lg(x), m=0;
  for(i = 1; i < l; i++)
  {
    long e = ZX_expi(gel(x,i));
    if (e > m) m = e;
  }
  return m;
}

static long
ZXM_expi(GEN x)
{
  long i, l = lg(x), m=0;
  for(i = 1; i < l; i++)
  {
    long e = ZXC_expi(gel(x,i));
    if (e > m) m = e;
  }
  return m;
}

static GEN
ZX_eval2BIL(GEN x, long k)
{
  if (signe(x)==0) return gen_0;
  if (typ(x)==t_INT) return x;
  return ZX_eval2BILspec(x+2, k, lgpol(x));
}

/*Eval x in 2^(k*BIL) in linear time*/
static GEN
ZXC_eval2BIL(GEN x, long k)
{
  long i, lx = lg(x);
  GEN A = cgetg(lx, t_COL);
  for (i=1; i<lx; i++) gel(A,i) = ZX_eval2BIL(gel(x,i), k);
  return A;
}

static GEN
ZXM_eval2BIL(GEN x, long k)
{
  long i, lx = lg(x);
  GEN A = cgetg(lx, t_MAT);
  for (i=1; i<lx; i++) gel(A,i) = ZXC_eval2BIL(gel(x,i), k);
  return A;
}

static GEN
Z_mod2BIL_ZXQ(GEN x, long bs, GEN T)
{
  pari_sp av = avma;
  long v = varn(T), d = 2*(degpol(T)-1);
  GEN z = Z_mod2BIL_ZX(x, bs, d, 0);
  setvarn(z, v);
  return gerepileupto(av, ZX_rem(z, T));
}

static GEN
ZC_mod2BIL_ZXQC(GEN x, long bs, GEN T)
{
  long i, lx = lg(x);
  GEN A = cgetg(lx, t_COL);
  for (i=1; i<lx; i++) gel(A,i) = Z_mod2BIL_ZXQ(gel(x,i), bs, T);
  return A;
}

static GEN
ZM_mod2BIL_ZXQM(GEN x, long bs, GEN T)
{
  long i, lx = lg(x);
  GEN A = cgetg(lx, t_MAT);
  for (i=1; i<lx; i++) gel(A,i) = ZC_mod2BIL_ZXQC(gel(x,i), bs, T);
  return A;
}

GEN
ZXQM_mul(GEN x, GEN y, GEN T)
{
  long d = degpol(T);
  GEN z;
  pari_sp av = avma;
  if (d == 0)
    z = ZM_mul(simplify_shallow(x),simplify_shallow(y));
  else
  {
    long ex = ZXM_expi(x), ey = ZXM_expi(y), d= degpol(T), n = lg(x)-1;
    long e = ex + ey + expu(d) + expu(n) + 4;
    long N = divsBIL(e)+1;
    z = ZM_mul(ZXM_eval2BIL(x,N), ZXM_eval2BIL(y,N));
    z = ZM_mod2BIL_ZXQM(z, N, T);
  }
  return gerepileupto(av, z);
}

GEN
ZXQM_sqr(GEN x, GEN T)
{
  long d = degpol(T);
  GEN z;
  pari_sp av = avma;
  if (d == 0)
    z = ZM_sqr(simplify_shallow(x));
  else
  {
    long ex = ZXM_expi(x), d = degpol(T), n = lg(x)-1;
    long e = 2*ex + expu(d) + expu(n) + 4;
    long N = divsBIL(e)+1;
    z = ZM_sqr(ZXM_eval2BIL(x,N));
    z = ZM_mod2BIL_ZXQM(z, N, T);
  }
  return gerepileupto(av, z);
}

GEN
QXQM_mul(GEN x, GEN y, GEN T)
{
  GEN dx, nx = Q_primitive_part(x, &dx);
  GEN dy, ny = Q_primitive_part(y, &dy);
  GEN z = ZXQM_mul(nx, ny, T);
  if (dx || dy)
  {
    GEN d = dx ? dy ? gmul(dx, dy): dx : dy;
    if (!gequal1(d)) z = RgM_Rg_mul(z, d);
  }
  return z;
}

GEN
QXQM_sqr(GEN x, GEN T)
{
  GEN dx, nx = Q_primitive_part(x, &dx);
  GEN z = ZXQM_sqr(nx, T);
  if (dx) z = RgM_Rg_mul(z, gsqr(dx));
  return z;
}

static GEN
Z_mod2BIL_Fq(GEN x, long bs, GEN T, GEN p)
{
  pari_sp av = avma;
  long v = get_FpX_var(T), d = 2*(get_FpX_degree(T)-1);
  GEN z = Z_mod2BIL_ZX(x, bs, d, 0);
  setvarn(z, v);
  return gerepileupto(av, FpX_rem(z, T, p));
}

static GEN
ZC_mod2BIL_FqC(GEN x, long bs, GEN T, GEN p)
{
  long i, lx = lg(x);
  GEN A = cgetg(lx, t_COL);
  for (i=1; i<lx; i++) gel(A,i) = Z_mod2BIL_Fq(gel(x,i), bs, T, p);
  return A;
}

static GEN
ZM_mod2BIL_FqM(GEN x, long bs, GEN T, GEN p)
{
  long i, lx = lg(x);
  GEN A = cgetg(lx, t_MAT);
  for (i=1; i<lx; i++) gel(A,i) = ZC_mod2BIL_FqC(gel(x,i), bs, T, p);
  return A;
}

GEN
FqM_mul_Kronecker(GEN x, GEN y, GEN T, GEN p)
{
  pari_sp av = avma;
  long ex = ZXM_expi(x), ey = ZXM_expi(y), d= degpol(T), n = lg(x)-1;
  long e = ex + ey + expu(d) + expu(n) + 4;
  long N = divsBIL(e)+1;
  GEN  z = ZM_mul(ZXM_eval2BIL(x,N), ZXM_eval2BIL(y,N));
  return gerepileupto(av, ZM_mod2BIL_FqM(z, N, T, p));
}

/*******************************************************************/
/*                                                                 */
/*                                ZXX                              */
/*                                                                 */
/*******************************************************************/

void
RgX_check_ZXX(GEN x, const char *s)
{
  long k = lg(x)-1;
  for ( ; k>1; k--) {
    GEN t = gel(x,k);
    switch(typ(t)) {
      case t_INT: break;
      case t_POL: if (RgX_is_ZX(t)) break;
      /* fall through */
      default: pari_err_TYPE(stack_strcat(s, " not in Z[X,Y]"),x);
    }
  }
}

/*Renormalize (in place) polynomial with t_INT or ZX coefficients.*/
GEN
ZXX_renormalize(GEN x, long lx)
{
  long i;
  for (i = lx-1; i>1; i--)
    if (signe(gel(x,i))) break;
  stackdummy((pari_sp)(x + lg(x)), (pari_sp)(x + (i+1)));
  setlg(x, i+1); setsigne(x, i!=1); return x;
}

long
ZXX_max_lg(GEN x)
{
  long i, prec = 0, lx = lg(x);
  for (i=2; i<lx; i++)
  {
    GEN p = gel(x,i);
    long l = (typ(p) == t_INT)? lgefint(p): ZX_max_lg(p);
    if (l > prec) prec = l;
  }
  return prec;
}

GEN
ZXX_Z_mul(GEN y, GEN x)
{
  long i, l = lg(y);
  GEN z = cgetg(l,t_POL); z[1] = y[1];
  for(i=2; i<l; i++)
    if(typ(gel(y,i))==t_INT)
      gel(z,i) = mulii(gel(y,i),x);
    else
      gel(z,i) = ZX_Z_mul(gel(y,i),x);
  return z;
}

GEN
ZXX_Z_add_shallow(GEN x, GEN y)
{
  long i, l = lg(x);
  GEN z, a;
  if (signe(x)==0) return scalarpol(y,varn(x));
  z = cgetg(l,t_POL); z[1] = x[1];
  a = gel(x,2);
  gel(z, 2) = typ(a)==t_INT? addii(a,y): ZX_Z_add(a,y);
  for(i=3; i<l; i++)
    gel(z,i) = gel(x,i);
  return z;
}

GEN
ZXX_Z_divexact(GEN y, GEN x)
{
  long i, l = lg(y);
  GEN z = cgetg(l,t_POL); z[1] = y[1];
  for(i=2; i<l; i++)
    if(typ(gel(y,i))==t_INT)
      gel(z,i) = diviiexact(gel(y,i),x);
    else
      gel(z,i) = ZX_Z_divexact(gel(y,i),x);
  return z;
}

/* Kronecker substitution, ZXX -> ZX:
 * P(X,Y) = sum_{0<=i<lP} P_i(X) * Y^i, where deg P_i < n.
 * Returns P(X,X^(2n-1)) */
GEN
ZXX_to_Kronecker_spec(GEN P, long lP, long n)
{
  long i, k, N = (n<<1) + 1;
  GEN y;
  if (!lP) return pol_0(0);
  y = cgetg((N-2)*lP + 2, t_POL) + 2;
  for (k=i=0; i<lP; i++)
  {
    long j;
    GEN c = gel(P,i);
    if (typ(c)!=t_POL)
    {
      gel(y,k++) = c;
      j = 3;
    }
    else
    {
      long l = lg(c);
      if (l-3 >= n)
        pari_err_BUG("ZXX_to_Kronecker, P is not reduced mod Q");
      for (j=2; j < l; j++) gel(y,k++) = gel(c,j);
    }
    if (i == lP-1) break;
    for (   ; j < N; j++) gel(y,k++) = gen_0;
  }
  y-=2; setlg(y, k+2); y[1] = evalsigne(1); return y;
}

GEN
ZXX_to_Kronecker(GEN P, long n)
{
  GEN z = ZXX_to_Kronecker_spec(P+2, lgpol(P), n);
  setvarn(z,varn(P)); return z;
}

GEN
ZXQX_sqr(GEN x, GEN T)
{
  pari_sp av = avma;
  long n = degpol(T);
  GEN z = ZXX_sqr_Kronecker(x, n);
  z = Kronecker_to_ZXX(z, n, varn(T));
  return gerepileupto(av, z);
}

GEN
ZXQX_mul(GEN x, GEN y, GEN T)
{
  pari_sp av = avma;
  long n = degpol(T);
  GEN z = ZXX_mul_Kronecker(x, y, n);
  z = Kronecker_to_ZXX(z, n, varn(T));
  return gerepileupto(av, z);
}

GEN
QX_mul(GEN x, GEN y)
{
  GEN dx, nx = Q_primitive_part(x, &dx);
  GEN dy, ny = Q_primitive_part(y, &dy);
  GEN z = ZX_mul(nx, ny);
  if (dx || dy)
  {
    GEN d = dx ? dy ? gmul(dx, dy): dx : dy;
    return ZX_Q_mul(z, d);
  } else
    return z;
}

GEN
QX_sqr(GEN x)
{
  GEN dx, nx = Q_primitive_part(x, &dx);
  GEN z = ZX_sqr(nx);
  if (dx)
    return ZX_Q_mul(z, gsqr(dx));
  else
    return z;
}

GEN
QX_ZX_rem(GEN x, GEN y)
{
  pari_sp av = avma;
  GEN d, nx = Q_primitive_part(x, &d);
  GEN r = ZX_rem(nx, y);
  if (d) r = ZX_Q_mul(r, d);
  return gerepileupto(av, r);
}
