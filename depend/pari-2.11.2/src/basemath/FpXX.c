/* Copyright (C) 2012  The PARI group.

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

/* Not so fast arithmetic with polynomials over FpX */

/*******************************************************************/
/*                                                                 */
/*                             FpXX                                */
/*                                                                 */
/*******************************************************************/
/*Polynomials whose coefficients are either polynomials or integers*/

static ulong
to_FlxqX(GEN P, GEN Q, GEN T, GEN p, GEN *pt_P, GEN *pt_Q, GEN *pt_T)
{
  ulong pp = uel(p,2);
  long v = get_FpX_var(T);
  *pt_P = ZXX_to_FlxX(P, pp, v);
  if (pt_Q) *pt_Q = ZXX_to_FlxX(Q, pp, v);
  *pt_T = ZXT_to_FlxT(T, pp);
  return pp;
}

static GEN
ZXX_copy(GEN a) { return gcopy(a); }

GEN
FpXX_red(GEN z, GEN p)
{
  GEN res;
  long i, l = lg(z);
  res = cgetg(l,t_POL); res[1] = z[1];
  for (i=2; i<l; i++)
  {
    GEN zi = gel(z,i), c;
    if (typ(zi)==t_INT)
      c = modii(zi,p);
    else
    {
      pari_sp av = avma;
      c = FpX_red(zi,p);
      switch(lg(c)) {
        case 2: avma = av; c = gen_0; break;
        case 3: c = gerepilecopy(av, gel(c,2)); break;
      }
    }
    gel(res,i) = c;
  }
  return FpXX_renormalize(res,lg(res));
}
GEN
FpXX_add(GEN x, GEN y, GEN p)
{
  long i,lz;
  GEN z;
  long lx=lg(x);
  long ly=lg(y);
  if (ly>lx) swapspec(x,y, lx,ly);
  lz = lx; z = cgetg(lz, t_POL); z[1]=x[1];
  for (i=2; i<ly; i++) gel(z,i) = Fq_add(gel(x,i), gel(y,i), NULL, p);
  for (   ; i<lx; i++) gel(z,i) = gcopy(gel(x,i));
  return FpXX_renormalize(z, lz);
}
GEN
FpXX_sub(GEN x, GEN y, GEN p)
{
  long i,lz;
  GEN z;
  long lx=lg(x);
  long ly=lg(y);
  if (ly <= lx)
  {
    lz = lx; z = cgetg(lz, t_POL); z[1]=x[1];
    for (i=2; i<ly; i++) gel(z,i) = Fq_sub(gel(x,i), gel(y,i), NULL, p);
    for (   ; i<lx; i++) gel(z,i) = gcopy(gel(x,i));
  }
  else
  {
    lz = ly; z = cgetg(lz, t_POL); z[1]=x[1];
    for (i=2; i<lx; i++) gel(z,i) = Fq_sub(gel(x,i), gel(y,i), NULL, p);
    for (   ; i<ly; i++) gel(z,i) = Fq_neg(gel(y,i), NULL, p);
  }
  return FpXX_renormalize(z, lz);
}

static GEN
FpXX_subspec(GEN x, GEN y, GEN p, long nx, long ny)
{
  long i,lz;
  GEN z;
  if (ny <= nx)
  {
    lz = nx+2; z = cgetg(lz, t_POL)+2;
    for (i=0; i<ny; i++) gel(z,i) = Fq_sub(gel(x,i), gel(y,i), NULL, p);
    for (   ; i<nx; i++) gel(z,i) = gcopy(gel(x,i));
  }
  else
  {
    lz = ny+2; z = cgetg(lz, t_POL)+2;
    for (i=0; i<nx; i++) gel(z,i) = Fq_sub(gel(x,i), gel(y,i), NULL, p);
    for (   ; i<ny; i++) gel(z,i) = Fq_neg(gel(y,i), NULL, p);
  }
  return FpXX_renormalize(z-2, lz);
}

GEN
FpXX_neg(GEN x, GEN p)
{
  long i, lx = lg(x);
  GEN y = cgetg(lx,t_POL);
  y[1] = x[1];
  for(i=2; i<lx; i++) gel(y,i) = Fq_neg(gel(x,i), NULL, p);
  return FpXX_renormalize(y, lx);
}

GEN
FpXX_Fp_mul(GEN P, GEN u, GEN p)
{
  long i, lP;
  GEN res = cgetg_copy(P, &lP); res[1] = P[1];
  for(i=2; i<lP; i++)
  {
    GEN x = gel(P,i);
    gel(res,i) = typ(x)==t_INT? Fp_mul(x,u,p): FpX_Fp_mul(x,u,p);
  }
  return FpXX_renormalize(res,lP);
}

GEN
FpXX_mulu(GEN P, ulong u, GEN p)
{
  long i, lP;
  GEN res = cgetg_copy(P, &lP); res[1] = P[1];
  for(i=2; i<lP; i++)
  {
    GEN x = gel(P,i);
    gel(res,i) = typ(x)==t_INT? Fp_mulu(x,u,p): FpX_mulu(x,u,p);
  }
  return FpXX_renormalize(res,lP);
}

GEN
FpXX_halve(GEN P, GEN p)
{
  long i, lP;
  GEN res = cgetg_copy(P, &lP); res[1] = P[1];
  for(i=2; i<lP; i++)
  {
    GEN x = gel(P,i);
    gel(res,i) = typ(x)==t_INT? Fp_halve(x,p): FpX_halve(x,p);
  }
  return FpXX_renormalize(res,lP);
}

GEN
FpXX_deriv(GEN P, GEN p)
{
  long i, l = lg(P)-1;
  GEN res;

  if (l < 3) return pol_0(varn(P));
  res = cgetg(l, t_POL);
  res[1] = P[1];
  for (i=2; i<l ; i++)
  {
    GEN x = gel(P,i+1);
    gel(res,i) = typ(x)==t_INT? Fp_mulu(x,i-1,p): FpX_mulu(x,i-1,p);
  }
  return FpXX_renormalize(res, l);
}

GEN
FpXX_integ(GEN P, GEN p)
{
  long i, l = lg(P);
  GEN res;

  if (l == 2) return pol_0(varn(P));
  res = cgetg(l+1, t_POL);
  res[1] = P[1];
  gel(res,2) = gen_0;
  for (i=3; i<=l ; i++)
  {
    GEN x = gel(P,i-1);
    GEN i1 = Fp_inv(utoi(i-2), p);
    gel(res,i) = typ(x)==t_INT? Fp_mul(x,i1,p): FpX_Fp_mul(x,i1,p);
  }
  return FpXX_renormalize(res, l+1);
}

/*******************************************************************/
/*                                                                 */
/*                             (Fp[X]/(Q))[Y]                      */
/*                                                                 */
/*******************************************************************/

static GEN
get_FpXQX_red(GEN T, GEN *B)
{
  if (typ(T)!=t_VEC) { *B=NULL; return T; }
  *B = gel(T,1); return gel(T,2);
}

GEN
random_FpXQX(long d1, long v, GEN T, GEN p)
{
  long dT = get_FpX_degree(T), vT = get_FpX_var(T);
  long i, d = d1+2;
  GEN y = cgetg(d,t_POL); y[1] = evalsigne(1) | evalvarn(v);
  for (i=2; i<d; i++) gel(y,i) = random_FpX(dT, vT, p);
  return FpXQX_renormalize(y,d);
}

/*Not stack clean*/
GEN
Kronecker_to_FpXQX(GEN Z, GEN T, GEN p)
{
  long i,j,lx,l, N = (get_FpX_degree(T)<<1) + 1;
  GEN x, t = cgetg(N,t_POL), z = FpX_red(Z, p);
  t[1] = evalvarn(get_FpX_var(T));
  l = lg(z); lx = (l-2) / (N-2);
  x = cgetg(lx+3,t_POL);
  x[1] = z[1];
  for (i=2; i<lx+2; i++)
  {
    for (j=2; j<N; j++) gel(t,j) = gel(z,j);
    z += (N-2);
    gel(x,i) = FpX_rem(FpX_renormalize(t,N), T,p);
  }
  N = (l-2) % (N-2) + 2;
  for (j=2; j<N; j++) gel(t,j) = gel(z,j);
  gel(x,i) = FpX_rem(FpX_renormalize(t,N), T,p);
  return FpXQX_renormalize(x, i+1);
}

/* shallow, n = deg(T) */
GEN
Kronecker_to_ZXX(GEN z, long n, long v)
{
  long i,j,lx,l, N = (n<<1)+1;
  GEN x, t;
  l = lg(z); lx = (l-2) / (N-2);
  x = cgetg(lx+3,t_POL);
  x[1] = z[1];
  for (i=2; i<lx+2; i++)
  {
    t = cgetg(N,t_POL); t[1] = evalvarn(v);
    for (j=2; j<N; j++) gel(t,j) = gel(z,j);
    z += (N-2);
    gel(x,i) = ZX_renormalize(t,N);
  }
  N = (l-2) % (N-2) + 2;
  t = cgetg(N,t_POL); t[1] = evalvarn(v);
  for (j=2; j<N; j++) gel(t,j) = gel(z,j);
  gel(x,i) = ZX_renormalize(t,N);
  return ZXX_renormalize(x, i+1);
}
/* shallow */
GEN
ZXX_mul_Kronecker(GEN x, GEN y, long n)
{ return ZX_mul(ZXX_to_Kronecker(x,n), ZXX_to_Kronecker(y,n)); }

GEN
ZXX_sqr_Kronecker(GEN x, long n)
{ return ZX_sqr(ZXX_to_Kronecker(x,n)); }

GEN
FpXQX_red(GEN z, GEN T, GEN p)
{
  long i, l = lg(z);
  GEN res = cgetg(l,t_POL); res[1] = z[1];
  for(i=2;i<l;i++)
    if (typ(gel(z,i)) == t_INT)
      gel(res,i) = modii(gel(z,i),p);
    else
      gel(res,i) = FpXQ_red(gel(z,i),T,p);
  return FpXQX_renormalize(res,l);
}

/* z in Z[X], return z * Mod(1,p), normalized*/
GEN
FpXQX_to_mod(GEN z, GEN T, GEN p)
{
  long i,l = lg(z);
  GEN x = cgetg(l, t_POL);
  x[1] = z[1];
  if (l == 2) return x;
  T = FpX_to_mod(T, p);
  for (i=2; i<l; i++)
  {
    GEN zi = gel(z,i);
    gel(x,i) = typ(zi) == t_POL? mkpolmod(FpX_to_mod(zi, p), T): icopy(zi);
  }
  return normalizepol_lg(x,l);
}

static int
ZXX_is_ZX_spec(GEN a,long na)
{
  long i;
  for(i=0;i<na;i++)
    if(typ(gel(a,i))!=t_INT) return 0;
  return 1;
}

static int
ZXX_is_ZX(GEN a) { return ZXX_is_ZX_spec(a+2,lgpol(a)); }

static GEN
FpXX_FpX_mulspec(GEN P, GEN U, GEN p, long v, long lU)
{
  long i, lP =lg(P);
  GEN res;
  res = cgetg(lP, t_POL); res[1] = P[1];
  for(i=2; i<lP; i++)
  {
    GEN Pi = gel(P,i);
    gel(res,i) = typ(Pi)==t_INT? FpX_Fp_mulspec(U, Pi, p, lU):
                                 FpX_mulspec(U, Pi+2, p, lU, lgpol(Pi));
    setvarn(gel(res,i),v);
  }
  return FpXQX_renormalize(res,lP);
}

GEN
FpXX_FpX_mul(GEN P, GEN U, GEN p)
{ return FpXX_FpX_mulspec(P,U+2,p,varn(U),lgpol(U)); }

static GEN
FpXY_FpY_mulspec(GEN x, GEN y, GEN T, GEN p, long lx, long ly)
{
  pari_sp av = avma;
  long v = fetch_var();
  GEN z = RgXY_swapspec(x,get_FpX_degree(T)-1,v,lx);
  z = FpXX_FpX_mulspec(z,y,p,v,ly);
  z = RgXY_swapspec(z+2,lx+ly+3,get_FpX_var(T),lgpol(z));
  (void)delete_var(); return gerepilecopy(av,z);
}

static GEN
FpXQX_mulspec(GEN x, GEN y, GEN T, GEN p, long lx, long ly)
{
  pari_sp av = avma;
  GEN z, kx, ky;
  long n;
  if (ZXX_is_ZX_spec(y,ly))
  {
    if (ZXX_is_ZX_spec(x,lx))
      return FpX_mulspec(x,y,p,lx,ly);
    else
      return FpXY_FpY_mulspec(x,y,T,p,lx,ly);
  } else if (ZXX_is_ZX_spec(x,lx))
      return FpXY_FpY_mulspec(y,x,T,p,ly,lx);
  n = get_FpX_degree(T);
  kx = ZXX_to_Kronecker_spec(x, lx, n);
  ky = ZXX_to_Kronecker_spec(y, ly, n);
  z = Kronecker_to_FpXQX(ZX_mul(ky,kx), T, p);
  return gerepileupto(av, z);
}

GEN
FpXQX_mul(GEN x, GEN y, GEN T, GEN p)
{
  GEN z = FpXQX_mulspec(x+2,y+2,T,p,lgpol(x),lgpol(y));
  setvarn(z,varn(x)); return z;
}

GEN
FpXQX_sqr(GEN x, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN z, kx;
  if (ZXX_is_ZX(x)) return ZX_sqr(x);
  kx= ZXX_to_Kronecker(x, get_FpX_degree(T));
  z = Kronecker_to_FpXQX(ZX_sqr(kx), T, p);
  return gerepileupto(av, z);
}

GEN
FpXQX_FpXQ_mul(GEN P, GEN U, GEN T, GEN p)
{
  long i, lP;
  GEN res;
  res = cgetg_copy(P, &lP); res[1] = P[1];
  for(i=2; i<lP; i++)
    gel(res,i) = typ(gel(P,i))==t_INT? FpX_Fp_mul(U, gel(P,i), p):
                                       FpXQ_mul(U, gel(P,i), T,p);
  return FpXQX_renormalize(res,lP);
}

/* x and y in Z[Y][X]. Assume T irreducible mod p */
static GEN
FpXQX_divrem_basecase(GEN x, GEN y, GEN T, GEN p, GEN *pr)
{
  long vx, dx, dy, dy1, dz, i, j, sx, lr;
  pari_sp av0, av, tetpil;
  GEN z,p1,rem,lead;

  if (!signe(y)) pari_err_INV("FpX_divrem",y);
  vx=varn(x); dy=degpol(y); dx=degpol(x);
  if (dx < dy)
  {
    if (pr)
    {
      av0 = avma; x = FpXQX_red(x, T, p);
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
    if (gequal1(lead)) return FpXQX_red(x,T,p);
    av0 = avma; x = FqX_Fq_mul(x, Fq_inv(lead, T,p), T,p);
    return gerepileupto(av0,x);
  }
  av0 = avma; dz = dx-dy;
  lead = gequal1(lead)? NULL: gclone(Fq_inv(lead,T,p));
  avma = av0;
  z = cgetg(dz+3,t_POL); z[1] = x[1];
  x += 2; y += 2; z += 2;
  for (dy1=dy-1; dy1>=0 && !signe(gel(y, dy1)); dy1--);

  p1 = gel(x,dx); av = avma;
  gel(z,dz) = lead? gerepileupto(av, Fq_mul(p1,lead, T, p)): gcopy(p1);
  for (i=dx-1; i>=dy; i--)
  {
    av=avma; p1=gel(x,i);
    for (j=i-dy1; j<=i && j<=dz; j++)
      p1 = Fq_sub(p1, Fq_mul(gel(z,j),gel(y,i-j),NULL,p),NULL,p);
    if (lead) p1 = Fq_mul(p1, lead, NULL,p);
    tetpil=avma; gel(z,i-dy) = gerepile(av,tetpil,Fq_red(p1,T,p));
  }
  if (!pr) { if (lead) gunclone(lead); return z-2; }

  rem = (GEN)avma; av = (pari_sp)new_chunk(dx+3);
  for (sx=0; ; i--)
  {
    p1 = gel(x,i);
    for (j=maxss(0,i-dy1); j<=i && j<=dz; j++)
      p1 = Fq_sub(p1, Fq_mul(gel(z,j),gel(y,i-j),NULL,p),NULL,p);
    tetpil=avma; p1 = Fq_red(p1, T, p); if (signe(p1)) { sx = 1; break; }
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
    for (j=maxss(0,i-dy1); j<=i && j<=dz; j++)
      p1 = Fq_sub(p1, Fq_mul(gel(z,j),gel(y,i-j), NULL,p), NULL,p);
    tetpil=avma; gel(rem,i) = gerepile(av,tetpil, Fq_red(p1, T, p));
  }
  rem -= 2;
  if (lead) gunclone(lead);
  if (!sx) (void)FpXQX_renormalize(rem, lr);
  if (pr == ONLY_REM) return gerepileupto(av0,rem);
  *pr = rem; return z-2;
}

static GEN
FpXQX_halfgcd_basecase(GEN a, GEN b, GEN T, GEN p)
{
  pari_sp av=avma;
  GEN u,u1,v,v1;
  long vx = varn(a);
  long n = lgpol(a)>>1;
  u1 = v = pol_0(vx);
  u = v1 = pol_1(vx);
  while (lgpol(b)>n)
  {
    GEN r, q = FpXQX_divrem(a,b, T, p, &r);
    a = b; b = r; swap(u,u1); swap(v,v1);
    u1 = FpXX_sub(u1, FpXQX_mul(u, q, T, p), p);
    v1 = FpXX_sub(v1, FpXQX_mul(v, q ,T, p), p);
    if (gc_needed(av,2))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"FpXQX_halfgcd (d = %ld)",degpol(b));
      gerepileall(av,6, &a,&b,&u1,&v1,&u,&v);
    }
  }
  return gerepilecopy(av, mkmat2(mkcol2(u,u1), mkcol2(v,v1)));
}
static GEN
FpXQX_addmulmul(GEN u, GEN v, GEN x, GEN y, GEN T, GEN p)
{
  return FpXX_add(FpXQX_mul(u, x, T, p),FpXQX_mul(v, y, T, p), p);
}

static GEN
FpXQXM_FpXQX_mul2(GEN M, GEN x, GEN y, GEN T, GEN p)
{
  GEN res = cgetg(3, t_COL);
  gel(res, 1) = FpXQX_addmulmul(gcoeff(M,1,1), gcoeff(M,1,2), x, y, T, p);
  gel(res, 2) = FpXQX_addmulmul(gcoeff(M,2,1), gcoeff(M,2,2), x, y, T, p);
  return res;
}

static GEN
FpXQXM_mul2(GEN A, GEN B, GEN T, GEN p)
{
  GEN A11=gcoeff(A,1,1),A12=gcoeff(A,1,2), B11=gcoeff(B,1,1),B12=gcoeff(B,1,2);
  GEN A21=gcoeff(A,2,1),A22=gcoeff(A,2,2), B21=gcoeff(B,2,1),B22=gcoeff(B,2,2);
  GEN M1 = FpXQX_mul(FpXX_add(A11,A22, p), FpXX_add(B11,B22, p), T, p);
  GEN M2 = FpXQX_mul(FpXX_add(A21,A22, p), B11, T, p);
  GEN M3 = FpXQX_mul(A11, FpXX_sub(B12,B22, p), T, p);
  GEN M4 = FpXQX_mul(A22, FpXX_sub(B21,B11, p), T, p);
  GEN M5 = FpXQX_mul(FpXX_add(A11,A12, p), B22, T, p);
  GEN M6 = FpXQX_mul(FpXX_sub(A21,A11, p), FpXX_add(B11,B12, p), T, p);
  GEN M7 = FpXQX_mul(FpXX_sub(A12,A22, p), FpXX_add(B21,B22, p), T, p);
  GEN T1 = FpXX_add(M1,M4, p), T2 = FpXX_sub(M7,M5, p);
  GEN T3 = FpXX_sub(M1,M2, p), T4 = FpXX_add(M3,M6, p);
  retmkmat2(mkcol2(FpXX_add(T1,T2, p), FpXX_add(M2,M4, p)),
            mkcol2(FpXX_add(M3,M5, p), FpXX_add(T3,T4, p)));
}
/* Return [0,1;1,-q]*M */
static GEN
FpXQX_FpXQXM_qmul(GEN q, GEN M, GEN T, GEN p)
{
  GEN u, v, res = cgetg(3, t_MAT);
  u = FpXX_sub(gcoeff(M,1,1), FpXQX_mul(gcoeff(M,2,1), q, T, p), p);
  gel(res,1) = mkcol2(gcoeff(M,2,1), u);
  v = FpXX_sub(gcoeff(M,1,2), FpXQX_mul(gcoeff(M,2,2), q, T, p), p);
  gel(res,2) = mkcol2(gcoeff(M,2,2), v);
  return res;
}

static GEN
matid2_FpXQXM(long v)
{
  retmkmat2(mkcol2(pol_1(v),pol_0(v)),
            mkcol2(pol_0(v),pol_1(v)));
}

static GEN
FpXQX_halfgcd_split(GEN x, GEN y, GEN T, GEN p)
{
  pari_sp av=avma;
  GEN R, S, V;
  GEN y1, r, q;
  long l = lgpol(x), n = l>>1, k;
  if (lgpol(y)<=n) return matid2_FpXQXM(varn(x));
  R = FpXQX_halfgcd(RgX_shift_shallow(x,-n),RgX_shift_shallow(y,-n), T, p);
  V = FpXQXM_FpXQX_mul2(R,x,y, T, p); y1 = gel(V,2);
  if (lgpol(y1)<=n) return gerepilecopy(av, R);
  q = FpXQX_divrem(gel(V,1), y1, T, p, &r);
  k = 2*n-degpol(y1);
  S = FpXQX_halfgcd(RgX_shift_shallow(y1,-k), RgX_shift_shallow(r,-k), T, p);
  return gerepileupto(av, FpXQXM_mul2(S,FpXQX_FpXQXM_qmul(q,R, T, p), T, p));
}

/* Return M in GL_2(Fp[X]) such that:
if [a',b']~=M*[a,b]~ then degpol(a')>= (lgpol(a)>>1) >degpol(b')
*/

static GEN
FpXQX_halfgcd_i(GEN x, GEN y, GEN T, GEN p)
{
  if (lg(x)<=FpXQX_HALFGCD_LIMIT) return FpXQX_halfgcd_basecase(x, y, T, p);
  return FpXQX_halfgcd_split(x, y, T, p);
}

GEN
FpXQX_halfgcd(GEN x, GEN y, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN M,q,r;
  if (lgefint(p)==3)
  {
    ulong pp = to_FlxqX(x, y, T, p, &x, &y, &T);
    M = FlxXM_to_ZXXM(FlxqX_halfgcd(x, y, T, pp));
  }
  else
  {
    if (!signe(x))
    {
      long v = varn(x);
      retmkmat2(mkcol2(pol_0(v),pol_1(v)),
                mkcol2(pol_1(v),pol_0(v)));
    }
    if (degpol(y)<degpol(x)) return FpXQX_halfgcd_i(x, y, T, p);
    q = FpXQX_divrem(y, x, T, p, &r);
    M = FpXQX_halfgcd_i(x, r, T, p);
    gcoeff(M,1,1) = FpXX_sub(gcoeff(M,1,1), FpXQX_mul(q, gcoeff(M,1,2), T, p), p);
    gcoeff(M,2,1) = FpXX_sub(gcoeff(M,2,1), FpXQX_mul(q, gcoeff(M,2,2), T, p), p);
  }
  return gerepilecopy(av, M);
}

static GEN
FpXQX_gcd_basecase(GEN a, GEN b, GEN T, GEN p)
{
  pari_sp av = avma, av0=avma;
  while (signe(b))
  {
    GEN c;
    if (gc_needed(av0,2))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"FpXQX_gcd (d = %ld)",degpol(b));
      gerepileall(av0,2, &a,&b);
    }
    av = avma; c = FpXQX_rem(a, b, T, p); a=b; b=c;
  }
  avma = av; return a;
}

GEN
FpXQX_gcd(GEN x, GEN y, GEN T, GEN p)
{
  pari_sp av = avma;
  if (lgefint(p) == 3)
  {
    GEN Pl, Ql, Tl, U;
    ulong pp = to_FlxqX(x, y, T, p, &Pl, &Ql, &Tl);
    U  = FlxqX_gcd(Pl, Ql, Tl, pp);
    return gerepileupto(av, FlxX_to_ZXX(U));
  }
  x = FpXQX_red(x, T, p);
  y = FpXQX_red(y, T, p);
  if (!signe(x)) return gerepileupto(av, y);
  while (lg(y)>FpXQX_GCD_LIMIT)
  {
    GEN c;
    if (lgpol(y)<=(lgpol(x)>>1))
    {
      GEN r = FpXQX_rem(x, y, T, p);
      x = y; y = r;
    }
    c = FpXQXM_FpXQX_mul2(FpXQX_halfgcd(x,y, T, p), x, y, T, p);
    x = gel(c,1); y = gel(c,2);
    gerepileall(av,2,&x,&y);
  }
  return gerepileupto(av, FpXQX_gcd_basecase(x, y, T, p));
}

static GEN
FpXQX_extgcd_basecase(GEN a, GEN b, GEN T, GEN p, GEN *ptu, GEN *ptv)
{
  pari_sp av=avma;
  GEN u,v,d,d1,v1;
  long vx = varn(a);
  d = a; d1 = b;
  v = pol_0(vx); v1 = pol_1(vx);
  while (signe(d1))
  {
    GEN r, q = FpXQX_divrem(d, d1, T, p, &r);
    v = FpXX_sub(v,FpXQX_mul(q,v1,T, p),p);
    u=v; v=v1; v1=u;
    u=r; d=d1; d1=u;
    if (gc_needed(av,2))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"FpXQX_extgcd (d = %ld)",degpol(d));
      gerepileall(av,5, &d,&d1,&u,&v,&v1);
    }
  }
  if (ptu) *ptu = FpXQX_div(FpXX_sub(d,FpXQX_mul(b,v, T, p), p), a, T, p);
  *ptv = v; return d;
}

static GEN
FpXQX_extgcd_halfgcd(GEN x, GEN y, GEN T, GEN p, GEN *ptu, GEN *ptv)
{
  pari_sp av=avma;
  GEN u,v,R = matid2_FpXQXM(varn(x));
  while (lg(y)>FpXQX_EXTGCD_LIMIT)
  {
    GEN M, c;
    if (lgpol(y)<=(lgpol(x)>>1))
    {
      GEN r, q = FpXQX_divrem(x, y, T, p, &r);
      x = y; y = r;
      R = FpXQX_FpXQXM_qmul(q, R, T, p);
    }
    M = FpXQX_halfgcd(x,y, T, p);
    c = FpXQXM_FpXQX_mul2(M, x,y, T, p);
    R = FpXQXM_mul2(M, R, T, p);
    x = gel(c,1); y = gel(c,2);
    gerepileall(av,3,&x,&y,&R);
  }
  y = FpXQX_extgcd_basecase(x,y, T, p, &u,&v);
  if (ptu) *ptu = FpXQX_addmulmul(u,v,gcoeff(R,1,1),gcoeff(R,2,1), T, p);
  *ptv = FpXQX_addmulmul(u,v,gcoeff(R,1,2),gcoeff(R,2,2), T, p);
  return y;
}

/* x and y in Z[Y][X], return lift(gcd(x mod T,p, y mod T,p)). Set u and v st
 * ux + vy = gcd (mod T,p) */
GEN
FpXQX_extgcd(GEN x, GEN y, GEN T, GEN p, GEN *ptu, GEN *ptv)
{
  GEN d;
  pari_sp ltop=avma;
  if (lgefint(p) == 3)
  {
    GEN Pl, Ql, Tl, Dl;
    ulong pp = to_FlxqX(x, y, T, p, &Pl, &Ql, &Tl);
    Dl = FlxqX_extgcd(Pl, Ql, Tl, pp, ptu, ptv);
    if (ptu) *ptu = FlxX_to_ZXX(*ptu);
    *ptv = FlxX_to_ZXX(*ptv);
    d = FlxX_to_ZXX(Dl);
  }
  else
  {
    x = FpXQX_red(x, T, p);
    y = FpXQX_red(y, T, p);
    if (lg(y)>FpXQX_EXTGCD_LIMIT)
      d = FpXQX_extgcd_halfgcd(x, y, T, p, ptu, ptv);
    else
      d = FpXQX_extgcd_basecase(x, y, T, p, ptu, ptv);
  }
  gerepileall(ltop,ptu?3:2,&d,ptv,ptu);
  return d;
}

GEN
FpXQX_dotproduct(GEN x, GEN y, GEN T, GEN p)
{
  long i, l = minss(lg(x), lg(y));
  pari_sp av;
  GEN c;
  if (l == 2) return gen_0;
  av = avma; c = gmul(gel(x,2),gel(y,2));
  for (i=3; i<l; i++) c = gadd(c, gmul(gel(x,i),gel(y,i)));
  return gerepileupto(av, Fq_red(c,T,p));
}

/***********************************************************************/
/**                                                                   **/
/**                       Barrett reduction                           **/
/**                                                                   **/
/***********************************************************************/

/* Return new lgpol */
static long
ZXX_lgrenormalizespec(GEN x, long lx)
{
  long i;
  for (i = lx-1; i>=0; i--)
    if (signe(gel(x,i))) break;
  return i+1;
}

static GEN
FpXQX_invBarrett_basecase(GEN S, GEN T, GEN p)
{
  long i, l=lg(S)-1, lr = l-1, k;
  GEN r=cgetg(lr, t_POL); r[1]=S[1];
  gel(r,2) = gen_1;
  for (i=3; i<lr; i++)
  {
    pari_sp av = avma;
    GEN u = gel(S,l-i+2);
    for (k=3; k<i; k++)
      u = Fq_add(u, Fq_mul(gel(S,l-i+k), gel(r,k), NULL, p), NULL, p);
    gel(r,i) = gerepileupto(av, Fq_red(Fq_neg(u, NULL, p), T, p));
  }
  return FpXQX_renormalize(r,lr);
}

INLINE GEN
FpXX_recipspec(GEN x, long l, long n)
{
  return RgX_recipspec_shallow(x, l, n);
}

static GEN
FpXQX_invBarrett_Newton(GEN S, GEN T, GEN p)
{
  pari_sp av = avma;
  long nold, lx, lz, lq, l = degpol(S), i, lQ;
  GEN q, y, z, x = cgetg(l+2, t_POL) + 2;
  ulong mask = quadratic_prec_mask(l-2); /* assume l > 2 */
  for (i=0;i<l;i++) gel(x,i) = gen_0;
  q = RgX_recipspec_shallow(S+2,l+1,l+1); lQ = lgpol(q); q+=2;
  /* We work on _spec_ FpX's, all the l[xzq] below are lgpol's */

  /* initialize */
  gel(x,0) = Fq_inv(gel(q,0), T, p);
  if (lQ>1) gel(q,1) = Fq_red(gel(q,1), T, p);
  if (lQ>1 && signe(gel(q,1)))
  {
    GEN u = gel(q, 1);
    if (!gequal1(gel(x,0))) u = Fq_mul(u, Fq_sqr(gel(x,0), T, p), T, p);
    gel(x,1) = Fq_neg(u, T, p); lx = 2;
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
    lq = ZXX_lgrenormalizespec(q, minss(lQ,lnew));
    z = FpXQX_mulspec(x, q, T, p, lx, lq); /* FIXME: high product */
    lz = lgpol(z); if (lz > lnew) lz = lnew;
    z += 2;
    /* subtract 1 [=>first nold words are 0]: renormalize so that z(0) != 0 */
    for (i = nold; i < lz; i++) if (signe(gel(z,i))) break;
    nold = nnew;
    if (i >= lz) continue; /* z-1 = 0(t^(nnew + 1)) */

    /* z + i represents (x*q - 1) / t^i */
    lz = ZXX_lgrenormalizespec (z+i, lz-i);
    z = FpXQX_mulspec(x, z+i, T, p, lx, lz); /* FIXME: low product */
    lz = lgpol(z); z += 2;
    if (lz > lnew-i) lz = ZXX_lgrenormalizespec(z, lnew-i);

    lx = lz+ i;
    y  = x + i; /* x -= z * t^i, in place */
    for (i = 0; i < lz; i++) gel(y,i) = Fq_neg(gel(z,i), T, p);
  }
  x -= 2; setlg(x, lx + 2); x[1] = S[1];
  return gerepilecopy(av, x);
}

/* 1/polrecip(S)+O(x^(deg(S)-1)) */
GEN
FpXQX_invBarrett(GEN S, GEN T, GEN p)
{
  pari_sp ltop = avma;
  long l = lg(S);
  GEN r;
  if (l<5) return pol_0(varn(S));
  if (l<=FpXQX_INVBARRETT_LIMIT)
  {
    GEN c = gel(S,l-1), ci=gen_1;
    if (!gequal1(c))
    {
      ci = Fq_inv(c, T, p);
      S = FqX_Fq_mul(S, ci, T, p);
      r = FpXQX_invBarrett_basecase(S, T, p);
      r = FqX_Fq_mul(r, ci, T, p);
    } else
      r = FpXQX_invBarrett_basecase(S, T, p);
  }
  else
    r = FpXQX_invBarrett_Newton(S, T, p);
  return gerepileupto(ltop, r);
}

GEN
FpXQX_get_red(GEN S, GEN T, GEN p)
{
  if (typ(S)==t_POL && lg(S)>FpXQX_BARRETT_LIMIT)
    retmkvec2(FpXQX_invBarrett(S,T,p),S);
  return S;
}

/* Compute x mod S where 2 <= degpol(S) <= l+1 <= 2*(degpol(S)-1)
 * and mg is the Barrett inverse of S. */
static GEN
FpXQX_divrem_Barrettspec(GEN x, long l, GEN mg, GEN S, GEN T, GEN p, GEN *pr)
{
  GEN q, r;
  long lt = degpol(S); /*We discard the leading term*/
  long ld, lm, lT, lmg;
  ld = l-lt;
  lm = minss(ld, lgpol(mg));
  lT  = ZXX_lgrenormalizespec(S+2,lt);
  lmg = ZXX_lgrenormalizespec(mg+2,lm);
  q = FpXX_recipspec(x+lt,ld,ld);                 /* q = rec(x)     lq<=ld*/
  q = FpXQX_mulspec(q+2,mg+2,T,p,lgpol(q),lmg);    /* q = rec(x) * mg lq<=ld+lm*/
  q = FpXX_recipspec(q+2,minss(ld,lgpol(q)),ld);  /* q = rec (rec(x) * mg) lq<=ld*/
  if (!pr) return q;
  r = FpXQX_mulspec(q+2,S+2,T,p,lgpol(q),lT);      /* r = q*pol        lr<=ld+lt*/
  r = FpXX_subspec(x,r+2,p,lt,minss(lt,lgpol(r))); /* r = x - r   lr<=lt */
  if (pr == ONLY_REM) return r;
  *pr = r; return q;
}

static GEN
FpXQX_divrem_Barrett_noGC(GEN x, GEN mg, GEN S, GEN T, GEN p, GEN *pr)
{
  long l = lgpol(x), lt = degpol(S), lm = 2*lt-1;
  GEN q = NULL, r;
  long i;
  if (l <= lt)
  {
    if (pr == ONLY_REM) return ZXX_copy(x);
    if (pr == ONLY_DIVIDES) return signe(x)? NULL: pol_0(varn(x));
    if (pr) *pr =  ZXX_copy(x);
    return pol_0(varn(x));
  }
  if (lt <= 1)
    return FpXQX_divrem_basecase(x,S,T,p,pr);
  if (pr != ONLY_REM && l>lm)
  {
    q = cgetg(l-lt+2, t_POL);
    for (i=0;i<l-lt;i++) gel(q+2,i) = gen_0;
  }
  r = l>lm ? shallowcopy(x): x;
  while (l>lm)
  {
    GEN zr, zq = FpXQX_divrem_Barrettspec(r+2+l-lm,lm,mg,S,T,p,&zr);
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
      GEN zq = FpXQX_divrem_Barrettspec(r+2,l,mg,S,T,p,&r);
      if (!q) q = zq;
      else
      {
        long lq = lgpol(zq);
        for(i=0; i<lq; i++) gel(q+2,i) = gel(zq,2+i);
      }
    }
    else
    { setlg(r, l+2); r = ZXX_copy(r); }
  }
  else
  {
    if (l > lt)
      (void) FpXQX_divrem_Barrettspec(r+2,l,mg,S,T,p,&r);
    else
    { setlg(r, l+2); r = ZXX_copy(r); }
    r[1] = x[1]; return FpXQX_renormalize(r, lg(r));
  }
  if (pr) { r[1] = x[1]; r = FpXQX_renormalize(r, lg(r)); }
  q[1] = x[1]; q = FpXQX_renormalize(q, lg(q));
  if (pr == ONLY_DIVIDES) return signe(r)? NULL: q;
  if (pr) *pr = r;
  return q;
}

GEN
FpXQX_divrem(GEN x, GEN S, GEN T, GEN p, GEN *pr)
{
  GEN B, y = get_FpXQX_red(S, &B);
  long dy = degpol(y), dx = degpol(x), d = dx-dy;
  if (pr==ONLY_REM) return FpXQX_rem(x, y, T, p);
  if (lgefint(p) == 3)
  {
    GEN a, b, t, z;
    pari_sp tetpil, av = avma;
    ulong pp = to_FlxqX(x, y, T, p, &a, &b, &t);
    z = FlxqX_divrem(a, b, t, pp, pr);
    if (pr == ONLY_DIVIDES && !z) { avma = av; return NULL; }
    tetpil=avma;
    z = FlxX_to_ZXX(z);
    if (pr && pr != ONLY_DIVIDES && pr != ONLY_REM)
      *pr = FlxX_to_ZXX(*pr);
    else return gerepile(av, tetpil, z);
    gerepileallsp(av,tetpil,2, pr, &z);
    return z;
  }
  if (!B && d+3 < FpXQX_DIVREM_BARRETT_LIMIT)
    return FpXQX_divrem_basecase(x,y,T,p,pr);
  else
  {
    pari_sp av=avma;
    GEN mg = B? B: FpXQX_invBarrett(y, T, p);
    GEN q = FpXQX_divrem_Barrett_noGC(x,mg,y,T,p,pr);
    if (!q) {avma=av; return NULL;}
    if (!pr || pr==ONLY_DIVIDES) return gerepilecopy(av, q);
    gerepileall(av,2,&q,pr);
    return q;
  }
}

GEN
FpXQX_rem(GEN x, GEN S, GEN T, GEN p)
{
  GEN B, y = get_FpXQX_red(S, &B);
  long dy = degpol(y), dx = degpol(x), d = dx-dy;
  if (d < 0) return FpXQX_red(x, T, p);
  if (lgefint(p) == 3)
  {
    pari_sp av = avma;
    GEN a, b, t, z;
    ulong pp = to_FlxqX(x, y, T, p, &a, &b, &t);
    z = FlxqX_rem(a, b, t, pp);
    z = FlxX_to_ZXX(z);
    return gerepileupto(av, z);
  }
  if (!B && d+3 < FpXQX_REM_BARRETT_LIMIT)
    return FpXQX_divrem_basecase(x,y, T, p, ONLY_REM);
  else
  {
    pari_sp av=avma;
    GEN mg = B? B: FpXQX_invBarrett(y, T, p);
    GEN r = FpXQX_divrem_Barrett_noGC(x, mg, y, T, p, ONLY_REM);
    return gerepileupto(av, r);
  }
}

/* x + y*z mod p */
INLINE GEN
Fq_addmul(GEN x, GEN y, GEN z, GEN T, GEN p)
{
  pari_sp av;
  if (!signe(y) || !signe(z)) return Fq_red(x, T, p);
  if (!signe(x)) return Fq_mul(z,y, T, p);
  av = avma;
  return gerepileupto(av, Fq_add(x, Fq_mul(y, z, T, p), T, p));
}

GEN
FpXQX_div_by_X_x(GEN a, GEN x, GEN T, GEN p, GEN *r)
{
  long l = lg(a)-1, i;
  GEN z = cgetg(l, t_POL);
  z[1] = evalsigne(1) | evalvarn(0);
  gel(z, l-1) = gel(a,l);
  for (i=l-2; i>1; i--) /* z[i] = a[i+1] + x*z[i+1] */
    gel(z, i) = Fq_addmul(gel(a,i+1), x, gel(z,i+1), T, p);
  if (r) *r = Fq_addmul(gel(a,2), x, gel(z,2), T, p);
  return z;
}

struct _FpXQXQ {
  GEN T, S;
  GEN p;
};

static GEN _FpXQX_mul(void *data, GEN a,GEN b)
{
  struct _FpXQXQ *d=(struct _FpXQXQ*)data;
  return FpXQX_mul(a,b,d->T,d->p);
}

static GEN _FpXQX_sqr(void *data, GEN a)
{
  struct _FpXQXQ *d=(struct _FpXQXQ*)data;
  return FpXQX_sqr(a, d->T, d->p);
}

GEN
FpXQX_powu(GEN x, ulong n, GEN T, GEN p)
{
  struct _FpXQXQ D;
  if (n==0) return pol_1(varn(x));
  D.T = T; D.p = p;
  return gen_powu(x, n, (void *)&D, _FpXQX_sqr, _FpXQX_mul);
}

GEN
FpXQXV_prod(GEN V, GEN T, GEN p)
{
  if (lgefint(p) == 3)
  {
    pari_sp av = avma;
    ulong pp = p[2];
    GEN Tl = ZXT_to_FlxT(T, pp);
    GEN Vl = ZXXV_to_FlxXV(V, pp, get_FpX_var(T));
    Tl = FlxqXV_prod(Vl, Tl, pp);
    return gerepileupto(av, FlxX_to_ZXX(Tl));
  }
  else
  {
    struct _FpXQXQ d;
    d.T=T; d.p=p;
    return gen_product(V, (void*)&d, &_FpXQX_mul);
  }
}

static GEN
_FpXQX_divrem(void * E, GEN x, GEN y, GEN *r)
{
  struct _FpXQXQ *d = (struct _FpXQXQ *) E;
  return FpXQX_divrem(x, y, d->T, d->p, r);
}

static GEN
_FpXQX_add(void * E, GEN x, GEN y)
{
  struct _FpXQXQ *d = (struct _FpXQXQ *) E;
  return FpXX_add(x, y, d->p);
}

static GEN
_FpXQX_sub(void * E, GEN x, GEN y) {
  struct _FpXQXQ *d = (struct _FpXQXQ*) E;
  return FpXX_sub(x,y, d->p);
}

static struct bb_ring FpXQX_ring = { _FpXQX_add, _FpXQX_mul, _FpXQX_sqr };

GEN
FpXQX_digits(GEN x, GEN B, GEN T, GEN p)
{
  pari_sp av = avma;
  long d = degpol(B), n = (lgpol(x)+d-1)/d;
  GEN z;
  struct _FpXQXQ D;
  D.T = T; D.p = p;
  z = gen_digits(x, B, n, (void *)&D, &FpXQX_ring, _FpXQX_divrem);
  return gerepileupto(av, z);
}

GEN
FpXQXV_FpXQX_fromdigits(GEN x, GEN B, GEN T, GEN p)
{
  pari_sp av = avma;
  struct _FpXQXQ D;
  GEN z;
  D.T = T; D.p = p;
  z = gen_fromdigits(x,B,(void *)&D, &FpXQX_ring);
  return gerepileupto(av, z);
}

/* Q an FpXY (t_POL with FpX coeffs), evaluate at X = x */
GEN
FpXY_evalx(GEN Q, GEN x, GEN p)
{
  long i, lb = lg(Q);
  GEN z;
  z = cgetg(lb, t_POL); z[1] = Q[1];
  for (i=2; i<lb; i++)
  {
    GEN q = gel(Q,i);
    gel(z,i) = typ(q) == t_INT? modii(q,p): FpX_eval(q, x, p);
  }
  return FpX_renormalize(z, lb);
}
/* Q an FpXY, evaluate at Y = y */
GEN
FpXY_evaly(GEN Q, GEN y, GEN p, long vx)
{
  pari_sp av = avma;
  long i, lb = lg(Q);
  GEN z;
  if (!signe(Q)) return pol_0(vx);
  if (lb == 3 || !signe(y)) {
    z = gel(Q, 2);
    return typ(z)==t_INT? scalar_ZX(z, vx): ZX_copy(z);
  }
  z = gel(Q, lb-1);
  if (typ(z) == t_INT) z = scalar_ZX_shallow(z, vx);
  for (i=lb-2; i>=2; i--) z = Fq_add(gel(Q,i), FpX_Fp_mul(z, y, p), NULL, p);
  return gerepileupto(av, z);
}
/* Q an FpXY, evaluate at (X,Y) = (x,y) */
GEN
FpXY_eval(GEN Q, GEN y, GEN x, GEN p)
{
  pari_sp av = avma;
  return gerepileuptoint(av, FpX_eval(FpXY_evalx(Q, x, p), y, p));
}

GEN
FpXY_FpXQV_evalx(GEN P, GEN x, GEN T, GEN p)
{
  long i, lP = lg(P);
  GEN res = cgetg(lP,t_POL);
  res[1] = P[1];
  for(i=2; i<lP; i++)
    gel(res,i) = typ(gel(P,i))==t_INT? icopy(gel(P,i)):
                                       FpX_FpXQV_eval(gel(P,i), x, T, p);
  return FlxX_renormalize(res, lP);
}

GEN
FpXY_FpXQ_evalx(GEN P, GEN x, GEN T, GEN p)
{
  pari_sp av = avma;
  long n = brent_kung_optpow(get_FpX_degree(T)-1,lgpol(P),1);
  GEN xp = FpXQ_powers(x, n, T, p);
  return gerepileupto(av, FpXY_FpXQV_evalx(P, xp, T, p));
}

/*******************************************************************/
/*                                                                 */
/*                       (Fp[X]/T(X))[Y] / S(Y)                    */
/*                                                                 */
/*******************************************************************/

/*Preliminary implementation to speed up FpX_ffisom*/
typedef struct {
  GEN S, T, p;
} FpXYQQ_muldata;

/* reduce x in Fp[X, Y] in the algebra Fp[X,Y]/ (S(X),T(Y)) */
static GEN
FpXYQQ_redswap(GEN x, GEN S, GEN T, GEN p)
{
  pari_sp ltop=avma;
  long n = get_FpX_degree(S);
  long m = get_FpX_degree(T);
  long v = get_FpX_var(T);
  GEN V = RgXY_swap(x,m,v);
  V = FpXQX_red(V,S,p);
  V = RgXY_swap(V,n,v);
  return gerepilecopy(ltop,V);
}
static GEN
FpXYQQ_sqr(void *data, GEN x)
{
  FpXYQQ_muldata *D = (FpXYQQ_muldata*)data;
  return FpXYQQ_redswap(FpXQX_sqr(x, D->T, D->p),D->S,D->T,D->p);

}
static GEN
FpXYQQ_mul(void *data, GEN x, GEN y)
{
  FpXYQQ_muldata *D = (FpXYQQ_muldata*)data;
  return FpXYQQ_redswap(FpXQX_mul(x,y, D->T, D->p),D->S,D->T,D->p);
}

/* x in Z[X,Y], S in Z[X] over Fq = Z[Y]/(p,T); compute lift(x^n mod (S,T,p)) */
GEN
FpXYQQ_pow(GEN x, GEN n, GEN S, GEN T, GEN p)
{
  pari_sp av = avma;
  FpXYQQ_muldata D;
  GEN y;
  if (lgefint(p) == 3)
  {
    ulong pp = to_FlxqX(x, NULL, T, p, &x, NULL, &T);
    S = ZX_to_Flx(S, pp);
    y = FlxX_to_ZXX( FlxYqq_pow(x, n, S, T, pp) );
  }
  else
  {
    D.S = S;
    D.T = T;
    D.p = p;
    y = gen_pow(x, n, (void*)&D, &FpXYQQ_sqr, &FpXYQQ_mul);
  }
  return gerepileupto(av, y);
}

GEN
FpXQXQ_mul(GEN x, GEN y, GEN S, GEN T, GEN p) {
  return FpXQX_rem(FpXQX_mul(x, y, T, p), S, T, p);
}

GEN
FpXQXQ_sqr(GEN x, GEN S, GEN T, GEN p) {
  return FpXQX_rem(FpXQX_sqr(x, T, p), S, T, p);
}

/* Inverse of x in Z/pZ[X]/(pol) or NULL if inverse doesn't exist
 * return lift(1 / (x mod (p,pol))) */
GEN
FpXQXQ_invsafe(GEN x, GEN S, GEN T, GEN p)
{
  GEN V, z = FpXQX_extgcd(get_FpXQX_mod(S), x, T, p, NULL, &V);
  if (degpol(z)) return NULL;
  z = gel(z,2);
  z = typ(z)==t_INT ? Fp_invsafe(z,p) : FpXQ_invsafe(z,T,p);
  if (!z) return NULL;
  return typ(z)==t_INT ? FpXX_Fp_mul(V, z, p): FpXQX_FpXQ_mul(V, z, T, p);
}

GEN
FpXQXQ_inv(GEN x, GEN S, GEN T,GEN p)
{
  pari_sp av = avma;
  GEN U = FpXQXQ_invsafe(x, S, T, p);
  if (!U) pari_err_INV("FpXQXQ_inv",x);
  return gerepileupto(av, U);
}

GEN
FpXQXQ_div(GEN x,GEN y,GEN S, GEN T,GEN p)
{
  pari_sp av = avma;
  return gerepileupto(av, FpXQXQ_mul(x, FpXQXQ_inv(y,S,T,p),S,T,p));
}

static GEN
_FpXQXQ_cmul(void *data, GEN P, long a, GEN x) {
  struct _FpXQXQ *d = (struct _FpXQXQ*) data;
  GEN y = gel(P,a+2);
  return typ(y)==t_INT ? FpXX_Fp_mul(x,y, d->p):
                         FpXX_FpX_mul(x,y,d->p);
}
static GEN
_FpXQXQ_red(void *data, GEN x) {
  struct _FpXQXQ *d = (struct _FpXQXQ*) data;
  return FpXQX_red(x, d->T, d->p);
}
static GEN
_FpXQXQ_mul(void *data, GEN x, GEN y) {
  struct _FpXQXQ *d = (struct _FpXQXQ*) data;
  return FpXQXQ_mul(x,y, d->S,d->T, d->p);
}
static GEN
_FpXQXQ_sqr(void *data, GEN x) {
  struct _FpXQXQ *d = (struct _FpXQXQ*) data;
  return FpXQXQ_sqr(x, d->S,d->T, d->p);
}

static GEN
_FpXQXQ_one(void *data) {
  struct _FpXQXQ *d = (struct _FpXQXQ*) data;
  return pol_1(get_FpXQX_var(d->S));
}

static GEN
_FpXQXQ_zero(void *data) {
  struct _FpXQXQ *d = (struct _FpXQXQ*) data;
  return pol_0(get_FpXQX_var(d->S));
}

static struct bb_algebra FpXQXQ_algebra = { _FpXQXQ_red, _FpXQX_add,
       _FpXQX_sub, _FpXQXQ_mul, _FpXQXQ_sqr, _FpXQXQ_one, _FpXQXQ_zero };

const struct bb_algebra *
get_FpXQXQ_algebra(void **E, GEN S, GEN T, GEN p)
{
  GEN z = new_chunk(sizeof(struct _FpXQXQ));
  struct _FpXQXQ *e = (struct _FpXQXQ *) z;
  e->T = FpX_get_red(T, p);
  e->S = FpXQX_get_red(S, e->T, p);
  e->p  = p; *E = (void*)e;
  return &FpXQXQ_algebra;
}

static struct bb_algebra FpXQX_algebra = { _FpXQXQ_red, _FpXQX_add,
       _FpXQX_sub, _FpXQX_mul, _FpXQX_sqr, _FpXQXQ_one, _FpXQXQ_zero };

const struct bb_algebra *
get_FpXQX_algebra(void **E, GEN T, GEN p, long v)
{
  GEN z = new_chunk(sizeof(struct _FpXQXQ));
  struct _FpXQXQ *e = (struct _FpXQXQ *) z;
  e->T = FpX_get_red(T, p);
  e->S = pol_x(v);
  e->p  = p; *E = (void*)e;
  return &FpXQX_algebra;
}

/* x over Fq, return lift(x^n) mod S */
GEN
FpXQXQ_pow(GEN x, GEN n, GEN S, GEN T, GEN p)
{
  pari_sp ltop = avma;
  GEN y;
  struct _FpXQXQ D;
  long s = signe(n);
  if (!s) return pol_1(varn(x));
  if (is_pm1(n)) /* +/- 1 */
    return (s < 0)? FpXQXQ_inv(x,S,T,p): ZXX_copy(x);
  if (lgefint(p) == 3)
  {
    ulong pp = to_FlxqX(x, S, T, p, &x, &S, &T);
    GEN z = FlxqXQ_pow(x, n, S, T, pp);
    y = FlxX_to_ZXX(z);
  }
  else
  {
    T = FpX_get_red(T, p);
    S = FpXQX_get_red(S, T, p);
    D.S = S; D.T = T; D.p = p;
    if (s < 0) x = FpXQXQ_inv(x,S,T,p);
    y = gen_pow(x, n, (void*)&D,&_FpXQXQ_sqr,&_FpXQXQ_mul);
  }
  return gerepileupto(ltop, y);
}

/* generates the list of powers of x of degree 0,1,2,...,l*/
GEN
FpXQXQ_powers(GEN x, long l, GEN S, GEN T, GEN p)
{
  struct _FpXQXQ D;
  int use_sqr = 2*degpol(x) >= get_FpXQX_degree(S);
  T = FpX_get_red(T, p);
  S = FpXQX_get_red(S, T, p);
  D.S = S; D.T = T; D.p = p;
  return gen_powers(x, l, use_sqr, (void*)&D, &_FpXQXQ_sqr, &_FpXQXQ_mul,&_FpXQXQ_one);
}

/* Let v a linear form, return the linear form z->v(tau*z)
   that is, v*(M_tau) */

INLINE GEN
FpXQX_recipspec(GEN x, long l, long n)
{
  return RgX_recipspec_shallow(x, l, n);
}

static GEN
FpXQXQ_transmul_init(GEN tau, GEN S, GEN T, GEN p)
{
  GEN bht;
  GEN h, Sp = get_FpXQX_red(S, &h);
  long n = degpol(Sp), vT = varn(Sp);
  GEN ft = FpXQX_recipspec(Sp+2, n+1, n+1);
  GEN bt = FpXQX_recipspec(tau+2, lgpol(tau), n);
  setvarn(ft, vT); setvarn(bt, vT);
  if (h)
    bht = FpXQXn_mul(bt, h, n-1, T, p);
  else
  {
    GEN bh = FpXQX_div(RgX_shift_shallow(tau, n-1), S, T, p);
    bht = FpXQX_recipspec(bh+2, lgpol(bh), n-1);
    setvarn(bht, vT);
  }
  return mkvec3(bt, bht, ft);
}

static GEN
FpXQXQ_transmul(GEN tau, GEN a, long n, GEN T, GEN p)
{
  pari_sp ltop = avma;
  GEN t1, t2, t3, vec;
  GEN bt = gel(tau, 1), bht = gel(tau, 2), ft = gel(tau, 3);
  if (signe(a)==0) return pol_0(varn(a));
  t2 = RgX_shift_shallow(FpXQX_mul(bt, a, T, p),1-n);
  if (signe(bht)==0) return gerepilecopy(ltop, t2);
  t1 = RgX_shift_shallow(FpXQX_mul(ft, a, T, p),-n);
  t3 = FpXQXn_mul(t1, bht, n-1, T, p);
  vec = FpXX_sub(t2, RgX_shift_shallow(t3, 1), p);
  return gerepileupto(ltop, vec);
}

static GEN
polxn_FpXX(long n, long v, long vT)
{
  long i, a = n+2;
  GEN p = cgetg(a+1, t_POL);
  p[1] = evalsigne(1)|evalvarn(v);
  for (i = 2; i < a; i++) gel(p,i) = pol_0(vT);
  gel(p,a) = pol_1(vT); return p;
}

GEN
FpXQXQ_minpoly(GEN x, GEN S, GEN T, GEN p)
{
  pari_sp ltop = avma;
  long vS, vT, n;
  GEN v_x, g, tau;
  vS = get_FpXQX_var(S);
  vT = get_FpX_var(T);
  n = get_FpXQX_degree(S);
  g = pol_1(vS);
  tau = pol_1(vS);
  S = FpXQX_get_red(S, T, p);
  v_x = FpXQXQ_powers(x, usqrt(2*n), S, T, p);
  while(signe(tau) != 0)
  {
    long i, j, m, k1;
    GEN M, v, tr;
    GEN g_prime, c;
    if (degpol(g) == n) { tau = pol_1(vS); g = pol_1(vS); }
    v = random_FpXQX(n, vS, T, p);
    tr = FpXQXQ_transmul_init(tau, S, T, p);
    v = FpXQXQ_transmul(tr, v, n, T, p);
    m = 2*(n-degpol(g));
    k1 = usqrt(m);
    tr = FpXQXQ_transmul_init(gel(v_x,k1+1), S, T, p);
    c = cgetg(m+2,t_POL);
    c[1] = evalsigne(1)|evalvarn(vS);
    for (i=0; i<m; i+=k1)
    {
      long mj = minss(m-i, k1);
      for (j=0; j<mj; j++)
        gel(c,m+1-(i+j)) = FpXQX_dotproduct(v, gel(v_x,j+1), T, p);
      v = FpXQXQ_transmul(tr, v, n, T, p);
    }
    c = FpXX_renormalize(c, m+2);
    /* now c contains <v,x^i> , i = 0..m-1  */
    M = FpXQX_halfgcd(polxn_FpXX(m, vS, vT), c, T, p);
    g_prime = gmael(M, 2, 2);
    if (degpol(g_prime) < 1) continue;
    g = FpXQX_mul(g, g_prime, T, p);
    tau = FpXQXQ_mul(tau, FpXQX_FpXQXQV_eval(g_prime, v_x, S, T, p), S, T, p);
  }
  g = FpXQX_normalize(g,T, p);
  return gerepilecopy(ltop,g);
}

GEN
FpXQXQ_matrix_pow(GEN y, long n, long m, GEN S, GEN T, GEN p)
{
  return RgXV_to_RgM(FpXQXQ_powers(y,m-1,S,T,p),n);
}

GEN
FpXQX_FpXQXQV_eval(GEN P, GEN V, GEN S, GEN T, GEN p)
{
  struct _FpXQXQ D;
  T = FpX_get_red(T, p);
  S = FpXQX_get_red(S, T, p);
  D.S=S; D.T=T; D.p=p;
  return gen_bkeval_powers(P, degpol(P), V, (void*)&D, &FpXQXQ_algebra,
                                                   _FpXQXQ_cmul);
}

GEN
FpXQX_FpXQXQ_eval(GEN Q, GEN x, GEN S, GEN T, GEN p)
{
  struct _FpXQXQ D;
  int use_sqr = 2*degpol(x) >= get_FpXQX_degree(S);
  T = FpX_get_red(T, p);
  S = FpXQX_get_red(S, T, p);
  D.S=S; D.T=T; D.p=p;
  return gen_bkeval(Q, degpol(Q), x, use_sqr, (void*)&D, &FpXQXQ_algebra,
      _FpXQXQ_cmul);
}

static GEN
FpXQXQ_autpow_sqr(void * E, GEN x)
{
  struct _FpXQXQ *D = (struct _FpXQXQ *)E;
  GEN S = D->S, T = D->T, p = D->p;
  GEN phi = gel(x,1), S1 = gel(x,2);
  long n = brent_kung_optpow(get_FpX_degree(T)-1,lgpol(S1)+1,1);
  GEN V = FpXQ_powers(phi, n, T, p);
  GEN phi2 = FpX_FpXQV_eval(phi, V, T, p);
  GEN Sphi = FpXY_FpXQV_evalx(S1, V, T, p);
  GEN S2 = FpXQX_FpXQXQ_eval(Sphi, S1, S, T, p);
  return mkvec2(phi2, S2);
}

static GEN
FpXQXQ_autpow_mul(void * E, GEN x, GEN y)
{
  struct _FpXQXQ *D = (struct _FpXQXQ *)E;
  GEN S = D->S, T = D->T, p = D->p;
  GEN phi1 = gel(x,1), S1 = gel(x,2);
  GEN phi2 = gel(y,1), S2 = gel(y,2);
  long n = brent_kung_optpow(get_FpX_degree(T)-1, lgpol(S1)+1, 1);
  GEN V = FpXQ_powers(phi2, n, T, p);
  GEN phi3 = FpX_FpXQV_eval(phi1, V, T, p);
  GEN Sphi = FpXY_FpXQV_evalx(S1, V, T, p);
  GEN S3 = FpXQX_FpXQXQ_eval(Sphi, S2, S, T, p);
  return mkvec2(phi3, S3);
}

GEN
FpXQXQ_autpow(GEN aut, long n, GEN S, GEN T, GEN p)
{
  struct _FpXQXQ D;
  T = FpX_get_red(T, p);
  S = FpXQX_get_red(S, T, p);
  D.S=S; D.T=T; D.p=p;
  return gen_powu(aut,n,&D,FpXQXQ_autpow_sqr,FpXQXQ_autpow_mul);
}

static GEN
FpXQXQ_auttrace_mul(void *E, GEN x, GEN y)
{
  struct _FpXQXQ *D = (struct _FpXQXQ *)E;
  GEN S = D->S, T = D->T;
  GEN p = D->p;
  GEN S1 = gel(x,1), a1 = gel(x,2);
  GEN S2 = gel(y,1), a2 = gel(y,2);
  long n = brent_kung_optpow(maxss(degpol(S1),degpol(a1)),2,1);
  GEN V = FpXQXQ_powers(S2, n, S, T, p);
  GEN S3 = FpXQX_FpXQXQV_eval(S1, V, S, T, p);
  GEN aS = FpXQX_FpXQXQV_eval(a1, V, S, T, p);
  GEN a3 = FpXX_add(aS, a2, p);
  return mkvec2(S3, a3);
}

static GEN
FpXQXQ_auttrace_sqr(void *E, GEN x)
{ return FpXQXQ_auttrace_mul(E, x, x); }

GEN
FpXQXQ_auttrace(GEN aut, long n, GEN S, GEN T, GEN p)
{
  struct _FpXQXQ D;
  T = FpX_get_red(T, p);
  S = FpXQX_get_red(S, T, p);
  D.S=S; D.T=T; D.p=p;
  return gen_powu(aut,n,&D,FpXQXQ_auttrace_sqr,FpXQXQ_auttrace_mul);
}

static GEN
FpXQXQ_autsum_mul(void *E, GEN x, GEN y)
{
  struct _FpXQXQ *D = (struct _FpXQXQ *) E;
  GEN S = D->S, T = D->T, p = D->p;
  GEN phi1 = gel(x,1), S1 = gel(x,2), a1 = gel(x,3);
  GEN phi2 = gel(y,1), S2 = gel(y,2), a2 = gel(y,3);
  long n2 = brent_kung_optpow(get_FpX_degree(T)-1, lgpol(S1)+lgpol(a1)+1, 1);
  GEN V2 = FpXQ_powers(phi2, n2, T, p);
  GEN phi3 = FpX_FpXQV_eval(phi1, V2, T, p);
  GEN Sphi = FpXY_FpXQV_evalx(S1, V2, T, p);
  GEN aphi = FpXY_FpXQV_evalx(a1, V2, T, p);
  long n = brent_kung_optpow(maxss(degpol(Sphi),degpol(aphi)),2,1);
  GEN V = FpXQXQ_powers(S2, n, S, T, p);
  GEN S3 = FpXQX_FpXQXQV_eval(Sphi, V, S, T, p);
  GEN aS = FpXQX_FpXQXQV_eval(aphi, V, S, T, p);
  GEN a3 = FpXQXQ_mul(aS, a2, S, T, p);
  return mkvec3(phi3, S3, a3);
}

static GEN
FpXQXQ_autsum_sqr(void * T, GEN x)
{ return FpXQXQ_autsum_mul(T,x,x); }

GEN
FpXQXQ_autsum(GEN aut, long n, GEN S, GEN T, GEN p)
{
  struct _FpXQXQ D;
  T = FpX_get_red(T, p);
  S = FpXQX_get_red(S, T, p);
  D.S=S; D.T=T; D.p=p;
  return gen_powu(aut,n,&D,FpXQXQ_autsum_sqr,FpXQXQ_autsum_mul);
}

GEN
FpXQXn_mul(GEN x, GEN y, long n, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN z, kx, ky;
  long d;
  if (ZXX_is_ZX(y) && ZXX_is_ZX(x))
    return FpXn_mul(x,y,n,p);
  d = get_FpX_degree(T);
  kx = ZXX_to_Kronecker(x, d);
  ky = ZXX_to_Kronecker(y, d);
  z = Kronecker_to_FpXQX(ZXn_mul(ky,kx,(2*d-1)*n), T, p);
  return gerepileupto(av, z);
}

GEN
FpXQXn_sqr(GEN x, long n, GEN T, GEN p)
{
  pari_sp av = avma;
  GEN z, kx;
  long d;
  if (ZXX_is_ZX(x)) return ZXn_sqr(x, n);
  d = get_FpX_degree(T);
  kx= ZXX_to_Kronecker(x, d);
  z = Kronecker_to_FpXQX(ZXn_sqr(kx, (2*d-1)*n), T, p);
  return gerepileupto(av, z);
}

INLINE GEN
FpXXn_red(GEN a, long n)
{ return RgXn_red_shallow(a, n); }

GEN
FpXQXn_exp(GEN h, long e, GEN T, GEN p)
{
  pari_sp av = avma, av2;
  long v = varn(h), n=1;
  GEN f = pol_1(v), g = pol_1(v);
  ulong mask = quadratic_prec_mask(e);
  av2 = avma;
  if (signe(h)==0 || degpol(h)<1 || !gequal0(gel(h,2)))
    pari_err_DOMAIN("FpXQXn_exp","valuation", "<", gen_1, h);
  for (;mask>1;)
  {
    GEN q, w;
    long n2 = n;
    n<<=1; if (mask & 1) n--;
    mask >>= 1;
    g = FpXX_sub(FpXX_mulu(g,2,p), FpXQXn_mul(f, FpXQXn_sqr(g, n2, T, p), n2, T, p), p);
    q = FpXX_deriv(FpXXn_red(h,n2), p);
    w = FpXX_add(q, FpXQXn_mul(g, FpXX_sub(FpXX_deriv(f, p), FpXQXn_mul(f,q,n-1, T, p), p),n-1, T, p), p);
    f = FpXX_add(f, FpXQXn_mul(f, FpXX_sub(FpXXn_red(h, n), FpXX_integ(w, p), p), n, T, p), p);
    if (gc_needed(av2,2))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"FpXQXn_exp, e = %ld", n);
      gerepileall(av2, 2, &f, &g);
    }
  }
  return gerepileupto(av, f);
}

/* (f*g) \/ x^n */
static GEN
FpXQX_mulhigh_i(GEN f, GEN g, long n, GEN T, GEN p)
{
  return RgX_shift_shallow(FpXQX_mul(f,g,T, p),-n);
}

static GEN
FpXQXn_mulhigh(GEN f, GEN g, long n2, long n, GEN T, GEN p)
{
  GEN F = RgX_blocks(f, n2, 2), fl = gel(F,1), fh = gel(F,2);
  return FpXX_add(FpXQX_mulhigh_i(fl, g, n2, T, p), FpXQXn_mul(fh, g, n - n2, T, p), p);
}

GEN
FpXQXn_inv(GEN f, long e, GEN T, GEN p)
{
  pari_sp av = avma, av2;
  ulong mask;
  GEN W, a;
  long v = varn(f), n = 1;

  if (!signe(f)) pari_err_INV("FpXXn_inv",f);
  a = Fq_inv(gel(f,2), T, p);
  if (e == 1) return scalarpol(a, v);
  else if (e == 2)
  {
    GEN b;
    if (degpol(f) <= 0) return scalarpol(a, v);
    b = Fq_neg(gel(f,3),T,p);
    if (signe(b)==0) return scalarpol(a, v);
    if (!is_pm1(a)) b = Fq_mul(b, Fq_sqr(a, T, p), T, p);
    W = deg1pol_shallow(b, a, v);
    return gerepilecopy(av, W);
  }
  W = scalarpol_shallow(Fq_inv(gel(f,2), T, p),v);
  mask = quadratic_prec_mask(e);
  av2 = avma;
  for (;mask>1;)
  {
    GEN u, fr;
    long n2 = n;
    n<<=1; if (mask & 1) n--;
    mask >>= 1;
    fr = FpXXn_red(f, n);
    u = FpXQXn_mul(W, FpXQXn_mulhigh(fr, W, n2, n, T, p), n-n2, T, p);
    W = FpXX_sub(W, RgX_shift_shallow(u, n2), p);
    if (gc_needed(av2,2))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"FpXQXn_inv, e = %ld", n);
      W = gerepileupto(av2, W);
    }
  }
  return gerepileupto(av, W);
}
