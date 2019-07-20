/* Copyright (C) 2000-2003  The PARI group.

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

/*************************************************************************/
/**                                                                     **/
/**                   Routines for handling FFELT                       **/
/**                                                                     **/
/*************************************************************************/

/*************************************************************************/
/**                                                                     **/
/**                   Low-level constructors                            **/
/**                                                                     **/
/*************************************************************************/

INLINE void
_getFF(GEN x, GEN *T, GEN *p, ulong *pp)
{
  *T=gel(x,3);
  *p=gel(x,4);
  *pp=(*p)[2];
}

INLINE GEN
_initFF(GEN x, GEN *T, GEN *p, ulong *pp)
{
  _getFF(x,T,p,pp);
  return cgetg(5,t_FFELT);
}

INLINE void
_checkFF(GEN x, GEN y, const char *s)
{ if (!FF_samefield(x,y)) pari_err_OP(s,x,y); }

INLINE GEN
_mkFF(GEN x, GEN z, GEN r)
{
  z[1]=x[1];
  gel(z,2)=r;
  gel(z,3)=gcopy(gel(x,3));
  gel(z,4)=icopy(gel(x,4));
  return z;
}

INLINE GEN
_mkFF_i(GEN x, GEN z, GEN r)
{
  z[1]=x[1];
  gel(z,2)=r;
  gel(z,3)=gel(x,3);
  gel(z,4)=gel(x,4);
  return z;
}

INLINE GEN
mkFF_i(GEN x, GEN r)
{
  GEN z = cgetg(5,t_FFELT);
  return _mkFF_i(x,z,r);
}

/*************************************************************************/
/**                                                                     **/
/**                   medium-level constructors                         **/
/**                                                                     **/
/*************************************************************************/

static GEN
Z_to_raw(GEN x, GEN ff)
{
  ulong pp;
  GEN T, p;
  _getFF(ff,&T,&p,&pp);
  switch(ff[1])
  {
  case t_FF_FpXQ:
    return scalarpol(x, varn(T));
  case t_FF_F2xq:
    return Z_to_F2x(x,varn(T));
  default:
    return Z_to_Flx(x,pp,T[1]);
  }
}

static GEN
Rg_to_raw(GEN x, GEN ff)
{
  long tx = typ(x);
  switch(tx)
  {
  case t_INT: case t_FRAC: case t_PADIC: case t_INTMOD:
    return Z_to_raw(Rg_to_Fp(x, FF_p_i(ff)), ff);
  case t_FFELT:
    if (!FF_samefield(x,ff))
      pari_err_MODULUS("Rg_to_raw",x,ff);
    return gel(x,2);
  }
  pari_err_TYPE("Rg_to_raw",x);
  return NULL; /* LCOV_EXCL_LINE */
}

static GEN
FFX_to_raw(GEN x, GEN ff)
{
  long i, lx;
  GEN y = cgetg_copy(x,&lx);
  y[1] = x[1];
  for(i=2; i<lx; i++)
    gel(y, i) = Rg_to_raw(gel(x, i), ff);
  switch (ff[1])
  {
  case t_FF_FpXQ:
    return FpXX_renormalize(y, lx);
  case t_FF_F2xq:
    return F2xX_renormalize(y, lx);
  default:
    return FlxX_renormalize(y, lx);
  }
}

static GEN
FFC_to_raw(GEN x, GEN ff)
{ pari_APPLY_same(Rg_to_raw(gel(x, i), ff)) }

static GEN
FFM_to_raw(GEN x, GEN ff)
{ pari_APPLY_same(FFC_to_raw(gel(x, i), ff)) }

/* in place */
static GEN
rawFq_to_FF(GEN x, GEN ff)
{
  return mkFF_i(ff, typ(x)==t_INT ? scalarpol(x, varn(gel(ff,3))): x);
}

/* in place */
static GEN
raw_to_FFX(GEN x, GEN ff)
{
  long i, lx = lg(x);
  for (i=2; i<lx; i++) gel(x,i) = rawFq_to_FF(gel(x,i), ff);
  return x;
}

/* in place */
static GEN
raw_to_FFC(GEN x, GEN ff)
{
  long i, lx = lg(x);
  for (i=1; i<lx; i++) gel(x,i) = mkFF_i(ff, gel(x,i));
  return x;
}

/* in place */
static GEN
raw_to_FFM(GEN x, GEN ff)
{
  long i, lx = lg(x);
  for (i=1; i<lx; i++) gel(x,i) = raw_to_FFC(gel(x,i), ff);
  return x;
}

GEN
Fq_to_FF(GEN x, GEN ff)
{
  ulong pp;
  GEN r, T, p, z=_initFF(ff,&T,&p,&pp);
  int is_int = typ(x)==t_INT;
  switch(ff[1])
  {
  case t_FF_FpXQ:
    r= is_int ? scalarpol(x, varn(T)): x;
    break;
  case t_FF_F2xq:
    r= is_int ? Z_to_F2x(x,T[1]): ZX_to_F2x(x);
    break;
  default:
    r= is_int ? Z_to_Flx(x,pp,T[1]): ZX_to_Flx(x,pp);
  }
  setvarn(r, varn(T)); /* paranoia */
  return _mkFF_i(ff,z,r);
}

/*************************************************************************/
/**                                                                     **/
/**                   Public functions                                  **/
/**                                                                     **/
/*************************************************************************/

/* Return true if x and y are defined in the same field */

static int
FF_samechar(GEN x, GEN y)
{
  return x[1] == y[1] && equalii(gel(x,4),gel(y,4));
}

int
FF_samefield(GEN x, GEN y)
{
  return FF_samechar(x, y) && gidentical(gel(x,3),gel(y,3));
}

int
FF_equal(GEN x, GEN y)
{ return FF_samefield(x,y) && gidentical(gel(x,2),gel(y,2)); }

int
FF_equal0(GEN x)
{
  return lgpol(gel(x,2))==0;
}

int
FF_equal1(GEN x)
{
  GEN A = gel(x,2);
  switch(x[1])
  {
  case t_FF_FpXQ:
    return degpol(A)==0 && gequal1(gel(A,2));
  default:
    return degpol(A)==0 && A[2]==1;
  }
}

static int
Fp_cmp_1(GEN x, GEN p)
{
  pari_sp av = avma;
  int b = equalii(x, addis(p,-1));
  avma = av; return b;
}

int
FF_equalm1(GEN x)
{
  ulong pp;
  GEN T, p, y = gel(x,2);
  _getFF(x,&T,&p,&pp);
  switch(x[1])
  {
  case t_FF_FpXQ:
    return (degpol(y) == 0 && Fp_cmp_1(gel(y,2), p));
  default:
    return (degpol(y) == 0 && uel(y,2) == pp-1);
  }
}

GEN
FF_zero(GEN x)
{
  ulong pp;
  GEN r, T, p, z=_initFF(x,&T,&p,&pp);
  switch(x[1])
  {
  case t_FF_FpXQ:
    r=zeropol(varn(T));
    break;
  case t_FF_F2xq:
    r=zero_F2x(T[1]);
    break;
  default:
    r=zero_Flx(T[1]);
  }
  return _mkFF(x,z,r);
}

GEN
FF_1(GEN x)
{
  ulong pp;
  GEN r, T, p, z=_initFF(x,&T,&p,&pp);
  switch(x[1])
  {
  case t_FF_FpXQ:
    r=pol_1(varn(T));
    break;
  case t_FF_F2xq:
    r=pol1_F2x(T[1]);
    break;
  default:
    r=pol1_Flx(T[1]);
  }
  return _mkFF(x,z,r);
}

GEN
FF_gen(GEN x)
{
  ulong pp;
  GEN r, T, p, z=_initFF(x,&T,&p,&pp);
  switch(x[1])
  {
  case t_FF_FpXQ:
    r = pol_x(varn(T));
    if (degpol(T)==1) r = FpX_rem(r, T, p);
    break;
  case t_FF_F2xq:
    r = polx_F2x(T[1]);
    if (F2x_degree(T)==1) r = F2x_rem(r, T);
    break;
  default:
    r = polx_Flx(T[1]);
    if (degpol(T)==1) r = Flx_rem(r, T, pp);
  }
  return _mkFF(x,z,r);
}
GEN
FF_q(GEN x)
{
  ulong pp;
  GEN T, p;
  _getFF(x,&T,&p,&pp);
  switch(x[1])
  {
  case t_FF_FpXQ:
    return powiu(p, degpol(T));
    break;
  case t_FF_F2xq:
    return int2n(F2x_degree(T));
    break;
  default:
    return powuu(pp,degpol(T));
  }
}

GEN
FF_p(GEN x)
{
  return icopy(gel(x,4));
}

GEN
FF_p_i(GEN x)
{
  return gel(x,4);
}

GEN
FF_mod(GEN x)
{
  switch(x[1])
  {
  case t_FF_FpXQ:
    return ZX_copy(gel(x,3));
  case t_FF_F2xq:
    return F2x_to_ZX(gel(x,3));
  default:
    return Flx_to_ZX(gel(x,3));
  }
}

long
FF_f(GEN x)
{
  switch(x[1])
  {
  case t_FF_F2xq:
    return F2x_degree(gel(x,3));
  default:
    return degpol(gel(x,3));
  }
}

GEN
FF_to_F2xq(GEN x)
{
  switch(x[1])
  {
  case t_FF_FpXQ:
    return ZX_to_F2x(gel(x,2));
  case t_FF_F2xq:
    return zv_copy(gel(x,2));
  default:
    return Flx_to_F2x(gel(x,2));
  }
}

GEN
FF_to_F2xq_i(GEN x)
{
  switch(x[1])
  {
  case t_FF_FpXQ:
    return ZX_to_F2x(gel(x,2));
  case t_FF_F2xq:
    return gel(x,2);
  default:
    return Flx_to_F2x(gel(x,2));
  }
}

GEN
FF_to_Flxq(GEN x)
{
  switch(x[1])
  {
  case t_FF_FpXQ:
    return ZX_to_Flx(gel(x,2),itou(gel(x,4)));
  case t_FF_F2xq:
    return F2x_to_Flx(gel(x,2));
  default:
    return zv_copy(gel(x,2));
  }
}

GEN
FF_to_Flxq_i(GEN x)
{
  switch(x[1])
  {
  case t_FF_FpXQ:
    return ZX_to_Flx(gel(x,2),itou(gel(x,4)));
  case t_FF_F2xq:
    return F2x_to_Flx(gel(x,2));
  default:
    return gel(x,2);
  }
}

GEN
FF_to_FpXQ(GEN x)
{
  switch(x[1])
  {
  case t_FF_FpXQ:
    return ZX_copy(gel(x,2));
  case t_FF_F2xq:
    return F2x_to_ZX(gel(x,2));
  default:
    return Flx_to_ZX(gel(x,2));
  }
}

GEN
FF_to_FpXQ_i(GEN x)
{
  switch(x[1])
  {
  case t_FF_FpXQ:
    return gel(x,2);
  case t_FF_F2xq:
    return F2x_to_ZX(gel(x,2));
  default:
    return Flx_to_ZX(gel(x,2));
  }
}

GEN
FF_add(GEN x, GEN y)
{
  ulong pp;
  GEN r, T, p, z=_initFF(x,&T,&p,&pp);
  _checkFF(x,y,"+");
  switch(x[1])
  {
  case t_FF_FpXQ:
    r=FpX_add(gel(x,2),gel(y,2),p);
    break;
  case t_FF_F2xq:
    r=F2x_add(gel(x,2),gel(y,2));
    break;
  default:
    r=Flx_add(gel(x,2),gel(y,2),pp);
  }
  return _mkFF(x,z,r);
}
GEN
FF_sub(GEN x, GEN y)
{
  ulong pp;
  GEN r, T, p, z=_initFF(x,&T,&p,&pp);
  _checkFF(x,y,"+");
  switch(x[1])
  {
  case t_FF_FpXQ:
    r=FpX_sub(gel(x,2),gel(y,2),p);
    break;
  case t_FF_F2xq:
    r=F2x_add(gel(x,2),gel(y,2));
    break;
  default:
    r=Flx_sub(gel(x,2),gel(y,2),pp);
  }
  return _mkFF(x,z,r);
}

GEN
FF_Z_add(GEN x, GEN y)
{
  ulong pp;
  GEN r, T, p, z=_initFF(x,&T,&p,&pp);
  switch(x[1])
  {
  case t_FF_FpXQ:
    {
      pari_sp av=avma;
      r=gerepileupto(av,FpX_Fp_add(gel(x,2),modii(y,p),p));
      break;
    }
  case t_FF_F2xq:
    r=mpodd(y)?F2x_1_add(gel(x,2)):vecsmall_copy(gel(x,2));
    break;
  default:
    r=Flx_Fl_add(gel(x,2),umodiu(y,pp),pp);
  }
  return _mkFF(x,z,r);
}

GEN
FF_Q_add(GEN x, GEN y)
{
  ulong pp;
  GEN r, T, p, z=_initFF(x,&T,&p,&pp);
  switch(x[1])
  {
  case t_FF_FpXQ:
    {
      pari_sp av=avma;
      r=gerepileupto(av,FpX_Fp_add(gel(x,2),Rg_to_Fp(y,p),p));
      break;
    }
  case t_FF_F2xq:
    r=Rg_to_Fl(y,pp)?F2x_1_add(gel(x,2)):vecsmall_copy(gel(x,2));
    break;
  default:
    r=Flx_Fl_add(gel(x,2),Rg_to_Fl(y,pp),pp);
  }
  return _mkFF(x,z,r);
}

GEN
FF_neg(GEN x)
{
  ulong pp;
  GEN r, T, p, z=_initFF(x,&T,&p,&pp);
  switch(x[1])
  {
  case t_FF_FpXQ:
    r=FpX_neg(gel(x,2),p);
    break;
  case t_FF_F2xq:
    r=vecsmall_copy(gel(x,2));
    break;
  default:
    r=Flx_neg(gel(x,2),pp);
  }
  return _mkFF(x,z,r);
}

GEN
FF_neg_i(GEN x)
{
  ulong pp;
  GEN r, T, p, z=_initFF(x,&T,&p,&pp);
  switch(x[1])
  {
  case t_FF_FpXQ:
    r=FpX_neg(gel(x,2),p);
    break;
  case t_FF_F2xq:
    r=gel(x,2);
    break;
  default:
    r=Flx_neg(gel(x,2),pp);
  }
  return _mkFF_i(x,z,r);
}

GEN
FF_map(GEN m, GEN x)
{
  ulong pp;
  GEN r, T, p, z=_initFF(m,&T,&p,&pp);
  switch(m[1])
  {
  case t_FF_FpXQ:
    r=FpX_FpXQ_eval(gel(x,2),gel(m,2),T,p);
    break;
  case t_FF_F2xq:
    r=F2x_F2xq_eval(gel(x,2),gel(m,2),T);
    break;
  default:
    r=Flx_Flxq_eval(gel(x,2),gel(m,2),T,pp);
  }
  return _mkFF(m,z,r);
}

GEN
FF_Frobenius(GEN x, long e)
{
  ulong pp;
  GEN r, T, p, z=_initFF(x,&T,&p,&pp);
  ulong n = umodsu(e, FF_f(x));
  if (n==0) return gcopy(x);
  switch(x[1])
  {
  case t_FF_FpXQ:
    r=FpXQ_pow(gel(x,2),p,T,p);
    if (n>1) r=FpXQ_autpow(r,n,T,p);
    break;
  case t_FF_F2xq:
    r=F2xq_sqr(gel(x,2),T);
    if (n>1) r=F2xq_autpow(r,n,T);
    break;
  default:
    r=Flxq_powu(gel(x,2),pp,T,pp);
    if (n>1) r=Flxq_autpow(r,n,T,pp);
  }
  return _mkFF(x,z,r);
}

GEN
FFX_preimage(GEN x, GEN F, GEN y)
{
  GEN r, T, p, z;
  ulong pp;
  if (FF_equal0(x)) return FF_zero(y);
  z=_initFF(y,&T,&p,&pp);
  F = FFX_to_raw(F, y);
  switch(y[1])
  {
  case t_FF_FpXQ:
    r = FpXQX_rem(gel(x,2), F, T, p);
    break;
  case t_FF_F2xq:
    r = F2xqX_rem(F2x_to_F2xX(gel(x,2),T[1]), F, T);
    break;
  default:
    r = FlxqX_rem(Flx_to_FlxX(gel(x,2),T[1]), F, T, pp);
  }
  if (degpol(r) > 0) return NULL;
  r = (y[1] == t_FF_FpXQ)? Fq_to_FpXQ(gel(r,2),T, p): gel(r,2);
  return _mkFF(y,z,r);
}

GEN
FF_mul(GEN x, GEN y)
{
  ulong pp;
  GEN r, T, p, z=_initFF(x,&T,&p,&pp);
  pari_sp av=avma;
  _checkFF(x,y,"*");
  switch(x[1])
  {
  case t_FF_FpXQ:
    r=FpXQ_mul(gel(x,2),gel(y,2),T,p);
    break;
  case t_FF_F2xq:
    r=F2xq_mul(gel(x,2),gel(y,2),T);
    break;
  default:
    r=Flxq_mul(gel(x,2),gel(y,2),T,pp);
  }
  return _mkFF(x,z,gerepileupto(av, r));
}

GEN
FF_Z_mul(GEN x, GEN y)
{
  ulong pp;
  GEN r, T, p, A = gel(x,2), z=_initFF(x,&T,&p,&pp);
  switch(x[1])
  {
  case t_FF_FpXQ: /* modii(y,p) left on stack for efficiency */
    r = FpX_Fp_mul(A, modii(y,p),p);
    break;
  case t_FF_F2xq:
    r = mpodd(y)? vecsmall_copy(A): zero_Flx(A[1]);
    break;
  default:
    r = Flx_Fl_mul(A, umodiu(y,pp), pp);
  }
  return _mkFF(x,z,r);
}

GEN
FF_Z_Z_muldiv(GEN x, GEN a, GEN b)
{
  ulong pp;
  GEN r, T, p, A = gel(x,2), z=_initFF(x,&T,&p,&pp);
  switch(x[1])
  {
  case t_FF_FpXQ: /* Fp_div(a,b,p) left on stack for efficiency */
    r = FpX_Fp_mul(A, Fp_div(a,b,p), p);
    break;
  case t_FF_F2xq:
    if (!mpodd(b)) pari_err_INV("FF_Z_Z_muldiv", b);
    r = mpodd(a)? vecsmall_copy(A): zero_Flx(A[1]);
    break;
  default:
    r = Flx_Fl_mul(A, Fl_div(umodiu(a,pp),umodiu(b,pp),pp),pp);
  }
  return _mkFF(x,z,r);
}

GEN
FF_sqr(GEN x)
{
  ulong pp;
  GEN r, T, p, z=_initFF(x,&T,&p,&pp);
  switch(x[1])
  {
  case t_FF_FpXQ:
    {
      pari_sp av=avma;
      r=gerepileupto(av,FpXQ_sqr(gel(x,2),T,p));
      break;
    }
  case t_FF_F2xq:
    r=F2xq_sqr(gel(x,2),T);
    break;
  default:
    r=Flxq_sqr(gel(x,2),T,pp);
  }
  return _mkFF(x,z,r);
}

GEN
FF_mul2n(GEN x, long n)
{
  ulong pp;
  GEN r, T, p, A = gel(x,2), z=_initFF(x,&T,&p,&pp);
  switch(x[1])
  {
  case t_FF_FpXQ:
    {
      GEN p1; /* left on stack for efficiency */
      if (n>0) p1=remii(int2n(n),p);
      else p1=Fp_inv(remii(int2n(-n),p),p);
      r = FpX_Fp_mul(A, p1, p);
    }
    break;
  case t_FF_F2xq:
    if (n<0) pari_err_INV("FF_mul2n", gen_2);
    r = n==0? vecsmall_copy(A): zero_Flx(A[1]);
    break;
  default:
    {
      ulong l1;
      if (n>0) l1 = umodiu(int2n(n),pp);
      else l1 = Fl_inv(umodiu(int2n(-n),pp),pp);
      r = Flx_Fl_mul(A,l1,pp);
    }
  }
  return _mkFF(x,z,r);
}

GEN
FF_inv(GEN x)
{
  ulong pp;
  GEN r, T, p, z=_initFF(x,&T,&p,&pp);
  pari_sp av=avma;
  switch(x[1])
  {
  case t_FF_FpXQ:
    r=gerepileupto(av,FpXQ_inv(gel(x,2),T,p));
    break;
  case t_FF_F2xq:
    r=F2xq_inv(gel(x,2),T);
    break;
  default:
    r=Flxq_inv(gel(x,2),T,pp);
  }
  return _mkFF(x,z,r);
}

GEN
FF_div(GEN x, GEN y)
{
  ulong pp;
  GEN r, T, p, z=_initFF(x,&T,&p,&pp);
  pari_sp av=avma;
  _checkFF(x,y,"/");
  switch(x[1])
  {
  case t_FF_FpXQ:
    r=gerepileupto(av,FpXQ_div(gel(x,2),gel(y,2),T,p));
    break;
  case t_FF_F2xq:
    r=gerepileupto(av,F2xq_div(gel(x,2),gel(y,2),T));
    break;
  default:
    r=gerepileupto(av,Flxq_div(gel(x,2),gel(y,2),T,pp));
  }
  return _mkFF(x,z,r);
}

GEN
Z_FF_div(GEN n, GEN x)
{
  ulong pp;
  GEN r, T, p, A = gel(x,2), z=_initFF(x,&T,&p,&pp);
  pari_sp av=avma;
  switch(x[1])
  {
  case t_FF_FpXQ:
    r = gerepileupto(av,FpX_Fp_mul(FpXQ_inv(A,T,p),modii(n,p),p));
    break;
  case t_FF_F2xq:
    r = F2xq_inv(A,T); /*Check for division by 0*/
    if(!mpodd(n)) { avma = av; r = zero_Flx(A[1]); }
    break;
  default:
    r = gerepileupto(av, Flx_Fl_mul(Flxq_inv(A,T,pp),umodiu(n,pp),pp));
  }
  return _mkFF(x,z,r);
}

GEN
FF_sqrtn(GEN x, GEN n, GEN *zetan)
{
  ulong pp;
  GEN r, T, p, y=_initFF(x,&T,&p,&pp);
  switch (x[1])
  {
  case t_FF_FpXQ:
    r=FpXQ_sqrtn(gel(x,2),n,T,p,zetan);
    break;
  case t_FF_F2xq:
    r=F2xq_sqrtn(gel(x,2),n,T,zetan);
    break;
  default:
    r=Flxq_sqrtn(gel(x,2),n,T,pp,zetan);
  }
  if (!r) pari_err_SQRTN("FF_sqrtn",x);
  (void)_mkFF(x, y, r);
  if (zetan)
  {
    GEN z = cgetg(lg(y),t_FFELT);
    *zetan=_mkFF(x, z, *zetan);
  }
  return y;
}

GEN
FF_sqrt(GEN x)
{
  ulong pp;
  GEN r, T, p, y=_initFF(x,&T,&p,&pp);
  switch (x[1])
  {
  case t_FF_FpXQ:
    r = FpXQ_sqrt(gel(x,2),T,p);
    break;
  case t_FF_F2xq:
    r = F2xq_sqrt(gel(x,2),T);
    break;
  default:
    r = Flxq_sqrt(gel(x,2),T,pp);
  }
  if (!r) pari_err_SQRTN("FF_sqrt",x);
  return _mkFF(x, y, r);
}

long
FF_issquare(GEN x)
{
  GEN T, p;
  ulong pp;
  _getFF(x, &T, &p, &pp);
  switch(x[1])
  {
  case t_FF_FpXQ:
    return FpXQ_issquare(gel(x,2), T, p);
  case t_FF_F2xq:
    return 1;
  default: /* case t_FF_Flxq: */
    return Flxq_issquare(gel(x,2), T, pp);
  }
}

long
FF_issquareall(GEN x, GEN *pt)
{
  if (!pt) return FF_issquare(x);
  return FF_ispower(x, gen_2, pt);
}

long
FF_ispower(GEN x, GEN K, GEN *pt)
{
  ulong pp;
  GEN r, T, p;
  pari_sp av = avma;

  if (FF_equal0(x)) { if (pt) *pt = gcopy(x); return 1; }
  _getFF(x, &T, &p, &pp);
  if (pt) *pt = cgetg(5,t_FFELT);
  switch(x[1])
  {
  case t_FF_FpXQ:
    r = FpXQ_sqrtn(gel(x,2),K,T,p,NULL);
    break;
  case t_FF_F2xq:
    r = F2xq_sqrtn(gel(x,2),K,T,NULL);
    break;
  default: /* case t_FF_Flxq: */
    r = Flxq_sqrtn(gel(x,2),K,T,pp,NULL);
    break;
  }
  if (!r) { avma = av; return 0; }
  if (pt) { (void)_mkFF(x,*pt,r); }
  return 1;
}

GEN
FF_pow(GEN x, GEN n)
{
  ulong pp;
  GEN r, T, p, z=_initFF(x,&T,&p,&pp);
  switch(x[1])
   {
   case t_FF_FpXQ:
     r = FpXQ_pow(gel(x,2), n, T, p);
     break;
   case t_FF_F2xq:
     r = F2xq_pow(gel(x,2), n, T);
     break;
   default:
     r = Flxq_pow(gel(x,2), n, T, pp);
   }
  return _mkFF(x,z,r);
}

GEN
FF_norm(GEN x)
{
  ulong pp;
  GEN T,p;
  _getFF(x,&T,&p,&pp);
  switch (x[1])
  {
  case t_FF_FpXQ:
    return FpXQ_norm(gel(x,2),T,p);
  case t_FF_F2xq:
    return lgpol(gel(x,2))?gen_1:gen_0;
  default:
    return utoi(Flxq_norm(gel(x,2),T,pp));
  }
}

GEN
FF_trace(GEN x)
{
  ulong pp;
  GEN T,p;
  _getFF(x,&T,&p,&pp);
  switch(x[1])
  {
  case t_FF_FpXQ:
    return FpXQ_trace(gel(x,2),T,p);
  case t_FF_F2xq:
    return F2xq_trace(gel(x,2),T)?gen_1:gen_0;
  default:
    return utoi(Flxq_trace(gel(x,2),T,pp));
  }
}

GEN
FF_conjvec(GEN x)
{
  ulong pp;
  GEN r,T,p,v;
  long i,l;
  pari_sp av;
  _getFF(x,&T,&p,&pp);
  av = avma;
  switch(x[1])
  {
  case t_FF_FpXQ:
    v = FpXQ_conjvec(gel(x,2), T, p);
    break;
  case t_FF_F2xq:
    v = F2xq_conjvec(gel(x,2), T);
    break;
  default:
    v = Flxq_conjvec(gel(x,2), T, pp);
  }
  l = lg(v); r = cgetg(l, t_COL);
  for(i=1; i<l; i++)
    gel(r,i) = mkFF_i(x, gel(v,i));
  return gerepilecopy(av, r);
}

GEN
FF_charpoly(GEN x)
{
  ulong pp;
  GEN T,p;
  pari_sp av=avma;
  _getFF(x,&T,&p,&pp);
  switch(x[1])
  {
  case t_FF_FpXQ:
    return gerepileupto(av,FpXQ_charpoly(gel(x,2), T, p));
  case t_FF_F2xq:
    return gerepileupto(av,Flx_to_ZX(Flxq_charpoly(F2x_to_Flx(gel(x,2)),
                                                   F2x_to_Flx(T), 2UL)));
  default:
    return gerepileupto(av,Flx_to_ZX(Flxq_charpoly(gel(x,2), T, pp)));
  }
}

GEN
FF_minpoly(GEN x)
{
  ulong pp;
  GEN T,p;
  pari_sp av=avma;
  _getFF(x,&T,&p,&pp);
  switch(x[1])
  {
  case t_FF_FpXQ:
    return gerepileupto(av,FpXQ_minpoly(gel(x,2), T, p));
  case t_FF_F2xq:
    return gerepileupto(av,Flx_to_ZX(Flxq_minpoly(F2x_to_Flx(gel(x,2)),
                                                  F2x_to_Flx(T), 2UL)));
  default:
    return gerepileupto(av,Flx_to_ZX(Flxq_minpoly(gel(x,2), T, pp)));
  }
}

GEN
FF_log(GEN x, GEN g, GEN ord)
{
  pari_sp av=avma;
  ulong pp;
  GEN r, T, p;
  _getFF(x,&T,&p,&pp);
  _checkFF(x,g,"log");
  switch(x[1])
  {
  case t_FF_FpXQ:
    if (!ord) ord = factor_pn_1(p,degpol(T));
    r = FpXQ_log(gel(x,2), gel(g,2), ord, T, p);
    break;
  case t_FF_F2xq:
    if (!ord) ord = factor_pn_1(gen_2,F2x_degree(T));
    r = F2xq_log(gel(x,2), gel(g,2), ord, T);
    break;
  default:
    if (!ord) ord = factor_pn_1(p,degpol(T));
    r = Flxq_log(gel(x,2), gel(g,2), ord, T, pp);
  }
  return gerepileupto(av, r);
}

GEN
FF_order(GEN x, GEN o)
{
  pari_sp av=avma;
  ulong pp;
  GEN r, T,p;
  _getFF(x,&T,&p,&pp);
  switch(x[1])
  {
  case t_FF_FpXQ:
    if (!o) o = factor_pn_1(p,degpol(T));
    r = FpXQ_order(gel(x,2), o, T, p);
    break;
  case t_FF_F2xq:
    if (!o) o = factor_pn_1(gen_2,F2x_degree(T));
    r = F2xq_order(gel(x,2), o, T);
    break;
  default:
    if (!o) o = factor_pn_1(p,degpol(T));
    r = Flxq_order(gel(x,2), o, T, pp);
  }
  if (!o) r = gerepileuptoint(av,r);
  return r;
}

GEN
FF_primroot(GEN x, GEN *o)
{
  ulong pp;
  GEN r,T,p,z=_initFF(x,&T,&p,&pp);
  switch(x[1])
  {
  case t_FF_FpXQ:
    r = gener_FpXQ(T, p, o);
    break;
  case t_FF_F2xq:
    r = gener_F2xq(T, o);
    break;
  default:
    r = gener_Flxq(T, pp, o);
  }
  return _mkFF(x,z,r);
}

static GEN
to_FFE(GEN P, GEN fg)
{
  if(ell_is_inf(P))
    return ellinf();
  else
    retmkvec2(mkFF_i(fg,gel(P,1)), mkFF_i(fg,gel(P,2)));
}

static GEN
to_FFE_vec(GEN x, GEN ff)
{
  long i, lx = lg(x);
  for (i=1; i<lx; i++) gel(x,i) = to_FFE(gel(x,i), ff);
  return x;
}

static GEN
FpXQ_ell_to_a4a6(GEN E, GEN T, GEN p)
{
  GEN a1, a3, b2, c4, c6;
  a1 = Rg_to_FpXQ(ell_get_a1(E),T,p);
  a3 = Rg_to_FpXQ(ell_get_a3(E),T,p);
  b2 = Rg_to_FpXQ(ell_get_b2(E),T,p);
  c4 = Rg_to_FpXQ(ell_get_c4(E),T,p);
  c6 = Rg_to_FpXQ(ell_get_c6(E),T,p);
  retmkvec3(FpX_neg(FpX_mulu(c4, 27, p), p), FpX_neg(FpX_mulu(c6, 54, p), p),
            mkvec4(Z_to_FpX(utoi(6),p,varn(T)),FpX_mulu(b2,3,p),
                   FpX_mulu(a1,3,p),FpX_mulu(a3,108,p)));
}

static GEN
F3xq_ell_to_a4a6(GEN E, GEN T)
{
  GEN a1, a3, b2, b4, b6;
  a1 = Rg_to_Flxq(ell_get_a1(E),T,3);
  a3 = Rg_to_Flxq(ell_get_a3(E),T,3);
  b2 = Rg_to_Flxq(ell_get_b2(E),T,3);
  b4 = Rg_to_Flxq(ell_get_b4(E),T,3);
  b6 = Rg_to_Flxq(ell_get_b6(E),T,3);
  if(lgpol(b2)) /* ordinary case */
  {
    GEN b4b2 = Flxq_div(b4,b2,T,3);
    GEN a6 = Flx_sub(b6,Flxq_mul(b4b2,Flx_add(b4,Flxq_sqr(b4b2,T,3),3),T,3),3);
    retmkvec3(mkvec(b2), a6,
       mkvec4(Fl_to_Flx(1,T[1]),b4b2,Flx_neg(a1,3),Flx_neg(a3,3)));
  }
  else /* super-singular case */
    retmkvec3(Flx_neg(b4, 3), b6,
       mkvec4(Fl_to_Flx(1,T[1]),zero_Flx(T[1]), Flx_neg(a1,3), Flx_neg(a3,3)));
}

static GEN
Flxq_ell_to_a4a6(GEN E, GEN T, ulong p)
{
  GEN a1, a3, b2, c4, c6;
  if(p==3) return F3xq_ell_to_a4a6(E, T);
  a1 = Rg_to_Flxq(ell_get_a1(E),T,p);
  a3 = Rg_to_Flxq(ell_get_a3(E),T,p);
  b2 = Rg_to_Flxq(ell_get_b2(E),T,p);
  c4 = Rg_to_Flxq(ell_get_c4(E),T,p);
  c6 = Rg_to_Flxq(ell_get_c6(E),T,p);
  retmkvec3(Flx_neg(Flx_mulu(c4, 27, p), p), Flx_neg(Flx_mulu(c6, 54, p), p),
            mkvec4(Fl_to_Flx(6%p,T[1]),Flx_mulu(b2,3,p),
                   Flx_mulu(a1,3,p),Flx_mulu(a3,108,p)));
}

static GEN
F2xq_ell_to_a4a6(GEN E, GEN T)
{
  long v = T[1];
  GEN a1 = Rg_to_F2xq(ell_get_a1(E),T);
  GEN a2 = Rg_to_F2xq(ell_get_a2(E),T);
  GEN a3 = Rg_to_F2xq(ell_get_a3(E),T);
  GEN a4 = Rg_to_F2xq(ell_get_a4(E),T);
  GEN a6 = Rg_to_F2xq(ell_get_a6(E),T);
  if (lgpol(a1))
  {
    GEN a1i = F2xq_inv(a1,T);
    GEN a1i2 = F2xq_sqr(a1i,T);
    GEN a1i3 = F2xq_mul(a1i,a1i2,T);
    GEN a1i6 = F2xq_sqr(a1i3,T);
    GEN d  = F2xq_mul(a3,a1i,T);
    GEN dd = F2xq_mul(d,a1i2,T);
    GEN e  = F2xq_mul(F2x_add(a4,F2xq_sqr(d,T)),a1i,T);
    GEN ee = F2xq_mul(e,a1i3,T);
    GEN da2 = F2x_add(a2,d);
    GEN d2 = F2xq_mul(da2,a1i2,T);
    GEN d6 = F2xq_mul(F2x_add(F2x_add(F2xq_mul(F2x_add(F2xq_mul(da2,d,T),a4),d,T),a6),F2xq_sqr(e,T)),a1i6,T);
    retmkvec3(d2, d6, mkvec4(a1i,dd,pol0_F2x(v),ee));
  }
  else
  { /* allow a1 = a3 = 0: singular curve */
    GEN d4 = F2x_add(F2xq_sqr(a2,T),a4);
    GEN d6 = F2x_add(F2xq_mul(a2,a4,T),a6);
    GEN a3i = lgpol(a3)? F2xq_inv(a3,T): a3;
    retmkvec3(mkvec3(a3,d4,a3i), d6, mkvec4(pol1_F2x(v),a2,pol0_F2x(T[1]),pol0_F2x(T[1])));
  }
}

static GEN
FqV_to_FpXQV(GEN x, GEN T)
{
  pari_sp av = avma;
  long v = varn(T), i, s=0, l = lg(x);
  GEN y = shallowcopy(x);
  for(i=1; i<l; i++)
    if (typ(gel(x,i))==t_INT)
    {
      gel(y,i) = scalarpol(gel(x,i), v);
      s = 1;
    }
  if (!s) { avma = av; return x; }
  return y;
}

GEN
FF_ellcard(GEN E)
{
  GEN T,p;
  ulong pp;
  GEN e = ellff_get_a4a6(E);
  GEN fg = ellff_get_field(E);
  _getFF(fg,&T,&p,&pp);
  switch(fg[1])
  {
  case t_FF_FpXQ:
    return FpXQ_ellcard(Fq_to_FpXQ(gel(e,1),T,p), Fq_to_FpXQ(gel(e,2),T,p),T,p);
  case t_FF_F2xq:
    return F2xq_ellcard(gel(e,1),gel(e,2),T);
  default:
    return Flxq_ellcard(gel(e,1),gel(e,2),T,pp);
  }
}

GEN
FF_ellcard_SEA(GEN E, long smallfact)
{
  pari_sp av = avma;
  GEN T,p;
  ulong pp;
  GEN e = ellff_get_a4a6(E), a4, a6, card;
  GEN fg = ellff_get_field(E);
  _getFF(fg,&T,&p,&pp);
  switch(fg[1])
  {
  case t_FF_FpXQ:
    a4 = Fq_to_FpXQ(gel(e,1), T, p);
    a6 = Fq_to_FpXQ(gel(e,2), T, p);
    card = Fq_ellcard_SEA(a4, a6, powiu(p,degpol(T)), T,p, smallfact);
    break;
  case t_FF_F2xq:
    pari_err_IMPL("SEA for char 2");
  default:
    a4 = Flx_to_ZX(gel(e,1));
    a6 = Flx_to_ZX(gel(e,2));
    card = Fq_ellcard_SEA(a4, a6, powuu(pp,degpol(T)), Flx_to_ZX(T), p, smallfact);
  }
  return gerepileuptoint(av, card);
}

/* return G, set m */
GEN
FF_ellgroup(GEN E, GEN *pm)
{
  GEN T, p, e, fg, N;
  ulong pp;

  N = ellff_get_card(E);
  e = ellff_get_a4a6(E);
  fg = ellff_get_field(E);
  _getFF(fg,&T,&p,&pp);
  switch(fg[1])
  {
  case t_FF_FpXQ:
    return FpXQ_ellgroup(Fq_to_FpXQ(gel(e,1),T,p),
                         Fq_to_FpXQ(gel(e,2),T,p),N,T,p,pm);
  case t_FF_F2xq:
    return F2xq_ellgroup(gel(e,1),gel(e,2),N,T,pm);
  default:
    return Flxq_ellgroup(gel(e,1),gel(e,2),N,T,pp,pm);
  }
}

GEN
FF_ellgens(GEN E)
{
  GEN D, fg, e, m, T, p, F, e3;
  ulong pp;

  fg = ellff_get_field(E);
  e = ellff_get_a4a6(E);
  m = ellff_get_m(E);
  D = ellff_get_D(E);
  _getFF(fg,&T,&p,&pp);
  switch(fg[1])
  {
  case t_FF_FpXQ:
    e3 = FqV_to_FpXQV(gel(e,3),T);
    F = FpXQ_ellgens(Fq_to_FpXQ(gel(e,1),T,p),Fq_to_FpXQ(gel(e,2),T,p),e3,D,m,T,p);
    break;
  case t_FF_F2xq:
    F = F2xq_ellgens(gel(e,1),gel(e,2),gel(e,3),D,m,T);
    break;
  default:
    F = Flxq_ellgens(gel(e,1),gel(e,2),gel(e,3),D,m,T, pp);
    break;
  }
  return to_FFE_vec(F,fg);
}

GEN
FF_elldata(GEN E, GEN fg)
{
  GEN T,p,e;
  ulong pp;
  _getFF(fg,&T,&p,&pp);
  switch(fg[1])
  {
  case t_FF_FpXQ:
    e = FpXQ_ell_to_a4a6(E,T,p); break;
  case t_FF_F2xq:
    e = F2xq_ell_to_a4a6(E,T); break;
  default:
    e = Flxq_ell_to_a4a6(E,T,pp); break;
  }
  return mkvec2(fg,e);
}

/* allow singular E, set E.j = 0 in this case */
GEN
FF_ellinit(GEN E, GEN fg)
{
  GEN T,p,e, D, c4, y = E;
  ulong pp;
  long i;
  _getFF(fg,&T,&p,&pp);
  switch(fg[1])
  {
  case t_FF_FpXQ:
    e = FpXQ_ell_to_a4a6(E,T,p);
    for(i=1;i<=12;i++) gel(y,i) = mkFF_i(fg,Rg_to_FpXQ(gel(E,i),T,p));
    break;
  case t_FF_F2xq:
    e = F2xq_ell_to_a4a6(E,T);
    for(i=1;i<=12;i++) gel(y,i) = mkFF_i(fg,Rg_to_F2xq(gel(E,i),T));
    break;
  default:
    e = Flxq_ell_to_a4a6(E,T,pp);
    for(i=1;i<=12;i++) gel(y,i) = mkFF_i(fg,Rg_to_Flxq(gel(E,i),T,pp));
    break;
  }
  D = ell_get_disc(y);
  c4 = ell_get_c4(y);
  gel(y,13) = FF_equal0(D)? D: gdiv(gpowgs(c4,3), D);
  gel(y,14) = mkvecsmall(t_ELL_Fq);
  gel(y,15) = mkvec2(fg,e);
  return y;
}

GEN
FF_elltwist(GEN E)
{
  pari_sp av = avma;
  GEN fg = ellff_get_field(E), e = ellff_get_a4a6(E);
  GEN T, p, a, a6, V;
  ulong pp;
  _getFF(fg,&T,&p,&pp);
  switch (fg[1])
  {
  case t_FF_FpXQ:
    FpXQ_elltwist(gel(e,1), gel(e,2), T, p, &a, &a6);
    V = mkvec5(gen_0, gen_0, gen_0, mkFF_i(fg, a), mkFF_i(fg, a6));
    break;
  case t_FF_F2xq:
    F2xq_elltwist(gel(e,1), gel(e,2), T, &a, &a6);
    V = typ(a)==t_VECSMALL ?
          mkvec5(gen_1, mkFF_i(fg, a), gen_0, gen_0, mkFF_i(fg, a6)):
          mkvec5(gen_0, gen_0, mkFF_i(fg, gel(a,1)), mkFF_i(fg, gel(a,2)), mkFF_i(fg, a6));
    break;
  default:
    Flxq_elltwist(gel(e,1), gel(e,2), T, pp, &a, &a6);
    V = typ(a)==t_VECSMALL ?
          mkvec5(gen_0, gen_0, gen_0, mkFF_i(fg, a), mkFF_i(fg, a6)):
          mkvec5(gen_0, mkFF_i(fg, gel(a,1)), gen_0, gen_0, mkFF_i(fg, a6));
  }
  return gerepilecopy(av, V);
}

static long
F3x_equalm1(GEN x)
{ return degpol(x)==0 && x[2] == 2; }

GEN
FF_ellrandom(GEN E)
{
  pari_sp av = avma;
  GEN fg = ellff_get_field(E), e = ellff_get_a4a6(E), Q;
  GEN T,p;
  ulong pp;
  _getFF(fg,&T,&p,&pp);
  switch (fg[1])
  {
  case t_FF_FpXQ:
    Q = random_FpXQE(Fq_to_FpXQ(gel(e,1),T,p), Fq_to_FpXQ(gel(e,2),T,p), T, p);
    Q = FpXQE_changepoint(Q, FqV_to_FpXQV(gel(e,3), T) , T, p);
    break;
  case t_FF_F2xq:
    {
      long d = F2x_degree(T);
      /* if #E(Fq) = 1 return [0] */
      if (d<=2 && typ(gel(e,1)) == t_VEC)
      { /* over F2 or F4, supersingular */
        GEN v = gel(e,1), A6 = gel(e,2), a3 = gel(v,1), A4 = gel(v,2);
        if (F2x_equal1(a3) &&
             ((d==1 && F2x_equal1(A4) && F2x_equal1(A6))
           || (d==2 && !lgpol(A4)     && F2x_degree(A6)==1))) return ellinf();
      }
      Q = random_F2xqE(gel(e,1), gel(e,2), T);
      Q = F2xqE_changepoint(Q, gel(e,3), T);
      break;
    }
  default:
    /* if #E(Fq) = 1 return [0] */
    if (pp==3 && degpol(T)==1 && typ(gel(e,1))==t_VECSMALL)
    { /* over F3, supersingular */
      GEN mb4 = gel(e,1), b6 = gel(e,2);
      if (F3x_equalm1(mb4) && F3x_equalm1(b6)) return ellinf();
    }
    Q = random_FlxqE(gel(e,1), gel(e,2), T, pp);
    Q = FlxqE_changepoint(Q, gel(e,3), T, pp);
  }
  return gerepilecopy(av, to_FFE(Q, fg));
}

GEN
FF_ellmul(GEN E, GEN P, GEN n)
{
  pari_sp av = avma;
  GEN fg = ellff_get_field(E), e = ellff_get_a4a6(E), Q;
  GEN T,p, Pp, Qp, e3;
  ulong pp;
  _getFF(fg,&T,&p,&pp);
  switch (fg[1])
  {
  case t_FF_FpXQ:
    e3 = FqV_to_FpXQV(gel(e,3),T);
    Pp = FpXQE_changepointinv(RgE_to_FpXQE(P, T, p), e3, T, p);
    Qp = FpXQE_mul(Pp, n, gel(e,1), T, p);
    Q = FpXQE_changepoint(Qp, gel(e,3), T, p);
    break;
  case t_FF_F2xq:
    Pp = F2xqE_changepointinv(RgE_to_F2xqE(P, T), gel(e,3), T);
    Qp = F2xqE_mul(Pp, n, gel(e,1), T);
    Q = F2xqE_changepoint(Qp, gel(e,3), T);
    break;
  default:
    Pp = FlxqE_changepointinv(RgE_to_FlxqE(P, T, pp), gel(e,3), T, pp);
    Qp = FlxqE_mul(Pp, n, gel(e,1), T, pp);
    Q = FlxqE_changepoint(Qp, gel(e,3), T, pp);
  }
  return gerepilecopy(av, to_FFE(Q, fg));
}

GEN
FF_ellorder(GEN E, GEN P, GEN o)
{
  pari_sp av = avma;
  GEN fg = ellff_get_field(E), e = ellff_get_a4a6(E);
  GEN r,T,p,Pp,e3;
  ulong pp;
  _getFF(fg,&T,&p,&pp);
  switch (fg[1])
  {
  case t_FF_FpXQ:
    e3 = FqV_to_FpXQV(gel(e,3),T);
    Pp = FpXQE_changepointinv(RgE_to_FpXQE(P,T,p), e3, T, p);
    r = FpXQE_order(Pp, o, gel(e,1), T, p);
    break;
  case t_FF_F2xq:
    Pp = F2xqE_changepointinv(RgE_to_F2xqE(P,T), gel(e,3), T);
    r = F2xqE_order(Pp, o, gel(e,1), T);
    break;
  default:
    Pp = FlxqE_changepointinv(RgE_to_FlxqE(P,T,pp), gel(e,3), T, pp);
    r = FlxqE_order(Pp, o, gel(e,1), T, pp);
  }
  return gerepileupto(av, r);
}

GEN
FF_elllog(GEN E, GEN P, GEN Q, GEN o)
{
  pari_sp av = avma;
  GEN fg = ellff_get_field(E), e = ellff_get_a4a6(E);
  GEN r,T,p, Pp,Qp, e3;
  ulong pp;
  _getFF(fg,&T,&p,&pp);
  switch(fg[1])
  {
  case t_FF_FpXQ:
    e3 = FqV_to_FpXQV(gel(e,3),T);
    Pp = FpXQE_changepointinv(RgE_to_FpXQE(P,T,p), e3, T, p);
    Qp = FpXQE_changepointinv(RgE_to_FpXQE(Q,T,p), e3, T, p);
    r = FpXQE_log(Pp, Qp, o, gel(e,1), T, p);
    break;
  case t_FF_F2xq:
    Pp = F2xqE_changepointinv(RgE_to_F2xqE(P,T), gel(e,3), T);
    Qp = F2xqE_changepointinv(RgE_to_F2xqE(Q,T), gel(e,3), T);
    r = F2xqE_log(Pp, Qp, o, gel(e,1), T);
    break;
  default:
    Pp = FlxqE_changepointinv(RgE_to_FlxqE(P,T,pp), gel(e,3), T, pp);
    Qp = FlxqE_changepointinv(RgE_to_FlxqE(Q,T,pp), gel(e,3), T, pp);
    r = FlxqE_log(Pp, Qp, o, gel(e,1), T, pp);
  }
  return gerepileupto(av, r);
}

GEN
FF_ellweilpairing(GEN E, GEN P, GEN Q, GEN m)
{
  GEN fg = ellff_get_field(E), e = ellff_get_a4a6(E);
  GEN r,T,p, Pp,Qp, e3;
  ulong pp;
  GEN z=_initFF(fg,&T,&p,&pp);
  pari_sp av = avma;
  switch(fg[1])
  {
  case t_FF_FpXQ:
    e3 = FqV_to_FpXQV(gel(e,3),T);
    Pp = FpXQE_changepointinv(RgE_to_FpXQE(P,T,p), e3, T, p);
    Qp = FpXQE_changepointinv(RgE_to_FpXQE(Q,T,p), e3, T, p);
    r = FpXQE_weilpairing(Pp, Qp, m, gel(e,1), T, p);
    break;
  case t_FF_F2xq:
    Pp = F2xqE_changepointinv(RgE_to_F2xqE(P,T), gel(e,3), T);
    Qp = F2xqE_changepointinv(RgE_to_F2xqE(Q,T), gel(e,3), T);
    r = F2xqE_weilpairing(Pp, Qp, m, gel(e,1), T);
    break;
  default:
    Pp = FlxqE_changepointinv(RgE_to_FlxqE(P,T,pp), gel(e,3), T, pp);
    Qp = FlxqE_changepointinv(RgE_to_FlxqE(Q,T,pp), gel(e,3), T, pp);
    r = FlxqE_weilpairing(Pp, Qp, m, gel(e,1), T, pp);
  }
  r = gerepileupto(av, r);
  return _mkFF(fg,z,r);
}

GEN
FF_elltatepairing(GEN E, GEN P, GEN Q, GEN m)
{
  GEN fg = ellff_get_field(E), e = ellff_get_a4a6(E);
  GEN r,T,p, Pp,Qp, e3;
  ulong pp;
  GEN z=_initFF(fg,&T,&p,&pp);
  pari_sp av = avma;
  switch(fg[1])
  {
  case t_FF_FpXQ:
    e3 = FqV_to_FpXQV(gel(e,3),T);
    Pp = FpXQE_changepointinv(RgE_to_FpXQE(P,T,p), e3, T, p);
    Qp = FpXQE_changepointinv(RgE_to_FpXQE(Q,T,p), e3, T, p);
    r = FpXQE_tatepairing(Pp, Qp, m, gel(e,1), T, p);
    break;
  case t_FF_F2xq:
    Pp = F2xqE_changepointinv(RgE_to_F2xqE(P,T), gel(e,3), T);
    Qp = F2xqE_changepointinv(RgE_to_F2xqE(Q,T), gel(e,3), T);
    r = F2xqE_tatepairing(Pp, Qp, m, gel(e,1), T);
    break;
  default:
    Pp = FlxqE_changepointinv(RgE_to_FlxqE(P,T,pp), gel(e,3), T, pp);
    Qp = FlxqE_changepointinv(RgE_to_FlxqE(Q,T,pp), gel(e,3), T, pp);
    r = FlxqE_tatepairing(Pp, Qp, m, gel(e,1), T, pp);
  }
  r = gerepileupto(av, r);
  return _mkFF(fg,z,r);
}

GEN
FFX_roots(GEN Pf, GEN ff)
{
  pari_sp av = avma;
  GEN r,T,p;
  ulong pp;
  GEN P = FFX_to_raw(Pf, ff);
  _getFF(ff,&T,&p,&pp);
  switch(ff[1])
  {
  case t_FF_FpXQ:
    r = FpXQX_roots(P, T, p);
    break;
  case t_FF_F2xq:
    r = F2xqX_roots(P, T);
    break;
  default:
    r = FlxqX_roots(P, T, pp);
  }
  return gerepilecopy(av, raw_to_FFC(r, ff));
}

static GEN
raw_to_FFXC(GEN x, GEN ff)
{ pari_APPLY_type(t_COL, raw_to_FFX(gel(x,i), ff)); }

static GEN
raw_to_FFX_fact(GEN F, GEN ff)
{
  GEN y, u, v;
  GEN P = gel(F,1), E = gel(F,2);
  long j, l = lg(P);
  y = cgetg(3,t_MAT);
  u = cgetg(l,t_COL); gel(y,1) = u;
  v = cgetg(l,t_COL); gel(y,2) = v;
  for (j=1; j<l; j++)
  {
    gel(u,j) = raw_to_FFX(gel(P,j), ff);
    gel(v,j) = utoi(uel(E,j));
  }
  return y;
}

static GEN
FFX_zero(GEN ff, long v)
{
  GEN r = cgetg(3,t_POL);
  r[1] = evalvarn(v);
  gel(r,2) = FF_zero(ff);
  return r;
}

static GEN
FFX_wrap2(GEN Pf, GEN Qf, GEN ff, GEN FpXQX(GEN, GEN, GEN, GEN),
          GEN F2xqX(GEN, GEN, GEN), GEN FlxqX(GEN, GEN, GEN, ulong))
{
  pari_sp av = avma;
  GEN r,T,p;
  ulong pp;
  GEN P = FFX_to_raw(Pf, ff);
  GEN Q = FFX_to_raw(Qf, ff);
  _getFF(ff,&T,&p,&pp);
  switch(ff[1])
  {
  case t_FF_FpXQ:
    r = FpXQX(P, Q, T, p);
    break;
  case t_FF_F2xq:
    r = F2xqX(P, Q, T);
    break;
  default:
    r = FlxqX(P, Q, T, pp);
  }
  if (!lgpol(r)) { avma = av; return FFX_zero(ff, varn(Pf)); }
  return gerepilecopy(av, raw_to_FFX(r, ff));
}

GEN
FFX_mul(GEN Pf, GEN Qf, GEN ff)
{ return FFX_wrap2(Pf, Qf, ff, FpXQX_mul, F2xqX_mul, FlxqX_mul); }

GEN
FFX_sqr(GEN Pf, GEN ff)
{
  pari_sp av = avma;
  GEN r,T,p;
  ulong pp;
  GEN P = FFX_to_raw(Pf, ff);
  _getFF(ff,&T,&p,&pp);
  switch(ff[1])
  {
  case t_FF_FpXQ:
    r = FpXQX_sqr(P, T, p);
    break;
  case t_FF_F2xq:
    r = F2xqX_sqr(P, T);
    break;
  default:
    r = FlxqX_sqr(P, T, pp);
  }
  if (!lgpol(r)) { avma = av; return FFX_zero(ff, varn(Pf)); }
  return gerepilecopy(av, raw_to_FFX(r, ff));
}

GEN
FFX_rem(GEN Pf, GEN Qf, GEN ff)
{ return FFX_wrap2(Pf, Qf, ff, FpXQX_rem, F2xqX_rem, FlxqX_rem); }

GEN
FFXQ_sqr(GEN Pf, GEN Qf, GEN ff)
{ return FFX_wrap2(Pf, Qf, ff, FpXQXQ_sqr, F2xqXQ_sqr, FlxqXQ_sqr); }

GEN
FFXQ_inv(GEN Pf, GEN Qf, GEN ff)
{ return FFX_wrap2(Pf, Qf, ff, FpXQXQ_inv, F2xqXQ_inv, FlxqXQ_inv); }

GEN
FFXQ_mul(GEN Pf, GEN Qf, GEN Sf, GEN ff)
{
  pari_sp av = avma;
  GEN r,T,p;
  ulong pp;
  GEN P = FFX_to_raw(Pf, ff);
  GEN Q = FFX_to_raw(Qf, ff);
  GEN S = FFX_to_raw(Sf, ff);
  _getFF(ff,&T,&p,&pp);
  switch(ff[1])
  {
  case t_FF_FpXQ:
    r = FpXQXQ_mul(P, Q, S, T, p);
    break;
  case t_FF_F2xq:
    r = F2xqXQ_mul(P, Q, S, T);
    break;
  default:
    r = FlxqXQ_mul(P, Q, S, T, pp);
  }
  if (!lgpol(r)) { avma = av; return FFX_zero(ff, varn(Pf)); }
  return gerepilecopy(av, raw_to_FFX(r, ff));
}

long
FFX_ispower(GEN Pf, long k, GEN ff, GEN *pt_r)
{
  pari_sp av = avma;
  GEN P,T,p;
  ulong pp;
  long s;
  if (degpol(Pf) % k) return 0;
  P = FFX_to_raw(Pf, ff);
  _getFF(ff,&T,&p,&pp);
  switch(ff[1])
  {
  case t_FF_FpXQ:
    s = FpXQX_ispower(P, k, T, p, pt_r);
    break;
  case t_FF_F2xq:
    s = F2xqX_ispower(P, k, T, pt_r);
    break;
  default:
    s = FlxqX_ispower(P, k, T, pp, pt_r);
  }
  if (s==0) { avma = av; return 0; }
  if (pt_r)
    *pt_r = gerepilecopy(av, raw_to_FFX(*pt_r, ff));
  else avma = av;
  return 1;
}

GEN
FFX_factor(GEN Pf, GEN ff)
{
  pari_sp av = avma;
  GEN r,T,p;
  ulong pp;
  GEN P = FFX_to_raw(Pf, ff);
  _getFF(ff,&T,&p,&pp);
  switch(ff[1])
  {
  case t_FF_FpXQ:
    r = FpXQX_factor(P, T, p);
    break;
  case t_FF_F2xq:
    r = F2xqX_factor(P, T);
    break;
  default:
    r = FlxqX_factor(P, T, pp);
  }
  return gerepilecopy(av, raw_to_FFX_fact(r, ff));
}

GEN
FFX_factor_squarefree(GEN Pf, GEN ff)
{
  pari_sp av = avma;
  GEN r,T,p;
  ulong pp;
  GEN P = FFX_to_raw(Pf, ff);
  _getFF(ff,&T,&p,&pp);
  switch(ff[1])
  {
  case t_FF_FpXQ:
    r = FpXQX_factor_squarefree(P, T, p);
    break;
  case t_FF_F2xq:
    r = F2xqX_factor_squarefree(P, T);
    break;
  default:
    r = FlxqX_factor_squarefree(P, T, pp);
  }
  return gerepilecopy(av, raw_to_FFXC(r, ff));
}

GEN
FFX_ddf(GEN Pf, GEN ff)
{
  pari_sp av = avma;
  GEN r,T,p;
  ulong pp;
  GEN P = FFX_to_raw(Pf, ff);
  _getFF(ff,&T,&p,&pp);
  switch(ff[1])
  {
  case t_FF_FpXQ:
    r = FpXQX_ddf(P, T, p);
    break;
  case t_FF_F2xq:
    r = F2xqX_ddf(P, T);
    break;
  default:
    r = FlxqX_ddf(P, T, pp);
  }
  return gerepilecopy(av, raw_to_FFX_fact(r, ff));
}

GEN
FFX_degfact(GEN Pf, GEN ff)
{
  pari_sp av = avma;
  GEN r,T,p;
  ulong pp;
  GEN P = FFX_to_raw(Pf, ff);
  _getFF(ff, &T, &p, &pp);
  switch(ff[1])
  {
  case t_FF_FpXQ:
    r = FpXQX_degfact(P, T, p);
    break;
  case t_FF_F2xq:
    r = F2xqX_degfact(P, T);
    break;
  default:
    r = FlxqX_degfact(P, T, pp);
  }
  return gerepilecopy(av, r);
}

GEN
FqX_to_FFX(GEN x, GEN ff)
{
  long i, lx;
  GEN y =  cgetg_copy(x,&lx);
  y[1] = x[1];
  for (i=2; i<lx; i++) gel(y,i) = Fq_to_FF(gel(x,i), ff);
  return y;
}

GEN
ffgen(GEN T, long v)
{
  GEN A, p = NULL, ff = cgetg(5,t_FFELT);
  long d;
  switch(typ(T))
  {
    case t_FFELT:
      p = FF_p_i(T); T = FF_mod(T); d = degpol(T);
      break;
    case t_POL:
      d = degpol(T); p = NULL;
      if (d < 1 || !RgX_is_FpX(T, &p) || !p) pari_err_TYPE("ffgen",T);
      T = RgX_to_FpX(T, p);
      /* testing for irreducibility is too costly */
      if (!FpX_is_squarefree(T,p)) pari_err_IRREDPOL("ffgen",T);
      break;
    case t_INT:
      d = ispseudoprimepower(T,&p);
      if (!d) pari_err_PRIME("ffgen",T);
      T = init_Fq(p, d, v);
      break;
    case t_VEC: case t_COL:
      if (lg(T) == 3) {
        p = gel(T,1);
        A = gel(T,2);
        if (typ(p) == t_INT && typ(A) == t_INT)
        {
          d = itos(A);
          T = init_Fq(p, d, v);
          break;
        }
      }
    default:
      pari_err_TYPE("ffgen",T);
      return NULL;
  }
  if (v < 0) v = varn(T);
  if (lgefint(p)==3)
  {
    ulong pp = p[2];
    long sv = evalvarn(v);
    if (pp==2)
    {
      ff[1] = t_FF_F2xq;
      T = ZX_to_F2x(T); T[1] = sv;
      A = polx_F2x(sv); if (d == 1) A = F2x_rem(A, T);
      p = gen_2;
    }
    else
    {
      ff[1] = t_FF_Flxq;
      T = ZX_to_Flx(T,pp); T[1] = sv;
      A = polx_Flx(sv); if (d == 1) A = Flx_rem(A, T, pp);
      p = icopy(p);
    }
  }
  else
  {
    ff[1] = t_FF_FpXQ;
    setvarn(T,v);
    A = pol_x(v); if (d == 1) A = FpX_rem(A, T, p);
    p = icopy(p);
  }
  gel(ff,2) = A;
  gel(ff,3) = T;
  gel(ff,4) = p; return ff;
}

GEN
p_to_FF(GEN p, long v)
{
  GEN A, T;
  GEN ff = cgetg(5,t_FFELT);
  if (lgefint(p)==3)
  {
    ulong pp = p[2];
    long sv = evalvarn(v);
    if (pp==2)
    {
      ff[1] = t_FF_F2xq;
      T = polx_F2x(sv);
      A = pol1_F2x(sv);
      p = gen_2;
    }
    else
    {
      ff[1] = t_FF_Flxq;
      T = polx_Flx(sv);
      A = pol1_Flx(sv);
      p = icopy(p);
    }
  }
  else
  {
    ff[1] = t_FF_FpXQ;
    T = pol_x(v);
    A = pol_1(v);
    p = icopy(p);
  }
  gel(ff,2) = A;
  gel(ff,3) = T;
  gel(ff,4) = p; return ff;
}
GEN
Tp_to_FF(GEN T, GEN p)
{
  GEN A, ff;
  long v;
  if (!T) return p_to_FF(p,0);
  ff = cgetg(5,t_FFELT);
  v = varn(T);
  if (lgefint(p)==3)
  {
    ulong pp = p[2];
    long sv = evalvarn(v);
    if (pp==2)
    {
      ff[1] = t_FF_F2xq;
      T = ZX_to_F2x(T);
      A = pol1_F2x(sv);
      p = gen_2;
    }
    else
    {
      ff[1] = t_FF_Flxq;
      T = ZX_to_Flx(T, pp);
      A = pol1_Flx(sv);
      p = icopy(p);
    }
  }
  else
  {
    ff[1] = t_FF_FpXQ;
    T = ZX_copy(T);
    A = pol_1(v);
    p = icopy(p);
  }
  gel(ff,2) = A;
  gel(ff,3) = T;
  gel(ff,4) = p; return ff;
}

GEN
fforder(GEN x, GEN o)
{
  if (typ(x)!=t_FFELT) pari_err_TYPE("fforder",x);
  return FF_order(x,o);
}

GEN
ffprimroot(GEN x, GEN *o)
{
  if (typ(x)!=t_FFELT) pari_err_TYPE("ffprimroot",x);
  return FF_primroot(x,o);
}

GEN
fflog(GEN x, GEN g, GEN o)
{
  if (typ(x)!=t_FFELT) pari_err_TYPE("fflog",x);
  if (typ(g)!=t_FFELT) pari_err_TYPE("fflog",g);
  return FF_log(x,g,o);
}

GEN
ffrandom(GEN ff)
{
  ulong pp;
  GEN r, T, p, z = _initFF(ff,&T,&p,&pp);
  switch(ff[1])
  {
  case t_FF_FpXQ:
    r = random_FpX(degpol(T), varn(T), p);
    break;
  case t_FF_F2xq:
    r = random_F2x(F2x_degree(T), T[1]);
    break;
  default:
    r = random_Flx(degpol(T), T[1], pp);
  }
  return _mkFF(ff,z,r);
}

int
Rg_is_FF(GEN c, GEN *ff)
{
  switch(typ(c))
  {
  case t_FFELT:
    if (!*ff) *ff = c;
    else if (!FF_samefield(*ff, c)) return 0;
    break;
  default:
    return 0;
  }
  return 1;
}

int
RgC_is_FFC(GEN x, GEN *ff)
{
  long i, lx = lg(x);
  for (i=lx-1; i>0; i--)
    if (!Rg_is_FF(gel(x,i), ff)) return 0;
  return (*ff != NULL);
}

int
RgM_is_FFM(GEN x, GEN *ff)
{
  long j, lx = lg(x);
  for (j=lx-1; j>0; j--)
    if (!RgC_is_FFC(gel(x,j), ff)) return 0;
  return (*ff != NULL);
}

static GEN
FqC_to_FpXQC(GEN x, GEN T, GEN p)
{
  long i, lx;
  GEN y = cgetg_copy(x,&lx);
  for(i=1; i<lx; i++)
    gel(y, i) = Fq_to_FpXQ(gel(x, i), T, p);
  return y;
}

static GEN
FqM_to_FpXQM(GEN x, GEN T, GEN p)
{
  long i, lx;
  GEN y = cgetg_copy(x,&lx);
  for(i=1; i<lx; i++)
    gel(y, i) = FqC_to_FpXQC(gel(x, i), T, p);
  return y;
}

/* for functions t_MAT -> t_MAT */
static GEN
FFM_wrap(GEN M, GEN ff, GEN (*Fq)(GEN,GEN,GEN),
                       GEN (*Flxq)(GEN,GEN,ulong),
                       GEN (*F2xq)(GEN,GEN))
{
  pari_sp av = avma;
  ulong pp;
  GEN T, p;
  _getFF(ff,&T,&p,&pp); M = FFM_to_raw(M, ff);
  switch(ff[1])
  {
  case t_FF_FpXQ: M = Fq(M,T,p); if (M) M = FqM_to_FpXQM(M,T,p);
                  break;
  case t_FF_F2xq: M = F2xq(M,T); break;
  default: M = Flxq(M,T,pp); break;
  }
  if (!M) { avma = av; return NULL; }
  return gerepilecopy(av, raw_to_FFM(M, ff));
}

/* for functions (t_MAT, t_MAT) -> t_MAT */
static GEN
FFM_FFM_wrap(GEN M, GEN N, GEN ff,
             GEN (*Fq)(GEN, GEN, GEN, GEN),
             GEN (*Flxq)(GEN, GEN, GEN, ulong),
             GEN (*F2xq)(GEN, GEN, GEN))
{
  pari_sp av = avma;
  ulong pp;
  GEN T, p;
  int is_sqr = M==N;
  _getFF(ff, &T, &p, &pp);
  M = FFM_to_raw(M, ff);
  N = is_sqr? M: FFM_to_raw(N, ff);
  switch(ff[1])
  {
  case t_FF_FpXQ: M = Fq(M, N, T, p); if (M) M = FqM_to_FpXQM(M, T, p);
                  break;
  case t_FF_F2xq: M = F2xq(M, N, T); break;
  default: M = Flxq(M, N, T, pp); break;
  }
  if (!M) { avma = av; return NULL; }
  return gerepilecopy(av, raw_to_FFM(M, ff));
}

/* for functions (t_MAT, t_COL) -> t_COL */
static GEN
FFM_FFC_wrap(GEN M, GEN C, GEN ff,
             GEN (*Fq)(GEN, GEN, GEN, GEN),
             GEN (*Flxq)(GEN, GEN, GEN, ulong),
             GEN (*F2xq)(GEN, GEN, GEN))
{
  pari_sp av = avma;
  ulong pp;
  GEN T, p;
  _getFF(ff, &T, &p, &pp);
  M = FFM_to_raw(M, ff);
  C = FFC_to_raw(C, ff);
  switch(ff[1])
  {
  case t_FF_FpXQ: C = Fq(M, C, T, p); if (C) C = FqC_to_FpXQC(C, T, p);
                  break;
  case t_FF_F2xq: C = F2xq(M, C, T); break;
  default: C = Flxq(M, C, T, pp); break;
  }
  if (!C) { avma = av; return NULL; }
  return gerepilecopy(av, raw_to_FFC(C, ff));
}

GEN
FFM_ker(GEN M, GEN ff)
{ return FFM_wrap(M,ff, &FqM_ker,&FlxqM_ker,&F2xqM_ker); }
GEN
FFM_image(GEN M, GEN ff)
{ return FFM_wrap(M,ff, &FqM_image,&FlxqM_image,&F2xqM_image); }
GEN
FFM_inv(GEN M, GEN ff)
{ return FFM_wrap(M,ff, &FqM_inv,&FlxqM_inv,&F2xqM_inv); }
GEN
FFM_suppl(GEN M, GEN ff)
{ return FFM_wrap(M,ff, &FqM_suppl,&FlxqM_suppl,&F2xqM_suppl); }

GEN
FFM_deplin(GEN M, GEN ff)
{
  pari_sp av = avma;
  ulong pp;
  GEN C, T, p;
  _getFF(ff, &T, &p, &pp); M = FFM_to_raw(M, ff);
  switch(ff[1]) {
  case t_FF_FpXQ: C = FqM_deplin(M, T, p);
    if (C) C = FqC_to_FpXQC(C, T, p); break;
  case t_FF_F2xq: C = F2xqM_deplin(M, T); break;
  default: C = FlxqM_deplin(M, T, pp); break;
  }
  if (!C) { avma = av; return NULL; }
  return gerepilecopy(av, raw_to_FFC(C, ff));
}

GEN
FFM_indexrank(GEN M, GEN ff)
{
  pari_sp av = avma;
  ulong pp;
  GEN R, T, p;
  _getFF(ff,&T,&p,&pp); M = FFM_to_raw(M, ff);
  switch(ff[1]) {
  case t_FF_FpXQ: R = FqM_indexrank(M,T,p); break;
  case t_FF_F2xq: R = F2xqM_indexrank(M,T); break;
  default: R = FlxqM_indexrank(M,T,pp); break;
  }
  return gerepileupto(av, R);
}

long
FFM_rank(GEN M, GEN ff)
{
  pari_sp av = avma;
  long r;
  ulong pp;
  GEN T, p;
  _getFF(ff,&T,&p,&pp); M = FFM_to_raw(M, ff);
  switch(ff[1])
  {
  case t_FF_FpXQ: r = FqM_rank(M,T,p); break;
  case t_FF_F2xq: r = F2xqM_rank(M,T); break;
  default: r = FlxqM_rank(M,T,pp); break;
  }
  avma = av; return r;
}
GEN
FFM_det(GEN M, GEN ff)
{
  pari_sp av = avma;
  ulong pp;
  GEN d, T, p;
  _getFF(ff,&T,&p,&pp); M = FFM_to_raw(M, ff);
  switch(ff[1])
  {
  case t_FF_FpXQ: d = FqM_det(M,T,p); break;
  case t_FF_F2xq: d = F2xqM_det(M,T); break;
  default: d = FlxqM_det(M,T,pp); break;
  }
  return gerepilecopy(av, mkFF_i(ff, d));
}

GEN
FFM_FFC_gauss(GEN M, GEN C, GEN ff)
{
  return FFM_FFC_wrap(M, C, ff, FqM_FqC_gauss,
                      FlxqM_FlxqC_gauss, F2xqM_F2xqC_gauss);
}

GEN
FFM_gauss(GEN M, GEN N, GEN ff)
{
  return FFM_FFM_wrap(M, N, ff, FqM_gauss,
                      FlxqM_gauss, F2xqM_gauss);
}

GEN
FFM_FFC_invimage(GEN M, GEN C, GEN ff)
{
  return FFM_FFC_wrap(M, C, ff, FqM_FqC_invimage,
                      FlxqM_FlxqC_invimage, F2xqM_F2xqC_invimage);
}

GEN
FFM_invimage(GEN M, GEN N, GEN ff)
{
  return FFM_FFM_wrap(M, N, ff, FqM_invimage,
                      FlxqM_invimage, F2xqM_invimage);
}

GEN
FFM_FFC_mul(GEN M, GEN C, GEN ff)
{
  return FFM_FFC_wrap(M, C, ff, FqM_FqC_mul,
                      FlxqM_FlxqC_mul, F2xqM_F2xqC_mul);
}

GEN
FFM_mul(GEN M, GEN N, GEN ff)
{
  return FFM_FFM_wrap(M, N, ff, FqM_mul, FlxqM_mul, F2xqM_mul);
}
