/* Copyright (C) 2001  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/* This file is a quick hack adapted from gmp-4.0 tuning utilities
 * (T. Granlund et al.)
 *
 * (GMU MP Library is Copyright Free Software Foundation, Inc.) */
#define PARI_TUNE
#include <pari.h>
#include <paripriv.h>

int option_trace = 0;
double Step_Factor = .01; /* small steps by default */
ulong DFLT_mod1, DFLT_hmod, DFLT_qmod, DFLT_mod2;
GEN LARGE_mod;

#ifdef LONG_IS_64BIT
#  define DFLT_mod DFLT_mod1
#  define Fmod_MUL_MULII_LIMIT Flx_MUL_MULII_LIMIT
#  define Fmod_SQR_SQRI_LIMIT  Flx_SQR_SQRI_LIMIT
#  else
#  define DFLT_mod DFLT_mod2
#  define Fmod_MUL_MULII_LIMIT Flx_MUL_MULII2_LIMIT
#  define Fmod_SQR_SQRI_LIMIT  Flx_SQR_SQRI2_LIMIT
#endif

typedef struct {
  ulong reps, type;
  long *var, *var_disable, *var_enable, var_enable_min,  size, enabled;
  GEN x, y;
  ulong l;
  GEN T, p;
} speed_param;

typedef double (*speed_function_t)(speed_param *s);

typedef struct {
  int               kernel;
  const char        *name;
  long              *var;
  int               type; /* t_INT or t_REAL */
  long              min_size;
  long              max_size;
  speed_function_t  fun;
  double            step_factor; /* how much to step sizes (rounded down) */
  double            stop_factor;
  long              *var_disable;
  long              *var_enable;
} tune_param;

/* ========================================================== */
/* To use GMP cycle counting functions, look for GMP in Oxxx/Makefile */
#ifdef GMP_TIMER
/* needed to link with gmp-4.0/tune/{time,freq}.o */
int speed_option_verbose = 0;
extern double speed_unittime;
extern int    speed_precision;
void speed_starttime(void);
double speed_endtime(void);
#else
static pari_timer __T;
static double speed_unittime = 1e-4;
static int    speed_precision= 1000;
static void speed_starttime() { timer_start(&__T); }
static double speed_endtime() { return (double)timer_delay(&__T)/1000.; }
#endif

/* ========================================================== */
/* int, n words, odd */
static GEN
rand_INT(long n)
{
  pari_sp av = avma;
  GEN x, N = int2n(n*BITS_IN_LONG);
  do x = randomi(N); while (lgefint(x) != n+2);
  if (!mpodd(x)) x = addis(x,1); /*For Barrett REDC */
  return gerepileuptoint(av, x);
}
/* real, n words */
static GEN
rand_REAL(long n) { return gmul2n(itor(rand_INT(n), n+2),-BITS_IN_LONG*n); }

static GEN
rand_FpX(long n)
{
  GEN x;
  do x = random_FpX(n+1, 0, LARGE_mod); while (degpol(x) < n);
  return x;
}
/* Flx, degree n */
static GEN
rand_F2x(long n)
{
  GEN x;
  do x = random_F2x(BITS_IN_LONG*n, 0); while (lgpol(x) < n);
  return x;
}
/* Flx, degree n */
static GEN
rand_Flx(long n, ulong l)
{
  GEN x;
  do x = random_Flx(n+1, 0, l); while (degpol(x) < n);
  return x;
}

static GEN
rand_F2xqX(long n, GEN T)
{
  GEN x;
  do x = random_F2xqX(n+1, 0, T); while (degpol(x) < n);
  return x;
}

static GEN
rand_FlxqX(long n, GEN T, ulong l)
{
  GEN x;
  do x = random_FlxqX(n+1, 0, T, l); while (degpol(x) < n);
  return x;
}

static GEN
rand_FpXQX(long n, GEN T)
{
  GEN x;
  do x = random_FpXQX(n+1, 0, T, LARGE_mod); while (degpol(x) < n);
  return x;
}
/* normalized Fpx, degree n */
static GEN
rand_NFpX(long n)
{
  pari_sp av = avma;
  GEN x = gadd(pol_xn(n,0), random_FpX(n, 0, LARGE_mod));
  return gerepileupto(av, x);
}

/* normalized Flx, degree n */
static GEN
rand_NFlx(long n, ulong l)
{
  pari_sp av = avma;
  GEN x = Flx_add(Flx_shift(pol1_Flx(0),n), random_Flx(n, 0, l), l);
  return gerepileuptoleaf(av, x);
}

static GEN
rand_NF2xqX(long n, GEN T)
{
  pari_sp av = avma;
  GEN x = F2xX_add(monomial(pol1_F2x(0),n,0), random_F2xqX(n, 0, T));
  return gerepileupto(av, x);
}

static GEN
rand_NFlxqX(long n, GEN T, long l)
{
  pari_sp av = avma;
  GEN x = FlxX_add(monomial(pol1_Flx(0),n,0), random_FlxqX(n, 0, T, l), l);
  return gerepileupto(av, x);
}

static GEN
rand_NFpXQX(long n, GEN T)
{
  pari_sp av = avma;
  GEN x = gadd(pol_xn(n,0), random_FpXQX(n, 0, T, LARGE_mod));
  return gerepileupto(av, x);
}

#define t_F2x     100
#define t_Fqx     200
#define t_Fhx     201
#define t_Flx     202
#define t_Fl1x    203
#define t_Fl2x    204
#define t_NFqx    210
#define t_NFhx    211
#define t_NFlx    212
#define t_NFl1x   213
#define t_NFl2x   214
#define t_FpX     300
#define t_NFpX    310
#define t_F2xqX   400
#define t_NF2xqX  410
#define t_FlxqX   500
#define t_NFlxqX  510
#define t_FpXQX   600
#define t_NFpXQX  610

static GEN
rand_g(speed_param *s)
{
  long n = s->size;
  switch (s->type) {
    case t_INT:  return rand_INT(n);
    case t_REAL: return rand_REAL(n);
    case t_F2x:  return rand_F2x(n);
    case t_Fqx:  return rand_Flx(n,DFLT_qmod);
    case t_Fhx:  return rand_Flx(n,DFLT_hmod);
    case t_Flx:  return rand_Flx(n,DFLT_mod);
    case t_Fl1x: return rand_Flx(n,DFLT_mod1);
    case t_Fl2x: return rand_Flx(n,DFLT_mod2);
    case t_NFqx: return rand_NFlx(n,DFLT_qmod);
    case t_NFhx: return rand_NFlx(n,DFLT_hmod);
    case t_NFlx: return rand_NFlx(n,DFLT_mod);
    case t_NFl1x: return rand_NFlx(n,DFLT_mod1);
    case t_NFl2x: return rand_NFlx(n,DFLT_mod2);
    case t_FpX:    return rand_FpX(n);
    case t_NFpX:   return rand_NFpX(n);
    case t_F2xqX:  return rand_F2xqX(n, s->T);
    case t_NF2xqX: return rand_NF2xqX(n, s->T);
    case t_FlxqX:  return rand_FlxqX(n, s->T, s->l);
    case t_NFlxqX: return rand_NFlxqX(n, s->T, s->l);
    case t_FpXQX:  return rand_FpXQX(n, s->T);
    case t_NFpXQX: return rand_NFpXQX(n, s->T);
  }
  return NULL;
}

static void
dft_Flxq(speed_param *s)
{
  do
  {
    s->T = rand_NFlx(10, s->l);
  } while (!Flx_is_irred(s->T, s->l));
  s->T[1] = evalvarn(1);
  s->T = Flx_get_red(s->T, s->l);
}

static void
dft_FpXQ(speed_param *s)
{
  s->T = rand_NFpX(10);
  setvarn(s->T, 1);
  s->T = FpX_get_red(s->T, s->p);
}

static void
dftmod(speed_param *s)
{
  switch (s->type) {
    case t_Fqx:  s->l=DFLT_qmod; return;
    case t_Fhx:  s->l=DFLT_hmod; return;
    case t_Flx:  s->l=DFLT_mod;  return;
    case t_Fl1x: s->l=DFLT_mod1; return;
    case t_Fl2x: s->l=DFLT_mod2; return;
    case t_NFqx: s->l=DFLT_qmod;  return;
    case t_NFhx: s->l=DFLT_hmod;  return;
    case t_NFlx: s->l=DFLT_mod;  return;
    case t_NFl1x: s->l=DFLT_mod1;  return;
    case t_NFl2x: s->l=DFLT_mod2;  return;
    case t_FpX:  s->p=LARGE_mod; return;
    case t_NFpX: s->p=LARGE_mod; return;
    case t_F2xqX:  s->l=2;  dft_Flxq(s); return;
    case t_NF2xqX: s->l=2;  dft_Flxq(s); return;
    case t_FlxqX:  s->l=DFLT_mod;  dft_Flxq(s); return;
    case t_NFlxqX: s->l=DFLT_mod;  dft_Flxq(s); return;
    case t_FpXQX:  s->p=LARGE_mod; dft_FpXQ(s); return;
    case t_NFpXQX: s->p=LARGE_mod; dft_FpXQ(s); return;
  }
}

/* ========================================================== */
#define TIME_FUN(call) {\
  {                                      \
    pari_sp av = avma;                   \
    int i;                               \
    speed_starttime();                   \
    i = (s)->reps;                       \
    do { call; avma = av; } while (--i); \
  }                                      \
  return speed_endtime();                \
}

#define m_menable(s,var,min) (*(s->var)=minss(lg(s->x)-2,s->min))
#define  m_enable(s,var) (*(s->var)=lg(s->x)-2)/* enable  asymptotically fastest */
#define m_disable(s,var) (*(s->var)=lg(s->x)+1)/* disable asymptotically fastest */

static void enable(speed_param *s)
{
  m_enable(s,var); s->enabled = 1;
  if (s->var_disable) m_disable(s,var_disable);
  if (s->var_enable) m_menable(s,var_enable,var_enable_min);
}

static void disable(speed_param *s)
{
  m_disable(s,var); s->enabled = 0;
  if (s->var_disable) m_disable(s,var_disable);
  if (s->var_enable) m_menable(s,var_enable,var_enable_min);
}

static double speed_mulrr(speed_param *s)
{ TIME_FUN(mulrr(s->x, s->y)); }

static double speed_sqrr(speed_param *s)
{ TIME_FUN(sqrr(s->x)); }

static double speed_mulii(speed_param *s)
{ TIME_FUN(mulii(s->x, s->y)); }

static double speed_sqri (speed_param *s)
{ TIME_FUN(sqri(s->x)); }

static double speed_exp(speed_param *s)
{ TIME_FUN(mpexp(s->x)); }

static double speed_inv(speed_param *s)
{ TIME_FUN(invr(s->x)); }

static double speed_log(speed_param *s)
{ TIME_FUN(mplog(s->x)); }

static double speed_logcx(speed_param *s)
{ GEN z; setexpo(s->x,0); z = mkcomplex(gen_1, s->x);
  glog(z,s->size);
  TIME_FUN(glog(z,s->size)); }

static double speed_atan(speed_param *s)
{ setexpo(s->x, 0);
  gatan(s->x, 0);
  TIME_FUN(gatan(s->x, 0)); }

static double speed_Fp_pow(speed_param *s)
{ TIME_FUN( Fp_pow(s->x, subis(s->y,1), s->y)); }

static double speed_divrr(speed_param *s)
{ TIME_FUN(divrr(s->x, s->y)); }

static double speed_invmod(speed_param *s)
{ GEN T; TIME_FUN(invmod(s->x, s->y, &T)); }

static double speed_F2x_mul(speed_param *s)
{ TIME_FUN(F2x_mul(s->x, s->y)); }

static double speed_Flx_sqr(speed_param *s)
{ TIME_FUN(Flx_sqr(s->x, s->l)); }

static double speed_Flx_inv(speed_param *s)
{ TIME_FUN(Flx_invBarrett(s->x, s->l)); }

static double speed_Flx_mul(speed_param *s)
{ TIME_FUN(Flx_mul(s->x, s->y, s->l)); }

static double speed_Flx_divrem(speed_param *s)
{
  GEN r, x = rand_NFlx((degpol(s->x)-1)*2, s->l);
  TIME_FUN(Flx_divrem(x, s->x, s->l, &r));
}

static double speed_Flx_rem(speed_param *s) {
  GEN x = rand_NFlx((degpol(s->x)-1)*2, s->l);
  TIME_FUN(Flx_rem(x, s->x, s->l));
}

static double speed_Flxq_red(speed_param *s) {
  GEN x = rand_NFlx((degpol(s->x)-1)*2, s->l);
  GEN q = Flx_get_red(s->x, s->l);
  TIME_FUN(Flx_rem(x, q, s->l));
}

static double speed_Flx_halfgcd(speed_param *s)
{ TIME_FUN(Flx_halfgcd(s->x, s->y, s->l)); }

static double speed_Flx_gcd(speed_param *s)
{ TIME_FUN(Flx_gcd(s->x, s->y, s->l)); }

static double speed_Flx_extgcd(speed_param *s)
{ GEN u,v; TIME_FUN(Flx_extgcd(s->x, s->y, s->l, &u, &v)); }

static double speed_FpX_inv(speed_param *s)
{ TIME_FUN(FpX_invBarrett(s->x, s->p)); }

static double speed_FpX_divrem(speed_param *s)
{
  GEN r, x = rand_NFpX((degpol(s->x)-1)*2);
  TIME_FUN(FpX_divrem(x, s->x, s->p, &r));
}

static double speed_FpX_rem(speed_param *s)
{
  GEN x = rand_NFpX((degpol(s->x)-1)*2);
  TIME_FUN(FpX_rem(x, s->x, s->p));
}

static double speed_FpXQ_red(speed_param *s) {
  GEN x = rand_NFpX((degpol(s->x)-1)*2);
  GEN q = FpX_get_red(s->x, s->p);
  TIME_FUN(FpX_rem(x, q, s->p));
}

static double speed_FpX_halfgcd(speed_param *s)
{ TIME_FUN(FpX_halfgcd(s->x, s->y, s->p)); }
static double speed_FpX_gcd(speed_param *s)
{ TIME_FUN(FpX_gcd(s->x, s->y, s->p)); }
static double speed_FpX_extgcd(speed_param *s)
{ GEN u,v; TIME_FUN(FpX_extgcd(s->x, s->y, s->p, &u, &v)); }

static double speed_F2xqX_inv(speed_param *s)
{ TIME_FUN(F2xqX_invBarrett(s->x, s->T)); }

static double speed_F2xqX_divrem(speed_param *s)
{
  GEN r, x = rand_NF2xqX((degpol(s->x)-1)*2, s->T);
  TIME_FUN(F2xqX_divrem(x, s->x, s->T, &r));
}

static double speed_F2xqX_rem(speed_param *s)
{
  GEN x = rand_NF2xqX((degpol(s->x)-1)*2, s->T);
  TIME_FUN(F2xqX_rem(x, s->x, s->T));
}

static double speed_F2xqXQ_red(speed_param *s) {
  GEN x = rand_NF2xqX((degpol(s->x)-1)*2, s->T);
  GEN q = F2xqX_get_red(s->x, s->T);
  TIME_FUN(F2xqX_rem(x, q, s->T));
}

static double speed_FlxqX_inv(speed_param *s)
{ TIME_FUN(FlxqX_invBarrett(s->x, s->T, s->l)); }


static double speed_FlxqX_divrem(speed_param *s)
{
  GEN r, x = rand_NFlxqX((degpol(s->x)-1)*2, s->T, s->l);
  TIME_FUN(FlxqX_divrem(x, s->x, s->T, s->l, &r));
}

static double speed_FlxqX_rem(speed_param *s)
{
  GEN x = rand_NFlxqX((degpol(s->x)-1)*2, s->T, s->l);
  TIME_FUN(FlxqX_rem(x, s->x, s->T, s->l));
}

static double speed_FlxqXQ_red(speed_param *s) {
  GEN x = rand_NFlxqX((degpol(s->x)-1)*2, s->T, s->l);
  GEN q = FlxqX_get_red(s->x, s->T, s->l);
  TIME_FUN(FlxqX_rem(x, q, s->T, s->l));
}

static double speed_FlxqX_halfgcd(speed_param *s)
{ TIME_FUN(FlxqX_halfgcd(s->x, s->y, s->T, s->l)); }

static double speed_FlxqX_extgcd(speed_param *s)
{ GEN u,v; TIME_FUN(FlxqX_extgcd(s->x, s->y, s->T, s->l, &u, &v)); }

static double speed_FlxqX_gcd(speed_param *s)
{ TIME_FUN(FlxqX_gcd(s->x, s->y, s->T, s->l)); }

static double speed_FpXQX_inv(speed_param *s)
{ TIME_FUN(FpXQX_invBarrett(s->x, s->T, s->p)); }

static double speed_FpXQX_divrem(speed_param *s)
{
  GEN r, x = rand_NFpXQX((degpol(s->x)-1)*2, s->T);
  TIME_FUN(FpXQX_divrem(x, s->x, s->T, s->p, &r));
}

static double speed_FpXQX_rem(speed_param *s)
{
  GEN x = rand_NFpXQX((degpol(s->x)-1)*2, s->T);
  TIME_FUN(FpXQX_rem(x, s->x, s->T, s->p));
}

static double speed_FpXQXQ_red(speed_param *s) {
  GEN x = rand_NFpXQX((degpol(s->x)-1)*2, s->T);
  GEN q = FpXQX_get_red(s->x, s->T, s->p);
  TIME_FUN(FpXQX_rem(x, q, s->T, s->p));
}

static double speed_FpXQX_halfgcd(speed_param *s)
{ TIME_FUN(FpXQX_halfgcd(s->x, s->y, s->T, s->p)); }

static double speed_FpXQX_extgcd(speed_param *s)
{ GEN u,v; TIME_FUN(FpXQX_extgcd(s->x, s->y, s->T, s->p, &u, &v)); }

static double speed_FpXQX_gcd(speed_param *s)
{ TIME_FUN(FpXQX_gcd(s->x, s->y, s->T, s->p)); }

/* small coeffs: earlier thresholds for more complicated rings */
static double speed_RgX_sqr(speed_param *s)
{ TIME_FUN(RgX_sqr_i(s->x)); }
static double speed_RgX_mul(speed_param *s)
{ TIME_FUN(RgX_mul_i(s->x, s->y)); }

enum { PARI = 1, GMP = 2 };
#ifdef PARI_KERNEL_GMP
#  define AVOID PARI
#else
#  define AVOID GMP
#endif

/* Thresholds are set in this order. If f() depends on g(), g() should
 * occur first */
#define var(a) # a, &a
static tune_param param[] = {
{PARI,var(MULII_KARATSUBA_LIMIT),  t_INT, 4,0, speed_mulii,0,0,&MULII_FFT_LIMIT},
{PARI,var(SQRI_KARATSUBA_LIMIT),   t_INT, 4,0, speed_sqri,0,0,&SQRI_FFT_LIMIT},
{PARI,var(MULII_FFT_LIMIT),        t_INT, 500,0, speed_mulii,0.02},
{PARI,var(SQRI_FFT_LIMIT),         t_INT, 500,0, speed_sqri,0.02},
{0,   var(MULRR_MULII_LIMIT),      t_REAL,4,0, speed_mulrr},
{0,   var(SQRR_SQRI_LIMIT),        t_REAL,4,0, speed_sqrr},
{0,   var(Fp_POW_REDC_LIMIT),      t_INT, 3,100, speed_Fp_pow,0,0,&Fp_POW_BARRETT_LIMIT},
{0,   var(Fp_POW_BARRETT_LIMIT),   t_INT, 3,0, speed_Fp_pow},
{0,   var(INVNEWTON_LIMIT),        t_REAL,66,0, speed_inv,0.03},
{GMP, var(DIVRR_GMP_LIMIT),        t_REAL,4,0, speed_divrr},
{0,   var(EXPNEWTON_LIMIT),        t_REAL,66,0, speed_exp},
{0,   var(LOGAGM_LIMIT),           t_REAL,4,0, speed_log},
{0,   var(LOGAGMCX_LIMIT),         t_REAL,3,0, speed_logcx,0.05},
{0,   var(AGM_ATAN_LIMIT),         t_REAL,20,0, speed_atan,0.05},
{GMP, var(INVMOD_GMP_LIMIT),       t_INT, 3,0, speed_invmod},
{0,   var(F2x_MUL_KARATSUBA_LIMIT),t_F2x,3,0, speed_F2x_mul},
{0,   var(Flx_MUL_KARATSUBA_LIMIT),t_Flx,5,0, speed_Flx_mul,0,0,&Fmod_MUL_MULII_LIMIT},
{0,   var(Flx_SQR_KARATSUBA_LIMIT),t_Flx,5,0, speed_Flx_sqr,0,0,&Fmod_SQR_SQRI_LIMIT},
{0,   var(Flx_MUL_QUARTMULII_LIMIT),t_Fqx,3,0, speed_Flx_mul},
{0,   var(Flx_SQR_QUARTSQRI_LIMIT), t_Fqx,3,0, speed_Flx_sqr},
{0,   var(Flx_MUL_HALFMULII_LIMIT),t_Fhx,3,0, speed_Flx_mul},
{0,   var(Flx_SQR_HALFSQRI_LIMIT), t_Fhx,3,0, speed_Flx_sqr},
{0,   var(Flx_MUL_MULII_LIMIT),    t_Fl1x,5,0, speed_Flx_mul},
{0,   var(Flx_SQR_SQRI_LIMIT),     t_Fl1x,5,0, speed_Flx_sqr},
{0,   var(Flx_MUL_MULII2_LIMIT),   t_Fl2x,5,20000, speed_Flx_mul,0.05},
{0,   var(Flx_SQR_SQRI2_LIMIT),    t_Fl2x,5,20000, speed_Flx_sqr,0.05},
{0,  var(Flx_INVBARRETT_KARATSUBA_LIMIT), t_NFlx,5,20000,
            speed_Flx_inv,0,0,&Fmod_MUL_MULII_LIMIT,&Flx_MUL_KARATSUBA_LIMIT},
{0,  var(Flx_INVBARRETT_QUARTMULII_LIMIT), t_NFqx,5,0,
            speed_Flx_inv,0,0,NULL,&Flx_MUL_QUARTMULII_LIMIT},
{0,  var(Flx_INVBARRETT_HALFMULII_LIMIT), t_NFhx,5,0,
            speed_Flx_inv,0,0,NULL,&Flx_MUL_HALFMULII_LIMIT},
{0,  var(Flx_INVBARRETT_MULII_LIMIT), t_NFl1x,5,0,
            speed_Flx_inv,0,0,NULL,&Flx_MUL_MULII_LIMIT},
{0,  var(Flx_INVBARRETT_MULII2_LIMIT),t_NFl2x,5,0,
            speed_Flx_inv,0,0,NULL,&Flx_MUL_MULII2_LIMIT},
{0,  var(Flx_DIVREM_BARRETT_LIMIT),t_NFlx,10,0, speed_Flx_divrem,0.05},
{0,  var(Flx_REM_BARRETT_LIMIT),  t_NFlx,10,0, speed_Flx_rem,0.05},
{0,  var(Flx_BARRETT_KARATSUBA_LIMIT), t_NFlx,5,0,
            speed_Flxq_red,0,0,&Fmod_MUL_MULII_LIMIT,&Flx_MUL_KARATSUBA_LIMIT},
{0,  var(Flx_BARRETT_QUARTMULII_LIMIT), t_NFqx,5,0,
            speed_Flxq_red,0,0,NULL,&Flx_MUL_QUARTMULII_LIMIT},
{0,  var(Flx_BARRETT_HALFMULII_LIMIT), t_NFhx,5,0,
            speed_Flxq_red,0,0,NULL,&Flx_MUL_HALFMULII_LIMIT},
{0,  var(Flx_BARRETT_MULII_LIMIT), t_NFl1x,5,0,
            speed_Flxq_red,0,0,NULL,&Flx_MUL_MULII_LIMIT},
{0,  var(Flx_BARRETT_MULII2_LIMIT),t_NFl2x,5,0,
            speed_Flxq_red,0,0,NULL,&Flx_MUL_MULII2_LIMIT},
{0,  var(Flx_HALFGCD_KARATSUBA_LIMIT), t_Flx,10,0,
            speed_Flx_halfgcd,0,0,&Fmod_MUL_MULII_LIMIT,&Flx_MUL_KARATSUBA_LIMIT},
{0,  var(Flx_HALFGCD_QUARTMULII_LIMIT), t_Fqx,10,0,
            speed_Flx_halfgcd,0,0,NULL,&Flx_MUL_QUARTMULII_LIMIT},
{0,  var(Flx_HALFGCD_HALFMULII_LIMIT), t_Fhx,10,0,
            speed_Flx_halfgcd,0,0,NULL,&Flx_MUL_HALFMULII_LIMIT},
{0,  var(Flx_HALFGCD_MULII_LIMIT), t_Fl1x,10,0,
            speed_Flx_halfgcd,0,0,NULL,&Flx_MUL_MULII_LIMIT},
{0,  var(Flx_HALFGCD_MULII2_LIMIT),t_Fl2x,10,0,
            speed_Flx_halfgcd,0,0,NULL,&Flx_MUL_MULII2_LIMIT},
{0,  var(Flx_GCD_LIMIT),           t_Flx,10,0, speed_Flx_gcd,0.1},
{0,  var(Flx_EXTGCD_LIMIT),        t_Flx,10,0, speed_Flx_extgcd},
{0,  var(F2xqX_INVBARRETT_LIMIT),t_NF2xqX,10,0, speed_F2xqX_inv,0.05},
{0,  var(F2xqX_BARRETT_LIMIT),   t_NF2xqX,10,0, speed_F2xqXQ_red,0.05},
{0,  var(F2xqX_DIVREM_BARRETT_LIMIT), t_NF2xqX,10,0, speed_F2xqX_divrem,0.05},
{0,  var(F2xqX_REM_BARRETT_LIMIT), t_NF2xqX,10,0, speed_F2xqX_rem,0.05},
{0,  var(FlxqX_INVBARRETT_LIMIT),t_NFlxqX,10,0, speed_FlxqX_inv,0.05},
{0,  var(FlxqX_BARRETT_LIMIT),   t_NFlxqX,10,0, speed_FlxqXQ_red,0.05},
{0,  var(FlxqX_DIVREM_BARRETT_LIMIT), t_NFlxqX,10,0, speed_FlxqX_divrem,0.05},
{0,  var(FlxqX_REM_BARRETT_LIMIT), t_NFlxqX,10,0, speed_FlxqX_rem,0.05},
{0,  var(FlxqX_HALFGCD_LIMIT),    t_FlxqX,10,0, speed_FlxqX_halfgcd,0.05},
{0,  var(FlxqX_GCD_LIMIT),        t_FlxqX,10,0, speed_FlxqX_gcd,0.05},
{0,  var(FlxqX_EXTGCD_LIMIT),     t_FlxqX,10,0, speed_FlxqX_extgcd,0.05},
{0,  var(FpX_INVBARRETT_LIMIT),   t_NFpX,10,0, speed_FpX_inv,0.05},
{0,  var(FpX_DIVREM_BARRETT_LIMIT),t_NFpX,10,0, speed_FpX_divrem,0.05},
{0,  var(FpX_REM_BARRETT_LIMIT),  t_NFpX,10,0, speed_FpX_rem,0.05},
{0,  var(FpX_BARRETT_LIMIT),      t_NFpX,10,0, speed_FpXQ_red},
{0,  var(FpX_HALFGCD_LIMIT),       t_FpX,10,0, speed_FpX_halfgcd},
{0,  var(FpX_GCD_LIMIT),           t_FpX,10,0, speed_FpX_gcd,0.1},
{0,  var(FpX_EXTGCD_LIMIT),        t_FpX,10,0, speed_FpX_extgcd},
{0,  var(FpXQX_INVBARRETT_LIMIT),t_NFpXQX,10,0, speed_FpXQX_inv,0.05},
{0,  var(FpXQX_BARRETT_LIMIT),   t_NFpXQX,10,0, speed_FpXQXQ_red,0.05},
{0,  var(FpXQX_DIVREM_BARRETT_LIMIT), t_NFpXQX,10,0, speed_FpXQX_divrem,0.05},
{0,  var(FpXQX_REM_BARRETT_LIMIT), t_NFpXQX,10,0, speed_FpXQX_rem,0.05},
{0,  var(FpXQX_HALFGCD_LIMIT),    t_FpXQX,10,0, speed_FpXQX_halfgcd,0.05},
{0,  var(FpXQX_GCD_LIMIT),        t_FpXQX,10,0, speed_FpXQX_gcd,0.05},
{0,  var(FpXQX_EXTGCD_LIMIT),     t_FpXQX,10,0, speed_FpXQX_extgcd,0.05},
{0,  var(RgX_MUL_LIMIT),           t_FpX, 4,0, speed_RgX_mul},
{0,  var(RgX_SQR_LIMIT),           t_FpX, 4,0, speed_RgX_sqr},
};

/* ========================================================== */
int ndat = 0, allocdat = 0;
struct dat_t {
  long size;
  double d;
} *dat = NULL;

int
double_cmp_ptr(double *x, double *y) { return (int)(*x - *y); }

double
time_fun(speed_function_t fun, speed_param *s, long enabled)
{
  const double TOLERANCE = 1.005; /* 0.5% */
  pari_sp av = avma;
  double t[30];
  ulong i, j, e;

  s->reps = 1;
  if (enabled) enable(s); else disable(s);
  for (i = 0; i < numberof(t); i++)
  {
    for (;;)
    {
      double reps_d;
      t[i] = fun(s);
      if (!t[i]) { s->reps *= 10; continue; }
      if (t[i] >= speed_unittime * speed_precision) break;

      /* go to a value of reps to make t[i] >= precision */
      reps_d = ceil (1.1 * s->reps
                     * speed_unittime * speed_precision
                     / maxdd(t[i], speed_unittime));
      if (reps_d > 2e9 || reps_d < 1.0)
        pari_err(e_MISC, "Fatal error: new reps bad: %.2f", reps_d);

      s->reps = (ulong)reps_d;
    }
    t[i] /= s->reps;

    /* require 3 values within TOLERANCE when >= 2 secs, 4 when below */
    e = (t[0] >= 2.0)? 3: 4;

   /* Look for e many t[]'s within TOLERANCE of each other to consider a
      valid measurement.  Return smallest among them.  */
    if (i >= e)
    {
      qsort (t, i+1, sizeof(t[0]), (QSCOMP)double_cmp_ptr);
      for (j = e-1; j < i; j++)
        if (t[j] <= t[j-e+1] * TOLERANCE) { avma = av; return t[j-e+1]; }
    }
  }
  pari_err(e_MISC,"couldn't measure time");
  return -1.0; /* LCOV_EXCL_LINE */
}

int
cmpdat(const void *a, const void *b)
{
  struct dat_t *da =(struct dat_t *)a;
  struct dat_t *db =(struct dat_t *)b;
  return da->size-db->size;
}

void
add_dat(long size, double d)
{
  if (ndat == allocdat)
  {
    allocdat += maxss(allocdat, 100);
    dat = (struct dat_t*) pari_realloc((void*)dat, allocdat * sizeof(dat[0]));
  }
  dat[ndat].size = size;
  dat[ndat].d    = d; ndat++;
  qsort(dat, ndat, sizeof(*dat), cmpdat);
}

void
diag(const char *format, ...)
{
  va_list ap;
  va_start(ap, format);
  vfprintf(stderr, format, ap);
  va_end(ap);
}
void
print_define(const char *name, long value)
{ printf("#define __%-30s %ld\n", name, value); }

long
analyze_dat(int final)
{
  double  x, min_x;
  int     j, min_j;

  /* If the threshold is set at dat[0].size, any positive values are bad. */
  x = 0.0;
  for (j = 0; j < ndat; j++)
    if (dat[j].d > 0.0) x += dat[j].d;

  if (final && option_trace >= 3)
  {
    diag("\n");
    diag("x is the sum of the badness from setting thresh at given size\n");
    diag("  (minimum x is sought)\n");
    diag("size=%ld  first x=%.4f\n", dat[j].size, x);
  }

  min_x = x;
  min_j = 0;

  /* When stepping to the next dat[j].size, positive values are no longer
     bad (so subtracted), negative values become bad (so add the absolute
     value, meaning subtract). */
  for (j = 0; j < ndat; j++)
  {
    if (final && option_trace >= 3)
      diag ("size=%ld  x=%.4f\n", dat[j].size, x);

    if (x < min_x) { min_x = x; min_j = j; }
    x -= dat[j].d;
  }
  return min_j;
}

void
Test(tune_param *param, long linear)
{
  int since_positive, since_change, thresh, new_thresh;
  speed_param s;
  long save_var_disable = -1;
  pari_timer T;
  pari_sp av=avma;
  long good = -1, bad = param->min_size;

  if (param->kernel == AVOID) { print_define(param->name, -1); return; }

#define DEFAULT(x,n)  if (! (param->x))  param->x = (n);
  DEFAULT(step_factor, Step_Factor);
  DEFAULT(stop_factor, 1.2);
  DEFAULT(max_size, 10000);
  if (param->var_disable) save_var_disable = *(param->var_disable);
  if (param->var_enable)  s.var_enable_min = *(param->var_enable);

  s.type = param->type;
  s.size = param->min_size;
  s.var  = param->var;
  s.var_disable  = param->var_disable;
  s.var_enable  = param->var_enable;
  dftmod(&s);
  ndat = since_positive = since_change = thresh = 0;
  if (option_trace >= 1)
  {
    timer_start(&T);
    diag("\nSetting %s... (default %ld)\n", param->name, *(param->var));
  }
  if (option_trace >= 2)
  {
    diag("              algorithm-A  algorithm-B   ratio  possible\n");
    diag("               (seconds)    (seconds)    diff    thresh\n");
  }

  for(;;)
  {
    pari_sp av=avma;
    double t1, t2, d;
    s.x = rand_g(&s);
    s.y = rand_g(&s);
    t1 = time_fun(param->fun, &s, 0);
    t2 = time_fun(param->fun, &s, 1);
    avma = av;
    if (t2 >= t1) d = (t2 - t1) / t2;
    else          d = (t2 - t1) / t1;

    add_dat(s.size, d);
    new_thresh = analyze_dat(0);

    if (option_trace >= 2)
      diag ("size =%4ld     %.8f   %.8f  % .4f %c  %ld\n",
            s.size, t1,t2, d, d < 0? '#': ' ', dat[new_thresh].size);

#define SINCE_POSITIVE 20
#define SINCE_CHANGE 50
    if (linear)
    {
      /* Stop if method B has been consistently faster for a while */
      if (d >= 0)
        since_positive = 0;
      else
        if (++since_positive > SINCE_POSITIVE)
        {
          if (option_trace >= 1)
            diag("Stop: since_positive (%d)\n", SINCE_POSITIVE);
          break;
        }
      /* Stop if method A has become slower by a certain factor */
      if (t1 >= t2 * param->stop_factor)
      {
        if (option_trace >= 1)
          diag("Stop: t1 >= t2 * factor (%.1f)\n", param->stop_factor);
        break;
      }
      /* Stop if threshold implied hasn't changed for a while */
      if (thresh != new_thresh)
        since_change = 0, thresh = new_thresh;
      else
        if (++since_change > SINCE_CHANGE)
        {
          if (option_trace >= 1)
            diag("Stop: since_change (%d)\n", SINCE_CHANGE);
          break;
        }
      s.size += maxss((long)floor(s.size * param->step_factor), 1);
    }
    else
    {
      if (t2 <= t1)
        new_thresh = good = s.size;
       else
        bad = s.size;
      if (bad == -1)
        linear = 1;
      else if (good == -1)
      {
        long new_size = minss(2*s.size,param->max_size-1);
        if (new_size==s.size) linear = 1;
        s.size = new_size;
      }
      else if (good-bad < 20*param->step_factor*bad)
      {
        linear = 1;
        new_thresh = s.size = bad + 1;
      }
      else s.size = (good+bad)/2;
      err_printf("bad= %ld good = %ld thresh = %ld linear = %ld\n",bad, good, thresh, linear);
    }
    if (s.size >= param->max_size)
    {
      if (option_trace >= 1)
        diag("Stop: max_size (%ld). Disable Algorithm B?\n",param->max_size);
      break;
    }
  }
  thresh = dat[analyze_dat(1)].size;
  if (option_trace >= 1)
    diag("Total time: %gs\n", (double)timer_delay(&T)/1000.);
  print_define(param->name, thresh);
  *(param->var) = thresh; /* set to optimal value for next tests */
  if (param->var_disable) *(param->var_disable) = save_var_disable;
  if (param->var_enable) *(param->var_enable) = s.var_enable_min;
  avma = av;
}

void error(char **argv) {
  long i;
  diag("This is the PARI/GP tuning utility. Usage: tune [OPTION] var1 var2...\n");
  diag("Options:\n");
  diag("  -t:     verbose output\n");
  diag("  -tt:    very verbose output\n");
  diag("  -ttt:   output everything\n");
  diag("  -s xxx: set step factor between successive sizes to xxx (default 0.01)\n");
  diag("  -p xxx: set Flx modulus to xxx (default 27449)\n");
  diag("  -u xxx: set speed_unittime to xxx (default 1e-4s)\n");
  diag("Tunable variables (omitting variable indices tunes everybody):\n");
  for (i = 0; i < (long)numberof(param); i++)
    diag("  %2ld: %-25s (default %4ld)\n", i, param[i].name, *(param[i].var));
  exit(1);
}

int
main(int argc, char **argv)
{
  int i, r, n = 0;
  int linear = 1;
  GEN v;
  pari_init(8000000, 2);
  DFLT_mod = 27449;
  LARGE_mod=subis(powuu(3,128),62);
#ifdef LONG_IS_64BIT
  DFLT_qmod = 3;
  DFLT_hmod = 257;
  DFLT_mod2 = 281474976710677UL;
#else
  DFLT_qmod = 3;
  DFLT_hmod = 3;
  DFLT_mod1 = 1031UL;
#endif
  v = new_chunk(argc);
  for (i = 1; i < argc; i++)
  {
    char *s = argv[i];
    if (*s == '-') {
      switch(*++s) {
        case 't': option_trace++;
          while (*++s == 't') option_trace++;
          break;
        case 'd': linear = 1-linear;
          break;
        case 'p':
          if (!*++s)
          {
            if (++i == argc) error(argv);
            s = argv[i];
          }
          DFLT_mod = itou(gp_read_str(s)); break;
        case 's':
          if (!*++s)
          {
            if (++i == argc) error(argv);
            s = argv[i];
          }
          Step_Factor = atof(s); break;
        case 'u': s++;
          if (!*++s)
          {
            if (++i == argc) error(argv);
            s = argv[i];
          }
          speed_unittime = atof(s); break;
        default: error(argv);
      }
    } else {
      if (!isdigit((int)*s)) error(argv);
      r = atol(s); if (r >= (long)numberof(param) || r < 0) error(argv);
      v[n++] = r;
    }
  }
  if (n) { for (i = 0; i < n; i++) Test(&param[ v[i] ], linear); return 0; }
  n = numberof(param);
  for (i = 0; i < n; i++) Test(&param[i], linear);
  return 0;
}
