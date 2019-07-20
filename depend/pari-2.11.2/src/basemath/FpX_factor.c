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

/***********************************************************************/
/**                                                                   **/
/**               Factorisation over finite field                     **/
/**                                                                   **/
/***********************************************************************/

/*******************************************************************/
/*                                                                 */
/*           ROOTS MODULO a prime p (no multiplicities)            */
/*                                                                 */
/*******************************************************************/
/* Replace F by a monic normalized FpX having the same factors;
 * assume p prime and *F a ZX */
static int
ZX_factmod_init(GEN *F, GEN p)
{
  if (lgefint(p) == 3)
  {
    ulong pp = p[2];
    if (pp == 2) { *F = ZX_to_F2x(*F); return 0; }
    *F = ZX_to_Flx(*F, pp);
    if (lg(*F) > 3) *F = Flx_normalize(*F, pp);
    return 1;
  }
  *F = FpX_red(*F, p);
  if (lg(*F) > 3) *F = FpX_normalize(*F, p);
  return 2;
}
static void
ZX_rootmod_init(GEN *F, GEN p)
{
  if (lgefint(p) == 3)
  {
    ulong pp = p[2];
    *F = ZX_to_Flx(*F, pp);
    if (lg(*F) > 3) *F = Flx_normalize(*F, pp);
  }
  else
  {
    *F = FpX_red(*F, p);
    if (lg(*F) > 3) *F = FpX_normalize(*F, p);
  }
}

/* return 1,...,p-1 [not_0 = 1] or 0,...,p [not_0 = 0] */
static GEN
all_roots_mod_p(ulong p, int not_0)
{
  GEN r;
  ulong i;
  if (not_0) {
    r = cgetg(p, t_VECSMALL);
    for (i = 1; i < p; i++) r[i] = i;
  } else {
    r = cgetg(p+1, t_VECSMALL);
    for (i = 0; i < p; i++) r[i+1] = i;
  }
  return r;
}

/* X^n - 1 */
static GEN
Flx_Xnm1(long sv, long n, ulong p)
{
  GEN t = cgetg(n+3, t_VECSMALL);
  long i;
  t[1] = sv;
  t[2] = p - 1;
  for (i = 3; i <= n+1; i++) t[i] = 0;
  t[i] = 1; return t;
}
/* X^n + 1 */
static GEN
Flx_Xn1(long sv, long n, ulong p)
{
  GEN t = cgetg(n+3, t_VECSMALL);
  long i;
  (void) p;
  t[1] = sv;
  t[2] = 1;
  for (i = 3; i <= n+1; i++) t[i] = 0;
  t[i] = 1; return t;
}

static ulong
Fl_nonsquare(ulong p)
{
  long k = 2;
  for (;; k++)
  {
    long i = krouu(k, p);
    if (!i) pari_err_PRIME("Fl_nonsquare",utoipos(p));
    if (i < 0) return k;
  }
}

static GEN
Flx_root_mod_2(GEN f)
{
  int z1, z0 = !(f[2] & 1);
  long i,n;
  GEN y;

  for (i=2, n=1; i < lg(f); i++) n += f[i];
  z1 = n & 1;
  y = cgetg(z0+z1+1, t_VECSMALL); i = 1;
  if (z0) y[i++] = 0;
  if (z1) y[i  ] = 1;
  return y;
}
static ulong
Flx_oneroot_mod_2(GEN f)
{
  long i,n;
  if (!(f[2] & 1)) return 0;
  for (i=2, n=1; i < lg(f); i++) n += f[i];
  if (n & 1) return 1;
  return 2;
}

static GEN FpX_roots_i(GEN f, GEN p);
static GEN Flx_roots_i(GEN f, ulong p);

static int
cmpGuGu(GEN a, GEN b) { return (ulong)a < (ulong)b? -1: (a == b? 0: 1); }

/* Generic driver to computes the roots of f modulo pp, using 'Roots' when
 * pp is a small prime.
 * if (gpwrap), check types thoroughly and return t_INTMODs, otherwise
 * assume that f is an FpX, pp a prime and return t_INTs */
static GEN
rootmod_aux(GEN f, GEN pp)
{
  GEN y;
  switch(lg(f))
  {
    case 2: pari_err_ROOTS0("rootmod");
    case 3: return cgetg(1,t_COL);
  }
  if (typ(f) == t_VECSMALL)
  {
    ulong p = pp[2];
    if (p == 2)
      y = Flx_root_mod_2(f);
    else
    {
      if (!odd(p)) pari_err_PRIME("rootmod",utoi(p));
      y = Flx_roots_i(f, p);
    }
    y = Flc_to_ZC(y);
  }
  else
    y = FpX_roots_i(f, pp);
  return y;
}
/* assume that f is a ZX and p a prime */
GEN
FpX_roots(GEN f, GEN p)
{
  pari_sp av = avma;
  GEN y; ZX_rootmod_init(&f, p); y = rootmod_aux(f, p);
  return gerepileupto(av, y);
}

/* assume x reduced mod p > 2, monic. */
static int
FpX_quad_factortype(GEN x, GEN p)
{
  GEN b = gel(x,3), c = gel(x,2);
  GEN D = subii(sqri(b), shifti(c,2));
  return kronecker(D,p);
}
/* assume x reduced mod p, monic. Return one root, or NULL if irreducible */
static GEN
FpX_quad_root(GEN x, GEN p, int unknown)
{
  GEN s, D, b = gel(x,3), c = gel(x,2);

  if (absequaliu(p, 2)) {
    if (!signe(b)) return c;
    return signe(c)? NULL: gen_1;
  }
  D = subii(sqri(b), shifti(c,2));
  D = remii(D,p);
  if (unknown && kronecker(D,p) == -1) return NULL;

  s = Fp_sqrt(D,p);
  /* p is not prime, go on and give e.g. maxord a chance to recover */
  if (!s) return NULL;
  return Fp_halve(Fp_sub(s,b, p), p);
}
static GEN
FpX_otherroot(GEN x, GEN r, GEN p)
{ return Fp_neg(Fp_add(gel(x,3), r, p), p); }

/* disc(x^2+bx+c) = b^2 - 4c */
static ulong
Fl_disc_bc(ulong b, ulong c, ulong p)
{ return Fl_sub(Fl_sqr(b,p), Fl_double(Fl_double(c,p),p), p); }
/* p > 2 */
static ulong
Flx_quad_root(GEN x, ulong p, int unknown)
{
  ulong s, b = x[3], c = x[2];
  ulong D = Fl_disc_bc(b, c, p);
  if (unknown && krouu(D,p) == -1) return p;
  s = Fl_sqrt(D,p);
  if (s==~0UL) return p;
  return Fl_halve(Fl_sub(s,b, p), p);
}
static ulong
Flx_otherroot(GEN x, ulong r, ulong p)
{ return Fl_neg(Fl_add(x[3], r, p), p); }


/* 'todo' contains the list of factors to be split.
 * 'done' the list of finished factors, no longer touched */
struct split_t { GEN todo, done; };
static void
split_init(struct split_t *S, long max)
{
  S->todo = vectrunc_init(max);
  S->done = vectrunc_init(max);
}
#if 0
/* move todo[i] to done */
static void
split_convert(struct split_t *S, long i)
{
  long n = lg(S->todo)-1;
  vectrunc_append(S->done, gel(S->todo,i));
  if (n) gel(S->todo,i) = gel(S->todo, n);
  setlg(S->todo, n);
}
#endif
/* append t to todo */
static void
split_add(struct split_t *S, GEN t) { vectrunc_append(S->todo, t); }
/* delete todo[i], add t to done */
static void
split_moveto_done(struct split_t *S, long i, GEN t)
{
  long n = lg(S->todo)-1;
  vectrunc_append(S->done, t);
  if (n) gel(S->todo,i) = gel(S->todo, n);
  setlg(S->todo, n);

}
/* append t to done */
static void
split_add_done(struct split_t *S, GEN t)
{ vectrunc_append(S->done, t); }
/* split todo[i] into a and b */
static void
split_todo(struct split_t *S, long i, GEN a, GEN b)
{
  gel(S->todo, i) = a;
  split_add(S, b);
}
/* split todo[i] into a and b, moved to done */
static void
split_done(struct split_t *S, long i, GEN a, GEN b)
{
  split_moveto_done(S, i, a);
  split_add_done(S, b);
}

/* by splitting, assume p > 2 prime, deg(f) > 0, and f monic */
static GEN
FpX_roots_i(GEN f, GEN p)
{
  GEN pol, pol0, a, q;
  struct split_t S;

  split_init(&S, lg(f)-1);
  settyp(S.done, t_COL);
  if (ZX_valrem(f, &f)) split_add_done(&S, gen_0);
  switch(degpol(f))
  {
    case 0: return ZC_copy(S.done);
    case 1: split_add_done(&S, subii(p, gel(f,2))); return ZC_copy(S.done);
    case 2: {
      GEN s, r = FpX_quad_root(f, p, 1);
      if (r) {
        split_add_done(&S, r);
        s = FpX_otherroot(f,r, p);
        /* f not known to be square free yet */
        if (!equalii(r, s)) split_add_done(&S, s);
      }
      return sort(S.done);
    }
  }

  a = FpXQ_pow(pol_x(varn(f)), subiu(p,1), f,p);
  if (lg(a) < 3) pari_err_PRIME("rootmod",p);
  a = FpX_Fp_sub_shallow(a, gen_1, p); /* a = x^(p-1) - 1 mod f */
  a = FpX_gcd(f,a, p);
  if (!degpol(a)) return ZC_copy(S.done);
  split_add(&S, FpX_normalize(a,p));

  q = shifti(p,-1);
  pol0 = icopy(gen_1); /* constant term, will vary in place */
  pol = deg1pol_shallow(gen_1, pol0, varn(f));
  for (pol0[2] = 1;; pol0[2]++)
  {
    long j, l = lg(S.todo);
    if (l == 1) return sort(S.done);
    if (pol0[2] == 100 && !BPSW_psp(p)) pari_err_PRIME("polrootsmod",p);
    for (j = 1; j < l; j++)
    {
      GEN b, r, s, c = gel(S.todo,j);
      switch(degpol(c))
      { /* convert linear and quadratics to roots, try to split the rest */
        case 1:
          split_moveto_done(&S, j, subii(p, gel(c,2)));
          j--; l--; break;
        case 2:
          r = FpX_quad_root(c, p, 0);
          if (!r) pari_err_PRIME("polrootsmod",p);
          s = FpX_otherroot(c,r, p);
          split_done(&S, j, r, s);
          j--; l--; break;
        default:
          b = FpXQ_pow(pol,q, c,p);
          if (degpol(b) <= 0) continue;
          b = FpX_gcd(c,FpX_Fp_sub_shallow(b,gen_1,p), p);
          if (!degpol(b)) continue;
          b = FpX_normalize(b, p);
          c = FpX_div(c,b, p);
          split_todo(&S, j, b, c);
      }
    }
  }
}

/* Assume f is normalized */
static ulong
Flx_cubic_root(GEN ff, ulong p)
{
  GEN f = Flx_normalize(ff,p);
  ulong pi = get_Fl_red(p);
  ulong a = f[4], b=f[3], c=f[2], p3 = p%3==1 ? (2*p+1)/3 :(p+1)/3;
  ulong t = Fl_mul_pre(a, p3, p, pi), t2 = Fl_sqr_pre(t, p, pi);
  ulong A = Fl_sub(b, Fl_triple(t2, p), p);
  ulong B = Fl_addmul_pre(c, t, Fl_sub(Fl_double(t2, p), b, p), p, pi);
  ulong A3 =  Fl_mul_pre(A, p3, p, pi);
  ulong A32 = Fl_sqr_pre(A3, p, pi), A33 = Fl_mul_pre(A3, A32, p, pi);
  ulong S = Fl_neg(B,p), P = Fl_neg(A3,p);
  ulong D = Fl_add(Fl_sqr_pre(S, p, pi), Fl_double(Fl_double(A33, p), p), p);
  ulong s = Fl_sqrt_pre(D, p, pi), vS1, vS2;
  if (s!=~0UL)
  {
    ulong S1 = S==s ? S: Fl_halve(Fl_sub(S, s, p), p);
    if (p%3==2) /* 1 solutions */
      vS1 = Fl_powu_pre(S1, (2*p-1)/3, p, pi);
    else
    {
      vS1 = Fl_sqrtl_pre(S1, 3, p, pi);
      if (vS1==~0UL) return p; /*0 solutions*/
      /*3 solutions*/
    }
    vS2 = P? Fl_mul_pre(P, Fl_inv(vS1, p), p, pi): 0;
    return Fl_sub(Fl_add(vS1,vS2, p), t, p);
  }
  else
  {
    pari_sp av = avma;
    GEN S1 = mkvecsmall2(Fl_halve(S, p), Fl_halve(1UL, p));
    GEN vS1 = Fl2_sqrtn_pre(S1, utoi(3), D, p, pi, NULL);
    ulong Sa;
    if (!vS1) return p; /*0 solutions, p%3==2*/
    Sa = vS1[1];
    if (p%3==1) /*1 solutions*/
    {
      ulong Fa = Fl2_norm_pre(vS1, D, p, pi);
      if (Fa!=P)
        Sa = Fl_mul(Sa, Fl_div(Fa, P, p),p);
    }
    avma = av;
    return Fl_sub(Fl_double(Sa,p),t,p);
  }
}

/* assume p > 2 prime */
static ulong
Flx_oneroot_i(GEN f, ulong p, long fl)
{
  GEN pol, a;
  ulong q;
  long da;

  if (Flx_val(f)) return 0;
  switch(degpol(f))
  {
    case 1: return Fl_neg(f[2], p);
    case 2: return Flx_quad_root(f, p, 1);
    case 3: if (p>3) return Flx_cubic_root(f, p); /*FALL THROUGH*/
  }

  if (!fl)
  {
    a = Flxq_powu(polx_Flx(f[1]), p - 1, f,p);
    if (lg(a) < 3) pari_err_PRIME("rootmod",utoipos(p));
    a = Flx_Fl_add(a, p-1, p); /* a = x^(p-1) - 1 mod f */
    a = Flx_gcd(f,a, p);
  } else a = f;
  da = degpol(a);
  if (!da) return p;
  a = Flx_normalize(a,p);

  q = p >> 1;
  pol = polx_Flx(f[1]);
  for(pol[2] = 1;; pol[2]++)
  {
    if (pol[2] == 1000 && !uisprime(p)) pari_err_PRIME("Flx_oneroot",utoipos(p));
    switch(da)
    {
      case 1: return Fl_neg(a[2], p);
      case 2: return Flx_quad_root(a, p, 0);
      case 3: if (p>3) return Flx_cubic_root(a, p); /*FALL THROUGH*/
      default: {
        GEN b = Flxq_powu(pol,q, a,p);
        long db;
        if (degpol(b) <= 0) continue;
        b = Flx_gcd(a,Flx_Fl_add(b,p-1,p), p);
        db = degpol(b); if (!db) continue;
        b = Flx_normalize(b, p);
        if (db <= (da >> 1)) {
          a = b;
          da = db;
        } else {
          a = Flx_div(a,b, p);
          da -= db;
        }
      }
    }
  }
}

/* assume p > 2 prime */
static GEN
FpX_oneroot_i(GEN f, GEN p)
{
  GEN pol, pol0, a, q;
  long da;

  if (ZX_val(f)) return gen_0;
  switch(degpol(f))
  {
    case 1: return subii(p, gel(f,2));
    case 2: return FpX_quad_root(f, p, 1);
  }

  a = FpXQ_pow(pol_x(varn(f)), subiu(p,1), f,p);
  if (lg(a) < 3) pari_err_PRIME("rootmod",p);
  a = FpX_Fp_sub_shallow(a, gen_1, p); /* a = x^(p-1) - 1 mod f */
  a = FpX_gcd(f,a, p);
  da = degpol(a);
  if (!da) return NULL;
  a = FpX_normalize(a,p);

  q = shifti(p,-1);
  pol0 = icopy(gen_1); /* constant term, will vary in place */
  pol = deg1pol_shallow(gen_1, pol0, varn(f));
  for (pol0[2]=1; ; pol0[2]++)
  {
    if (pol0[2] == 1000 && !BPSW_psp(p)) pari_err_PRIME("FpX_oneroot",p);
    switch(da)
    {
      case 1: return subii(p, gel(a,2));
      case 2: return FpX_quad_root(a, p, 0);
      default: {
        GEN b = FpXQ_pow(pol,q, a,p);
        long db;
        if (degpol(b) <= 0) continue;
        b = FpX_gcd(a,FpX_Fp_sub_shallow(b,gen_1,p), p);
        db = degpol(b); if (!db) continue;
        b = FpX_normalize(b, p);
        if (db <= (da >> 1)) {
          a = b;
          da = db;
        } else {
          a = FpX_div(a,b, p);
          da -= db;
        }
      }
    }
  }
}

ulong
Flx_oneroot(GEN f, ulong p)
{
  pari_sp av = avma;
  ulong r;
  switch(lg(f))
  {
    case 2: return 0;
    case 3: avma = av; return p;
  }
  if (p == 2) return Flx_oneroot_mod_2(f);
  r = Flx_oneroot_i(Flx_normalize(f, p), p, 0);
  avma = av; return r;
}

ulong
Flx_oneroot_split(GEN f, ulong p)
{
  pari_sp av = avma;
  ulong r;
  switch(lg(f))
  {
    case 2: return 0;
    case 3: avma = av; return p;
  }
  if (p == 2) return Flx_oneroot_mod_2(f);
  r = Flx_oneroot_i(Flx_normalize(f, p), p, 1);
  avma = av; return r;
}

/* assume that p is prime */
GEN
FpX_oneroot(GEN f, GEN pp) {
  pari_sp av = avma;
  ZX_rootmod_init(&f, pp);
  switch(lg(f))
  {
    case 2: avma = av; return gen_0;
    case 3: avma = av; return NULL;
  }
  if (typ(f) == t_VECSMALL)
  {
    ulong r, p = pp[2];
    if (p == 2)
      r = Flx_oneroot_mod_2(f);
    else
      r = Flx_oneroot_i(f, p, 0);
    avma = av;
    return (r == p)? NULL: utoi(r);
  }
  f = FpX_oneroot_i(f, pp);
  if (!f) { avma = av; return NULL; }
  return gerepileuptoint(av, f);
}

/* returns a root of unity in F_p that is suitable for finding a factor   */
/* of degree deg_factor of a polynomial of degree deg; the order is       */
/* returned in n                                                          */
/* A good choice seems to be n close to deg/deg_factor; we choose n       */
/* twice as big and decrement until it divides p-1.                       */
static GEN
good_root_of_unity(GEN p, long deg, long deg_factor, long *pt_n)
{
   pari_sp ltop = avma;
   GEN pm, factn, power, base, zeta;
   long n;

   pm = subis (p, 1ul);
   for (n = deg / 2 / deg_factor + 1; !dvdiu (pm, n); n--);
   factn = Z_factor(stoi(n));
   power = diviuexact (pm, n);
   base = gen_1;
   do {
      base = addis (base, 1l);
      zeta = Fp_pow (base, power, p);
   }
   while (!equaliu (Fp_order (zeta, factn, p), n));
   *pt_n = n;
   return gerepileuptoint (ltop, zeta);
}

GEN
FpX_oneroot_split(GEN fact, GEN p)
{
  pari_sp av = avma;
  long n, deg_f, i, dmin;
  GEN prim, expo, minfactor, xplusa, zeta, xpow;
  fact = FpX_normalize(fact, p);
  deg_f = degpol(fact);
  if (deg_f<=2) return FpX_oneroot(fact, p);
  minfactor = fact; /* factor of minimal degree found so far */
  dmin = degpol(minfactor);
  prim = good_root_of_unity(p, deg_f, 1, &n);
  expo = diviuexact(subiu(p, 1), n);
  xplusa = pol_x(varn(fact));
  zeta = gen_1;
  while (dmin != 1)
  {
    /* split minfactor by computing its gcd with (X+a)^exp-zeta, where    */
    /* zeta varies over the roots of unity in F_p                         */
    fact = minfactor; deg_f = dmin;
    /* update X+a, avoid a=0 */
    gel (xplusa, 2) = addis (gel (xplusa, 2), 1);
    xpow = FpXQ_pow (xplusa, expo, fact, p);
    for (i = 0; i < n; i++)
    {
      GEN tmp = FpX_gcd(FpX_Fp_sub(xpow, zeta, p), fact, p);
      long dtmp = degpol(tmp);
      if (dtmp > 0 && dtmp < deg_f)
      {
        fact = FpX_div(fact, tmp, p); deg_f = degpol(fact);
        if (dtmp < dmin)
        {
          minfactor = FpX_normalize (tmp, p);
          dmin = dtmp;
          if (dmin == 1 || dmin <= deg_f / (n / 2) + 1)
            /* stop early to avoid too many gcds */
            break;
        }
      }
      zeta = Fp_mul (zeta, prim, p);
    }
  }
  return gerepileuptoint(av, Fp_neg(gel(minfactor,2), p));
}

/*******************************************************************/
/*                                                                 */
/*                     FACTORISATION MODULO p                      */
/*                                                                 */
/*******************************************************************/

/* F / E  a vector of vectors of factors / exponents of virtual length l
 * (their real lg may be larger). Set their lg to j, concat and return [F,E] */
static GEN
FE_concat(GEN F, GEN E, long l)
{
  setlg(E,l); E = shallowconcat1(E);
  setlg(F,l); F = shallowconcat1(F); return mkvec2(F,E);
}

static GEN
ddf_to_ddf2_i(GEN V, long fl)
{
  GEN F, D;
  long i, j, l = lg(V);
  F = cgetg(l, t_VEC);
  D = cgetg(l, t_VECSMALL);
  for (i = j = 1; i < l; i++)
  {
    GEN Vi = gel(V,i);
    if ((fl==2 && F2x_degree(Vi) == 0)
      ||(fl==0 && degpol(Vi) == 0)) continue;
    gel(F,j) = Vi;
    uel(D,j) = i; j++;
  }
  setlg(F,j);
  setlg(D,j); return mkvec2(F,D);
}

GEN
ddf_to_ddf2(GEN V)
{ return ddf_to_ddf2_i(V, 0); }

static GEN
F2x_ddf_to_ddf2(GEN V)
{ return ddf_to_ddf2_i(V, 2); }

GEN
vddf_to_simplefact(GEN V, long d)
{
  GEN E, F;
  long i, j, c, l = lg(V);
  F = cgetg(d+1, t_VECSMALL);
  E = cgetg(d+1, t_VECSMALL);
  for (i = c = 1; i < l; i++)
  {
    GEN Vi = gel(V,i);
    long l = lg(Vi);
    for (j = 1; j < l; j++)
    {
      long k, n = degpol(gel(Vi,j)) / j;
      for (k = 1; k <= n; k++) { uel(F,c) = j; uel(E,c) = i; c++; }
    }
  }
  setlg(F,c);
  setlg(E,c);
  return sort_factor(mkvec2(F,E), (void*)&cmpGuGu, cmp_nodata);
}

/* product of terms of degree 1 in factorization of f */
GEN
FpX_split_part(GEN f, GEN p)
{
  long n = degpol(f);
  GEN z, X = pol_x(varn(f));
  if (n <= 1) return f;
  f = FpX_red(f, p);
  z = FpX_sub(FpX_Frobenius(f, p), X, p);
  return FpX_gcd(z,f,p);
}

/* Compute the number of roots in Fp without counting multiplicity
 * return -1 for 0 polynomial. lc(f) must be prime to p. */
long
FpX_nbroots(GEN f, GEN p)
{
  pari_sp av = avma;
  GEN z = FpX_split_part(f, p);
  avma = av; return degpol(z);
}

int
FpX_is_totally_split(GEN f, GEN p)
{
  long n=degpol(f);
  pari_sp av = avma;
  if (n <= 1) return 1;
  if (abscmpui(n, p) > 0) return 0;
  f = FpX_red(f, p);
  avma = av; return gequalX(FpX_Frobenius(f, p));
}

long
Flx_nbroots(GEN f, ulong p)
{
  long n = degpol(f);
  pari_sp av = avma;
  GEN z;
  if (n <= 1) return n;
  if (n == 2)
  {
    ulong D;
    if (p==2) return (f[2]==0) + (f[2]!=f[3]);
    D = Fl_sub(Fl_sqr(f[3], p), Fl_mul(Fl_mul(f[4], f[2], p), 4%p, p), p);
    return 1 + krouu(D,p);
  }
  z = Flx_sub(Flx_Frobenius(f, p), polx_Flx(f[1]), p);
  z = Flx_gcd(z, f, p);
  avma = av; return degpol(z);
}

long
FpX_ddf_degree(GEN T, GEN XP, GEN p)
{
  pari_sp av = avma;
  GEN X, b, g, xq;
  long i, j, n, v, B, l, m;
  pari_timer ti;
  hashtable h;

  n = get_FpX_degree(T); v = get_FpX_var(T);
  X = pol_x(v);
  if (ZX_equal(X,XP)) return 1;
  B = n/2;
  l = usqrt(B);
  m = (B+l-1)/l;
  T = FpX_get_red(T, p);
  hash_init_GEN(&h, l+2, ZX_equal, 1);
  hash_insert_long(&h, X,  0);
  hash_insert_long(&h, XP, 1);
  if (DEBUGLEVEL>=7) timer_start(&ti);
  b = XP;
  xq = FpXQ_powers(b, brent_kung_optpow(n, l-1, 1),  T, p);
  if (DEBUGLEVEL>=7) timer_printf(&ti,"FpX_ddf_degree: xq baby");
  for (i = 3; i <= l+1; i++)
  {
    b = FpX_FpXQV_eval(b, xq, T, p);
    if (gequalX(b)) { avma = av; return i-1; }
    hash_insert_long(&h, b, i-1);
  }
  if (DEBUGLEVEL>=7) timer_printf(&ti,"FpX_ddf_degree: baby");
  g = b;
  xq = FpXQ_powers(g, brent_kung_optpow(n, m, 1),  T, p);
  if (DEBUGLEVEL>=7) timer_printf(&ti,"FpX_ddf_degree: xq giant");
  for(i = 2; i <= m+1; i++)
  {
    g = FpX_FpXQV_eval(g, xq, T, p);
    if (hash_haskey_long(&h, g, &j)) { avma=av; return l*i-j; }
  }
  avma = av; return n;
}

/* See <http://www.shoup.net/papers/factorimpl.pdf> */
static GEN
FpX_ddf_Shoup(GEN T, GEN XP, GEN p)
{
  GEN b, g, h, F, f, Tr, xq;
  long i, j, n, v, B, l, m;
  pari_timer ti;

  n = get_FpX_degree(T); v = get_FpX_var(T);
  if (n == 0) return cgetg(1, t_VEC);
  if (n == 1) return mkvec(get_FpX_mod(T));
  B = n/2;
  l = usqrt(B);
  m = (B+l-1)/l;
  T = FpX_get_red(T, p);
  b = cgetg(l+2, t_VEC);
  gel(b, 1) = pol_x(v);
  gel(b, 2) = XP;
  if (DEBUGLEVEL>=7) timer_start(&ti);
  xq = FpXQ_powers(gel(b, 2), brent_kung_optpow(n, l-1, 1),  T, p);
  if (DEBUGLEVEL>=7) timer_printf(&ti,"FpX_ddf_Shoup: xq baby");
  for (i = 3; i <= l+1; i++)
    gel(b, i) = FpX_FpXQV_eval(gel(b, i-1), xq, T, p);
  if (DEBUGLEVEL>=7) timer_printf(&ti,"FpX_ddf_Shoup: baby");
  xq = FpXQ_powers(gel(b, l+1), brent_kung_optpow(n, m-1, 1),  T, p);
  if (DEBUGLEVEL>=7) timer_printf(&ti,"FpX_ddf_Shoup: xq giant");
  g = cgetg(m+1, t_VEC);
  gel(g, 1) = gel(xq, 2);
  for(i = 2; i <= m; i++) gel(g, i) = FpX_FpXQV_eval(gel(g, i-1), xq, T, p);
  if (DEBUGLEVEL>=7) timer_printf(&ti,"FpX_ddf_Shoup: giant");
  h = cgetg(m+1, t_VEC);
  for (j = 1; j <= m; j++)
  {
    pari_sp av = avma;
    GEN gj = gel(g,j), e = FpX_sub(gj, gel(b,1), p);
    for (i = 2; i <= l; i++) e = FpXQ_mul(e, FpX_sub(gj, gel(b,i), p), T, p);
    gel(h,j) = gerepileupto(av, e);
  }
  if (DEBUGLEVEL>=7) timer_printf(&ti,"FpX_ddf_Shoup: diff");
  Tr = get_FpX_mod(T);
  F = cgetg(m+1, t_VEC);
  for (j = 1; j <= m; j++)
  {
    GEN u = FpX_gcd(Tr, gel(h,j), p);
    if (degpol(u))
    {
      u = FpX_normalize(u, p);
      Tr = FpX_div(Tr, u, p);
    }
    gel(F,j) = u;
  }
  if (DEBUGLEVEL>=7) timer_printf(&ti,"FpX_ddf_Shoup: F");
  f = const_vec(n, pol_1(v));
  for (j = 1; j <= m; j++)
  {
    GEN e = gel(F, j);
    for (i=l-1; i >= 0; i--)
    {
      GEN u = FpX_gcd(e, FpX_sub(gel(g, j), gel(b, i+1), p), p);
      if (degpol(u))
      {
        u = FpX_normalize(u, p);
        gel(f, l*j-i) = u;
        e = FpX_div(e, u, p);
      }
      if (!degpol(e)) break;
    }
  }
  if (DEBUGLEVEL>=7) timer_printf(&ti,"FpX_ddf_Shoup: f");
  if (degpol(Tr)) gel(f, degpol(Tr)) = Tr;
  return f;
}

static void
FpX_edf_simple(GEN Tp, GEN XP, long d, GEN p, GEN V, long idx)
{
  long n = degpol(Tp), r = n/d, ct = 0;
  GEN T, f, ff, p2;
  if (r==1) { gel(V, idx) = Tp; return; }
  p2 = shifti(p,-1);
  T = FpX_get_red(Tp, p);
  XP = FpX_rem(XP, T, p);
  while (1)
  {
    pari_sp btop = avma;
    long i;
    GEN g = random_FpX(n, varn(Tp), p);
    GEN t = gel(FpXQ_auttrace(mkvec2(XP, g), d, T, p), 2);
    if (signe(t) == 0) continue;
    for(i=1; i<=10; i++)
    {
      pari_sp btop2 = avma;
      GEN R = FpXQ_pow(FpX_Fp_add(t, randomi(p), p), p2, T, p);
      f = FpX_gcd(FpX_Fp_sub(R, gen_1, p), Tp, p);
      if (degpol(f) > 0 && degpol(f) < n) break;
      avma = btop2;
    }
    if (degpol(f) > 0 && degpol(f) < n) break;
    if (++ct == 10 && !BPSW_psp(p)) pari_err_PRIME("FpX_edf_simple",p);
    avma = btop;
  }
  f = FpX_normalize(f, p);
  ff = FpX_div(Tp, f ,p);
  FpX_edf_simple(f, XP, d, p, V, idx);
  FpX_edf_simple(ff, XP, d, p, V, idx+degpol(f)/d);
}

static void
FpX_edf_rec(GEN T, GEN hp, GEN t, long d, GEN p2, GEN p, GEN V, long idx)
{
  pari_sp av;
  GEN Tp = get_FpX_mod(T);
  long n = degpol(hp), vT = varn(Tp), ct = 0;
  GEN u1, u2, f1, f2, R, h;
  h = FpX_get_red(hp, p);
  t = FpX_rem(t, T, p);
  av = avma;
  do
  {
    avma = av;
    R = FpXQ_pow(deg1pol(gen_1, randomi(p), vT), p2, h, p);
    u1 = FpX_gcd(FpX_Fp_sub(R, gen_1, p), hp, p);
    if (++ct == 10 && !BPSW_psp(p)) pari_err_PRIME("FpX_edf_rec",p);
  } while (degpol(u1)==0 || degpol(u1)==n);
  f1 = FpX_gcd(FpX_FpXQ_eval(u1, t, T, p), Tp, p);
  f1 = FpX_normalize(f1, p);
  u2 = FpX_div(hp, u1, p);
  f2 = FpX_div(Tp, f1, p);
  if (degpol(u1)==1)
    gel(V, idx) = f1;
  else
    FpX_edf_rec(FpX_get_red(f1, p), u1, t, d, p2, p, V, idx);
  idx += degpol(f1)/d;
  if (degpol(u2)==1)
    gel(V, idx) = f2;
  else
    FpX_edf_rec(FpX_get_red(f2, p), u2, t, d, p2, p, V, idx);
}

/* assume Tp a squarefree product of r > 1 irred. factors of degree d */
static void
FpX_edf(GEN Tp, GEN XP, long d, GEN p, GEN V, long idx)
{
  long n = degpol(Tp), r = n/d, vT = varn(Tp), ct = 0;
  GEN T, h, t;
  pari_timer ti;

  T = FpX_get_red(Tp, p);
  XP = FpX_rem(XP, T, p);
  if (DEBUGLEVEL>=7) timer_start(&ti);
  do
  {
    GEN g = random_FpX(n, vT, p);
    t = gel(FpXQ_auttrace(mkvec2(XP, g), d, T, p), 2);
    if (DEBUGLEVEL>=7) timer_printf(&ti,"FpX_edf: FpXQ_auttrace");
    h = FpXQ_minpoly(t, T, p);
    if (DEBUGLEVEL>=7) timer_printf(&ti,"FpX_edf: FpXQ_minpoly");
    if (++ct == 10 && !BPSW_psp(p)) pari_err_PRIME("FpX_edf",p);
  } while (degpol(h) != r);
  FpX_edf_rec(T, h, t, d, shifti(p, -1), p, V, idx);
}

static GEN
FpX_factor_Shoup(GEN T, GEN p)
{
  long i, n, s = 0;
  GEN XP, D, V;
  long e = expi(p);
  pari_timer ti;
  n = get_FpX_degree(T);
  T = FpX_get_red(T, p);
  if (DEBUGLEVEL>=6) timer_start(&ti);
  XP = FpX_Frobenius(T, p);
  if (DEBUGLEVEL>=6) timer_printf(&ti,"FpX_Frobenius");
  D = FpX_ddf_Shoup(T, XP, p);
  if (DEBUGLEVEL>=6) timer_printf(&ti,"FpX_ddf_Shoup");
  s = ddf_to_nbfact(D);
  V = cgetg(s+1, t_COL);
  for (i = 1, s = 1; i <= n; i++)
  {
    GEN Di = gel(D,i);
    long ni = degpol(Di), ri = ni/i;
    if (ni == 0) continue;
    Di = FpX_normalize(Di, p);
    if (ni == i) { gel(V, s++) = Di; continue; }
    if (ri <= e*expu(e))
      FpX_edf(Di, XP, i, p, V, s);
    else
      FpX_edf_simple(Di, XP, i, p, V, s);
    if (DEBUGLEVEL>=6) timer_printf(&ti,"FpX_edf(%ld)",i);
    s += ri;
  }
  return V;
}

long
ddf_to_nbfact(GEN D)
{
  long l = lg(D), i, s = 0;
  for(i = 1; i < l; i++) s += degpol(gel(D,i))/i;
  return s;
}

/* Yun algorithm: Assume p > degpol(T) */
static GEN
FpX_factor_Yun(GEN T, GEN p)
{
  long n = degpol(T), i = 1;
  GEN a, b, c, d = FpX_deriv(T, p);
  GEN V = cgetg(n+1,t_VEC);
  a = FpX_gcd(T, d, p);
  if (degpol(a) == 0) return mkvec(T);
  b = FpX_div(T, a, p);
  do
  {
    c = FpX_div(d, a, p);
    d = FpX_sub(c, FpX_deriv(b, p), p);
    a = FpX_normalize(FpX_gcd(b, d, p), p);
    gel(V, i++) = a;
    b = FpX_div(b, a, p);
  } while (degpol(b));
  setlg(V, i); return V;
}
GEN
FpX_factor_squarefree(GEN T, GEN p)
{
  if (lgefint(p)==3)
  {
    ulong pp = (ulong)p[2];
    GEN u = Flx_factor_squarefree(ZX_to_Flx(T,pp), pp);
    return FlxV_to_ZXV(u);
  }
  return FpX_factor_Yun(T, p);
}

long
FpX_ispower(GEN f, ulong k, GEN p, GEN *pt_r)
{
  pari_sp av = avma;
  GEN lc, F;
  long i, l, n = degpol(f), v = varn(f);
  if (n % k) return 0;
  if (lgefint(p)==3)
  {
    ulong pp = p[2];
    GEN fp = ZX_to_Flx(f, pp);
    if (!Flx_ispower(fp, k, pp, pt_r)) { avma = av; return 0; }
    if (pt_r) *pt_r = gerepileupto(av, Flx_to_ZX(*pt_r)); else avma = av;
    return 1;
  }
  lc = Fp_sqrtn(leading_coeff(f), stoi(k), p, NULL);
  if (!lc) { av = avma; return 0; }
  F = FpX_factor_Yun(f, p); l = lg(F)-1;
  for(i=1; i <= l; i++)
    if (i%k && degpol(gel(F,i))) { avma = av; return 0; }
  if (pt_r)
  {
    GEN r = scalarpol(lc, v), s = pol_1(v);
    for (i=l; i>=1; i--)
    {
      if (i%k) continue;
      s = FpX_mul(s, gel(F,i), p);
      r = FpX_mul(r, s, p);
    }
    *pt_r = gerepileupto(av, r);
  } else av = avma;
  return 1;
}

static GEN
FpX_factor_Cantor(GEN T, GEN p)
{
  GEN E, F, V = FpX_factor_Yun(T, p);
  long i, j, l = lg(V);
  F = cgetg(l, t_VEC);
  E = cgetg(l, t_VEC);
  for (i=1, j=1; i < l; i++)
    if (degpol(gel(V,i)))
    {
      GEN Fj = FpX_factor_Shoup(gel(V,i), p);
      gel(F, j) = Fj;
      gel(E, j) = const_vecsmall(lg(Fj)-1, i);
      j++;
    }
  return sort_factor_pol(FE_concat(F,E,j), cmpii);
}

static GEN
FpX_ddf_i(GEN T, GEN p)
{
  GEN XP;
  T = FpX_get_red(T, p);
  XP = FpX_Frobenius(T, p);
  return ddf_to_ddf2(FpX_ddf_Shoup(T, XP, p));
}

GEN
FpX_ddf(GEN f, GEN p)
{
  pari_sp av = avma;
  GEN F;
  switch(ZX_factmod_init(&f, p))
  {
    case 0:  F = F2x_ddf(f);
             F2xV_to_ZXV_inplace(gel(F,1)); break;
    case 1:  F = Flx_ddf(f,p[2]);
             FlxV_to_ZXV_inplace(gel(F,1)); break;
    default: F = FpX_ddf_i(f,p); break;
  }
  return gerepilecopy(av, F);
}

static GEN Flx_simplefact_Cantor(GEN T, ulong p);
static GEN
FpX_simplefact_Cantor(GEN T, GEN p)
{
  GEN V, XP;
  long i, l;
  if (lgefint(p) == 3)
  {
    ulong pp = p[2];
    return Flx_simplefact_Cantor(ZX_to_Flx(T,pp), pp);
  }
  T = FpX_get_red(T, p);
  XP = FpX_Frobenius(T, p);
  V = FpX_factor_Yun(get_FpX_mod(T), p); l = lg(V);
  for (i=1; i < l; i++) gel(V,i) = FpX_ddf_Shoup(gel(V,i), XP, p);
  return vddf_to_simplefact(V, get_FpX_degree(T));
}

static int
FpX_isirred_Cantor(GEN Tp, GEN p)
{
  pari_sp av = avma;
  pari_timer ti;
  long n, d;
  GEN T = get_FpX_mod(Tp);
  GEN dT = FpX_deriv(T, p);
  GEN XP, D;
  if (degpol(FpX_gcd(T, dT, p)) != 0) { avma = av; return 0; }
  n = get_FpX_degree(T);
  T = FpX_get_red(Tp, p);
  if (DEBUGLEVEL>=6) timer_start(&ti);
  XP = FpX_Frobenius(T, p);
  if (DEBUGLEVEL>=6) timer_printf(&ti,"FpX_Frobenius");
  D = FpX_ddf_Shoup(T, XP, p);
  if (DEBUGLEVEL>=6) timer_printf(&ti,"FpX_ddf_Shoup");
  d = degpol(gel(D, n));
  avma = av; return d==n;
}

static GEN FpX_factor_deg2(GEN f, GEN p, long d, long flag);

/*Assume that p is large and odd*/
static GEN
FpX_factor_i(GEN f, GEN pp, long flag)
{
  long d = degpol(f);
  if (d <= 2) return FpX_factor_deg2(f,pp,d,flag);
  switch(flag)
  {
    default: return FpX_factor_Cantor(f, pp);
    case 1: return FpX_simplefact_Cantor(f, pp);
    case 2: return FpX_isirred_Cantor(f, pp)? gen_1: NULL;
  }
}

long
FpX_nbfact_Frobenius(GEN T, GEN XP, GEN p)
{
  pari_sp av = avma;
  long s = ddf_to_nbfact(FpX_ddf_Shoup(T, XP, p));
  avma = av; return s;
}

long
FpX_nbfact(GEN T, GEN p)
{
  pari_sp av = avma;
  GEN XP = FpX_Frobenius(T, p);
  long n = FpX_nbfact_Frobenius(T, XP, p);
  avma = av; return n;
}

/* p > 2 */
static GEN
FpX_is_irred_2(GEN f, GEN p, long d)
{
  switch(d)
  {
    case -1:
    case 0: return NULL;
    case 1: return gen_1;
  }
  return FpX_quad_factortype(f, p) == -1? gen_1: NULL;
}
/* p > 2 */
static GEN
FpX_degfact_2(GEN f, GEN p, long d)
{
  switch(d)
  {
    case -1:retmkvec2(mkvecsmall(-1),mkvecsmall(1));
    case 0: return trivial_fact();
    case 1: retmkvec2(mkvecsmall(1), mkvecsmall(1));
  }
  switch(FpX_quad_factortype(f, p)) {
    case  1: retmkvec2(mkvecsmall2(1,1), mkvecsmall2(1,1));
    case -1: retmkvec2(mkvecsmall(2), mkvecsmall(1));
    default: retmkvec2(mkvecsmall(1), mkvecsmall(2));
  }
}

GEN
prime_fact(GEN x) { retmkmat2(mkcolcopy(x), mkcol(gen_1)); }
GEN
trivial_fact(void) { retmkmat2(cgetg(1,t_COL), cgetg(1,t_COL)); }

/* not gerepile safe */
static GEN
FpX_factor_2(GEN f, GEN p, long d)
{
  GEN r, s, R, S;
  long v;
  int sgn;
  switch(d)
  {
    case -1: retmkvec2(mkcol(pol_0(varn(f))), mkvecsmall(1));
    case  0: retmkvec2(cgetg(1,t_COL), cgetg(1,t_VECSMALL));
    case  1: retmkvec2(mkcol(f), mkvecsmall(1));
  }
  r = FpX_quad_root(f, p, 1);
  if (!r) return mkvec2(mkcol(f), mkvecsmall(1));
  v = varn(f);
  s = FpX_otherroot(f, r, p);
  if (signe(r)) r = subii(p, r);
  if (signe(s)) s = subii(p, s);
  sgn = cmpii(s, r); if (sgn < 0) swap(s,r);
  R = deg1pol_shallow(gen_1, r, v);
  if (!sgn) return mkvec2(mkcol(R), mkvecsmall(2));
  S = deg1pol_shallow(gen_1, s, v);
  return mkvec2(mkcol2(R,S), mkvecsmall2(1,1));
}
static GEN
FpX_factor_deg2(GEN f, GEN p, long d, long flag)
{
  switch(flag) {
    case 2: return FpX_is_irred_2(f, p, d);
    case 1: return FpX_degfact_2(f, p, d);
    default: return FpX_factor_2(f, p, d);
  }
}

static int
F2x_quad_factortype(GEN x)
{ return x[2] == 7 ? -1: x[2] == 6 ? 1 :0; }

static GEN
F2x_is_irred_2(GEN f, long d)
{ return d == 1 || (d==2 && F2x_quad_factortype(f) == -1)? gen_1: NULL; }

static GEN
F2x_degfact_2(GEN f, long d)
{
  if (!d) return trivial_fact();
  if (d == 1) return mkvec2(mkvecsmall(1), mkvecsmall(1));
  switch(F2x_quad_factortype(f)) {
    case 1: return mkvec2(mkvecsmall2(1,1), mkvecsmall2(1,1));
    case -1:return mkvec2(mkvecsmall(2), mkvecsmall(1));
    default: return mkvec2(mkvecsmall(1), mkvecsmall(2));
  }
}

static GEN
F2x_factor_2(GEN f, long d)
{
  long v = f[1];
  if (!d) return mkvec2(cgetg(1,t_COL), cgetg(1,t_VECSMALL));
  if (labs(d) == 1) return mkvec2(mkcol(f), mkvecsmall(1));
  switch(F2x_quad_factortype(f))
  {
  case -1: return mkvec2(mkcol(f), mkvecsmall(1));
  case 0:  return mkvec2(mkcol(mkvecsmall2(v,2+F2x_coeff(f,0))), mkvecsmall(2));
  default: return mkvec2(mkcol2(mkvecsmall2(v,2),mkvecsmall2(v,3)), mkvecsmall2(1,1));
  }
}
static GEN
F2x_factor_deg2(GEN f, long d, long flag)
{
  switch(flag) {
    case 2: return F2x_is_irred_2(f, d);
    case 1: return F2x_degfact_2(f, d);
    default: return F2x_factor_2(f, d);
  }
}

/* xt = NULL or x^(p-1)/2 mod g */
static void
split_squares(struct split_t *S, GEN g, ulong p, GEN xt)
{
  ulong q = p >> 1;
  GEN a = Flx_mod_Xnm1(g, q, p); /* mod x^(p-1)/2 - 1 */
  long d = degpol(a);
  if (d < 0)
  {
    ulong i;
    split_add_done(S, (GEN)1);
    for (i = 2; i <= q; i++) split_add_done(S, (GEN)Fl_sqr(i,p));
  } else {
    if (a != g) { (void)Flx_valrem(a, &a); d = degpol(a); }
    if (d)
    {
      if (xt) xt = Flx_Fl_add(xt, p-1, p); else xt = Flx_Xnm1(g[1], q, p);
      a = Flx_gcd(a, xt, p);
      if (degpol(a)) split_add(S, Flx_normalize(a, p));
    }
  }
}
static void
split_nonsquares(struct split_t *S, GEN g, ulong p, GEN xt)
{
  ulong q = p >> 1;
  GEN a = Flx_mod_Xn1(g, q, p); /* mod x^(p-1)/2 + 1 */
  long d = degpol(a);
  if (d < 0)
  {
    ulong i, z = Fl_nonsquare(p);
    split_add_done(S, (GEN)z);
    for (i = 2; i <= q; i++) split_add_done(S, (GEN)Fl_mul(z, Fl_sqr(i,p), p));
  } else {
    if (a != g) { (void)Flx_valrem(a, &a); d = degpol(a); }
    if (d)
    {
      if (xt) xt = Flx_Fl_add(xt, 1, p); else xt = Flx_Xn1(g[1], q, p);
      a = Flx_gcd(a, xt, p);
      if (degpol(a)) split_add(S, Flx_normalize(a, p));
    }
  }
}
/* p > 2. f monic Flx, f(0) != 0. Add to split_t structs coprime factors
 * of g = \prod_{f(a) = 0} (X - a). Return 0 when f(x) = 0 for all x in Fp* */
static int
split_Flx_cut_out_roots(struct split_t *S, GEN f, ulong p)
{
  GEN a, g = Flx_mod_Xnm1(f, p-1, p); /* f mod x^(p-1) - 1 */
  long d = degpol(g);
  if (d < 0) return 0;
  if (g != f) { (void)Flx_valrem(g, &g); d = degpol(g); } /*kill powers of x*/
  if (!d) return 1;
  if ((p >> 4) <= (ulong)d)
  { /* small p; split directly using x^((p-1)/2) +/- 1 */
    GEN xt = ((ulong)d < (p>>1))? Flx_rem(monomial_Flx(1, p>>1, g[1]), g, p)
                                : NULL;
    split_squares(S, g, p, xt);
    split_nonsquares(S, g, p, xt);
  } else { /* large p; use x^(p-1) - 1 directly */
    a = Flxq_powu(polx_Flx(f[1]), p-1, g,p);
    if (lg(a) < 3) pari_err_PRIME("rootmod",utoipos(p));
    a = Flx_Fl_add(a, p-1, p); /* a = x^(p-1) - 1 mod g */
    g = Flx_gcd(g,a, p);
    if (degpol(g)) split_add(S, Flx_normalize(g,p));
  }
  return 1;
}

/* by splitting, assume p > 2 prime, deg(f) > 0, and f monic */
static GEN
Flx_roots_i(GEN f, ulong p)
{
  GEN pol, g;
  long v = Flx_valrem(f, &g);
  ulong q;
  struct split_t S;

  /* optimization: test for small degree first */
  switch(degpol(g))
  {
    case 1: {
      ulong r = p - g[2];
      return v? mkvecsmall2(0, r): mkvecsmall(r);
    }
    case 2: {
      ulong r = Flx_quad_root(g, p, 1), s;
      if (r == p) return v? mkvecsmall(0): cgetg(1,t_VECSMALL);
      s = Flx_otherroot(g,r, p);
      if (r < s)
        return v? mkvecsmall3(0, r, s): mkvecsmall2(r, s);
      else if (r > s)
        return v? mkvecsmall3(0, s, r): mkvecsmall2(s, r);
      else
        return v? mkvecsmall2(0, s): mkvecsmall(s);
    }
  }
  q = p >> 1;
  split_init(&S, lg(f)-1);
  settyp(S.done, t_VECSMALL);
  if (v) split_add_done(&S, (GEN)0);
  if (! split_Flx_cut_out_roots(&S, g, p))
    return all_roots_mod_p(p, lg(S.done) == 1);
  pol = polx_Flx(f[1]);
  for (pol[2]=1; ; pol[2]++)
  {
    long j, l = lg(S.todo);
    if (l == 1) { vecsmall_sort(S.done); return S.done; }
    if (pol[2] == 100 && !uisprime(p)) pari_err_PRIME("polrootsmod",utoipos(p));
    for (j = 1; j < l; j++)
    {
      GEN b, c = gel(S.todo,j);
      ulong r, s;
      switch(degpol(c))
      {
        case 1:
          split_moveto_done(&S, j, (GEN)(p - c[2]));
          j--; l--; break;
        case 2:
          r = Flx_quad_root(c, p, 0);
          if (r == p) pari_err_PRIME("polrootsmod",utoipos(p));
          s = Flx_otherroot(c,r, p);
          split_done(&S, j, (GEN)r, (GEN)s);
          j--; l--; break;
        default:
          b = Flxq_powu(pol,q, c,p); /* pol^(p-1)/2 */
          if (degpol(b) <= 0) continue;
          b = Flx_gcd(c,Flx_Fl_add(b,p-1,p), p);
          if (!degpol(b)) continue;
          b = Flx_normalize(b, p);
          c = Flx_div(c,b, p);
          split_todo(&S, j, b, c);
      }
    }
  }
}

GEN
Flx_roots(GEN f, ulong p)
{
  pari_sp av = avma;
  switch(lg(f))
  {
    case 2: pari_err_ROOTS0("Flx_roots");
    case 3: avma = av; return cgetg(1, t_VECSMALL);
  }
  if (p == 2) return Flx_root_mod_2(f);
  return gerepileuptoleaf(av, Flx_roots_i(Flx_normalize(f, p), p));
}

/* assume x reduced mod p, monic. */
static int
Flx_quad_factortype(GEN x, ulong p)
{
  ulong b = x[3], c = x[2];
  return krouu(Fl_disc_bc(b, c, p), p);
}
static GEN
Flx_is_irred_2(GEN f, ulong p, long d)
{
  if (!d) return NULL;
  if (d == 1) return gen_1;
  return Flx_quad_factortype(f, p) == -1? gen_1: NULL;
}
static GEN
Flx_degfact_2(GEN f, ulong p, long d)
{
  if (!d) return trivial_fact();
  if (d == 1) return mkvec2(mkvecsmall(1), mkvecsmall(1));
  switch(Flx_quad_factortype(f, p)) {
    case 1: return mkvec2(mkvecsmall2(1,1), mkvecsmall2(1,1));
    case -1:return mkvec2(mkvecsmall(2), mkvecsmall(1));
    default: return mkvec2(mkvecsmall(1), mkvecsmall(2));
  }
}
/* p > 2 */
static GEN
Flx_factor_2(GEN f, ulong p, long d)
{
  ulong r, s;
  GEN R,S;
  long v = f[1];
  if (!d) return mkvec2(cgetg(1,t_COL), cgetg(1,t_VECSMALL));
  if (labs(d) == 1) return mkvec2(mkcol(f), mkvecsmall(1));
  r = Flx_quad_root(f, p, 1);
  if (r==p) return mkvec2(mkcol(f), mkvecsmall(1));
  s = Flx_otherroot(f, r, p);
  r = Fl_neg(r, p);
  s = Fl_neg(s, p);
  if (s < r) lswap(s,r);
  R = mkvecsmall3(v,r,1);
  if (s == r) return mkvec2(mkcol(R), mkvecsmall(2));
  S = mkvecsmall3(v,s,1);
  return mkvec2(mkcol2(R,S), mkvecsmall2(1,1));
}
static GEN
Flx_factor_deg2(GEN f, ulong p, long d, long flag)
{
  switch(flag) {
    case 2: return Flx_is_irred_2(f, p, d);
    case 1: return Flx_degfact_2(f, p, d);
    default: return Flx_factor_2(f, p, d);
  }
}

void
F2xV_to_FlxV_inplace(GEN v)
{
  long i;
  for(i=1;i<lg(v);i++) gel(v,i)= F2x_to_Flx(gel(v,i));
}
void
FlxV_to_ZXV_inplace(GEN v)
{
  long i;
  for(i=1;i<lg(v);i++) gel(v,i)= Flx_to_ZX(gel(v,i));
}
void
F2xV_to_ZXV_inplace(GEN v)
{
  long i;
  for(i=1;i<lg(v);i++) gel(v,i)= F2x_to_ZX(gel(v,i));
}

static GEN
F2x_Berlekamp_ker(GEN u)
{
  pari_sp ltop=avma;
  long j,N = F2x_degree(u);
  GEN Q;
  pari_timer T;
  timer_start(&T);
  Q = F2x_matFrobenius(u);
  for (j=1; j<=N; j++)
    F2m_flip(Q,j,j);
  if(DEBUGLEVEL>=9) timer_printf(&T,"Berlekamp matrix");
  Q = F2m_ker_sp(Q,0);
  if(DEBUGLEVEL>=9) timer_printf(&T,"kernel");
  return gerepileupto(ltop,Q);
}
#define set_irred(i) { if ((i)>ir) swap(t[i],t[ir]); ir++;}
static long
F2x_split_Berlekamp(GEN *t)
{
  GEN u = *t, a, b, vker;
  long lb, d, i, ir, L, la, sv = u[1], du = F2x_degree(u);

  if (du == 1) return 1;
  if (du == 2)
  {
    if (F2x_quad_factortype(u) == 1) /* 0 is a root: shouldn't occur */
    {
      t[0] = mkvecsmall2(sv, 2);
      t[1] = mkvecsmall2(sv, 3);
      return 2;
    }
    return 1;
  }

  vker = F2x_Berlekamp_ker(u);
  lb = lgcols(vker);
  d = lg(vker)-1;
  ir = 0;
  /* t[i] irreducible for i < ir, still to be treated for i < L */
  for (L=1; L<d; )
  {
    GEN pol;
    if (d == 2)
      pol = F2v_to_F2x(gel(vker,2), sv);
    else
    {
      GEN v = zero_zv(lb);
      v[1] = du;
      v[2] = random_Fl(2); /*Assume vker[1]=1*/
      for (i=2; i<=d; i++)
        if (random_Fl(2)) F2v_add_inplace(v, gel(vker,i));
      pol = F2v_to_F2x(v, sv);
    }
    for (i=ir; i<L && L<d; i++)
    {
      a = t[i]; la = F2x_degree(a);
      if (la == 1) { set_irred(i); }
      else if (la == 2)
      {
        if (F2x_quad_factortype(a) == 1) /* 0 is a root: shouldn't occur */
        {
          t[i] = mkvecsmall2(sv, 2);
          t[L] = mkvecsmall2(sv, 3); L++;
        }
        set_irred(i);
      }
      else
      {
        pari_sp av = avma;
        long lb;
        b = F2x_rem(pol, a);
        if (F2x_degree(b) <= 0) { avma=av; continue; }
        b = F2x_gcd(a,b); lb = F2x_degree(b);
        if (lb && lb < la)
        {
          t[L] = F2x_div(a,b);
          t[i]= b; L++;
        }
        else avma = av;
      }
    }
  }
  return d;
}
/* assume deg f > 2 */
static GEN
F2x_Berlekamp_i(GEN f, long flag)
{
  long lfact, val, d = F2x_degree(f), j, k, lV;
  GEN y, E, t, V;

  val = F2x_valrem(f, &f);
  if (flag == 2 && val) return NULL;
  V = F2x_factor_squarefree(f); lV = lg(V);
  if (flag == 2 && lV > 2) return NULL;

  /* to hold factors and exponents */
  t = cgetg(d+1, flag? t_VECSMALL: t_VEC);
  E = cgetg(d+1,t_VECSMALL);
  lfact = 1;
  if (val) {
    if (flag == 1) t[1] = 1; else gel(t,1) = polx_F2x(f[1]);
    E[1] = val; lfact++;
  }

  for (k=1; k<lV; k++)
  {
    if (F2x_degree(gel(V, k))==0) continue;
    gel(t,lfact) = gel(V, k);
    d = F2x_split_Berlekamp(&gel(t,lfact));
    if (flag == 2 && d != 1) return NULL;
    if (flag == 1)
      for (j=0; j<d; j++) t[lfact+j] = F2x_degree(gel(t,lfact+j));
    for (j=0; j<d; j++) E[lfact+j] = k;
    lfact += d;
  }
  if (flag == 2) return gen_1; /* irreducible */
  setlg(t, lfact);
  setlg(E, lfact); y = mkvec2(t,E);
  return flag ? sort_factor(y, (void*)&cmpGuGu, cmp_nodata)
              : sort_factor_pol(y, cmpGuGu);
}

/* Adapted from Shoup NTL */
GEN
F2x_factor_squarefree(GEN f)
{
  GEN r, t, v, tv;
  long i, q, n = F2x_degree(f);
  GEN u = const_vec(n+1, pol1_F2x(f[1]));
  for(q = 1;;q *= 2)
  {
    r = F2x_gcd(f, F2x_deriv(f));
    if (F2x_degree(r) == 0)
    {
      gel(u, q) = f;
      break;
    }
    t = F2x_div(f, r);
    if (F2x_degree(t) > 0)
    {
      long j;
      for(j = 1;;j++)
      {
        v = F2x_gcd(r, t);
        tv = F2x_div(t, v);
        if (F2x_degree(tv) > 0)
          gel(u, j*q) = tv;
        if (F2x_degree(v) <= 0) break;
        r = F2x_div(r, v);
        t = v;
      }
      if (F2x_degree(r) == 0) break;
    }
    f = F2x_sqrt(r);
  }
  for (i = n; i; i--)
    if (F2x_degree(gel(u,i))) break;
  setlg(u,i+1); return u;
}

static GEN
F2x_ddf_simple(GEN T, GEN XP)
{
  pari_sp av = avma, av2;
  GEN f, z, Tr, X;
  long j, n = F2x_degree(T), v = T[1], B = n/2;
  if (n == 0) return cgetg(1, t_VEC);
  if (n == 1) return mkvec(T);
  z = XP; Tr = T; X = polx_F2x(v);
  f = const_vec(n, pol1_F2x(v));
  av2 = avma;
  for (j = 1; j <= B; j++)
  {
    GEN u = F2x_gcd(Tr, F2x_add(z, X));
    if (F2x_degree(u))
    {
      gel(f, j) = u;
      Tr = F2x_div(Tr, u);
      av2 = avma;
    } else z = gerepileuptoleaf(av2, z);
    if (!F2x_degree(Tr)) break;
    z = F2xq_sqr(z, Tr);
  }
  if (F2x_degree(Tr)) gel(f, F2x_degree(Tr)) = Tr;
  return gerepilecopy(av, f);
}

GEN
F2x_ddf(GEN T)
{
  GEN XP;
  T = F2x_get_red(T);
  XP = F2x_Frobenius(T);
  return F2x_ddf_to_ddf2(F2x_ddf_simple(T, XP));
}

static GEN
F2xq_frobtrace(GEN a, long d, GEN T)
{
  pari_sp av = avma;
  long i;
  GEN x = a;
  for(i=1; i<d; i++)
  {
    x = F2x_add(a, F2xq_sqr(x,T));
    if (gc_needed(av, 2))
      x = gerepileuptoleaf(av, x);
  }
  return x;
}

static void
F2x_edf_simple(GEN Tp, GEN XP, long d, GEN V, long idx)
{
  long n = F2x_degree(Tp), r = n/d;
  GEN T, f, ff;
  if (r==1) { gel(V, idx) = Tp; return; }
  T = Tp;
  XP = F2x_rem(XP, T);
  while (1)
  {
    pari_sp btop = avma;
    long df;
    GEN g = random_F2x(n, Tp[1]);
    GEN t = F2xq_frobtrace(g, d, T);
    if (lgpol(t) == 0) continue;
    f = F2x_gcd(t, Tp); df = F2x_degree(f);
    if (df > 0 && df < n) break;
    avma = btop;
  }
  ff = F2x_div(Tp, f);
  F2x_edf_simple(f, XP, d, V, idx);
  F2x_edf_simple(ff, XP, d, V, idx+F2x_degree(f)/d);
}

static GEN
F2x_factor_Shoup(GEN T)
{
  long i, n, s = 0;
  GEN XP, D, V;
  pari_timer ti;
  n = F2x_degree(T);
  if (DEBUGLEVEL>=6) timer_start(&ti);
  XP = F2x_Frobenius(T);
  if (DEBUGLEVEL>=6) timer_printf(&ti,"F2x_Frobenius");
  D = F2x_ddf_simple(T, XP);
  if (DEBUGLEVEL>=6) timer_printf(&ti,"F2x_ddf_simple");
  for (i = 1; i <= n; i++)
    s += F2x_degree(gel(D,i))/i;
  V = cgetg(s+1, t_COL);
  for (i = 1, s = 1; i <= n; i++)
  {
    GEN Di = gel(D,i);
    long ni = F2x_degree(Di), ri = ni/i;
    if (ni == 0) continue;
    if (ni == i) { gel(V, s++) = Di; continue; }
    F2x_edf_simple(Di, XP, i, V, s);
    if (DEBUGLEVEL>=6) timer_printf(&ti,"F2x_edf(%ld)",i);
    s += ri;
  }
  return V;
}

static GEN
F2x_factor_Cantor(GEN T)
{
  GEN E, F, V = F2x_factor_squarefree(T);
  long i, j, l = lg(V);
  E = cgetg(l, t_VEC);
  F = cgetg(l, t_VEC);
  for (i=1, j=1; i < l; i++)
    if (F2x_degree(gel(V,i)))
    {
      GEN Fj = F2x_factor_Shoup(gel(V,i));
      gel(F, j) = Fj;
      gel(E, j) = const_vecsmall(lg(Fj)-1, i);
      j++;
    }
  return sort_factor_pol(FE_concat(F,E,j), cmpGuGu);
}

#if 0
static GEN
F2x_simplefact_Shoup(GEN T)
{
  long i, n, s = 0, j = 1, k;
  GEN XP, D, V;
  pari_timer ti;
  n = F2x_degree(T);
  if (DEBUGLEVEL>=6) timer_start(&ti);
  XP = F2x_Frobenius(T);
  if (DEBUGLEVEL>=6) timer_printf(&ti,"F2x_Frobenius");
  D = F2x_ddf_simple(T, XP);
  if (DEBUGLEVEL>=6) timer_printf(&ti,"F2x_ddf_simple");
  for (i = 1; i <= n; i++)
    s += F2x_degree(gel(D,i))/i;
  V = cgetg(s+1, t_VECSMALL);
  for (i = 1; i <= n; i++)
  {
    long ni = F2x_degree(gel(D,i)), ri = ni/i;
    if (ni == 0) continue;
    for (k = 1; k <= ri; k++)
      V[j++] = i;
  }
  return V;
}
static GEN
F2x_simplefact_Cantor(GEN T)
{
  GEN E, F, V = F2x_factor_squarefree(T);
  long i, j, l = lg(V);
  F = cgetg(l, t_VEC);
  E = cgetg(l, t_VEC);
  for (i=1, j=1; i < l; i++)
    if (F2x_degree(gel(V,i)))
    {
      GEN Fj = F2x_simplefact_Shoup(gel(V,i));
      gel(F, j) = Fj;
      gel(E, j) = const_vecsmall(lg(Fj)-1, i);
      j++;
    }
  return sort_factor(FE_concat(F,E,j), (void*)&cmpGuGu, cmp_nodata);
}
static int
F2x_isirred_Cantor(GEN T)
{
  pari_sp av = avma;
  pari_timer ti;
  long n, d;
  GEN dT = F2x_deriv(T);
  GEN XP, D;
  if (F2x_degree(F2x_gcd(T, dT)) != 0) { avma = av; return 0; }
  n = F2x_degree(T);
  if (DEBUGLEVEL>=6) timer_start(&ti);
  XP = F2x_Frobenius(T);
  if (DEBUGLEVEL>=6) timer_printf(&ti,"F2x_Frobenius");
  D = F2x_ddf_simple(T, XP);
  if (DEBUGLEVEL>=6) timer_printf(&ti,"F2x_ddf_simple");
  d = F2x_degree(gel(D, n));
  avma = av; return d==n;
}
#endif

/* driver for Cantor factorization, assume deg f > 2; not competitive for
 * flag != 0, or as deg f increases */
static GEN
F2x_Cantor_i(GEN f, long flag)
{
  switch(flag)
  {
    default: return F2x_factor_Cantor(f);
#if 0
    case 1: return F2x_simplefact_Cantor(f);
    case 2: return F2x_isirred_Cantor(f)? gen_1: NULL;
#endif
  }
}
static GEN
F2x_factor_i(GEN f, long flag)
{
  long d = F2x_degree(f);
  if (d <= 2) return F2x_factor_deg2(f,d,flag);
  return (flag == 0 && d <= 20)? F2x_Cantor_i(f, flag)
                               : F2x_Berlekamp_i(f, flag);
}

GEN
F2x_degfact(GEN f)
{
  pari_sp av = avma;
  GEN z = F2x_factor_i(f, 1);
  return gerepilecopy(av, z);
}

int
F2x_is_irred(GEN f) { return !!F2x_factor_i(f, 2); }

/* Adapted from Shoup NTL */
GEN
Flx_factor_squarefree(GEN f, ulong p)
{
  long i, q, n = degpol(f);
  GEN u = const_vec(n+1, pol1_Flx(f[1]));
  for(q = 1;;q *= p)
  {
    GEN t, v, tv, r = Flx_gcd(f, Flx_deriv(f, p), p);
    if (degpol(r) == 0) { gel(u, q) = f; break; }
    t = Flx_div(f, r, p);
    if (degpol(t) > 0)
    {
      long j;
      for(j = 1;;j++)
      {
        v = Flx_gcd(r, t, p);
        tv = Flx_div(t, v, p);
        if (degpol(tv) > 0)
          gel(u, j*q) = Flx_normalize(tv, p);
        if (degpol(v) <= 0) break;
        r = Flx_div(r, v, p);
        t = v;
      }
      if (degpol(r) == 0) break;
    }
    f = Flx_normalize(Flx_deflate(r, p), p);
  }
  for (i = n; i; i--)
    if (degpol(gel(u,i))) break;
  setlg(u,i+1); return u;
}

long
Flx_ispower(GEN f, ulong k, ulong p, GEN *pt_r)
{
  pari_sp av = avma;
  ulong lc;
  GEN F;
  long i, n = degpol(f), v = f[1], l;
  if (n % k) return 0;
  lc = Fl_sqrtn(Flx_lead(f), k, p, NULL);
  if (lc == ULONG_MAX) { av = avma; return 0; }
  F = Flx_factor_squarefree(f, p); l = lg(F)-1;
  for (i = 1; i <= l; i++)
    if (i%k && degpol(gel(F,i))) { avma = av; return 0; }
  if (pt_r)
  {
    GEN r = Fl_to_Flx(lc, v), s = pol1_Flx(v);
    for(i = l; i >= 1; i--)
    {
      if (i%k) continue;
      s = Flx_mul(s, gel(F,i), p);
      r = Flx_mul(r, s, p);
    }
    *pt_r = gerepileuptoleaf(av, r);
  } else av = avma;
  return 1;
}

/* See <http://www.shoup.net/papers/factorimpl.pdf> */
static GEN
Flx_ddf_Shoup(GEN T, GEN XP, ulong p)
{
  pari_sp av = avma;
  GEN b, g, h, F, f, Tr, xq;
  long i, j, n, v, bo, ro;
  long B, l, m;
  pari_timer ti;
  n = get_Flx_degree(T); v = get_Flx_var(T);
  if (n == 0) return cgetg(1, t_VEC);
  if (n == 1) return mkvec(get_Flx_mod(T));
  B = n/2;
  l = usqrt(B);
  m = (B+l-1)/l;
  T = Flx_get_red(T, p);
  b = cgetg(l+2, t_VEC);
  gel(b, 1) = polx_Flx(v);
  gel(b, 2) = XP;
  bo = brent_kung_optpow(n, l-1, 1);
  ro = l<=1 ? 0:(bo-1)/(l-1) + ((n-1)/bo);
  if (DEBUGLEVEL>=7) timer_start(&ti);
  if (expu(p) <= ro)
    for (i = 3; i <= l+1; i++)
      gel(b, i) = Flxq_powu(gel(b, i-1), p, T, p);
  else
  {
    xq = Flxq_powers(gel(b, 2), bo,  T, p);
    if (DEBUGLEVEL>=7) timer_printf(&ti,"Flx_ddf_Shoup: xq baby");
    for (i = 3; i <= l+1; i++)
      gel(b, i) = Flx_FlxqV_eval(gel(b, i-1), xq, T, p);
  }
  if (DEBUGLEVEL>=7) timer_printf(&ti,"Flx_ddf_Shoup: baby");
  xq = Flxq_powers(gel(b, l+1), brent_kung_optpow(n, m-1, 1),  T, p);
  if (DEBUGLEVEL>=7) timer_printf(&ti,"Flx_ddf_Shoup: xq giant");
  g = cgetg(m+1, t_VEC);
  gel(g, 1) = gel(xq, 2);
  for(i = 2; i <= m; i++)
    gel(g, i) = Flx_FlxqV_eval(gel(g, i-1), xq, T, p);
  if (DEBUGLEVEL>=7) timer_printf(&ti,"Flx_ddf_Shoup: giant");
  h = cgetg(m+1, t_VEC);
  for (j = 1; j <= m; j++)
  {
    pari_sp av = avma;
    GEN gj = gel(g, j);
    GEN e = Flx_sub(gj, gel(b, 1), p);
    for (i = 2; i <= l; i++)
      e = Flxq_mul(e, Flx_sub(gj, gel(b, i), p), T, p);
    gel(h, j) = gerepileupto(av, e);
  }
  if (DEBUGLEVEL>=7) timer_printf(&ti,"Flx_ddf_Shoup: diff");
  Tr = get_Flx_mod(T);
  F = cgetg(m+1, t_VEC);
  for (j = 1; j <= m; j++)
  {
    GEN u = Flx_gcd(Tr, gel(h, j), p);
    if (degpol(u))
    {
      u = Flx_normalize(u, p);
      Tr = Flx_div(Tr, u, p);
    }
    gel(F, j) = u;
  }
  if (DEBUGLEVEL>=7) timer_printf(&ti,"Flx_ddf_Shoup: F");
  f = const_vec(n, pol1_Flx(v));
  for (j = 1; j <= m; j++)
  {
    GEN e = gel(F, j);
    for (i=l-1; i >= 0; i--)
    {
      GEN u = Flx_gcd(e, Flx_sub(gel(g, j), gel(b, i+1), p), p);
      if (degpol(u))
      {
        gel(f, l*j-i) = u;
        e = Flx_div(e, u, p);
      }
      if (!degpol(e)) break;
    }
  }
  if (DEBUGLEVEL>=7) timer_printf(&ti,"Flx_ddf_Shoup: f");
  if (degpol(Tr)) gel(f, degpol(Tr)) = Tr;
  return gerepilecopy(av, f);
}

static void
Flx_edf_simple(GEN Tp, GEN XP, long d, ulong p, GEN V, long idx)
{
  long n = degpol(Tp), r = n/d;
  GEN T, f, ff;
  ulong p2;
  if (r==1) { gel(V, idx) = Tp; return; }
  p2 = p>>1;
  T = Flx_get_red(Tp, p);
  XP = Flx_rem(XP, T, p);
  while (1)
  {
    pari_sp btop = avma;
    long i;
    GEN g = random_Flx(n, Tp[1], p);
    GEN t = gel(Flxq_auttrace(mkvec2(XP, g), d, T, p), 2);
    if (lgpol(t) == 0) continue;
    for(i=1; i<=10; i++)
    {
      pari_sp btop2 = avma;
      GEN R = Flxq_powu(Flx_Fl_add(t, random_Fl(p), p), p2, T, p);
      f = Flx_gcd(Flx_Fl_add(R, p-1, p), Tp, p);
      if (degpol(f) > 0 && degpol(f) < n) break;
      avma = btop2;
    }
    if (degpol(f) > 0 && degpol(f) < n) break;
    avma = btop;
  }
  f = Flx_normalize(f, p);
  ff = Flx_div(Tp, f ,p);
  Flx_edf_simple(f, XP, d, p, V, idx);
  Flx_edf_simple(ff, XP, d, p, V, idx+degpol(f)/d);
}
static void
Flx_edf(GEN Tp, GEN XP, long d, ulong p, GEN V, long idx);

static void
Flx_edf_rec(GEN T, GEN XP, GEN hp, GEN t, long d, ulong p, GEN V, long idx)
{
  pari_sp av;
  GEN Tp = get_Flx_mod(T);
  long n = degpol(hp), vT = Tp[1];
  GEN u1, u2, f1, f2;
  ulong p2 = p>>1;
  GEN R, h;
  h = Flx_get_red(hp, p);
  t = Flx_rem(t, T, p);
  av = avma;
  do
  {
    avma = av;
    R = Flxq_powu(mkvecsmall3(vT, random_Fl(p), 1), p2, h, p);
    u1 = Flx_gcd(Flx_Fl_add(R, p-1, p), hp, p);
  } while (degpol(u1)==0 || degpol(u1)==n);
  f1 = Flx_gcd(Flx_Flxq_eval(u1, t, T, p), Tp, p);
  f1 = Flx_normalize(f1, p);
  u2 = Flx_div(hp, u1, p);
  f2 = Flx_div(Tp, f1, p);
  if (degpol(u1)==1)
  {
    if (degpol(f1)==d)
      gel(V, idx) = f1;
    else
      Flx_edf(f1, XP, d, p, V, idx);
  }
  else
    Flx_edf_rec(Flx_get_red(f1, p), XP, u1, t, d, p, V, idx);
  idx += degpol(f1)/d;
  if (degpol(u2)==1)
  {
    if (degpol(f2)==d)
      gel(V, idx) = f2;
    else
      Flx_edf(f2, XP, d, p, V, idx);
  }
  else
    Flx_edf_rec(Flx_get_red(f2, p), XP, u2, t, d, p, V, idx);
}

static void
Flx_edf(GEN Tp, GEN XP, long d, ulong p, GEN V, long idx)
{
  long n = degpol(Tp), r = n/d, vT = Tp[1];
  GEN T, h, t;
  pari_timer ti;
  if (r==1) { gel(V, idx) = Tp; return; }
  T = Flx_get_red(Tp, p);
  XP = Flx_rem(XP, T, p);
  if (DEBUGLEVEL>=7) timer_start(&ti);
  do
  {
    GEN g = random_Flx(n, vT, p);
    t = gel(Flxq_auttrace(mkvec2(XP, g), d, T, p), 2);
    if (DEBUGLEVEL>=7) timer_printf(&ti,"Flx_edf: Flxq_auttrace");
    h = Flxq_minpoly(t, T, p);
    if (DEBUGLEVEL>=7) timer_printf(&ti,"Flx_edf: Flxq_minpoly");
  } while (degpol(h) <= 1);
  Flx_edf_rec(T, XP, h, t, d, p, V, idx);
}

static GEN
Flx_factor_Shoup(GEN T, ulong p)
{
  long i, n, s = 0;
  GEN XP, D, V;
  long e = expu(p);
  pari_timer ti;
  n = get_Flx_degree(T);
  T = Flx_get_red(T, p);
  if (DEBUGLEVEL>=6) timer_start(&ti);
  XP = Flx_Frobenius(T, p);
  if (DEBUGLEVEL>=6) timer_printf(&ti,"Flx_Frobenius");
  D = Flx_ddf_Shoup(T, XP, p);
  if (DEBUGLEVEL>=6) timer_printf(&ti,"Flx_ddf_Shoup");
  s = ddf_to_nbfact(D);
  V = cgetg(s+1, t_COL);
  for (i = 1, s = 1; i <= n; i++)
  {
    GEN Di = gel(D,i);
    long ni = degpol(Di), ri = ni/i;
    if (ni == 0) continue;
    Di = Flx_normalize(Di, p);
    if (ni == i) { gel(V, s++) = Di; continue; }
    if (ri <= e*expu(e))
      Flx_edf(Di, XP, i, p, V, s);
    else
      Flx_edf_simple(Di, XP, i, p, V, s);
    if (DEBUGLEVEL>=6) timer_printf(&ti,"Flx_edf(%ld)",i);
    s += ri;
  }
  return V;
}

static GEN
Flx_factor_Cantor(GEN T, ulong p)
{
  GEN E, F, V = Flx_factor_squarefree(get_Flx_mod(T), p);
  long i, j, l = lg(V);
  F = cgetg(l, t_VEC);
  E = cgetg(l, t_VEC);
  for (i=1, j=1; i < l; i++)
    if (degpol(gel(V,i)))
    {
      GEN Fj = Flx_factor_Shoup(gel(V,i), p);
      gel(F, j) = Fj;
      gel(E, j) = const_vecsmall(lg(Fj)-1, i);
      j++;
    }
  return sort_factor_pol(FE_concat(F,E,j), cmpGuGu);
}

GEN
Flx_ddf(GEN T, ulong p)
{
  GEN XP;
  T = Flx_get_red(T, p);
  XP = Flx_Frobenius(T, p);
  return ddf_to_ddf2(Flx_ddf_Shoup(T, XP, p));
}

static GEN
Flx_simplefact_Cantor(GEN T, ulong p)
{
  GEN XP, V;
  long i, l;
  T = Flx_get_red(T, p);
  XP = Flx_Frobenius(T, p);
  V = Flx_factor_squarefree(get_Flx_mod(T), p); l = lg(V);
  for (i=1; i < l; i++) gel(V,i) = Flx_ddf_Shoup(gel(V,i), XP, p);
  return vddf_to_simplefact(V, get_Flx_degree(T));
}

static int
Flx_isirred_Cantor(GEN Tp, ulong p)
{
  pari_sp av = avma;
  pari_timer ti;
  long n, d;
  GEN T = get_Flx_mod(Tp);
  GEN dT = Flx_deriv(T, p);
  GEN XP, D;
  if (degpol(Flx_gcd(T, dT, p)) != 0) { avma = av; return 0; }
  n = get_Flx_degree(T);
  T = Flx_get_red(Tp, p);
  if (DEBUGLEVEL>=6) timer_start(&ti);
  XP = Flx_Frobenius(T, p);
  if (DEBUGLEVEL>=6) timer_printf(&ti,"Flx_Frobenius");
  D = Flx_ddf_Shoup(T, XP, p);
  if (DEBUGLEVEL>=6) timer_printf(&ti,"Flx_ddf_Shoup");
  d = degpol(gel(D, n));
  avma = av; return d==n;
}

/* f monic */
static GEN
Flx_factor_i(GEN f, ulong pp, long flag)
{
  long d;
  if (pp==2) { /*We need to handle 2 specially */
    GEN F = F2x_factor_i(Flx_to_F2x(f),flag);
    if (flag==0) F2xV_to_FlxV_inplace(gel(F,1));
    return F;
  }
  d = degpol(f);
  if (d <= 2) return Flx_factor_deg2(f,pp,d,flag);
  switch(flag)
  {
    default: return Flx_factor_Cantor(f, pp);
    case 1: return Flx_simplefact_Cantor(f, pp);
    case 2: return Flx_isirred_Cantor(f, pp)? gen_1: NULL;
  }
}

GEN
Flx_degfact(GEN f, ulong p)
{
  pari_sp av = avma;
  GEN z = Flx_factor_i(Flx_normalize(f,p),p,1);
  return gerepilecopy(av, z);
}

/* T must be squarefree mod p*/
GEN
Flx_nbfact_by_degree(GEN T, long *nb, ulong p)
{
  GEN XP, D;
  pari_timer ti;
  long i, s, n = get_Flx_degree(T);
  GEN V = const_vecsmall(n, 0);
  pari_sp av = avma;
  T = Flx_get_red(T, p);
  if (DEBUGLEVEL>=6) timer_start(&ti);
  XP = Flx_Frobenius(T, p);
  if (DEBUGLEVEL>=6) timer_printf(&ti,"Flx_Frobenius");
  D = Flx_ddf_Shoup(T, XP, p);
  if (DEBUGLEVEL>=6) timer_printf(&ti,"Flx_ddf_Shoup");
  for (i = 1, s = 0; i <= n; i++)
  {
    V[i] = degpol(gel(D,i))/i;
    s += V[i];
  }
  *nb = s;
  avma = av; return V;
}

long
Flx_nbfact_Frobenius(GEN T, GEN XP, ulong p)
{
  pari_sp av = avma;
  long s = ddf_to_nbfact(Flx_ddf_Shoup(T, XP, p));
  avma = av; return s;
}

/* T must be squarefree mod p*/
long
Flx_nbfact(GEN T, ulong p)
{
  pari_sp av = avma;
  GEN XP = Flx_Frobenius(T, p);
  long n = Flx_nbfact_Frobenius(T, XP, p);
  avma = av; return n;
}

int
Flx_is_irred(GEN f, ulong p)
{
  pari_sp av = avma;
  int z = !!Flx_factor_i(Flx_normalize(f,p),p,2);
  avma = av; return z;
}

/* Use this function when you think f is reducible, and that there are lots of
 * factors. If you believe f has few factors, use FpX_nbfact(f,p)==1 instead */
int
FpX_is_irred(GEN f, GEN p)
{
  pari_sp av = avma;
  int z;
  switch(ZX_factmod_init(&f,p))
  {
    case 0:  z = !!F2x_factor_i(f,2); break;
    case 1:  z = !!Flx_factor_i(f,p[2],2); break;
    default: z = !!FpX_factor_i(f,p,2); break;
  }
  avma = av; return z;
}
GEN
FpX_degfact(GEN f, GEN p) {
  pari_sp av = avma;
  GEN F;
  switch(ZX_factmod_init(&f,p))
  {
    case 0:  F = F2x_factor_i(f,1); break;
    case 1:  F = Flx_factor_i(f,p[2],1); break;
    default: F = FpX_factor_i(f,p,1); break;
  }
  return gerepilecopy(av, F);
}

#if 0
/* set x <-- x + c*y mod p */
/* x is not required to be normalized.*/
static void
Flx_addmul_inplace(GEN gx, GEN gy, ulong c, ulong p)
{
  long i, lx, ly;
  ulong *x=(ulong *)gx;
  ulong *y=(ulong *)gy;
  if (!c) return;
  lx = lg(gx);
  ly = lg(gy);
  if (lx<ly) pari_err_BUG("lx<ly in Flx_addmul_inplace");
  if (SMALL_ULONG(p))
    for (i=2; i<ly;  i++) x[i] = (x[i] + c*y[i]) % p;
  else
    for (i=2; i<ly;  i++) x[i] = Fl_add(x[i], Fl_mul(c,y[i],p),p);
}
#endif

GEN
FpX_factor(GEN f, GEN p)
{
  pari_sp av = avma;
  GEN F;
  switch(ZX_factmod_init(&f, p))
  {
    case 0:  F = F2x_factor_i(f,0);
             F2xV_to_ZXV_inplace(gel(F,1)); break;
    case 1:  F = Flx_factor_i(f,p[2],0);
             FlxV_to_ZXV_inplace(gel(F,1)); break;
    default: F = FpX_factor_i(f,p,0); break;
  }
  return gerepilecopy(av, F);
}

GEN
Flx_factor(GEN f, ulong p)
{
  pari_sp av = avma;
  return gerepilecopy(av, Flx_factor_i(Flx_normalize(f,p),p,0));
}
GEN
F2x_factor(GEN f)
{
  pari_sp av = avma;
  return gerepilecopy(av, F2x_factor_i(f,0));
}
