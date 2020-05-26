/* Copyright (C) 2000  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/********************************************************************/
/**                                                                **/
/**                      GENERIC OPERATIONS                        **/
/**                         (first part)                           **/
/**                                                                **/
/********************************************************************/
#include "pari.h"
#include "paripriv.h"

/* assume z[1] was created last */
#define fix_frac_if_int(z) if (equali1(gel(z,2)))\
  z = gerepileupto((pari_sp)(z+3), gel(z,1));

/* assume z[1] was created last */
#define fix_frac_if_int_GC(z,tetpil) { if (equali1(gel(z,2)))\
  z = gerepileupto((pari_sp)(z+3), gel(z,1));\
else\
  gerepilecoeffssp((pari_sp)z, tetpil, z+1, 2); }

static void
warn_coercion(GEN x, GEN y, GEN z)
{
  if (DEBUGLEVEL)
   pari_warn(warner,"coercing quotient rings; moduli %Ps and %Ps -> %Ps",x,y,z);
}

static long
kro_quad(GEN x, GEN y)
{
  pari_sp av=avma;
  long k = kronecker(quad_disc(x), y);
  avma = av; return k;
}

/* is -1 not a square in Zp, assume p prime */
INLINE int
Zp_nosquare_m1(GEN p) { return (mod4(p) & 2); /* 2 or 3 mod 4 */ }

static GEN addsub_pp(GEN x, GEN y, GEN(*op)(GEN,GEN));
static GEN addsub_frac(GEN x, GEN y, GEN (*op)(GEN,GEN));
static GEN mulpp(GEN x, GEN y);
static GEN divpp(GEN x, GEN y);
/* Argument codes for inline routines
 * c: complex, p: padic, q: quad, f: floating point (REAL, some complex)
 * R: without imaginary part (INT, REAL, INTMOD, FRAC, PADIC if -1 not square)
 * T: some type (to be converted to PADIC)
 */
static GEN
addRc(GEN x, GEN y) {
  GEN z = cgetg(3,t_COMPLEX);
  gel(z,1) = gadd(x,gel(y,1));
  gel(z,2) = gcopy(gel(y,2)); return z;
}
static GEN
mulRc(GEN x, GEN y) {
  GEN z = cgetg(3,t_COMPLEX);
  gel(z,1) = isintzero(gel(y,1))? gen_0: gmul(x,gel(y,1));
  gel(z,2) = gmul(x,gel(y,2)); return z;
}
/* for INTMODs: can't simplify when Re(x) = gen_0 */
static GEN
mulRc_direct(GEN x, GEN y) {
  GEN z = cgetg(3,t_COMPLEX);
  gel(z,1) = gmul(x,gel(y,1));
  gel(z,2) = gmul(x,gel(y,2)); return z;
}
static GEN
divRc(GEN x, GEN y) {
  GEN t = gdiv(x, cxnorm(y)), mt = gneg(t); /* left on stack for efficiency */
  GEN z = cgetg(3,t_COMPLEX);
  gel(z,1) = isintzero(gel(y,1))? gen_0: gmul(t, gel(y,1));
  gel(z,2) = gmul(mt, gel(y,2));
  return z;
}
static GEN
divcR(GEN x, GEN y) {
  GEN z = cgetg(3,t_COMPLEX);
  gel(z,1) = isintzero(gel(x,1))? gen_0: gdiv(gel(x,1), y);
  gel(z,2) = gdiv(gel(x,2), y); return z;
}
static GEN
addRq(GEN x, GEN y) {
  GEN z = cgetg(4,t_QUAD);
  gel(z,1) = ZX_copy(gel(y,1));
  gel(z,2) = gadd(x, gel(y,2));
  gel(z,3) = gcopy(gel(y,3)); return z;
}
static GEN
mulRq(GEN x, GEN y) {
  GEN z = cgetg(4,t_QUAD);
  gel(z,1) = ZX_copy(gel(y,1));
  gel(z,2) = gmul(x,gel(y,2));
  gel(z,3) = gmul(x,gel(y,3)); return z;
}
static GEN
addqf(GEN x, GEN y, long prec) { pari_sp av = avma;
  long i = gexpo(x) - gexpo(y);
  if (i > 0) prec += nbits2extraprec( i );
  return gerepileupto(av, gadd(y, quadtofp(x, prec)));
}
static GEN
mulrfrac(GEN x, GEN y)
{
  pari_sp av = avma;
  GEN z, a = gel(y,1), b = gel(y,2);
  if (is_pm1(a)) /* frequent special case */
  {
    z = divri(x, b);
    if (signe(a) < 0) togglesign(z);
    return z;
  }
  return gerepileuptoleaf(av, divri(mulri(x,gel(y,1)), gel(y,2)));
}
static GEN
mulqf(GEN x, GEN y, long prec) { pari_sp av = avma;
  return gerepileupto(av, gmul(y, quadtofp(x, prec)));
}
static GEN
divqf(GEN x, GEN y, long prec) { pari_sp av = avma;
  return gerepileupto(av, gdiv(quadtofp(x,prec), y));
}
static GEN
divfq(GEN x, GEN y, long prec) { pari_sp av = avma;
  return gerepileupto(av, gdiv(x, quadtofp(y,prec)));
}
/* y PADIC, x + y by converting x to padic */
static GEN
addTp(GEN x, GEN y) { pari_sp av = avma; GEN z;

  if (!valp(y)) z = cvtop2(x,y);
  else {
    long l = signe(gel(y,4))? valp(y) + precp(y): valp(y);
    z  = cvtop(x, gel(y,2), l);
  }
  return gerepileupto(av, addsub_pp(z, y, addii));
}
/* y PADIC, x * y by converting x to padic */
static GEN
mulTp(GEN x, GEN y) { pari_sp av = avma;
  return gerepileupto(av, mulpp(cvtop2(x,y), y));
}
/* y PADIC, non zero x / y by converting x to padic */
static GEN
divTp(GEN x, GEN y) { pari_sp av = avma;
  return gerepileupto(av, divpp(cvtop2(x,y), y));
}
/* x PADIC, x / y by converting y to padic. Assume x != 0; otherwise y
 * converted to O(p^e) and division by 0 */
static GEN
divpT(GEN x, GEN y) { pari_sp av = avma;
  return gerepileupto(av, divpp(x, cvtop2(y,x)));
}

/* z := Mod(x,X) + Mod(y,X) [ t_INTMOD preallocated ], x,y,X INT, 0 <= x,y < X
 * clean memory from z on */
static GEN
add_intmod_same(GEN z, GEN X, GEN x, GEN y) {
  if (lgefint(X) == 3) {
    ulong u = Fl_add(itou(x),itou(y), X[2]);
    avma = (pari_sp)z; gel(z,2) = utoi(u);
  }
  else {
    GEN u = addii(x,y); if (cmpii(u, X) >= 0) u = subii(u, X);
    gel(z,2) = gerepileuptoint((pari_sp)z, u);
  }
  gel(z,1) = icopy(X); return z;
}
static GEN
sub_intmod_same(GEN z, GEN X, GEN x, GEN y) {
  if (lgefint(X) == 3) {
    ulong u = Fl_sub(itou(x),itou(y), X[2]);
    avma = (pari_sp)z; gel(z,2) = utoi(u);
  }
  else {
    GEN u = subii(x,y); if (signe(u) < 0) u = addii(u, X);
    gel(z,2) = gerepileuptoint((pari_sp)z, u);
  }
  gel(z,1) = icopy(X); return z;
}
/* cf add_intmod_same */
static GEN
mul_intmod_same(GEN z, GEN X, GEN x, GEN y) {
  if (lgefint(X) == 3) {
    ulong u = Fl_mul(itou(x),itou(y), X[2]);
    avma = (pari_sp)z; gel(z,2) = utoi(u);
  }
  else
    gel(z,2) = gerepileuptoint((pari_sp)z, remii(mulii(x,y), X) );
  gel(z,1) = icopy(X); return z;
}
/* cf add_intmod_same */
static GEN
div_intmod_same(GEN z, GEN X, GEN x, GEN y)
{
  if (lgefint(X) == 3) {
    ulong m = uel(X,2), u = Fl_div(itou(x), itou(y), m);
    avma = (pari_sp)z; gel(z,2) = utoi(u);
  }
  else
    gel(z,2) = gerepileuptoint((pari_sp)z, remii(mulii(x, Fp_inv(y,X)), X) );
  gel(z,1) = icopy(X); return z;
}

/*******************************************************************/
/*                                                                 */
/*        REDUCTION to IRREDUCIBLE TERMS (t_FRAC/t_RFRAC)          */
/*                                                                 */
/* (static routines are not memory clean, but OK for gerepileupto) */
/*******************************************************************/
/* Compute the denominator of (1/y) * (n/d) = n/yd, y a "scalar".
 * Sanity check : avoid (1/2) / (Mod(1,2)*x + 1) "=" 1 / (0 * x + 1) */
static GEN
rfrac_denom_mul_scal(GEN d, GEN y)
{
  GEN D = RgX_Rg_mul(d, y);
  if (lg(D) != lg(d))
  { /* try to generate a meaningful diagnostic */
    D = gdiv(leading_coeff(d), y); /* should fail */
    pari_err_INV("gred_rfrac", y); /* better than nothing */
  }
  return D;
}

/* d a t_POL, n a coprime t_POL of same var or "scalar". Not memory clean */
GEN
gred_rfrac_simple(GEN n, GEN d)
{
  GEN c, cn, cd, z;
  long dd = degpol(d);

  if (dd <= 0)
  {
    if (dd < 0) pari_err_INV("gred_rfrac_simple", d);
    n = gdiv(n, gel(d,2));
    if (typ(n) != t_POL || varn(n) != varn(d)) n = scalarpol(n, varn(d));
    return n;
  }

  cd = content(d);
  while (typ(n) == t_POL && !degpol(n)) n = gel(n,2);
  cn = (typ(n) == t_POL && varn(n) == varn(d))? content(n): n;
  if (!gequal1(cd)) {
    d = RgX_Rg_div(d,cd);
    if (!gequal1(cn))
    {
      if (gequal0(cn)) {
        if (isexactzero(cn)) return scalarpol(cn, varn(d));
        n = (cn != n)? RgX_Rg_div(n,cd): gdiv(n, cd);
        c = gen_1;
      } else {
        n = (cn != n)? RgX_Rg_div(n,cn): gen_1;
        c = gdiv(cn,cd);
      }
    }
    else
      c = ginv(cd);
  } else {
    if (!gequal1(cn))
    {
      if (gequal0(cn)) {
        if (isexactzero(cn)) return scalarpol(cn, varn(d));
        c = gen_1;
      } else {
        n = (cn != n)? RgX_Rg_div(n,cn): gen_1;
        c = cn;
      }
    } else {
      GEN y = cgetg(3,t_RFRAC);
      gel(y,1) = gcopy(n);
      gel(y,2) = RgX_copy(d); return y;
    }
  }

  if (typ(c) == t_POL)
  {
    z = c;
    do { z = content(z); } while (typ(z) == t_POL);
    cd = denom_i(z);
    cn = gmul(c, cd);
  }
  else
  {
    cn = numer_i(c);
    cd = denom_i(c);
  }
  z = cgetg(3,t_RFRAC);
  gel(z,1) = gmul(n, cn);
  gel(z,2) = rfrac_denom_mul_scal(d, cd);
  return z;
}

/* in rare cases x may be a t_POL, after 0/x for instance -> pol_0() */
static GEN
fix_rfrac(GEN x, long d)
{
  GEN z, N, D;
  if (!d || typ(x) == t_POL) return x;
  z = cgetg(3, t_RFRAC);
  N = gel(x,1);
  D = gel(x,2);
  if (d > 0) {
    gel(z, 1) = (typ(N)==t_POL && varn(N)==varn(D))? RgX_shift(N,d)
                                                   : monomialcopy(N,d,varn(D));
    gel(z, 2) = RgX_copy(D);
  } else {
    gel(z, 1) = gcopy(N);
    gel(z, 2) = RgX_shift(D, -d);
  }
  return z;
}

/* assume d != 0 */
static GEN
gred_rfrac2(GEN n, GEN d)
{
  GEN y, z;
  long v, vd, vn;

  n = simplify_shallow(n);
  if (isintzero(n)) return scalarpol(Rg_get_0(d), varn(d));
  d = simplify_shallow(d);
  if (typ(d) != t_POL) return gdiv(n,d);
  vd = varn(d);
  if (typ(n) != t_POL)
  {
    if (varncmp(vd, gvar(n)) >= 0) return gdiv(n,d);
    if (varncmp(vd, gvar2(n)) < 0) return gred_rfrac_simple(n,d);
    pari_err_BUG("gred_rfrac2 [incompatible variables]");
  }
  vn = varn(n);
  if (varncmp(vd, vn) < 0) return gred_rfrac_simple(n,d);
  if (varncmp(vd, vn) > 0) return RgX_Rg_div(n,d);

  /* now n and d are t_POLs in the same variable */
  v = RgX_valrem(n, &n) - RgX_valrem(d, &d);
  if (!degpol(d))
  {
    n = RgX_Rg_div(n,gel(d,2));
    return v? RgX_mulXn(n,v): n;
  }

  /* X does not divide gcd(n,d), deg(d) > 0 */
  if (!isinexact(n) && !isinexact(d))
  {
    y = RgX_divrem(n, d, &z);
    if (!signe(z)) { cgiv(z); return v? RgX_mulXn(y, v): y; }
    z = RgX_gcd(d, z);
    if (degpol(z)) { n = RgX_div(n,z); d = RgX_div(d,z); }
  }
  return fix_rfrac(gred_rfrac_simple(n,d), v);
}

/* x,y t_INT, return x/y in reduced form */
GEN
Qdivii(GEN x, GEN y)
{
  pari_sp av = avma;
  GEN r, q;

  if (is_pm1(y)) return (signe(y) < 0)? negi(x): icopy(x);
  if (equali1(x)) {
    long s = signe(y);
    if (!s) pari_err_INV("gdiv",y);
    if (signe(x) < 0) s = -s;
    q = cgetg(3, t_FRAC);
    gel(q,1) = s<0? gen_m1: gen_1;
    gel(q,2) = absi(y); return q;
  }
  q = dvmdii(x,y,&r);
  if (r == gen_0) return q; /* gen_0 intended */
  r = gcdii(y,r);
  if (lgefint(r) == 3)
  {
    ulong t = r[2];
    avma = av;
    if (t == 1) q = mkfraccopy(x,y);
    else
    {
      q = cgetg(3,t_FRAC);
      gel(q,1) = diviuexact(x,t);
      gel(q,2) = diviuexact(y,t);
    }
  }
  else
  { /* rare: r and q left on stack for efficiency */
    q = cgetg(3,t_FRAC);
    gel(q,1) = diviiexact(x,r);
    gel(q,2) = diviiexact(y,r);
  }
  normalize_frac(q); return q;
}

/*******************************************************************/
/*                                                                 */
/*                          CONJUGATION                            */
/*                                                                 */
/*******************************************************************/
/* lift( conj(Mod(x, y)) ), assuming degpol(y) = 2, degpol(x) < 2 */
static GEN
quad_polmod_conj(GEN x, GEN y)
{
  GEN z, u, v, a, b;
  if (typ(x) != t_POL) return gcopy(x);
  if (varn(x) != varn(y) || degpol(x) <= 0) return RgX_copy(x);
  a = gel(y,4); u = gel(x,3); /*Mod(ux + v, ax^2 + bx + c)*/
  b = gel(y,3); v = gel(x,2);
  z = cgetg(4, t_POL); z[1] = x[1];
  gel(z,2) = gsub(v, gdiv(gmul(u,b), a));
  gel(z,3) = gneg(u); return z;
}
static GEN
quad_polmod_norm(GEN x, GEN y)
{
  GEN z, u, v, a, b, c;
  if (typ(x) != t_POL || varn(x) != varn(y) || degpol(x) <= 0) return gsqr(x);
  a = gel(y,4); u = gel(x,3); /*Mod(ux + v, ax^2 + bx + c)*/
  b = gel(y,3); v = gel(x,2);
  c = gel(y,2);
  z = gmul(u, gsub(gmul(c,u), gmul(b,v)));
  if (!gequal1(a)) z = gdiv(z, a);
  return gadd(z, gsqr(v));
}

GEN
conj_i(GEN x)
{
  long lx, i;
  GEN y;

  switch(typ(x))
  {
    case t_INT: case t_REAL: case t_INTMOD: case t_FRAC: case t_PADIC:
      return x;

    case t_COMPLEX: return mkcomplex(gel(x,1), gneg(gel(x,2)));

    case t_QUAD:
      y = cgetg(4,t_QUAD);
      gel(y,1) = gel(x,1);
      gel(y,2) = gequal0(gmael(x,1,3))? gel(x,2)
                                      : gadd(gel(x,2), gel(x,3));
      gel(y,3) = gneg(gel(x,3)); return y;

    case t_POL: case t_SER:
      y = cgetg_copy(x, &lx); y[1] = x[1];
      for (i=2; i<lx; i++) gel(y,i) = conj_i(gel(x,i));
      return y;

    case t_RFRAC: case t_VEC: case t_COL: case t_MAT:
      y = cgetg_copy(x, &lx);
      for (i=1; i<lx; i++) gel(y,i) = conj_i(gel(x,i));
      return y;

    case t_POLMOD:
    {
      GEN X = gel(x,1);
      long d = degpol(X);
      if (d < 2) return x;
      if (d == 2) return mkpolmod(quad_polmod_conj(gel(x,2), X), X);
    }
  }
  pari_err_TYPE("gconj",x);
  return NULL; /* LCOV_EXCL_LINE */
}
GEN
gconj(GEN x)
{ pari_sp av = avma; return gerepilecopy(av, conj_i(x)); }

GEN
conjvec(GEN x,long prec)
{
  long lx, s, i;
  GEN z;

  switch(typ(x))
  {
    case t_INT: case t_INTMOD: case t_FRAC:
      return mkcolcopy(x);

    case t_COMPLEX: case t_QUAD:
      z=cgetg(3,t_COL); gel(z,1) = gcopy(x); gel(z,2) = gconj(x); break;

    case t_FFELT:
      return FF_conjvec(x);

    case t_VEC: case t_COL:
      lx = lg(x); z = cgetg(lx,t_MAT);
      if (lx == 1) return z;
      gel(z,1) = conjvec(gel(x,1),prec);
      s = lgcols(z);
      for (i=2; i<lx; i++)
      {
        gel(z,i) = conjvec(gel(x,i),prec);
        if (lg(gel(z,i)) != s) pari_err_OP("conjvec", gel(z,1), gel(z,i));
      }
      break;

    case t_POLMOD: {
      GEN T = gel(x,1), r;
      pari_sp av;

      lx = lg(T);
      if (lx <= 3) return cgetg(1,t_COL);
      x = gel(x,2);
      for (i=2; i<lx; i++)
      {
        GEN c = gel(T,i);
        switch(typ(c)) {
          case t_INTMOD: {
            GEN p = gel(c,1);
            pari_sp av;
            if (typ(x) != t_POL) retconst_col(lx-3, Rg_to_Fp(x, p));
            av = avma;
            T = RgX_to_FpX(T,p);
            x = RgX_to_FpX(x, p);
            if (varn(x) != varn(T)) pari_err_VAR("conjvec",x,T);
            z = FpXQC_to_mod(FpXQ_conjvec(x, T , p), T, p);
            return gerepileupto(av, z);
          }
          case t_INT:
          case t_FRAC: break;
          default: pari_err_TYPE("conjvec [not a rational t_POL]",T);
        }
      }
      if (typ(x) != t_POL)
      {
        if (!is_rational_t(typ(x)))
          pari_err_TYPE("conjvec [not a rational t_POL]",x);
        retconst_col(lx-3, gcopy(x));
      }
      RgX_check_QX(x,"conjvec");
      av = avma;
      if (varn(x) != varn(T)) pari_err_VAR("conjvec",x,T);
      r = cleanroots(T,prec);
      z = cgetg(lx-2,t_COL);
      for (i=1; i<=lx-3; i++) gel(z,i) = poleval(x, gel(r,i));
      return gerepileupto(av, z);
    }

    default:
      pari_err_TYPE("conjvec",x);
      return NULL; /* LCOV_EXCL_LINE */
  }
  return z;
}


/********************************************************************/
/**                                                                **/
/**                           ADDITION                             **/
/**                                                                **/
/********************************************************************/
/* x, y compatible PADIC, op = add or sub */
static GEN
addsub_pp(GEN x, GEN y, GEN (*op)(GEN,GEN))
{
  pari_sp av = avma;
  long d,e,r,rx,ry;
  GEN u, z, mod, p = gel(x,2);
  int swap;

  (void)new_chunk(5 + lgefint(gel(x,3)) + lgefint(gel(y,3)));
  e = valp(x);
  r = valp(y); d = r-e;
  if (d < 0) { swap = 1; swap(x,y); e = r; d = -d; } else swap = 0;
  rx = precp(x);
  ry = precp(y);
  if (d) /* v(x) < v(y) */
  {
    r = d+ry; z = powiu(p,d);
    if (r < rx) mod = mulii(z,gel(y,3)); else { r = rx; mod = gel(x,3); }
    z = mulii(z,gel(y,4));
    u = swap? op(z, gel(x,4)): op(gel(x,4), z);
  }
  else
  {
    long c;
    if (ry < rx) { r=ry; mod = gel(y,3); } else { r=rx; mod = gel(x,3); }
    u = swap? op(gel(y,4), gel(x,4)): op(gel(x,4), gel(y,4));
    if (!signe(u) || (c = Z_pvalrem(u,p,&u)) >= r)
    {
      avma = av; return zeropadic(p, e+r);
    }
    if (c)
    {
      mod = diviiexact(mod, powiu(p,c));
      r -= c;
      e += c;
    }
  }
  u = modii(u, mod);
  avma = av; z = cgetg(5,t_PADIC);
  z[1] = evalprecp(r) | evalvalp(e);
  gel(z,2) = icopy(p);
  gel(z,3) = icopy(mod);
  gel(z,4) = icopy(u); return z;
}
/* Rg_to_Fp(t_FRAC) without GC */
static GEN
Q_to_Fp(GEN x, GEN p)
{ return mulii(gel(x,1), Fp_inv(gel(x,2),p)); }
/* return x + y, where y t_PADIC and x is a non-zero t_INT or t_FRAC */
static GEN
addQp(GEN x, GEN y)
{
  pari_sp av = avma;
  long d, r, e, vy = valp(y), py = precp(y);
  GEN z, q, mod, u, p = gel(y,2);

  e = Q_pvalrem(x, p, &x);
  d = vy - e; r = d + py;
  if (r <= 0) { avma = av; return gcopy(y); }
  mod = gel(y,3);
  u   = gel(y,4);
  (void)new_chunk(5 + ((lgefint(mod) + lgefint(p)*labs(d)) << 1));

  if (d > 0)
  {
    q = powiu(p,d);
    mod = mulii(mod, q);
    if (typ(x) != t_INT) x = Q_to_Fp(x, mod);
    u = addii(x,  mulii(u, q));
  }
  else if (d < 0)
  {
    q = powiu(p,-d);
    if (typ(x) != t_INT) x = Q_to_Fp(x, mod);
    u = addii(u, mulii(x, q));
    r = py; e = vy;
  }
  else
  {
    long c;
    if (typ(x) != t_INT) x = Q_to_Fp(x, mod);
    u = addii(u, x);
    if (!signe(u) || (c = Z_pvalrem(u,p,&u)) >= r)
    {
      avma = av; return zeropadic(p,e+r);
    }
    if (c)
    {
      mod = diviiexact(mod, powiu(p,c));
      r -= c;
      e += c;
    }
  }
  u = modii(u, mod); avma = av;
  z = cgetg(5,t_PADIC);
  z[1] = evalprecp(r) | evalvalp(e);
  gel(z,2) = icopy(p);
  gel(z,3) = icopy(mod);
  gel(z,4) = icopy(u); return z;
}

/* Mod(x,X) + Mod(y,X) */
#define addsub_polmod_same addsub_polmod_scal
/* Mod(x,X) +/- Mod(y,Y) */
static GEN
addsub_polmod(GEN X, GEN Y, GEN x, GEN y, GEN(*op)(GEN,GEN))
{
  long T[3] = { evaltyp(t_POLMOD) | _evallg(3),0,0 };
  GEN z = cgetg(3,t_POLMOD);
  long vx = varn(X), vy = varn(Y);
  if (vx==vy) {
    pari_sp av;
    gel(z,1) = RgX_gcd(X,Y); av = avma;
    warn_coercion(X,Y,gel(z,1));
    gel(z,2) = gerepileupto(av, gmod(op(x, y), gel(z,1))); return z;
  }
  if (varncmp(vx, vy) < 0)
  { gel(z,1) = RgX_copy(X); gel(T,1) = Y; gel(T,2) = y; y = T; }
  else
  { gel(z,1) = RgX_copy(Y); gel(T,1) = X; gel(T,2) = x; x = T; }
  gel(z,2) = op(x, y); return z;
}
/* Mod(y, Y) +/- x,  x scalar or polynomial in same var and reduced degree */
static GEN
addsub_polmod_scal(GEN Y, GEN y, GEN x, GEN(*op)(GEN,GEN))
{ retmkpolmod(degpol(Y)? op(y, x): gen_0, RgX_copy(Y)); }

/* typ(y) == t_SER, x "scalar" [e.g object in lower variable] */
static GEN
add_ser_scal(GEN y, GEN x)
{
  long i, l, ly, vy;
  GEN z;

  if (isrationalzero(x)) return gcopy(y);
  ly = lg(y);
  l = valp(y);
  if (l < 3-ly) return gcopy(y);
  /* l + ly >= 3 */
  if (l < 0)
  {
    z = cgetg(ly,t_SER); z[1] = y[1];
    for (i = 2; i <= 1-l; i++) gel(z,i) = gcopy(gel(y,i));
    gel(z,i) = gadd(x,gel(y,i)); i++;
    for (     ; i < ly; i++)   gel(z,i) = gcopy(gel(y,i));
    return z;
  }
  vy = varn(y);
  if (l > 0)
  {
    if (ser_isexactzero(y))
      return scalarser(ly == 2? x: gadd(x,gel(y,2)), vy, l);
    y -= l; ly += l;
    z = cgetg(ly,t_SER);
    x = gcopy(x);
    for (i=3; i<=l+1; i++) gel(z,i) = gen_0;
  }
  else
  { /* l = 0, ly >= 3. Also OK if ser_isexactzero(y) */
    z = cgetg(ly,t_SER);
    x = gadd(x, gel(y,2));
    i = 3;
  }
  for (; i<ly; i++) gel(z,i) = gcopy(gel(y,i));
  gel(z,2) = x;
  z[1] = evalsigne(1) | _evalvalp(0) | evalvarn(vy);
  return gequal0(x)? normalize(z): z;
}
static long
_serprec(GEN x) { return ser_isexactzero(x)? 2: lg(x); }
/* x,y t_SER in the same variable: x+y */
static GEN
ser_add(GEN x, GEN y)
{
  long i, lx,ly, n = valp(y) - valp(x);
  GEN z;
  if (n < 0) { n = -n; swap(x,y); }
  /* valp(x) <= valp(y) */
  lx = _serprec(x);
  if (lx == 2) /* don't lose type information */
    return scalarser(gadd(Rg_get_0(x), Rg_get_0(y)), varn(x), valp(x));
  ly = _serprec(y) + n; if (lx < ly) ly = lx;
  if (n)
  {
    if (n+2 > lx) return gcopy(x);
    z = cgetg(ly,t_SER);
    for (i=2; i<=n+1; i++) gel(z,i) = gcopy(gel(x,i));
    for (   ; i < ly; i++) gel(z,i) = gadd(gel(x,i),gel(y,i-n));
  } else {
    z = cgetg(ly,t_SER);
    for (i=2; i < ly; i++) gel(z,i) = gadd(gel(x,i),gel(y,i));
  }
  z[1] = x[1]; return normalize(z);
}
/* typ(y) == RFRAC, x polynomial in same variable or "scalar" */
static GEN
add_rfrac_scal(GEN y, GEN x)
{
  pari_sp av;
  GEN n;

  if (isintzero(x)) return gcopy(y); /* frequent special case */
  av = avma; n = gadd(gmul(x, gel(y,2)), gel(y,1));
  return gerepileupto(av, gred_rfrac_simple(n, gel(y,2)));
}

/* x "scalar", ty != t_MAT and non-scalar */
static GEN
add_scal(GEN y, GEN x, long ty)
{
  switch(ty)
  {
    case t_POL: return RgX_Rg_add(y, x);
    case t_SER: return add_ser_scal(y, x);
    case t_RFRAC: return add_rfrac_scal(y, x);
    case t_COL: return RgC_Rg_add(y, x);
    case t_VEC:
      if (isintzero(x)) return gcopy(y);
      break;
  }
  pari_err_TYPE2("+",x,y);
  return NULL; /* LCOV_EXCL_LINE */
}

static GEN
addsub_frac(GEN x, GEN y, GEN (*op)(GEN,GEN))
{
  pari_sp av0 = avma;
  GEN x1 = gel(x,1), x2 = gel(x,2), z = cgetg(3,t_FRAC);
  GEN y1 = gel(y,1), y2 = gel(y,2), q, r, n, d, delta;
  int s = cmpii(x2, y2);

  if (!s)
  { /* common denominator: (x1 op y1) / x2 */
    n = op(x1, y1);
    if (!signe(n)) { avma = av0; return gen_0; }
    d = x2;
    q = dvmdii(n, d, &r);
    if (r == gen_0) { avma = av0; return icopy(q); }
    r = gcdii(d, r);
    if (!equali1(r)) { n = diviiexact(n, r); d = diviiexact(d, r); }
    avma = (pari_sp)z;
    gel(z,1) = icopy(n);
    gel(z,2) = icopy(d); return z;
  }
  if (s < 0)
  {
    GEN Q = dvmdii(y2, x2, &r);
    if (r == gen_0)
    { /* y2 = Q x2: 1/x2 . (Q x1 op y1)/Q, where latter is in coprime form */
      pari_sp av = avma;
      n = op(mulii(Q,x1), y1);
      q = dvmdii(n, x2, &r);
      if (r == gen_0)
      {
        gel(z,1) = gerepileuptoint(av, q);
        gel(z,2) = Q; return z;
      }
      r = gcdii(x2, r);
      if (!equali1(r)) { n = diviiexact(n, r); x2 = diviiexact(x2, r); }
      d = mulii(x2,Q); avma = (pari_sp)z;
      gel(z,1) = icopy(n);
      gel(z,2) = icopy(d); return z;
    }
    delta = gcdii(x2,r);
  }
  else
  {
    GEN Q = dvmdii(x2, y2, &r);
    if (r == gen_0)
    { /* x2 = Q y2: 1/y2 . (x1 op Q y1)/Q, where latter is in coprime form */
      pari_sp av = avma;
      n = op(x1, mulii(Q,y1));
      q = dvmdii(n, y2, &r);
      if (r == gen_0)
      {
        gel(z,1) = gerepileuptoint(av, q);
        gel(z,2) = Q; return z;
      }
      r = gcdii(y2, r);
      if (!equali1(r)) { n = diviiexact(n, r); y2 = diviiexact(y2, r); }
      d = mulii(y2,Q); avma=(pari_sp)z;
      gel(z,1) = icopy(n);
      gel(z,2) = icopy(d); return z;
    }
    delta = gcdii(y2,r);
  }
  /* delta = gcd(x2,y2) */
  if (equali1(delta))
  { /* numerator is non-zero */
    gel(z,1) = gerepileuptoint((pari_sp)z, op(mulii(x1,y2), mulii(y1,x2)));
    gel(z,2) = mulii(x2,y2); return z;
  }
  x2 = diviiexact(x2,delta);
  y2 = diviiexact(y2,delta);
  n = op(mulii(x1,y2), mulii(y1,x2));
  if (!signe(n)) { avma = av0; return gen_0; }
  d = mulii(x2, y2);
  q = dvmdii(n, delta, &r);
  if (r == gen_0)
  {
    if (equali1(d)) { avma = av0; return icopy(q); }
    avma = (pari_sp)z;
    gel(z,2) = icopy(d);
    gel(z,1) = icopy(q); return z;
  }
  r = gcdii(delta, r);
  if (!equali1(r))
  {
    n     = diviiexact(n, r);
    delta = diviiexact(delta, r);
  }
  d = mulii(d,delta); avma = (pari_sp)z;
  gel(z,1) = icopy(n);
  gel(z,2) = icopy(d); return z;
}

/* assume x2, y2 are t_POLs in the same variable */
static GEN
add_rfrac(GEN x, GEN y)
{
  pari_sp av = avma;
  GEN x1 = gel(x,1), x2 = gel(x,2);
  GEN y1 = gel(y,1), y2 = gel(y,2), q, r, n, d, delta;

  delta = RgX_gcd(x2,y2);
  if (!degpol(delta))
  {
    n = simplify_shallow( gadd(gmul(x1,y2), gmul(y1,x2)) );
    d = RgX_mul(x2, y2);
    return gerepileupto(av, gred_rfrac_simple(n, d));
  }
  x2 = RgX_div(x2,delta);
  y2 = RgX_div(y2,delta);
  n = gadd(gmul(x1,y2), gmul(y1,x2));
  if (!signe(n))
  {
    n = simplify_shallow(n);
    if (isrationalzero(n)) return gerepileupto(av, zeropol(varn(x2)));
    return gerepilecopy(av, mkrfrac(n, RgX_mul(gel(x,2),y2)));
  }
  if (degpol(n) == 0)
    return gerepileupto(av, gred_rfrac_simple(gel(n,2), RgX_mul(gel(x,2),y2)));
  q = RgX_divrem(n, delta, &r); /* we want gcd(n,delta) */
  if (isexactzero(r))
  {
    GEN z;
    d = RgX_mul(x2, y2);
    /* "constant" denominator ? */
    z = lg(d) == 3? RgX_Rg_div(q, gel(d,2)): gred_rfrac_simple(q, d);
    return gerepileupto(av, z);
  }
  r = RgX_gcd(delta, r);
  if (degpol(r))
  {
    n = RgX_div(n, r);
    d = RgX_mul(RgX_mul(x2,y2), RgX_div(delta, r));
  }
  else
    d = RgX_mul(gel(x,2), y2);
  return gerepileupto(av, gred_rfrac_simple(n, d));
}

GEN
gadd(GEN x, GEN y)
{
  long tx = typ(x), ty = typ(y), vx, vy, lx, i, l;
  pari_sp av, tetpil;
  GEN z, p1;

  if (tx == ty) switch(tx) /* shortcut to generic case */
  {
    case t_INT: return addii(x,y);
    case t_REAL: return addrr(x,y);
    case t_INTMOD:  { GEN X = gel(x,1), Y = gel(y,1);
      z = cgetg(3,t_INTMOD);
      if (X==Y || equalii(X,Y))
        return add_intmod_same(z, X, gel(x,2), gel(y,2));
      gel(z,1) = gcdii(X,Y);
      warn_coercion(X,Y,gel(z,1));
      av = avma; p1 = addii(gel(x,2),gel(y,2));
      gel(z,2) = gerepileuptoint(av, remii(p1, gel(z,1))); return z;
    }
    case t_FRAC: return addsub_frac(x,y,addii);
    case t_COMPLEX: z = cgetg(3,t_COMPLEX);
      gel(z,2) = gadd(gel(x,2),gel(y,2));
      if (isintzero(gel(z,2)))
      {
        avma = (pari_sp)(z+3);
        return gadd(gel(x,1),gel(y,1));
      }
      gel(z,1) = gadd(gel(x,1),gel(y,1));
      return z;
    case t_PADIC:
      if (!equalii(gel(x,2),gel(y,2))) pari_err_OP("+",x,y);
      return addsub_pp(x,y, addii);
    case t_QUAD: z = cgetg(4,t_QUAD);
      if (!ZX_equal(gel(x,1),gel(y,1))) pari_err_OP("+",x,y);
      gel(z,1) = ZX_copy(gel(x,1));
      gel(z,2) = gadd(gel(x,2),gel(y,2));
      gel(z,3) = gadd(gel(x,3),gel(y,3)); return z;
    case t_POLMOD:
      if (RgX_equal_var(gel(x,1), gel(y,1)))
        return addsub_polmod_same(gel(x,1), gel(x,2), gel(y,2), &gadd);
      return addsub_polmod(gel(x,1), gel(y,1), gel(x,2), gel(y,2), &gadd);
    case t_FFELT: return FF_add(x,y);
    case t_POL:
      vx = varn(x);
      vy = varn(y);
      if (vx != vy) {
        if (varncmp(vx, vy) < 0) return RgX_Rg_add(x, y);
        else                     return RgX_Rg_add(y, x);
      }
      return RgX_add(x, y);
    case t_SER:
      vx = varn(x);
      vy = varn(y);
      if (vx != vy) {
        if (varncmp(vx, vy) < 0) return add_ser_scal(x, y);
        else                     return add_ser_scal(y, x);
      }
      return ser_add(x, y);
    case t_RFRAC:
      vx = varn(gel(x,2));
      vy = varn(gel(y,2));
      if (vx != vy) {
        if (varncmp(vx, vy) < 0) return add_rfrac_scal(x, y);
        else                     return add_rfrac_scal(y, x);
      }
      return add_rfrac(x,y);
    case t_VEC:
      if (lg(y) != lg(x)) pari_err_OP("+",x,y);
      return RgV_add(x,y);
    case t_COL:
      if (lg(y) != lg(x)) pari_err_OP("+",x,y);
      return RgC_add(x,y);
    case t_MAT:
      lx = lg(x);
      if (lg(y) != lx) pari_err_OP("+",x,y);
      if (lx == 1) return cgetg(1, t_MAT);
      if (lgcols(y) != lgcols(x)) pari_err_OP("+",x,y);
      return RgM_add(x,y);

    default: pari_err_TYPE2("+",x,y);
  }
  /* tx != ty */
  if (tx > ty) { swap(x,y); lswap(tx,ty); }

  if (is_const_t(ty)) switch(tx) /* tx < ty, is_const_t(tx) && is_const_t(ty) */
  {
    case t_INT:
      switch(ty)
      {
        case t_REAL: return addir(x,y);
        case t_INTMOD:
          z = cgetg(3, t_INTMOD);
          return add_intmod_same(z, gel(y,1), gel(y,2), modii(x, gel(y,1)));
        case t_FRAC: z = cgetg(3,t_FRAC);
          gel(z,1) = gerepileuptoint((pari_sp)z, addii(gel(y,1), mulii(gel(y,2),x)));
          gel(z,2) = icopy(gel(y,2)); return z;
        case t_COMPLEX: return addRc(x, y);
        case t_PADIC:
          if (!signe(x)) return gcopy(y);
          return addQp(x,y);
        case t_QUAD: return addRq(x, y);
        case t_FFELT: return FF_Z_add(y,x);
      }

    case t_REAL:
      switch(ty)
      {
        case t_FRAC:
          if (!signe(gel(y,1))) return rcopy(x);
          if (!signe(x))
          {
            lx = expi(gel(y,1)) - expi(gel(y,2)) - expo(x);
            return lx <= 0? rcopy(x): fractor(y, nbits2prec(lx));
          }
          av=avma; z=addir(gel(y,1),mulir(gel(y,2),x)); tetpil=avma;
          return gerepile(av,tetpil,divri(z,gel(y,2)));
        case t_COMPLEX: return addRc(x, y);
        case t_QUAD: return gequal0(y)? rcopy(x): addqf(y, x, lg(x));

        default: pari_err_TYPE2("+",x,y);
      }

    case t_INTMOD:
      switch(ty)
      {
        case t_FRAC: { GEN X = gel(x,1);
          z = cgetg(3, t_INTMOD);
          p1 = Fp_div(gel(y,1), gel(y,2), X);
          return add_intmod_same(z, X, p1, gel(x,2));
        }
        case t_FFELT:
          if (!equalii(gel(x,1),FF_p_i(y)))
            pari_err_OP("+",x,y);
          return FF_Z_add(y,gel(x,2));
        case t_COMPLEX: return addRc(x, y);
        case t_PADIC: { GEN X = gel(x,1);
          z = cgetg(3, t_INTMOD);
          return add_intmod_same(z, X, gel(x,2), padic_to_Fp(y, X));
        }
        case t_QUAD: return addRq(x, y);
      }

    case t_FRAC:
      switch (ty)
      {
        case t_COMPLEX: return addRc(x, y);
        case t_PADIC:
          if (!signe(gel(x,1))) return gcopy(y);
          return addQp(x,y);
        case t_QUAD: return addRq(x, y);
        case t_FFELT: return FF_Q_add(y, x);
      }

    case t_FFELT:
      pari_err_TYPE2("+",x,y);

    case t_COMPLEX:
      switch(ty)
      {
        case t_PADIC:
          return Zp_nosquare_m1(gel(y,2))? addRc(y, x): addTp(x, y);
        case t_QUAD:
          lx = precision(x); if (!lx) pari_err_OP("+",x,y);
          return gequal0(y)? gcopy(x): addqf(y, x, lx);
      }

    case t_PADIC: /* ty == t_QUAD */
      return (kro_quad(y,gel(x,2)) == -1)? addRq(x, y): addTp(y, x);
  }
  /* tx < ty, !is_const_t(y) */
  switch(ty)
  {
    case t_MAT:
      if (is_matvec_t(tx)) pari_err_TYPE2("+",x,y);
      if (isrationalzero(x)) return gcopy(y);
      return RgM_Rg_add(y, x);
    case t_COL:
      if (tx == t_VEC) pari_err_TYPE2("+",x,y);
      return RgC_Rg_add(y, x);
    case t_POLMOD: /* is_const_t(tx) in this case */
      return addsub_polmod_scal(gel(y,1), gel(y,2), x, &gadd);
  }
  if (is_scalar_t(tx))  {
    if (tx == t_POLMOD)
    {
      vx = varn(gel(x,1));
      vy = gvar(y);
      if (vx == vy) y = gmod(y, gel(x,1)); /* error if ty == t_SER */
      else
        if (varncmp(vx,vy) > 0) return add_scal(y, x, ty);
      return addsub_polmod_scal(gel(x,1), gel(x,2), y, &gadd);
    }
    return add_scal(y, x, ty);
  }
  /* x and y are not scalars, ty != t_MAT */
  vx = gvar(x);
  vy = gvar(y);
  if (vx != vy) { /* x or y is treated as a scalar */
    if (is_vec_t(tx) || is_vec_t(ty)) pari_err_TYPE2("+",x,y);
    return (varncmp(vx, vy) < 0)? add_scal(x, y, tx)
                                : add_scal(y, x, ty);
  }
  /* vx = vy */
  switch(tx)
  {
    case t_POL:
      switch (ty)
      {
        case t_SER:
          if (lg(x) == 2) return gcopy(y);
          i = RgX_val(x); if (i == LONG_MAX) i = 0; /* e.g. x = Mod(0,3)*x^0 */
          i = lg(y) + valp(y) - i;
          if (i < 3) return gcopy(y);
          p1 = RgX_to_ser(x,i); y = ser_add(p1,y);
          settyp(p1, t_VECSMALL); /* p1 left on stack */
          return y;

        case t_RFRAC: return add_rfrac_scal(y, x);
      }
      break;

    case t_SER:
      if (ty == t_RFRAC)
      {
        GEN n, d;
        long vn, vd;
        av = avma;
        n = gel(y,1); vn = gval(n, vy);
        d = gel(y,2); vd = RgX_valrem(d, &d);

        l = lg(x) + valp(x) - (vn - vd);
        if (l < 3) { avma = av; return gcopy(x); }

        /* take advantage of y = t^n ! */
        if (degpol(d))
          y = gdiv(n, RgX_to_ser_inexact(d,l));
        else {
          y = gdiv(n, gel(d,2));
          if (gvar(y) == vy) y = RgX_to_ser(y,l); else y = scalarser(y, vy, l);
        }
        setvalp(y, valp(y) - vd);
        return gerepileupto(av, gadd(y, x));
      }
      break;
  }
  pari_err_TYPE2("+",x,y);
  return NULL; /* LCOV_EXCL_LINE */
}

GEN
gaddsg(long x, GEN y)
{
  long ty = typ(y);
  GEN z;

  switch(ty)
  {
    case t_INT:  return addsi(x,y);
    case t_REAL: return addsr(x,y);
    case t_INTMOD:
      z = cgetg(3, t_INTMOD);
      return add_intmod_same(z, gel(y,1), gel(y,2), modsi(x, gel(y,1)));
    case t_FRAC: z = cgetg(3,t_FRAC);
      gel(z,1) = gerepileuptoint((pari_sp)z, addii(gel(y,1), mulis(gel(y,2),x)));
      gel(z,2) = icopy(gel(y,2)); return z;
    case t_COMPLEX:
      z = cgetg(3, t_COMPLEX);
      gel(z,1) = gaddsg(x, gel(y,1));
      gel(z,2) = gcopy(gel(y,2)); return z;

    default: return gadd(stoi(x), y);
  }
}

GEN
gsubsg(long x, GEN y)
{
  GEN z, a, b;
  pari_sp av;

  switch(typ(y))
  {
    case t_INT:  return subsi(x,y);
    case t_REAL: return subsr(x,y);
    case t_INTMOD:
      z = cgetg(3, t_INTMOD); a = gel(y,1); b = gel(y,2);
      return add_intmod_same(z, a, Fp_neg(b,a), modsi(x, a));
    case t_FRAC: z = cgetg(3,t_FRAC); a = gel(y,1); b = gel(y,2);
      gel(z,1) = gerepileuptoint((pari_sp)z, subii(mulis(b,x), a));
      gel(z,2) = icopy(gel(y,2)); return z;
    case t_COMPLEX:
      z = cgetg(3, t_COMPLEX);
      gel(z,1) = gsubsg(x, gel(y,1));
      gel(z,2) = gneg(gel(y,2)); return z;
  }
  av = avma;
  return gerepileupto(av, gadd(stoi(x), gneg_i(y)));
}

/********************************************************************/
/**                                                                **/
/**                          SUBTRACTION                           **/
/**                                                                **/
/********************************************************************/

GEN
gsub(GEN x, GEN y)
{
  long tx = typ(x), ty = typ(y);
  pari_sp av;
  GEN z;
  if (tx == ty) switch(tx) /* shortcut to generic case */
  {
    case t_INT: return subii(x,y);
    case t_REAL: return subrr(x,y);
    case t_INTMOD:  { GEN p1, X = gel(x,1), Y = gel(y,1);
      z = cgetg(3,t_INTMOD);
      if (X==Y || equalii(X,Y))
        return sub_intmod_same(z, X, gel(x,2), gel(y,2));
      gel(z,1) = gcdii(X,Y);
      warn_coercion(X,Y,gel(z,1));
      av = avma; p1 = subii(gel(x,2),gel(y,2));
      gel(z,2) = gerepileuptoint(av, modii(p1, gel(z,1))); return z;
    }
    case t_FRAC: return addsub_frac(x,y, subii);
    case t_COMPLEX: z = cgetg(3,t_COMPLEX);
      gel(z,2) = gsub(gel(x,2),gel(y,2));
      if (isintzero(gel(z,2)))
      {
        avma = (pari_sp)(z+3);
        return gsub(gel(x,1),gel(y,1));
      }
      gel(z,1) = gsub(gel(x,1),gel(y,1));
      return z;
    case t_PADIC:
      if (!equalii(gel(x,2),gel(y,2))) pari_err_OP("+",x,y);
      return addsub_pp(x,y, subii);
    case t_QUAD: z = cgetg(4,t_QUAD);
      if (!ZX_equal(gel(x,1),gel(y,1))) pari_err_OP("+",x,y);
      gel(z,1) = ZX_copy(gel(x,1));
      gel(z,2) = gsub(gel(x,2),gel(y,2));
      gel(z,3) = gsub(gel(x,3),gel(y,3)); return z;
    case t_POLMOD:
      if (RgX_equal_var(gel(x,1), gel(y,1)))
        return addsub_polmod_same(gel(x,1), gel(x,2), gel(y,2), &gsub);
      return addsub_polmod(gel(x,1), gel(y,1), gel(x,2), gel(y,2), &gsub);
    case t_FFELT: return FF_sub(x,y);
    case t_POL: {
      long vx = varn(x);
      long vy = varn(y);
      if (vx != vy) {
        if (varncmp(vx, vy) < 0) return RgX_Rg_sub(x, y);
        else                     return Rg_RgX_sub(x, y);
      }
      return RgX_sub(x, y);
    }
    case t_VEC:
      if (lg(y) != lg(x)) pari_err_OP("+",x,y);
      return RgV_sub(x,y);
    case t_COL:
      if (lg(y) != lg(x)) pari_err_OP("+",x,y);
      return RgC_sub(x,y);
    case t_MAT: {
      long lx = lg(x);
      if (lg(y) != lx) pari_err_OP("+",x,y);
      if (lx == 1) return cgetg(1, t_MAT);
      if (lgcols(y) != lgcols(x)) pari_err_OP("+",x,y);
      return RgM_sub(x,y);
    }
    case t_RFRAC: case t_SER: break;

    default: pari_err_TYPE2("+",x,y);
  }
  av = avma;
  return gerepileupto(av, gadd(x,gneg_i(y)));
}

/********************************************************************/
/**                                                                **/
/**                        MULTIPLICATION                          **/
/**                                                                **/
/********************************************************************/
static GEN
mul_ser_scal(GEN y, GEN x) {
  long ly, i;
  GEN z;
  if (isexactzero(x)) return gmul(Rg_get_0(y), x);
  if (ser_isexactzero(y))
  {
    if (lg(y) == 2) return gcopy(y);
    return scalarser(gmul(x,gel(y,2)), varn(y), valp(y));
  }
  z = cgetg_copy(y, &ly); z[1] = y[1];
  for (i = 2; i < ly; i++) gel(z,i) = gmul(x,gel(y,i));
  return normalize(z);
}
/* (n/d) * x, x "scalar" or polynomial in the same variable as d
 * [n/d a valid RFRAC]  */
static GEN
mul_rfrac_scal(GEN n, GEN d, GEN x)
{
  pari_sp av = avma;
  GEN z;

  switch(typ(x))
  {
    case t_PADIC:
      n = gmul(n, x);
      d = gcvtop(d, gel(x,2), signe(gel(x,4))? precp(x): 1);
      return gerepileupto(av, gdiv(n,d));

    case t_INTMOD: case t_POLMOD:
      n = gmul(n, x);
      d = gmul(d, gmodulo(gen_1, gel(x,1)));
      return gerepileupto(av, gdiv(n,d));
  }
  z = gred_rfrac2(x, d);
  n = simplify_shallow(n);
  if (typ(z) == t_RFRAC)
  {
    n = gmul(gel(z,1), n);
    d = gel(z,2);
    if (typ(n) == t_POL && varncmp(varn(n), varn(d)) < 0)
      z = RgX_Rg_div(n, d);
    else
      z = gred_rfrac_simple(n, d);
  }
  else
    z = gmul(z, n);
  return gerepileupto(av, z);
}
static GEN
mul_scal(GEN y, GEN x, long ty)
{
  switch(ty)
  {
    case t_POL:
      if (lg(y) == 2) return scalarpol(gmul(gen_0,x), varn(y));
      return RgX_Rg_mul(y, x);
    case t_SER: return mul_ser_scal(y, x);
    case t_RFRAC: return mul_rfrac_scal(gel(y,1),gel(y,2), x);
    case t_QFI: case t_QFR:
      if (typ(x) == t_INT && gequal1(x)) return gcopy(y); /* fall through */
  }
  pari_err_TYPE2("*",x,y);
  return NULL; /* LCOV_EXCL_LINE */
}

static GEN
mul_gen_rfrac(GEN X, GEN Y)
{
  GEN y1 = gel(Y,1), y2 = gel(Y,2);
  long vx = gvar(X), vy = varn(y2);
  return (varncmp(vx, vy) <= 0)? mul_scal(Y, X, typ(Y)):
                                 gred_rfrac_simple(gmul(y1,X), y2);
}
/* (x1/x2) * (y1/y2) */
static GEN
mul_rfrac(GEN x1, GEN x2, GEN y1, GEN y2)
{
  GEN z, X, Y;
  pari_sp av = avma;

  X = gred_rfrac2(x1, y2);
  Y = gred_rfrac2(y1, x2);
  if (typ(X) == t_RFRAC)
  {
    if (typ(Y) == t_RFRAC) {
      x1 = gel(X,1);
      x2 = gel(X,2);
      y1 = gel(Y,1);
      y2 = gel(Y,2);
      z = gred_rfrac_simple(gmul(x1,y1), gmul(x2,y2));
    } else
      z = mul_gen_rfrac(Y, X);
  }
  else if (typ(Y) == t_RFRAC)
    z = mul_gen_rfrac(X, Y);
  else
    z = gmul(X, Y);
  return gerepileupto(av, z);
}
/* (x1/x2) /y2, x2 and y2 are t_POL in the same variable */
static GEN
div_rfrac_pol(GEN x1, GEN x2, GEN y2)
{
  pari_sp av = avma;
  GEN X = gred_rfrac2(x1, y2);
  if (typ(X) == t_RFRAC && varn(gel(X,2)) == varn(x2))
  {
    x2 = RgX_mul(gel(X,2), x2);
    x1 = gel(X,1);
  }
  else
    x1 = X;
  return gerepileupto(av, gred_rfrac_simple(x1, x2));
}

/* Mod(y, Y) * x,  assuming x scalar */
static GEN
mul_polmod_scal(GEN Y, GEN y, GEN x)
{ retmkpolmod(gmul(x,y), RgX_copy(Y)); }

/* cf mulqq */
static GEN
quad_polmod_mul(GEN P, GEN x, GEN y)
{
  GEN T = cgetg(4, t_POL), b = gel(P,3), c = gel(P,2), p1, p2, p3, p4;
  pari_sp tetpil, av = avma;
  T[1] = x[1];
  p2 = gmul(gel(x,2), gel(y,2));
  p3 = gmul(gel(x,3), gel(y,3));
  p1 = gmul(gneg_i(c),p3);
  /* operands are usually small: gadd ~ gmul and Karatsuba is a waste */
  if (typ(b) == t_INT)
  {
    if (signe(b))
    {
      p4 = gadd(gmul(gel(x,2), gel(y,3)), gmul(gel(x,3), gel(y,2)));
      if (is_pm1(b))
      {
        if (signe(b) > 0) p3 = gneg(p3);
      }
      else
        p3 = gmul(negi(b), p3);
    }
    else
    {
      p3 = gmul(gel(x,2),gel(y,3));
      p4 = gmul(gel(x,3),gel(y,2));
    }
  }
  else
  {
    p4 = gadd(gmul(gel(x,2), gel(y,3)), gmul(gel(x,3), gel(y,2)));
    p3 = gmul(gneg_i(b), p3);
  }
  tetpil = avma;
  gel(T,2) = gadd(p2, p1);
  gel(T,3) = gadd(p4, p3);
  gerepilecoeffssp(av,tetpil,T+2,2);
  return normalizepol_lg(T,4);
}
/* Mod(x,T) * Mod(y,T) */
static GEN
mul_polmod_same(GEN T, GEN x, GEN y)
{
  GEN z = cgetg(3,t_POLMOD), a;
  long v = varn(T), lx = lg(x), ly = lg(y);
  gel(z,1) = RgX_copy(T);
  /* x * y mod T optimised */
  if (typ(x) != t_POL || varn(x) != v || lx <= 3
   || typ(y) != t_POL || varn(y) != v || ly <= 3)
    a = gmul(x, y);
  else
  {
    if (lg(T) == 5 && isint1(gel(T,4))) /* quadratic fields */
      a = quad_polmod_mul(T, x, y);
    else
      a = RgXQ_mul(x, y, gel(z,1));
  }
  gel(z,2) = a; return z;
}
static GEN
sqr_polmod(GEN T, GEN x)
{
  GEN a, z = cgetg(3,t_POLMOD);
  gel(z,1) = RgX_copy(T);
  if (typ(x) != t_POL || varn(x) != varn(T) || lg(x) <= 3)
    a = gsqr(x);
  else
  {
    pari_sp av = avma;
    a = RgXQ_sqr(x, gel(z,1));
    a = gerepileupto(av, a);
  }
  gel(z,2) = a; return z;
}
/* Mod(x,X) * Mod(y,Y) */
static GEN
mul_polmod(GEN X, GEN Y, GEN x, GEN y)
{
  long T[3] = { evaltyp(t_POLMOD) | _evallg(3),0,0 };
  long vx = varn(X), vy = varn(Y);
  GEN z = cgetg(3,t_POLMOD);

  if (vx==vy) {
    pari_sp av;
    gel(z,1) = RgX_gcd(X,Y); av = avma;
    warn_coercion(X,Y,gel(z,1));
    gel(z,2) = gerepileupto(av, gmod(gmul(x, y), gel(z,1)));
    return z;
  }
  if (varncmp(vx, vy) < 0)
  { gel(z,1) = RgX_copy(X); gel(T,1) = Y; gel(T,2) = y; y = T; }
  else
  { gel(z,1) = RgX_copy(Y); gel(T,1) = X; gel(T,2) = x; x = T; }
  gel(z,2) = gmul(x, y); return z;
}

#if 0 /* used by 3M only */
/* set z = x+y and return 1 if x,y have the same sign
 * set z = x-y and return 0 otherwise */
static int
did_add(GEN x, GEN y, GEN *z)
{
  long tx = typ(x), ty = typ(y);
  if (tx == ty) switch(tx)
  {
    case t_INT: *z = addii(x,y); return 1;
    case t_FRAC: *z = addsub_frac(x,y,addii); return 1;
    case t_REAL:
      if (signe(x) == -signe(y))
      { *z = subrr(x,y); return 0; }
      else
      { *z = addrr(x,y); return 1; }
  }
  if (tx == t_REAL) switch(ty)
  {
    case t_INT:
      if (signe(x) == -signe(y))
      { *z = subri(x,y); return 0; }
      else
      { *z = addri(x,y); return 1; }
    case t_FRAC:
      if (signe(x) == -signe(gel(y,1)))
      { *z = gsub(x,y); return 0; }
      else
      { *z = gadd(x,y); return 1; }
  }
  else if (ty == t_REAL) switch(tx)
  {
    case t_INT:
      if (signe(x) == -signe(y))
      { *z = subir(x,y); return 0; }
      else
      { *z = addir(x,y); return 1; }
    case t_FRAC:
      if (signe(gel(x,1)) == -signe(y))
      { *z = gsub(x,y); return 0; }
      else
      { *z = gadd(x,y); return 1; }
  }
  *z = gadd(x,y); return 1;
}
#endif
/* x * I * y, x t_COMPLEX with non-intzero real part, y non-intzero "scalar" */
static GEN
mulcIR(GEN x, GEN y)
{
  GEN z = cgetg(3,t_COMPLEX);
  pari_sp av = avma;
  gel(z,1) = gerepileupto(av, gneg(gmul(y,gel(x,2))));
  gel(z,2) = gmul(y, gel(x,1));
  return z;

}
/* x,y COMPLEX */
static GEN
mulcc(GEN x, GEN y)
{
  GEN xr = gel(x,1), xi = gel(x,2);
  GEN yr = gel(y,1), yi = gel(y,2);
  GEN p1, p2, p3, p4, z;
  pari_sp tetpil, av;

  if (isintzero(xr))
  {
    if (isintzero(yr)) {
      av = avma;
      return gerepileupto(av, gneg(gmul(xi,yi)));
    }
    return mulcIR(y, xi);
  }
  if (isintzero(yr)) return mulcIR(x, yi);

  z = cgetg(3,t_COMPLEX); av = avma;
#if 0
  /* 3M method avoiding catastrophic cancellation, BUT loses accuracy due to
   * e.g. xr + xi if exponents differ */
  if (did_add(xr, xi, &p3))
  {
    if (did_add(yr, yi, &p4)) {
    /* R = xr*yr - xi*yi
     * I = (xr+xi)(yr+yi) - xr*yr - xi*yi */
      p1 = gmul(xr,yr);
      p2 = gmul(xi,yi); p2 = gneg(p2);
      p3 = gmul(p3, p4);
      p4 = gsub(p2, p1);
    } else {
    /* R = (xr + xi) * (yr - yi) + (xr * yi - xi * yr)
     * I = xr*yi + xi*yr */
      p1 = gmul(p3,p4);
      p3 = gmul(xr,yi);
      p4 = gmul(xi,yr);
      p2 = gsub(p3, p4);
    }
  } else {
    if (did_add(yr, yi, &p4)) {
     /* R = (xr - xi) * (yr + yi) + (xi * yr - xr * yi)
      * I = xr*yi +xi*yr */
      p1 = gmul(p3,p4);
      p3 = gmul(xr,yi);
      p4 = gmul(xi,yr);
      p2 = gsub(p4, p3);
    } else {
    /* R = xr*yr - xi*yi
     * I = -(xr-xi)(yr-yi) + xr*yr + xi*yi */
      p3 = gneg( gmul(p3, p4) );
      p1 = gmul(xr,yr);
      p2 = gmul(xi,yi);
      p4 = gadd(p1, p2);

      p2 = gneg(p2);
    }
  }
  tetpil = avma;
  gel(z,1) = gadd(p1,p2);
  gel(z,2) = gadd(p3,p4);
#else
  if (typ(xr)==t_INT && typ(yr)==t_INT && typ(xi)==t_INT && typ(yi)==t_INT)
  { /* 3M formula */
    p3 = addii(xr,xi);
    p4 = addii(yr,yi);
    p1 = mulii(xr,yr);
    p2 = mulii(xi,yi);
    p3 = mulii(p3,p4);
    p4 = addii(p2,p1);
    tetpil = avma;
    gel(z,1) = subii(p1,p2);
    gel(z,2) = subii(p3,p4);
    if (!signe(gel(z,2)))
      return gerepileuptoint((pari_sp)(z+3), gel(z,1));
  }
  else
  { /* naive 4M formula: avoid all loss of accuracy */
    p1 = gmul(xr,yr);
    p2 = gmul(xi,yi);
    p3 = gmul(xr,yi);
    p4 = gmul(xi,yr);
    tetpil = avma;
    gel(z,1) = gsub(p1,p2);
    gel(z,2) = gadd(p3,p4);
    if (isintzero(gel(z,2)))
    {
      cgiv(gel(z,2));
      return gerepileupto((pari_sp)(z+3), gel(z,1));
    }
  }
#endif

  gerepilecoeffssp(av,tetpil, z+1,2); return z;
}
/* x,y PADIC */
static GEN
mulpp(GEN x, GEN y) {
  long l = valp(x) + valp(y);
  pari_sp av;
  GEN z, t;
  if (!equalii(gel(x,2),gel(y,2))) pari_err_OP("*",x,y);
  if (!signe(gel(x,4))) return zeropadic(gel(x,2), l);
  if (!signe(gel(y,4))) return zeropadic(gel(x,2), l);

  t = (precp(x) > precp(y))? y: x;
  z = cgetp(t); setvalp(z,l); av = avma;
  affii(remii(mulii(gel(x,4),gel(y,4)), gel(t,3)), gel(z,4));
  avma = av; return z;
}
/* x,y QUAD */
static GEN
mulqq(GEN x, GEN y) {
  GEN z = cgetg(4,t_QUAD);
  GEN p1, p2, p3, p4, P = gel(x,1), b = gel(P,3), c = gel(P,2);
  pari_sp av, tetpil;
  if (!ZX_equal(P, gel(y,1))) pari_err_OP("*",x,y);

  gel(z,1) = ZX_copy(P); av = avma;
  p2 = gmul(gel(x,2),gel(y,2));
  p3 = gmul(gel(x,3),gel(y,3));
  p1 = gmul(gneg_i(c),p3);

  if (signe(b))
    p4 = gadd(gmul(gel(x,2),gel(y,3)), gmul(gel(x,3),gel(y,2)));
  else
  {
    p3 = gmul(gel(x,2),gel(y,3));
    p4 = gmul(gel(x,3),gel(y,2));
  }
  tetpil = avma;
  gel(z,2) = gadd(p2,p1);
  gel(z,3) = gadd(p4,p3);
  gerepilecoeffssp(av,tetpil,z+2,2); return z;
}

GEN
mulcxI(GEN x)
{
  GEN z;
  switch(typ(x))
  {
    case t_INT: case t_REAL: case t_FRAC:
      return mkcomplex(gen_0, x);
    case t_COMPLEX:
      if (isintzero(gel(x,1))) return gneg(gel(x,2));
      z = cgetg(3,t_COMPLEX);
      gel(z,1) = gneg(gel(x,2));
      gel(z,2) = gel(x,1); return z;
    default:
      return gmul(gen_I(), x);
  }
}
GEN
mulcxmI(GEN x)
{
  GEN z;
  switch(typ(x))
  {
    case t_INT: case t_REAL: case t_FRAC:
      return mkcomplex(gen_0, gneg(x));
    case t_COMPLEX:
      if (isintzero(gel(x,1))) return gel(x,2);
      z = cgetg(3,t_COMPLEX);
      gel(z,1) = gel(x,2);
      gel(z,2) = gneg(gel(x,1)); return z;
    default:
      return gmul(mkcomplex(gen_0, gen_m1), x);
  }
}
/* x * I^k */
GEN
mulcxpowIs(GEN x, long k)
{
  switch (k & 3)
  {
    case 1: return mulcxI(x);
    case 2: return gneg(x);
    case 3: return mulcxmI(x);
  }
  return x;
}

/* fill in coefficients of t_SER z from coeffs of t_POL y */
static GEN
fill_ser(GEN z, GEN y)
{
  long i, lx = lg(z), ly = lg(y);
  if (ly >= lx) {
    for (i = 2; i < lx; i++) gel(z,i) = gel(y,i);
  } else {
    for (i = 2; i < ly; i++) gel(z,i) = gel(y,i);
    for (     ; i < lx; i++) gel(z,i) = gen_0;
  }
  return normalize(z);
}

GEN
gmul(GEN x, GEN y)
{
  long tx, ty, lx, ly, vx, vy, i, l;
  pari_sp av, tetpil;
  GEN z, p1, p2;

  if (x == y) return gsqr(x);
  tx = typ(x); ty = typ(y);
  if (tx == ty) switch(tx)
  {
    case t_INT: return mulii(x,y);
    case t_REAL: return mulrr(x,y);
    case t_INTMOD: { GEN X = gel(x,1), Y = gel(y,1);
      z = cgetg(3,t_INTMOD);
      if (X==Y || equalii(X,Y))
        return mul_intmod_same(z, X, gel(x,2), gel(y,2));
      gel(z,1) = gcdii(X,Y);
      warn_coercion(X,Y,gel(z,1));
      av = avma; p1 = mulii(gel(x,2),gel(y,2));
      gel(z,2) = gerepileuptoint(av, remii(p1, gel(z,1))); return z;
    }
    case t_FRAC:
    {
      GEN x1 = gel(x,1), x2 = gel(x,2);
      GEN y1 = gel(y,1), y2 = gel(y,2);
      z=cgetg(3,t_FRAC);
      p1 = gcdii(x1, y2);
      if (!equali1(p1)) { x1 = diviiexact(x1,p1); y2 = diviiexact(y2,p1); }
      p1 = gcdii(x2, y1);
      if (!equali1(p1)) { x2 = diviiexact(x2,p1); y1 = diviiexact(y1,p1); }
      tetpil = avma;
      gel(z,2) = mulii(x2,y2);
      gel(z,1) = mulii(x1,y1);
      fix_frac_if_int_GC(z,tetpil); return z;
    }
    case t_COMPLEX: return mulcc(x, y);
    case t_PADIC: return mulpp(x, y);
    case t_QUAD: return mulqq(x, y);
    case t_FFELT: return FF_mul(x, y);
    case t_POLMOD:
      if (RgX_equal_var(gel(x,1), gel(y,1)))
        return mul_polmod_same(gel(x,1), gel(x,2), gel(y,2));
      return mul_polmod(gel(x,1), gel(y,1), gel(x,2), gel(y,2));
    case t_POL:
      vx = varn(x);
      vy = varn(y);
      if (vx != vy) {
        if (varncmp(vx, vy) < 0) return RgX_Rg_mul(x, y);
        else                     return RgX_Rg_mul(y, x);
      }
      return RgX_mul(x, y);

    case t_SER: {
      vx = varn(x);
      vy = varn(y);
      if (vx != vy) {
        if (varncmp(vx, vy) < 0) return mul_ser_scal(x, y);
        else                     return mul_ser_scal(y, x);
      }
      lx = lg(x);
      ly = lg(y); if (lx > ly) { lx = ly; swap(x, y); }
      if (lx == 2) return zeroser(vx, valp(x)+valp(y));
      av = avma; z = cgetg(lx,t_SER);
      z[1] = evalvalp(valp(x)+valp(y)) | evalvarn(vx) | evalsigne(1);
      x = ser2pol_i(x, lx);
      y = ser2pol_i(y, lx);
      y = RgXn_mul(x, y, lx-2);
      return gerepilecopy(av, fill_ser(z,y));
    }
    case t_QFI: return qficomp(x,y);
    case t_QFR: return qfrcomp(x,y);
    case t_RFRAC: return mul_rfrac(gel(x,1),gel(x,2), gel(y,1),gel(y,2));
    case t_MAT: return RgM_mul(x, y);

    case t_VECSMALL: /* multiply as permutation. cf perm_mul */
      z = cgetg_copy(x, &l);
      if (l != lg(y)) break;
      for (i=1; i<l; i++)
      {
        long yi = y[i];
        if (yi < 1 || yi >= l) pari_err_TYPE2("*",x,y);
        z[i] = x[yi];
      }
      return z;


    default:
      pari_err_TYPE2("*",x,y);
  }
  /* tx != ty */
  if (is_const_t(ty) && is_const_t(tx))  {
    if (tx > ty) { swap(x,y); lswap(tx,ty); }
    switch(tx) {
    case t_INT:
      switch(ty)
      {
        case t_REAL: return signe(x)? mulir(x,y): gen_0;
        case t_INTMOD:
          z = cgetg(3, t_INTMOD);
          return mul_intmod_same(z, gel(y,1), gel(y,2), modii(x, gel(y,1)));
        case t_FRAC:
          if (!signe(x)) return gen_0;
          z=cgetg(3,t_FRAC);
          p1 = gcdii(x,gel(y,2));
          if (equali1(p1))
          {
            avma = (pari_sp)z;
            gel(z,2) = icopy(gel(y,2));
            gel(z,1) = mulii(gel(y,1), x);
          }
          else
          {
            x = diviiexact(x,p1); tetpil = avma;
            gel(z,2) = diviiexact(gel(y,2), p1);
            gel(z,1) = mulii(gel(y,1), x);
            fix_frac_if_int_GC(z,tetpil);
          }
          return z;
        case t_COMPLEX: return signe(x)? mulRc(x, y): gen_0;
        case t_PADIC: return signe(x)? mulTp(x, y): gen_0;
        case t_QUAD: return mulRq(x,y);
        case t_FFELT: return FF_Z_mul(y,x);
      }

    case t_REAL:
      switch(ty)
      {
        case t_FRAC: return mulrfrac(x, y);
        case t_COMPLEX: return mulRc(x, y);
        case t_QUAD: return mulqf(y, x, realprec(x));
        default: pari_err_TYPE2("*",x,y);
      }

    case t_INTMOD:
      switch(ty)
      {
        case t_FRAC: { GEN X = gel(x,1);
          z = cgetg(3, t_INTMOD); p1 = Fp_mul(gel(y,1), gel(x,2), X);
          return div_intmod_same(z, X, p1, remii(gel(y,2), X));
        }
        case t_COMPLEX: return mulRc_direct(x,y);
        case t_PADIC: { GEN X = gel(x,1);
          z = cgetg(3, t_INTMOD);
          return mul_intmod_same(z, X, gel(x,2), padic_to_Fp(y, X));
        }
        case t_QUAD: return mulRq(x, y);
        case t_FFELT:
          if (!equalii(gel(x,1),FF_p_i(y)))
            pari_err_OP("*",x,y);
          return FF_Z_mul(y,gel(x,2));
      }

    case t_FRAC:
      switch(ty)
      {
        case t_COMPLEX: return mulRc(x, y);
        case t_PADIC: return signe(gel(x,1))? mulTp(x, y): gen_0;
        case t_QUAD:  return mulRq(x, y);
        case t_FFELT: return FF_Z_Z_muldiv(y, gel(x,1),gel(x,2));
      }

    case t_FFELT:
      pari_err_TYPE2("*",x,y);

    case t_COMPLEX:
      switch(ty)
      {
        case t_PADIC:
          return Zp_nosquare_m1(gel(y,2))? mulRc(y, x): mulTp(x, y);
        case t_QUAD:
          lx = precision(x); if (!lx) pari_err_OP("*",x,y);
          return mulqf(y, x, lx);
      }

    case t_PADIC: /* ty == t_QUAD */
      return (kro_quad(y,gel(x,2))== -1)? mulRq(x, y): mulTp(y, x);
    }
  }

  if (is_matvec_t(ty))
  {
    if (!is_matvec_t(tx))
    {
      if (is_noncalc_t(tx)) pari_err_TYPE2( "*",x,y); /* necessary if ly = 1 */
      z = cgetg_copy(y, &ly);
      for (i=1; i<ly; i++) gel(z,i) = gmul(x,gel(y,i));
      return z;
    }
    switch(tx)
    {
      case t_VEC:
        switch(ty) {
          case t_COL: return RgV_RgC_mul(x,y);
          case t_MAT: return RgV_RgM_mul(x,y);
        }
        break;
      case t_COL:
        switch(ty) {
          case t_VEC: return RgC_RgV_mul(x,y);
          case t_MAT: return RgC_RgM_mul(x,y);
        }
        break;
      case t_MAT:
        switch(ty) {
          case t_VEC: return RgM_RgV_mul(x,y);
          case t_COL: return RgM_RgC_mul(x,y);
        }
    }
  }
  if (is_matvec_t(tx))
  {
    if (is_noncalc_t(ty)) pari_err_TYPE2( "*",x,y); /* necessary if lx = 1 */
    z = cgetg_copy(x, &lx);
    for (i=1; i<lx; i++) gel(z,i) = gmul(y,gel(x,i));
    return z;
  }
  if (tx > ty) { swap(x,y); lswap(tx,ty); }
  /* tx < ty, !ismatvec(x and y) */

  if (ty == t_POLMOD) /* is_const_t(tx) in this case */
    return mul_polmod_scal(gel(y,1), gel(y,2), x);
  if (is_scalar_t(tx)) {
    if (tx == t_POLMOD) {
      vx = varn(gel(x,1));
      vy = gvar(y);
      if (vx != vy) {
        if (varncmp(vx,vy) > 0) return mul_scal(y, x, ty);
        return mul_polmod_scal(gel(x,1), gel(x,2), y);
      }
      /* error if ty == t_SER */
      av = avma; y = gmod(y, gel(x,1));
      return gerepileupto(av, mul_polmod_same(gel(x,1), gel(x,2), y));
    }
    return mul_scal(y, x, ty);
  }

  /* x and y are not scalars, nor matvec */
  vx = gvar(x);
  vy = gvar(y);
  if (vx != vy) /* x or y is treated as a scalar */
    return (varncmp(vx, vy) < 0)? mul_scal(x, y, tx)
                                : mul_scal(y, x, ty);
  /* vx = vy */
  switch(tx)
  {
    case t_POL:
      switch (ty)
      {
        case t_SER:
        {
          long vn;
          if (lg(x) == 2) return zeropol(vx);
          if (lg(y) == 2) return zeroser(vx, valp(y)+RgX_val(x));
          av = avma;
          vn = RgX_valrem(x, &x);
          /* take advantage of x = t^n ! */
          if (degpol(x)) {
            p1 = RgX_to_ser(x,lg(y));
            if (vn) settyp(x, t_VECSMALL); /* *new* x left on stack */
            p2 = gmul(p1,y);
            settyp(p1, t_VECSMALL); /* p1 left on stack */
          } else {
            avma = av;
            p2 = mul_ser_scal(y, gel(x,2));
          }
          setvalp(p2, valp(p2) + vn);
          return p2;
        }

        case t_RFRAC: return mul_rfrac_scal(gel(y,1),gel(y,2), x);
      }
      break;

    case t_SER:
      switch (ty)
      {
        case t_RFRAC:
          av = avma;
          return gerepileupto(av, gdiv(gmul(gel(y,1),x), gel(y,2)));
      }
      break;
  }
  pari_err_TYPE2("*",x,y);
  return NULL; /* LCOV_EXCL_LINE */
}

/* return a non-normalized result */
GEN
sqr_ser_part(GEN x, long l1, long l2)
{
  long i, j, l;
  pari_sp av;
  GEN Z, z, p1, p2;
  long mi;
  if (l2 < l1) return zeroser(varn(x), 2*valp(x));
  p2 = cgetg(l2+2, t_VECSMALL)+1; /* left on stack on exit */
  Z = cgetg(l2-l1+3, t_SER);
  Z[1] = evalvalp(2*valp(x)) | evalvarn(varn(x));
  z = Z + 2-l1;
  x += 2; mi = 0;
  for (i=0; i<l1; i++)
  {
    p2[i] = !isrationalzero(gel(x,i)); if (p2[i]) mi = i;
  }

  for (i=l1; i<=l2; i++)
  {
    p2[i] = !isrationalzero(gel(x,i)); if (p2[i]) mi = i;
    p1=gen_0; av=avma; l=((i+1)>>1) - 1;
    for (j=i-mi; j<=minss(l,mi); j++)
      if (p2[j] && p2[i-j]) p1 = gadd(p1, gmul(gel(x,j),gel(x,i-j)));
    p1 = gshift(p1,1);
    if ((i&1) == 0 && p2[i>>1])
      p1 = gadd(p1, gsqr(gel(x,i>>1)));
    gel(z,i) = gerepileupto(av,p1);
  }
  return Z;
}

GEN
gsqr(GEN x)
{
  long i, lx;
  pari_sp av, tetpil;
  GEN z, p1, p2, p3, p4;

  switch(typ(x))
  {
    case t_INT: return sqri(x);
    case t_REAL: return sqrr(x);
    case t_INTMOD: { GEN X = gel(x,1);
      z = cgetg(3,t_INTMOD);
      gel(z,2) = gerepileuptoint((pari_sp)z, remii(sqri(gel(x,2)), X));
      gel(z,1) = icopy(X); return z;
    }
    case t_FRAC: return sqrfrac(x);

    case t_COMPLEX:
      if (isintzero(gel(x,1))) {
        av = avma;
        return gerepileupto(av, gneg(gsqr(gel(x,2))));
      }
      z = cgetg(3,t_COMPLEX); av = avma;
      p1 = gadd(gel(x,1),gel(x,2));
      p2 = gsub(gel(x,1), gel(x,2));
      p3 = gmul(gel(x,1),gel(x,2));
      tetpil = avma;
      gel(z,1) = gmul(p1,p2);
      gel(z,2) = gshift(p3,1); gerepilecoeffssp(av,tetpil,z+1,2); return z;

    case t_PADIC:
      z = cgetg(5,t_PADIC);
      i = (absequaliu(gel(x,2), 2) && signe(gel(x,4)))? 1: 0;
      if (i && precp(x) == 1) i = 2; /* (1 + O(2))^2 = 1 + O(2^3) */
      z[1] = evalprecp(precp(x)+i) | evalvalp(valp(x)*2);
      gel(z,2) = icopy(gel(x,2));
      gel(z,3) = shifti(gel(x,3), i); av = avma;
      gel(z,4) = gerepileuptoint(av, remii(sqri(gel(x,4)), gel(z,3)));
      return z;

    case t_QUAD: z = cgetg(4,t_QUAD);
      p1 = gel(x,1);
      gel(z,1) = ZX_copy(p1); av = avma;
      p2 = gsqr(gel(x,2));
      p3 = gsqr(gel(x,3));
      p4 = gmul(gneg_i(gel(p1,2)),p3);

      if (gequal0(gel(p1,3)))
      {
        tetpil = avma;
        gel(z,2) = gerepile(av,tetpil,gadd(p4,p2));
        av = avma;
        p2 = gmul(gel(x,2),gel(x,3)); tetpil = avma;
        gel(z,3) = gerepile(av,tetpil,gmul2n(p2,1)); return z;
      }

      p1 = gmul2n(gmul(gel(x,2),gel(x,3)), 1);
      tetpil = avma;
      gel(z,2) = gadd(p2,p4);
      gel(z,3) = gadd(p1,p3);
      gerepilecoeffssp(av,tetpil,z+2,2); return z;

    case t_POLMOD:
      return sqr_polmod(gel(x,1), gel(x,2));

    case t_FFELT: return FF_sqr(x);

    case t_POL: return RgX_sqr(x);

    case t_SER:
      lx = lg(x);
      if (ser_isexactzero(x)) {
        GEN z = gcopy(x);
        setvalp(z, 2*valp(x));
        return z;
      }
      if (lx < 40)
        return normalize( sqr_ser_part(x, 0, lx-3) );
      else
      {
        pari_sp av = avma;
        GEN z = cgetg(lx,t_SER);
        z[1] = evalvalp(2*valp(x)) | evalvarn(varn(x)) | evalsigne(1);
        x = ser2pol_i(x,lx);
        x = RgXn_sqr(x, lx-2);
        return gerepilecopy(av, fill_ser(z,x));
      }

    case t_RFRAC: z = cgetg(3,t_RFRAC);
      gel(z,1) = gsqr(gel(x,1));
      gel(z,2) = gsqr(gel(x,2)); return z;

    case t_MAT: return RgM_sqr(x);
    case t_QFR: return qfrsqr(x);
    case t_QFI: return qfisqr(x);
    case t_VECSMALL:
      z = cgetg_copy(x, &lx);
      for (i=1; i<lx; i++)
      {
        long xi = x[i];
        if (xi < 1 || xi >= lx) pari_err_TYPE2("*",x,x);
        z[i] = x[xi];
      }
      return z;
  }
  pari_err_TYPE2("*",x,x);
  return NULL; /* LCOV_EXCL_LINE */
}

/********************************************************************/
/**                                                                **/
/**                           DIVISION                             **/
/**                                                                **/
/********************************************************************/
static GEN
div_rfrac_scal(GEN x, GEN y)
{
  pari_sp av = avma;
  GEN d = rfrac_denom_mul_scal(gel(x,2), y);
  return gerepileupto(av, gred_rfrac_simple(gel(x,1), d));
}
static GEN
div_scal_rfrac(GEN x, GEN y)
{
  GEN y1 = gel(y,1), y2 = gel(y,2);
  pari_sp av = avma;
  if (typ(y1) == t_POL && varn(y2) == varn(y1))
  {
    if (degpol(y1)) return gerepileupto(av, gred_rfrac_simple(gmul(x, y2), y1));
    y1 = gel(y1,2);
  }
  return RgX_Rg_mul(y2, gdiv(x,y1));
}
static GEN
div_rfrac(GEN x, GEN y)
{ return mul_rfrac(gel(x,1),gel(x,2), gel(y,2),gel(y,1)); }

static GEN
div_ser_scal(GEN x, GEN y) {
  long i, lx;
  GEN z;
  if (ser_isexactzero(x))
  {
    if (lg(x) == 2) return gcopy(x);
    return scalarser(gdiv(gel(x,2), y), varn(x), valp(x));
  }
  z = cgetg_copy(x, &lx); z[1] = x[1];
  for (i=2; i<lx; i++) gel(z,i) = gdiv(gel(x,i),y);
  return normalize(z);
}
GEN
ser_normalize(GEN x)
{
  long i, lx = lg(x);
  GEN c, z;
  if (lx == 2) return x;
  c = gel(x,2); if (gequal1(c)) return x;
  z = cgetg(lx, t_SER); z[1] = x[1]; gel(z,2) = gen_1;
  for (i=3; i<lx; i++) gel(z,i) = gdiv(gel(x,i),c);
  return z;
}

static GEN
div_T_scal(GEN x, GEN y, long tx) {
  switch(tx)
  {
    case t_POL: return RgX_Rg_div(x, y);
    case t_SER: return div_ser_scal(x, y);
    case t_RFRAC: return div_rfrac_scal(x,y);
  }
  pari_err_TYPE2("/",x,y);
  return NULL; /* LCOV_EXCL_LINE */
}

static GEN
div_scal_pol(GEN x, GEN y) {
  long ly = lg(y);
  pari_sp av;
  if (ly == 3) return scalarpol(gdiv(x,gel(y,2)), varn(y));
  if (isrationalzero(x)) return zeropol(varn(y));
  av = avma;
  return gerepileupto(av, gred_rfrac_simple(x,y));
}
static GEN
div_scal_ser(GEN x, GEN y) { /* TODO: improve */
  GEN z;
  long ly, i;
  if (gequal0(x)) { pari_sp av=avma; return gerepileupto(av, gmul(x, ginv(y))); }
  ly = lg(y); z = (GEN)pari_malloc(ly*sizeof(long));
  z[0] = evaltyp(t_SER) | evallg(ly);
  z[1] = evalsigne(1) | _evalvalp(0) | evalvarn(varn(y));
  gel(z,2) = x; for (i=3; i<ly; i++) gel(z,i) = gen_0;
  y = gdiv(z,y); pari_free(z); return y;
}
static GEN
div_scal_T(GEN x, GEN y, long ty) {
  switch(ty)
  {
    case t_POL: return div_scal_pol(x, y);
    case t_SER: return div_scal_ser(x, y);
    case t_RFRAC: return div_scal_rfrac(x, y);
  }
  pari_err_TYPE2("/",x,y);
  return NULL; /* LCOV_EXCL_LINE */
}

/* assume tx = ty = t_SER, same variable vx */
static GEN
div_ser(GEN x, GEN y, long vx)
{
  long i, j, l = valp(x) - valp(y), lx = lg(x), ly = lg(y);
  GEN y_lead, p1, p2, z;

  if (!signe(y)) pari_err_INV("div_ser", y);
  if (ser_isexactzero(x))
  {
    if (lx == 2) return zeroser(vx, l);
    return scalarser(gmul(gel(x,2),Rg_get_0(y)), varn(x), l);
  }
  y_lead = gel(y,2);
  if (gequal0(y_lead)) /* normalize denominator if leading term is 0 */
  {
    GEN y0 = y;
    pari_warn(warner,"normalizing a series with 0 leading term");
    for (l--, ly--,y++; ly > 2; l--, ly--, y++)
    {
      y_lead = gel(y,2);
      if (!gequal0(y_lead)) break;
    }
    if (ly <= 2) pari_err_INV("div_ser", y0);
  }
  if (ly < lx) lx = ly;
  p2 = cgetg(lx, t_VECSMALL); /* left on stack for efficiency */
  for (i=3; i<lx; i++)
  {
    p1 = gel(y,i);
    if (isrationalzero(p1)) p1 = NULL;
    gel(p2,i) = p1;
  }
  z = cgetg(lx,t_SER);
  z[1] = evalvalp(l) | evalvarn(vx) | evalsigne(1);
  gel(z,2) = gdiv(gel(x,2), y_lead);
  for (i=3; i<lx; i++)
  {
    pari_sp av = avma;
    p1 = gel(x,i);
    for (j=2, l=i; j<i; j++, l--)
      if (p2[l]) p1 = gsub(p1, gmul(gel(z,j), gel(p2,l)));
    gel(z,i) = gerepileupto(av, gdiv(p1, y_lead));
  }
  return normalize(z);
}
/* x,y compatible PADIC */
static GEN
divpp(GEN x, GEN y) {
  pari_sp av;
  long a, b;
  GEN z, M;

  if (!signe(gel(y,4))) pari_err_INV("divpp",y);
  if (!signe(gel(x,4))) return zeropadic(gel(x,2), valp(x)-valp(y));
  a = precp(x);
  b = precp(y); if (a > b) { M = gel(y,3); } else { M = gel(x,3); b = a; }
  z = cgetg(5, t_PADIC);
  z[1] = _evalprecp(b) | evalvalp(valp(x) - valp(y));
  gel(z,2) = icopy(gel(x,2));
  gel(z,3) = icopy(M); av = avma;
  gel(z,4) = gerepileuptoint(av, remii(mulii(gel(x,4), Fp_inv(gel(y,4), M)), M) );
  return z;
}
static GEN
div_polmod_same(GEN T, GEN x, GEN y)
{
  long v = varn(T);
  GEN a, z = cgetg(3, t_POLMOD);
  gel(z,1) = RgX_copy(T);
  if (typ(y) != t_POL || varn(y) != v || lg(y) <= 3)
    a = gdiv(x, y);
  else if (typ(x) != t_POL || varn(x) != v || lg(x) <= 3)
  {
    pari_sp av = avma;
    a = gerepileupto(av, gmul(x, RgXQ_inv(y, T)));
  }
  else if (degpol(T) == 2 && isint1(gel(T,4))) /* quadratic fields */
  {
    pari_sp av = avma;
    a = quad_polmod_mul(T, x, quad_polmod_conj(y, T));
    a = RgX_Rg_div(a, quad_polmod_norm(y, T));
    a = gerepileupto(av, a);
  }
  else
  {
    pari_sp av = avma;
    a = RgXQ_mul(x, ginvmod(y, gel(z,1)), gel(z,1));
    a = gerepileupto(av, a);
  }
  gel(z,2) = a; return z;
}
GEN
gdiv(GEN x, GEN y)
{
  long tx = typ(x), ty = typ(y), lx, ly, vx, vy, i;
  pari_sp av, tetpil;
  GEN z, p1, p2;

  if (tx == ty) switch(tx)
  {
    case t_INT:
      return Qdivii(x,y);

    case t_REAL: return divrr(x,y);
    case t_INTMOD: { GEN X = gel(x,1), Y = gel(y,1);
      z = cgetg(3,t_INTMOD);
      if (X==Y || equalii(X,Y))
        return div_intmod_same(z, X, gel(x,2), gel(y,2));
      gel(z,1) = gcdii(X,Y);
      warn_coercion(X,Y,gel(z,1));
      av = avma; p1 = mulii(gel(x,2), Fp_inv(gel(y,2), gel(z,1)));
      gel(z,2) = gerepileuptoint(av, remii(p1, gel(z,1))); return z;
    }
    case t_FRAC: {
      GEN x1 = gel(x,1), x2 = gel(x,2);
      GEN y1 = gel(y,1), y2 = gel(y,2);
      z = cgetg(3, t_FRAC);
      p1 = gcdii(x1, y1);
      if (!equali1(p1)) { x1 = diviiexact(x1,p1); y1 = diviiexact(y1,p1); }
      p1 = gcdii(x2, y2);
      if (!equali1(p1)) { x2 = diviiexact(x2,p1); y2 = diviiexact(y2,p1); }
      tetpil = avma;
      gel(z,2) = mulii(x2,y1);
      gel(z,1) = mulii(x1,y2);
      normalize_frac(z);
      fix_frac_if_int_GC(z,tetpil);
      return z;
    }
    case t_COMPLEX:
      if (isintzero(gel(y,1)))
      {
        y = gel(y,2);
        if (isintzero(gel(x,1))) return gdiv(gel(x,2), y);
        z = cgetg(3,t_COMPLEX);
        gel(z,1) = gdiv(gel(x,2), y);
        av = avma;
        gel(z,2) = gerepileupto(av, gneg(gdiv(gel(x,1), y)));
        return z;
      }
      av = avma; p1 = cxnorm(y); p2 = mulcc(x, conj_i(y)); tetpil = avma;
      return gerepile(av, tetpil, gdiv(p2,p1));

    case t_PADIC:
      if (!equalii(gel(x,2),gel(y,2))) pari_err_OP("/",x,y);
      return divpp(x, y);

    case t_QUAD:
      if (!ZX_equal(gel(x,1),gel(y,1))) pari_err_OP("/",x,y);
      av = avma; p1 = quadnorm(y); p2 = mulqq(x, conj_i(y)); tetpil = avma;
      return gerepile(av, tetpil, gdiv(p2,p1));

    case t_FFELT: return FF_div(x,y);

    case t_POLMOD:
      if (RgX_equal_var(gel(x,1), gel(y,1)))
        z = div_polmod_same(gel(x,1), gel(x,2), gel(y,2));
      else {
        av = avma;
        z = gerepileupto(av, gmul(x, ginv(y)));
      }
      return z;

    case t_POL:
      vx = varn(x);
      vy = varn(y);
      if (vx != vy) {
        if (varncmp(vx, vy) < 0) return RgX_Rg_div(x, y);
                            else return div_scal_pol(x, y);
      }
      if (!signe(y)) pari_err_INV("gdiv",y);
      if (lg(y) == 3) return RgX_Rg_div(x,gel(y,2));
      av = avma;
      return gerepileupto(av, gred_rfrac2(x,y));

    case t_SER:
      vx = varn(x);
      vy = varn(y);
      if (vx != vy) {
        if (varncmp(vx, vy) < 0) return div_ser_scal(x, y);
                            else return div_scal_ser(x, y);
      }
      return div_ser(x, y, vx);
    case t_RFRAC:
      vx = varn(gel(x,2));
      vy = varn(gel(y,2));
      if (vx != vy) {
        if (varncmp(vx, vy) < 0) return div_rfrac_scal(x, y);
                            else return div_scal_rfrac(x, y);
      }
      return div_rfrac(x,y);

    case t_QFI: av = avma; return gerepileupto(av, qficomp(x, ginv(y)));
    case t_QFR: av = avma; return gerepileupto(av, qfrcomp(x, ginv(y)));

    case t_MAT:
      av = avma; p1 = RgM_inv(y);
      if (!p1) pari_err_INV("gdiv",y);
      return gerepileupto(av, RgM_mul(x, p1));

    default: pari_err_TYPE2("/",x,y);
  }

  if (tx==t_INT && is_const_t(ty)) /* optimized for speed */
  {
    long s = signe(x);
    if (!s) {
      if (gequal0(y)) pari_err_INV("gdiv",y);
      switch (ty)
      {
      default: return gen_0;
      case t_INTMOD:
        z = cgetg(3,t_INTMOD);
        gel(z,1) = icopy(gel(y,1));
        gel(z,2) = gen_0; return z;
      case t_FFELT: return FF_zero(y);
      }
    }
    if (is_pm1(x)) {
      if (s > 0) return ginv(y);
      av = avma; return gerepileupto(av, ginv(gneg(y)));
    }
    switch(ty)
    {
      case t_REAL: return divir(x,y);
      case t_INTMOD:
        z = cgetg(3, t_INTMOD);
        return div_intmod_same(z, gel(y,1), modii(x, gel(y,1)), gel(y,2));
      case t_FRAC:
        z = cgetg(3,t_FRAC); p1 = gcdii(x,gel(y,1));
        if (equali1(p1))
        {
          avma = (pari_sp)z;
          gel(z,2) = icopy(gel(y,1));
          gel(z,1) = mulii(gel(y,2), x);
          normalize_frac(z);
          fix_frac_if_int(z);
        }
        else
        {
          x = diviiexact(x,p1); tetpil = avma;
          gel(z,2) = diviiexact(gel(y,1), p1);
          gel(z,1) = mulii(gel(y,2), x);
          normalize_frac(z);
          fix_frac_if_int_GC(z,tetpil);
        }
        return z;

      case t_FFELT: return Z_FF_div(x,y);
      case t_COMPLEX: return divRc(x,y);
      case t_PADIC: return divTp(x, y);
      case t_QUAD:
        av = avma; p1 = quadnorm(y); p2 = mulRq(x, conj_i(y)); tetpil = avma;
        return gerepile(av, tetpil, gdiv(p2,p1));
    }
  }
  if (gequal0(y))
  {
    if (is_matvec_t(tx) && lg(x) == 1) return gcopy(x);
    if (ty != t_MAT) pari_err_INV("gdiv",y);
  }

  if (is_const_t(tx) && is_const_t(ty)) switch(tx)
  {
    case t_REAL:
      switch(ty)
      {
        case t_INT: return divri(x,y);
        case t_FRAC:
          av = avma; z = divri(mulri(x,gel(y,2)), gel(y,1));
          return gerepileuptoleaf(av, z);
        case t_COMPLEX: return divRc(x, y);
        case t_QUAD: return divfq(x, y, realprec(x));
        default: pari_err_TYPE2("/",x,y);
      }

    case t_INTMOD:
      switch(ty)
      {
        case t_INT:
          z = cgetg(3, t_INTMOD);
          return div_intmod_same(z, gel(x,1), gel(x,2), modii(y, gel(x,1)));
        case t_FRAC: { GEN X = gel(x,1);
          z = cgetg(3,t_INTMOD); p1 = remii(mulii(gel(y,2), gel(x,2)), X);
          return div_intmod_same(z, X, p1, modii(gel(y,1), X));
        }
        case t_FFELT:
          if (!equalii(gel(x,1),FF_p_i(y)))
            pari_err_OP("/",x,y);
          return Z_FF_div(gel(x,2),y);

        case t_COMPLEX:
          av = avma;
          return gerepileupto(av, mulRc_direct(gdiv(x,cxnorm(y)), conj_i(y)));

        case t_QUAD:
          av = avma; p1 = quadnorm(y); p2 = gmul(x,conj_i(y)); tetpil = avma;
          return gerepile(av,tetpil, gdiv(p2,p1));

        case t_PADIC: { GEN X = gel(x,1);
          z = cgetg(3, t_INTMOD);
          return div_intmod_same(z, X, gel(x,2), padic_to_Fp(y, X));
        }
        case t_REAL: pari_err_TYPE2("/",x,y);
      }

    case t_FRAC:
      switch(ty)
      {
        case t_INT: z = cgetg(3, t_FRAC);
        p1 = gcdii(y,gel(x,1));
        if (equali1(p1))
        {
          avma = (pari_sp)z; tetpil = 0;
          gel(z,1) = icopy(gel(x,1));
        }
        else
        {
          y = diviiexact(y,p1); tetpil = avma;
          gel(z,1) = diviiexact(gel(x,1), p1);
        }
        gel(z,2) = mulii(gel(x,2),y);
        normalize_frac(z);
        if (tetpil) fix_frac_if_int_GC(z,tetpil);
        return z;

        case t_REAL:
          av=avma; p1=mulri(y,gel(x,2)); tetpil=avma;
          return gerepile(av, tetpil, divir(gel(x,1), p1));

        case t_INTMOD: { GEN Y = gel(y,1);
          z = cgetg(3,t_INTMOD); p1 = remii(mulii(gel(y,2),gel(x,2)), Y);
          return div_intmod_same(z, Y, modii(gel(x,1), Y), p1);
        }

        case t_FFELT: av=avma;
          return gerepileupto(av,Z_FF_div(gel(x,1),FF_Z_mul(y,gel(x,2))));

        case t_COMPLEX: return divRc(x, y);

        case t_PADIC:
          if (!signe(gel(x,1))) return gen_0;
          return divTp(x, y);

        case t_QUAD:
          av=avma; p1=quadnorm(y); p2=gmul(x,conj_i(y)); tetpil=avma;
          return gerepile(av,tetpil,gdiv(p2,p1));
      }

    case t_FFELT:
      switch (ty)
      {
        case t_INT: return FF_Z_Z_muldiv(x,gen_1,y);
        case t_FRAC: return FF_Z_Z_muldiv(x,gel(y,2),gel(y,1));
        case t_INTMOD:
          if (!equalii(gel(y,1),FF_p_i(x)))
            pari_err_OP("/",x,y);
          return FF_Z_Z_muldiv(x,gen_1,gel(y,2));
        default:
        pari_err_TYPE2("/",x,y);
      }
      break;

    case t_COMPLEX:
      switch(ty)
      {
        case t_INT: case t_REAL: case t_FRAC: return divcR(x,y);
        case t_INTMOD: return mulRc_direct(ginv(y), x);
        case t_PADIC:
          return Zp_nosquare_m1(gel(y,2))? divcR(x,y): divTp(x, y);
        case t_QUAD:
          lx = precision(x); if (!lx) pari_err_OP("/",x,y);
          return divfq(x, y, lx);
      }

    case t_PADIC:
      switch(ty)
      {
        case t_INT: case t_FRAC: { GEN p = gel(x,2);
          return signe(gel(x,4))? divpT(x, y)
                            : zeropadic(p, valp(x) - Q_pval(y,p));
        }
        case t_INTMOD: { GEN Y = gel(y,1);
          z = cgetg(3, t_INTMOD);
          return div_intmod_same(z, Y, padic_to_Fp(x, Y), gel(y,2));
        }
        case t_COMPLEX: case t_QUAD:
          av=avma; p1=gmul(x,conj_i(y)); p2=gnorm(y); tetpil=avma;
          return gerepile(av,tetpil,gdiv(p1,p2));

        case t_REAL: pari_err_TYPE2("/",x,y);
      }

    case t_QUAD:
      switch (ty)
      {
        case t_INT: case t_INTMOD: case t_FRAC:
          z = cgetg(4,t_QUAD);
          gel(z,1) = ZX_copy(gel(x,1));
          gel(z,2) = gdiv(gel(x,2), y);
          gel(z,3) = gdiv(gel(x,3), y); return z;
        case t_REAL: return divqf(x, y, realprec(y));
        case t_PADIC: return divTp(x, y);
        case t_COMPLEX:
          ly = precision(y); if (!ly) pari_err_OP("/",x,y);
          return divqf(x, y, ly);
      }
  }
  switch(ty) {
    case t_REAL: case t_INTMOD: case t_PADIC: case t_POLMOD:
      return gmul(x, ginv(y)); /* missing gerepile, for speed */
    case t_MAT:
      av = avma; p1 = RgM_inv(y);
      if (!p1) pari_err_INV("gdiv",y);
      return gerepileupto(av, gmul(x, p1));
    case t_VEC: case t_COL:
    case t_LIST: case t_STR: case t_VECSMALL: case t_CLOSURE:
      pari_err_TYPE2("/",x,y);
  }
  switch(tx) {
    case t_VEC: case t_COL: case t_MAT:
      z = cgetg_copy(x, &lx);
      for (i=1; i<lx; i++) gel(z,i) = gdiv(gel(x,i),y);
      return z;
    case t_LIST: case t_STR: case t_VECSMALL: case t_CLOSURE:
      pari_err_TYPE2("/",x,y);
  }

  vy = gvar(y);
  if (tx == t_POLMOD) { GEN X = gel(x,1);
    vx = varn(X);
    if (vx != vy) {
      if (varncmp(vx, vy) > 0) return div_scal_T(x, y, ty);
      retmkpolmod(gdiv(gel(x,2), y), RgX_copy(X));
    }
    /* y is POL, SER or RFRAC */
    av = avma;
    switch(ty)
    {
      case t_RFRAC: y = gmod(ginv(y), X); break;
      default: y = ginvmod(gmod(y,X), X);
    }
    return gerepileupto(av, mul_polmod_same(X, gel(x,2), y));
  }
  /* x and y are not both is_scalar_t. If one of them is scalar, it's not a
   * POLMOD (done already), hence its variable is NO_VARIABLE. If the other has
   * variable NO_VARIABLE, then the operation is incorrect */
  vx = gvar(x);
  if (vx != vy) { /* includes cases where one is scalar */
    if (varncmp(vx, vy) < 0) return div_T_scal(x, y, tx);
                        else return div_scal_T(x, y, ty);
  }
  switch(tx)
  {
    case t_POL:
      switch(ty)
      {
        case t_SER:
          if (lg(y) == 2)
            return zeroser(vx, RgX_val(x) - valp(y));
          p1 = RgX_to_ser(x,lg(y));
          p2 = div_ser(p1, y, vx);
          settyp(p1, t_VECSMALL); /* p1 left on stack */
          return p2;

        case t_RFRAC:
        {
          GEN y1 = gel(y,1), y2 = gel(y,2);
          if (typ(y1) == t_POL && varn(y1) == vx)
            return mul_rfrac_scal(y2, y1, x);
          av = avma;
          return gerepileupto(av, RgX_Rg_div(RgX_mul(y2, x), y1));
        }
      }
      break;

    case t_SER:
      switch(ty)
      {
        case t_POL:
          if (lg(x) == 2)
            return zeroser(vx, valp(x) - RgX_val(y));
          p1 = RgX_to_ser_inexact(y,lg(x));
          p2 = div_ser(x, p1, vx);
          settyp(p1, t_VECSMALL); /* p1 left on stack */
          return p2;
        case t_RFRAC:
          av = avma;
          return gerepileupto(av, gdiv(gmul(x,gel(y,2)), gel(y,1)));
      }
      break;

    case t_RFRAC:
      switch(ty)
      {
        case t_POL: return div_rfrac_pol(gel(x,1),gel(x,2), y);
        case t_SER:
          av = avma; z = RgX_to_ser_inexact(gel(x,2), lg(y));
          return gerepileupto(av, gdiv(gel(x,1), gmul(z,y)));
      }
      break;
  }
  pari_err_TYPE2("/",x,y);
  return NULL; /* LCOV_EXCL_LINE */
}

/********************************************************************/
/**                                                                **/
/**                     SIMPLE MULTIPLICATION                      **/
/**                                                                **/
/********************************************************************/
GEN
gmulsg(long s, GEN y)
{
  long ly, i;
  pari_sp av;
  GEN z;

  switch(typ(y))
  {
    case t_INT:  return mulsi(s,y);
    case t_REAL: return mulsr(s,y);
    case t_INTMOD: { GEN p = gel(y,1);
      z = cgetg(3,t_INTMOD);
      gel(z,2) = gerepileuptoint((pari_sp)z, modii(mulsi(s,gel(y,2)), p));
      gel(z,1) = icopy(p); return z;
    }
    case t_FFELT: return FF_Z_mul(y,stoi(s));
    case t_FRAC:
      if (!s) return gen_0;
      z = cgetg(3,t_FRAC);
      i = labs(s); i = ugcd(i, umodiu(gel(y,2), i));
      if (i == 1)
      {
        gel(z,2) = icopy(gel(y,2));
        gel(z,1) = mulis(gel(y,1), s);
      }
      else
      {
        gel(z,2) = divis(gel(y,2), i);
        gel(z,1) = mulis(gel(y,1), s/i);
        fix_frac_if_int(z);
      }
      return z;

    case t_COMPLEX: z = cgetg(3, t_COMPLEX);
      gel(z,1) = gmulsg(s,gel(y,1));
      gel(z,2) = gmulsg(s,gel(y,2)); return z;

    case t_PADIC:
      if (!s) return gen_0;
      av = avma; return gerepileupto(av, mulpp(cvtop2(stoi(s),y), y));

    case t_QUAD: z = cgetg(4, t_QUAD);
      gel(z,1) = ZX_copy(gel(y,1));
      gel(z,2) = gmulsg(s,gel(y,2));
      gel(z,3) = gmulsg(s,gel(y,3)); return z;

    case t_POLMOD:
      retmkpolmod(gmulsg(s,gel(y,2)), RgX_copy(gel(y,1)));

    case t_POL:
      if (!signe(y)) return RgX_copy(y);
      if (!s) return scalarpol(Rg_get_0(y), varn(y));
      z = cgetg_copy(y, &ly); z[1]=y[1];
      for (i=2; i<ly; i++) gel(z,i) = gmulsg(s,gel(y,i));
      return normalizepol_lg(z, ly);

    case t_SER:
      if (ser_isexactzero(y)) return gcopy(y);
      if (!s) return Rg_get_0(y);
      z = cgetg_copy(y, &ly); z[1]=y[1];
      for (i=2; i<ly; i++) gel(z,i) = gmulsg(s,gel(y,i));
      return normalize(z);

    case t_RFRAC:
      if (!s) return zeropol(varn(gel(y,2)));
      if (s == 1) return gcopy(y);
      if (s == -1) return gneg(y);
      return mul_rfrac_scal(gel(y,1), gel(y,2), stoi(s));

    case t_VEC: case t_COL: case t_MAT:
      z = cgetg_copy(y, &ly);
      for (i=1; i<ly; i++) gel(z,i) = gmulsg(s,gel(y,i));
      return z;
  }
  pari_err_TYPE("gmulsg",y);
  return NULL; /* LCOV_EXCL_LINE */
}

/********************************************************************/
/**                                                                **/
/**                       SIMPLE DIVISION                          **/
/**                                                                **/
/********************************************************************/

GEN
gdivgs(GEN x, long s)
{
  long tx = typ(x), lx, i;
  pari_sp av;
  GEN z, y;

  if (!s)
  {
    if (is_matvec_t(tx) && lg(x) == 1) return gcopy(x);
    pari_err_INV("gdivgs",gen_0);
  }
  switch(tx)
  {
    case t_INT:
      av = avma; z = divis_rem(x,s,&i);
      if (!i) return z;

      i = cgcd(s, i);
      avma=av; z = cgetg(3,t_FRAC);
      if (i == 1) y = icopy(x); else { s /= i; y = diviuexact(x, i); }
      gel(z,1) = y;
      gel(z,2) = stoi(s); normalize_frac(z); return z;

    case t_REAL:
      return divrs(x,s);

    case t_INTMOD:
      z = cgetg(3, t_INTMOD);
      return div_intmod_same(z, gel(x,1), gel(x,2), modsi(s, gel(x,1)));

    case t_FFELT: return FF_Z_Z_muldiv(x,gen_1,stoi(s));

    case t_FRAC: z = cgetg(3, t_FRAC);
      i = labs(s); i = ugcd(i, umodiu(gel(x,1), i));
      if (i == 1)
      {
        gel(z,2) = mulsi(s, gel(x,2));
        gel(z,1) = icopy(gel(x,1));
      }
      else
      {
        gel(z,2) = mulsi(s/i, gel(x,2));
        gel(z,1) = divis(gel(x,1), i);
      }
      normalize_frac(z);
      fix_frac_if_int(z); return z;

    case t_COMPLEX: z = cgetg(3, t_COMPLEX);
      gel(z,1) = gdivgs(gel(x,1),s);
      gel(z,2) = gdivgs(gel(x,2),s); return z;

    case t_PADIC: /* divpT */
    {
      GEN p = gel(x,2);
      if (!signe(gel(x,4))) return zeropadic(p, valp(x) - u_pval(s,p));
      av = avma;
      return gerepileupto(av, divpp(x, cvtop2(stoi(s),x)));
    }

    case t_QUAD: z = cgetg(4, t_QUAD);
      gel(z,1) = ZX_copy(gel(x,1));
      gel(z,2) = gdivgs(gel(x,2),s);
      gel(z,3) = gdivgs(gel(x,3),s); return z;

    case t_POLMOD:
      retmkpolmod(gdivgs(gel(x,2),s), RgX_copy(gel(x,1)));

    case t_RFRAC:
      if (s == 1) return gcopy(x);
      else if (s == -1) return gneg(x);
      return div_rfrac_scal(x, stoi(s));

    case t_POL: case t_SER:
      z = cgetg_copy(x, &lx); z[1] = x[1];
      for (i=2; i<lx; i++) gel(z,i) = gdivgs(gel(x,i),s);
      return z;
    case t_VEC: case t_COL: case t_MAT:
      z = cgetg_copy(x, &lx);
      for (i=1; i<lx; i++) gel(z,i) = gdivgs(gel(x,i),s);
      return z;

  }
  pari_err_TYPE2("/",x, stoi(s));
  return NULL; /* LCOV_EXCL_LINE */
}

/* True shift (exact multiplication by 2^n) */
GEN
gmul2n(GEN x, long n)
{
  long lx, i, k, l;
  GEN z, a, b;

  switch(typ(x))
  {
    case t_INT:
      if (n>=0) return shifti(x,n);
      if (!signe(x)) return gen_0;
      l = vali(x); n = -n;
      if (n<=l) return shifti(x,-n);
      z = cgetg(3,t_FRAC);
      gel(z,1) = shifti(x,-l);
      gel(z,2) = int2n(n-l); return z;

    case t_REAL:
      return shiftr(x,n);

    case t_INTMOD: b = gel(x,1); a = gel(x,2);
      z = cgetg(3,t_INTMOD);
      if (n <= 0) return div_intmod_same(z, b, a, modii(int2n(-n), b));
      gel(z,2) = gerepileuptoint((pari_sp)z, modii(shifti(a,n), b));
      gel(z,1) = icopy(b); return z;

    case t_FFELT: return FF_mul2n(x,n);

    case t_FRAC: a = gel(x,1); b = gel(x,2);
      l = vali(a);
      k = vali(b);
      if (n+l >= k)
      {
        if (expi(b) == k) return shifti(a,n-k); /* b power of 2 */
        l = n-k; k = -k;
      }
      else
      {
        k = -(l+n); l = -l;
      }
      z = cgetg(3,t_FRAC);
      gel(z,1) = shifti(a,l);
      gel(z,2) = shifti(b,k); return z;

    case t_COMPLEX: z = cgetg(3,t_COMPLEX);
      gel(z,1) = gmul2n(gel(x,1),n);
      gel(z,2) = gmul2n(gel(x,2),n); return z;

    case t_QUAD: z = cgetg(4,t_QUAD);
      gel(z,1) = ZX_copy(gel(x,1));
      gel(z,2) = gmul2n(gel(x,2),n);
      gel(z,3) = gmul2n(gel(x,3),n); return z;

    case t_POLMOD:
      retmkpolmod(gmul2n(gel(x,2),n), RgX_copy(gel(x,1)));

    case t_POL:
      z = cgetg_copy(x, &lx); z[1] = x[1];
      for (i=2; i<lx; i++) gel(z,i) = gmul2n(gel(x,i),n);
      return normalizepol_lg(z, lx); /* needed if char = 2 */
    case t_SER:
      if (ser_isexactzero(x)) return gcopy(x);
      z = cgetg_copy(x, &lx); z[1] = x[1];
      for (i=2; i<lx; i++) gel(z,i) = gmul2n(gel(x,i),n);
      return normalize(z); /* needed if char = 2 */
    case t_VEC: case t_COL: case t_MAT:
      z = cgetg_copy(x, &lx);
      for (i=1; i<lx; i++) gel(z,i) = gmul2n(gel(x,i),n);
      return z;

    case t_RFRAC: /* int2n wrong if n < 0 */
      return mul_rfrac_scal(gel(x,1),gel(x,2), gmul2n(gen_1,n));

    case t_PADIC: /* int2n wrong if n < 0 */
      return gmul(gmul2n(gen_1,n),x);
  }
  pari_err_TYPE("gmul2n",x);
  return NULL; /* LCOV_EXCL_LINE */
}

/*******************************************************************/
/*                                                                 */
/*                              INVERSE                            */
/*                                                                 */
/*******************************************************************/
static GEN
inv_polmod(GEN T, GEN x)
{
  GEN z = cgetg(3,t_POLMOD), a;
  gel(z,1) = RgX_copy(T);
  if (typ(x) != t_POL || varn(x) != varn(T) || lg(x) <= 3)
    a = ginv(x);
  else
  {
    if (lg(T) == 5) /* quadratic fields */
      a = RgX_Rg_div(quad_polmod_conj(x,T), quad_polmod_norm(x,T));
    else
      a = RgXQ_inv(x, T);
  }
  gel(z,2) = a; return z;
}

GEN
ginv(GEN x)
{
  long s;
  pari_sp av, tetpil;
  GEN z, y, p1, p2;

  switch(typ(x))
  {
    case t_INT:
      if (is_pm1(x)) return icopy(x);
      s = signe(x); if (!s) pari_err_INV("ginv",gen_0);
      z = cgetg(3,t_FRAC);
      gel(z,1) = s<0? gen_m1: gen_1;
      gel(z,2) = absi(x); return z;

    case t_REAL: return invr(x);

    case t_INTMOD: z=cgetg(3,t_INTMOD);
      gel(z,1) = icopy(gel(x,1));
      gel(z,2) = Fp_inv(gel(x,2),gel(x,1)); return z;

    case t_FRAC: {
      GEN a = gel(x,1), b = gel(x,2);
      s = signe(a);
      if (is_pm1(a)) return s > 0? icopy(b): negi(b);
      z = cgetg(3,t_FRAC);
      gel(z,1) = icopy(b);
      gel(z,2) = icopy(a);
      normalize_frac(z); return z;
    }
    case t_COMPLEX:
      av=avma;
      p1=cxnorm(x);
      p2=mkcomplex(gel(x,1), gneg(gel(x,2)));
      tetpil=avma;
      return gerepile(av,tetpil,divcR(p2,p1));

    case t_QUAD:
      av=avma; p1=gnorm(x); p2=conj_i(x); tetpil=avma;
      return gerepile(av,tetpil,gdiv(p2,p1));

    case t_PADIC: z = cgetg(5,t_PADIC);
      if (!signe(gel(x,4))) pari_err_INV("ginv",x);
      z[1] = _evalprecp(precp(x)) | evalvalp(-valp(x));
      gel(z,2) = icopy(gel(x,2));
      gel(z,3) = icopy(gel(x,3));
      gel(z,4) = Fp_inv(gel(x,4),gel(z,3)); return z;

    case t_POLMOD: return inv_polmod(gel(x,1), gel(x,2));
    case t_FFELT: return FF_inv(x);
    case t_POL: return gred_rfrac_simple(gen_1,x);
    case t_SER: return gdiv(gen_1,x);

    case t_RFRAC:
    {
      GEN n = gel(x,1), d = gel(x,2);
      pari_sp av = avma, ltop;
      if (gequal0(n)) pari_err_INV("ginv",x);

      n = simplify_shallow(n);
      if (typ(n) != t_POL || varn(n) != varn(d))
      {
        if (gequal1(n)) { avma = av; return RgX_copy(d); }
        ltop = avma;
        z = RgX_Rg_div(d,n);
      } else {
        ltop = avma;
        z = cgetg(3,t_RFRAC);
        gel(z,1) = RgX_copy(d);
        gel(z,2) = RgX_copy(n);
      }
      stackdummy(av, ltop);
      return z;
    }

    case t_QFR:
      av = avma; z = cgetg(5, t_QFR);
      gel(z,1) = gel(x,1);
      gel(z,2) = negi( gel(x,2) );
      gel(z,3) = gel(x,3);
      gel(z,4) = negr( gel(x,4) );
      return gerepileupto(av, redreal(z));

    case t_QFI:
      y = gcopy(x);
      if (!equalii(gel(x,1),gel(x,2)) && !equalii(gel(x,1),gel(x,3)))
        togglesign(gel(y,2));
      return y;
    case t_MAT:
      y = RgM_inv(x);
      if (!y) pari_err_INV("ginv",x);
      return y;
    case t_VECSMALL:
    {
      long i, lx = lg(x)-1;
      y = zero_zv(lx);
      for (i=1; i<=lx; i++)
      {
        long xi = x[i];
        if (xi<1 || xi>lx || y[xi])
          pari_err_TYPE("ginv [not a permutation]", x);
        y[xi] = i;
      }
      return y;
    }
  }
  pari_err_TYPE("inverse",x);
  return NULL; /* LCOV_EXCL_LINE */
}
