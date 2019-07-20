/* Copyright (C) 2000-2005  The PARI group.

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
/*         QUADRATIC POLYNOMIAL ASSOCIATED TO A DISCRIMINANT       */
/*                                                                 */
/*******************************************************************/

void
check_quaddisc(GEN x, long *s, long *r, const char *f)
{
  if (typ(x) != t_INT) pari_err_TYPE(f,x);
  *s = signe(x);
  if (Z_issquare(x)) pari_err_DOMAIN(f,"issquare(disc)","=", gen_1,x);
  *r = mod4(x); if (*s < 0 && *r) *r = 4 - *r;
  if (*r > 1) pari_err_DOMAIN(f,"disc % 4",">", gen_1,x);
}
void
check_quaddisc_real(GEN x, long *r, const char *f)
{
  long sx; check_quaddisc(x, &sx, r, f);
  if (sx < 0) pari_err_DOMAIN(f, "disc","<",gen_0,x);
}
void
check_quaddisc_imag(GEN x, long *r, const char *f)
{
  long sx; check_quaddisc(x, &sx, r, f);
  if (sx > 0) pari_err_DOMAIN(f, "disc",">",gen_0,x);
}

/* X^2 + b X + c is the canonical quadratic t_POL of discriminant D.
 * Dodd is non-zero iff D is odd */
static void
quadpoly_bc(GEN D, long Dodd, GEN *b, GEN *c)
{
  if (Dodd)
  {
    pari_sp av = avma;
    *b = gen_m1;
    *c = gerepileuptoint(av, shifti(subui(1,D), -2));
  }
  else
  {
    *b = gen_0;
    *c = shifti(D,-2); togglesign(*c);
  }
}
/* X^2 - X - (D-1)/4 or X^2 - D/4 */
GEN
quadpoly(GEN D)
{
  long Dmod4, s;
  GEN b, c, y = cgetg(5,t_POL);
  check_quaddisc(D, &s, &Dmod4, "quadpoly");
  y[1] = evalsigne(1) | evalvarn(0);
  quadpoly_bc(D, Dmod4, &b,&c);
  gel(y,2) = c;
  gel(y,3) = b;
  gel(y,4) = gen_1; return y;
}

GEN
quadpoly0(GEN x, long v)
{
  GEN T = quadpoly(x);
  if (v > 0) setvarn(T, v);
  return T;
}

GEN
quadgen(GEN x)
{ retmkquad(quadpoly(x), gen_0, gen_1); }

GEN
quadgen0(GEN x, long v)
{
  if (v==-1) v = fetch_user_var("w");
  retmkquad(quadpoly0(x, v), gen_0, gen_1);
}

/***********************************************************************/
/**                                                                   **/
/**                      BINARY QUADRATIC FORMS                       **/
/**                                                                   **/
/***********************************************************************/
GEN
qfi(GEN x, GEN y, GEN z)
{
  if (signe(x) < 0) pari_err_IMPL("negative definite t_QFI");
  retmkqfi(icopy(x),icopy(y),icopy(z));
}
GEN
qfr(GEN x, GEN y, GEN z, GEN d)
{
  if (typ(d) != t_REAL) pari_err_TYPE("qfr",d);
  retmkqfr(icopy(x),icopy(y),icopy(z),rcopy(d));
}

GEN
Qfb0(GEN x, GEN y, GEN z, GEN d, long prec)
{
  pari_sp av = avma;
  GEN D;
  long s, r;
  if (typ(x)!=t_INT) pari_err_TYPE("Qfb",x);
  if (typ(y)!=t_INT) pari_err_TYPE("Qfb",y);
  if (typ(z)!=t_INT) pari_err_TYPE("Qfb",z);
  D = qfb_disc3(x,y,z);
  check_quaddisc(D, &s, &r, "Qfb");
  avma = av;
  if (s < 0) return qfi(x, y, z);

  d = d? gtofp(d,prec): real_0(prec);
  return qfr(x,y,z,d);
}

/* composition */
static void
qfb_sqr(GEN z, GEN x)
{
  GEN c, d1, x2, v1, v2, c3, m, p1, r;

  d1 = bezout(gel(x,2),gel(x,1),&x2, NULL); /* usually 1 */
  c = gel(x,3);
  m = mulii(c,x2);
  if (equali1(d1))
    v1 = v2 = gel(x,1);
  else
  {
    v1 = diviiexact(gel(x,1),d1);
    v2 = mulii(v1, gcdii(d1,c)); /* = v1 iff x primitive */
    c = mulii(c, d1);
  }
  togglesign(m);
  r = modii(m,v2);
  p1 = mulii(r, v1);
  c3 = addii(c, mulii(r,addii(gel(x,2),p1)));
  gel(z,1) = mulii(v1,v2);
  gel(z,2) = addii(gel(x,2), shifti(p1,1));
  gel(z,3) = diviiexact(c3,v2);
}
/* z <- x * y */
static void
qfb_comp(GEN z, GEN x, GEN y)
{
  GEN n, c, d, y1, v1, v2, c3, m, p1, r;

  if (x == y) { qfb_sqr(z,x); return; }
  n = shifti(subii(gel(y,2),gel(x,2)), -1);
  v1 = gel(x,1);
  v2 = gel(y,1);
  c  = gel(y,3);
  d = bezout(v2,v1,&y1,NULL);
  if (equali1(d))
    m = mulii(y1,n);
  else
  {
    GEN s = subii(gel(y,2), n);
    GEN x2, y2, d1 = bezout(s,d,&x2,&y2); /* x2 s + y2 (x1 v1 + y1 v2) = d1 */
    if (!equali1(d1))
    {
      v1 = diviiexact(v1,d1);
      v2 = diviiexact(v2,d1); /* gcd = 1 iff x or y primitive */
      v1 = mulii(v1, gcdii(c,gcdii(gel(x,3),gcdii(d1,n))));
      c = mulii(c, d1);
    }
    m = addii(mulii(mulii(y1,y2),n), mulii(gel(y,3),x2));
  }
  togglesign(m);
  r = modii(m, v1);
  p1 = mulii(r, v2);
  c3 = addii(c, mulii(r,addii(gel(y,2),p1)));
  gel(z,1) = mulii(v1,v2);
  gel(z,2) = addii(gel(y,2), shifti(p1,1));
  gel(z,3) = diviiexact(c3,v1);
}

static GEN redimag_av(pari_sp av, GEN q);
static GEN
qficomp0(GEN x, GEN y, int raw)
{
  pari_sp av = avma;
  GEN z = cgetg(4,t_QFI);
  qfb_comp(z, x,y);
  if (raw) return gerepilecopy(av,z);
  return redimag_av(av, z);
}
static GEN
qfrcomp0(GEN x, GEN y, int raw)
{
  pari_sp av = avma;
  GEN z = cgetg(5,t_QFR);
  qfb_comp(z, x,y); gel(z,4) = addrr(gel(x,4),gel(y,4));
  if (raw) return gerepilecopy(av,z);
  return gerepileupto(av, redreal(z));
}
GEN
qfrcomp(GEN x, GEN y) { return qfrcomp0(x,y,0); }
GEN
qfrcompraw(GEN x, GEN y) { return qfrcomp0(x,y,1); }
GEN
qficomp(GEN x, GEN y) { return qficomp0(x,y,0); }
GEN
qficompraw(GEN x, GEN y) { return qficomp0(x,y,1); }
GEN
qfbcompraw(GEN x, GEN y)
{
  long tx = typ(x);
  if (typ(y) != tx) pari_err_TYPE2("*",x,y);
  switch(tx) {
    case t_QFI: return qficompraw(x,y);
    case t_QFR: return qfrcompraw(x,y);
  }
  pari_err_TYPE("composition",x);
  return NULL; /* LCOV_EXCL_LINE */
}

static GEN
qfisqr0(GEN x, long raw)
{
  pari_sp av = avma;
  GEN z = cgetg(4,t_QFI);

  if (typ(x)!=t_QFI) pari_err_TYPE("composition",x);
  qfb_sqr(z,x);
  if (raw) return gerepilecopy(av,z);
  return redimag_av(av, z);
}
static GEN
qfrsqr0(GEN x, long raw)
{
  pari_sp av = avma;
  GEN z = cgetg(5,t_QFR);

  if (typ(x)!=t_QFR) pari_err_TYPE("composition",x);
  qfb_sqr(z,x); gel(z,4) = shiftr(gel(x,4),1);
  if (raw) return gerepilecopy(av,z);
  return gerepileupto(av, redreal(z));
}
GEN
qfrsqr(GEN x) { return qfrsqr0(x,0); }
GEN
qfrsqrraw(GEN x) { return qfrsqr0(x,1); }
GEN
qfisqr(GEN x) { return qfisqr0(x,0); }
GEN
qfisqrraw(GEN x) { return qfisqr0(x,1); }

static GEN
qfr_1_by_disc(GEN D, long prec)
{
  GEN y = cgetg(5,t_QFR), isqrtD;
  pari_sp av = avma;
  long r;

  check_quaddisc_real(D, &r, "qfr_1_by_disc");
  gel(y,1) = gen_1; isqrtD = sqrti(D);
  if ((r & 1) != mod2(isqrtD)) /* we know isqrtD > 0 */
    isqrtD = gerepileuptoint(av, subiu(isqrtD,1));
  gel(y,2) = isqrtD; av = avma;
  gel(y,3) = gerepileuptoint(av, shifti(subii(sqri(isqrtD), D),-2));
  gel(y,4) = real_0(prec); return y;
}
GEN
qfr_1(GEN x)
{
  if (typ(x) != t_QFR) pari_err_TYPE("qfr_1",x);
  return qfr_1_by_disc(qfb_disc(x), precision(gel(x,4)));
}

static void
qfr_1_fill(GEN y, struct qfr_data *S)
{
  pari_sp av = avma;
  GEN y2 = S->isqrtD;
  gel(y,1) = gen_1;
  if (mod2(S->D) != mod2(y2)) y2 = subiu(y,1);
  gel(y,2) = y2; av = avma;
  gel(y,3) = gerepileuptoint(av, shifti(subii(sqri(y2), S->D),-2));
}
static GEN
qfr5_1(struct qfr_data *S, long prec)
{
  GEN y = cgetg(6, t_VEC);
  qfr_1_fill(y, S);
  gel(y,4) = gen_0;
  gel(y,5) = real_1(prec); return y;
}
static GEN
qfr3_1(struct qfr_data *S)
{
  GEN y = cgetg(4, t_VEC);
  qfr_1_fill(y, S); return y;
}

/* Assume D < 0 is the discriminant of a t_QFI */
static GEN
qfi_1_by_disc(GEN D)
{
  GEN b,c, y = cgetg(4,t_QFI);
  quadpoly_bc(D, mod2(D), &b,&c);
  if (b == gen_m1) b = gen_1;
  gel(y,1) = gen_1;
  gel(y,2) = b;
  gel(y,3) = c; return y;
}
GEN
qfi_1(GEN x)
{
  if (typ(x) != t_QFI) pari_err_TYPE("qfi_1",x);
  return qfi_1_by_disc(qfb_disc(x));
}

static GEN
invraw(GEN x)
{
  GEN y = gcopy(x);
  if (typ(y) == t_QFR) togglesign(gel(y,4));
  togglesign(gel(y,2)); return y;
}
GEN
qfrpowraw(GEN x, long n)
{
  pari_sp av = avma;
  long m;
  GEN y;

  if (typ(x) != t_QFR) pari_err_TYPE("qfrpowraw",x);
  if (!n) return qfr_1(x);
  if (n== 1) return gcopy(x);
  if (n==-1) return invraw(x);

  y = NULL; m = labs(n);
  for (; m>1; m>>=1)
  {
    if (m&1) y = y? qfrcompraw(y,x): x;
    x = qfrsqrraw(x);
  }
  y = y? qfrcompraw(y,x): x;
  if (n < 0) y = invraw(y);
  return gerepileupto(av,y);
}
GEN
qfipowraw(GEN x, long n)
{
  pari_sp av = avma;
  long m;
  GEN y;

  if (typ(x) != t_QFI) pari_err_TYPE("qfipow",x);
  if (!n) return qfi_1(x);
  if (n== 1) return gcopy(x);
  if (n==-1) return invraw(x);

  y = NULL; m = labs(n);
  for (; m>1; m>>=1)
  {
    if (m&1) y = y? qficompraw(y,x): x;
    x = qfisqrraw(x);
  }
  y = y? qficompraw(y,x): x;
  if (n < 0) y = invraw(y);
  return gerepileupto(av,y);
}

GEN
qfbpowraw(GEN x, long n)
{ return (typ(x)==t_QFI)? qfipowraw(x,n): qfrpowraw(x,n); }

static long
parteucl(GEN L, GEN *d, GEN *v3, GEN *v, GEN *v2)
{
  long z;
  *v = gen_0; *v2 = gen_1;
  for (z=0; abscmpii(*v3,L) > 0; z++)
  {
    GEN t3, t2 = subii(*v, mulii(truedvmdii(*d,*v3,&t3),*v2));
    *v = *v2; *d = *v3; *v2 = t2; *v3 = t3;
  }
  return z;
}

/* composition: Shanks' NUCOMP & NUDUPL */
/* L = floor((|d|/4)^(1/4)) */
GEN
nucomp(GEN x, GEN y, GEN L)
{
  pari_sp av = avma;
  long z;
  GEN a, a1, a2, b2, b, d, d1, g, n, p1, q1, q2, s, u, u1, v, v2, v3, Q;

  if (x==y) return nudupl(x,L);
  if (typ(x) != t_QFI) pari_err_TYPE("nucomp",x);
  if (typ(y) != t_QFI) pari_err_TYPE("nucomp",y);

  if (abscmpii(gel(x,1),gel(y,1)) < 0) swap(x, y);
  s = shifti(addii(gel(x,2),gel(y,2)), -1);
  n = subii(gel(y,2), s);
  a1 = gel(x,1);
  a2 = gel(y,1); d = bezout(a2,a1,&u,&v);
  if (equali1(d)) { a = negi(mulii(u,n)); d1 = d; }
  else if (dvdii(s,d)) /* d | s */
  {
    a = negi(mulii(u,n)); d1 = d;
    a1 = diviiexact(a1, d1);
    a2 = diviiexact(a2, d1);
    s = diviiexact(s, d1);
  }
  else
  {
    GEN p2, l;
    d1 = bezout(s,d,&u1,NULL);
    if (!equali1(d1))
    {
      a1 = diviiexact(a1,d1);
      a2 = diviiexact(a2,d1);
      s = diviiexact(s,d1);
      d = diviiexact(d,d1);
    }
    p1 = remii(gel(x,3),d);
    p2 = remii(gel(y,3),d);
    l = modii(mulii(negi(u1), addii(mulii(u,p1),mulii(v,p2))), d);
    a = subii(mulii(l,diviiexact(a1,d)), mulii(u,diviiexact(n,d)));
  }
  a = modii(a,a1); p1 = subii(a,a1); if (abscmpii(a,p1) > 0) a = p1;
  d = a1; v3 = a; z = parteucl(L, &d,&v3, &v,&v2);
  Q = cgetg(4,t_QFI);
  if (!z) {
    g = diviiexact(addii(mulii(v3,s),gel(y,3)), d);
    b = a2;
    b2 = gel(y,2);
    v2 = d1;
    gel(Q,1) = mulii(d,b);
  } else {
    GEN e, q3, q4;
    if (z&1) { v3 = negi(v3); v2 = negi(v2); }
    b = diviiexact(addii(mulii(a2,d), mulii(n,v)), a1);
    e = diviiexact(addii(mulii(s,d),mulii(gel(y,3),v)), a1);
    q3 = mulii(e,v2);
    q4 = subii(q3,s);
    b2 = addii(q3,q4);
    g = diviiexact(q4,v);
    if (!equali1(d1)) { v2 = mulii(d1,v2); v = mulii(d1,v); b2 = mulii(d1,b2); }
    gel(Q,1) = addii(mulii(d,b), mulii(e,v));
  }
  q1 = mulii(b, v3);
  q2 = addii(q1,n);
  gel(Q,2) = addii(b2, z? addii(q1,q2): shifti(q1, 1));
  gel(Q,3) = addii(mulii(v3,diviiexact(q2,d)), mulii(g,v2));
  return redimag_av(av, Q);
}

GEN
nudupl(GEN x, GEN L)
{
  pari_sp av = avma;
  long z;
  GEN u, v, d, d1, p1, a, b, c, a2, b2, c2, Q, v2, v3, g;

  if (typ(x) != t_QFI) pari_err_TYPE("nudupl",x);
  a = gel(x,1);
  b = gel(x,2);
  d1 = bezout(b,a, &u,NULL);
  if (!equali1(d1))
  {
    a = diviiexact(a, d1);
    b = diviiexact(b, d1);
  }
  c = modii(negi(mulii(u,gel(x,3))), a);
  p1 = subii(c,a); if (abscmpii(c,p1) > 0) c = p1;
  d = a; v3 = c; z = parteucl(L, &d,&v3, &v,&v2);
  a2 = sqri(d);
  c2 = sqri(v3);
  Q = cgetg(4,t_QFI);
  if (!z) {
    g = diviiexact(addii(mulii(v3,b),gel(x,3)), d);
    b2 = gel(x,2);
    v2 = d1;
    gel(Q,1) = a2;
  } else {
    GEN e;
    if (z&1) { v = negi(v); d = negi(d); }
    e = diviiexact(addii(mulii(gel(x,3),v), mulii(b,d)), a);
    g = diviiexact(subii(mulii(e,v2), b), v);
    b2 = addii(mulii(e,v2), mulii(v,g));
    if (!equali1(d1)) { b2 = mulii(d1,b2); v = mulii(d1,v); v2 = mulii(d1,v2); }
    gel(Q,1) = addii(a2, mulii(e,v));
  }
  gel(Q,2) = addii(b2, subii(sqri(addii(d,v3)), addii(a2,c2)));
  gel(Q,3) = addii(c2, mulii(g,v2));
  return redimag_av(av, Q);
}

static GEN
mul_nucomp(void *l, GEN x, GEN y) { return nucomp(x, y, (GEN)l); }
static GEN
mul_nudupl(void *l, GEN x) { return nudupl(x, (GEN)l); }
GEN
nupow(GEN x, GEN n, GEN L)
{
  pari_sp av;
  GEN y, D;

  if (typ(n) != t_INT) pari_err_TYPE("nupow",n);
  if (typ(x) != t_QFI) pari_err_TYPE("nupow",x);
  if (gequal1(n)) return gcopy(x);
  av = avma;
  D = qfb_disc(x);
  y = qfi_1_by_disc(D);
  if (!signe(n)) return y;
  if (!L) L = sqrtnint(absi_shallow(D), 4);
  y = gen_pow(x, n, (void*)L, &mul_nudupl, &mul_nucomp);
  if (signe(n) < 0
  && !absequalii(gel(y,1),gel(y,2))
  && !absequalii(gel(y,1),gel(y,3))) togglesign(gel(y,2));
  return gerepileupto(av, y);
}

/* Reduction */

/* assume a > 0. Write b = q*2a + r, with -a < r <= a */
static GEN
dvmdii_round(GEN b, GEN a, GEN *r)
{
  GEN a2 = shifti(a, 1), q = dvmdii(b, a2, r);
  if (signe(b) >= 0) {
    if (abscmpii(*r, a) > 0) { q = addiu(q, 1); *r = subii(*r, a2); }
  } else { /* r <= 0 */
    if (abscmpii(*r, a) >= 0){ q = subiu(q, 1); *r = addii(*r, a2); }
  }
  return q;
}
/* Assume 0 < a <= LONG_MAX. Ensure no overflow */
static long
dvmdsu_round(long b, ulong a, long *r)
{
  ulong a2 = a << 1, q, ub, ur;
  if (b >= 0) {
    ub = b;
    q = ub / a2;
    ur = ub % a2;
    if (ur > a) { ur -= a; q++; *r = (long)ur; *r -= (long)a; }
    else *r = (long)ur;
    return (long)q;
  } else { /* r <= 0 */
    ub = (ulong)-b; /* |b| */
    q = ub / a2;
    ur = ub % a2;
    if (ur >= a) { ur -= a; q++; *r = (long)ur; *r = (long)a - *r; }
    else *r = -(long)ur;
    return -(long)q;
  }
}
/* reduce b mod 2*a. Update b,c */
static void
REDB(GEN a, GEN *b, GEN *c)
{
  GEN r, q = dvmdii_round(*b, a, &r);
  if (!signe(q)) return;
  *c = subii(*c, mulii(q, shifti(addii(*b, r),-1)));
  *b = r;
}
/* Assume a > 0. Reduce b mod 2*a. Update b,c */
static void
sREDB(ulong a, long *b, ulong *c)
{
  long r, q;
  ulong uz;
  if (a > LONG_MAX) return; /* b already reduced */
  q = dvmdsu_round(*b, a, &r);
  if (q == 0) return;
  /* Final (a,r,c2) satisfies |r| <= |b| hence c2 <= c, c2 = c - q*z,
   * where z = (b+r) / 2, representable as long, has the same sign as q. */
  if (*b < 0)
  { /* uz = -z >= 0, q < 0 */
    if (r >= 0) /* different signs=>no overflow, exact division */
      uz = (ulong)-((*b + r)>>1);
    else
    {
      ulong ub = (ulong)-*b, ur = (ulong)-r;
      uz = (ub + ur) >> 1;
    }
    *c -= (-q) * uz; /* c -= qz */
  }
  else
  { /* uz = z >= 0, q > 0 */
    if (r <= 0)
      uz = (*b + r)>>1;
    else
    {
      ulong ub = (ulong)*b, ur = (ulong)r;
      uz = ((ub + ur) >> 1);
    }
    *c -= q * uz; /* c -= qz */
  }
  *b = r;
}
static void
REDBU(GEN a, GEN *b, GEN *c, GEN u1, GEN *u2)
{ /* REDB(a,b,c) */
  GEN r, q = dvmdii_round(*b, a, &r);
  *c = subii(*c, mulii(q, shifti(addii(*b, r),-1)));
  *b = r;
  *u2 = subii(*u2, mulii(q, u1));
}

/* q t_QFI, return reduced representative and set base change U in Sl2(Z) */
GEN
redimagsl2(GEN q, GEN *U)
{
  GEN Q = cgetg(4, t_QFI);
  pari_sp av = avma, av2;
  GEN z, u1,u2,v1,v2, a = gel(q,1), b = gel(q,2), c = gel(q,3);
  long cmp;
  /* upper bound for size of final (a,b,c) */
  (void)new_chunk(2*(lgefint(a) + lgefint(b) + lgefint(c) + 3));
  av2 = avma;
  u1 = gen_1; u2 = gen_0;
  cmp = abscmpii(a, b);
  if (cmp < 0)
    REDBU(a,&b,&c, u1,&u2);
  else if (cmp == 0 && signe(b) < 0)
  { /* b = -a */
    b = negi(b);
    u2 = gen_1;
  }
  for(;;)
  {
    cmp = abscmpii(a, c); if (cmp <= 0) break;
    swap(a,c); b = negi(b);
    z = u1; u1 = u2; u2 = negi(z);
    REDBU(a,&b,&c, u1,&u2);
    if (gc_needed(av, 1)) {
      if (DEBUGMEM>1) pari_warn(warnmem, "redimagsl2");
      gerepileall(av2, 5, &a,&b,&c, &u1,&u2);
    }
  }
  if (cmp == 0 && signe(b) < 0)
  {
    b = negi(b);
    z = u1; u1 = u2; u2 = negi(z);
  }
  avma = av;
  a = icopy(a); gel(Q,1) = a;
  b = icopy(b); gel(Q,2) = b;
  c = icopy(c); gel(Q,3) = c;
  u1 = icopy(u1);
  u2 = icopy(u2); av = avma;

  /* Let q = (A,B,C). q o [u1,u2; v1,v2] = Q implies
   * [v1,v2] = (1/C) [(b-B)/2 u1 - a u2, c u1 - (b+B)/2 u2] */
  z = shifti(subii(b, gel(q,2)), -1);
  v1 = subii(mulii(z, u1), mulii(a, u2)); v1 = diviiexact(v1, gel(q,3));
  z = subii(z, b);
  v2 = addii(mulii(z, u2), mulii(c, u1)); v2 = diviiexact(v2, gel(q,3));
  avma = av;
  v1 = icopy(v1);
  v2 = icopy(v2);
  *U = mkmat2(mkcol2(u1,v1), mkcol2(u2,v2)); return Q;
}

static GEN
setq_b0(ulong a, ulong c)
{ retmkqfi( utoipos(a), gen_0, utoipos(c) ); }
/* assume |sb| = 1 */
static GEN
setq(ulong a, ulong b, ulong c, long sb)
{ retmkqfi( utoipos(a), sb == 1? utoipos(b): utoineg(b), utoipos(c) ); }
/* 0 < a, c < 2^BIL, b = 0 */
static GEN
redimag_1_b0(ulong a, ulong c)
{ return (a <= c)? setq_b0(a, c): setq_b0(c, a); }

/* 0 < a, c < 2^BIL: single word affair */
static GEN
redimag_1(pari_sp av, GEN a, GEN b, GEN c)
{
  ulong ua, ub, uc;
  long sb;
  for(;;)
  { /* at most twice */
    long lb = lgefint(b); /* <= 3 after first loop */
    if (lb == 2) return redimag_1_b0(a[2],c[2]);
    if (lb == 3 && uel(b,2) <= (ulong)LONG_MAX) break;
    REDB(a,&b,&c);
    if (uel(a,2) <= uel(c,2))
    { /* lg(b) <= 3 but may be too large for itos */
      long s = signe(b);
      avma = av;
      if (!s) return redimag_1_b0(a[2], c[2]);
      if (a[2] == c[2]) s = 1;
      return setq(a[2], b[2], c[2], s);
    }
    swap(a,c); b = negi(b);
  }
  /* b != 0 */
  avma = av;
  ua = a[2];
  ub = sb = b[2]; if (signe(b) < 0) sb = -sb;
  uc = c[2];
  if (ua < ub)
    sREDB(ua, &sb, &uc);
  else if (ua == ub && sb < 0) sb = (long)ub;
  while(ua > uc)
  {
    lswap(ua,uc); sb = -sb;
    sREDB(ua, &sb, &uc);
  }
  if (!sb) return setq_b0(ua, uc);
  else
  {
    long s = 1;
    if (sb < 0)
    {
      sb = -sb;
      if (ua != uc) s = -1;
    }
    return setq(ua, sb, uc, s);
  }
}

static GEN
redimag_av(pari_sp av, GEN q)
{
  GEN a = gel(q,1), b = gel(q,2), c = gel(q,3);
  long cmp, lc = lgefint(c);

  if (lgefint(a) == 3 && lc == 3) return redimag_1(av, a, b, c);
  cmp = abscmpii(a, b);
  if (cmp < 0)
    REDB(a,&b,&c);
  else if (cmp == 0 && signe(b) < 0)
    b = negi(b);
  for(;;)
  {
    cmp = abscmpii(a, c); if (cmp <= 0) break;
    lc = lgefint(a); /* lg(future c): we swap a & c next */
    if (lc == 3) return redimag_1(av, a, b, c);
    swap(a,c); b = negi(b); /* apply rho */
    REDB(a,&b,&c);
  }
  if (cmp == 0 && signe(b) < 0) b = negi(b);
  /* size of reduced Qfb(a,b,c) <= 3 lg(c) + 4 <= 4 lg(c) */
  (void)new_chunk(lc<<2);
  a = icopy(a); b = icopy(b); c = icopy(c);
  avma = av;
  retmkqfi(icopy(a), icopy(b), icopy(c));
}
GEN
redimag(GEN q) { return redimag_av(avma, q); }

static GEN
rhoimag(GEN x)
{
  GEN a = gel(x,1), b = gel(x,2), c = gel(x,3);
  int fl = abscmpii(a, c);
  if (fl <= 0) {
    int fg = abscmpii(a, b);
    if (fg >= 0) {
      x = qfi(a,b,c);
      if ((!fl || !fg) && signe(gel(x,2)) < 0) setsigne(gel(x,2), 1);
      return x;
    }
  }
  x = cgetg(4, t_QFI);
  (void)new_chunk(lgefint(a) + lgefint(b) + lgefint(c) + 3);
  swap(a,c); b = negi(b);
  REDB(a, &b, &c); avma = (pari_sp)x;
  gel(x,1) = icopy(a);
  gel(x,2) = icopy(b);
  gel(x,3) = icopy(c); return x;
}

/* qfr3 / qfr5 */

/* t_QFR are unusable: D, sqrtD, isqrtD are recomputed all the time and the
 * logarithmic Shanks's distance is costly and hard to control.
 * qfr3 / qfr5 routines take a container of t_INTs (e.g a t_VEC) as argument,
 * at least 3 (resp. 5) components [it is a feature that they do not check the
 * precise type or length of the input]. They return a vector of length 3
 * (resp. 5). A qfr3 [a,b,c] contains the form coeffs, in a qfr5 [a,b,c, e,d]
 * the t_INT e is a binary exponent, d a t_REAL, coding the distance in
 * multiplicative form: the true distance is obtained from qfr5_dist.
 * All other qfr routines are obsolete (inefficient) wrappers */

/* static functions are not stack-clean. Unless mentionned otherwise, public
 * functions are. */

#define EMAX 22
static void
fix_expo(GEN x)
{
  if (expo(gel(x,5)) >= (1L << EMAX)) {
    gel(x,4) = addiu(gel(x,4), 1);
    shiftr_inplace(gel(x,5), - (1L << EMAX));
  }
}

/* (1/2) log (d * 2^{e * 2^EMAX}). Not stack clean if e != 0 */
GEN
qfr5_dist(GEN e, GEN d, long prec)
{
  GEN t = logr_abs(d);
  if (signe(e)) {
    GEN u = mulir(e, mplog2(prec));
    shiftr_inplace(u, EMAX); t = addrr(t, u);
  }
  shiftr_inplace(t, -1); return t;
}

static void
rho_get_BC(GEN *B, GEN *C, GEN b, GEN c, struct qfr_data *S)
{
  GEN t, u;
  u = shifti(c,1);
  t = (abscmpii(S->isqrtD,c) >= 0)? S->isqrtD: c;
  u = remii(addii_sign(t,1, b,signe(b)), u);
  *B = addii_sign(t, 1, u, -signe(u)); /* |t| - (|t|+b) % |2c| */
  if (*B == gen_0)
  { u = shifti(S->D, -2); setsigne(u, -1); }
  else
    u = shifti(addii_sign(sqri(*B),1, S->D,-1), -2);
  *C = diviiexact(u, c); /* = (B^2-D)/4c */
}
/* Not stack-clean */
GEN
qfr3_rho(GEN x, struct qfr_data *S)
{
  GEN B, C, b = gel(x,2), c = gel(x,3);
  rho_get_BC(&B, &C, b, c, S);
  return mkvec3(c,B,C);
}
/* Not stack-clean */
GEN
qfr5_rho(GEN x, struct qfr_data *S)
{
  GEN B, C, y, b = gel(x,2), c = gel(x,3);
  long sb = signe(b);

  rho_get_BC(&B, &C, b, c, S);
  y = mkvec5(c,B,C, gel(x,4), gel(x,5));
  if (sb) {
    GEN t = subii(sqri(b), S->D);
    if (sb < 0)
      t = divir(t, sqrr(subir(b,S->sqrtD)));
    else
      t = divri(sqrr(addir(b,S->sqrtD)), t);
    /* t = (b + sqrt(D)) / (b - sqrt(D)), evaluated stably */
    gel(y,5) = mulrr(t, gel(y,5)); fix_expo(y);
  }
  return y;
}

/* Not stack-clean */
GEN
qfr_to_qfr5(GEN x, long prec)
{ return mkvec5(gel(x,1),gel(x,2),gel(x,3),gen_0,real_1(prec)); }

/* d0 = initial distance, x = [a,b,c, expo(d), d], d = exp(2*distance) */
GEN
qfr5_to_qfr(GEN x, GEN d0)
{
  GEN y;
  if (lg(x) ==  6)
  {
    GEN n = gel(x,4), d = absr(gel(x,5));
    if (signe(n))
    {
      n = addis(shifti(n, EMAX), expo(d));
      setexpo(d, 0); d = logr_abs(d);
      if (signe(n)) d = addrr(d, mulir(n, mplog2(lg(d0))));
      shiftr_inplace(d, -1);
      d0 = addrr(d0, d);
    }
    else if (!gequal1(d)) /* avoid loss of precision */
    {
      d = logr_abs(d);
      shiftr_inplace(d, -1);
      d0 = addrr(d0, d);
    }
  }
  y = cgetg(5, t_QFR);
  gel(y,1) = gel(x,1);
  gel(y,2) = gel(x,2);
  gel(y,3) = gel(x,3);
  gel(y,4) = d0; return y;
}

/* Not stack-clean */
GEN
qfr3_to_qfr(GEN x, GEN d)
{
  GEN z = cgetg(5, t_QFR);
  gel(z,1) = gel(x,1);
  gel(z,2) = gel(x,2);
  gel(z,3) = gel(x,3);
  gel(z,4) = d; return z;
}

static int
ab_isreduced(GEN a, GEN b, GEN isqrtD)
{
  if (signe(b) > 0 && abscmpii(b, isqrtD) <= 0)
  {
    GEN t = addii_sign(isqrtD,1, shifti(a,1),-1);
    long l = abscmpii(b, t); /* compare |b| and |floor(sqrt(D)) - |2a|| */
    if (l > 0 || (l == 0 && signe(t) < 0)) return 1;
  }
  return 0;
}

INLINE int
qfr_isreduced(GEN x, GEN isqrtD)
{
  return ab_isreduced(gel(x,1),gel(x,2),isqrtD);
}

/* Not stack-clean */
GEN
qfr5_red(GEN x, struct qfr_data *S)
{
  pari_sp av = avma;
  while (!qfr_isreduced(x, S->isqrtD))
  {
    x = qfr5_rho(x, S);
    if (gc_needed(av,2))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"qfr5_red");
      x = gerepilecopy(av, x);
    }
  }
  return x;
}
/* Not stack-clean */
GEN
qfr3_red(GEN x, struct qfr_data *S)
{
  pari_sp av = avma;
  while (!qfr_isreduced(x, S->isqrtD))
  {
    x = qfr3_rho(x, S);
    if (gc_needed(av,2))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"qfr3_red");
      x = gerepilecopy(av, x);
    }
  }
  return x;
}

static void
get_disc(GEN x, struct qfr_data *S)
{
  if (!S->D) S->D = qfb_disc(x);
  else if (typ(S->D) != t_INT) pari_err_TYPE("qfr_init",S->D);
  if (!signe(S->D)) pari_err_DOMAIN("qfr_init", "disc", "=", gen_0,x);
}

void
qfr_data_init(GEN D, long prec, struct qfr_data *S)
{
  S->D = D;
  S->sqrtD = sqrtr(itor(S->D,prec));
  S->isqrtD = truncr(S->sqrtD);
}

static GEN
qfr5_init(GEN x, struct qfr_data *S)
{
  GEN d = gel(x,4);
  long prec = realprec(d), l = -expo(d);
  if (l < BITS_IN_LONG) l = BITS_IN_LONG;
  prec = maxss(prec, nbits2prec(l));
  x = qfr_to_qfr5(x,prec);

  get_disc(x, S);
  if (!S->sqrtD) S->sqrtD = sqrtr(itor(S->D,prec));
  else if (typ(S->sqrtD) != t_REAL) pari_err_TYPE("qfr_init",S->sqrtD);

  if (!S->isqrtD)
  {
    pari_sp av=avma;
    long e;
    S->isqrtD = gcvtoi(S->sqrtD,&e);
    if (e>-2) { avma = av; S->isqrtD = sqrti(S->D); }
  }
  else if (typ(S->isqrtD) != t_INT) pari_err_TYPE("qfr_init",S->isqrtD);
  return x;
}
static GEN
qfr3_init(GEN x, struct qfr_data *S)
{
  get_disc(x, S);
  if (!S->isqrtD) S->isqrtD = sqrti(S->D);
  else if (typ(S->isqrtD) != t_INT) pari_err_TYPE("qfr_init",S->isqrtD);
  return x;
}

#define qf_NOD  2
#define qf_STEP 1

static GEN
redreal0(GEN x, long flag, GEN D, GEN isqrtD, GEN sqrtD)
{
  pari_sp av = avma;
  struct qfr_data S;
  GEN d;
  if (typ(x) != t_QFR) pari_err_TYPE("redreal",x);
  d = gel(x,4);
  S.D = D;
  S.sqrtD = sqrtD;
  S.isqrtD = isqrtD;
  x = (flag & qf_NOD)? qfr3_init(x, &S): qfr5_init(x, &S);
  switch(flag) {
    case 0:              x = qfr5_red(x,&S); break;
    case qf_NOD:         x = qfr3_red(x,&S); break;
    case qf_STEP:        x = qfr5_rho(x,&S); break;
    case qf_STEP|qf_NOD: x = qfr3_rho(x,&S); break;
    default: pari_err_FLAG("qfbred");
  }
  return gerepilecopy(av, qfr5_to_qfr(x,d));
}
GEN
redreal(GEN x)
{ return redreal0(x,0,NULL,NULL,NULL); }
GEN
rhoreal(GEN x)
{ return redreal0(x,qf_STEP,NULL,NULL,NULL); }
GEN
redrealnod(GEN x, GEN isqrtD)
{ return redreal0(x,qf_NOD,NULL,isqrtD,NULL); }
GEN
rhorealnod(GEN x, GEN isqrtD)
{ return redreal0(x,qf_STEP|qf_NOD,NULL,isqrtD,NULL); }
GEN
qfbred0(GEN x, long flag, GEN D, GEN isqrtD, GEN sqrtD)
{
  if (typ(x) == t_QFI)
    return (flag & qf_STEP)? rhoimag(x): redimag(x);
  return redreal0(x,flag,D,isqrtD,sqrtD);
}

GEN
qfr5_comp(GEN x, GEN y, struct qfr_data *S)
{
  pari_sp av = avma;
  GEN z = cgetg(6,t_VEC); qfb_comp(z,x,y);
  if (x == y)
  {
    gel(z,4) = shifti(gel(x,4),1);
    gel(z,5) = sqrr(gel(x,5));
  }
  else
  {
    gel(z,4) = addii(gel(x,4),gel(y,4));
    gel(z,5) = mulrr(gel(x,5),gel(y,5));
  }
  fix_expo(z); z = qfr5_red(z,S);
  return gerepilecopy(av,z);
}
/* Not stack-clean */
GEN
qfr3_comp(GEN x, GEN y, struct qfr_data *S)
{
  GEN z = cgetg(4,t_VEC); qfb_comp(z,x,y);
  return qfr3_red(z, S);
}

/* valid for t_QFR, qfr3, qfr5 */
static GEN
qfr_inv(GEN x) {
  GEN z = shallowcopy(x);
  gel(z,2) = negi(gel(z,2));
  return z;
}

/* return x^n. Not stack-clean */
GEN
qfr5_pow(GEN x, GEN n, struct qfr_data *S)
{
  GEN y = NULL;
  long i, m, s = signe(n);
  if (!s) return qfr5_1(S, lg(gel(x,5)));
  for (i=lgefint(n)-1; i>1; i--)
  {
    m = n[i];
    for (; m; m>>=1)
    {
      if (m&1) y = y? qfr5_comp(y,x,S): x;
      if (m == 1 && i == 2) break;
      x = qfr5_comp(x,x,S);
    }
  }
  return y;
}
/* return x^n. Not stack-clean */
GEN
qfr3_pow(GEN x, GEN n, struct qfr_data *S)
{
  GEN y = NULL;
  long i, m, s = signe(n);
  if (!s) return qfr3_1(S);
  if (s < 0) x = qfr_inv(x);
  for (i=lgefint(n)-1; i>1; i--)
  {
    m = n[i];
    for (; m; m>>=1)
    {
      if (m&1) y = y? qfr3_comp(y,x,S): x;
      if (m == 1 && i == 2) break;
      x = qfr3_comp(x,x,S);
    }
  }
  return y;
}
GEN
qfrpow(GEN x, GEN n)
{
  struct qfr_data S = { NULL, NULL, NULL };
  long s = signe(n);
  pari_sp av = avma;
  GEN d0;

  if (!s) return qfr_1(x);
  if (is_pm1(n)) return s > 0? redreal(x): ginv(x);
  if (s < 0) x = qfr_inv(x);
  d0 = gel(x,4);
  if (!signe(d0)) {
    x = qfr3_init(x, &S);
    x = qfr3_pow(x, n, &S);
    x = qfr3_to_qfr(x, d0);
  } else {
    x = qfr5_init(x, &S);
    x = qfr5_pow(qfr_to_qfr5(x, lg(S.sqrtD)), n, &S);
    x = qfr5_to_qfr(x, mulri(d0,n));
  }
  return gerepilecopy(av, x);
}

/* Prime forms attached to prime ideals of degree 1 */

/* assume x != 0 a t_INT, p > 0
 * Return a t_QFI, but discriminant sign is not checked: can be used for
 * real forms as well */
GEN
primeform_u(GEN x, ulong p)
{
  GEN c, y = cgetg(4, t_QFI);
  pari_sp av = avma;
  ulong b;
  long s;

  s = mod8(x); if (signe(x) < 0 && s) s = 8-s;
  /* 2 or 3 mod 4 */
  if (s & 2) pari_err_DOMAIN("primeform", "disc % 4", ">",gen_1, x);
  if (p == 2) {
    switch(s) {
      case 0: b = 0; break;
      case 1: b = 1; break;
      case 4: b = 2; break;
      default: pari_err_SQRTN("primeform", mkintmod(x,utoi(p)) );
               b = 0; /* -Wall */
    }
    c = shifti(subsi(s,x), -3);
  } else {
    b = Fl_sqrt(umodiu(x,p), p);
    if (b == ~0UL) pari_err_SQRTN("primeform", mkintmod(x,utoi(p)) );
    /* mod(b) != mod2(x) ? */
    if ((b ^ s) & 1) b = p - b;
    c = diviuexact(shifti(subii(sqru(b), x), -2), p);
  }
  gel(y,3) = gerepileuptoint(av, c);
  gel(y,2) = utoi(b);
  gel(y,1) = utoipos(p); return y;
}

/* special case: p = 1 return unit form */
GEN
primeform(GEN x, GEN p, long prec)
{
  const char *f = "primeform";
  pari_sp av;
  long s, sx = signe(x), sp = signe(p);
  GEN y, b, absp;

  if (typ(x) != t_INT) pari_err_TYPE(f,x);
  if (typ(p) != t_INT) pari_err_TYPE(f,p);
  if (!sp) pari_err_DOMAIN(f,"p","=",gen_0,p);
  if (!sx) pari_err_DOMAIN(f,"D","=",gen_0,x);
  if (lgefint(p) == 3)
  {
    ulong pp = p[2];
    if (pp == 1) {
      if (sx < 0) {
        long r;
        if (sp < 0) pari_err_IMPL("negative definite t_QFI");
        r = mod4(x);
        if (r && r != 3) pari_err_DOMAIN(f,"disc % 4",">", gen_1,x);
        return qfi_1_by_disc(x);
      }
      y = qfr_1_by_disc(x,prec);
      if (sp < 0) { gel(y,1) = gen_m1; togglesign(gel(y,3)); }
      return y;
    }
    y = primeform_u(x, pp);
    if (sx < 0) {
      if (sp < 0) pari_err_IMPL("negative definite t_QFI");
      return y;
    }
    if (sp < 0) { togglesign(gel(y,1)); togglesign(gel(y,3)); }
    return gcopy( qfr3_to_qfr(y, real_0(prec)) );
  }
  s = mod8(x);
  if (sx < 0)
  {
    if (sp < 0) pari_err_IMPL("negative definite t_QFI");
    if (s) s = 8-s;
    y = cgetg(4, t_QFI);
  }
  else
  {
    y = cgetg(5, t_QFR);
    gel(y,4) = real_0(prec);
  }
  /* 2 or 3 mod 4 */
  if (s & 2) pari_err_DOMAIN(f, "disc % 4", ">",gen_1, x);
  absp = absi_shallow(p); av = avma;
  b = Fp_sqrt(x, absp); if (!b) pari_err_SQRTN(f, mkintmod(x,absp));
  s &= 1; /* s = x mod 2 */
  /* mod(b) != mod2(x) ? [Warning: we may have b == 0] */
  if ((!signe(b) && s) || mod2(b) != s) b = gerepileuptoint(av, subii(absp,b));

  av = avma;
  gel(y,3) = gerepileuptoint(av, diviiexact(shifti(subii(sqri(b), x), -2), p));
  gel(y,2) = b;
  gel(y,1) = icopy(p);
  return y;
}

/* Let M and N in SL2(Z), return (N*M^-1)[,1] */
static GEN
SL2_div_mul_e1(GEN N, GEN M)
{
  GEN b = gcoeff(M,2,1), d = gcoeff(M,2,2);
  GEN p = subii(mulii(gcoeff(N,1,1), d), mulii(gcoeff(N,1,2), b));
  GEN q = subii(mulii(gcoeff(N,2,1), d), mulii(gcoeff(N,2,2), b));
  return mkvec2(p,q);
}
/* Let M and N in SL2(Z), return (N*[1,0;0,-1]*M^-1)[,1] */
static GEN
SL2_swap_div_mul_e1(GEN N, GEN M)
{
  GEN b = gcoeff(M,2,1), d = gcoeff(M,2,2);
  GEN p = addii(mulii(gcoeff(N,1,1), d), mulii(gcoeff(N,1,2), b));
  GEN q = addii(mulii(gcoeff(N,2,1), d), mulii(gcoeff(N,2,2), b));
  return mkvec2(p,q);
}

/* Test equality modulo GL2 of two reduced forms */
static int
GL2_qfb_equal(GEN a, GEN b)
{
  return equalii(gel(a,1),gel(b,1))
   && absequalii(gel(a,2),gel(b,2))
   &&    equalii(gel(a,3),gel(b,3));
}

static GEN
qfbsolve_cornacchia(GEN c, GEN p, int swap)
{
  pari_sp av = avma;
  GEN M, N;
  if (kronecker(negi(c), p) < 0 || !cornacchia(c, p, &M,&N)) {
    avma = av; return gen_0;
  }
  return gerepilecopy(av, swap? mkvec2(N,M): mkvec2(M,N));
}

GEN
qfisolvep(GEN Q, GEN p)
{
  GEN M, N, x,y, a,b,c, d;
  pari_sp av = avma;
  if (!signe(gel(Q,2)))
  {
    a = gel(Q,1);
    c = gel(Q,3); /* if principal form, use faster cornacchia */
    if (equali1(a)) return qfbsolve_cornacchia(c, p, 0);
    if (equali1(c)) return qfbsolve_cornacchia(a, p, 1);
  }
  d = qfb_disc(Q); if (kronecker(d,p) < 0) return gen_0;
  a = redimagsl2(Q, &N);
  if (equali1(gel(a,1))) /* principal form */
  {
    long r;
    if (!signe(gel(a,2)))
    {
      a = qfbsolve_cornacchia(gel(a,3), p, 0);
      if (a == gen_0) { avma = av; return gen_0; }
      a = ZM_ZC_mul(N, a);
      a[0] = evaltyp(t_VEC) | _evallg(3); /* transpose */
      return gerepileupto(av, a);
    }
    /* x^2 + xy + ((1-d)/4)y^2 = p <==> (2x + y)^2 - d y^2 = 4p */
    if (!cornacchia2(negi(d), p, &x, &y)) { avma = av; return gen_0; }
    x = divis_rem(subii(x,y), 2, &r); if (r) { avma = av; return gen_0; }
    a = ZM_ZC_mul(N, mkvec2(x,y));
    a[0] = evaltyp(t_VEC) | _evallg(3); /* transpose */
    return gerepileupto(av, a);
  }
  b = redimagsl2(primeform(d, p, 0), &M);
  if (!GL2_qfb_equal(a,b)) { avma = av; return gen_0; }
  if (signe(gel(a,2))==signe(gel(b,2)))
    x = SL2_div_mul_e1(N,M);
  else
    x = SL2_swap_div_mul_e1(N,M);
  return gerepilecopy(av, x);
}

GEN
redrealsl2step(GEN A, GEN d, GEN rd)
{
  pari_sp ltop = avma;
  GEN N, V = gel(A,1), M = gel(A,2);
  GEN a = gel(V,1), b = gel(V,2), c = gel(V,3);
  GEN C = mpabs_shallow(c);
  GEN t = addii(b, gmax_shallow(rd, C));
  GEN r, q = truedvmdii(t, shifti(C,1), &r);
  b = subii(t, addii(r,b));
  a = c;
  c = truedivii(subii(sqri(b), d), shifti(c,2));
  if (signe(a) < 0) togglesign(q);
  N = mkmat2(gel(M,2),
             mkcol2(subii(mulii(q, gcoeff(M, 1, 2)), gcoeff(M, 1, 1)),
                    subii(mulii(q, gcoeff(M, 2, 2)), gcoeff(M, 2, 1))));
  return gerepilecopy(ltop, mkvec2(mkvec3(a,b,c),N));
}

GEN
redrealsl2(GEN V, GEN d, GEN rd)
{
  pari_sp ltop = avma;
  GEN M, u1, u2, v1, v2;
  GEN a = gel(V,1), b = gel(V,2), c = gel(V,3);
  u1 = v2 = gen_1; v1 = u2 = gen_0;
  while (!ab_isreduced(a,b,rd))
  {
    GEN C = mpabs_shallow(c);
    GEN t = addii(b, gmax_shallow(rd,C));
    GEN r, q = truedvmdii(t, shifti(C,1), &r);
    b = subii(t, addii(r,b));
    a = c;
    c = truedivii(subii(sqri(b), d), shifti(c,2));
    if (signe(a) < 0) togglesign(q);
    r = u1; u1 = v1; v1 = subii(mulii(q, v1), r);
    r = u2; u2 = v2; v2 = subii(mulii(q, v2), r);
    if (gc_needed(ltop, 1))
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"redrealsl2");
      gerepileall(ltop, 7, &a,&b,&c,&u1,&u2,&v1,&v2);
    }
  }
  M = mkmat2(mkcol2(u1,u2), mkcol2(v1,v2));
  return gerepilecopy(ltop, mkvec2(mkvec3(a,b,c), M));
}

GEN
qfbredsl2(GEN q, GEN S)
{
  GEN v, D, isD;
  pari_sp av;
  switch(typ(q))
  {
    case t_QFI:
      if (S) pari_err_TYPE("qfbredsl2",S);
      v = cgetg(3,t_VEC);
      gel(v,1) = redimagsl2(q, &gel(v,2));
      return v;
    case t_QFR:
      av = avma;
      if (S) {
        if (typ(S) != t_VEC || lg(S) != 3) pari_err_TYPE("qfbredsl2",S);
        D = gel(S,1);
        isD = gel(S,2);
        if (typ(D) != t_INT || signe(D) <= 0 || typ(isD) != t_INT)
          pari_err_TYPE("qfbredsl2",S);
      }
      else
      {
        D = qfb_disc(q);
        isD = sqrtint(D);
      }
      v = redrealsl2(q,D,isD);
      gel(v,1) = qfr3_to_qfr(gel(v,1), real_0(precision(gel(q,4))));
      return gerepilecopy(av, v);

    default:
        pari_err_TYPE("qfbredsl2",q);
        return NULL;
  }
}

GEN
qfrsolvep(GEN Q, GEN p)
{
  pari_sp ltop = avma, btop;
  GEN N, P, P1, P2, M, rd, d = qfb_disc(Q);
  if (kronecker(d, p) < 0) { avma = ltop; return gen_0; }
  rd = sqrti(d);
  M = N = redrealsl2(Q, d,rd);
  P = primeform(d, p, DEFAULTPREC);
  P1 = redrealsl2(P, d,rd);
  togglesign( gel(P,2) );
  P2 = redrealsl2(P, d,rd);
  btop = avma;
  for(;;)
  {
    if (ZV_equal(gel(M,1), gel(P1,1))) { N = gel(P1,2); break; }
    if (ZV_equal(gel(M,1), gel(P2,1))) { N = gel(P2,2); break; }
    M = redrealsl2step(M, d,rd);
    if (ZV_equal(gel(M,1), gel(N,1))) { avma = ltop; return gen_0; }
    if (gc_needed(btop, 1)) M = gerepileupto(btop, M);
  }
  return gerepilecopy(ltop, SL2_div_mul_e1(gel(M,2),N));
}

GEN
qfbsolve(GEN Q,GEN n)
{
  if (typ(n)!=t_INT) pari_err_TYPE("qfbsolve",n);
  switch(typ(Q))
  {
  case t_QFI: return qfisolvep(Q,n);
  case t_QFR: return qfrsolvep(Q,n);
  default:
    pari_err_TYPE("qfbsolve",Q);
    return NULL; /* LCOV_EXCL_LINE */
  }
}

/* 1 if there exists x,y such that x^2 + dy^2 = p [prime], 0 otherwise */
long
cornacchia(GEN d, GEN p, GEN *px, GEN *py)
{
  pari_sp av = avma, av2;
  GEN a, b, c, L, r;

  if (typ(d) != t_INT) pari_err_TYPE("cornacchia", d);
  if (typ(p) != t_INT) pari_err_TYPE("cornacchia", p);
  if (signe(d) <= 0) pari_err_DOMAIN("cornacchia", "d","<=",gen_0,d);
  *px = *py = gen_0;
  b = subii(p, d);
  if (signe(b) < 0) return 0;
  if (signe(b) == 0) { avma = av; *py = gen_1; return 1; }
  b = Fp_sqrt(b, p); /* sqrt(-d) */
  if (!b) { avma = av; return 0; }
  if (abscmpii(shifti(b,1), p) > 0) b = subii(b,p);
  a = p; L = sqrti(p);
  av2 = avma;
  while (abscmpii(b, L) > 0)
  {
    r = remii(a, b); a = b; b = r;
    if (gc_needed(av2, 1)) {
      if (DEBUGMEM>1) pari_warn(warnmem,"cornacchia");
      gerepileall(av2, 2, &a,&b);
    }
  }
  a = subii(p, sqri(b));
  c = dvmdii(a, d, &r);
  if (r != gen_0 || !Z_issquareall(c, &c)) { avma = av; return 0; }
  avma = av;
  *px = icopy(b);
  *py = icopy(c); return 1;
}

static long
cornacchia2_helper(long av, GEN d, GEN p, GEN b, GEN px4, GEN *px, GEN *py)
{
  pari_sp av2 = avma;
  GEN a, c, r, L;
  long k = mod4(d);
  if (!signe(b)) { /* d = p,2p,3p,4p */
    avma = av;
    if (absequalii(d, px4)){ *py = gen_1; return 1; }
    if (absequalii(d, p))  { *py = gen_2; return 1; }
    return 0;
  }
  if (mod2(b) != (k & 1)) b = subii(p,b);
  a = shifti(p,1); L = sqrti(px4);
  av2 = avma;
  while (cmpii(b, L) > 0)
  {
    r = remii(a, b); a = b; b = r;
    if (gc_needed(av2, 1)) {
      if (DEBUGMEM>1) pari_warn(warnmem,"cornacchia");
      gerepileall(av2, 2, &a,&b);
    }
  }
  a = subii(px4, sqri(b));
  c = dvmdii(a, d, &r);
  if (r != gen_0 || !Z_issquareall(c, &c)) { avma = av; return 0; }
  avma = av;
  *px = icopy(b);
  *py = icopy(c); return 1;
}

/* 1 if there exists x,y such that x^2 + dy^2 = 4p [p prime], 0 otherwise */
long
cornacchia2(GEN d, GEN p, GEN *px, GEN *py)
{
  pari_sp av = avma;
  GEN b, px4;
  long k;

  if (typ(d) != t_INT) pari_err_TYPE("cornacchia2", d);
  if (typ(p) != t_INT) pari_err_TYPE("cornacchia2", p);
  if (signe(d) <= 0) pari_err_DOMAIN("cornacchia2", "d","<=",gen_0,d);
  *px = *py = gen_0;
  k = mod4(d);
  if (k == 1 || k == 2) pari_err_DOMAIN("cornacchia2","-d mod 4", ">",gen_1,d);
  px4 = shifti(p,2);
  if (abscmpii(px4, d) < 0) { avma = av; return 0; }
  if (absequaliu(p, 2))
  {
    avma = av;
    switch (itou_or_0(d)) {
      case 4: *px = gen_2; break;
      case 7: *px = gen_1; break;
      default: return 0;
    }
    *py = gen_1; return 1;
  }
  b = Fp_sqrt(negi(d), p);
  if (!b) { avma = av; return 0; }
  return cornacchia2_helper(av, d, p, b, px4, px, py);
}

/* 1 if there exists x,y such that x^2 + dy^2 = 4p [p prime], 0 otherwise */
long
cornacchia2_sqrt(GEN d, GEN p, GEN b, GEN *px, GEN *py)
{
  pari_sp av = avma;
  GEN px4;
  *px = *py = gen_0;
  px4 = shifti(p,2);
  if (abscmpii(px4, d) < 0) { avma = av; return 0; }
  return cornacchia2_helper(av, d, p, b, px4, px, py);
}
