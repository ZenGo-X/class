/* Copyright (C) 2000  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/*******************************************************************/
/*                                                                 */
/*                ROOTS OF COMPLEX POLYNOMIALS                     */
/*  (original code contributed by Xavier Gourdon, INRIA RR 1852)   */
/*                                                                 */
/*******************************************************************/
#include "pari.h"
#include "paripriv.h"

static const double pariINFINITY = 1./0.;

static long
isvalidcoeff(GEN x)
{
  switch (typ(x))
  {
    case t_INT: case t_REAL: case t_FRAC: return 1;
    case t_COMPLEX: return isvalidcoeff(gel(x,1)) && isvalidcoeff(gel(x,2));
  }
  return 0;
}

static void
checkvalidpol(GEN p, const char *f)
{
  long i,n = lg(p);
  for (i=2; i<n; i++)
    if (!isvalidcoeff(gel(p,i))) pari_err_TYPE(f, gel(p,i));
}

/********************************************************************/
/**                                                                **/
/**                   FAST ARITHMETIC over Z[i]                    **/
/**                                                                **/
/********************************************************************/
static THREAD long KARASQUARE_LIMIT, COOKSQUARE_LIMIT;

/* fast sum of x,y: t_INT or t_COMPLEX(t_INT) */
static GEN
addCC(GEN x, GEN y)
{
  GEN z;

  if (typ(x) == t_INT)
  {
    if (typ(y) == t_INT) return addii(x,y);
    /* ty == t_COMPLEX */
    z = cgetg(3,t_COMPLEX);
    gel(z,1) = addii(x, gel(y,1));
    gel(z,2) = icopy(gel(y,2)); return z;
  }
  /* tx == t_COMPLEX */
  z = cgetg(3,t_COMPLEX);
  if (typ(y) == t_INT)
  {
    gel(z,1) = addii(gel(x,1),y);
    gel(z,2) = icopy(gel(x,2)); return z;
  }
  /* ty == t_COMPLEX */
  gel(z,1) = addii(gel(x,1),gel(y,1));
  gel(z,2) = addii(gel(x,2),gel(y,2)); return z;
}
/* fast product of x,y: t_INT or t_COMPLEX(t_INT) */
static GEN
mulCC(GEN x, GEN y)
{
  GEN z;

  if (typ(x) == t_INT)
  {
    if (typ(y) == t_INT) return mulii(x,y);
    /* ty == t_COMPLEX */
    z = cgetg(3,t_COMPLEX);
    gel(z,1) = mulii(x, gel(y,1));
    gel(z,2) = mulii(x, gel(y,2)); return z;
  }
  /* tx == t_COMPLEX */
  z = cgetg(3,t_COMPLEX);
  if (typ(y) == t_INT)
  {
    gel(z,1) = mulii(gel(x,1),y);
    gel(z,2) = mulii(gel(x,2),y); return z;
  }
  /* ty == t_COMPLEX */
  {
    pari_sp av = avma, tetpil;
    GEN p1, p2;

    p1 = mulii(gel(x,1),gel(y,1));
    p2 = mulii(gel(x,2),gel(y,2));
    y = mulii(addii(gel(x,1),gel(x,2)),
              addii(gel(y,1),gel(y,2)));
    x = addii(p1,p2); tetpil = avma;
    gel(z,1) = subii(p1,p2);
    gel(z,2) = subii(y,x); gerepilecoeffssp(av,tetpil,z+1,2);
    return z;
  }
}
/* fast squaring x: t_INT or t_COMPLEX(t_INT) */
static GEN
sqrCC(GEN x)
{
  GEN z;

  if (typ(x) == t_INT) return sqri(x);
  /* tx == t_COMPLEX */
  z = cgetg(3,t_COMPLEX);
  {
    pari_sp av = avma, tetpil;
    GEN y, p1, p2;

    p1 = sqri(gel(x,1));
    p2 = sqri(gel(x,2));
    y = sqri(addii(gel(x,1),gel(x,2)));
    x = addii(p1,p2); tetpil = avma;
    gel(z,1) = subii(p1,p2);
    gel(z,2) = subii(y,x); gerepilecoeffssp(av,tetpil,z+1,2);
    return z;
  }
}

static void
set_karasquare_limit(long bit)
{
  if (bit<600)       { KARASQUARE_LIMIT=8; COOKSQUARE_LIMIT=400; }
  else if (bit<2000) { KARASQUARE_LIMIT=4; COOKSQUARE_LIMIT=200; }
  else if (bit<3000) { KARASQUARE_LIMIT=4; COOKSQUARE_LIMIT=125; }
  else if (bit<5000) { KARASQUARE_LIMIT=2; COOKSQUARE_LIMIT= 75; }
  else               { KARASQUARE_LIMIT=1; COOKSQUARE_LIMIT= 50; }
}

/* assume lP > 0, lP = lgpol(P) */
static GEN
CX_square_spec(GEN P, long lP)
{
  GEN s, t;
  long i, j, l, nn, n = lP - 1;
  pari_sp av;

  nn = n<<1; s = cgetg(nn+3,t_POL); s[1] = evalsigne(1)|evalvarn(0);
  gel(s,2) = sqrCC(gel(P,0)); /* i = 0 */
  for (i=1; i<=n; i++)
  {
    av = avma; l = (i+1)>>1;
    t = mulCC(gel(P,0), gel(P,i)); /* j = 0 */
    for (j=1; j<l; j++) t = addCC(t, mulCC(gel(P,j), gel(P,i-j)));
    t = gmul2n(t,1);
    if ((i & 1) == 0) t = addCC(t, sqrCC(gel(P,i>>1)));
    gel(s,i+2) = gerepileupto(av, t);
  }
  gel(s,nn+2) = sqrCC(gel(P,n)); /* i = nn */
  for (   ; i<nn; i++)
  {
    av = avma; l = (i+1)>>1;
    t = mulCC(gel(P,i-n),gel(P,n)); /* j = i-n */
    for (j=i-n+1; j<l; j++) t = addCC(t, mulCC(gel(P,j),gel(P,i-j)));
    t = gmul2n(t,1);
    if ((i & 1) == 0) t = addCC(t, sqrCC(gel(P,i>>1)));
    gel(s,i+2) = gerepileupto(av, t);
  }
  return normalizepol_lg(s, nn+3);
}
/* nx = lgpol(x) */
static GEN
RgX_s_mulspec(GEN x, long nx, long s)
{
  GEN z, t;
  long i;
  if (!s || !nx) return pol_0(0);
  z = cgetg(nx+2, t_POL); z[1] = evalsigne(1)|evalvarn(0); t = z + 2;
  for (i=0; i < nx; i++) gel(t,i) = gmulgs(gel(x,i), s);
  return z;
}
/* nx = lgpol(x), return x << s. Inefficient if s = 0... */
static GEN
RgX_shiftspec(GEN x, long nx, long s)
{
  GEN z, t;
  long i;
  if (!nx) return pol_0(0);
  z = cgetg(nx+2, t_POL); z[1] = evalsigne(1)|evalvarn(0); t = z + 2;
  for (i=0; i < nx; i++) gel(t,i) = gmul2n(gel(x,i), s);
  return z;
}

/* spec function. nP = lgpol(P) */
static GEN
karasquare(GEN P, long nP)
{
  GEN Q, s0, s1, s2, a, t;
  long n0, n1, i, l, N, N0, N1, n = nP - 1; /* degree(P) */
  pari_sp av;

  if (n <= KARASQUARE_LIMIT) return nP? CX_square_spec(P, nP): pol_0(0);
  av = avma;
  n0 = (n>>1) + 1; n1 = nP - n0;
  s0 = karasquare(P, n0); Q = P + n0;
  s2 = karasquare(Q, n1);
  s1 = RgX_addspec_shallow(P, Q, n0, n1);
  s1 = RgX_sub(karasquare(s1+2, lgpol(s1)), RgX_add(s0,s2));
  N = (n<<1) + 1;
  a = cgetg(N + 2, t_POL); a[1] = evalsigne(1)|evalvarn(0);
  t = a+2; l = lgpol(s0); s0 += 2; N0 = n0<<1;
  for (i=0; i < l;  i++) gel(t,i) = gel(s0,i);
  for (   ; i < N0; i++) gel(t,i) = gen_0;
  t = a+2 + N0; l = lgpol(s2); s2 += 2; N1 = N - N0;
  for (i=0; i < l;  i++) gel(t,i) = gel(s2,i);
  for (   ; i < N1; i++) gel(t,i) = gen_0;
  t = a+2 + n0; l = lgpol(s1); s1 += 2;
  for (i=0; i < l; i++)  gel(t,i) = gadd(gel(t,i), gel(s1,i));
  return gerepilecopy(av, normalizepol_lg(a, N+2));
}
/* spec function. nP = lgpol(P) */
static GEN
cook_square(GEN P, long nP)
{
  GEN Q, p0, p1, p2, p3, q, r, t, vp, vm;
  long n0, n3, i, j, n = nP - 1;
  pari_sp av;

  if (n <= COOKSQUARE_LIMIT) return  nP? karasquare(P, nP): pol_0(0);
  av = avma;

  n0 = (n+1) >> 2; n3 = n+1 - 3*n0;
  p0 = P;
  p1 = p0+n0;
  p2 = p1+n0;
  p3 = p2+n0; /* lgpol(p0,p1,p2) = n0, lgpol(p3) = n3 */

  q = cgetg(8,t_VEC) + 4;
  Q = cook_square(p0, n0);
  r = RgX_addspec_shallow(p0,p2, n0,n0);
  t = RgX_addspec_shallow(p1,p3, n0,n3);
  gel(q,-1) = RgX_sub(r,t);
  gel(q,1)  = RgX_add(r,t);
  r = RgX_addspec_shallow(p0,RgX_shiftspec(p2,n0, 2)+2, n0,n0);
  t = gmul2n(RgX_addspec_shallow(p1,RgX_shiftspec(p3,n3, 2)+2, n0,n3), 1);
  gel(q,-2) = RgX_sub(r,t);
  gel(q,2)  = RgX_add(r,t);
  r = RgX_addspec_shallow(p0,RgX_s_mulspec(p2,n0, 9)+2, n0,n0);
  t = gmulsg(3, RgX_addspec_shallow(p1,RgX_s_mulspec(p3,n3, 9)+2, n0,n3));
  gel(q,-3) = RgX_sub(r,t);
  gel(q,3)  = RgX_add(r,t);

  r = new_chunk(7);
  vp = cgetg(4,t_VEC);
  vm = cgetg(4,t_VEC);
  for (i=1; i<=3; i++)
  {
    GEN a = gel(q,i), b = gel(q,-i);
    a = cook_square(a+2, lgpol(a));
    b = cook_square(b+2, lgpol(b));
    gel(vp,i) = RgX_add(b, a);
    gel(vm,i) = RgX_sub(b, a);
  }
  gel(r,0) = Q;
  gel(r,1) = gdivgs(gsub(gsub(gmulgs(gel(vm,2),9),gel(vm,3)),
                     gmulgs(gel(vm,1),45)),
                60);
  gel(r,2) = gdivgs(gadd(gadd(gmulgs(gel(vp,1),270),gmulgs(Q,-490)),
                     gadd(gmulgs(gel(vp,2),-27),gmulgs(gel(vp,3),2))),
                360);
  gel(r,3) = gdivgs(gadd(gadd(gmulgs(gel(vm,1),13),gmulgs(gel(vm,2),-8)),
                    gel(vm,3)),
                48);
  gel(r,4) = gdivgs(gadd(gadd(gmulgs(Q,56),gmulgs(gel(vp,1),-39)),
                     gsub(gmulgs(gel(vp,2),12),gel(vp,3))),
                144);
  gel(r,5) = gdivgs(gsub(gadd(gmulgs(gel(vm,1),-5),gmulgs(gel(vm,2),4)),
                     gel(vm,3)),
                240);
  gel(r,6) = gdivgs(gadd(gadd(gmulgs(Q,-20),gmulgs(gel(vp,1),15)),
                     gadd(gmulgs(gel(vp,2),-6),gel(vp,3))),
                720);
  q = cgetg(2*n+3,t_POL); q[1] = evalsigne(1)|evalvarn(0);
  t = q+2;
  for (i=0; i<=2*n; i++) gel(t,i) = gen_0;
  for (i=0; i<=6; i++,t += n0)
  {
    GEN h = gel(r,i);
    long d = lgpol(h);
    h += 2;
    for (j=0; j<d; j++) gel(t,j) = gadd(gel(t,j), gel(h,j));
  }
  return gerepilecopy(av, normalizepol_lg(q, 2*n+3));
}

static GEN
graeffe(GEN p)
{
  GEN p0, p1, s0, s1;
  long n = degpol(p), n0, n1, i;

  if (!n) return gcopy(p);
  n0 = (n>>1)+1; n1 = n+1 - n0; /* n1 <= n0 <= n1+1 */
  p0 = new_chunk(n0);
  p1 = new_chunk(n1);
  for (i=0; i<n1; i++)
  {
    p0[i] = p[2+(i<<1)];
    p1[i] = p[3+(i<<1)];
  }
  if (n1 != n0)
    p0[i] = p[2+(i<<1)];
  s0 = cook_square(p0, n0);
  s1 = cook_square(p1, n1);
  return RgX_sub(s0, RgX_shift_shallow(s1,1));
}
GEN
ZX_graeffe(GEN p)
{
  pari_sp av = avma;
  GEN p0, p1, s0, s1;
  long n = degpol(p);

  if (!n) return ZX_copy(p);
  RgX_even_odd(p, &p0, &p1);
  /* p = p0(x^2) + x p1(x^2) */
  s0 = ZX_sqr(p0);
  s1 = ZX_sqr(p1);
  return gerepileupto(av, ZX_sub(s0, RgX_shift_shallow(s1,1)));
}
GEN
polgraeffe(GEN p)
{
  pari_sp av = avma;
  GEN p0, p1, s0, s1;
  long n = degpol(p);

  if (typ(p) != t_POL) pari_err_TYPE("polgraeffe",p);
  n = degpol(p);
  if (!n) return gcopy(p);
  RgX_even_odd(p, &p0, &p1);
  /* p = p0(x^2) + x p1(x^2) */
  s0 = RgX_sqr(p0);
  s1 = RgX_sqr(p1);
  return gerepileupto(av, RgX_sub(s0, RgX_shift_shallow(s1,1)));
}

/********************************************************************/
/**                                                                **/
/**                       MODULUS OF ROOTS                         **/
/**                                                                **/
/********************************************************************/

/* Quick approximation to log2(|x|); first define y s.t. |y-x| < 2^-32 then
 * return y rounded to 2 ulp. In particular, if result < 2^21, absolute error
 * is bounded by 2^-31. If result > 2^21, it is correct to 2 ulp */
static double
mydbllog2i(GEN x)
{
#ifdef LONG_IS_64BIT
  const double W = 1/(4294967296. * 4294967296.); /* 2^-64 */
#else
  const double W = 1/4294967296.; /*2^-32*/
#endif
  GEN m;
  long lx = lgefint(x);
  double l;
  if (lx == 2) return -pariINFINITY;
  m = int_MSW(x);
  l = (double)(ulong)*m;
  if (lx == 3) return log2(l);
  l += ((double)(ulong)*int_precW(m)) * W;
  /* at least m = min(53,BIL) bits are correct in the mantissa, thus log2
   * is correct with error < log(1 + 2^-m) ~ 2^-m. Adding the correct
   * exponent BIL(lx-3) causes 1ulp further round-off error */
  return log2(l) + (double)(BITS_IN_LONG*(lx-3));
}

/* return log(|x|) or -pariINFINITY */
static double
mydbllogr(GEN x) {
  if (!signe(x)) return -pariINFINITY;
  return M_LN2*dbllog2r(x);
}

/* return log2(|x|) or -pariINFINITY */
static double
mydbllog2r(GEN x) {
  if (!signe(x)) return -pariINFINITY;
  return dbllog2r(x);
}
double
dbllog2(GEN z)
{
  double x, y;
  switch(typ(z))
  {
    case t_INT: return mydbllog2i(z);
    case t_FRAC: return mydbllog2i(gel(z,1))-mydbllog2i(gel(z,2));
    case t_REAL: return mydbllog2r(z);
    default: /*t_COMPLEX*/
      x = dbllog2(gel(z,1));
      y = dbllog2(gel(z,2));
      if (x == -pariINFINITY) return y;
      if (y == -pariINFINITY) return x;
      if (fabs(x-y) > 10) return maxdd(x,y);
      return x + 0.5*log2(1 + exp2(2*(y-x)));
  }
}
static GEN /* beware overflow */
dblexp(double x) { return fabs(x) < 100.? dbltor(exp(x)): mpexp(dbltor(x)); }

/* find s such that  A_h <= 2^s <= 2 A_i  for one h and all i < n = deg(p),
 * with  A_i := (binom(n,i) lc(p) / p_i) ^ 1/(n-i), and  p = sum p_i X^i */
static long
findpower(GEN p)
{
  double x, L, mins = pariINFINITY;
  long n = degpol(p),i;

  L = dbllog2(gel(p,n+2)); /* log2(lc * binom(n,i)) */
  for (i=n-1; i>=0; i--)
  {
    L += log2((double)(i+1) / (double)(n-i));
    x = dbllog2(gel(p,i+2));
    if (x != -pariINFINITY)
    {
      double s = (L - x) / (double)(n-i);
      if (s < mins) mins = s;
    }
  }
  i = (long)ceil(mins);
  if (i - mins > 1 - 1e-12) i--;
  return i;
}

/* returns the exponent for logmodulus(), from the Newton diagram */
static long
newton_polygon(GEN p, long k)
{
  pari_sp av = avma;
  double *logcoef, slope;
  long n = degpol(p), i, j, h, l, *vertex;

  logcoef = (double*)stack_malloc_align((n+1)*sizeof(double), sizeof(double));
  vertex = (long*)new_chunk(n+1);

  /* vertex[i] = 1 if i a vertex of convex hull, 0 otherwise */
  for (i=0; i<=n; i++) { logcoef[i] = dbllog2(gel(p,2+i)); vertex[i] = 0; }
  vertex[0] = 1; /* sentinel */
  for (i=0; i < n; i=h)
  {
    slope = logcoef[i+1]-logcoef[i];
    for (j = h = i+1; j<=n; j++)
    {
      double pij = (logcoef[j]-logcoef[i])/(double)(j-i);
      if (slope < pij) { slope = pij; h = j; }
    }
    vertex[h] = 1;
  }
  h = k;   while (!vertex[h]) h++;
  l = k-1; while (!vertex[l]) l--;
  avma = av;
  return (long)floor((logcoef[h]-logcoef[l])/(double)(h-l) + 0.5);
}

/* change z into z*2^e, where z is real or complex of real */
static void
myshiftrc(GEN z, long e)
{
  if (typ(z)==t_COMPLEX)
  {
    if (signe(gel(z,1))) shiftr_inplace(gel(z,1), e);
    if (signe(gel(z,2))) shiftr_inplace(gel(z,2), e);
  }
  else
    if (signe(z)) shiftr_inplace(z, e);
}

/* return z*2^e, where z is integer or complex of integer (destroy z) */
static GEN
myshiftic(GEN z, long e)
{
  if (typ(z)==t_COMPLEX)
  {
    gel(z,1) = signe(gel(z,1))? mpshift(gel(z,1),e): gen_0;
    gel(z,2) = mpshift(gel(z,2),e);
    return z;
  }
  return signe(z)? mpshift(z,e): gen_0;
}

static GEN
RgX_gtofp_bit(GEN q, long bit)
{
  if (bit < 0) bit = 0;
  return RgX_gtofp(q, nbits2prec(bit));
}

static GEN
mygprecrc(GEN x, long prec, long e)
{
  GEN y;
  switch(typ(x))
  {
    case t_REAL: return signe(x)? rtor(x, prec): real_0_bit(e);
    case t_COMPLEX:
      y = cgetg(3,t_COMPLEX);
      gel(y,1) = mygprecrc(gel(x,1),prec,e);
      gel(y,2) = mygprecrc(gel(x,2),prec,e);
      return y;
    default: return gcopy(x);
  }
}

/* gprec behaves badly with the zero for polynomials.
The second parameter in mygprec is the precision in base 2 */
static GEN
mygprec(GEN x, long bit)
{
  long lx, i, e, prec;
  GEN y;

  if (bit < 0) bit = 0; /* should rarely happen */
  e = gexpo(x) - bit;
  prec = nbits2prec(bit);
  switch(typ(x))
  {
    case t_POL:
      y = cgetg_copy(x, &lx); y[1] = x[1];
      for (i=2; i<lx; i++) gel(y,i) = mygprecrc(gel(x,i),prec,e);
      break;

    default: y = mygprecrc(x,prec,e);
  }
  return y;
}

/* normalize a polynomial p, that is change it with coefficients in Z[i],
after making product by 2^shift */
static GEN
pol_to_gaussint(GEN p, long shift)
{
  long i, l = lg(p);
  GEN q = cgetg(l, t_POL); q[1] = p[1];
  for (i=2; i<l; i++) gel(q,i) = gtrunc2n(gel(p,i), shift);
  return q;
}

/* returns a polynomial q in Z[i][x] keeping bit bits of p */
static GEN
eval_rel_pol(GEN p, long bit)
{
  long i;
  for (i = 2; i < lg(p); i++)
    if (gequal0(gel(p,i))) gel(p,i) = gen_0; /* bad behavior of gexpo */
  return pol_to_gaussint(p, bit-gexpo(p)+1);
}

/* returns p(R*x)/R^n (in R or R[i]), R = exp(lrho), bit bits of precision */
static GEN
homothetie(GEN p, double lrho, long bit)
{
  GEN q, r, t, iR;
  long n = degpol(p), i;

  iR = mygprec(dblexp(-lrho),bit);
  q = mygprec(p, bit);
  r = cgetg(n+3,t_POL); r[1] = p[1];
  t = iR; r[n+2] = q[n+2];
  for (i=n-1; i>0; i--)
  {
    gel(r,i+2) = gmul(t, gel(q,i+2));
    t = mulrr(t, iR);
  }
  gel(r,2) = gmul(t, gel(q,2)); return r;
}

/* change q in 2^(n*e) p(x*2^(-e)), n=deg(q)  [ ~as above with R = 2^-e ]*/
static void
homothetie2n(GEN p, long e)
{
  if (e)
  {
    long i,n = lg(p)-1;
    for (i=2; i<=n; i++) myshiftrc(gel(p,i), (n-i)*e);
  }
}

/* return 2^f * 2^(n*e) p(x*2^(-e)), n=deg(q) */
static void
homothetie_gauss(GEN p, long e, long f)
{
  if (e || f)
  {
    long i, n = lg(p)-1;
    for (i=2; i<=n; i++) gel(p,i) = myshiftic(gel(p,i), f+(n-i)*e);
  }
}

/* Lower bound on the modulus of the largest root z_0
 * k is set to an upper bound for #{z roots, |z-z_0| < eps} */
static double
lower_bound(GEN p, long *k, double eps)
{
  long n = degpol(p), i, j;
  pari_sp ltop = avma;
  GEN a, s, S, ilc;
  double r, R, rho;

  if (n < 4) { *k = n; return 0.; }
  S = cgetg(5,t_VEC);
  a = cgetg(5,t_VEC); ilc = gdiv(real_1(DEFAULTPREC), gel(p,n+2));
  for (i=1; i<=4; i++) gel(a,i) = gmul(ilc,gel(p,n+2-i));
  /* i = 1 split out from next loop for efficiency and initialization */
  s = gel(a,1);
  gel(S,1) = gneg(s); /* Newton sum S_i */
  rho = r = gtodouble(gabs(s,3));
  R = r / n;
  for (i=2; i<=4; i++)
  {
    s = gmulsg(i,gel(a,i));
    for (j=1; j<i; j++) s = gadd(s, gmul(gel(S,j),gel(a,i-j)));
    gel(S,i) = gneg(s); /* Newton sum S_i */
    r = gtodouble(gabs(s,3));
    if (r > 0.)
    {
      r = exp(log(r/n) / (double)i);
      if (r > R) R = r;
    }
  }
  if (R > 0. && eps < 1.2)
    *k = (long)floor((rho/R + n) / (1 + exp(-eps)*cos(eps)));
  else
    *k = n;
  avma = ltop; return R;
}

/* return R such that exp(R - tau) <= rho_n(P) <= exp(R + tau)
 * P(0) != 0 and P non constant */
static double
logmax_modulus(GEN p, double tau)
{
  GEN r, q, aux, gunr;
  pari_sp av, ltop = avma;
  long i,k,n=degpol(p),nn,bit,M,e;
  double rho,eps, tau2 = (tau > 3.0)? 0.5: tau/6.;

  r = cgeti(BIGDEFAULTPREC);
  av = avma;

  eps = - 1/log(1.5*tau2); /* > 0 */
  bit = (long) ((double) n*log2(1./tau2)+3*log2((double) n))+1;
  gunr = real_1_bit(bit+2*n);
  aux = gdiv(gunr, gel(p,2+n));
  q = RgX_Rg_mul(p, aux); gel(q,2+n) = gunr;
  e = findpower(q);
  homothetie2n(q,e);
  affsi(e, r);
  q = pol_to_gaussint(q, bit);
  M = (long) (log2( log(4.*n) / (2*tau2) )) + 2;
  nn = n;
  for (i=0,e=0;;)
  { /* nn = deg(q) */
    rho = lower_bound(q, &k, eps);
    if (rho > exp2(-(double)e)) e = (long)-floor(log2(rho));
    affii(shifti(addis(r,e), 1), r);
    if (++i == M) break;

    bit = (long) ((double)k * log2(1./tau2) +
                     (double)(nn-k)*log2(1./eps) + 3*log2((double)nn)) + 1;
    homothetie_gauss(q, e, bit-(long)floor(dbllog2(gel(q,2+nn))+0.5));
    nn -= RgX_valrem(q, &q);
    set_karasquare_limit(gexpo(q));
    q = gerepileupto(av, graeffe(q));
    tau2 *= 1.5; if (tau2 > 0.9) tau2 = 0.5;
    eps = -1/log(tau2); /* > 0 */
    e = findpower(q);
  }
  if (!signe(r)) { avma = ltop; return 0.; }
  r = itor(r, DEFAULTPREC); shiftr_inplace(r, -M);
  avma = ltop; return -rtodbl(r) * M_LN2; /* -log(2) sum e_i 2^-i */
}

static GEN
RgX_normalize1(GEN x)
{
  long i, n = lg(x)-1;
  GEN y;
  for (i = n; i > 1; i--)
    if (!gequal0( gel(x,i) )) break;
  if (i == n) return x;
  pari_warn(warner,"normalizing a polynomial with 0 leading term");
  if (i == 1) pari_err_ROOTS0("roots");
  y = cgetg(i+1, t_POL); y[1] = x[1];
  for (; i > 1; i--) gel(y,i) = gel(x,i);
  return y;
}

static GEN
polrootsbound_i(GEN P, double TAU)
{
  pari_sp av = avma;
  double d;
  (void)RgX_valrem_inexact(P,&P);
  P = RgX_normalize1(P);
  switch(degpol(P))
  {
    case -1: pari_err_ROOTS0("roots");
    case 0:  avma = av; return gen_0;
  }
  d = logmax_modulus(P, TAU) + TAU;
  /* not dblexp: result differs on ARM emulator */
  return gerepileuptoleaf(av, mpexp(dbltor(d)));
}
GEN
polrootsbound(GEN P, GEN tau)
{
  if (typ(P) != t_POL) pari_err_TYPE("polrootsbound",P);
  checkvalidpol(P, "polrootsbound");
  return polrootsbound_i(P, tau? gtodouble(tau): 0.01);
}

/* log of modulus of the smallest root of p, with relative error tau */
static double
logmin_modulus(GEN p, double tau)
{
  pari_sp av = avma;
  double r;

  if (gequal0(gel(p,2))) return -pariINFINITY;
  r = - logmax_modulus(RgX_recip_shallow(p),tau);
  avma = av; return r;
}

/* return the log of the k-th modulus (ascending order) of p, rel. error tau*/
static double
logmodulus(GEN p, long k, double tau)
{
  GEN q;
  long i, kk = k, imax, n = degpol(p), nn, bit, e;
  pari_sp av, ltop=avma;
  double r, tau2 = tau/6;

  bit = (long)(n * (2. + log2(3.*n/tau2)));
  av = avma;
  q = gprec_w(p, nbits2prec(bit));
  q = RgX_gtofp_bit(q, bit);
  e = newton_polygon(q,k);
  r = (double)e;
  homothetie2n(q,e);
  imax = (long)(log2(3./tau) + log2(log(4.*n)))+1;
  for (i=1; i<imax; i++)
  {
    q = eval_rel_pol(q,bit);
    kk -= RgX_valrem(q, &q);
    nn = degpol(q);

    set_karasquare_limit(bit);
    q = gerepileupto(av, graeffe(q));
    e = newton_polygon(q,kk);
    r += e / exp2((double)i);
    q = RgX_gtofp_bit(q, bit);
    homothetie2n(q,e);

    tau2 *= 1.5; if (tau2 > 1.) tau2 = 1.;
    bit = 1 + (long)(nn*(2. + log2(3.*nn/tau2)));
  }
  avma = ltop; return -r * M_LN2;
}

/* return the log of the k-th modulus r_k of p, rel. error tau, knowing that
 * rmin < r_k < rmax. This information helps because we may reduce precision
 * quicker */
static double
logpre_modulus(GEN p, long k, double tau, double lrmin, double lrmax)
{
  GEN q;
  long n = degpol(p), i, imax, imax2, bit;
  pari_sp ltop = avma, av;
  double lrho, aux, tau2 = tau/6.;

  aux = (lrmax - lrmin) / 2. + 4*tau2;
  imax = (long) log2(log((double)n)/ aux);
  if (imax <= 0) return logmodulus(p,k,tau);

  lrho  = (lrmin + lrmax) / 2;
  av = avma;
  bit = (long)(n*(2. + aux / M_LN2 - log2(tau2)));
  q = homothetie(p, lrho, bit);
  imax2 = (long)(log2(3./tau * log(4.*n))) + 1;
  if (imax > imax2) imax = imax2;

  for (i=0; i<imax; i++)
  {
    q = eval_rel_pol(q,bit);
    set_karasquare_limit(bit);
    q = gerepileupto(av, graeffe(q));
    aux = 2*aux + 2*tau2;
    tau2 *= 1.5;
    bit = (long)(n*(2. + aux / M_LN2 - log2(1-exp(-tau2))));
    q = RgX_gtofp_bit(q, bit);
  }
  aux = exp2((double)imax);
  aux = logmodulus(q,k, aux*tau/3.) / aux;
  avma = ltop; return lrho + aux;
}

static double
ind_maxlog2(GEN q)
{
  long i, k = -1;
  double L = - pariINFINITY;
  for (i=0; i<=degpol(q); i++)
  {
    double d = dbllog2(gel(q,2+i));
    if (d > L) { L = d; k = i; }
  }
  return k;
}

/* Returns k such that r_k e^(-tau) < R < r_{k+1} e^tau.
 * Assume that l <= k <= n-l */
static long
dual_modulus(GEN p, double lrho, double tau, long l)
{
  long i, imax, delta_k = 0, n = degpol(p), nn, v2, v, bit, ll = l;
  double tau2 = tau * 7./8.;
  pari_sp av = avma;
  GEN q;

  bit = 6*n - 5*l + (long)(n*(-log2(tau2) + tau2 * 8./7.));
  q = homothetie(p, lrho, bit);
  imax = (long)(log(log(2.*n)/tau2)/log(7./4.)+1);

  for (i=0; i<imax; i++)
  {
    q = eval_rel_pol(q,bit); v2 = n - degpol(q);
    v = RgX_valrem(q, &q);
    ll -= maxss(v, v2); if (ll < 0) ll = 0;

    nn = degpol(q); delta_k += v;
    if (!nn) return delta_k;

    set_karasquare_limit(bit);
    q = gerepileupto(av, graeffe(q));
    tau2 *= 7./4.;
    bit = 6*nn - 5*ll + (long)(nn*(-log2(tau2) + tau2 * 8./7.));
  }
  avma = av; return delta_k + (long)ind_maxlog2(q);
}

/********************************************************************/
/**                                                                **/
/**              FACTORS THROUGH CIRCLE INTEGRATION                **/
/**                                                                **/
/********************************************************************/
/* l power of 2 */
static void
fft(GEN Omega, GEN p, GEN f, long step, long l)
{
  pari_sp ltop;
  long i, l1, l2, l3, rapi, step4;
  GEN f1, f2, f3, f02, f13, g02, g13, ff;

  if (l == 2)
  {
    gel(f,0) = gadd(gel(p,0),gel(p,step));
    gel(f,1) = gsub(gel(p,0),gel(p,step)); return;
  }
  if (l == 4)
  {
    f1 = gadd(gel(p,0),   gel(p,step<<1));
    f2 = gsub(gel(p,0),   gel(p,step<<1));
    f3 = gadd(gel(p,step),gel(p,3*step));
    f02= gsub(gel(p,step),gel(p,3*step));
    f02 = mulcxI(f02);
    gel(f,0) = gadd(f1, f3);
    gel(f,1) = gadd(f2, f02);
    gel(f,2) = gsub(f1, f3);
    gel(f,3) = gsub(f2, f02); return;
  }

  ltop = avma;
  l1 = l>>2; l2 = 2*l1; l3 = l1+l2; step4 = step<<2;
  fft(Omega,p,          f,   step4,l1);
  fft(Omega,p+step,     f+l1,step4,l1);
  fft(Omega,p+(step<<1),f+l2,step4,l1);
  fft(Omega,p+3*step,   f+l3,step4,l1);

  ff = cgetg(l+1,t_VEC);
  for (i=0; i<l1; i++)
  {
    rapi = step*i;
    f1 = gmul(gel(Omega,rapi),    gel(f,i+l1));
    f2 = gmul(gel(Omega,rapi<<1), gel(f,i+l2));
    f3 = gmul(gel(Omega,3*rapi),  gel(f,i+l3));

    f02 = gadd(gel(f,i),f2);
    g02 = gsub(gel(f,i),f2);
    f13 = gadd(f1,f3);
    g13 = mulcxI(gsub(f1,f3));

    gel(ff,i+1)    = gadd(f02, f13);
    gel(ff,i+l1+1) = gadd(g02, g13);
    gel(ff,i+l2+1) = gsub(f02, f13);
    gel(ff,i+l3+1) = gsub(g02, g13);
  }
  ff = gerepilecopy(ltop,ff);
  for (i=0; i<l; i++) f[i] = ff[i+1];
}

GEN
FFTinit(long k, long prec)
{
  if (k <= 0) pari_err_DOMAIN("FFTinit", "k", "<=", gen_0, stoi(k));
  return grootsof1(1L << k, prec);
}

GEN
FFT(GEN x, GEN Omega)
{
  long i, l = lg(Omega), n = lg(x);
  GEN y, z;
  if (!is_vec_t(typ(x))) pari_err_TYPE("FFT",x);
  if (typ(Omega) != t_VEC) pari_err_TYPE("FFT",Omega);
  if (n > l) pari_err_DIM("FFT");

  if (n < l) {
    z = cgetg(l, t_VECSMALL); /* cf stackdummy */
    for (i = 1; i < n; i++) z[i] = x[i];
    for (     ; i < l; i++) gel(z,i) = gen_0;
  }
  else z = x;
  y = cgetg(l, t_VEC);
  fft(Omega+1, z+1, y+1, 1, l-1);
  return y;
}

/* returns 1 if p has only real coefficients, 0 else */
static int
isreal(GEN p)
{
  long i;
  for (i = lg(p)-1; i > 1; i--)
    if (typ(gel(p,i)) == t_COMPLEX) return 0;
  return 1;
}

/* x non complex */
static GEN
abs_update_r(GEN x, double *mu) {
  GEN y = gtofp(x, DEFAULTPREC);
  double ly = mydbllogr(y); if (ly < *mu) *mu = ly;
  setabssign(y); return y;
}
/* return |x|, low accuracy. Set *mu = min(log(y), *mu) */
static GEN
abs_update(GEN x, double *mu) {
  GEN y, xr, yr;
  double ly;
  if (typ(x) != t_COMPLEX) return abs_update_r(x, mu);
  xr = gel(x,1);
  yr = gel(x,2);
  if (gequal0(xr)) return abs_update_r(yr,mu);
  if (gequal0(yr)) return abs_update_r(xr,mu);
  /* have to treat 0 specially: 0E-10 + 1e-20 = 0E-10 */
  xr = gtofp(xr, DEFAULTPREC);
  yr = gtofp(yr, DEFAULTPREC);
  y = sqrtr(addrr(sqrr(xr), sqrr(yr)));
  ly = mydbllogr(y); if (ly < *mu) *mu = ly;
  return y;
}

static void
initdft(GEN *Omega, GEN *prim, long N, long Lmax, long bit)
{
  long prec = nbits2prec(bit);
  *Omega = grootsof1(Lmax, prec) + 1;
  *prim = rootsof1u_cx(N, prec);
}

static void
parameters(GEN p, long *LMAX, double *mu, double *gamma,
           int polreal, double param, double param2)
{
  GEN q, pc, Omega, A, RU, prim, g, TWO;
  long n = degpol(p), bit, NN, K, i, j, Lmax;
  pari_sp av2, av = avma;

  bit = gexpo(p) + (long)param2+8;
  Lmax = 4; while (Lmax <= n) Lmax <<= 1;
  NN = (long)(param*3.14)+1; if (NN < Lmax) NN = Lmax;
  K = NN/Lmax; if (K & 1) K++;
  NN = Lmax*K;
  if (polreal) K = K/2+1;

  initdft(&Omega, &prim, NN, Lmax, bit);
  q = mygprec(p,bit) + 2;
  A = cgetg(Lmax+1,t_VEC); A++;
  pc= cgetg(Lmax+1,t_VEC); pc++;
  for (i=0; i <= n; i++) gel(pc,i)= gel(q,i);
  for (   ; i<Lmax; i++) gel(pc,i) = gen_0;

  *mu = pariINFINITY;
  g = real_0_bit(-bit);
  TWO = real2n(1, DEFAULTPREC);
  av2 = avma;
  RU = gen_1;
  for (i=0; i<K; i++)
  {
    if (i) {
      GEN z = RU;
      for (j=1; j<n; j++)
      {
        gel(pc,j) = gmul(gel(q,j),z);
        z = gmul(z,RU); /* RU = prim^i, z=prim^(ij) */
      }
      gel(pc,n) = gmul(gel(q,n),z);
    }

    fft(Omega,pc,A,1,Lmax);
    if (polreal && i>0 && i<K-1)
      for (j=0; j<Lmax; j++) g = addrr(g, divrr(TWO, abs_update(gel(A,j),mu)));
    else
      for (j=0; j<Lmax; j++) g = addrr(g, invr(abs_update(gel(A,j),mu)));
    RU = gmul(RU, prim);
    if (gc_needed(av,1))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"parameters");
      gerepileall(av2,2, &g,&RU);
    }
  }
  *gamma = mydbllog2r(divru(g,NN));
  *LMAX = Lmax; avma = av;
}

/* NN is a multiple of Lmax */
static void
dft(GEN p, long k, long NN, long Lmax, long bit, GEN F, GEN H, long polreal)
{
  GEN Omega, q, qd, pc, pd, A, B, C, RU, aux, U, W, prim, prim2;
  long n = degpol(p), i, j, K;
  pari_sp ltop;

  initdft(&Omega, &prim, NN, Lmax, bit);
  RU = cgetg(n+2,t_VEC) + 1;

  K = NN/Lmax; if (polreal) K = K/2+1;
  q = mygprec(p,bit);
  qd = RgX_deriv(q);

  A = cgetg(Lmax+1,t_VEC); A++;
  B = cgetg(Lmax+1,t_VEC); B++;
  C = cgetg(Lmax+1,t_VEC); C++;
  pc = cgetg(Lmax+1,t_VEC); pc++;
  pd = cgetg(Lmax+1,t_VEC); pd++;
  pc[0] = q[2];  for (i=n+1; i<Lmax; i++) gel(pc,i) = gen_0;
  pd[0] = qd[2]; for (i=n;   i<Lmax; i++) gel(pd,i) = gen_0;

  ltop = avma;
  W = cgetg(k+1,t_VEC);
  U = cgetg(k+1,t_VEC);
  for (i=1; i<=k; i++) gel(W,i) = gel(U,i) = gen_0;

  gel(RU,0) = gen_1;
  prim2 = gen_1;
  for (i=0; i<K; i++)
  {
    gel(RU,1) = prim2;
    for (j=1; j<n; j++) gel(RU,j+1) = gmul(gel(RU,j),prim2);
    /* RU[j] = prim^(ij)= prim2^j */

    for (j=1; j<n; j++) gel(pd,j) = gmul(gel(qd,j+2),gel(RU,j));
    fft(Omega,pd,A,1,Lmax);
    for (j=1; j<=n; j++) gel(pc,j) = gmul(gel(q,j+2),gel(RU,j));
    fft(Omega,pc,B,1,Lmax);
    for (j=0; j<Lmax; j++) gel(C,j) = ginv(gel(B,j));
    for (j=0; j<Lmax; j++) gel(B,j) = gmul(gel(A,j),gel(C,j));
    fft(Omega,B,A,1,Lmax);
    fft(Omega,C,B,1,Lmax);

    if (polreal) /* p has real coefficients */
    {
      if (i>0 && i<K-1)
      {
        for (j=1; j<=k; j++)
        {
          gel(W,j) = gadd(gel(W,j), gshift(mulreal(gel(A,j+1),gel(RU,j+1)),1));
          gel(U,j) = gadd(gel(U,j), gshift(mulreal(gel(B,j),gel(RU,j)),1));
        }
      }
      else
      {
        for (j=1; j<=k; j++)
        {
          gel(W,j) = gadd(gel(W,j), mulreal(gel(A,j+1),gel(RU,j+1)));
          gel(U,j) = gadd(gel(U,j), mulreal(gel(B,j),gel(RU,j)));
        }
      }
    }
    else
    {
      for (j=1; j<=k; j++)
      {
        gel(W,j) = gadd(gel(W,j), gmul(gel(A,j+1),gel(RU,j+1)));
        gel(U,j) = gadd(gel(U,j), gmul(gel(B,j),gel(RU,j)));
      }
    }
    prim2 = gmul(prim2,prim);
    gerepileall(ltop,3, &W,&U,&prim2);
  }

  for (i=1; i<=k; i++)
  {
    aux=gel(W,i);
    for (j=1; j<i; j++) aux = gadd(aux, gmul(gel(W,i-j),gel(F,k+2-j)));
    gel(F,k+2-i) = gdivgs(aux,-i*NN);
  }
  for (i=0; i<k; i++)
  {
    aux=gel(U,k-i);
    for (j=1+i; j<k; j++) aux = gadd(aux,gmul(gel(F,2+j),gel(U,j-i)));
    gel(H,i+2) = gdivgs(aux,NN);
  }
}

#define NEWTON_MAX 10
static GEN
refine_H(GEN F, GEN G, GEN HH, long bit, long Sbit)
{
  GEN H = HH, D, aux;
  pari_sp ltop = avma;
  long error, i, bit1, bit2;

  D = Rg_RgX_sub(gen_1, RgX_rem(RgX_mul(H,G),F)); error = gexpo(D);
  bit2 = bit + Sbit;
  for (i=0; error>-bit && i<NEWTON_MAX && error<=0; i++)
  {
    if (gc_needed(ltop,1))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"refine_H");
      gerepileall(ltop,2, &D,&H);
    }
    bit1 = -error + Sbit;
    aux = RgX_mul(mygprec(H,bit1), mygprec(D,bit1));
    aux = RgX_rem(mygprec(aux,bit1), mygprec(F,bit1));

    bit1 = -error*2 + Sbit; if (bit1 > bit2) bit1 = bit2;
    H = RgX_add(mygprec(H,bit1), aux);
    D = Rg_RgX_sub(gen_1, RgX_rem(RgX_mul(H,G),F));
    error = gexpo(D); if (error < -bit1) error = -bit1;
  }
  if (error > -bit/2) return NULL; /* FAIL */
  return gerepilecopy(ltop,H);
}

/* return 0 if fails, 1 else */
static long
refine_F(GEN p, GEN *F, GEN *G, GEN H, long bit, double gamma)
{
  GEN f0, FF, GG, r, HH = H;
  long error, i, bit1 = 0, bit2, Sbit, Sbit2,  enh, normF, normG, n = degpol(p);
  pari_sp av = avma;

  FF = *F; GG = RgX_divrem(p, FF, &r);
  error = gexpo(r); if (error <= -bit) error = 1-bit;
  normF = gexpo(FF);
  normG = gexpo(GG);
  enh = gexpo(H); if (enh < 0) enh = 0;
  Sbit = normF + 2*normG + enh + (long)(4.*log2((double)n)+gamma) + 1;
  Sbit2 = enh + 2*(normF+normG) + (long)(2.*gamma+5.*log2((double)n)) + 1;
  bit2 = bit + Sbit;
  for (i=0; error>-bit && i<NEWTON_MAX && error<=0; i++)
  {
    if (bit1 == bit2 && i >= 2) { Sbit += n; Sbit2 += n; bit2 += n; }
    if (gc_needed(av,1))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"refine_F");
      gerepileall(av,4, &FF,&GG,&r,&HH);
    }

    bit1 = -error + Sbit2;
    HH = refine_H(mygprec(FF,bit1), mygprec(GG,bit1), mygprec(HH,bit1),
                  1-error, Sbit2);
    if (!HH) return 0; /* FAIL */

    bit1 = -error + Sbit;
    r = RgX_mul(mygprec(HH,bit1), mygprec(r,bit1));
    f0 = RgX_rem(mygprec(r,bit1), mygprec(FF,bit1));

    bit1 = -2*error + Sbit; if (bit1 > bit2) bit1 = bit2;
    FF = gadd(mygprec(FF,bit1),f0);

    bit1 = -3*error + Sbit; if (bit1 > bit2) bit1 = bit2;
    GG = RgX_divrem(mygprec(p,bit1), mygprec(FF,bit1), &r);
    error = gexpo(r); if (error < -bit1) error = -bit1;
  }
  if (error>-bit) return 0; /* FAIL */
  *F = FF; *G = GG; return 1;
}

/* returns F and G from the unit circle U such that |p-FG|<2^(-bit) |cd|,
where cd is the leading coefficient of p */
static void
split_fromU(GEN p, long k, double delta, long bit,
            GEN *F, GEN *G, double param, double param2)
{
  GEN pp, FF, GG, H;
  long n = degpol(p), NN, bit2, Lmax;
  int polreal = isreal(p);
  pari_sp ltop;
  double mu, gamma;

  pp = gdiv(p, gel(p,2+n));
  parameters(pp, &Lmax,&mu,&gamma, polreal,param,param2);

  H  = cgetg(k+2,t_POL); H[1] = p[1];
  FF = cgetg(k+3,t_POL); FF[1]= p[1];
  gel(FF,k+2) = gen_1;

  NN = (long)(0.5/delta); NN |= 1; if (NN < 2) NN = 2;
  NN *= Lmax; ltop = avma;
  for(;;)
  {
    bit2 = (long)(((double)NN*delta-mu)/M_LN2) + gexpo(pp) + 8;
    dft(pp, k, NN, Lmax, bit2, FF, H, polreal);
    if (refine_F(pp,&FF,&GG,H,bit,gamma)) break;
    NN <<= 1; avma = ltop;
  }
  *G = gmul(GG,gel(p,2+n)); *F = FF;
}

static void
optimize_split(GEN p, long k, double delta, long bit,
            GEN *F, GEN *G, double param, double param2)
{
  long n = degpol(p);
  GEN FF, GG;

  if (k <= n/2)
    split_fromU(p,k,delta,bit,F,G,param,param2);
  else
  {
    split_fromU(RgX_recip_shallow(p),n-k,delta,bit,&FF,&GG,param,param2);
    *F = RgX_recip_shallow(GG);
    *G = RgX_recip_shallow(FF);
  }
}

/********************************************************************/
/**                                                                **/
/**               SEARCH FOR SEPARATING CIRCLE                     **/
/**                                                                **/
/********************************************************************/

/* return p(2^e*x) *2^(-n*e) */
static void
scalepol2n(GEN p, long e)
{
  long i,n=lg(p)-1;
  for (i=2; i<=n; i++) gel(p,i) = gmul2n(gel(p,i),(i-n)*e);
}

/* returns p(x/R)*R^n */
static GEN
scalepol(GEN p, GEN R, long bit)
{
  GEN q,aux,gR;
  long i;

  aux = gR = mygprec(R,bit); q = mygprec(p,bit);
  for (i=lg(p)-2; i>=2; i--)
  {
    gel(q,i) = gmul(aux,gel(q,i));
    aux = gmul(aux,gR);
  }
  return q;
}

/* return (conj(a)X-1)^n * p[ (X-a) / (conj(a)X-1) ] */
static GEN
conformal_pol(GEN p, GEN a)
{
  GEN z, r, ma = gneg(a), ca = conj_i(a);
  long n = degpol(p), i;
  pari_sp av = avma;

  z = mkpoln(2, ca, gen_m1);
  r = scalarpol(gel(p,2+n), 0);
  for (i=n-1; ; i--)
  {
    r = RgX_addmulXn_shallow(r, gmul(ma,r), 1); /* r *= (X - a) */
    r = gadd(r, gmul(z, gel(p,2+i)));
    if (i == 0) return gerepileupto(av, r);
    z = RgX_addmulXn_shallow(gmul(z,ca), gneg(z), 1); /* z *= conj(a)X - 1 */
    if (gc_needed(av,2))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"conformal_pol");
      gerepileall(av,2, &r,&z);
    }
  }
}

static const double UNDEF = -100000.;

static double
logradius(double *radii, GEN p, long k, double aux, double *delta)
{
  long i, n = degpol(p);
  double lrho, lrmin, lrmax;
  if (k > 1)
  {
    i = k-1; while (i>0 && radii[i] == UNDEF) i--;
    lrmin = logpre_modulus(p,k,aux, radii[i], radii[k]);
  }
  else /* k=1 */
    lrmin = logmin_modulus(p,aux);
  radii[k] = lrmin;

  if (k+1<n)
  {
    i = k+2; while (i<=n && radii[i] == UNDEF) i++;
    lrmax = logpre_modulus(p,k+1,aux, radii[k+1], radii[i]);
  }
  else /* k+1=n */
    lrmax = logmax_modulus(p,aux);
  radii[k+1] = lrmax;

  lrho = radii[k];
  for (i=k-1; i>=1; i--)
  {
    if (radii[i] == UNDEF || radii[i] > lrho)
      radii[i] = lrho;
    else
      lrho = radii[i];
  }
  lrho = radii[k+1];
  for (i=k+1; i<=n; i++)
  {
    if (radii[i] == UNDEF || radii[i] < lrho)
      radii[i] = lrho;
    else
      lrho = radii[i];
  }
  *delta = (lrmax - lrmin) / 2;
  if (*delta > 1.) *delta = 1.;
  return (lrmin + lrmax) / 2;
}

static void
update_radius(long n, double *radii, double lrho, double *par, double *par2)
{
  double t, param = 0., param2 = 0.;
  long i;
  for (i=1; i<=n; i++)
  {
    radii[i] -= lrho;
    t = fabs(rtodbl( invr(subsr(1, dblexp(radii[i]))) ));
    param += t; if (t > 1.) param2 += log2(t);
  }
  *par = param; *par2 = param2;
}

/* apply the conformal mapping then split from U */
static void
conformal_mapping(double *radii, GEN ctr, GEN p, long k, long bit,
                  double aux, GEN *F,GEN *G)
{
  long bit2, n = degpol(p), i;
  pari_sp ltop = avma, av;
  GEN q, FF, GG, a, R;
  double lrho, delta, param, param2;
  /* n * (2.*log2(2.732)+log2(1.5)) + 1 */
  bit2 = bit + (long)(n*3.4848775) + 1;
  a = sqrtr_abs( stor(3, 2*MEDDEFAULTPREC - 2) );
  a = divrs(a, -6);
  a = gmul(mygprec(a,bit2), mygprec(ctr,bit2)); /* a = -ctr/2sqrt(3) */

  av = avma;
  q = conformal_pol(mygprec(p,bit2), a);
  for (i=1; i<=n; i++)
    if (radii[i] != UNDEF) /* update array radii */
    {
      pari_sp av2 = avma;
      GEN t, r = dblexp(radii[i]), r2 = sqrr(r);
      /* 2(r^2 - 1) / (r^2 - 3(r-1)) */
      t = divrr(shiftr((subrs(r2,1)),1), subrr(r2, mulur(3,subrs(r,1))));
      radii[i] = mydbllogr(addsr(1,t)) / 2;
      avma = av2;
    }
  lrho = logradius(radii, q,k,aux/10., &delta);
  update_radius(n, radii, lrho, &param, &param2);

  bit2 += (long)(n * fabs(lrho)/M_LN2 + 1.);
  R = mygprec(dblexp(-lrho), bit2);
  q = scalepol(q,R,bit2);
  gerepileall(av,2, &q,&R);

  optimize_split(q,k,delta,bit2,&FF,&GG,param,param2);
  bit2 += n; R = invr(R);
  FF = scalepol(FF,R,bit2);
  GG = scalepol(GG,R,bit2);

  a = mygprec(a,bit2);
  FF = conformal_pol(FF,a);
  GG = conformal_pol(GG,a);

  a = invr(subsr(1, gnorm(a)));
  FF = RgX_Rg_mul(FF, powru(a,k));
  GG = RgX_Rg_mul(GG, powru(a,n-k));

  *F = mygprec(FF,bit+n);
  *G = mygprec(GG,bit+n); gerepileall(ltop,2, F,G);
}

/* split p, this time without scaling. returns in F and G two polynomials
 * such that |p-FG|< 2^(-bit)|p| */
static void
split_2(GEN p, long bit, GEN ctr, double thickness, GEN *F, GEN *G)
{
  GEN q, FF, GG, R;
  double aux, delta, param, param2;
  long n = degpol(p), i, j, k, bit2;
  double lrmin, lrmax, lrho, *radii;

  radii = (double*) stack_malloc_align((n+1) * sizeof(double), sizeof(double));

  for (i=2; i<n; i++) radii[i] = UNDEF;
  aux = thickness/(double)(4 * n);
  lrmin = logmin_modulus(p, aux);
  lrmax = logmax_modulus(p, aux);
  radii[1] = lrmin;
  radii[n] = lrmax;
  i = 1; j = n;
  lrho = (lrmin + lrmax) / 2;
  k = dual_modulus(p, lrho, aux, 1);
  if (5*k < n || (n < 2*k && 5*k < 4*n))
    { lrmax = lrho; j=k+1; radii[j] = lrho; }
  else
    { lrmin = lrho; i=k;   radii[i] = lrho; }
  while (j > i+1)
  {
    if (i+j == n+1)
      lrho = (lrmin + lrmax) / 2;
    else
    {
      double kappa = 2. - log(1. + minss(i,n-j)) / log(1. + minss(j,n-i));
      if (i+j < n+1) lrho = lrmax * kappa + lrmin;
      else           lrho = lrmin * kappa + lrmax;
      lrho /= 1+kappa;
    }
    aux = (lrmax - lrmin) / (4*(j-i));
    k = dual_modulus(p, lrho, aux, minss(i,n+1-j));
    if (k-i < j-k-1 || (k-i == j-k-1 && 2*k > n))
      { lrmax = lrho; j=k+1; radii[j] = lrho - aux; }
    else
      { lrmin = lrho; i=k;   radii[i] = lrho + aux; }
  }
  aux = lrmax - lrmin;

  if (ctr)
  {
    lrho = (lrmax + lrmin) / 2;
    for (i=1; i<=n; i++)
      if (radii[i] != UNDEF) radii[i] -= lrho;

    bit2 = bit + (long)(n * fabs(lrho)/M_LN2 + 1.);
    R = mygprec(dblexp(-lrho), bit2);
    q = scalepol(p,R,bit2);
    conformal_mapping(radii, ctr, q, k, bit2, aux, &FF, &GG);
  }
  else
  {
    lrho = logradius(radii, p, k, aux/10., &delta);
    update_radius(n, radii, lrho, &param, &param2);

    bit2 = bit + (long)(n * fabs(lrho)/M_LN2 + 1.);
    R = mygprec(dblexp(-lrho), bit2);
    q = scalepol(p,R,bit2);
    optimize_split(q, k, delta, bit2, &FF, &GG, param, param2);
  }
  bit  += n;
  bit2 += n; R = invr(mygprec(R,bit2));
  *F = mygprec(scalepol(FF,R,bit2), bit);
  *G = mygprec(scalepol(GG,R,bit2), bit);
}

/* procedure corresponding to steps 5,6,.. page 44 in RR n. 1852 */
/* put in F and G two polynomial such that |p-FG|<2^(-bit)|p|
 * where the maximum modulus of the roots of p is <=1.
 * Assume sum of roots is 0. */
static void
split_1(GEN p, long bit, GEN *F, GEN *G)
{
  long i, imax, n = degpol(p), polreal = isreal(p), ep = gexpo(p), bit2 = bit+n;
  GEN ctr, q, qq, FF, GG, v, gr, r, newq;
  double lrmin, lrmax, lthick;
  const double LOG3 = 1.098613;

  lrmax = logmax_modulus(p, 0.01);
  gr = mygprec(dblexp(-lrmax), bit2);
  q = scalepol(p,gr,bit2);

  bit2 = bit + gexpo(q) - ep + (long)((double)n*2.*log2(3.)+1);
  v = cgetg(5,t_VEC);
  gel(v,1) = gen_2;
  gel(v,2) = gen_m2;
  gel(v,3) = mkcomplex(gen_0, gel(v,1));
  gel(v,4) = mkcomplex(gen_0, gel(v,2));
  q = mygprec(q,bit2); lthick = 0;
  newq = ctr = NULL; /* -Wall */
  imax = polreal? 3: 4;
  for (i=1; i<=imax; i++)
  {
    qq = RgX_translate(q, gel(v,i));
    lrmin = logmin_modulus(qq,0.05);
    if (LOG3 > lrmin + lthick)
    {
      double lquo = logmax_modulus(qq,0.05) - lrmin;
      if (lquo > lthick) { lthick = lquo; newq = qq; ctr = gel(v,i); }
    }
    if (lthick > M_LN2) break;
    if (polreal && i==2 && lthick > LOG3 - M_LN2) break;
  }
  bit2 = bit + gexpo(newq) - ep + (long)(n*LOG3/M_LN2 + 1);
  split_2(newq, bit2, ctr, lthick, &FF, &GG);
  r = gneg(mygprec(ctr,bit2));
  FF = RgX_translate(FF,r);
  GG = RgX_translate(GG,r);

  gr = invr(gr); bit2 = bit - ep + gexpo(FF)+gexpo(GG);
  *F = scalepol(FF,gr,bit2);
  *G = scalepol(GG,gr,bit2);
}

/* put in F and G two polynomials such that |P-FG|<2^(-bit)|P|,
where the maximum modulus of the roots of p is < 0.5 */
static int
split_0_2(GEN p, long bit, GEN *F, GEN *G)
{
  GEN q, b;
  long n = degpol(p), k, bit2, eq;
  double aux0 = dbllog2(gel(p,n+2)); /* != -oo */
  double aux1 = dbllog2(gel(p,n+1)), aux;

  if (aux1 == -pariINFINITY) /* p1 = 0 */
    aux = 0;
  else
  {
    aux = aux1 - aux0; /* log2(p1/p0) */
    /* beware double overflow */
    if (aux >= 0 && (aux > 1e4 || exp2(aux) > 2.5*n)) return 0;
    aux = (aux < -300)? 0.: n*log2(1 + exp2(aux)/(double)n);
  }
  bit2 = bit+1 + (long)(log2((double)n) + aux);
  q = mygprec(p,bit2);
  if (aux1 == -pariINFINITY) b = NULL;
  else
  {
    b = gdivgs(gdiv(gel(q,n+1),gel(q,n+2)),-n);
    q = RgX_translate(q,b);
  }
  gel(q,n+1) = gen_0; eq = gexpo(q);
  k = 0;
  while (k <= n/2 && (- gexpo(gel(q,k+2)) > bit2 + 2*(n-k) + eq
                      || gequal0(gel(q,k+2)))) k++;
  if (k > 0)
  {
    if (k > n/2) k = n/2;
    bit2 += k<<1;
    *F = pol_xn(k, 0);
    *G = RgX_shift_shallow(q, -k);
  }
  else
  {
    split_1(q,bit2,F,G);
    bit2 = bit + gexpo(*F) + gexpo(*G) - gexpo(p) + (long)aux+1;
    *F = mygprec(*F,bit2);
  }
  *G = mygprec(*G,bit2);
  if (b)
  {
    GEN mb = mygprec(gneg(b), bit2);
    *F = RgX_translate(*F, mb);
    *G = RgX_translate(*G, mb);
  }
  return 1;
}

/* put in F and G two polynomials such that |P-FG|<2^(-bit)|P|.
 * Assume max_modulus(p) < 2 */
static void
split_0_1(GEN p, long bit, GEN *F, GEN *G)
{
  GEN FF, GG;
  long n, bit2, normp;

  if  (split_0_2(p,bit,F,G)) return;

  normp = gexpo(p);
  scalepol2n(p,2); /* p := 4^(-n) p(4*x) */
  n = degpol(p); bit2 = bit + 2*n + gexpo(p) - normp;
  split_1(mygprec(p,bit2), bit2,&FF,&GG);
  scalepol2n(FF,-2);
  scalepol2n(GG,-2); bit2 = bit + gexpo(FF) + gexpo(GG) - normp;
  *F = mygprec(FF,bit2);
  *G = mygprec(GG,bit2);
}

/* put in F and G two polynomials such that |P-FG|<2^(-bit)|P| */
static void
split_0(GEN p, long bit, GEN *F, GEN *G)
{
  const double LOG1_9 = 0.6418539;
  long n = degpol(p), k = 0;
  GEN q;

  while (gexpo(gel(p,k+2)) < -bit && k <= n/2) k++;
  if (k > 0)
  {
    if (k > n/2) k = n/2;
    *F = pol_xn(k, 0);
    *G = RgX_shift_shallow(p, -k);
  }
  else
  {
    double lr = logmax_modulus(p, 0.05);
    if (lr < LOG1_9) split_0_1(p, bit, F, G);
    else
    {
      q = RgX_recip_shallow(p);
      lr = logmax_modulus(q,0.05);
      if (lr < LOG1_9)
      {
        split_0_1(q, bit, F, G);
        *F = RgX_recip_shallow(*F);
        *G = RgX_recip_shallow(*G);
      }
      else
        split_2(p,bit,NULL, 1.2837,F,G);
    }
  }
}

/********************************************************************/
/**                                                                **/
/**                ERROR ESTIMATE FOR THE ROOTS                    **/
/**                                                                **/
/********************************************************************/

static GEN
root_error(long n, long k, GEN roots_pol, long err, GEN shatzle)
{
  GEN rho, d, eps, epsbis, eps2, aux, rap = NULL;
  long i, j;

  d = cgetg(n+1,t_VEC);
  for (i=1; i<=n; i++)
  {
    if (i!=k)
    {
      aux = gsub(gel(roots_pol,i), gel(roots_pol,k));
      gel(d,i) = gabs(mygprec(aux,31), DEFAULTPREC);
    }
  }
  rho = gabs(mygprec(gel(roots_pol,k),31), DEFAULTPREC);
  if (expo(rho) < 0) rho = real_1(DEFAULTPREC);
  eps = mulrr(rho, shatzle);
  aux = shiftr(powru(rho,n), err);

  for (j=1; j<=2 || (j<=5 && cmprr(rap, dbltor(1.2)) > 0); j++)
  {
    GEN prod = NULL; /* 1. */
    long m = n;
    epsbis = mulrr(eps, dbltor(1.25));
    for (i=1; i<=n; i++)
    {
      if (i != k && cmprr(gel(d,i),epsbis) > 0)
      {
        GEN dif = subrr(gel(d,i),eps);
        prod = prod? mulrr(prod, dif): dif;
        m--;
      }
    }
    eps2 = prod? divrr(aux, prod): aux;
    if (m > 1) eps2 = sqrtnr(shiftr(eps2, 2*m-2), m);
    rap = divrr(eps,eps2); eps = eps2;
  }
  return eps;
}

/* round a complex or real number x to an absolute value of 2^(-bit) */
static GEN
mygprec_absolute(GEN x, long bit)
{
  long e;
  GEN y;

  switch(typ(x))
  {
    case t_REAL:
      e = expo(x) + bit;
      return (e <= 0 || !signe(x))? real_0_bit(-bit): rtor(x, nbits2prec(e));
    case t_COMPLEX:
      if (gexpo(gel(x,2)) < -bit) return mygprec_absolute(gel(x,1),bit);
      y = cgetg(3,t_COMPLEX);
      gel(y,1) = mygprec_absolute(gel(x,1),bit);
      gel(y,2) = mygprec_absolute(gel(x,2),bit);
      return y;
    default: return x;
  }
}

static long
a_posteriori_errors(GEN p, GEN roots_pol, long err)
{
  long i, n = degpol(p), e_max = -(long)EXPOBITS;
  GEN sigma, shatzle;

  err += (long)log2((double)n) + 1;
  if (err > -2) return 0;
  sigma = real2n(-err, LOWDEFAULTPREC);
  /*  2 / ((s - 1)^(1/n) - 1) */
  shatzle = divur(2, subrs(sqrtnr(subrs(sigma,1),n), 1));
  for (i=1; i<=n; i++)
  {
    pari_sp av = avma;
    GEN x = root_error(n,i,roots_pol,err,shatzle);
    long e = gexpo(x);
    avma = av; if (e > e_max) e_max = e;
    gel(roots_pol,i) = mygprec_absolute(gel(roots_pol,i), -e);
  }
  return e_max;
}

/********************************************************************/
/**                                                                **/
/**                           MAIN                                 **/
/**                                                                **/
/********************************************************************/
static GEN
append_clone(GEN r, GEN a) { a = gclone(a); vectrunc_append(r, a); return a; }

/* put roots in placeholder roots_pol so that |P - L_1...L_n| < 2^(-bit)|P|
 * returns prod (x-roots_pol[i]) */
static GEN
split_complete(GEN p, long bit, GEN roots_pol)
{
  long n = degpol(p);
  pari_sp ltop;
  GEN p1, F, G, a, b, m1, m2;

  if (n == 1)
  {
    a = gneg_i(gdiv(gel(p,2), gel(p,3)));
    (void)append_clone(roots_pol,a); return p;
  }
  ltop = avma;
  if (n == 2)
  {
    F = gsub(gsqr(gel(p,3)), gmul2n(gmul(gel(p,2),gel(p,4)), 2));
    F = gsqrt(F, nbits2prec(bit));
    p1 = ginv(gmul2n(gel(p,4),1));
    a = gneg_i(gmul(gadd(F,gel(p,3)), p1));
    b =        gmul(gsub(F,gel(p,3)), p1);
    a = append_clone(roots_pol,a);
    b = append_clone(roots_pol,b); avma = ltop;
    a = mygprec(a, 3*bit);
    b = mygprec(b, 3*bit);
    return gmul(gel(p,4), mkpoln(3, gen_1, gneg(gadd(a,b)), gmul(a,b)));
  }
  split_0(p,bit,&F,&G);
  m1 = split_complete(F,bit,roots_pol);
  m2 = split_complete(G,bit,roots_pol);
  return gerepileupto(ltop, gmul(m1,m2));
}

static GEN
quicktofp(GEN x)
{
  const long prec = DEFAULTPREC;
  switch(typ(x))
  {
    case t_INT: return itor(x, prec);
    case t_REAL: return rtor(x, prec);
    case t_FRAC: return fractor(x, prec);
    case t_COMPLEX: {
      GEN a = gel(x,1), b = gel(x,2);
      /* avoid problem with 0, e.g. x = 0 + I*1e-100. We don't want |x| = 0. */
      if (isintzero(a)) return cxcompotor(b, prec);
      if (isintzero(b)) return cxcompotor(a, prec);
      a = cxcompotor(a, prec);
      b = cxcompotor(b, prec); return sqrtr(addrr(sqrr(a), sqrr(b)));
    }
    default: pari_err_TYPE("quicktofp",x);
      return NULL;/*LCOV_EXCL_LINE*/
  }

}

/* bound log_2 |largest root of p| (Fujiwara's bound) */
double
fujiwara_bound(GEN p)
{
  pari_sp av = avma;
  long i, n = degpol(p);
  GEN cc;
  double loglc, Lmax;

  if (n <= 0) pari_err_CONSTPOL("fujiwara_bound");
  loglc = mydbllog2r( quicktofp(gel(p,n+2)) ); /* log_2 |lc(p)| */
  cc = gel(p, 2);
  if (gequal0(cc))
    Lmax = -pariINFINITY-1;
  else
    Lmax = (mydbllog2r(quicktofp(cc)) - loglc - 1) / n;
  for (i = 1; i < n; i++)
  {
    GEN y = gel(p,i+2);
    double L;
    if (gequal0(y)) continue;
    L = (mydbllog2r(quicktofp(y)) - loglc) / (n-i);
    if (L > Lmax) Lmax = L;
  }
  avma = av; return Lmax + 1;
}

/* Fujiwara's bound, real roots. Based on the following remark: if
 *   p = x^n + sum a_i x^i and q = x^n + sum min(a_i,0)x^i
 * then for all x >= 0, p(x) >= q(x). Thus any bound for the (positive) roots
 * of q is a bound for the positive roots of p. */
double
fujiwara_bound_real(GEN p, long sign)
{
  pari_sp av = avma;
  GEN x;
  long n = degpol(p), i, signodd, signeven;
  double fb;
  if (n <= 0) pari_err_CONSTPOL("fujiwara_bound");
  x = shallowcopy(p);
  if (gsigne(gel(x, n+2)) > 0)
  {
    signeven = 1;
    signodd = sign;
  }
  else
  {
    signeven = -1;
    signodd = -sign;
  }
  for (i = 0; i < n; i++)
  {
    if ((n - i) % 2)
    {
      if (gsigne(gel(x, i+2)) == signodd ) gel(x, i+2) = gen_0;
    }
    else
    {
      if (gsigne(gel(x, i+2)) == signeven) gel(x, i+2) = gen_0;
    }
  }
  fb = fujiwara_bound(x);
  avma = av; return fb;
}

static GEN
mygprecrc_special(GEN x, long prec, long e)
{
  GEN y;
  switch(typ(x))
  {
    case t_REAL:
      if (!signe(x)) return real_0_bit(minss(e, expo(x)));
      return (prec > realprec(x))? rtor(x, prec): x;
    case t_COMPLEX:
      y = cgetg(3,t_COMPLEX);
      gel(y,1) = mygprecrc_special(gel(x,1),prec,e);
      gel(y,2) = mygprecrc_special(gel(x,2),prec,e);
      return y;
    default: return x;
  }
}

/* like mygprec but keep at least the same precision as before */
static GEN
mygprec_special(GEN x, long bit)
{
  long lx, i, e, prec;
  GEN y;

  if (bit < 0) bit = 0; /* should not happen */
  e = gexpo(x) - bit;
  prec = nbits2prec(bit);
  switch(typ(x))
  {
    case t_POL:
      y = cgetg_copy(x, &lx); y[1] = x[1];
      for (i=2; i<lx; i++) gel(y,i) = mygprecrc_special(gel(x,i),prec,e);
      break;

    default: y = mygprecrc_special(x,prec,e);
  }
  return y;
}

static GEN
fix_roots1(GEN r)
{
  long i, l = lg(r);
  GEN allr = cgetg(l, t_VEC);
  for (i=1; i<l; i++)
  {
    GEN t = gel(r,i);
    gel(allr,i) = gcopy(t); gunclone(t);
  }
  return allr;
}
static GEN
fix_roots(GEN r, GEN *m, long h, long bit)
{
  long i, j, k, l, prec;
  GEN allr, ro1;
  if (h == 1) return fix_roots1(r);
  prec = nbits2prec(bit);
  ro1 = grootsof1(h, prec) + 1;
  l = lg(r)-1;
  allr = cgetg(h*l+1, t_VEC);
  for (k=1,i=1; i<=l; i++)
  {
    GEN p2, p1 = gel(r,i);
    p2 = (h == 2)? gsqrt(p1, prec): gsqrtn(p1, utoipos(h), NULL, prec);
    for (j=0; j<h; j++) gel(allr,k++) = gmul(p2, gel(ro1,j));
    gunclone(p1);
  }
  *m = roots_to_pol(allr, 0);
  return allr;
}

static GEN
all_roots(GEN p, long bit)
{
  GEN lc, pd, q, roots_pol, m;
  long bit0,  bit2, i, e, h, n = degpol(p);
  double fb;
  pari_sp av;

  pd = RgX_deflate_max(p, &h); lc = leading_coeff(pd);
  fb = fujiwara_bound(pd);
  e = (fb < 0)? 0: (long)(2 * fb);
  bit0 = bit + gexpo(pd) - gexpo(lc) + (long)log2(n/h)+1+e;
  bit2 = bit0; e = 0;
  for (av=avma,i=1;; i++,avma=av)
  {
    roots_pol = vectrunc_init(n+1);
    bit2 += e + (n << i);
    q = RgX_gtofp_bit(mygprec(pd,bit2), bit2);
    q[1] = evalsigne(1)|evalvarn(0);
    m = split_complete(q,bit2,roots_pol);
    roots_pol = fix_roots(roots_pol, &m, h, bit2);
    q = mygprec_special(p,bit2); lc = leading_coeff(q);
    q[1] = evalsigne(1)|evalvarn(0);
    if (h > 1) m = gmul(m,lc);

    e = gexpo(gsub(q, m)) - gexpo(lc) + (long)log2((double)n) + 1;
    if (e < -2*bit2) e = -2*bit2; /* avoid e = -pariINFINITY */
    if (e < 0)
    {
      e = bit + a_posteriori_errors(p,roots_pol,e);
      if (e < 0) return roots_pol;
    }
    if (DEBUGLEVEL > 7)
      err_printf("all_roots: restarting, i = %ld, e = %ld\n", i,e);
  }
}

INLINE int
isexactscalar(GEN x) { long tx = typ(x); return is_rational_t(tx); }

static int
isexactpol(GEN p)
{
  long i,n = degpol(p);
  for (i=0; i<=n; i++)
    if (!isexactscalar(gel(p,i+2))) return 0;
  return 1;
}

static GEN
solve_exact_pol(GEN p, long bit)
{
  long i, j, k, m, n = degpol(p), iroots = 0;
  GEN ex, factors, v = zerovec(n);

  factors = ZX_squff(Q_primpart(p), &ex);
  for (i=1; i<lg(factors); i++)
  {
    GEN roots_fact = all_roots(gel(factors,i), bit);
    n = degpol(gel(factors,i));
    m = ex[i];
    for (j=1; j<=n; j++)
      for (k=1; k<=m; k++) v[++iroots] = roots_fact[j];
  }
  return v;
}

/* return the roots of p with absolute error bit */
static GEN
roots_com(GEN q, long bit)
{
  GEN L, p;
  long v = RgX_valrem_inexact(q, &p);
  int ex = isexactpol(p);
  if (!ex) p = RgX_normalize1(p);
  if (lg(p) == 3)
    L = cgetg(1,t_VEC); /* constant polynomial */
  else
    L = ex? solve_exact_pol(p,bit): all_roots(p,bit);
  if (v)
  {
    GEN M, z, t = gel(q,2);
    long i, x, y, l, n;

    if (isrationalzero(t)) x = -bit;
    else
    {
      n = gexpo(t);
      x = n / v; l = degpol(q);
      for (i = v; i <= l; i++)
      {
        t  = gel(q,i+2);
        if (isrationalzero(t)) continue;
        y = (n - gexpo(t)) / i;
        if (y < x) x = y;
      }
    }
    z = real_0_bit(x); l = v + lg(L);
    M = cgetg(l, t_VEC); L -= v;
    for (i = 1; i <= v; i++) gel(M,i) = z;
    for (     ; i <  l; i++) gel(M,i) = gel(L,i);
    L = M;
  }
  return L;
}

static GEN
tocomplex(GEN x, long l, long bit)
{
  GEN y;
  if (typ(x) == t_COMPLEX)
  {
    if (signe(gel(x,1))) return mygprecrc(x, l, -bit);
    x = gel(x,2);
    y = cgetg(3,t_COMPLEX);
    gel(y,1) = real_0_bit(-bit);
    gel(y,2) = mygprecrc(x, l, -bit);
  }
  else
  {
    y = cgetg(3,t_COMPLEX);
    gel(y,1) = mygprecrc(x, l, -bit);
    gel(y,2) = real_0_bit(-bit);
  }
  return y;
}

/* x,y are t_COMPLEX of t_REALs or t_REAL, compare lexicographically,
 * up to 2^-e absolute error */
static int
cmp_complex_appr(void *E, GEN x, GEN y)
{
  long e = (long)E;
  GEN z, xi, yi, xr, yr;
  long sxi, syi;
  if (typ(x) == t_COMPLEX) { xr = gel(x,1); xi = gel(x,2); sxi = signe(xi); }
  else { xr = x; xi = NULL; sxi = 0; }
  if (typ(y) == t_COMPLEX) { yr = gel(y,1); yi = gel(y,2); syi = signe(yi); }
  else { yr = y; yi = NULL; syi = 0; }
  /* Compare absolute values of imaginary parts */
  if (!sxi)
  {
    if (syi && expo(yi) >= e) return -1;
    /* |Im x| ~ |Im y| ~ 0 */
  }
  else if (!syi)
  {
    if (sxi && expo(xi) >= e) return 1;
    /* |Im x| ~ |Im y| ~ 0 */
  }
  else
  {
    long sz;
    z = addrr_sign(xi, 1, yi, -1);
    sz = signe(z);
    if (sz && expo(z) >= e) return (int)sz;
  }
  /* |Im x| ~ |Im y|, sort according to real parts */
  z = subrr(xr, yr);
  if (expo(z) >= e) return (int)signe(z);
  /* Re x ~ Re y. Place negative absolute value before positive */
  return (int) (sxi - syi);
}

static GEN
clean_roots(GEN L, long l, long bit, long clean)
{
  long i, n = lg(L), ex = 5 - bit;
  GEN res = cgetg(n,t_COL);
  for (i=1; i<n; i++)
  {
    GEN c = gel(L,i);
    if (clean && isrealappr(c,ex))
    {
      if (typ(c) == t_COMPLEX) c = gel(c,1);
      c = mygprecrc(c, l, -bit);
    }
    else
      c = tocomplex(c, l, bit);
    gel(res,i) = c;
  }
  gen_sort_inplace(res, (void*)ex, &cmp_complex_appr, NULL);
  return res;
}

/* the vector of roots of p, with absolute error 2^(- prec2nbits(l)) */
static GEN
roots_aux(GEN p, long l, long clean)
{
  pari_sp av = avma;
  long bit;
  GEN L;

  if (typ(p) != t_POL)
  {
    if (gequal0(p)) pari_err_ROOTS0("roots");
    if (!isvalidcoeff(p)) pari_err_TYPE("roots",p);
    return cgetg(1,t_COL); /* constant polynomial */
  }
  if (!signe(p)) pari_err_ROOTS0("roots");
  checkvalidpol(p,"roots");
  if (lg(p) == 3) return cgetg(1,t_COL); /* constant polynomial */
  if (l < LOWDEFAULTPREC) l = LOWDEFAULTPREC;
  bit = prec2nbits(l);
  L = roots_com(p, bit);
  return gerepileupto(av, clean_roots(L, l, bit, clean));
}
GEN
roots(GEN p, long l) { return roots_aux(p,l, 0); }
/* clean up roots. If root is real replace it by its real part */
GEN
cleanroots(GEN p, long l) { return roots_aux(p,l, 1); }

/* private variant of conjvec. Allow non rational coefficients, shallow
 * function. */
GEN
polmod_to_embed(GEN x, long prec)
{
  GEN v, T = gel(x,1), A = gel(x,2);
  long i, l;
  if (typ(A) != t_POL || varn(A) != varn(T))
  {
    checkvalidpol(T,"polmod_to_embed");
    return const_col(degpol(T), A);
  }
  v = cleanroots(T,prec); l = lg(v);
  for (i=1; i<l; i++) gel(v,i) = poleval(A,gel(v,i));
  return v;
}

GEN
QX_complex_roots(GEN p, long l)
{
  pari_sp av = avma;
  long bit, v;
  GEN L;

  if (!signe(p)) pari_err_ROOTS0("QX_complex_roots");
  if (lg(p) == 3) return cgetg(1,t_COL); /* constant polynomial */
  if (l < LOWDEFAULTPREC) l = LOWDEFAULTPREC;
  bit = prec2nbits(l);
  v = RgX_valrem(p, &p);
  L = lg(p) > 3? all_roots(Q_primpart(p), bit): cgetg(1,t_COL);
  if (v) L = shallowconcat(const_vec(v, real_0_bit(-bit)), L);
  return gerepileupto(av, clean_roots(L, l, bit, 1));
}

/********************************************************************/
/**                                                                **/
/**                REAL ROOTS OF INTEGER POLYNOMIAL                **/
/**                                                                **/
/********************************************************************/

/* Count sign changes in the coefficients of (x+1)^deg(P)*P(1/(x+1))
 * The inversion is implicit (we take coefficients backwards). Roots of P
 * at 0 and 1 (mapped to oo and 0) are ignored here and must be dealt with
 * by the caller. Set root1 if P(1) = 0 */
static long
X2XP1(GEN P, long deg, int *root1, GEN *Premapped)
{
  const pari_sp av = avma;
  GEN v = shallowcopy(P);
  long i, j, vlim, nb, s;

  for (i = 0, vlim = deg+2;;)
  {
    for (j = 2; j < vlim; j++) gel(v, j+1) = addii(gel(v, j), gel(v, j+1));
    s = -signe(gel(v, vlim));
    vlim--; i++; if (s) break;
  }
  if (vlim == deg+1) *root1 = 0;
  else
  {
    *root1 = 1;
    if (Premapped) setlg(v, vlim + 2);
  }

  nb = 0;
  for (; i < deg; i++)
  {
    long s2 = -signe(gel(v, 2));
    int flag = (s2 == s);
    for (j = 2; j < vlim; j++)
    {
      gel(v, j+1) = addii(gel(v, j), gel(v, j+1));
      if (flag) flag = (s2 != signe(gel(v, j+1)));
    }
    if (s == signe(gel(v, vlim)))
    {
      if (++nb >= 2) { avma = av; return 2; }
      s = -s;
    }
    /* if flag is set there will be no further sign changes */
    if (flag && (!Premapped || !nb)) goto END;
    vlim--;
    if (gc_needed(av, 3))
    {
      if (DEBUGMEM>1) pari_warn(warnmem, "X2XP1, i = %ld/%ld", i, deg-1);
      if (!Premapped) setlg(v, vlim + 2);
      v = gerepilecopy(av, v);
    }
  }
  if (vlim >= 2 && s == signe(gel(v, vlim))) nb++;
END:
  if (Premapped && nb == 1) *Premapped = v; else avma = av;
  return nb;
}

static long
_intervalcmp(GEN x, GEN y)
{
  if (typ(x) == t_VEC) x = gel(x, 1);
  if (typ(y) == t_VEC) y = gel(y, 1);
  return gcmp(x, y);
}

static GEN
_gen_nored(void *E, GEN x) { (void)E; return x; }
static GEN
_mp_add(void *E, GEN x, GEN y) { (void)E; return mpadd(x, y); }
static GEN
_mp_sub(void *E, GEN x, GEN y) { (void)E; return mpsub(x, y); }
static GEN
_mp_mul(void *E, GEN x, GEN y) { (void)E; return mpmul(x, y); }
static GEN
_mp_sqr(void *E, GEN x) { (void)E; return mpsqr(x); }
static GEN
_gen_one(void *E) { (void)E; return gen_1; }
static GEN
_gen_zero(void *E) { (void)E; return gen_0; }

static struct bb_algebra mp_algebra = { _gen_nored, _mp_add, _mp_sub,
                         _mp_mul, _mp_sqr, _gen_one, _gen_zero };

static GEN
_mp_cmul(void *E, GEN P, long a, GEN x) {(void)E; return mpmul(gel(P,a+2), x);}

/* Split the polynom P in two parts, whose coeffs have constant sign:
 * P(X) = X^D*Pp + Pm. Also compute the two parts of the derivative of P,
 * Pprimem = Pm', Pprimep = X*Pp'+ D*Pp => P' = X^(D-1)*Pprimep + Pprimem;
 * Pprimep[i] = (i+D) Pp[i]. Return D */
static long
split_pols(GEN P, GEN *pPp, GEN *pPm, GEN *pPprimep, GEN *pPprimem)
{
  long i, D, dP = degpol(P), s0 = signe(gel(P,2));
  GEN Pp, Pm, Pprimep, Pprimem;
  for(i=1; i <= dP; i++)
    if (signe(gel(P, i+2)) == -s0) break;
  D = i;
  Pm = cgetg(D + 2, t_POL);
  Pprimem = cgetg(D + 1, t_POL);
  Pp = cgetg(dP-D + 3, t_POL);
  Pprimep = cgetg(dP-D + 3, t_POL);
  Pm[1] = Pp[1] = Pprimem[1] = Pprimep[1] = P[1];
  for(i=0; i < D; i++)
  {
    GEN c = gel(P, i+2);
    gel(Pm, i+2) = c;
    if (i) gel(Pprimem, i+1) = mului(i, c);
  }
  for(; i <= dP; i++)
  {
    GEN c = gel(P, i+2);
    gel(Pp, i+2-D) = c;
    gel(Pprimep, i+2-D) = mului(i, c);
  }
  *pPm = normalizepol_lg(Pm, D+2);
  *pPprimem = normalizepol_lg(Pprimem, D+1);
  *pPp = normalizepol_lg(Pp, dP-D+3);
  *pPprimep = normalizepol_lg(Pprimep, dP-D+3);
  return dP - degpol(*pPp);
}

static GEN
bkeval_single_power(long d, GEN V)
{
  long mp = lg(V) - 2;
  if (d > mp) return gmul(gpowgs(gel(V, mp+1), d/mp), gel(V, (d%mp)+1));
  return gel(V, d+1);
}

static GEN
splitpoleval(GEN Pp, GEN Pm, GEN pows, long D, long bitprec)
{
  GEN vp = gen_bkeval_powers(Pp, degpol(Pp), pows, NULL, &mp_algebra, _mp_cmul);
  GEN vm = gen_bkeval_powers(Pm, degpol(Pm), pows, NULL, &mp_algebra, _mp_cmul);
  GEN xa = bkeval_single_power(D, pows);
  GEN r;
  if (!signe(vp)) return vm;
  vp = gmul(vp, xa);
  r = gadd(vp, vm);
  if (gexpo(vp) - (signe(r)? gexpo(r): 0) > prec2nbits(realprec(vp)) - bitprec)
    return NULL;
  return r;
}

/* optimized Cauchy bound for P = X^D*Pp + Pm, D > deg(Pm) */
static GEN
splitcauchy(GEN Pp, GEN Pm, long prec)
{
  GEN S = gel(Pp,2), A = gel(Pm,2);
  long i, lPm = lg(Pm), lPp = lg(Pp);
  for (i=3; i < lPm; i++) { GEN c = gel(Pm,i); if (abscmpii(A, c) < 0) A = c; }
  for (i=3; i < lPp; i++) S = addii(S, gel(Pp, i));
  return subsr(1, rdivii(A, S, prec)); /* 1 + |Pm|_oo / |Pp|_1 */
}

/* Newton for polynom P, P(0)!=0, with unique sign change => one root in ]0,oo[
 * P' has also at most one zero there */
static GEN
polsolve(GEN P, long bitprec)
{
  pari_sp av = avma, av2;
  GEN Pp, Pm, Pprimep, Pprimem, Pprime, Pprime2, ra, rb, rc, Pc;
  long deg = degpol(P);
  long expoold = LONG_MAX, cprec = DEFAULTPREC, prec = nbits2prec(bitprec);
  long iter, D, rt, s0, bitaddprec, addprec;
  if (deg == 1)
    return gerepileuptoleaf(av, rdivii(negi(gel(P,2)), gel(P,3), prec));
  Pprime = ZX_deriv(P);
  Pprime2 = ZX_deriv(Pprime);
  bitaddprec = 1 + 2*expu(deg); addprec = nbits2prec(bitaddprec);
  D = split_pols(P, &Pp, &Pm, &Pprimep, &Pprimem); /* P = X^D*Pp + Pm */
  s0 = signe(gel(P, 2));
  rt = maxss(D, brent_kung_optpow(maxss(degpol(Pp), degpol(Pm)), 2, 1));
  rb = splitcauchy(Pp, Pm, DEFAULTPREC);
  for(;;)
  {
    GEN pows = gen_powers(rb, rt, 1, NULL, _mp_sqr, _mp_mul, _gen_one);
    Pc = splitpoleval(Pp, Pm, pows, D, bitaddprec);
    if (!Pc) { cprec++; rb = rtor(rb, cprec); continue; }
    if (signe(Pc) != s0) break;
    shiftr_inplace(rb,1);
  }
  ra = NULL;
  iter = 0;
  for(;;)
  {
    GEN wdth;
    iter++;
    if (ra)
      rc = shiftr(addrr(ra, rb), -1);
    else
      rc = shiftr(rb, -1);
    do
    {
      GEN pows = gen_powers(rc, rt, 1, NULL, _mp_sqr, _mp_mul, _gen_one);
      Pc = splitpoleval(Pp, Pm, pows, D, bitaddprec+2);
      if (Pc) break;
      cprec++; rc = rtor(rc, cprec);
    } while (1);
    if (signe(Pc) == s0)
      ra = rc;
    else
      rb = rc;
    if (!ra) continue;
    wdth = subrr(rb, ra);
    if (!(iter % 8))
    {
      GEN m1 = poleval(Pprime, ra), M2;
      if (signe(m1) == s0) continue;
      M2 = poleval(Pprime2, rb);
      if (abscmprr(gmul(M2, wdth), shiftr(m1, 1)) > 0) continue;
      break;
    }
    else if (gexpo(wdth) <= -bitprec)
      break;
  }
  rc = rb;
  av2 = avma;
  for(;; rc = gerepileuptoleaf(av2, rc))
  {
    long exponew;
    GEN Ppc, dist, rcold = rc;
    GEN pows = gen_powers(rc, rt, 1, NULL, _mp_sqr, _mp_mul, _gen_one);
    Ppc = splitpoleval(Pprimep, Pprimem, pows, D-1, bitaddprec+4);
    if (Ppc)
      Pc = splitpoleval(Pp, Pm, pows, D, bitaddprec+4);
    if (!Ppc || !Pc)
    {
      if (cprec >= prec+addprec)
        cprec += EXTRAPRECWORD;
      else
        cprec = minss(2*cprec, prec+addprec);
      rc = rtor(rc, cprec); continue; /* backtrack one step */
    }
    dist = typ(Ppc) == t_REAL? divrr(Pc, Ppc): divri(Pc, Ppc);
    rc = subrr(rc, dist);
    if (cmprr(ra, rc) > 0 || cmprr(rb, rc) < 0)
    {
      if (cprec >= prec+addprec) break;
      cprec = minss(2*cprec, prec+addprec);
      rc = rtor(rcold, cprec); continue; /* backtrack one step */
    }
    if (expoold == LONG_MAX) { expoold = expo(dist); continue; }
    exponew = expo(dist);
    if (exponew < -bitprec - 1)
    {
      if (cprec >= prec+addprec) break;
      cprec = minss(2*cprec, prec+addprec);
      rc = rtor(rc, cprec); continue;
    }
    if (exponew > expoold - 2)
    {
      if (cprec >= prec+addprec) break;
      expoold = LONG_MAX;
      cprec = minss(2*cprec, prec+addprec);
      rc = rtor(rc, cprec); continue;
    }
    expoold = exponew;
  }
  return gerepileuptoleaf(av, rtor(rc, prec));
}

static GEN
usp(GEN Q0, long deg, long flag, long bitprec)
{
  const pari_sp av = avma;
  GEN Q, sol, c, Lc, Lk;
  long listsize = 64, nbr = 0, nb_todo, ind, deg0, indf, i, k, nb;


  sol = zerocol(deg);
  deg0 = deg;
  Lc = zerovec(listsize);
  Lk = cgetg(listsize+1, t_VECSMALL);
  c = gen_0;
  k = Lk[1] = 0;
  ind = 1; indf = 2;
  Q = leafcopy(Q0);

  nb_todo = 1;
  while (nb_todo)
  {
    GEN nc = gel(Lc, ind), Qremapped;
    pari_sp av2;
    int root1;
    if (Lk[ind] == k + 1)
    {
      deg0 = deg;
      setlg(Q0, deg + 3);
      Q0 = ZX_rescale2n(Q0, 1);
      Q = Q_primpart(Q0);
      c = gen_0;
    }

    if (!equalii(nc, c)) Q = ZX_translate(Q, subii(nc, c));

    k = Lk[ind];
    c = nc;
    ind++;
    nb_todo--;

    if (equalii(gel(Q, 2), gen_0))
    { /* Q(0) = 0 */
      GEN s = gmul2n(c, -k);
      long j;
      for (j = 1; j <= nbr; j++)
        if (gequal(gel(sol, j), s)) break;
      if (j > nbr) gel(sol, ++nbr) = s;

      deg0--;
      for (j = 2; j <= deg0 + 2; j++) gel(Q, j) = gel(Q, j+1);
      setlg(Q, j);
    }

    av2 = avma;
    nb = X2XP1(Q, deg0, &root1, flag == 1 ? &Qremapped : NULL);

    if      (nb == 0) /* no root in this open interval */;
    else if (nb == 1) /* exactly one root */
    {
      GEN s = gen_0;
      if (flag == 0)
        s = mkvec2(gmul2n(c,-k), gmul2n(addiu(c,1),-k));
      else if (flag == 1) /* Caveat: Qremapped is the reciprocal polynomial */
      {
        s = polsolve(Qremapped, bitprec+1);
        s = divrr(s, addsr(1, s));
        s = gmul2n(addir(c, s), -k);
        s = rtor(s, nbits2prec(bitprec));
      }
      gel(sol, ++nbr) = gerepileupto(av2, s);
    }
    else
    { /* unknown, add two nodes to refine */
      if (indf + 2 > listsize)
      {
        if (ind>1)
        {
          for (i = ind; i < indf; i++)
          {
            gel(Lc, i-ind+1) = gel(Lc, i);
            Lk[i-ind+1] = Lk[i];
          }
          indf -= ind-1;
          ind = 1;
        }
        if (indf + 2 > listsize)
        {
          listsize *= 2;
          Lc = vec_lengthen(Lc, listsize);
          Lk = vecsmall_lengthen(Lk, listsize);
        }
        for (i = indf; i <= listsize; i++) gel(Lc, i) = gen_0;
      }
      nc = shifti(c, 1);
      gel(Lc, indf) = nc;
      gel(Lc, indf + 1) = addiu(nc, 1);
      Lk[indf] = Lk[indf + 1] = k + 1;
      indf += 2;
      nb_todo += 2;
    }
    if (root1)
    { /* Q(1) = 0 */
      GEN s = gmul2n(addiu(c,1), -k);
      long j;
      for (j = 1; j <= nbr; j++)
        if (gequal(gel(sol, j), s)) break;
      if (j > nbr) gel(sol, ++nbr) = s;
    }

    if (gc_needed(av, 2))
    {
      gerepileall(av, 6, &Q0, &Q, &c, &Lc, &Lk, &sol);
      if (DEBUGMEM > 1) pari_warn(warnmem, "ZX_Uspensky", avma);
    }
  }

  setlg(sol, nbr+1);
  return gerepilecopy(av, sol);
}

static GEN
ZX_Uspensky_cst_pol(long nbz, long flag, long bitprec)
{
  switch(flag)
  {
    case 0:  return zerocol(nbz);
    case 1:  retconst_col(nbz, real_0_bit(-bitprec));
    default: return utoi(nbz);
  }
}

/* ZX_Uspensky(P, [a,a], flag) */
static GEN
ZX_Uspensky_equal(GEN P, GEN a, long flag)
{
  if (typ(a) != t_INFINITY && gequal0(poleval(P, a)))
    return flag <= 1 ? mkcol(a): gen_1;
  else
    return flag <= 1 ? cgetg(1, t_COL) : gen_0;
}

GEN
ZX_Uspensky(GEN P, GEN ab, long flag, long bitprec)
{
  pari_sp av = avma;
  GEN a, b, sol = NULL, Pcur;
  double fb;
  long nbz, deg;

  deg = degpol(P);
  if (deg == 0) return flag <= 1 ? cgetg(1, t_COL) : gen_0;
  if (ab)
  {
    if (typ(ab) == t_VEC)
    {
      if (lg(ab) != 3) pari_err_DIM("ZX_Uspensky");
      a = gel(ab, 1);
      b = gel(ab, 2);
    }
    else
    {
      a = ab;
      b = mkoo();
    }
  }
  else
  {
    a = mkmoo();
    b = mkoo();
  }
  switch (gcmp(a, b))
  {
    case 1: avma = av; return flag <= 1 ? cgetg(1, t_COL) : gen_0;
    case 0: return gerepilecopy(av, ZX_Uspensky_equal(P, a, flag));
  }
  nbz = ZX_valrem(P, &Pcur);
  deg -= nbz;
  if (!nbz) Pcur = P;
  if (nbz && (gsigne(a) > 0 || gsigne(b) < 0)) nbz = 0;
  if (deg == 0) { avma = av; return ZX_Uspensky_cst_pol(nbz, flag, bitprec); }
  if (deg == 1)
  {
    sol = gdiv(gneg(gel(Pcur, 2)), pollead(Pcur, -1));
    if (gcmp(a, sol) > 0 || gcmp(sol, b) > 0)
    {
      avma = av;
      return ZX_Uspensky_cst_pol(nbz, flag, bitprec);
    }
    if (flag >= 2) { avma = av; return utoi(nbz+1); }
    sol = gconcat(zerocol(nbz), mkcol(sol));
    if (flag == 1) sol = RgC_gtofp(sol, nbits2prec(bitprec));
    return gerepilecopy(av, sol);
  }
  switch(flag)
  {
    case 0:
      sol = zerocol(nbz);
      break;
    case 1:
      sol = const_col(nbz, real_0_bit(-bitprec));
      break;
    /* case 2: nothing */
  }

  if (typ(a) == t_INFINITY && typ(b) != t_INFINITY && gsigne(b))
  {
    fb = fujiwara_bound_real(Pcur, -1);
    if (fb <= -pariINFINITY) a = gen_0;
    else if (fb < 0) a = gen_m1;
    else a = negi(int2n((long)ceil(fb)));
  }
  if (typ(b) == t_INFINITY && typ(a) != t_INFINITY && gsigne(a))
  {
    fb = fujiwara_bound_real(Pcur, 1);
    if (fb <= -pariINFINITY) b = gen_0;
    else if (fb < 0) b = gen_1;
    else b = int2n((long)ceil(fb));
  }

  if (typ(a) != t_INFINITY && typ(b) != t_INFINITY)
  {
    GEN den, diff, unscaledres, co, Pdiv, ascaled;
    pari_sp av1;
    long i;
    if (gequal(a,b)) /* can occur if one of a,b was initially a t_INFINITY */
      return gerepilecopy(av, ZX_Uspensky_equal(P, a, flag));
    den = lcmii(Q_denom(a), Q_denom(b));
    if (!is_pm1(den))
    {
      Pcur = ZX_rescale(Pcur, den);
      ascaled = gmul(a, den);
    }
    else
    {
      den = NULL;
      ascaled = a;
    }
    diff = subii(den ? gmul(b,den) : b, ascaled);
    Pcur = ZX_unscale(ZX_translate(Pcur, ascaled), diff);
    av1 = avma;
    Pdiv = cgetg(deg+2, t_POL);
    Pdiv[1] = Pcur[1];
    co = gel(Pcur, deg+2);
    for (i = deg; --i >= 0; )
    {
      gel(Pdiv, i+2) = co;
      co = addii(co, gel(Pcur, i+2));
    }
    if (!signe(co))
    {
      Pcur = Pdiv;
      deg--;
      if (flag <= 1)
        sol = gconcat(sol, b);
      else
        nbz++;
    }
    else
      avma = av1;
    unscaledres = usp(Pcur, deg, flag, bitprec);
    if (flag <= 1)
    {
      for (i = 1; i < lg(unscaledres); i++)
      {
        GEN z = gmul(diff, gel(unscaledres, i));
        if (typ(z) == t_VEC)
        {
          gel(z, 1) = gadd(ascaled, gel(z, 1));
          gel(z, 2) = gadd(ascaled, gel(z, 2));
        }
        else
          z = gadd(ascaled, z);
        if (den) z = gdiv(z, den);
        gel(unscaledres, i) = z;
      }
      sol = gconcat(sol, unscaledres);
    }
    else
      nbz += lg(unscaledres) - 1;
  }
  if (typ(b) == t_INFINITY && (fb=fujiwara_bound_real(Pcur, 1)) > -pariINFINITY)
  {
    GEN Pcurp, unscaledres;
    long bp = (long)ceil(fb);
    if (bp < 0) bp = 0;
    Pcurp = ZX_unscale2n(Pcur, bp);
    unscaledres = usp(Pcurp, deg, flag, bitprec);
    if (flag <= 1)
      sol = shallowconcat(sol, gmul2n(unscaledres, bp));
    else
      nbz += lg(unscaledres)-1;
  }
  if (typ(a) == t_INFINITY && (fb=fujiwara_bound_real(Pcur,-1)) > -pariINFINITY)
  {
    GEN Pcurm, unscaledres;
    long i, bm = (long)ceil(fb);
    if (bm < 0) bm = 0;
    Pcurm = ZX_unscale2n(ZX_z_unscale(Pcur, -1), bm);
    unscaledres = usp(Pcurm, deg, flag, bitprec);
    if (flag <= 1)
    {
      for (i = 1; i < lg(unscaledres); i++)
      {
        GEN z = gneg(gmul2n(gel(unscaledres, i), bm));
        if (typ(z) == t_VEC) swap(gel(z, 1), gel(z, 2));
        gel(unscaledres, i) = z;
      }
      sol = shallowconcat(unscaledres, sol);
    }
    else
      nbz += lg(unscaledres)-1;
  }
  if (flag >= 2) return utoi(nbz);
  if (flag)
    sol = sort(sol);
  else
    sol = gen_sort(sol, (void *)_intervalcmp, cmp_nodata);
  return gerepileupto(av, sol);
}

/* x a scalar */
static GEN
rootsdeg0(GEN x)
{
  if (!is_real_t(typ(x))) pari_err_TYPE("realroots",x);
  if (gequal0(x)) pari_err_ROOTS0("realroots");
  return cgetg(1,t_COL); /* constant polynomial */
}
static void
checkbound(GEN a)
{
  switch(typ(a))
  {
    case t_INT: case t_FRAC: case t_INFINITY: break;
    default: pari_err_TYPE("polrealroots", a);
  }
}
static GEN
check_ab(GEN ab)
{
  GEN a, b;
  if (!ab) return NULL;
  if (typ(ab) != t_VEC || lg(ab) != 3) pari_err_TYPE("polrootsreal",ab);
  a = gel(ab,1); checkbound(a);
  b = gel(ab,2); checkbound(b);
  if (typ(a) == t_INFINITY && inf_get_sign(a) < 0 &&
      typ(b) == t_INFINITY && inf_get_sign(b) > 0) ab = NULL;
  return ab;
}
GEN
realroots(GEN P, GEN ab, long prec)
{
  pari_sp av = avma;
  long nrr = 0;
  GEN sol = NULL, fa, ex;
  long i, j, v;

  ab = check_ab(ab);
  if (typ(P) != t_POL) return rootsdeg0(P);
  switch(degpol(P))
  {
    case -1: return rootsdeg0(gen_0);
    case 0: return rootsdeg0(gel(P,2));
  }
  if (!RgX_is_ZX(P)) P = RgX_rescale_to_int(P);
  P = Q_primpart(P);
  v = ZX_valrem(P,&P);
  if (v && (!ab || (gsigne(gel(ab,1)) <= 0 && gsigne(gel(ab,2)) >= 0)))
    sol = const_col(v, real_0(prec));
  fa = ZX_squff(P, &ex);
  for (i = 1; i < lg(fa); i++)
  {
    GEN Pi = gel(fa, i), soli, soli2 = NULL;
    long n, nrri = 0, h;
    if (ab)
      h = 1;
    else
      Pi = ZX_deflate_max(Pi, &h);
    soli = ZX_Uspensky(Pi, h%2 ? ab: gen_0, 1, prec2nbits(prec));
    n = lg(soli);
    if (!(h % 2)) soli2 = cgetg(n, t_COL);
    for (j = 1; j < n; j++)
    {
      GEN elt = gel(soli, j); /* != 0 */
      if (typ(elt) != t_REAL)
      {
        nrri++; if (h > 1 && !(h % 2)) nrri++;
        elt = gtofp(elt, prec);
        gel(soli, j) = elt;
      }
      if (h > 1)
      {
        GEN r;
        if (h == 2)
          r = sqrtr(elt);
        else
        {
          if (signe(elt) < 0)
            r = negr(sqrtnr(negr(elt), h));
          else
            r = sqrtnr(elt, h);
        }
        gel(soli, j) = r;
        if (!(h % 2)) gel(soli2, j) = negr(r);
      }
    }
    if (!(h % 2)) soli = shallowconcat(soli, soli2);
    if (ex[i] > 1) soli = shallowconcat1( const_vec(ex[i], soli) );
    sol = sol? shallowconcat(sol, soli): soli;
    nrr += ex[i]*nrri;
  }
  if (!sol) { avma = av; return cgetg(1,t_COL); }

  if (DEBUGLEVEL > 4)
  {
    err_printf("Number of real roots: %d\n", lg(sol)-1);
    err_printf(" -- of which 2-integral: %ld\n", nrr);
  }
  return gerepileupto(av, sort(sol));
}

/* P non-constant, squarefree ZX */
long
ZX_sturm(GEN P)
{
  pari_sp av = avma;
  long h, r;
  P = ZX_deflate_max(P, &h);
  if (odd(h))
    r = itos(ZX_Uspensky(P, NULL, 2, 0));
  else
    r = 2*itos(ZX_Uspensky(P, gen_0, 2, 0));
  avma = av; return r;
}
/* P non-constant, squarefree ZX */
long
ZX_sturmpart(GEN P, GEN ab)
{
  pari_sp av = avma;
  long r;
  if (!check_ab(ab)) return ZX_sturm(P);
  r = itos(ZX_Uspensky(P, ab, 2, 0));
  avma = av; return r;
}
