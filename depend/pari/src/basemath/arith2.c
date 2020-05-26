/* Copyright (C) 2000  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/*********************************************************************/
/**                                                                 **/
/**                     ARITHMETIC FUNCTIONS                        **/
/**                        (second part)                            **/
/**                                                                 **/
/*********************************************************************/
#include "pari.h"
#include "paripriv.h"

GEN
boundfact(GEN n, ulong lim)
{
  switch(typ(n))
  {
    case t_INT: return Z_factor_limit(n,lim);
    case t_FRAC: {
      pari_sp av = avma;
      GEN a = Z_factor_limit(gel(n,1),lim);
      GEN b = Z_factor_limit(gel(n,2),lim);
      gel(b,2) = ZC_neg(gel(b,2));
      return gerepilecopy(av, merge_factor(a,b,(void*)&cmpii,cmp_nodata));
    }
  }
  pari_err_TYPE("boundfact",n);
  return NULL; /* LCOV_EXCL_LINE */
}

/* NOT memory clean */
GEN
Z_smoothen(GEN N, GEN L, GEN *pP, GEN *pe)
{
  long i, j, l = lg(L);
  GEN e = new_chunk(l), P = new_chunk(l);
  for (i = j = 1; i < l; i++)
  {
    ulong p = uel(L,i);
    long v = Z_lvalrem(N, p, &N);
    if (v) { P[j] = p; e[j] = v; j++; if (is_pm1(N)) { N = NULL; break; } }
  }
  P[0] = evaltyp(t_VECSMALL) | evallg(j); *pP = P;
  e[0] = evaltyp(t_VECSMALL) | evallg(j); *pe = e; return N;
}
/***********************************************************************/
/**                                                                   **/
/**                    SIMPLE FACTORISATIONS                          **/
/**                                                                   **/
/***********************************************************************/
/* Factor n and output [p,e,c] where
 * p, e and c are vecsmall with n = prod{p[i]^e[i]} and c[i] = p[i]^e[i] */
GEN
factoru_pow(ulong n)
{
  GEN f = cgetg(4,t_VEC);
  pari_sp av = avma;
  GEN F, P, E, p, e, c;
  long i, l;
  /* enough room to store <= 15 * [p,e,p^e] (OK if n < 2^64) */
  (void)new_chunk((15 + 1)*3);
  F = factoru(n);
  P = gel(F,1);
  E = gel(F,2); l = lg(P);
  avma = av;
  gel(f,1) = p = cgetg(l,t_VECSMALL);
  gel(f,2) = e = cgetg(l,t_VECSMALL);
  gel(f,3) = c = cgetg(l,t_VECSMALL);
  for(i = 1; i < l; i++)
  {
    p[i] = P[i];
    e[i] = E[i];
    c[i] = upowuu(p[i], e[i]);
  }
  return f;
}

static GEN
factorlim(GEN n, ulong lim)
{ return lim? Z_factor_limit(n, lim): Z_factor(n); }
/* factor p^n - 1, assuming p prime. If lim != 0, limit factorization to
 * primes <= lim */
GEN
factor_pn_1_limit(GEN p, long n, ulong lim)
{
  pari_sp av = avma;
  GEN A = factorlim(subiu(p,1), lim), d = divisorsu(n);
  long i, pp = itos_or_0(p);
  for(i=2; i<lg(d); i++)
  {
    GEN B;
    if (pp && d[i]%pp==0 && (
       ((pp&3)==1 && (d[i]&1)) ||
       ((pp&3)==3 && (d[i]&3)==2) ||
       (pp==2 && (d[i]&7)==4)))
    {
      GEN f=factor_Aurifeuille_prime(p,d[i]);
      B = factorlim(f, lim);
      A = merge_factor(A, B, (void*)&cmpii, cmp_nodata);
      B = factorlim(diviiexact(polcyclo_eval(d[i],p), f), lim);
    }
    else
      B = factorlim(polcyclo_eval(d[i],p), lim);
    A = merge_factor(A, B, (void*)&cmpii, cmp_nodata);
  }
  return gerepilecopy(av, A);
}
GEN
factor_pn_1(GEN p, ulong n)
{ return factor_pn_1_limit(p, n, 0); }

#if 0
static GEN
to_mat(GEN p, long e) {
  GEN B = cgetg(3, t_MAT);
  gel(B,1) = mkcol(p);
  gel(B,2) = mkcol(utoipos(e)); return B;
}
/* factor phi(n) */
GEN
factor_eulerphi(GEN n)
{
  pari_sp av = avma;
  GEN B = NULL, A, P, E, AP, AE;
  long i, l, v = vali(n);

  l = lg(n);
  /* result requires less than this: at most expi(n) primes */
  (void)new_chunk(bit_accuracy(l) * (l /*p*/ + 3 /*e*/ + 2 /*vectors*/) + 3+2);
  if (v) { n = shifti(n, -v); v--; }
  A = Z_factor(n); P = gel(A,1); E = gel(A,2); l = lg(P);
  for(i = 1; i < l; i++)
  {
    GEN p = gel(P,i), q = subiu(p,1), fa;
    long e = itos(gel(E,i)), w;

    w = vali(q); v += w; q = shifti(q,-w);
    if (! is_pm1(q))
    {
      fa = Z_factor(q);
      B = B? merge_factor(B, fa, (void*)&cmpii, cmp_nodata): fa;
    }
    if (e > 1) {
      if (B) {
        gel(B,1) = shallowconcat(gel(B,1), p);
        gel(B,2) = shallowconcat(gel(B,2), utoipos(e-1));
      } else
        B = to_mat(p, e-1);
    }
  }
  avma = av;
  if (!B) return v? to_mat(gen_2, v): trivial_fact();
  A = cgetg(3, t_MAT);
  P = gel(B,1); E = gel(B,2); l = lg(P);
  AP = cgetg(l+1, t_COL); gel(A,1) = AP; AP++;
  AE = cgetg(l+1, t_COL); gel(A,2) = AE; AE++;
  /* prepend "2^v" */
  gel(AP,0) = gen_2;
  gel(AE,0) = utoipos(v);
  for (i = 1; i < l; i++)
  {
    gel(AP,i) = icopy(gel(P,i));
    gel(AE,i) = icopy(gel(E,i));
  }
  return A;
}
#endif

/***********************************************************************/
/**                                                                   **/
/**         CHECK FACTORIZATION FOR ARITHMETIC FUNCTIONS              **/
/**                                                                   **/
/***********************************************************************/
int
RgV_is_ZVpos(GEN v)
{
  long i, l = lg(v);
  for (i = 1; i < l; i++)
  {
    GEN c = gel(v,i);
    if (typ(c) != t_INT || signe(c) <= 0) return 0;
  }
  return 1;
}
/* check whether v is a ZV with non-0 entries */
int
RgV_is_ZVnon0(GEN v)
{
  long i, l = lg(v);
  for (i = 1; i < l; i++)
  {
    GEN c = gel(v,i);
    if (typ(c) != t_INT || !signe(c)) return 0;
  }
  return 1;
}
/* check whether v is a ZV with non-zero entries OR exactly [0] */
static int
RgV_is_ZV0(GEN v)
{
  long i, l = lg(v);
  for (i = 1; i < l; i++)
  {
    GEN c = gel(v,i);
    long s;
    if (typ(c) != t_INT) return 0;
    s = signe(c);
    if (!s) return (l == 2);
  }
  return 1;
}

static int
RgV_is_prV(GEN v)
{
  long l = lg(v), i;
  for (i = 1; i < l; i++)
    if (!checkprid_i(gel(v,i))) return 0;
  return 1;
}
int
is_nf_factor(GEN F)
{
  return typ(F) == t_MAT && lg(F) == 3
    && RgV_is_prV(gel(F,1)) && RgV_is_ZVpos(gel(F,2));
}
int
is_nf_extfactor(GEN F)
{
  return typ(F) == t_MAT && lg(F) == 3
    && RgV_is_prV(gel(F,1)) && RgV_is_ZV(gel(F,2));
}

static int
is_Z_factor_i(GEN f)
{ return typ(f) == t_MAT && lg(f) == 3 && RgV_is_ZVpos(gel(f,2)); }
int
is_Z_factorpos(GEN f)
{ return is_Z_factor_i(f) && RgV_is_ZVpos(gel(f,1)); }
int
is_Z_factor(GEN f)
{ return is_Z_factor_i(f) && RgV_is_ZV0(gel(f,1)); }
/* as is_Z_factorpos, also allow factor(0) */
int
is_Z_factornon0(GEN f)
{ return is_Z_factor_i(f) && RgV_is_ZVnon0(gel(f,1)); }
GEN
clean_Z_factor(GEN f)
{
  GEN P = gel(f,1);
  long n = lg(P)-1;
  if (n && equalim1(gel(P,1)))
    return mkmat2(vecslice(P,2,n), vecslice(gel(f,2),2,n));
  return f;
}
GEN
fuse_Z_factor(GEN f, GEN B)
{
  GEN P = gel(f,1), E = gel(f,2), P2,E2;
  long i, l = lg(P);
  if (l == 1) return f;
  for (i = 1; i < l; i++)
    if (abscmpii(gel(P,i), B) > 0) break;
  if (i == l) return f;
  /* tail / initial segment */
  P2 = vecslice(P, i, l-1); P = vecslice(P, 1, i-1);
  E2 = vecslice(E, i, l-1); E = vecslice(E, 1, i-1);
  P = shallowconcat(P, mkvec(factorback2(P2,E2)));
  E = shallowconcat(E, mkvec(gen_1));
  return mkmat2(P, E);
}

/* n attached to a factorization of a positive integer: either N (t_INT)
 * a factorization matrix faN, or a t_VEC: [N, faN] */
GEN
check_arith_pos(GEN n, const char *f) {
  switch(typ(n))
  {
    case t_INT:
      if (signe(n) <= 0) pari_err_DOMAIN(f, "argument", "<=", gen_0, gen_0);
      return NULL;
    case t_VEC:
      if (lg(n) != 3 || typ(gel(n,1)) != t_INT || signe(gel(n,1)) <= 0) break;
      n = gel(n,2); /* fall through */
    case t_MAT:
      if (!is_Z_factorpos(n)) break;
      return n;
  }
  pari_err_TYPE(f,n);
  return NULL;
}
/* n attached to a factorization of a non-0 integer */
GEN
check_arith_non0(GEN n, const char *f) {
  switch(typ(n))
  {
    case t_INT:
      if (!signe(n)) pari_err_DOMAIN(f, "argument", "=", gen_0, gen_0);
      return NULL;
    case t_VEC:
      if (lg(n) != 3 || typ(gel(n,1)) != t_INT || !signe(gel(n,1))) break;
      n = gel(n,2); /* fall through */
    case t_MAT:
      if (!is_Z_factornon0(n)) break;
      return n;
  }
  pari_err_TYPE(f,n);
  return NULL;
}
/* n attached to a factorization of an integer */
GEN
check_arith_all(GEN n, const char *f) {
  switch(typ(n))
  {
    case t_INT:
      return NULL;
    case t_VEC:
      if (lg(n) != 3 || typ(gel(n,1)) != t_INT) break;
      n = gel(n,2); /* fall through */
    case t_MAT:
      if (!is_Z_factor(n)) break;
      return n;
  }
  pari_err_TYPE(f,n);
  return NULL;
}

/***********************************************************************/
/**                                                                   **/
/**                MISCELLANEOUS ARITHMETIC FUNCTIONS                 **/
/**                (ultimately depend on Z_factor())                  **/
/**                                                                   **/
/***********************************************************************/
/* set P,E from F. Check whether F is an integer and kill "factor" -1 */
static void
set_fact_check(GEN F, GEN *pP, GEN *pE, int *isint)
{
  GEN E, P;
  if (lg(F) != 3) pari_err_TYPE("divisors",F);
  P = gel(F,1);
  E = gel(F,2);
  RgV_check_ZV(E, "divisors");
  *isint = RgV_is_ZV(P);
  if (*isint)
  {
    long i, l = lg(P);
    /* skip -1 */
    if (l>1 && signe(gel(P,1)) < 0) { E++; P = vecslice(P,2,--l); }
    /* test for 0 */
    for (i = 1; i < l; i++)
      if (!signe(gel(P,i)) && signe(gel(E,i)))
        pari_err_DOMAIN("divisors", "argument", "=", gen_0, F);
  }
  *pP = P;
  *pE = E;
}
static void
set_fact(GEN F, GEN *pP, GEN *pE) { *pP = gel(F,1); *pE = gel(F,2); }

int
divisors_init(GEN n, GEN *pP, GEN *pE)
{
  long i,l;
  GEN E, P, e;
  int isint;

  switch(typ(n))
  {
    case t_INT:
      if (!signe(n)) pari_err_DOMAIN("divisors", "argument", "=", gen_0, gen_0);
      set_fact(absZ_factor(n), &P,&E);
      isint = 1; break;
    case t_VEC:
      if (lg(n) != 3 || typ(gel(n,2)) !=t_MAT) pari_err_TYPE("divisors",n);
      set_fact_check(gel(n,2), &P,&E, &isint);
      break;
    case t_MAT:
      set_fact_check(n, &P,&E, &isint);
      break;
    default:
      set_fact(factor(n), &P,&E);
      isint = 0; break;
  }
  l = lg(P);
  e = cgetg(l, t_VECSMALL);
  for (i=1; i<l; i++)
  {
    e[i] = itos(gel(E,i));
    if (e[i] < 0) pari_err_TYPE("divisors [denominator]",n);
  }
  *pP = P; *pE = e; return isint;
}

static long
ndiv(GEN E)
{
  long i, l;
  GEN e = cgetg_copy(E, &l); /* left on stack */
  ulong n;
  for (i=1; i<l; i++) e[i] = E[i]+1;
  n = itou_or_0( zv_prod_Z(e) );
  if (!n || n & ~LGBITS) pari_err_OVERFLOW("divisors");
  return n;
}
static int
cmpi1(void *E, GEN a, GEN b) { (void)E; return cmpii(gel(a,1), gel(b,1)); }
/* P a t_COL of objects, E a t_VECSMALL of exponents, return cleaned-up
 * factorization (removing 0 exponents) as a t_MAT with 2 cols. */
static GEN
fa_clean(GEN P, GEN E)
{
  long i, j, l = lg(E);
  GEN Q = cgetg(l, t_COL);
  for (i = j = 1; i < l; i++)
    if (E[i]) { gel(Q,j) = gel(P,i); E[j] = E[i]; j++; }
  setlg(Q,j);
  setlg(E,j); return mkmat2(Q,Flc_to_ZC(E));
}
GEN
divisors_factored(GEN N)
{
  pari_sp av = avma;
  GEN *d, *t1, *t2, *t3, D, P, E;
  int isint = divisors_init(N, &P, &E);
  GEN (*mul)(GEN,GEN) = isint? mulii: gmul;
  long i, j, l, n = ndiv(E);

  D = cgetg(n+1,t_VEC); d = (GEN*)D;
  l = lg(E);
  *++d = mkvec2(gen_1, const_vecsmall(l-1,0));
  for (i=1; i<l; i++)
    for (t1=(GEN*)D,j=E[i]; j; j--,t1=t2)
      for (t2=d, t3=t1; t3<t2; )
      {
        GEN a, b;
        a = mul(gel(*++t3,1), gel(P,i));
        b = leafcopy(gel(*t3,2)); b[i]++;
        *++d = mkvec2(a,b);
      }
  if (isint) gen_sort_inplace(D,NULL,&cmpi1,NULL);
  for (i = 1; i <= n; i++) gmael(D,i,2) = fa_clean(P, gmael(D,i,2));
  return gerepilecopy(av, D);
}
GEN
divisors(GEN N)
{
  long i, j, l;
  GEN *d, *t1, *t2, *t3, D, P, E;
  int isint = divisors_init(N, &P, &E);
  GEN (*mul)(GEN,GEN) = isint? mulii: gmul;

  D = cgetg(ndiv(E)+1,t_VEC); d = (GEN*)D;
  l = lg(E);
  *++d = gen_1;
  for (i=1; i<l; i++)
    for (t1=(GEN*)D,j=E[i]; j; j--,t1=t2)
      for (t2=d, t3=t1; t3<t2; ) *++d = mul(*++t3, gel(P,i));
  if (isint) ZV_sort_inplace(D);
  return D;
}
GEN
divisors0(GEN N, long flag)
{
  if (flag && flag != 1) pari_err_FLAG("divisors");
  return flag? divisors_factored(N): divisors(N);
}

GEN
divisorsu_fact(GEN fa)
{
  GEN d, t, t1, t2, t3, P = gel(fa,1), E = gel(fa,2);
  long i, j, l = lg(P);
  d = t = cgetg(numdivu_fact(fa) + 1,t_VECSMALL);
  *++d = 1;
  for (i=1; i<l; i++)
    for (t1=t,j=E[i]; j; j--,t1=t2)
      for (t2=d, t3=t1; t3<t2; ) *(++d) = *(++t3) * P[i];
  vecsmall_sort(t); return t;
}
GEN
divisorsu(ulong N)
{
  pari_sp av = avma;
  return gerepileupto(av, divisorsu_fact(factoru(N)));
}

static GEN
corefa(GEN fa)
{
  GEN P = gel(fa,1), E = gel(fa,2), c = gen_1;
  long i;
  for (i=1; i<lg(P); i++)
    if (mod2(gel(E,i))) c = mulii(c,gel(P,i));
  return c;
}
static GEN
core2fa(GEN fa)
{
  GEN P = gel(fa,1), E = gel(fa,2), c = gen_1, f = gen_1;
  long i;
  for (i=1; i<lg(P); i++)
  {
    long e = itos(gel(E,i));
    if (e & 1)  c = mulii(c, gel(P,i));
    if (e != 1) f = mulii(f, powiu(gel(P,i), e >> 1));
  }
  return mkvec2(c,f);
}
GEN
corepartial(GEN n, long all)
{
  pari_sp av = avma;
  if (typ(n) != t_INT) pari_err_TYPE("corepartial",n);
  return gerepileuptoint(av, corefa(Z_factor_limit(n,all)));
}
GEN
core2partial(GEN n, long all)
{
  pari_sp av = avma;
  if (typ(n) != t_INT) pari_err_TYPE("core2partial",n);
  return gerepilecopy(av, core2fa(Z_factor_limit(n,all)));
}
/* given an arithmetic function argument, return the underlying integer */
static GEN
arith_n(GEN A)
{
  switch(typ(A))
  {
    case t_INT: return A;
    case t_VEC: return gel(A,1);
    default: return factorback(A);
  }
}
static GEN
core2_i(GEN n)
{
  GEN f = core(n);
  if (!signe(f)) return mkvec2(gen_0, gen_1);
  return mkvec2(f, sqrtint(diviiexact(arith_n(n), f)));
}
GEN
core2(GEN n) { pari_sp av = avma; return gerepilecopy(av, core2_i(n)); }

GEN
core0(GEN n,long flag) { return flag? core2(n): core(n); }

static long
_mod4(GEN c) {
  long r, s = signe(c);
  if (!s) return 0;
  r = mod4(c); if (s < 0) r = 4-r;
  return r;
}

long
corediscs(long D, ulong *f)
{
  /* D = f^2 dK */
  long dK = D>=0 ? (long) coreu(D) : -(long) coreu(-(ulong) D);
  ulong dKmod4 = ((ulong)dK)&3UL;
  if (dKmod4 == 2 || dKmod4 == 3)
    dK *= 4;
  if (f) *f = usqrt((ulong)(D/dK));
  return D;
}

GEN
coredisc(GEN n)
{
  pari_sp av = avma;
  GEN c = core(n);
  if (_mod4(c)<=1) return c; /* c = 0 or 1 mod 4 */
  return gerepileuptoint(av, shifti(c,2));
}

GEN
coredisc2(GEN n)
{
  pari_sp av = avma;
  GEN y = core2_i(n);
  GEN c = gel(y,1), f = gel(y,2);
  if (_mod4(c)<=1) return gerepilecopy(av, y);
  y = cgetg(3,t_VEC);
  gel(y,1) = shifti(c,2);
  gel(y,2) = gmul2n(f,-1); return gerepileupto(av, y);
}

GEN
coredisc0(GEN n,long flag) { return flag? coredisc2(n): coredisc(n); }

long
omegau(ulong n)
{
  pari_sp av;
  GEN F;
  if (n == 1UL) return 0;
  av = avma; F = factoru(n);
  avma = av; return lg(gel(F,1))-1;
}
long
omega(GEN n)
{
  pari_sp av;
  GEN F, P;
  if ((F = check_arith_non0(n,"omega"))) {
    long n;
    P = gel(F,1); n = lg(P)-1;
    if (n && equalim1(gel(P,1))) n--;
    return n;
  }
  if (lgefint(n) == 3) return omegau(n[2]);
  av = avma;
  F = absZ_factor(n);
  P = gel(F,1); avma = av; return lg(P)-1;
}

long
bigomegau(ulong n)
{
  pari_sp av;
  GEN F;
  if (n == 1) return 0;
  av = avma; F = factoru(n);
  avma = av; return zv_sum(gel(F,2));
}
long
bigomega(GEN n)
{
  pari_sp av = avma;
  GEN F, E;
  if ((F = check_arith_non0(n,"bigomega")))
  {
    GEN P = gel(F,1);
    long n = lg(P)-1;
    E = gel(F,2);
    if (n && equalim1(gel(P,1))) E = vecslice(E,2,n);
  }
  else if (lgefint(n) == 3)
    return bigomegau(n[2]);
  else
    E = gel(absZ_factor(n), 2);
  E = ZV_to_zv(E);
  avma = av; return zv_sum(E);
}

/* assume f = factoru(n), possibly with 0 exponents. Return phi(n) */
ulong
eulerphiu_fact(GEN f)
{
  GEN P = gel(f,1), E = gel(f,2);
  long i, m = 1, l = lg(P);
  for (i = 1; i < l; i++)
  {
    ulong p = P[i], e = E[i];
    if (!e) continue;
    if (p == 2)
    { if (e > 1) m <<= e-1; }
    else
    {
      m *= (p-1);
      if (e > 1) m *= upowuu(p, e-1);
    }
  }
  return m;
}
ulong
eulerphiu(ulong n)
{
  pari_sp av = avma;
  GEN F;
  if (!n) return 2;
  F = factoru(n);
  avma = av; return eulerphiu_fact(F);
}
GEN
eulerphi(GEN n)
{
  pari_sp av = avma;
  GEN Q, F, P, E;
  long i, l;

  if ((F = check_arith_all(n,"eulerphi")))
  {
    F = clean_Z_factor(F);
    n = arith_n(n);
    if (lgefint(n) == 3)
    {
      ulong e;
      F = mkmat2(ZV_to_nv(gel(F,1)), ZV_to_nv(gel(F,2)));
      e = eulerphiu_fact(F);
      avma = av; return utoipos(e);
    }
  }
  else if (lgefint(n) == 3) return utoipos(eulerphiu(uel(n,2)));
  else
    F = absZ_factor(n);
  if (!signe(n)) return gen_2;
  P = gel(F,1);
  E = gel(F,2); l = lg(P);
  Q = cgetg(l, t_VEC);
  for (i = 1; i < l; i++)
  {
    GEN p = gel(P,i), q;
    ulong v = itou(gel(E,i));
    q = subiu(p,1);
    if (v != 1) q = mulii(q, v == 2? p: powiu(p, v-1));
    gel(Q,i) = q;
  }
  return gerepileuptoint(av, ZV_prod(Q));
}

long
numdivu_fact(GEN fa)
{
  GEN E = gel(fa,2);
  long n = 1, i, l = lg(E);
  for (i = 1; i < l; i++) n *= E[i]+1;
  return n;
}
long
numdivu(long N)
{
  pari_sp av;
  GEN fa;
  if (N == 1) return 1;
  av = avma; fa = factoru(N);
  avma = av; return numdivu_fact(fa);
}
static GEN
numdiv_aux(GEN F)
{
  GEN x, E = gel(F,2);
  long i, l = lg(E);
  x = cgetg(l, t_VECSMALL);
  for (i=1; i<l; i++) x[i] = itou(gel(E,i))+1;
  return x;
}
GEN
numdiv(GEN n)
{
  pari_sp av = avma;
  GEN F, E;
  if ((F = check_arith_non0(n,"numdiv")))
  {
    F = clean_Z_factor(F);
    E = numdiv_aux(F);
  }
  else if (lgefint(n) == 3)
    return utoipos(numdivu(n[2]));
  else
    E = numdiv_aux(absZ_factor(n));
  return gerepileuptoint(av, zv_prod_Z(E));
}

/* 1 + p + ... + p^v, p != 2^BIL - 1 */
static GEN
u_euler_sumdiv(ulong p, long v)
{
  GEN u = utoipos(1 + p); /* can't overflow */
  for (; v > 1; v--) u = addui(1, mului(p, u));
  return u;
}
/* 1 + q + ... + q^v */
static GEN
euler_sumdiv(GEN q, long v)
{
  GEN u = addui(1, q);
  for (; v > 1; v--) u = addui(1, mulii(q, u));
  return u;
}

static GEN
sumdiv_aux(GEN F)
{
  GEN x, P = gel(F,1), E = gel(F,2);
  long i, l = lg(P);
  x = cgetg(l, t_VEC);
  for (i=1; i<l; i++) gel(x,i) = euler_sumdiv(gel(P,i), itou(gel(E,i)));
  return ZV_prod(x);
}
GEN
sumdiv(GEN n)
{
  pari_sp av = avma;
  GEN F, v;

  if ((F = check_arith_non0(n,"sumdiv")))
  {
    F = clean_Z_factor(F);
    v = sumdiv_aux(F);
  }
  else if (lgefint(n) == 3)
  {
    if (n[2] == 1) return gen_1;
    F = factoru(n[2]);
    v = usumdiv_fact(F);
  }
  else
    v = sumdiv_aux(absZ_factor(n));
  return gerepileuptoint(av, v);
}

static GEN
sumdivk_aux(GEN F, long k)
{
  GEN x, P = gel(F,1), E = gel(F,2);
  long i, l = lg(P);
  x = cgetg(l, t_VEC);
  for (i=1; i<l; i++) gel(x,i) = euler_sumdiv(powiu(gel(P,i),k), gel(E,i)[2]);
  return ZV_prod(x);
}
GEN
sumdivk(GEN n, long k)
{
  pari_sp av = avma;
  GEN F, v;
  long k1;

  if (!k) return numdiv(n);
  if (k == 1) return sumdiv(n);
  if ((F = check_arith_non0(n,"sumdivk"))) F = clean_Z_factor(F);
  k1 = k; if (k < 0)  k = -k;
  if (k == 1)
    v = sumdiv(F? F: n);
  else
  {
    if (F)
      v = sumdivk_aux(F,k);
    else if (lgefint(n) == 3)
    {
      if (n[2] == 1) return gen_1;
      F = factoru(n[2]);
      v = usumdivk_fact(F,k);
    }
    else
      v = sumdivk_aux(absZ_factor(n), k);
    if (k1 > 0) return gerepileuptoint(av, v);
  }

  if (F) n = arith_n(n);
  if (k != 1) n = powiu(n,k);
  return gerepileupto(av, gdiv(v, n));
}

GEN
usumdiv_fact(GEN f)
{
  GEN P = gel(f,1), E = gel(f,2);
  long i, l = lg(P);
  GEN v = cgetg(l, t_VEC);
  for (i=1; i<l; i++) gel(v,i) = u_euler_sumdiv(P[i],E[i]);
  return ZV_prod(v);
}
GEN
usumdivk_fact(GEN f, ulong k)
{
  GEN P = gel(f,1), E = gel(f,2);
  long i, l = lg(P);
  GEN v = cgetg(l, t_VEC);
  for (i=1; i<l; i++) gel(v,i) = euler_sumdiv(powuu(P[i],k),E[i]);
  return ZV_prod(v);
}

long
uissquarefree_fact(GEN f)
{
  GEN E = gel(f,2);
  long i, l = lg(E);
  for (i = 1; i < l; i++)
    if (E[i] > 1) return 0;
  return 1;
}
long
uissquarefree(ulong n)
{
  if (!n) return 0;
  return moebiusu(n)? 1: 0;
}
long
Z_issquarefree(GEN n)
{
  switch(lgefint(n))
  {
    case 2: return 0;
    case 3: return uissquarefree(n[2]);
  }
  return moebius(n)? 1: 0;
}

static int
fa_issquarefree(GEN F)
{
  GEN P = gel(F,1), E = gel(F,2);
  long i, s, l = lg(P);
  if (l == 1) return 1;
  s = signe(gel(P,1)); /* = signe(x) */
  if (!s) return 0;
  for(i = 1; i < l; i++)
    if (!equali1(gel(E,i))) return 0;
  return 1;
}
long
issquarefree(GEN x)
{
  pari_sp av;
  GEN d;
  switch(typ(x))
  {
    case t_INT: return Z_issquarefree(x);
    case t_POL:
      if (!signe(x)) return 0;
      av = avma; d = RgX_gcd(x, RgX_deriv(x));
      avma = av; return (lg(d) == 3);
    case t_VEC:
    case t_MAT: return fa_issquarefree(check_arith_all(x,"issquarefree"));
    default: pari_err_TYPE("issquarefree",x);
      return 0; /* LCOV_EXCL_LINE */
  }
}

/*********************************************************************/
/**                                                                 **/
/**                    DIGITS / SUM OF DIGITS                       **/
/**                                                                 **/
/*********************************************************************/

/* set v[i] = 1 iff B^i is needed in the digits_dac algorithm */
static void
set_vexp(GEN v, long l)
{
  long m;
  if (v[l]) return;
  v[l] = 1; m = l>>1;
  set_vexp(v, m);
  set_vexp(v, l-m);
}

/* return all needed B^i for DAC algorithm, for lz digits */
static GEN
get_vB(GEN T, long lz, void *E, struct bb_ring *r)
{
  GEN vB, vexp = const_vecsmall(lz, 0);
  long i, l = (lz+1) >> 1;
  vexp[1] = 1;
  vexp[2] = 1;
  set_vexp(vexp, lz);
  vB = zerovec(lz); /* unneeded entries remain = 0 */
  gel(vB, 1) = T;
  for (i = 2; i <= l; i++)
    if (vexp[i])
    {
      long j = i >> 1;
      GEN B2j = r->sqr(E, gel(vB,j));
      gel(vB,i) = odd(i)? r->mul(E, B2j, T): B2j;
    }
  return vB;
}

static void
gen_digits_dac(GEN x, GEN vB, long l, GEN *z,
               void *E, GEN div(void *E, GEN a, GEN b, GEN *r))
{
  GEN q, r;
  long m = l>>1;
  if (l==1) { *z=x; return; }
  q = div(E, x, gel(vB,m), &r);
  gen_digits_dac(r, vB, m, z, E, div);
  gen_digits_dac(q, vB, l-m, z+m, E, div);
}

static GEN
gen_fromdigits_dac(GEN x, GEN vB, long i, long l, void *E,
                   GEN add(void *E, GEN a, GEN b),
                   GEN mul(void *E, GEN a, GEN b))
{
  GEN a, b;
  long m = l>>1;
  if (l==1) return gel(x,i);
  a = gen_fromdigits_dac(x, vB, i, m, E, add, mul);
  b = gen_fromdigits_dac(x, vB, i+m, l-m, E, add, mul);
  return add(E, a, mul(E, b, gel(vB, m)));
}

static GEN
gen_digits_i(GEN x, GEN B, long n, void *E, struct bb_ring *r,
                          GEN (*div)(void *E, GEN x, GEN y, GEN *r))
{
  GEN z, vB;
  if (n==1) retmkvec(gcopy(x));
  vB = get_vB(B, n, E, r);
  z = cgetg(n+1, t_VEC);
  gen_digits_dac(x, vB, n, (GEN*)(z+1), E, div);
  return z;
}

GEN
gen_digits(GEN x, GEN B, long n, void *E, struct bb_ring *r,
                          GEN (*div)(void *E, GEN x, GEN y, GEN *r))
{
  pari_sp av = avma;
  return gerepilecopy(av, gen_digits_i(x, B, n, E, r, div));
}

GEN
gen_fromdigits(GEN x, GEN B, void *E, struct bb_ring *r)
{
  pari_sp av = avma;
  long n = lg(x)-1;
  GEN vB = get_vB(B, n, E, r);
  GEN z = gen_fromdigits_dac(x, vB, 1, n, E, r->add, r->mul);
  return gerepilecopy(av, z);
}

static GEN
_addii(void *data /* ignored */, GEN x, GEN y)
{ (void)data; return addii(x,y); }
static GEN
_sqri(void *data /* ignored */, GEN x) { (void)data; return sqri(x); }
static GEN
_mulii(void *data /* ignored */, GEN x, GEN y)
 { (void)data; return mulii(x,y); }
static GEN
_dvmdii(void *data /* ignored */, GEN x, GEN y, GEN *r)
 { (void)data; return dvmdii(x,y,r); }

static struct bb_ring Z_ring = { _addii, _mulii, _sqri };

static GEN
check_basis(GEN B)
{
  if (!B) return utoipos(10);
  if (typ(B)!=t_INT) pari_err_TYPE("digits",B);
  if (abscmpiu(B,2)<0) pari_err_DOMAIN("digits","B","<",gen_2,B);
  return B;
}

/* x has l digits in base B, write them to z[0..l-1], vB[i] = B^i */
static void
digits_dacsmall(GEN x, GEN vB, long l, ulong* z)
{
  pari_sp av = avma;
  GEN q,r;
  long m;
  if (l==1) { *z=itou(x); return; }
  m=l>>1;
  q = dvmdii(x, gel(vB,m), &r);
  digits_dacsmall(q,vB,l-m,z);
  digits_dacsmall(r,vB,m,z+l-m);
  avma = av;
}

GEN
digits(GEN x, GEN B)
{
  pari_sp av=avma;
  long lz;
  GEN z, vB;
  if (typ(x)!=t_INT) pari_err_TYPE("digits",x);
  B = check_basis(B);
  if (signe(B)<0) pari_err_DOMAIN("digits","B","<",gen_0,B);
  if (!signe(x))       {avma = av; return cgetg(1,t_VEC); }
  if (abscmpii(x,B)<0) {avma = av; retmkvec(absi(x)); }
  if (Z_ispow2(B))
  {
    long k = expi(B);
    if (k == 1) return binaire(x);
    if (k < BITS_IN_LONG)
    {
      (void)new_chunk(4*(expi(x) + 2)); /* HACK */
      z = binary_2k_nv(x, k);
      avma = av; return Flv_to_ZV(z);
    }
    else
    {
      avma = av; return binary_2k(x, k);
    }
  }
  x = absi_shallow(x);
  lz = logint(x,B) + 1;
  if (lgefint(B)>3)
  {
    z = gerepileupto(av, gen_digits_i(x, B, lz, NULL, &Z_ring, _dvmdii));
    vecreverse_inplace(z); return z;
  }
  else
  {
    vB = get_vB(B, lz, NULL, &Z_ring);
    (void)new_chunk(3*lz); /* HACK */
    z = zero_zv(lz);
    digits_dacsmall(x,vB,lz,(ulong*)(z+1));
    avma = av; return Flv_to_ZV(z);
  }
}

static GEN
fromdigitsu_dac(GEN x, GEN vB, long i, long l)
{
  GEN a, b;
  long m = l>>1;
  if (l==1) return utoi(uel(x,i));
  if (l==2) return addumului(uel(x,i), uel(x,i+1), gel(vB, m));
  a = fromdigitsu_dac(x, vB, i, m);
  b = fromdigitsu_dac(x, vB, i+m, l-m);
  return addii(a, mulii(b, gel(vB, m)));
}

GEN
fromdigitsu(GEN x, GEN B)
{
  pari_sp av = avma;
  long n = lg(x)-1;
  GEN vB, z;
  if (n==0) return gen_0;
  vB = get_vB(B, n, NULL, &Z_ring);
  z = fromdigitsu_dac(x, vB, 1, n);
  return gerepileuptoint(av, z);
}

static int
ZV_in_range(GEN v, GEN B)
{
  long i, l = lg(v);
  for(i=1; i < l; i++)
  {
    GEN vi = gel(v, i);
    if (signe(vi) < 0 || cmpii(vi, B) >= 0)
      return 0;
  }
  return 1;
}

GEN
fromdigits(GEN x, GEN B)
{
  pari_sp av = avma;
  if (typ(x)!=t_VEC || !RgV_is_ZV(x)) pari_err_TYPE("fromdigits",x);
  if (lg(x)==1) return gen_0;
  B = check_basis(B);
  if (Z_ispow2(B) && ZV_in_range(x, B))
    return fromdigits_2k(x, expi(B));
  x = vecreverse(x);
  return gerepileuptoint(av, gen_fromdigits(x, B, NULL, &Z_ring));
}

static const ulong digsum[] ={
  0,1,2,3,4,5,6,7,8,9,1,2,3,4,5,6,7,8,9,10,2,3,4,5,6,7,8,9,10,11,3,4,5,6,7,8,
  9,10,11,12,4,5,6,7,8,9,10,11,12,13,5,6,7,8,9,10,11,12,13,14,6,7,8,9,10,11,
  12,13,14,15,7,8,9,10,11,12,13,14,15,16,8,9,10,11,12,13,14,15,16,17,9,10,11,
  12,13,14,15,16,17,18,1,2,3,4,5,6,7,8,9,10,2,3,4,5,6,7,8,9,10,11,3,4,5,6,7,8,
  9,10,11,12,4,5,6,7,8,9,10,11,12,13,5,6,7,8,9,10,11,12,13,14,6,7,8,9,10,11,
  12,13,14,15,7,8,9,10,11,12,13,14,15,16,8,9,10,11,12,13,14,15,16,17,9,10,11,
  12,13,14,15,16,17,18,10,11,12,13,14,15,16,17,18,19,2,3,4,5,6,7,8,9,10,11,3,
  4,5,6,7,8,9,10,11,12,4,5,6,7,8,9,10,11,12,13,5,6,7,8,9,10,11,12,13,14,6,7,8,
  9,10,11,12,13,14,15,7,8,9,10,11,12,13,14,15,16,8,9,10,11,12,13,14,15,16,17,
  9,10,11,12,13,14,15,16,17,18,10,11,12,13,14,15,16,17,18,19,11,12,13,14,15,
  16,17,18,19,20,3,4,5,6,7,8,9,10,11,12,4,5,6,7,8,9,10,11,12,13,5,6,7,8,9,10,
  11,12,13,14,6,7,8,9,10,11,12,13,14,15,7,8,9,10,11,12,13,14,15,16,8,9,10,11,
  12,13,14,15,16,17,9,10,11,12,13,14,15,16,17,18,10,11,12,13,14,15,16,17,18,
  19,11,12,13,14,15,16,17,18,19,20,12,13,14,15,16,17,18,19,20,21,4,5,6,7,8,9,
  10,11,12,13,5,6,7,8,9,10,11,12,13,14,6,7,8,9,10,11,12,13,14,15,7,8,9,10,11,
  12,13,14,15,16,8,9,10,11,12,13,14,15,16,17,9,10,11,12,13,14,15,16,17,18,10,
  11,12,13,14,15,16,17,18,19,11,12,13,14,15,16,17,18,19,20,12,13,14,15,16,17,
  18,19,20,21,13,14,15,16,17,18,19,20,21,22,5,6,7,8,9,10,11,12,13,14,6,7,8,9,
  10,11,12,13,14,15,7,8,9,10,11,12,13,14,15,16,8,9,10,11,12,13,14,15,16,17,9,
  10,11,12,13,14,15,16,17,18,10,11,12,13,14,15,16,17,18,19,11,12,13,14,15,16,
  17,18,19,20,12,13,14,15,16,17,18,19,20,21,13,14,15,16,17,18,19,20,21,22,14,
  15,16,17,18,19,20,21,22,23,6,7,8,9,10,11,12,13,14,15,7,8,9,10,11,12,13,14,
  15,16,8,9,10,11,12,13,14,15,16,17,9,10,11,12,13,14,15,16,17,18,10,11,12,13,
  14,15,16,17,18,19,11,12,13,14,15,16,17,18,19,20,12,13,14,15,16,17,18,19,20,
  21,13,14,15,16,17,18,19,20,21,22,14,15,16,17,18,19,20,21,22,23,15,16,17,18,
  19,20,21,22,23,24,7,8,9,10,11,12,13,14,15,16,8,9,10,11,12,13,14,15,16,17,9,
  10,11,12,13,14,15,16,17,18,10,11,12,13,14,15,16,17,18,19,11,12,13,14,15,16,
  17,18,19,20,12,13,14,15,16,17,18,19,20,21,13,14,15,16,17,18,19,20,21,22,14,
  15,16,17,18,19,20,21,22,23,15,16,17,18,19,20,21,22,23,24,16,17,18,19,20,21,
  22,23,24,25,8,9,10,11,12,13,14,15,16,17,9,10,11,12,13,14,15,16,17,18,10,11,
  12,13,14,15,16,17,18,19,11,12,13,14,15,16,17,18,19,20,12,13,14,15,16,17,18,
  19,20,21,13,14,15,16,17,18,19,20,21,22,14,15,16,17,18,19,20,21,22,23,15,16,
  17,18,19,20,21,22,23,24,16,17,18,19,20,21,22,23,24,25,17,18,19,20,21,22,23,
  24,25,26,9,10,11,12,13,14,15,16,17,18,10,11,12,13,14,15,16,17,18,19,11,12,
  13,14,15,16,17,18,19,20,12,13,14,15,16,17,18,19,20,21,13,14,15,16,17,18,19,
  20,21,22,14,15,16,17,18,19,20,21,22,23,15,16,17,18,19,20,21,22,23,24,16,17,
  18,19,20,21,22,23,24,25,17,18,19,20,21,22,23,24,25,26,18,19,20,21,22,23,24,
  25,26,27
};

ulong
sumdigitsu(ulong n)
{
  ulong s = 0;
  while (n) { s += digsum[n % 1000]; n /= 1000; }
  return s;
}

/* res=array of 9-digits integers, return \sum_{0 <= i < l} sumdigits(res[i]) */
static ulong
sumdigits_block(ulong *res, long l)
{
  long s = sumdigitsu(*--res);
  while (--l > 0) s += sumdigitsu(*--res);
  return s;
}

GEN
sumdigits(GEN n)
{
  pari_sp av = avma;
  ulong s, *res;
  long l;

  if (typ(n) != t_INT) pari_err_TYPE("sumdigits", n);
  l = lgefint(n);
  switch(l)
  {
    case 2: return gen_0;
    case 3: return utoipos(sumdigitsu(n[2]));
  }
  res = convi(n, &l);
  if ((ulong)l < ULONG_MAX / 81)
  {
    s = sumdigits_block(res, l);
    avma = av; return utoipos(s);
  }
  else /* Huge. Overflows ulong */
  {
    const long L = (long)(ULONG_MAX / 81);
    GEN S = gen_0;
    while (l > L)
    {
      S = addiu(S, sumdigits_block(res, L));
      res += L; l -= L;
    }
    if (l)
      S = addiu(S, sumdigits_block(res, l));
    return gerepileuptoint(av, S);
  }
}

GEN
sumdigits0(GEN x, GEN B)
{
  pari_sp av = avma;
  GEN z;
  long lz;

  if (!B) return sumdigits(x);
  if (typ(x) != t_INT) pari_err_TYPE("sumdigits", x);
  B = check_basis(B);
  if (Z_ispow2(B))
  {
    long k = expi(B);
    if (k == 1) { avma = av; return utoi(hammingweight(x)); }
    if (k < BITS_IN_LONG)
    {
      GEN z = binary_2k_nv(x, k);
      if (lg(z)-1 > 1L<<(BITS_IN_LONG-k)) /* may overflow */
        return gerepileuptoint(av, ZV_sum(Flv_to_ZV(z)));
      avma = av; return utoi(zv_sum(z));
    }
    return gerepileuptoint(av, ZV_sum(binary_2k(x, k)));
  }
  if (!signe(x))       { avma = av; return gen_0; }
  if (abscmpii(x,B)<0) { avma = av; return absi(x); }
  if (absequaliu(B,10))   { avma = av; return sumdigits(x); }
  x = absi_shallow(x); lz = logint(x,B) + 1;
  z = gen_digits_i(x, B, lz, NULL, &Z_ring, _dvmdii);
  return gerepileuptoint(av, ZV_sum(z));
}
