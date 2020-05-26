/* Copyright (C) 2009  The PARI group.

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

/************************************************************/
/*     Computation of all the extensions of a given         */
/*               degree of a p-adic field                   */
/* Xavier Roblot                                            */
/************************************************************/
/* cf. Math. Comp, vol. 70, No. 236, pp. 1641-1659 for more details.
   Note that n is now e (since the e from the paper is always = 1) and l
   is now f */
/* Structure for a given type of extension */
typedef struct {
  GEN p;
  long e, f, j;
  long a, b, c;
  long v;     /* auxiliary variable */
  long r;     /* pr = p^r */
  GEN pr;     /* p-adic precision for poly. reduction */
  GEN q, qm1; /* p^f, q - 1 */
  GEN T;      /* polynomial defining K^ur */
  GEN frob;   /* Frobenius acting of the root of T (mod pr) */
  GEN u;      /* suitable root of unity (expressed in terms of the root of T) */
  GEN nbext;  /* number of extensions */
  GEN roottable; /* table of roots of polynomials over the residue field */
  GEN pk;     /* powers of p: [p^1, p^2, ..., p^c] */
} KRASNER_t;

/* Structure containing the field data (constructed with FieldData) */
typedef struct {
  GEN p;
  GEN top;  /* absolute polynomial of a = z + pi (mod pr) */
  GEN topr; /* top mod p */
  GEN z;    /* root of T in terms of a (mod pr) */
  GEN eis;  /* relative polynomial of pi in terms of z (mod pr)  */
  GEN pi;   /* prime element in terms of a */
  GEN ipi;  /* p/pi in terms of a (mod pr) (used to divide by pi) */
  GEN pik;  /* [1, pi, ..., pi^(e-1), pi^e/p] in terms of a (mod pr).
               Note the last one is different! */
  long cj;  /* number of conjugate fields */
} FAD_t;

#undef CHECK

/* Eval P(x) assuming P has positive coefficients and the result is a long */
static ulong
ZX_z_eval(GEN P, ulong x)
{
  long i, l = lg(P);
  ulong z;

  if (typ(P) == t_INT) return itou(P);
  if (l == 2) return 0;
  z = itou(gel(P, l-1));
  for (i = l-2; i > 1; i--) z = z*x + itou(gel(P,i));
  return z;
}

/* Eval P(x, y) assuming P has positive coefficients and the result is a long */
static ulong
ZXY_z_eval(GEN P, ulong x, ulong y)
{
  long i, l = lg(P);
  ulong z;

  if (l == 2) return 0;
  z = ZX_z_eval(gel(P, l-1), y);
  for (i = l-2; i > 1; i--) z = z*x + ZX_z_eval(gel(P, i), y);
  return z;
}

/* P an Fq[X], where Fq = Fp[Y]/(T(Y)), a an FpX representing the automorphism
 * y -> a(y). Return a(P), applying a() coefficientwise. */
static GEN
FqX_FpXQ_eval(GEN P, GEN a, GEN T, GEN p)
{
  long i, l;
  GEN Q = cgetg_copy(P, &l);

  Q[1] = P[1];
  for (i = 2; i < l; i++)
  {
    GEN cf = gel(P, i);
    if (typ(cf) == t_POL) {
      switch(degpol(cf))
      {
        case -1: cf = gen_0; break;
        case 0:  cf = gel(cf,2); break;
        default:
          cf = FpX_FpXQ_eval(cf, a, T, p);
          cf = simplify_shallow(cf);
          break;
      }
    }
    gel(Q, i) = cf;
  }

  return Q;
}

/* Sieving routines */
static GEN
InitSieve(long l) { return zero_F2v(l); }
static long
NextZeroValue(GEN sv, long i)
{
  for(; i <= sv[1]; i++)
    if (!F2v_coeff(sv, i)) return i;
  return 0; /* sieve is full or out of the sieve! */
}
static void
SetSieveValue(GEN sv, long i)
{ if (i >= 1 && i <= sv[1]) F2v_set(sv, i); }

/* return 1 if the data verify Ore condition and 0 otherwise */
static long
VerifyOre(GEN p, long e, long j)
{
  long nv, b, vb, nb;

  if (j < 0) return 0;
  nv = e * u_pval(e, p);
  b  = j%e;
  if (b == 0) return (j == nv);
  if (j > nv) return 0;
  /* j < nv */
  vb = u_pval(b, p);
  nb = vb*e;
  return (nb <= j);
}

/* Given [K:Q_p] = m and disc(K/Q_p) = p^d, return all decompositions K/K^ur/Q_p
 * as [e, f, j] with
 *   K^ur/Q_p unramified of degree f,
 *   K/K^ur totally ramified of degree e and discriminant p^(e+j-1);
 * thus d = f*(e+j-1) and j > 0 iff ramification is wild */
static GEN
possible_efj_by_d(GEN p, long m, long d)
{
  GEN rep, div;
  long i, ctr, l;

  if (d == 0) return mkvec(mkvecsmall3(1, m, 0)); /* unramified */
  div = divisorsu(ugcd(m, d));
  l = lg(div); ctr = 1;
  rep = cgetg(l, t_VEC);
  for (i = 1; i < l; i++)
  {
    long f = div[i], e = m/f, j = d/f - e + 1;
    if (VerifyOre(p, e, j)) gel(rep, ctr++) = mkvecsmall3(e, f, j);
  }
  setlg(rep, ctr); return rep;
}

/* return the number of extensions corresponding to (e,f,j) */
static GEN
NumberExtensions(KRASNER_t *data)
{
  ulong pp, pa;
  long e, a, b;
  GEN p, q, s0, p1;

  e = data->e;
  p = data->p;
  q = data->q;
  a = data->a; /* floor(j/e) <= v_p(e), hence p^a | e */
  b = data->b; /* j % e */
  if (is_bigint(p)) /* implies a = 0 */
    return b == 0? utoipos(e): mulsi(e, data->qm1);

  pp = p[2];
  switch(a)
  {
    case 0:  pa = 1;  s0 = utoipos(e); break;
    case 1:  pa = pp; s0 = mului(e, powiu(q, e / pa)); break;
    default:
      pa = upowuu(pp, a); /* p^a */
      s0 = mulsi(e, powiu(q, (e / pa) * ((pa - 1) / (pp - 1))));
  }
  /* s0 = e * q^(e*sum(p^-i, i=1...a)) */
  if (b == 0) return s0;

  /* q^floor((b-1)/p^(a+1)) */
  p1 = powiu(q, sdivsi(b-1, muluu(pa, pp)));
  return mulii(mulii(data->qm1, s0), p1);
}

static GEN
get_topx(KRASNER_t *data, GEN eis)
{
  GEN p1, p2, rpl, c;
  pari_sp av;
  long j;
  /* top poly. is the minimal polynomial of root(T) + root(eis) */
  if (data->f == 1) return eis;
  c = FpX_neg(pol_x(data->v),data->pr);
  rpl = FqX_translate(eis, c, data->T, data->pr);
  p1 = p2 = rpl; av = avma;
  for (j = 1; j < data->f; j++)
  {
    /* compute conjugate polynomials using the Frobenius */
    p1 = FqX_FpXQ_eval(p1, data->frob, data->T, data->pr);
    p2 = FqX_mul(p2, p1, data->T, data->pr);
    if (gc_needed(av,2)) gerepileall(av, 2, &p1,&p2);
  }
  return simplify_shallow(p2); /* ZX */
}

/* eis (ZXY): Eisenstein polynomial over the field defined by T.
 * topx (ZX): absolute equation of root(T) + root(eis).
 * Return the struct FAD corresponding to the field it defines (GENs created
 * as clones). Assume e > 1. */
static void
FieldData(KRASNER_t *data, FAD_t *fdata, GEN eis, GEN topx)
{
  GEN p1, p2, p3, z, ipi, cipi, dipi, t, Q;

  fdata->p = data->p;
  t = leafcopy(topx); setvarn(t, data->v);
  fdata->top  = t;
  fdata->topr = FpX_red(t, data->pr);

  if (data->f == 1) z = gen_0;
  else
  { /* Compute a root of T in K(top) using Hensel's lift */
    z = pol_x(data->v);
    p1 = FpX_deriv(data->T, data->p);
    /* First lift to a root mod p */
    for (;;) {
      p2 = FpX_FpXQ_eval(data->T, z, fdata->top, data->p);
      if (gcmp0(p2)) break;
      p3 = FpX_FpXQ_eval(p1, z, fdata->top, data->p);
      z  = FpX_sub(z, FpXQ_div(p2, p3, fdata->top, data->p), data->p);
    }
    /* Then a root mod p^r */
    z = ZpX_ZpXQ_liftroot(data->T, z, fdata->top, data->p, data->r);
  }

  fdata->z  = z;
  fdata->eis = eis;
  fdata->pi  = Fq_sub(pol_x(data->v), fdata->z,
                      FpX_red(fdata->top, data->p), data->p);
  ipi = RgXQ_inv(fdata->pi, fdata->top);
  ipi = Q_remove_denom(ipi, &dipi);
  Q = mulii(data->pr, data->p);
  cipi = Fp_inv(diviiexact(dipi, data->p), Q);
  fdata->ipi = FpX_Fp_mul(ipi, cipi, Q); /* p/pi mod p^(pr+1) */

  /* Last one is set to pi^e/p (so we compute pi^e with one extra precision) */
  p2 = mulii(data->pr, data->p);
  p1 = FpXQ_powers(fdata->pi, data->e, fdata->topr, p2);
  gel(p1, data->e+1) = ZX_Z_divexact(gel(p1, data->e+1), data->p);
  fdata->pik  = p1;
}

/* return pol*ipi/p (mod top, pp) if it has integral coefficient, NULL
   otherwise. The result is reduced mod top, pp */
static GEN
DivideByPi(FAD_t *fdata, GEN pp, GEN ppp, GEN pol)
{
  GEN P;
  long i, l;
  pari_sp av = avma;

  /* "pol" is a t_INT or an FpX: signe() works for both */
  if (!signe(pol)) return pol;

  P = Fq_mul(pol, fdata->ipi, fdata->top, ppp); /* FpX */
  l  = lg(P);
  for (i = 2; i < l; i++)
  {
    GEN r;
    gel(P,i) = dvmdii(gel(P,i), fdata->p, &r);
    if (r != gen_0) { avma = av; return NULL; }
  }
  return FpX_red(P, pp);
}

/* return pol# = pol~/pi^vpi(pol~) mod pp where pol~(x) = pol(pi.x + beta)
 * has coefficients in the field defined by top and pi is a prime element */
static GEN
GetSharp(FAD_t *fdata, GEN pp, GEN ppp, GEN pol, GEN beta, long *pl)
{
  GEN p1, p2;
  long i, v, l, d = degpol(pol);
  pari_sp av = avma;

  if (!gequal0(beta))
    p1 = FqX_translate(pol, beta, fdata->topr, pp);
  else
    p1 = shallowcopy(pol);
  p2 = p1;
  for (v = 0;; v++)
  {
    for (i = 0; i <= v; i++)
    {
      GEN c = gel(p2, i+2);
      c = DivideByPi(fdata, pp, ppp, c);
      if (!c) break;
      gel(p2, i+2) = c;
    }
    if (i <= v) break;
    p1 = shallowcopy(p2);
  }
  if (!v) pari_err_BUG("GetSharp [no division]");

  for (l = v; l >= 0; l--)
  {
    GEN c = gel(p1, l+2);
    c = DivideByPi(fdata, pp, ppp, c);
    if (!c) { break; }
  }

  *pl = l; if (l < 2) return NULL;

  /* adjust powers */
  for (i = v+1; i <= d; i++)
    gel(p1, i+2) = Fq_mul(gel(p1, i+2),
                          gel(fdata->pik, i-v+1), fdata->topr, pp);

  return gerepilecopy(av, normalizepol(p1));
}

/* Compute roots of pol in the residue field. Use table look-up if possible */
static GEN
Quick_FqX_roots(KRASNER_t *data, GEN pol)
{
  GEN rts;
  ulong ind = 0;

  if (data->f == 1)
    pol = FpXY_evalx(pol, gen_0, data->p);
  else
    pol = FqX_red(pol, data->T, data->p);
  if (data->roottable)
  {
    ind = ZXY_z_eval(pol, data->q[2], data->p[2]);
    if (gel(data->roottable, ind)) return gel(data->roottable, ind);
  }
  rts = FqX_roots(pol, data->T, data->p);
  if (ind) gel(data->roottable, ind) = gclone(rts);
  return rts;
}

static void
FreeRootTable(GEN T)
{
  if (T)
  {
    long j, l = lg(T);
    for (j = 1; j < l; j++)
      if (gel(T,j)) gunclone(gel(T,j));
  }
}

/* Return the number of roots of pol congruent to alpha modulo pi working
   modulo pp (all roots if alpha is NULL); if flag is non-zero, return 1
   as soon as a root is found. (Note: ppp = pp*p for DivideByPi) */
static long
RootCongruents(KRASNER_t *data, FAD_t *fdata, GEN pol, GEN alpha, GEN pp, GEN ppp, long sl, long flag)
{
  GEN R;
  long s, i;

  if (alpha)
  {
    long l;
    pol = GetSharp(fdata, pp, ppp, pol, alpha, &l);
    if (l <= 1) return l;
    /* decrease precision if sl gets bigger than a multiple of e */
    sl += l;
    if (sl >= data->e)
    {
      sl -= data->e;
      ppp = pp;
      pp = diviiexact(pp, data->p);
    }
  }

  R  = Quick_FqX_roots(data, pol);
  for (s = 0, i = 1; i < lg(R); i++)
  {
    s += RootCongruents(data, fdata, pol, gel(R, i), pp, ppp, sl, flag);
    if (flag && s) return 1;
  }
  return s;
}

/* pol is a ZXY defining a polynomial over the field defined by fdata
   If flag != 0, return 1 as soon as a root is found. Computations are done with
   a precision of pr. */
static long
RootCountingAlgorithm(KRASNER_t *data, FAD_t *fdata, GEN pol, long flag)
{
  long j, l, d;
  GEN P = cgetg_copy(pol, &l);

  P[1] = pol[1];
  d = l-3;
  for (j = 0; j < d; j++)
  {
    GEN cf = gel(pol, j+2);
    if (typ(cf) == t_INT)
      cf = diviiexact(cf, data->p);
    else
      cf = ZX_Z_divexact(cf, data->p);
    gel(P, j+2) = Fq_mul(cf, gel(fdata->pik, j+1), fdata->topr, data->pr);
  }
  gel(P, d+2) = gel(fdata->pik, d+1); /* pik[d] = pi^d/p */

  return RootCongruents(data, fdata, P, NULL, diviiexact(data->pr, data->p), data->pr, 0, flag);
}

/* Return non-zero if the field given by fdata defines a field isomorphic to
 * the one defined by pol */
static long
IsIsomorphic(KRASNER_t *data, FAD_t *fdata, GEN pol)
{
  long j, nb;
  pari_sp av = avma;

  if (RgX_is_ZX(pol)) return RootCountingAlgorithm(data, fdata, pol, 1);

  for (j = 1; j <= data->f; j++)
  {
    GEN p1 = FqX_FpXQ_eval(pol, fdata->z, fdata->top, data->pr);
    nb = RootCountingAlgorithm(data, fdata, p1, 1);
    if (nb) { avma = av; return nb; }
    if (j < data->f)
      pol = FqX_FpXQ_eval(pol, data->frob, data->T, data->pr);
  }
  avma = av; return 0;
}

/* Compute the number of conjugates fields of the field given by fdata */
static void
NbConjugateFields(KRASNER_t *data, FAD_t *fdata)
{
  GEN pol = fdata->eis;
  long j, nb;
  pari_sp av = avma;

  if (RgX_is_ZX(pol)) { /* split for efficiency; contains the case f = 1 */
    fdata->cj = data->e / RootCountingAlgorithm(data, fdata, pol, 0);
    avma = av; return;
  }

  nb = 0;
  for (j = 1; j <= data->f; j++)
  { /* Transform to pol. in z to pol. in a */
    GEN p1 = FqX_FpXQ_eval(pol, fdata->z, fdata->top, data->pr);
    nb += RootCountingAlgorithm(data, fdata, p1, 0);
    /* Look at the roots of conjugates polynomials */
    if (j < data->f)
      pol = FqX_FpXQ_eval(pol, data->frob, data->T, data->pr);
  }
  avma = av;
  fdata->cj = data->e * data->f / nb;
  return;
}

/* return a minimal list of polynomials generating all the totally
   ramified extensions of K^ur of degree e and discriminant
   p^{e + j - 1} in the tamely ramified case */
static GEN
TamelyRamifiedCase(KRASNER_t *data)
{
  long av = avma;
  long g = ugcdui(data->e, data->qm1); /* (e, q-1) */
  GEN rep, eis, Xe = gpowgs(pol_x(0), data->e), m = stoi(data->e / g);

  rep = zerovec(g);
  eis = gadd(Xe, data->p);
  gel(rep, 1) = mkvec2(get_topx(data,eis), m);
  if (g > 1)
  {
    ulong pmodg = umodiu(data->p, g);
    long r = 1, ct = 1;
    GEN sv = InitSieve(g-1);
    /* let Frobenius act to get a minimal set of polynomials over Q_p */
    while (r)
    {
      long gr;
      GEN p1 = (typ(data->u) == t_INT)?
        mulii(Fp_powu(data->u, r, data->p), data->p):
        ZX_Z_mul(FpXQ_powu(data->u, r, data->T, data->p), data->p);
      eis = gadd(Xe, p1); /* add cst coef */
      ct++;
      gel(rep, ct) = mkvec2(get_topx(data,eis), m);
      gr = r;
      do { SetSieveValue(sv, gr); gr = Fl_mul(gr, pmodg, g); } while (gr != r);
      r  = NextZeroValue(sv, r);
    }
    setlg(rep, ct+1);
  }
  return gerepilecopy(av, rep);
}

static long
function_l(GEN p, long a, long b, long i)
{
  long l = 1 + a - z_pval(i, p);
  if (i < b) l++;
  return (l < 1)? 1: l;
}

/* Structure of the coefficients set Omega. Each coefficient is [start, zr]
 * meaning all the numbers of the form:
 *   zeta_0 * p^start + ... + zeta_s * p^c (s = c - start)
 * with zeta_i roots of unity (powers of zq + zero), zeta_0 = 0 is
 * possible iff zr = 1 */
static GEN
StructureOmega(KRASNER_t *data, GEN *pnbpol)
{
  GEN nbpol, O = cgetg(data->e + 1, t_VEC);
  long i;

  /* i = 0 */
  gel(O, 1) = mkvecsmall2(1, 0);
  nbpol = mulii(data->qm1, powiu(data->q, data->c - 1));
  for (i = 1; i < data->e; i++)
  {
    long v_start, zero = 0;
    GEN nbcf, p1;
    v_start = function_l(data->p, data->a, data->b, i);
    p1 = powiu(data->q, data->c - v_start);
    if (i == data->b)
      nbcf = mulii(p1, data->qm1);
    else
    {
      nbcf = mulii(p1, data->q);
      zero = 1;
    }
    gel(O, i+1) = mkvecsmall2(v_start, zero);
    nbpol = mulii(nbpol, nbcf);
  }
  *pnbpol = nbpol; return O;
}

/* a random element of the finite field */
static GEN
RandomFF(KRASNER_t *data)
{
  long i, l = data->f + 2, p = itou(data->p);
  GEN c = cgetg(l, t_POL);
  c[1] = evalvarn(data->v);
  for (i = 2; i < l; i++) gel(c, i) = utoi(random_Fl(p));
  return ZX_renormalize(c, l);
}
static GEN
RandomPol(KRASNER_t *data, GEN Omega)
{
  long i, j, l = data->e + 3, end = data->c;
  GEN pol = cgetg(l, t_POL);
  pol[1] = evalsigne(1) | evalvarn(0);
  for (i = 1; i <= data->e; i++)
  {
    GEN c, cf = gel(Omega, i);
    long st = cf[1], zr = cf[2];
    /* c = sum_{st <= j <= end} x_j p^j, where x_j are random Fq mod (p,upl)
     * If (!zr), insist on x_st != 0 */
    for (;;) {
      c = RandomFF(data);
      if (zr || signe(c)) break;
    }
    for (j = 1; j <= end-st; j++)
      c = ZX_add(c, ZX_Z_mul(RandomFF(data), gel(data->pk, j)));
    c = ZX_Z_mul(c, gel(data->pk, st));
    c = FpX_red(c, data->pr);
    switch(degpol(c))
    {
      case -1: c = gen_0; break;
      case  0: c = gel(c,2); break;
    }
    gel(pol, i+1) = c;
  }
  gel(pol, i+1) = gen_1; /* monic */
  return pol;
}

static void
CloneFieldData(FAD_t *fdata)
{
 fdata->top = gclone(fdata->top);
 fdata->topr= gclone(fdata->topr);
 fdata->z   = gclone(fdata->z);
 fdata->eis = gclone(fdata->eis);
 fdata->pi  = gclone(fdata->pi);
 fdata->ipi = gclone(fdata->ipi);
 fdata->pik = gclone(fdata->pik);
}
static void
FreeFieldData(FAD_t *fdata)
{
  gunclone(fdata->top);
  gunclone(fdata->topr);
  gunclone(fdata->z);
  gunclone(fdata->eis);
  gunclone(fdata->pi);
  gunclone(fdata->ipi);
  gunclone(fdata->pik);
}

static GEN
WildlyRamifiedCase(KRASNER_t *data)
{
  long nbext, ct, fd, nb = 0, j;
  GEN nbpol, rpl, rep, Omega;
  FAD_t **vfd;
  pari_timer T;
  pari_sp av = avma, av2;

  /* Omega = vector giving the structure of the set Omega */
  /* nbpol = number of polynomials to consider = |Omega| */
  Omega = StructureOmega(data, &nbpol);
  nbext = itos_or_0(data->nbext);
  if (!nbext || (nbext & ~LGBITS))
    pari_err_OVERFLOW("padicfields [too many extensions]");

  if (DEBUGLEVEL>0) {
    err_printf("There are %ld extensions to find and %Ps polynomials to consider\n", nbext, nbpol);
    timer_start(&T);
  }

  vfd = (FAD_t**)new_chunk(nbext);
  for (j = 0; j < nbext; j++) vfd[j] = (FAD_t*)new_chunk(sizeof(FAD_t));

  ct = 0;
  fd = 0;
  av2 = avma;

  while (fd < nbext)
  { /* Jump randomly among the polynomials : seems best... */
    rpl = RandomPol(data, Omega);
    if (DEBUGLEVEL>3) err_printf("considering polynomial %Ps\n", rpl);
    for (j = 0; j < ct; j++)
    {
      nb = IsIsomorphic(data, vfd[j], rpl);
      if (nb) break;
    }
    if (!nb)
    {
      GEN topx = get_topx(data, rpl);
      FAD_t *f = (FAD_t*)vfd[ct];
      FieldData(data, f, rpl, topx);
      CloneFieldData(f);
      NbConjugateFields(data, f);
      nb = f->cj;
      fd += nb;
      ct++;
      if (DEBUGLEVEL>1)
        err_printf("%ld more extension%s\t(%ld/%ld, %ldms)\n",
                   nb, (nb == 1)? "": "s", fd, nbext, timer_delay(&T));
    }
    avma = av2;
  }

  rep = cgetg(ct+1, t_VEC);
  for (j = 0; j < ct; j++)
  {
    FAD_t *f = (FAD_t*)vfd[j];
    GEN topx = ZX_copy(f->top);
    setvarn(topx, 0);
    gel(rep, j+1) = mkvec2(topx, stoi(f->cj));
    FreeFieldData(f);
  }
  FreeRootTable(data->roottable);
  return gerepileupto(av, rep);
}

/* return the minimal polynomial T of a generator of K^ur and the expression (mod pr)
 * in terms of T of a root of unity u such that u is l-maximal for all primes l
 * dividing g = (e,q-1). */
static void
setUnramData(KRASNER_t *d)
{
  if (d->f == 1)
  {
    d->T = pol_x(d->v);
    d->u = pgener_Fp(d->p);
    d->frob = pol_x(d->v);
  }
  else
  {
    GEN L, z, T, p = d->p;
    d->T = T = init_Fq(p, d->f, d->v);
    L = gel(factoru(ugcdui(d->e, d->qm1)), 1);
    z = gener_FpXQ_local(T, p, zv_to_ZV(L));
    d->u = ZpXQ_sqrtnlift(pol_1(d->v), d->qm1, z, T, p, d->r);
    d->frob = ZpX_ZpXQ_liftroot(T, FpXQ_pow(pol_x(d->v), p, T, p), T, p, d->r);
  }
}

/* return [ p^1, p^2, ..., p^c ] */
static GEN
get_pk(KRASNER_t *data)
{
  long i, l = data->c + 1;
  GEN pk = cgetg(l, t_VEC), p = data->p;
  gel(pk, 1) = p;
  for (i = 2; i <= data->c; i++) gel(pk, i) = mulii(gel(pk, i-1), p);
  return pk;
}

/* Compute an absolute polynomial for all the totally ramified
   extensions of Q_p(z) of degree e and discriminant p^{e + j - 1}
   where z is a root of upl defining an unramified extension of Q_p */
/* See padicfields for the meaning of flag */
static GEN
GetRamifiedPol(GEN p, GEN efj, long flag)
{
  long e = efj[1], f = efj[2], j = efj[3], i, l;
  const long v = 1;
  GEN L, pols;
  KRASNER_t data;
  pari_sp av = avma;

  if (DEBUGLEVEL>1)
    err_printf("  Computing extensions with decomposition [e, f, j] = [%ld, %ld, %ld]\n", e,f,j);
  data.p   = p;
  data.e   = e;
  data.f   = f;
  data.j   = j;
  data.a   = j/e;
  data.b   = j%e;
  data.c   = (e+2*j)/e+1;
  data.q   = powiu(p, f);
  data.qm1 = subiu(data.q, 1);
  data.v   = v;
  data.r   = 1 + (long)ceildivuu(2*j + 3, e); /* enough precision */
  data.pr  = powiu(p, data.r);
  data.nbext = NumberExtensions(&data);

  if (flag == 2) return data.nbext;

  setUnramData(&data);
  if (DEBUGLEVEL>1)
    err_printf("  Unramified part %Ps\n", data.T);
  data.roottable = NULL;
  if (j)
  {
    if (lgefint(data.q) == 3)
    {
      ulong npol = upowuu(data.q[2], e+1);
      if (npol && npol < (1<<19)) data.roottable = const_vec(npol, NULL);
    }
    data.pk = get_pk(&data);
    L = WildlyRamifiedCase(&data);
  }
  else
    L = TamelyRamifiedCase(&data);

  pols = cgetg_copy(L, &l);
  if (flag == 1)
  {
    GEN E = utoipos(e), F = utoipos(f), D = utoi(f*(e+j-1));
    for (i = 1; i < l; i++)
    {
      GEN T = gel(L,i);
      gel(pols, i) = mkvec5(ZX_copy(gel(T, 1)), E,F,D, icopy(gel(T, 2)));
    }
  }
  else
  {
    for (i = 1; i < l; i++)
    {
      GEN T = gel(L,i);
      gel(pols, i) = ZX_copy(gel(T,1));
    }
  }
  return gerepileupto(av, pols);
}

static GEN
possible_efj(GEN p, long m)
{ /* maximal possible discriminant valuation d <= m * (1+v_p(m)) - 1 */
  /* 1) [j = 0, tame] d = m - f with f | m and v_p(f) = v_p(m), or
   * 2) [j > 0, wild] d >= m, j <= v_p(e)*e   */
  ulong m1, pve, pp = p[2]; /* pp used only if v > 0 */
  long ve, v = u_pvalrem(m, p, &m1);
  GEN L, D = divisorsu(m1);
  long i, taum1 = lg(D)-1, nb = 0;

  if (v) {
    for (pve = 1,ve = 1; ve <= v; ve++) { pve *= pp; nb += pve * ve; }
    nb = itos_or_0(muluu(nb, zv_sum(D)));
    if (!nb || is_bigint( mului(pve, sqru(v)) ) )
      pari_err_OVERFLOW("padicfields [too many ramification possibilities]");
  }
  nb += taum1; /* upper bound for the number of possible triples [e,f,j] */

  L = cgetg(nb + 1, t_VEC);
  /* 1) tame */
  for (nb=1, i=1; i < lg(D); i++)
  {
    long e = D[i], f = m / e;
    gel(L, nb++) = mkvecsmall3(e, f, 0);
  }
  /* 2) wild */
  /* Ore's condition: either
   * 1) j = v_p(e) * e, or
   * 2) j = a e + b, with 0 < b < e and v_p(b) <= a < v_p(e) */
  for (pve = 1, ve = 1; ve <= v; ve++)
  {
    pve *= pp; /* = p^ve */
    for (i = 1; i < lg(D); i++)
    {
      long a,b, e = D[i] * pve, f = m / e;
      for (b = 1; b < e; b++)
        for (a = u_lval(b, pp); a < ve; a++)
          gel(L, nb++) = mkvecsmall3(e, f,  a*e + b);
      gel(L, nb++) = mkvecsmall3(e, f, ve*e);
    }
  }
  setlg(L, nb); return L;
}

#ifdef CHECK
static void
checkpols(GEN p, GEN EFJ, GEN pols)
{
  GEN pol, p1, p2;
  long c1, c2, e, f, j, i, l = lg(pols);

  if (typ(pols) == t_INT) return;

  e = EFJ[1];
  f = EFJ[2];
  j = EFJ[3];

  for (i = 1; i < l; i++)
  {
    pol = gel(pols, i);
    if (typ(pol) == t_VEC) pol = gel(pol, 1);
    if (!isirreducible(pol)) pari_err_BUG("Polynomial is reducible");
    p1 = poldisc0(pol, -1);
    if (gvaluation(p1, p) != f*(e+j-1)) pari_err_BUG("Discriminant is incorrect");
    /* only compute a p-maximal order */
    p1 = nfinitall(mkvec2(pol, mkvec(p)), 0, DEFAULTPREC);
    p2 = idealprimedec(p1, p);
    if(lg(p2) > 2) pari_err_BUG("Prime p is split");
    p2 = gel(p2, 1);
    if (cmpis(gel(p2, 3), e)) pari_err_BUG("Ramification index is incorrect");
    if (cmpis(gel(p2, 4), f)) pari_err_BUG("inertia degree is incorrect");
  }

  if (l == 2) return;
  if (e*f > 20) return;

  /* TODO: check that (random) distinct polynomials give non-isomorphic extensions */
  for (i = 1; i < 3*l; i++)
  {
    c1 = random_Fl(l-1)+1;
    c2 = random_Fl(l-1)+1;
    if (c1 == c2) continue;
    p1 = gel(pols, c1);
    if (typ(p1) == t_VEC) p1 = gel(p1, 1);
    p2 = gel(pols, c2);
    if (typ(p2) == t_VEC) p2 = gel(p2, 1);
    pol = polcompositum0(p1, p2, 0);
    pol = gel(pol, 1);
    if (poldegree(pol, -1) > 100) continue;
    p1 = factorpadic(pol, p, 2);
    p1 = gmael(p1, 1, 1);
    if (poldegree(p1, -1) == e*f) pari_err_BUG("fields are isomorphic");
    /*
      p1 = nfinitall(mkvec2(pol, mkvec(p)), 0, DEFAULTPREC);
      p2 = idealprimedec_galois(p1, p);
      if (!cmpis(mulii(gel(p2, 3), gel(p2, 4)), e*f)) pari_err_BUG("fields are isomorphic");
    */
  }
}
#endif

static GEN
pols_from_efj(pari_sp av, GEN EFJ, GEN p, long flag)
{
  long i, l;
  GEN L = cgetg_copy(EFJ, &l);
  if (l == 1) { avma = av; return flag == 2? gen_0: cgetg(1, t_VEC); }
  for (i = 1; i < l; i++)
  {
    gel(L,i) = GetRamifiedPol(p, gel(EFJ,i), flag);
#ifdef CHECK
    checkpols(p, gel(EFJ, i), gel(L, i));
#endif
  }
  if (flag == 2) return gerepileuptoint(av, ZV_sum(L));
  return gerepilecopy(av, shallowconcat1(L));
}

/* return a minimal list of polynomials generating all the extensions of
   Q_p of given degree N; if N is a t_VEC [n,d], return extensions of degree n
   and discriminant p^d. */
/* Return only the polynomials if flag = 0 (default), also the ramification
   degree, the residual degree and the discriminant if flag = 1 and only the
   number of extensions if flag = 2 */
GEN
padicfields0(GEN p, GEN N, long flag)
{
  pari_sp av = avma;
  long m = 0, d = -1;
  GEN L;

  if (typ(p) != t_INT) pari_err_TYPE("padicfields",p);
  /* be nice to silly users */
  if (!BPSW_psp(p)) pari_err_PRIME("padicfields",p);
  switch(typ(N))
  {
    case t_VEC:
      if (lg(N) != 3) pari_err_TYPE("padicfields",N);
      d = gtos(gel(N,2));
      N = gel(N,1); /* fall through */
    case t_INT:
      m = itos(N);
      if (m <= 0) pari_err_DOMAIN("padicfields", "degree", "<=", gen_0,N);
      break;
    default:
      pari_err_TYPE("padicfields",N);
  }
  if (d >= 0) return padicfields(p, m, d, flag);
  L = possible_efj(p, m);
  return pols_from_efj(av, L, p, flag);
}

GEN
padicfields(GEN p, long m, long d, long flag)
{
  long av = avma;
  GEN L = possible_efj_by_d(p, m, d);
  return pols_from_efj(av, L, p, flag);
}
