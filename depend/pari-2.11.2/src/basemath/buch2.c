/* Copyright (C) 2000  The PARI group.

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
/*         CLASS GROUP AND REGULATOR (McCURLEY, BUCHMANN)          */
/*                    GENERAL NUMBER FIELDS                        */
/*                                                                 */
/*******************************************************************/
/* get_random_ideal */
static const long RANDOM_BITS = 4;
/* Buchall */
static const double BNF_C1 = 0.0, BNF_C2 = 0.0;
static const long RELSUP = 5;
static const long FAIL_DIVISOR = 32;
static const long MINFAIL = 10;
/* small_norm */
static const long BNF_RELPID = 4;
static const long BMULT = 8;
static const long maxtry_ELEMENT = 1000*1000;
static const long maxtry_DEP = 20;
static const long maxtry_FACT = 500;
/* rnd_rel */
static const long RND_REL_RELPID = 1;
static const long PREVENT_LLL_IN_RND_REL = 1;
/* random relations */
static const long MINSFB = 3;
static const long SFB_MAX = 3;
static const long DEPSIZESFBMULT = 16;
static const long DEPSFBDIV = 10;
/* add_rel_i */
static const ulong mod_p = 27449UL;
/* be_honest */
static const long maxtry_HONEST = 50;

typedef struct FACT {
    long pr, ex;
} FACT;

typedef struct subFB_t {
  GEN subFB;
  struct subFB_t *old;
} subFB_t;

/* a factor base contains only non-inert primes
 * KC = # of P in factor base (p <= n, NP <= n2)
 * KC2= # of P assumed to generate class group (NP <= n2)
 *
 * KCZ = # of rational primes under ideals counted by KC
 * KCZ2= same for KC2 */

typedef struct FB_t {
  GEN FB; /* FB[i] = i-th rational prime used in factor base */
  GEN LP; /* vector of all prime ideals in FB */
  GEN *LV; /* LV[p] = vector of P|p, NP <= n2
            * isclone() is set for LV[p] iff all P|p are in FB
            * LV[i], i not prime or i > n2, is undefined! */
  GEN iLP; /* iLP[p] = i such that LV[p] = [LP[i],...] */
  GEN id2; /* id2[i] = powers of ideal i */
  GEN L_jid; /* indexes of "useful" prime ideals for rnd_rel */
  long KC, KCZ, KCZ2;
  GEN subFB; /* LP o subFB =  part of FB used to build random relations */
  int sfb_chg; /* need to change subFB ? */
  int newpow; /* need to compute powFB */
  GEN perm; /* permutation of LP used to represent relations [updated by
               hnfspec/hnfadd: dense rows come first] */
  GEN vecG, G0;
  GEN idealperm; /* permutation of ideals under field automorphisms */
  GEN minidx; /* minidx[i] min ideal in orbit of LP[i] under field autom */
  subFB_t *allsubFB; /* all subFB's used */
  GEN embperm; /* permutations of the complex embeddings */
  GEN invs; /* inverse of automorphism */
} FB_t;

enum { sfb_CHANGE = 1, sfb_INCREASE = 2 };

typedef struct REL_t {
  GEN R; /* relation vector as t_VECSMALL; clone */
  long nz; /* index of first non-zero elt in R (hash) */
  GEN m; /* pseudo-minimum yielding the relation; clone */
  long relorig; /* relation this one is an image of */
  long relaut; /* automorphim used to compute this relation from the original */
  GEN junk[3]; /*make sure sizeof(struct) is a power of two.*/
} REL_t;

typedef struct RELCACHE_t {
  REL_t *chk; /* last checkpoint */
  REL_t *base; /* first rel found */
  REL_t *last; /* last rel found so far */
  REL_t *end; /* target for last relation. base <= last <= end */
  size_t len; /* number of rels pre-allocated in base */
  long relsup; /* how many linearly dependent relations we allow */
  GEN basis; /* mod p basis (generating family actually) */
  ulong missing; /* missing vectors in generating family above */
} RELCACHE_t;

typedef struct FP_t {
  double **q;
  GEN x;
  double *y;
  double *z;
  double *v;
} FP_t;

typedef struct RNDREL_t {
  GEN Nideal;
  long jid;
  GEN ex;
  GEN m1;
} RNDREL_t;

static void
wr_rel(GEN col)
{
  long i, l = lg(col);
  err_printf("\nrel = ");
  for (i=1; i<l; i++)
    if (col[i]) err_printf("%ld^%ld ",i,col[i]);
  err_printf("\n");
}
static void
dbg_newrel(RELCACHE_t *cache)
{
  if (DEBUGLEVEL > 1)
  {
    err_printf("\n++++ cglob = %ld", cache->last - cache->base);
    wr_rel(cache->last->R);
  }
  else
    err_printf("%ld ", cache->last - cache->base);
}

static void
dbg_cancelrel(long jid, long jdir, GEN col)
{
  err_printf("relation cancelled: ");
  if (DEBUGLEVEL>3) err_printf("(jid=%ld,jdir=%ld)",jid,jdir);
  wr_rel(col); err_flush();
}


static void
delete_cache(RELCACHE_t *M)
{
  REL_t *rel;
  for (rel = M->base+1; rel <= M->last; rel++)
  {
    gunclone(rel->R);
    if (!rel->m) continue;
    gunclone(rel->m);
  }
  pari_free((void*)M->base); M->base = NULL;
}

static void
unclone_subFB(FB_t *F)
{
  subFB_t *sub, *subold;
  GEN id2 = F->id2;
  long i;

  for (sub = F->allsubFB; sub; sub = subold)
  {
    GEN subFB = sub->subFB;
    for (i = 1; i < lg(subFB); i++)
    {
      long id = subFB[i];
      if (gel(id2, id) == gen_0) continue;

      gunclone(gel(id2, id));
      gel(id2, id) = gen_0;
    }
    subold = sub->old;
    pari_free(sub);
  }
}

static void
delete_FB(FB_t *F)
{
  unclone_subFB(F);
  gunclone(F->minidx);
  gunclone(F->idealperm);
}

static void
reallocate(RELCACHE_t *M, long len)
{
  REL_t *old = M->base;
  M->len = len;
  M->base = (REL_t*)pari_realloc((void*)old, (len+1) * sizeof(REL_t));
  if (old)
  {
    size_t last = M->last - old, chk = M->chk - old, end = M->end - old;
    M->last = M->base + last;
    M->chk  = M->base + chk;
    M->end  = M->base + end;
  }
}

#define pr_get_smallp(pr) gel(pr,1)[2]

/* don't take P|p all other Q|p are already there */
static int
bad_subFB(FB_t *F, long t)
{
  GEN LP, P = gel(F->LP,t);
  long p = pr_get_smallp(P);
  LP = F->LV[p];
  return (isclone(LP) && t == F->iLP[p] + lg(LP)-1);
}

static void
assign_subFB(FB_t *F, GEN yes, long iyes)
{
  subFB_t *sub;
  long i, lv;

  /* single malloc for struct + GEN */
  lv = sizeof(subFB_t) + iyes*sizeof(long);
  sub = (subFB_t *)pari_malloc(lv);
  sub->subFB = (GEN)&sub[1];
  sub->old = F->allsubFB;
  F->allsubFB = sub;
  for (i = 0; i < iyes; i++) sub->subFB[i] = yes[i];
  F->subFB = sub->subFB;
  F->newpow = 1;
}

/*
 * Determine the permutation of the ideals made by each field automorphism.
 */
static void
FB_aut_perm(FB_t *F, GEN auts, GEN cyclic)
{
  pari_sp av0 = avma;
  long i, KC = F->KC, nauts = lg(auts);
  GEN minidx = zero_Flv(KC), perm = zero_Flm_copy(KC, nauts-1);

  if (nauts == 1)
  {
    for (i = 1; i <= KC; i++) minidx[i] = i;
  }
  else
  {
    long j, m;
    for (m = 1; m < lg(cyclic); m++)
    {
      GEN thiscyc = gel(cyclic, m);
      long k0 = thiscyc[1];
      GEN aut = gel(auts, k0), permk0 = gel(perm, k0), ppermk;
      i = 1;
      while (i <= KC)
      {
        pari_sp av2 = avma;
        GEN seen = zero_Flv(KC), P = gel(F->LP, i);
        long imin = i, p, f, l;
        p = pr_get_p(P)[2];
        f = pr_get_f(P);
        do
        {
          if (++i > KC) break;
          P = gel(F->LP, i);
        }
        while (p == pr_get_p(P)[2] && f == pr_get_f(P));
        for (j = imin; j < i; j++)
        {
          GEN img = ZM_ZC_mul(aut, pr_get_gen(gel(F->LP, j)));
          for (l = imin; l < i; l++)
            if (!seen[l] && ZC_prdvd(img, gel(F->LP, l)))
            {
              seen[l] = 1; permk0[j] = l; break;
            }
        }
        avma = av2;
      }
      for (ppermk = permk0, i = 2; i < lg(thiscyc); i++)
      {
        GEN permk = gel(perm, thiscyc[i]);
        for (j = 1; j <= KC; j++) permk[j] = permk0[ppermk[j]];
        ppermk = permk;
      }
    }
    for (j = 1; j <= KC; j++)
    {
      if (minidx[j]) continue;
      minidx[j] = j;
      for (i = 1; i < nauts; i++) minidx[coeff(perm, j, i)] = j;
    }
  }
  F->minidx = gclone(minidx);
  F->idealperm = gclone(perm);
  avma = av0;
}

/* set subFB.
 * Fill F->perm (if != NULL): primes ideals sorted by increasing norm (except
 * the ones in subFB come first [dense rows for hnfspec]) */
static int
subFBgen(FB_t *F, GEN auts, GEN cyclic, double PROD, long minsFB)
{
  GEN y, perm, yes, no;
  long i, j, k, iyes, ino, lv = F->KC + 1;
  double prod;
  pari_sp av;

  F->LP   = cgetg(lv, t_VEC);
  F->L_jid = F->perm = cgetg(lv, t_VECSMALL);
  av = avma;
  y = cgetg(lv,t_COL); /* Norm P */
  for (k=0, i=1; i <= F->KCZ; i++)
  {
    GEN LP = F->LV[F->FB[i]];
    long l = lg(LP);
    for (j = 1; j < l; j++)
    {
      GEN P = gel(LP,j);
      k++;
      gel(y,k) = pr_norm(P);
      gel(F->LP,k) = P;
    }
  }
  /* perm sorts LP by increasing norm */
  perm = indexsort(y);
  no  = cgetg(lv, t_VECSMALL); ino  = 1;
  yes = cgetg(lv, t_VECSMALL); iyes = 1;
  prod = 1.0;
  for (i = 1; i < lv; i++)
  {
    long t = perm[i];
    if (bad_subFB(F, t)) { no[ino++] = t; continue; }

    yes[iyes++] = t;
    prod *= (double)itos(gel(y,t));
    if (iyes > minsFB && prod > PROD) break;
  }
  setlg(yes, iyes);
  for (j=1; j<iyes; j++)     F->perm[j] = yes[j];
  for (i=1; i<ino; i++, j++) F->perm[j] =  no[i];
  for (   ; j<lv; j++)       F->perm[j] =  perm[j];
  F->allsubFB = NULL;
  FB_aut_perm(F, auts, cyclic);
  if (iyes) assign_subFB(F, yes, iyes);
  avma = av; return 1;
}
static int
subFB_change(FB_t *F)
{
  long i, iyes, minsFB, lv = F->KC + 1, l = lg(F->subFB)-1;
  pari_sp av = avma;
  GEN yes, L_jid = F->L_jid, present = zero_zv(lv-1);

  switch (F->sfb_chg)
  {
    case sfb_INCREASE: minsFB = l + 1; break;
    default: minsFB = l; break;
  }

  yes = cgetg(minsFB+1, t_VECSMALL); iyes = 1;
  if (L_jid)
  {
    for (i = 1; i < lg(L_jid); i++)
    {
      long l = L_jid[i];
      yes[iyes++] = l;
      present[l] = 1;
      if (iyes > minsFB) break;
    }
  }
  else i = 1;
  if (iyes <= minsFB)
  {
    for ( ; i < lv; i++)
    {
      long l = F->perm[i];
      if (present[l]) continue;
      yes[iyes++] = l;
      if (iyes > minsFB) break;
    }
    if (i == lv) return 0;
  }
  if (zv_equal(F->subFB, yes))
  {
    if (DEBUGLEVEL) err_printf("\n*** NOT Changing sub factor base\n");
  }
  else
  {
    if (DEBUGLEVEL) err_printf("\n*** Changing sub factor base\n");
    assign_subFB(F, yes, iyes);
  }
  F->sfb_chg = 0;
  avma = av; return 1;
}

static GEN
init_famat(GEN x) { return mkvec2(x, trivial_fact()); }

static GEN
red(GEN nf, GEN I, GEN G0, GEN *pm)
{
  GEN y = idealred0(nf, init_famat(I), G0), J = gel(y,1);
  if (is_pm1(gcoeff(J,1,1)) ||
      cmpii(ZM_det_triangular(I),
            ZM_det_triangular(J)) < 0) { *pm = gen_1; J = I; }
  else
  {
    GEN m = gel(y,2);
    *pm = lgcols(m)==1? gen_1: Q_primpart(gmael(m,1,1));
  }
  return J;
}

/* make sure enough room to store n more relations */
static void
pre_allocate(RELCACHE_t *cache, size_t n)
{
  size_t len = (cache->last - cache->base) + n;
  if (len >= cache->len) reallocate(cache, len << 1);
}

void
init_GRHcheck(GRHcheck_t *S, long N, long R1, double LOGD)
{
  const double c1 = M_PI*M_PI/2;
  const double c2 = 3.663862376709;
  const double c3 = 3.801387092431; /* Euler + log(8*Pi)*/
  S->clone = 0;
  S->cN = R1*c2 + N*c1;
  S->cD = LOGD - N*c3 - R1*M_PI/2;
  S->maxprimes = 16000; /* sufficient for LIMC=176081*/
  S->primes = (GRHprime_t*)pari_malloc(S->maxprimes*sizeof(*S->primes));
  S->nprimes = 0;
  S->limp = 0;
  u_forprime_init(&S->P, 2, ULONG_MAX);
}

void
free_GRHcheck(GRHcheck_t *S)
{
  if (S->clone)
  {
    long i = S->nprimes;
    GRHprime_t *pr;
    for (pr = S->primes, i = S->nprimes; i > 0; pr++, i--) gunclone(pr->dec);
  }
  pari_free(S->primes);
}

int
GRHok(GRHcheck_t *S, double L, double SA, double SB)
{
  return (S->cD + (S->cN + 2*SB) / L - 2*SA < -1e-8);
}

/* Return factorization pattern of p: [f,n], where n[i] primes of
 * residue degree f[i] */
static GEN
get_fs(GEN nf, GEN P, GEN index, ulong p)
{
  long j, k, f, n, l;
  GEN fs, ns;

  if (umodiu(index, p))
  { /* easy case: p does not divide index */
    GEN F = Flx_degfact(ZX_to_Flx(P,p), p);
    fs = gel(F,1); l = lg(fs);
  }
  else
  {
    GEN F = idealprimedec(nf, utoipos(p));
    l = lg(F);
    fs = cgetg(l, t_VECSMALL);
    for (j = 1; j < l; j++) fs[j] = pr_get_f(gel(F,j));
  }
  ns = cgetg(l, t_VECSMALL);
  f = fs[1]; n = 1;
  for (j = 2, k = 1; j < l; j++)
    if (fs[j] == f)
      n++;
    else
    {
      ns[k] = n; fs[k] = f; k++;
      f = fs[j]; n = 1;
    }
  ns[k] = n; fs[k] = f; k++;
  setlg(fs, k);
  setlg(ns, k); return mkvec2(fs,ns);
}

/* cache data for all rational primes up to the LIM */
static void
cache_prime_dec(GRHcheck_t *S, ulong LIM, GEN nf)
{
  pari_sp av = avma;
  GRHprime_t *pr;
  GEN index, P;
  double nb;

  if (S->limp >= LIM) return;
  S->clone = 1;
  nb = primepi_upper_bound((double)LIM); /* #{p <= LIM} <= nb */
  GRH_ensure(S, nb+1); /* room for one extra prime */
  P = nf_get_pol(nf);
  index = nf_get_index(nf);
  for (pr = S->primes + S->nprimes;;)
  {
    ulong p = u_forprime_next(&(S->P));
    pr->p = p;
    pr->logp = log((double)p);
    pr->dec = gclone(get_fs(nf, P, index, p));
    S->nprimes++;
    pr++;
    avma = av;
    /* store up to nextprime(LIM) included */
    if (p >= LIM) { S->limp = p; break; }
  }
}

static double
tailresback(long R1, long R2, double rK, long C, double C2, double C3, double r1K, double r2K, double logC, double logC2, double logC3)
{
  const double  rQ = 1.83787706641;
  const double r1Q = 1.98505372441;
  const double r2Q = 1.07991541347;
  return fabs((R1+R2-1)*(12*logC3+4*logC2-9*logC-6)/(2*C*logC3)
         + (rK-rQ)*(6*logC2 + 5*logC + 2)/(C*logC3)
         - R2*(6*logC2+11*logC+6)/(C2*logC2)
         - 2*(r1K-r1Q)*(3*logC2 + 4*logC + 2)/(C2*logC3)
         + (R1+R2-1)*(12*logC3+40*logC2+45*logC+18)/(6*C3*logC3)
         + (r2K-r2Q)*(2*logC2 + 3*logC + 2)/(C3*logC3));
}

static double
tailres(long R1, long R2, double al2K, double rKm, double rKM, double r1Km,
        double r1KM, double r2Km, double r2KM, double C, long i)
{
  /* C >= 3*2^i, lower bound for eint1(log(C)/2) */
  /* for(i=0,30,print(eint1(log(3*2^i)/2))) */
  static double tab[] = {
    0.50409264803,
    0.26205336997,
    0.14815491171,
    0.08770540561,
    0.05347651832,
    0.03328934284,
    0.02104510690,
    0.01346475900,
    0.00869778586,
    0.00566279855,
    0.00371111950,
    0.00244567837,
    0.00161948049,
    0.00107686891,
    0.00071868750,
    0.00048119961,
    0.00032312188,
    0.00021753772,
    0.00014679818,
    9.9272855581E-5,
    6.7263969995E-5,
    4.5656812967E-5,
    3.1041124593E-5,
    2.1136011590E-5,
    1.4411645381E-5,
    9.8393304088E-6,
    6.7257395409E-6,
    4.6025878272E-6,
    3.1529719271E-6,
    2.1620490021E-6,
    1.4839266071E-6
  };
  const double logC = log(C), logC2 = logC*logC, logC3 = logC*logC2;
  const double C2 = C*C, C3 = C*C2;
  double E1 = i >30? 0: tab[i];
  return al2K*((33*logC2+22*logC+8)/(8*logC3*sqrt(C))+15*E1/16)
    + maxdd(tailresback(rKm,r1KM,r2Km, C,C2,C3,R1,R2,logC,logC2,logC3),
            tailresback(rKM,r1Km,r2KM, C,C2,C3,R1,R2,logC,logC2,logC3))/2
    + ((R1+R2-1)*4*C+R2)*(C2+6*logC)/(4*C2*C2*logC2);
}

static long
primeneeded(long N, long R1, long R2, double LOGD)
{
  const double lim = 0.25; /* should be log(2)/2 == 0.34657... */
  const double al2K =  0.3526*LOGD - 0.8212*N + 4.5007;
  const double  rKm = -1.0155*LOGD + 2.1042*N - 8.3419;
  const double  rKM = -0.5   *LOGD + 1.2076*N + 1;
  const double r1Km = -       LOGD + 1.4150*N;
  const double r1KM = -       LOGD + 1.9851*N;
  const double r2Km = -       LOGD + 0.9151*N;
  const double r2KM = -       LOGD + 1.0800*N;
  long Cmin = 3, Cmax = 3, i = 0;
  while (tailres(R1, R2, al2K, rKm, rKM, r1Km, r1KM, r2Km, r2KM, Cmax, i) > lim)
  {
    Cmin = Cmax;
    Cmax *= 2;
    i++;
  }
  i--;
  while (Cmax - Cmin > 1)
  {
    long t = (Cmin + Cmax)/2;
    if (tailres(R1, R2, al2K, rKm, rKM, r1Km, r1KM, r2Km, r2KM, t, i) > lim)
      Cmin = t;
    else
      Cmax = t;
  }
  return Cmax;
}

/*
  for (; i > 0; pr++, i--)
  {
    GEN dec, a = NULL, b = NULL, fs, ns;
    long j, k, limp = (long)(llimc/pr->logp);
    ulong p = pr->p;
    dec = pr->dec;
    fs = gel(dec, 1); ns = gel(dec, 2);
    k = lg(fs);
    for (j = 1; j < k; j++)
    {
      long f, nb;
      GEN nor;
      f = fs[j]; if (f > limp) continue;
      nb = ns[j];
      nor = powuu(p, f);
      if (a)
      {
        a = mulii(a, powiu(nor, nb));
        b = mulii(b, powiu(subii(nor, gen_1), nb));
      }
      else
      {
        a = powuu(p, f*nb-1);
        b = diviuexact(powiu(subii(nor, gen_1), nb), p-1);
      }
    }
    if (a)
      invres = divri(mulir(b, invres), a);
    else
      invres = divru(mulur(p, invres), p-1);
  }
*/

static GEN
compute_invres(GRHcheck_t *S, long LIMC)
{
  pari_sp av = avma;
  double loginvres = 0.;
  GRHprime_t *pr;
  long i;
  double logLIMC = log((double)LIMC);
  double logLIMC2 = logLIMC*logLIMC, denc;
  double c0, c1, c2;
  denc = 1/(pow((double)LIMC, 3.) * logLIMC * logLIMC2);
  c2 = (    logLIMC2 + 3 * logLIMC / 2 + 1) * denc;
  denc *= LIMC;
  c1 = (3 * logLIMC2 + 4 * logLIMC     + 2) * denc;
  denc *= LIMC;
  c0 = (3 * logLIMC2 + 5 * logLIMC / 2 + 1) * denc;
  for (pr = S->primes, i = S->nprimes; i > 0; pr++, i--)
  {
    GEN dec, fs, ns;
    long addpsi;
    double addpsi1, addpsi2;
    double logp = pr->logp, NPk;
    long j, k, limp = logLIMC/logp;
    ulong p = pr->p, p2 = p*p;
    if (limp < 1) break;
    dec = pr->dec;
    fs = gel(dec, 1); ns = gel(dec, 2);
    loginvres += 1./p;
    /*
     * note for optimization: limp == 1 nearly always and limp >= 3 for
     * only very few primes.
     */
    for (k = 2, NPk = p; k <= limp; k++)
    {
      NPk *= p;
      loginvres += 1/(k * NPk);
    }
    addpsi = limp;
    addpsi1 = p *(pow((double)p , (double)limp)-1)/(p -1);
    addpsi2 = p2*(pow((double)p2, (double)limp)-1)/(p2-1);
    j = lg(fs);
    while (--j > 0)
    {
      long f, nb, kmax;
      double NP, NP2, addinvres;
      f = fs[j]; if (f > limp) continue;
      nb = ns[j];
      NP = pow((double)p, (double)f);
      addinvres = 1/NP;
      kmax = limp / f;
      for (k = 2, NPk = NP; k <= kmax; k++)
      {
        NPk *= NP;
        addinvres += 1/(k*NPk);
      }
      NP2 = NP*NP;
      loginvres -= nb * addinvres;
      addpsi -= nb * f * kmax;
      addpsi1 -= nb*(f*NP *(pow(NP ,(double)kmax)-1)/(NP -1));
      addpsi2 -= nb*(f*NP2*(pow(NP2,(double)kmax)-1)/(NP2-1));
    }
    loginvres -= (addpsi*c0 - addpsi1*c1 + addpsi2*c2)*logp;
  }
  return gerepileuptoleaf(av, mpexp(dbltor(loginvres)));
}

static long
nthideal(GRHcheck_t *S, GEN nf, long n)
{
  pari_sp av = avma;
  GEN P = nf_get_pol(nf);
  ulong p = 0, *vecN = (ulong*)const_vecsmall(n, LONG_MAX);
  long i, res, N = poldegree(P, -1);
  for (i = 0; ; i++)
  {
    GRHprime_t *pr;
    GEN fs;
    cache_prime_dec(S, p+1, nf);
    pr = S->primes + i;
    fs = gel(pr->dec, 1);
    p = pr->p;
    if (fs[1] != N)
    {
      GEN ns = gel(pr->dec, 2);
      long k, l, j = lg(fs);
      while (--j > 0)
      {
        ulong NP = upowuu(p, fs[j]);
        long nf;
        if (!NP) continue;
        for (k = 1; k <= n; k++) if (vecN[k] > NP) break;
        if (k > n) continue;
        /* vecN[k] <= NP */
        nf = ns[j]; /*#{primes of norme NP} = nf, insert them here*/
        for (l = k+nf; l <= n; l++) vecN[l] = vecN[l-nf];
        for (l = 0; l < nf && k+l <= n; l++) vecN[k+l] = NP;
        while (l <= k) vecN[l++] = NP;
      }
    }
    if (p > vecN[n]) break;
  }
  res = vecN[n]; avma = av; return res;
}


/* Compute FB, LV, iLP + KC*. Reset perm
 * C2: bound for norm of tested prime ideals (includes be_honest())
 * C1: bound for p, such that P|p (NP <= C2) used to build relations */
static void
FBgen(FB_t *F, GEN nf, long N, ulong C1, ulong C2, GRHcheck_t *S)
{
  GRHprime_t *pr;
  long i, ip;
  GEN prim;
  const double L = log((double)C2 + 0.5);

  cache_prime_dec(S, C2, nf);
  pr = S->primes;
  F->sfb_chg = 0;
  F->FB  = cgetg(C2+1, t_VECSMALL);
  F->iLP = cgetg(C2+1, t_VECSMALL);
  F->LV = (GEN*)const_vec(C2, NULL);

  prim = icopy(gen_1);
  i = ip = 0;
  F->KC = F->KCZ = 0;
  for (;; pr++) /* p <= C2 */
  {
    ulong p = pr->p;
    long k, l, m;
    GEN LP, nb, f;

    if (!F->KC && p > C1) { F->KCZ = i; F->KC = ip; }
    if (p > C2) break;

    if (DEBUGLEVEL>1) { err_printf(" %ld",p); err_flush(); }

    f = gel(pr->dec, 1); nb = gel(pr->dec, 2);
    if (f[1] == N)
    {
      if (p == C2) break;
      continue; /* p inert */
    }/* compute l such that p^f <= C2  <=> f <= l */
    l = (long)(L/pr->logp);
    for (k=0, m=1; m < lg(f) && f[m]<=l; m++) k += nb[m];
    if (!k) /* p too inert to appear in FB */
    {
      if (p == C2) break;
      continue;
    }
    prim[2] = p; LP = idealprimedec_limit_f(nf,prim, l);
    /* keep non-inert ideals with Norm <= C2 */
    if (m == lg(f)) setisclone(LP); /* flag it: all prime divisors in FB */
    F->FB[++i]= p;
    F->LV[p]  = LP;
    F->iLP[p] = ip; ip += k;
    if (p == C2) break;
  }
  if (!F->KC) { F->KCZ = i; F->KC = ip; }
  /* Note F->KC > 0 otherwise GRHchk is false */
  setlg(F->FB, F->KCZ+1); F->KCZ2 = i;
  if (DEBUGLEVEL>1)
  {
    err_printf("\n");
    if (DEBUGLEVEL>6)
    {
      err_printf("########## FACTORBASE ##########\n\n");
      err_printf("KC2=%ld, KC=%ld, KCZ=%ld, KCZ2=%ld\n",
                  ip, F->KC, F->KCZ, F->KCZ2);
      for (i=1; i<=F->KCZ; i++) err_printf("++ LV[%ld] = %Ps",i,F->LV[F->FB[i]]);
    }
  }
  F->perm = NULL; F->L_jid = NULL;
}

static int
GRHchk(GEN nf, GRHcheck_t *S, ulong LIMC)
{
  double logC = log((double)LIMC), SA = 0, SB = 0;
  GRHprime_t *pr = S->primes;

  cache_prime_dec(S, LIMC, nf);
  for (pr = S->primes;; pr++)
  {
    ulong p = pr->p;
    GEN dec, fs, ns;
    double logCslogp;
    long j;

    if (p > LIMC) break;
    dec = pr->dec; fs = gel(dec, 1); ns = gel(dec,2);
    logCslogp = logC/pr->logp;
    for (j = 1; j < lg(fs); j++)
    {
      long f = fs[j], M, nb;
      double logNP, q, A, B;
      if (f > logCslogp) break;
      logNP = f * pr->logp;
      q = 1/sqrt((double)upowuu(p, f));
      A = logNP * q; B = logNP * A; M = (long)(logCslogp/f);
      if (M > 1)
      {
        double inv1_q = 1 / (1-q);
        A *= (1 - pow(q, (double)M)) * inv1_q;
        B *= (1 - pow(q, (double)M)*(M+1 - M*q)) * inv1_q * inv1_q;
      }
      nb = ns[j];
      SA += nb * A;
      SB += nb * B;
    }
    if (p == LIMC) break;
  }
  return GRHok(S, logC, SA, SB);
}

/*  SMOOTH IDEALS */
static void
store(long i, long e, FACT *fact)
{
  ++fact[0].pr;
  fact[fact[0].pr].pr = i; /* index */
  fact[fact[0].pr].ex = e; /* exponent */
}

/* divide out x by all P|p, where x as in can_factor().  k = v_p(Nx) */
static int
divide_p_elt(GEN LP, long ip, long k, GEN m, FACT *fact)
{
  long j, l = lg(LP);
  for (j=1; j<l; j++)
  {
    GEN P = gel(LP,j);
    long v = ZC_nfval(m, P);
    if (!v) continue;
    store(ip + j, v, fact); /* v = v_P(m) > 0 */
    k -= v * pr_get_f(P);
    if (!k) return 1;
  }
  return 0;
}
static int
divide_p_id(GEN LP, long ip, long k, GEN nf, GEN I, FACT *fact)
{
  long j, l = lg(LP);
  for (j=1; j<l; j++)
  {
    GEN P = gel(LP,j);
    long v = idealval(nf,I, P);
    if (!v) continue;
    store(ip + j, v, fact); /* v = v_P(I) > 0 */
    k -= v * pr_get_f(P);
    if (!k) return 1;
  }
  return 0;
}
static int
divide_p_quo(GEN LP, long ip, long k, GEN nf, GEN I, GEN m, FACT *fact)
{
  long j, l = lg(LP);
  for (j=1; j<l; j++)
  {
    GEN P = gel(LP,j);
    long v = ZC_nfval(m, P);
    if (!v) continue;
    v -= idealval(nf,I, P);
    if (!v) continue;
    store(ip + j, v, fact); /* v = v_P(m / I) > 0 */
    k -= v * pr_get_f(P);
    if (!k) return 1;
  }
  return 0;
}

/* |*N| != 0 is the norm of a primitive ideal, in particular not divisible by
 * any inert prime. Is |*N| a smooth rational integer wrt F ? (put the
 * exponents in *ex) */
static int
smooth_norm(FB_t *F, GEN *N, GEN *ex)
{
  GEN FB = F->FB;
  const long KCZ = F->KCZ;
  const ulong limp = uel(FB,KCZ); /* last p in FB */
  long i;

  *ex = new_chunk(KCZ+1);
  for (i=1; ; i++)
  {
    int stop;
    ulong p = uel(FB,i);
    long v = Z_lvalrem_stop(N, p, &stop);
    (*ex)[i] = v;
    if (v)
    {
      GEN LP = F->LV[p];
      if(!LP) pari_err_BUG("can_factor");
      if (lg(LP) == 1) return 0;
      if (stop) break;
    }
    if (i == KCZ) return 0;
  }
  (*ex)[0] = i;
  return (abscmpiu(*N,limp) <= 0);
}

static int
divide_p(FB_t *F, long p, long k, GEN nf, GEN I, GEN m, FACT *fact)
{
  GEN LP = F->LV[p];
  long ip = F->iLP[p];
  if (!m) return divide_p_id (LP,ip,k,nf,I,fact);
  if (!I) return divide_p_elt(LP,ip,k,m,fact);
  return divide_p_quo(LP,ip,k,nf,I,m,fact);
}

/* Let x = m if I == NULL,
 *         I if m == NULL,
 *         m/I otherwise.
 * Can we factor the integral primitive ideal x ? |N| = Norm x > 0 */
static long
can_factor(FB_t *F, GEN nf, GEN I, GEN m, GEN N, FACT *fact)
{
  GEN ex;
  long i, res = 0;
  fact[0].pr = 0;
  if (is_pm1(N)) return 1;
  if (!smooth_norm(F, &N, &ex)) goto END;
  for (i=1; i<=ex[0]; i++)
    if (ex[i] && !divide_p(F, F->FB[i], ex[i], nf, I, m, fact)) goto END;
  res = is_pm1(N) || divide_p(F, itou(N), 1, nf, I, m, fact);
END:
  if (!res && DEBUGLEVEL > 1) { err_printf("."); err_flush(); }
  return res;
}

/* can we factor m/I ? [m in I from idealpseudomin_nonscalar], NI = norm I */
static long
factorgen(FB_t *F, GEN nf, GEN I, GEN NI, GEN m, FACT *fact)
{
  long e, r1 = nf_get_r1(nf);
  GEN M = nf_get_M(nf);
  GEN N = divri(embed_norm(RgM_RgC_mul(M,m), r1), NI); /* ~ N(m/I) */
  N = grndtoi(N, &e);
  if (e > -1)
  {
    if (DEBUGLEVEL > 1) { err_printf("+"); err_flush(); }
    return 0;
  }
  return can_factor(F, nf, I, m, N, fact);
}

/*  FUNDAMENTAL UNITS */

/* a, m real. Return  (Re(x) + a) + I * (Im(x) % m) */
static GEN
addRe_modIm(GEN x, GEN a, GEN m)
{
  GEN re, im, z;
  if (typ(x) == t_COMPLEX)
  {
    im = modRr_safe(gel(x,2), m);
    if (!im) return NULL;
    re = gadd(gel(x,1), a);
    z = gequal0(im)? re: mkcomplex(re, im);
  }
  else
    z = gadd(x, a);
  return z;
}

/* clean archimedean components */
static GEN
cleanarch(GEN x, long N, long prec)
{
  long i, R1, RU, tx = typ(x);
  GEN s, y, pi2;

  if (tx == t_MAT)
  {
    y = cgetg(lg(x), tx);
    for (i=1; i < lg(x); i++) {
      gel(y,i) = cleanarch(gel(x,i), N, prec);
      if (!gel(y,i)) return NULL;
    }
    return y;
  }
  if (!is_vec_t(tx)) pari_err_TYPE("cleanarch",x);
  RU = lg(x)-1; R1 = (RU<<1)-N;
  s = gdivgs(RgV_sum(real_i(x)), -N); /* -log |norm(x)| / N */
  y = cgetg(RU+1,tx);
  pi2 = Pi2n(1, prec);
  for (i=1; i<=R1; i++) {
    gel(y,i) = addRe_modIm(gel(x,i), s, pi2);
    if (!gel(y,i)) return NULL;
  }
  if (i <= RU)
  {
    GEN pi4 = Pi2n(2, prec), s2 = gmul2n(s, 1);
    for (   ; i<=RU; i++) {
      gel(y,i) = addRe_modIm(gel(x,i), s2, pi4);
      if (!gel(y,i)) return NULL;
    }
  }
  return y;
}

static GEN
not_given(long reason)
{
  if (DEBUGLEVEL)
    switch(reason)
    {
      case fupb_LARGE:
        pari_warn(warner,"fundamental units too large, not given");
        break;
      case fupb_PRECI:
        pari_warn(warner,"insufficient precision for fundamental units, not given");
        break;
    }
  return NULL;
}

/* check whether exp(x) will 1) get too big (real(x) large), 2) require
 * large accuracy for argument reduction (imag(x) large) */
static int
exp_OK(GEN x, long *pte)
{
  long i,I,j,J, e = - (long)HIGHEXPOBIT;
  RgM_dimensions(x, &I,&J);
  for (j=1; j<=J; j++)
    for (i=1; i<=I; i++)
    {
      GEN c = gcoeff(x,i,j), re;
      if (typ(c)!=t_COMPLEX) re = c;
      else
      {
        GEN im = gel(c,2);
        e = maxss(e, expo(im) + 5 - bit_prec(im));
        re = gel(c,1);
      }
      if (expo(re) > 20) { *pte = LONG_MAX; return 0; }
    }
  *pte = -e; return (e < 0);
}

static GEN
log_m1(long r1, long ru, long prec)
{
  GEN v = cgetg(ru+1,t_COL);
  GEN a = r1? PiI2n(0,prec): NULL;
  GEN a2 = (r1 != ru)? PiI2n(1,prec): NULL;
  long i;
  for (i=1; i<=r1; i++) gel(v,i) = a;
  for (   ; i<=ru; i++) gel(v,i) = a2;
  return v;
}
static GEN
getfu(GEN nf, GEN *ptA, long *pte, long prec)
{
  GEN u, y, matep, A, vec, T = nf_get_pol(nf), M = nf_get_M(nf);
  long e, i, j, R1, RU, N = degpol(T);

  if (DEBUGLEVEL) err_printf("\n#### Computing fundamental units\n");
  R1 = nf_get_r1(nf); RU = (N+R1)>>1;
  if (RU==1) { *pte=LONG_MAX; return cgetg(1,t_VEC); }

  *pte = 0; A = *ptA;
  if (lg(A) < RU) return not_given(fupb_PRECI);
  matep = cgetg(RU,t_MAT);
  for (j=1; j<RU; j++)
  {
    GEN c = cgetg(RU+1,t_COL), Aj = gel(A,j);
    GEN s = gdivgs(RgV_sum(real_i(Aj)), -N); /* -log |norm(Aj)| / N */
    gel(matep,j) = c;
    for (i=1; i<=R1; i++) gel(c,i) = gadd(s, gel(Aj,i));
    for (   ; i<=RU; i++) gel(c,i) = gadd(s, gmul2n(gel(Aj,i),-1));
  }
  u = lll(real_i(matep));
  if (lg(u) < RU) return not_given(fupb_PRECI);

  y = RgM_mul(matep,u);
  if (!exp_OK(y, pte))
    return not_given(*pte == LONG_MAX? fupb_LARGE: fupb_PRECI);
  if (prec <= 0) prec = gprecision(A);
  y = RgM_solve_realimag(M, gexp(y,prec));
  if (!y) return not_given(fupb_PRECI);
  y = grndtoi(y, &e);
  *pte = -e;
  if (e >= 0) return not_given(fupb_PRECI);
  for (j=1; j<RU; j++)
    if (!is_pm1(nfnorm(nf, gel(y,j)))) { *pte=0; return not_given(fupb_PRECI); }
  A = RgM_mul(A,u);
  settyp(y, t_VEC);
  /* y[i] are unit generators. Normalize: smallest T2 norm + lead coeff > 0 */
  vec = log_m1(R1,RU,prec);
  for (j=1; j<RU; j++)
  {
    GEN u = gel(y,j), v = zk_inv(nf, u);
    if (gcmp(RgC_fpnorml2(v,DEFAULTPREC),
             RgC_fpnorml2(u,DEFAULTPREC)) < 0)
    {
      gel(A,j) = RgC_neg(gel(A,j));
      u = v;
    }
    u = nf_to_scalar_or_alg(nf,u);
    if (gsigne(leading_coeff(u)) < 0)
    {
      gel(A,j) = RgC_add(gel(A,j), vec);
      u = RgX_neg(u);
    }
    gel(y,j) = u;
  }
  *ptA = A; return y;
}

static GEN
makeunits(GEN BNF)
{
  GEN bnf = checkbnf(BNF), fu = bnf_get_fu_nocheck(bnf), v;
  GEN nf = bnf_get_nf(bnf);
  long i, l;
  if (typ(fu) == t_MAT)
  {
    pari_sp av = avma;
    GEN A = bnf_get_logfu(bnf);
    fu = getfu(nf, &A, &l, 0);
    if (!fu)
      pari_err_PREC("makeunits [cannot compute units, use bnfinit(,1)]");
    fu = gerepilecopy(av, fu);
  }
  l = lg(fu) + 1; v = cgetg(l, t_VEC);
  gel(v,1) = nf_to_scalar_or_basis(nf,bnf_get_tuU(bnf));
  for (i = 2; i < l; i++) gel(v,i) = algtobasis(nf, gel(fu,i-1));
  return v;
}

/*******************************************************************/
/*                                                                 */
/*           PRINCIPAL IDEAL ALGORITHM (DISCRETE LOG)              */
/*                                                                 */
/*******************************************************************/

/* G: prime ideals, E: vector of non-negative exponents.
 * C = possible extra prime (^1) or NULL
 * Return Norm (product) */
static GEN
get_norm_fact_primes(GEN G, GEN E, GEN C)
{
  pari_sp av=avma;
  GEN N = gen_1, P, p;
  long i, c = lg(E);
  for (i=1; i<c; i++)
  {
    GEN ex = gel(E,i);
    long s = signe(ex);
    if (!s) continue;

    P = gel(G,i); p = pr_get_p(P);
    N = mulii(N, powii(p, mului(pr_get_f(P), ex)));
  }
  if (C) N = mulii(N, pr_norm(C));
  return gerepileuptoint(av, N);
}

/* gen: HNF ideals */
static GEN
get_norm_fact(GEN gen, GEN ex, GEN *pd)
{
  long i, c = lg(ex);
  GEN d,N,I,e,n,ne,de;
  d = N = gen_1;
  for (i=1; i<c; i++)
    if (signe(gel(ex,i)))
    {
      I = gel(gen,i); e = gel(ex,i); n = ZM_det_triangular(I);
      ne = powii(n,e);
      de = equalii(n, gcoeff(I,1,1))? ne: powii(gcoeff(I,1,1), e);
      N = mulii(N, ne);
      d = mulii(d, de);
    }
  *pd = d; return N;
}

static GEN
get_pr_lists(GEN FB, long N, int list_pr)
{
  GEN pr, L;
  long i, l = lg(FB), p, pmax;

  pmax = 0;
  for (i=1; i<l; i++)
  {
    pr = gel(FB,i); p = pr_get_smallp(pr);
    if (p > pmax) pmax = p;
  }
  L = const_vec(pmax, NULL);
  if (list_pr)
  {
    for (i=1; i<l; i++)
    {
      pr = gel(FB,i); p = pr_get_smallp(pr);
      if (!L[p]) gel(L,p) = vectrunc_init(N+1);
      vectrunc_append(gel(L,p), pr);
    }
    for (p=1; p<=pmax; p++)
      if (L[p]) gen_sort_inplace(gel(L,p), (void*)&cmp_prime_over_p,
                                 &cmp_nodata, NULL);
  }
  else
  {
    for (i=1; i<l; i++)
    {
      pr = gel(FB,i); p = pr_get_smallp(pr);
      if (!L[p]) gel(L,p) = vecsmalltrunc_init(N+1);
      vecsmalltrunc_append(gel(L,p), i);
    }
  }
  return L;
}

/* recover FB, LV, iLP, KCZ from Vbase */
static GEN
recover_partFB(FB_t *F, GEN Vbase, long N)
{
  GEN FB, LV, iLP, L = get_pr_lists(Vbase, N, 0);
  long l = lg(L), p, ip, i;

  i = ip = 0;
  FB = cgetg(l, t_VECSMALL);
  iLP= cgetg(l, t_VECSMALL);
  LV = cgetg(l, t_VEC);
  for (p = 2; p < l; p++)
  {
    if (!L[p]) continue;
    FB[++i] = p;
    gel(LV,p) = vecpermute(Vbase, gel(L,p));
    iLP[p]= ip; ip += lg(gel(L,p))-1;
  }
  F->KCZ = i;
  F->KC = ip;
  F->FB = FB; setlg(FB, i+1);
  F->LV = (GEN*)LV;
  F->iLP= iLP; return L;
}

/* add v^e to factorization */
static void
add_to_fact(long v, long e, FACT *fact)
{
  long i, l = fact[0].pr;
  for (i=1; i<=l && fact[i].pr < v; i++)/*empty*/;
  if (i <= l && fact[i].pr == v) fact[i].ex += e; else store(v, e, fact);
}
static void
inv_fact(FACT *fact)
{
  long i, l = fact[0].pr;
  for (i=1; i<=l; i++) fact[i].ex = -fact[i].ex;
}

/* L (small) list of primes above the same p including pr. Return pr index */
static int
pr_index(GEN L, GEN pr)
{
  long j, l = lg(L);
  GEN al = pr_get_gen(pr);
  for (j=1; j<l; j++)
    if (ZV_equal(al, pr_get_gen(gel(L,j)))) return j;
  pari_err_BUG("codeprime");
  return 0; /* LCOV_EXCL_LINE */
}

static long
Vbase_to_FB(FB_t *F, GEN pr)
{
  long p = pr_get_smallp(pr);
  return F->iLP[p] + pr_index(F->LV[p], pr);
}

/* x, y 2 extended ideals whose first component is an integral HNF and second
 * a famat */
static GEN
idealHNF_mulred(GEN nf, GEN x, GEN y)
{
  GEN A = idealHNF_mul(nf, gel(x,1), gel(y,1));
  GEN F = famat_mul_shallow(gel(x,2), gel(y,2));
  return idealred(nf, mkvec2(A, F));
}
/* red(x * pr^n), n > 0 is small, x extended ideal. Reduction in order to
 * avoid prec pb: don't let id become too large as lgsub increases */
static GEN
idealmulpowprimered(GEN nf, GEN x, GEN pr, ulong n)
{
  GEN A = idealmulpowprime(nf, gel(x,1), pr, utoipos(n));
  return idealred(nf, mkvec2(A, gel(x,2)));
}

/* return famat y (principal ideal) such that y / x is smooth [wrt Vbase] */
static GEN
SPLIT(FB_t *F, GEN nf, GEN x, GEN Vbase, FACT *fact)
{
  GEN vecG, ex, y, x0, Nx = ZM_det_triangular(x);
  long nbtest_lim, nbtest, i, j, ru, lgsub;
  pari_sp av;

  /* try without reduction if x is small */
  if (gexpo(gcoeff(x,1,1)) < 100 &&
      can_factor(F, nf, x, NULL, Nx, fact)) return NULL;

  av = avma;
  y = idealpseudomin_nonscalar(x, nf_get_roundG(nf));
  if (factorgen(F, nf, x, Nx, y, fact)) return y;
  avma = av;

  /* reduce in various directions */
  ru = lg(nf_get_roots(nf));
  vecG = cgetg(ru, t_VEC);
  for (j=1; j<ru; j++)
  {
    gel(vecG,j) = nf_get_Gtwist1(nf, j);
    av = avma;
    y = idealpseudomin_nonscalar(x, gel(vecG,j));
    if (factorgen(F, nf, x, Nx, y, fact)) return y;
    avma = av;
  }

  /* tough case, multiply by random products */
  lgsub = 3;
  ex = cgetg(lgsub, t_VECSMALL);
  x0 = init_famat(x);
  nbtest = 1; nbtest_lim = 4;
  for(;;)
  {
    GEN Ired, I, NI, id = x0;
    av = avma;
    if (DEBUGLEVEL>2) err_printf("# ideals tried = %ld\n",nbtest);
    for (i=1; i<lgsub; i++)
    {
      ex[i] = random_bits(RANDOM_BITS);
      if (ex[i]) id = idealmulpowprimered(nf, id, gel(Vbase,i), ex[i]);
    }
    if (id == x0) continue;
    /* I^(-1) * \prod Vbase[i]^ex[i] = (id[2]) / x */

    I = gel(id,1); NI = ZM_det_triangular(I);
    if (can_factor(F, nf, I, NULL, NI, fact))
    {
      inv_fact(fact); /* I^(-1) */
      for (i=1; i<lgsub; i++)
        if (ex[i]) add_to_fact(Vbase_to_FB(F,gel(Vbase,i)), ex[i], fact);
      return gel(id,2);
    }
    Ired = ru == 2? I: ZM_lll(I, 0.99, LLL_INPLACE);
    for (j=1; j<ru; j++)
    {
      pari_sp av2 = avma;
      y = idealpseudomin_nonscalar(Ired, gel(vecG,j));
      if (factorgen(F, nf, I, NI, y, fact))
      {
        for (i=1; i<lgsub; i++)
          if (ex[i]) add_to_fact(Vbase_to_FB(F,gel(Vbase,i)), ex[i], fact);
        return famat_mul_shallow(gel(id,2), y);
      }
      avma = av2;
    }
    avma = av;
    if (++nbtest > nbtest_lim)
    {
      nbtest = 0;
      if (++lgsub < minss(7, lg(Vbase)-1))
      {
        nbtest_lim <<= 1;
        ex = cgetg(lgsub, t_VECSMALL);
      }
      else nbtest_lim = LONG_MAX; /* don't increase further */
      if (DEBUGLEVEL>2) err_printf("SPLIT: increasing factor base [%ld]\n",lgsub);
    }
  }
}

INLINE GEN
bnf_get_W(GEN bnf) { return gel(bnf,1); }
INLINE GEN
bnf_get_B(GEN bnf) { return gel(bnf,2); }
INLINE GEN
bnf_get_C(GEN bnf) { return gel(bnf,4); }
INLINE GEN
bnf_get_vbase(GEN bnf) { return gel(bnf,5); }

/* Return y (as an elt of K or a t_MAT representing an elt in Z[K])
 * such that x / (y) is smooth and store the exponents of  its factorization
 * on g_W and g_B in Wex / Bex; return NULL for y = 1 */
static GEN
split_ideal(GEN bnf, GEN x, GEN *pWex, GEN *pBex)
{
  GEN L, y, Vbase = bnf_get_vbase(bnf);
  GEN Wex, W  = bnf_get_W(bnf);
  GEN Bex, B  = bnf_get_B(bnf);
  long p, j, i, l, nW, nB;
  FACT *fact;
  FB_t F;

  L = recover_partFB(&F, Vbase, lg(x)-1);
  fact = (FACT*)stack_malloc((F.KC+1)*sizeof(FACT));
  y = SPLIT(&F, bnf_get_nf(bnf), x, Vbase, fact);
  nW = lg(W)-1; *pWex = Wex = zero_zv(nW);
  nB = lg(B)-1; *pBex = Bex = zero_zv(nB); l = lg(F.FB);
  p = j = 0; /* -Wall */
  for (i = 1; i <= fact[0].pr; i++)
  { /* decode index C = ip+j --> (p,j) */
    long a, b, t, C = fact[i].pr;
    for (t = 1; t < l; t++)
    {
      long q = F.FB[t], k = C - F.iLP[q];
      if (k <= 0) break;
      p = q;
      j = k;
    }
    a = gel(L, p)[j];
    b = a - nW;
    if (b <= 0) Wex[a] = y? -fact[i].ex: fact[i].ex;
    else        Bex[b] = y? -fact[i].ex: fact[i].ex;
  }
  return y;
}

/**** logarithmic embeddings ****/
static GEN famat_to_arch(GEN nf, GEN fa, long prec);
static GEN
triv_arch(GEN nf) { return zerovec(lg(nf_get_roots(nf))-1); }

/* Get archimedean components: [e_i Log( sigma_i(X) )], where X = primpart(x),
 * and e_i = 1 (resp 2.) for i <= R1 (resp. > R1) */
static GEN
get_arch(GEN nf, GEN x, long prec)
{
  long i, l, R1;
  GEN v;
  if (typ(x) == t_MAT) return famat_to_arch(nf,x,prec);
  x = nf_to_scalar_or_basis(nf,x);
  if (typ(x) != t_COL) return triv_arch(nf);
  x = RgM_RgC_mul(nf_get_M(nf), Q_primpart(x));
  l = lg(x);
  for (i=1; i < l; i++) if (gequal0(gabs(gel(x,i),prec))) return NULL;
  v = cgetg(l,t_VEC); R1 = nf_get_r1(nf);
  for (i=1; i<=R1; i++) gel(v,i) = glog(gel(x,i),prec);
  for (   ; i < l; i++) gel(v,i) = gmul2n(glog(gel(x,i),prec),1);
  return v;
}
static GEN
famat_to_arch(GEN nf, GEN fa, long prec)
{
  GEN g,e, y = NULL;
  long i,l;

  if (typ(fa) != t_MAT) pari_err_TYPE("famat_to_arch",fa);
  if (lg(fa) == 1) return triv_arch(nf);
  g = gel(fa,1);
  e = gel(fa,2); l = lg(e);
  for (i=1; i<l; i++)
  {
    GEN t, x = nf_to_scalar_or_basis(nf, gel(g,i));
    /* multiplicative arch would be better (save logs), but exponents overflow
     * [ could keep track of expo separately, but not worth it ] */
    t = get_arch(nf,x,prec); if (!t) return NULL;
    if (gel(t,1) == gen_0) continue; /* rational */
    t = RgV_Rg_mul(t, gel(e,i));
    y = y? RgV_add(y,t): t;
  }
  return y ? y: triv_arch(nf);
}

static GEN
famat_get_arch_real(GEN nf,GEN x,GEN *emb,long prec)
{
  GEN A, T, a, t, g = gel(x,1), e = gel(x,2);
  long i, l = lg(e);

  if (l <= 1)
    return get_arch_real(nf, gen_1, emb, prec);
  A = T = NULL; /* -Wall */
  for (i=1; i<l; i++)
  {
    a = get_arch_real(nf, gel(g,i), &t, prec);
    if (!a) return NULL;
    a = RgC_Rg_mul(a, gel(e,i));
    t = vecpow(t, gel(e,i));
    if (i == 1) { A = a;          T = t; }
    else        { A = gadd(A, a); T = vecmul(T, t); }
  }
  *emb = T; return A;
}

static GEN
scalar_get_arch_real(GEN nf, GEN u, GEN *emb)
{
  GEN v, logu;
  long i, s = signe(u), RU = lg(nf_get_roots(nf))-1, R1 = nf_get_r1(nf);

  if (!s) pari_err_DOMAIN("get_arch_real","argument","=",gen_0,u);
  v = cgetg(RU+1, t_COL);
  logu = logr_abs(u);
  for (i=1; i<=R1; i++) gel(v,i) = logu;
  if (i <= RU)
  {
    GEN logu2 = shiftr(logu,1);
    for (   ; i<=RU; i++) gel(v,i) = logu2;
  }
  *emb = const_col(RU, u); return v;
}

static int
low_prec(GEN x) { return gequal0(x) || (typ(x) == t_REAL && realprec(x) <= DEFAULTPREC); }

/* For internal use. Get archimedean components: [e_i log( | sigma_i(x) | )],
 * with e_i = 1 (resp 2.) for i <= R1 (resp. > R1)
 * Return NULL if precision problem, and set *emb to the embeddings of x */
GEN
get_arch_real(GEN nf, GEN x, GEN *emb, long prec)
{
  long i, lx, R1;
  GEN v, t;

  if (typ(x) == t_MAT) return famat_get_arch_real(nf,x,emb,prec);
  x = nf_to_scalar_or_basis(nf,x);
  if (typ(x) != t_COL) return scalar_get_arch_real(nf, gtofp(x,prec), emb);
  R1 = nf_get_r1(nf);
  x = RgM_RgC_mul(nf_get_M(nf), x);
  lx = lg(x);
  v = cgetg(lx,t_COL);
  for (i=1; i<=R1; i++)
  {
    t = gabs(gel(x,i),prec); if (low_prec(t)) return NULL;
    gel(v,i) = glog(t,prec);
  }
  for (   ; i< lx; i++)
  {
    t = gnorm(gel(x,i)); if (low_prec(t)) return NULL;
    gel(v,i) = glog(t,prec);
  }
  *emb = x; return v;
}


GEN
init_red_mod_units(GEN bnf, long prec)
{
  GEN s = gen_0, p1,s1,mat, logfu = bnf_get_logfu(bnf);
  long i,j, RU = lg(logfu);

  if (RU == 1) return NULL;
  mat = cgetg(RU,t_MAT);
  for (j=1; j<RU; j++)
  {
    p1 = cgetg(RU+1,t_COL); gel(mat,j) = p1;
    s1 = gen_0;
    for (i=1; i<RU; i++)
    {
      gel(p1,i) = real_i(gcoeff(logfu,i,j));
      s1 = mpadd(s1, mpsqr(gel(p1,i)));
    }
    gel(p1,RU) = gen_0; if (mpcmp(s1,s) > 0) s = s1;
  }
  s = gsqrt(gmul2n(s,RU),prec);
  if (expo(s) < 27) s = utoipos(1UL << 27);
  return mkvec2(mat, s);
}

/* z computed above. Return unit exponents that would reduce col (arch) */
GEN
red_mod_units(GEN col, GEN z)
{
  long i,RU;
  GEN x,mat,N2;

  if (!z) return NULL;
  mat= gel(z,1);
  N2 = gel(z,2);
  RU = lg(mat); x = cgetg(RU+1,t_COL);
  for (i=1; i<RU; i++) gel(x,i) = real_i(gel(col,i));
  gel(x,RU) = N2;
  x = lll(shallowconcat(mat,x));
  if (typ(x) != t_MAT) return NULL;
  x = gel(x,RU);
  if (signe(gel(x,RU)) < 0) x = gneg_i(x);
  if (!gequal1(gel(x,RU))) pari_err_BUG("red_mod_units");
  setlg(x,RU); return x;
}

static GEN
add(GEN a, GEN t) { return a = a? gadd(a,t): t; }

/* [x] archimedian components, A column vector. return [x] A */
static GEN
act_arch(GEN A, GEN x)
{
  GEN a;
  long i,l = lg(A), tA = typ(A);
  if (tA == t_MAT)
  { /* assume lg(x) >= l */
    a = cgetg(l, t_VEC);
    for (i=1; i<l; i++) gel(a,i) = act_arch(gel(A,i), x);
    return a;
  }
  if (l==1) return cgetg(1, t_VEC);
  a = NULL;
  if (tA == t_VECSMALL)
  {
    for (i=1; i<l; i++)
    {
      long c = A[i];
      if (c) a = add(a, gmulsg(c, gel(x,i)));
    }
  }
  else
  { /* A a t_COL of t_INT. Assume lg(A)==lg(x) */
    for (i=1; i<l; i++)
    {
      GEN c = gel(A,i);
      if (signe(c)) a = add(a, gmul(c, gel(x,i)));
    }
  }
  if (!a) return zerovec(lgcols(x)-1);
  settyp(a, t_VEC); return a;
}

static long
prec_arch(GEN bnf)
{
  GEN a = bnf_get_C(bnf);
  long i, l = lg(a), prec;

  for (i=1; i<l; i++)
    if ( (prec = gprecision(gel(a,i))) ) return prec;
  return DEFAULTPREC;
}

static long
needed_bitprec(GEN x)
{
  long i, e = 0, l = lg(x);
  for (i = 1; i < l; i++)
  {
    GEN c = gel(x,i);
    long f = gexpo(c) - prec2nbits(gprecision(c));
    if (f > e) e = f;
  }
  return e;
}

/* col = archimedian components of x, Nx = kNx^e its norm (e > 0, usually = 1),
 * dx a bound for its denominator. Return x or NULL (fail) */
GEN
isprincipalarch(GEN bnf, GEN col, GEN kNx, GEN e, GEN dx, long *pe)
{
  GEN nf, x, y, logfu, s, M;
  long N, R1, RU, i, prec = gprecision(col);
  bnf = checkbnf(bnf); nf = bnf_get_nf(bnf); M = nf_get_M(nf);
  if (!prec) prec = prec_arch(bnf);
  *pe = 128;
  logfu = bnf_get_logfu(bnf);
  N = nf_get_degree(nf);
  R1 = nf_get_r1(nf);
  RU = (N + R1)>>1;
  if (!(col = cleanarch(col,N,prec))) return NULL;
  settyp(col, t_COL);
  if (RU > 1)
  { /* reduce mod units */
    GEN u, z = init_red_mod_units(bnf,prec);
    u = red_mod_units(col,z);
    if (!u && z) return NULL;
    if (u)
    {
      col = RgC_add(col, RgM_RgC_mul(logfu, u));
      if (!(col = cleanarch(col,N,prec))) return NULL;
    }
  }
  s = divru(mulir(e, glog(kNx,prec)), N);
  for (i=1; i<=R1; i++) gel(col,i) = gexp(gadd(s, gel(col,i)),prec);
  for (   ; i<=RU; i++) gel(col,i) = gexp(gadd(s, gmul2n(gel(col,i),-1)),prec);
  /* d.alpha such that x = alpha \prod gj^ej */
  x = RgM_solve_realimag(M,col); if (!x) return NULL;
  x = RgC_Rg_mul(x, dx);
  y = grndtoi(x, pe);
  if (*pe > -5) { *pe = needed_bitprec(x); return NULL; }
  return RgC_Rg_div(y, dx);
}

/* y = C \prod g[i]^e[i] ? */
static int
fact_ok(GEN nf, GEN y, GEN C, GEN g, GEN e)
{
  pari_sp av = avma;
  long i, c = lg(e);
  GEN z = C? C: gen_1;
  for (i=1; i<c; i++)
    if (signe(gel(e,i))) z = idealmul(nf, z, idealpow(nf, gel(g,i), gel(e,i)));
  if (typ(z) != t_MAT) z = idealhnf_shallow(nf,z);
  if (typ(y) != t_MAT) y = idealhnf_shallow(nf,y);
  i = ZM_equal(y, z); avma = av; return i;
}

/* assume x in HNF. cf class_group_gen for notations.
 * Return NULL iff flag & nf_FORCE and computation of principal ideal generator
 * fails */
static GEN
isprincipalall(GEN bnf, GEN x, long *ptprec, long flag)
{
  long i, nB, e, c, prec = *ptprec;
  GEN Q, xar, Wex, Bex, U, gen, cyc, xc, ex, d, col, A;
  GEN B  = bnf_get_B(bnf);
  GEN C  = bnf_get_C(bnf);
  GEN nf = bnf_get_nf(bnf);
  GEN clg2 = gel(bnf,9);
  pari_sp av;

  U = gel(clg2,1);
  cyc = bnf_get_cyc(bnf); c = lg(cyc)-1;
  gen = bnf_get_gen(bnf);
  ex = cgetg(c+1,t_COL);
  if (c == 0 && !(flag & (nf_GEN|nf_GENMAT|nf_GEN_IF_PRINCIPAL))) return ex;

  /* factor x */
  x = Q_primitive_part(x, &xc);
  av = avma;
  xar = split_ideal(bnf, x, &Wex, &Bex);
  /* x = g_W Wex + g_B Bex + [xar] = g_W (Wex - B*Bex) + [xar] + [C_B]Bex
   * since g_W B + g_B = [C_B] */
  A = zc_to_ZC(Wex);
  nB = lg(Bex)-1;
  if (nB) A = ZC_sub(A, ZM_zc_mul(B,Bex));
  Q = ZM_ZC_mul(U, A);
  for (i=1; i<=c; i++)
    gel(Q,i) = truedvmdii(gel(Q,i), gel(cyc,i), (GEN*)(ex+i));
  if ((flag & nf_GEN_IF_PRINCIPAL))
    { if (!ZV_equal0(ex)) return gen_0; }
  else if (!(flag & (nf_GEN|nf_GENMAT)))
    return ZC_copy(ex);

  /* compute arch component of the missing principal ideal */
  { /* g A = G Ur A + [ga]A, Ur A = D Q + R as above (R = ex)
           = G R + [GD]Q + [ga]A */
    GEN ga = gel(clg2,2), GD = gel(clg2,3);
    long nW = lg(Wex)-1;
    col = NULL;
    if (nB) col = act_arch(Bex, nW? vecslice(C,nW+1,lg(C)): C);
    if (nW) col = add(col, act_arch(A, ga));
    if (c)  col = add(col, act_arch(Q, GD));
    if (!col) col = triv_arch(nf);
  }
  if (xar)
  {
    GEN t = get_arch(nf, xar, prec);
    col = t? gadd(col, t): NULL;
  }

  /* find coords on Zk; Q = N (x / \prod gj^ej) = N(alpha), denom(alpha) | d */
  Q = gdiv(ZM_det_triangular(x), get_norm_fact(gen, ex, &d));
  col = col?isprincipalarch(bnf, col, Q, gen_1, d, &e): NULL;
  if (col && !fact_ok(nf,x, col,gen,ex)) col = NULL;
  if (!col && !ZV_equal0(ex))
  { /* in case isprincipalfact calls bnfinit() due to prec trouble...*/
    GEN y;
    ex = gerepilecopy(av, ex);
    y = isprincipalfact(bnf, x, gen, ZC_neg(ex), flag);
    if (typ(y) != t_VEC) return y;
    col = gel(y,2);
  }
  if (col)
  { /* add back missing content */
    if (xc) col = (typ(col)==t_MAT)? famat_mul_shallow(col,xc)
                                   : RgC_Rg_mul(col,xc);
  }
  else
  {
    if (e < 0) e = 0;
    *ptprec = prec + nbits2extraprec(e + 128);
    if (flag & nf_FORCE)
    {
      if (DEBUGLEVEL) pari_warn(warner,"precision too low for generators, e = %ld",e);
      return NULL;
    }
    pari_warn(warner,"precision too low for generators, not given");
    col = cgetg(1, t_COL);
  }
  return (flag & nf_GEN_IF_PRINCIPAL)? col: mkvec2(ex, col);
}

static GEN
triv_gen(GEN bnf, GEN x, long flag)
{
  GEN nf = bnf_get_nf(bnf);
  long c;
  if (flag & nf_GEN_IF_PRINCIPAL) return algtobasis(nf,x);
  c = lg(bnf_get_cyc(bnf)) - 1;
  if (flag & (nf_GEN|nf_GENMAT)) retmkvec2(zerocol(c), algtobasis(nf,x));
  return zerocol(c);
}

GEN
bnfisprincipal0(GEN bnf,GEN x,long flag)
{
  GEN arch, c, nf;
  long pr;
  pari_sp av = avma;

  bnf = checkbnf(bnf);
  nf = bnf_get_nf(bnf);
  switch( idealtyp(&x, &arch) )
  {
    case id_PRINCIPAL:
      if (gequal0(x)) pari_err_DOMAIN("bnfisprincipal","ideal","=",gen_0,x);
      return triv_gen(bnf, x, flag);
    case id_PRIME:
      if (pr_is_inert(x))
        return gerepileupto(av, triv_gen(bnf, gel(x,1), flag));
      x = pr_hnf(nf, x);
      break;
    case id_MAT:
      if (lg(x)==1) pari_err_DOMAIN("bnfisprincipal","ideal","=",gen_0,x);
      if (nf_get_degree(nf) != lg(x)-1)
        pari_err_TYPE("idealtyp [dimension != degree]", x);
  }
  pr = prec_arch(bnf); /* precision of unit matrix */
  c = getrand();
  for (;;)
  {
    pari_sp av1 = avma;
    GEN y = isprincipalall(bnf,x,&pr,flag);
    if (y) return gerepilecopy(av, y);

    if (DEBUGLEVEL) pari_warn(warnprec,"isprincipal",pr);
    avma = av1; bnf = bnfnewprec_shallow(bnf,pr); setrand(c);
  }
}
GEN
isprincipal(GEN bnf,GEN x) { return bnfisprincipal0(bnf,x,0); }

/* FIXME: OBSOLETE */
GEN
isprincipalgen(GEN bnf,GEN x)
{ return bnfisprincipal0(bnf,x,nf_GEN); }
GEN
isprincipalforce(GEN bnf,GEN x)
{ return bnfisprincipal0(bnf,x,nf_FORCE); }
GEN
isprincipalgenforce(GEN bnf,GEN x)
{ return bnfisprincipal0(bnf,x,nf_GEN | nf_FORCE); }

/* lg(u) > 1 */
static int
RgV_is1(GEN u) { return isint1(gel(u,1)) && RgV_isscalar(u); }
static GEN
add_principal_part(GEN nf, GEN u, GEN v, long flag)
{
  if (flag & nf_GENMAT)
    return (typ(u) == t_COL && RgV_is1(u))? v: famat_mul_shallow(v,u);
  else
    return nfmul(nf, v, u);
}

#if 0
/* compute C prod P[i]^e[i],  e[i] >=0 for all i. C may be NULL (omitted)
 * e destroyed ! */
static GEN
expand(GEN nf, GEN C, GEN P, GEN e)
{
  long i, l = lg(e), done = 1;
  GEN id = C;
  for (i=1; i<l; i++)
  {
    GEN ei = gel(e,i);
    if (signe(ei))
    {
      if (mod2(ei)) id = id? idealmul(nf, id, gel(P,i)): gel(P,i);
      ei = shifti(ei,-1);
      if (signe(ei)) done = 0;
      gel(e,i) = ei;
    }
  }
  if (id != C) id = idealred(nf, id);
  if (done) return id;
  return idealmulred(nf, id, idealsqr(nf, expand(nf,id,P,e)));
}
/* C is an extended ideal, possibly with C[1] = NULL */
static GEN
expandext(GEN nf, GEN C, GEN P, GEN e)
{
  long i, l = lg(e), done = 1;
  GEN A = gel(C,1);
  for (i=1; i<l; i++)
  {
    GEN ei = gel(e,i);
    if (signe(ei))
    {
      if (mod2(ei)) A = A? idealmul(nf, A, gel(P,i)): gel(P,i);
      ei = shifti(ei,-1);
      if (signe(ei)) done = 0;
      gel(e,i) = ei;
    }
  }
  if (A == gel(C,1))
    A = C;
  else
    A = idealred(nf, mkvec2(A, gel(C,2)));
  if (done) return A;
  return idealmulred(nf, A, idealsqr(nf, expand(nf,A,P,e)));
}
#endif

static GEN
expand(GEN nf, GEN C, GEN P, GEN e)
{
  long i, l = lg(e);
  GEN B, A = C;
  for (i=1; i<l; i++) /* compute prod P[i]^e[i] */
    if (signe(gel(e,i)))
    {
      B = idealpowred(nf, gel(P,i), gel(e,i));
      A = A? idealmulred(nf,A,B): B;
    }
  return A;
}
static GEN
expandext(GEN nf, GEN C, GEN P, GEN e)
{
  long i, l = lg(e);
  GEN B, A = gel(C,1), C1 = A;
  for (i=1; i<l; i++) /* compute prod P[i]^e[i] */
    if (signe(gel(e,i)))
    {
      gel(C,1) = gel(P,i);
      B = idealpowred(nf, C, gel(e,i));
      A = A? idealmulred(nf,A,B): B;
    }
  return A == C1? C: A;
}

/* isprincipal for C * \prod P[i]^e[i] (C omitted if NULL) */
GEN
isprincipalfact(GEN bnf, GEN C, GEN P, GEN e, long flag)
{
  const long gen = flag & (nf_GEN|nf_GENMAT|nf_GEN_IF_PRINCIPAL);
  long prec;
  pari_sp av = avma;
  GEN C0, Cext, c, id, nf = checknf(bnf);

  if (gen)
  {
    Cext = (flag & nf_GENMAT)? trivial_fact()
                             : mkpolmod(gen_1,nf_get_pol(nf));
    C0 = mkvec2(C, Cext);
    id = expandext(nf, C0, P, e);
  } else {
    Cext = NULL;
    C0 = C;
    id = expand(nf, C, P, e);
  }
  if (id == C0) /* e = 0 */
  {
    if (!C) return bnfisprincipal0(bnf, gen_1, flag);
    C = idealhnf_shallow(nf,C);
  }
  else
  {
    if (gen) { C = gel(id,1); Cext = gel(id,2); } else C = id;
  }
  prec = prec_arch(bnf);
  c = getrand();
  for (;;)
  {
    pari_sp av1 = avma;
    GEN y = isprincipalall(bnf, C, &prec, flag);
    if (y)
    {
      if (flag & nf_GEN_IF_PRINCIPAL)
      {
        if (typ(y) == t_INT) { avma = av; return NULL; }
        y = add_principal_part(nf, y, Cext, flag);
      }
      else
      {
        GEN u = gel(y,2);
        if (!gen || typ(y) != t_VEC) return gerepileupto(av,y);
        if (lg(u) != 1) gel(y,2) = add_principal_part(nf, u, Cext, flag);
      }
      return gerepilecopy(av, y);
    }
    if (DEBUGLEVEL) pari_warn(warnprec,"isprincipal",prec);
    avma = av1; bnf = bnfnewprec_shallow(bnf,prec); setrand(c);
  }
}
GEN
isprincipalfact_or_fail(GEN bnf, GEN C, GEN P, GEN e)
{
  const long flag = nf_GENMAT|nf_FORCE;
  long prec;
  pari_sp av = avma;
  GEN u, y, id, C0, Cext, nf = bnf_get_nf(bnf);

  Cext = trivial_fact();
  C0 = mkvec2(C, Cext);
  id = expandext(nf, C0, P, e);
  if (id == C0) /* e = 0 */
    C = idealhnf_shallow(nf,C);
  else {
    C = gel(id,1); Cext = gel(id,2);
  }
  prec = prec_arch(bnf);
  y = isprincipalall(bnf, C, &prec, flag);
  if (!y) { avma = av; return utoipos(prec); }
  u = gel(y,2);
  if (lg(u) != 1) gel(y,2) = add_principal_part(nf, u, Cext, flag);
  return gerepilecopy(av, y);
}

/* if x a famat, assume it is an algebraic integer (very costly to check) */
GEN
bnfisunit(GEN bnf,GEN x)
{
  long tx = typ(x), i, R1, RU, e, n, prec;
  pari_sp av = avma;
  GEN p1, v, rlog, logunit, ex, nf, pi2_sur_w, emb;

  bnf = checkbnf(bnf); nf = bnf_get_nf(bnf);
  logunit = bnf_get_logfu(bnf); RU = lg(logunit);
  n = bnf_get_tuN(bnf); /* # { roots of 1 } */
  if (tx == t_MAT)
  { /* famat, assumed integral */
    if (lg(x) != 3) pari_err_TYPE("bnfisunit [not a factorization]", x);
  } else {
    x = nf_to_scalar_or_basis(nf,x);
    if (typ(x) != t_COL)
    { /* rational unit ? */
      long s;
      if (typ(x) != t_INT || !is_pm1(x)) return cgetg(1,t_COL);
      s = signe(x); avma = av; v = zerocol(RU);
      gel(v,RU) = mkintmodu((s > 0)? 0: n>>1, n);
      return v;
    }
    if (!isint1(Q_denom(x))) { avma = av; return cgetg(1,t_COL); }
  }

  R1 = nf_get_r1(nf); v = cgetg(RU+1,t_COL);
  for (i=1; i<=R1; i++) gel(v,i) = gen_1;
  for (   ; i<=RU; i++) gel(v,i) = gen_2;
  logunit = shallowconcat(logunit, v);
  /* ex = fundamental units exponents */
  rlog = real_i(logunit);
  prec = nf_get_prec(nf);
  for (i=1;; i++)
  {
    GEN rx = get_arch_real(nf,x,&emb, MEDDEFAULTPREC);
    if (rx)
    {
      GEN logN = RgV_sum(rx); /* log(Nx), should be ~ 0 */
      if (gexpo(logN) > -20)
      { /* precision problem ? */
        if (typ(logN) != t_REAL) { avma = av; return cgetg(1,t_COL); } /*no*/
        if (i == 1)
        {
          GEN N = nfnorm(nf, x);
          if (!is_pm1(N)) { avma = av; return cgetg(1, t_COL); }
        }
      }
      else
      {
        ex = RgM_solve(rlog, rx);
        if (ex)
        {
          ex = grndtoi(ex, &e);
          if (!signe(gel(ex,RU)) && e < -4) break;
        }
      }
    }
    if (i == 1)
      prec = nbits2prec(gexpo(x) + 128);
    else
    {
      if (i > 4) pari_err_PREC("bnfisunit");
      prec = precdbl(prec);
    }
    if (DEBUGLEVEL) pari_warn(warnprec,"bnfisunit",prec);
    nf = nfnewprec_shallow(nf, prec);
  }

  setlg(ex, RU); /* ZC */
  p1 = imag_i( row_i(logunit,1, 1,RU-1) );
  p1 = RgV_dotproduct(p1, ex); if (!R1) p1 = gmul2n(p1, -1);
  p1 = gsub(garg(gel(emb,1),prec), p1);
  /* p1 = arg(the missing root of 1) */

  pi2_sur_w = divru(mppi(prec), n>>1); /* 2pi / n */
  e = umodiu(roundr(divrr(p1, pi2_sur_w)), n);
  if (n > 2)
  {
    GEN z = algtobasis(nf, bnf_get_tuU(bnf)); /* primitive root of 1 */
    GEN ro = RgV_dotproduct(row(nf_get_M(nf), 1), z);
    GEN p2 = roundr(divrr(garg(ro, prec), pi2_sur_w));
    e *= Fl_inv(umodiu(p2,n), n);
    e %= n;
  }

  gel(ex,RU) = mkintmodu(e, n);
  setlg(ex, RU+1); return gerepilecopy(av, ex);
}

GEN
nfsign_from_logarch(GEN LA, GEN invpi, GEN archp)
{
  long l = lg(archp), i;
  GEN y = cgetg(l, t_VECSMALL);
  pari_sp av = avma;

  for (i=1; i<l; i++)
  {
    GEN c = ground( gmul(imag_i(gel(LA,archp[i])), invpi) );
    y[i] = mpodd(c)? 1: 0;
  }
  avma = av; return y;
}

GEN
nfsign_units(GEN bnf, GEN archp, int add_zu)
{
  GEN invpi, y, A = bnf_get_logfu(bnf), nf = bnf_get_nf(bnf);
  long j = 1, RU = lg(A);

  invpi = invr( mppi(nf_get_prec(nf)) );
  if (!archp) archp = identity_perm( nf_get_r1(nf) );
  if (add_zu) { RU++; A--; }
  y = cgetg(RU,t_MAT);
  if (add_zu)
  {
    long w = bnf_get_tuN(bnf);
    gel(y, j++) = (w == 2)? const_vecsmall(lg(archp)-1, 1)
                          : cgetg(1, t_VECSMALL);
  }
  for ( ; j < RU; j++) gel(y,j) = nfsign_from_logarch(gel(A,j), invpi, archp);
  return y;
}

/* obsolete */
GEN
signunits(GEN bnf)
{
  pari_sp av;
  GEN S, y, nf;
  long i, j, r1, r2;

  bnf = checkbnf(bnf); nf = bnf_get_nf(bnf);
  nf_get_sign(nf, &r1,&r2);
  S = zeromatcopy(r1, r1+r2-1); av = avma;
  y = nfsign_units(bnf, NULL, 0);
  for (j = 1; j < lg(y); j++)
  {
    GEN Sj = gel(S,j), yj = gel(y,j);
    for (i = 1; i <= r1; i++) gel(Sj,i) = yj[i]? gen_m1: gen_1;
  }
  avma = av; return S;
}

static GEN
get_log_embed(REL_t *rel, GEN M, long RU, long R1, long prec)
{
  GEN arch, C, z = rel->m;
  long i;
  if (!z) return zerocol(RU);
  arch = typ(z) == t_COL? RgM_RgC_mul(M, z): RgC_Rg_mul(gel(M,1), z);
  C = cgetg(RU+1, t_COL); arch = glog(arch, prec);
  for (i=1; i<=R1; i++) gel(C,i) = gel(arch,i);
  for (   ; i<=RU; i++) gel(C,i) = gmul2n(gel(arch,i), 1);
  return C;
}

static GEN
perm_log_embed(GEN C, GEN perm)
{
  long i, n;
  GEN Cnew = cgetg_copy(C, &n);
  for (i = 1; i < n; i++)
  {
    long v = perm[i];
    if (v > 0)
      gel(Cnew, i) = gel(C, v);
    else
      gel(Cnew, i) = conj_i(gel(C, -v));
  }
  return Cnew;
}

static GEN
set_fact(FB_t *F, FACT *fact, GEN ex, long *pnz)
{
  long i, n = fact[0].pr;
  long nz;
  GEN c = zero_Flv(F->KC);
  if (!n) /* trivial factorization */
    *pnz = F->KC+1;
  else {
    nz = fact[1].pr;
    if (fact[n].pr < nz) /* Possible with jid in rnd_rel */
      nz = fact[n].pr;
    for (i=1; i<=n; i++) c[fact[i].pr] = fact[i].ex;
    if (ex)
    {
      for (i=1; i<lg(ex); i++)
        if (ex[i]) {
          long v = F->subFB[i];
          c[v] += ex[i];
          if (v < nz) nz = v;
        }
    }
    *pnz = nz;
  }
  return c;
}

/* Is cols already in the cache ? bs = index of first non zero coeff in cols
 * General check for colinearity useless since exceedingly rare */
static int
already_known(RELCACHE_t *cache, long bs, GEN cols)
{
  REL_t *r;
  long l = lg(cols);
  for (r = cache->last; r > cache->base; r--)
    if (bs == r->nz)
    {
      GEN coll = r->R;
      long b = bs;
      while (b < l && cols[b] == coll[b]) b++;
      if (b == l) return 1;
    }
  return 0;
}

/* Add relation R to cache, nz = index of first non zero coeff in R.
 * If relation is a linear combination of the previous ones, return 0.
 * Otherwise, update basis and return > 0. Compute mod p (much faster)
 * so some kernel vector might not be genuine. */
static int
add_rel_i(RELCACHE_t *cache, GEN R, long nz, GEN m, long orig, long aut, REL_t **relp, long in_rnd_rel)
{
  long i, k, n = lg(R)-1;

  if (nz == n+1) { k = 0; goto ADD_REL; }
  if (already_known(cache, nz, R)) return -1;
  if (cache->last >= cache->base + cache->len) return 0;
  if (DEBUGLEVEL>6)
  {
    err_printf("adding vector = %Ps\n",R);
    err_printf("generators =\n%Ps\n", cache->basis);
  }
  if (cache->missing)
  {
    GEN a = leafcopy(R), basis = cache->basis;
    k = lg(a);
    do --k; while (!a[k]);
    while (k)
    {
      GEN c = gel(basis, k);
      if (c[k])
      {
        long ak = a[k];
        for (i=1; i < k; i++) if (c[i]) a[i] = (a[i] + ak*(mod_p-c[i])) % mod_p;
        a[k] = 0;
        do --k; while (!a[k]); /* k cannot go below 0: codeword is a sentinel */
      }
      else
      {
        ulong invak = Fl_inv(uel(a,k), mod_p);
        /* Cleanup a */
        for (i = k; i-- > 1; )
        {
          long j, ai = a[i];
          c = gel(basis, i);
          if (!ai || !c[i]) continue;
          ai = mod_p-ai;
          for (j = 1; j < i; j++) if (c[j]) a[j] = (a[j] + ai*c[j]) % mod_p;
          a[i] = 0;
        }
        /* Insert a/a[k] as k-th column */
        c = gel(basis, k);
        for (i = 1; i<k; i++) if (a[i]) c[i] = (a[i] * invak) % mod_p;
        c[k] = 1; a = c;
        /* Cleanup above k */
        for (i = k+1; i<n; i++)
        {
          long j, ck;
          c = gel(basis, i);
          ck = c[k];
          if (!ck) continue;
          ck = mod_p-ck;
          for (j = 1; j < k; j++) if (a[j]) c[j] = (c[j] + ck*a[j]) % mod_p;
          c[k] = 0;
        }
        cache->missing--;
        break;
      }
    }
  }
  else
    k = (cache->last - cache->base) + 1;
  if (k || cache->relsup > 0 || (m && in_rnd_rel))
  {
    REL_t *rel;

ADD_REL:
    rel = ++cache->last;
    if (!k && cache->relsup && nz < n+1)
    {
      cache->relsup--;
      k = (rel - cache->base) + cache->missing;
    }
    rel->R  = gclone(R);
    rel->m  =  m ? gclone(m) : NULL;
    rel->nz = nz;
    if (aut)
    {
      rel->relorig = (rel - cache->base) - orig;
      rel->relaut = aut;
    }
    else
      rel->relaut = 0;
    if (relp) *relp = rel;
    if (DEBUGLEVEL) dbg_newrel(cache);
  }
  return k;
}

static int
add_rel(RELCACHE_t *cache, FB_t *F, GEN R, long nz, GEN m, long in_rnd_rel)
{
  REL_t *rel;
  long k, l, reln;
  const long nauts = lg(F->idealperm), KC = F->KC;

  k = add_rel_i(cache, R, nz, m, 0, 0, &rel, in_rnd_rel);
  if (k > 0 && m)
  {
    GEN Rl = cgetg(KC+1, t_VECSMALL);
    reln = rel - cache->base;
    for (l = 1; l < nauts; l++)
    {
      GEN perml = gel(F->idealperm, l);
      long i, nzl = perml[nz];

      for (i = 1; i <= KC; i++) Rl[i] = 0;
      for (i = nz; i <= KC; i++)
        if (R[i])
        {
          long v = perml[i];

          if (v < nzl) nzl = v;
          Rl[v] = R[i];
        }
      (void)add_rel_i(cache, Rl, nzl, NULL, reln, l, NULL, in_rnd_rel);
    }
  }
  return k;
}

/* Compute powers of prime ideal (P^0,...,P^a) (a > 1) */
static void
powPgen(GEN nf, GEN vp, GEN *ppowP, long a)
{
  GEN id2, J;
  long j;

  id2 = cgetg(a+1,t_VEC);
  J = mkvec2(pr_get_p(vp), zk_scalar_or_multable(nf,pr_get_gen(vp)));
  gel(id2,1) = J;
  vp = pr_hnf(nf,vp);
  for (j=2; j<=a; j++)
  {
    if (DEBUGLEVEL>1) err_printf(" %ld", j);
    J = idealtwoelt(nf, idealHNF_mul(nf, vp, J));
    gel(J, 2) = zk_scalar_or_multable(nf, gel(J,2));
    gel(id2,j) = J;
  }
  setlg(id2, j);
  *ppowP = id2;
  if (DEBUGLEVEL>1) err_printf("\n");
}


/* Compute powers of prime ideals (P^0,...,P^a) in subFB (a > 1) */
static void
powFBgen(RELCACHE_t *cache, FB_t *F, GEN nf, GEN auts)
{
  const long a = 1L<<RANDOM_BITS;
  pari_sp av = avma;
  GEN subFB = F->subFB, idealperm = F->idealperm;
  long i, k, l, id, n = lg(F->subFB), naut = lg(auts);

  if (DEBUGLEVEL) err_printf("Computing powers for subFB: %Ps\n",subFB);
  if (cache) pre_allocate(cache, n*naut);
  for (i=1; i<n; i++)
  {
    id = subFB[i];
    if (gel(F->id2, id) == gen_0)
    {
      GEN id2 = NULL;

      for (k = 1; k < naut; k++)
      {
        long sigmaid = coeff(idealperm, id, k);
        GEN sigmaid2 = gel(F->id2, sigmaid);
        if (sigmaid2 != gen_0)
        {
          GEN aut = gel(auts, k), invaut = gel(auts, F->invs[k]);
          long lid2;
          id2 = cgetg_copy(sigmaid2, &lid2);
          if (DEBUGLEVEL>1) err_printf("%ld: automorphism(%ld)\n", id,sigmaid);
          for (l = 1; l < lid2; l++)
          {
            GEN id2l = gel(sigmaid2, l);
            gel(id2, l) =
              mkvec2(gel(id2l, 1), ZM_mul(ZM_mul(invaut, gel(id2l, 2)), aut));
          }
          break;
        }
      }
      if (!id2)
      {
        if (DEBUGLEVEL>1) err_printf("%ld: 1", id);
        powPgen(nf, gel(F->LP, id), &id2, a);
      }
      gel(F->id2, id) = gclone(id2);
      avma = av;
    }
  }
  F->sfb_chg = 0;
  F->newpow = 0;
}

INLINE void
step(GEN x, double *y, GEN inc, long k)
{
  if (!y[k])
    x[k]++; /* leading coeff > 0 */
  else
  {
    long i = inc[k];
    x[k] += i;
    inc[k] = (i > 0)? -1-i: 1-i;
  }
}

INLINE long
Fincke_Pohst_ideal(RELCACHE_t *cache, FB_t *F, GEN nf, GEN M,
    GEN G, GEN ideal0, FACT *fact, long nbrelpid, FP_t *fp,
    RNDREL_t *rr, long prec, long *nbsmallnorm, long *nbfact)
{
  pari_sp av;
  const long N = nf_get_degree(nf), R1 = nf_get_r1(nf);
  GEN r, u, gx, inc=const_vecsmall(N, 1), ideal;
  GEN Nideal = nbrelpid ? NULL : idealnorm(nf, ideal0);
  double BOUND;
  long j, k, skipfirst, nbrelideal=0, dependent=0, try_elt=0,  try_factor=0;

  u = ZM_lll(ZM_mul(F->G0, ideal0), 0.99, LLL_IM|LLL_COMPATIBLE);
  ideal = ZM_mul(ideal0,u); /* approximate T2-LLL reduction */
  r = gaussred_from_QR(RgM_mul(G, ideal), prec); /* Cholesky for T2 | ideal */
  if (!r) pari_err_BUG("small_norm (precision too low)");

  skipfirst = ZV_isscalar(gel(ideal,1))? 1: 0; /* 1 probable */
  for (k=1; k<=N; k++)
  {
    fp->v[k] = gtodouble(gcoeff(r,k,k));
    for (j=1; j<k; j++) fp->q[j][k] = gtodouble(gcoeff(r,j,k));
    if (DEBUGLEVEL>3) err_printf("fp->v[%ld]=%.4g ",k,fp->v[k]);
  }
  BOUND = mindd(BMULT*fp->v[1], 2*(fp->v[2]+fp->v[1]*fp->q[1][2]*fp->q[1][2]));
  /* BOUND at most BMULT fp->x smallest known vector */
  if (DEBUGLEVEL>1)
  {
    if (DEBUGLEVEL>3) err_printf("\n");
    err_printf("BOUND = %.4g\n",BOUND); err_flush();
  }
  BOUND *= 1 + 1e-6;
  k = N; fp->y[N] = fp->z[N] = 0; fp->x[N] = 0;
  for (av = avma;; avma = av, step(fp->x,fp->y,inc,k))
  {
    GEN R;
    long nz;
    do
    { /* look for primitive element of small norm, cf minim00 */
      int fl = 0;
      double p;
      if (k > 1)
      {
        long l = k-1;
        fp->z[l] = 0;
        for (j=k; j<=N; j++) fp->z[l] += fp->q[l][j]*fp->x[j];
        p = (double)fp->x[k] + fp->z[k];
        fp->y[l] = fp->y[k] + p*p*fp->v[k];
        if (l <= skipfirst && !fp->y[1]) fl = 1;
        fp->x[l] = (long)floor(-fp->z[l] + 0.5);
        k = l;
      }
      for(;; step(fp->x,fp->y,inc,k))
      {
        if (++try_elt > maxtry_ELEMENT) return 0;
        if (!fl)
        {
          p = (double)fp->x[k] + fp->z[k];
          if (fp->y[k] + p*p*fp->v[k] <= BOUND) break;

          step(fp->x,fp->y,inc,k);

          p = (double)fp->x[k] + fp->z[k];
          if (fp->y[k] + p*p*fp->v[k] <= BOUND) break;
        }
        fl = 0; inc[k] = 1;
        if (++k > N) return 0;
      }
    } while (k > 1);

    /* element complete */
    if (zv_content(fp->x) !=1) continue; /* not primitive */
    gx = ZM_zc_mul(ideal,fp->x);
    if (ZV_isscalar(gx)) continue;
    if (++try_factor > maxtry_FACT) return 0;

    if (!nbrelpid)
    {
      if (!factorgen(F,nf,ideal0,Nideal,gx,fact))
         continue;
      return 1;
    }
    else if (rr)
    {
      if (!factorgen(F,nf,ideal0,rr->Nideal,gx,fact))
         continue;
      add_to_fact(rr->jid, 1, fact);
      gx = nfmul(nf, rr->m1, gx);
    }
    else
    {
      GEN Nx, xembed = RgM_RgC_mul(M, gx);
      long e;
      if (nbsmallnorm) (*nbsmallnorm)++;
      Nx = grndtoi(embed_norm(xembed, R1), &e);
      if (e >= 0) {
        if (DEBUGLEVEL > 1) { err_printf("+"); err_flush(); }
        continue;
      }
      if (!can_factor(F, nf, NULL, gx, Nx, fact)) continue;
    }

    /* smooth element */
    R = set_fact(F, fact, rr ? rr->ex : NULL, &nz);
    /* make sure we get maximal rank first, then allow all relations */
    if (add_rel(cache, F, R, nz, gx, rr ? 1 : 0) <= 0)
    { /* probably Q-dependent from previous ones: forget it */
      if (DEBUGLEVEL>1) err_printf("*");
      if (++dependent > maxtry_DEP) break;
      continue;
    }
    dependent = 0;
    if (DEBUGLEVEL && nbfact) (*nbfact)++;
    if (cache->last >= cache->end) return 1; /* we have enough */
    if (++nbrelideal == nbrelpid) break;
  }
  return 0;
}

static void
small_norm(RELCACHE_t *cache, FB_t *F, GEN nf, long nbrelpid, GEN M,
           FACT *fact, GEN p0)
{
  pari_timer T;
  const long prec = nf_get_prec(nf);
  FP_t fp;
  pari_sp av;
  GEN G = nf_get_G(nf), L_jid = F->L_jid;
  long nbsmallnorm, nbfact, noideal = lg(L_jid);
  REL_t *last = cache->last;

  if (DEBUGLEVEL)
  {
    timer_start(&T);
    err_printf("\n#### Look for %ld relations in %ld ideals (small_norm)\n",
               cache->end - last, lg(L_jid)-1);
  }
  nbsmallnorm = nbfact = 0;

  minim_alloc(lg(M), &fp.q, &fp.x, &fp.y, &fp.z, &fp.v);
  for (av = avma; --noideal; avma = av)
  {
    GEN ideal = gel(F->LP, L_jid[noideal]);

    if (DEBUGLEVEL>1)
      err_printf("\n*** Ideal no %ld: %Ps\n", L_jid[noideal], vecslice(ideal,1,4));
    if (p0)
      ideal = idealmul(nf, p0, ideal);
    else
      ideal = pr_hnf(nf, ideal);
    if (Fincke_Pohst_ideal(cache, F, nf, M, G, ideal, fact,
          nbrelpid, &fp, NULL, prec, &nbsmallnorm, &nbfact))
      break;
    if (DEBUGLEVEL>1) timer_printf(&T, "for this ideal");
  }
  if (DEBUGLEVEL)
  {
    err_printf("\n");
    timer_printf(&T, "small norm relations");
    if (nbsmallnorm && DEBUGLEVEL > 1)
      err_printf("  nb. fact./nb. small norm = %ld/%ld = %.3f\n",
                  nbfact,nbsmallnorm,((double)nbfact)/nbsmallnorm);
  }
}

/* I integral ideal in HNF form */
static GEN
remove_content(GEN I)
{
  long N = lg(I)-1;
  if (!equali1(gcoeff(I,N,N))) I = Q_primpart(I);
  return I;
}

static GEN
get_random_ideal(FB_t *F, GEN nf, GEN ex)
{
  long l = lg(ex);
  for (;;) {
    GEN ideal = NULL;
    long i;
    for (i=1; i<l; i++)
    {
      long id = F->subFB[i];
      ex[i] = random_bits(RANDOM_BITS);
      if (ex[i])
      {
        GEN a = gmael(F->id2,id,ex[i]);
        ideal = ideal? idealHNF_mul(nf,ideal, a): idealhnf_two(nf,a);
      }
    }
    if (ideal) { /* ex  != 0 */
      ideal = remove_content(ideal);
      if (!is_pm1(gcoeff(ideal,1,1))) return ideal; /* ideal != Z_K */
    }
  }
}

static void
rnd_rel(RELCACHE_t *cache, FB_t *F, GEN nf, FACT *fact)
{
  pari_timer T;
  const GEN L_jid = F->L_jid, M = nf_get_M(nf), G = F->G0;
  GEN baseideal;
  RNDREL_t rr;
  FP_t fp;
  const long nbG = lg(F->vecG)-1, lgsub = lg(F->subFB), l_jid = lg(L_jid);
  const long prec = nf_get_prec(nf);
  long jlist;
  pari_sp av;

  /* will compute P[ L_jid[i] ] * (random product from subFB) */
  if (DEBUGLEVEL) {
    timer_start(&T);
    err_printf("\n#### Look for %ld relations in %ld ideals (rnd_rel)\n",
               cache->end - cache->last, lg(L_jid)-1);
  }
  rr.ex = cgetg(lgsub, t_VECSMALL);
  baseideal = get_random_ideal(F, nf, rr.ex);
  baseideal = red(nf, baseideal, F->G0, &rr.m1);
  minim_alloc(lg(M), &fp.q, &fp.x, &fp.y, &fp.z, &fp.v);
  for (av = avma, jlist = 1; jlist < l_jid; jlist++, avma = av)
  {
    long j;
    GEN ideal;
    pari_sp av1;
    REL_t *last = cache->last;

    rr.jid = L_jid[jlist];
    ideal = gel(F->LP,rr.jid);
    if (DEBUGLEVEL>1)
      err_printf("\n*** Ideal no %ld: %Ps\n", rr.jid, vecslice(ideal,1,4));
    ideal = idealHNF_mul(nf, baseideal, ideal);
    rr.Nideal = ZM_det_triangular(ideal);
    if (Fincke_Pohst_ideal(cache, F, nf, M, G, ideal, fact,
                           RND_REL_RELPID, &fp, &rr, prec, NULL, NULL))
      break;
    if (PREVENT_LLL_IN_RND_REL || cache->last != last) continue;
    for (av1 = avma, j = 1; j <= nbG; j++, avma = av1)
    { /* reduce along various directions */
      GEN m = idealpseudomin_nonscalar(ideal, gel(F->vecG,j));
      GEN R;
      long nz;
      if (!factorgen(F,nf,ideal,rr.Nideal,m,fact)) continue;
      /* can factor ideal, record relation */
      add_to_fact(rr.jid, 1, fact);
      R = set_fact(F, fact, rr.ex, &nz);
      switch (add_rel(cache, F, R, nz, nfmul(nf, m, rr.m1), 1))
      {
        case -1: /* forget it */
          if (DEBUGLEVEL>1) dbg_cancelrel(rr.jid,j,R);
          continue;
      }
      if (DEBUGLEVEL) timer_printf(&T, "for this relation");
      /* Need more, try next prime ideal */
      if (cache->last < cache->end) break;
      /* We have found enough. Return */
      avma = av; return;
    }
  }
  if (DEBUGLEVEL)
  {
    err_printf("\n");
    timer_printf(&T, "for remaining ideals");
  }
}

static GEN
automorphism_perms(GEN M, GEN auts, GEN cyclic, long N)
{
  pari_sp av;
  const long r1plusr2 = lgcols(M), r1 = 2*r1plusr2-N-2, r2 = r1plusr2-r1-1;
  long nauts = lg(auts), ncyc = lg(cyclic), i, j, l, m;
  GEN Mt, perms = cgetg(nauts, t_VEC);

  for (l = 1; l < nauts; l++)
    gel(perms, l) = cgetg(r1plusr2, t_VECSMALL);
  av = avma;
  Mt = shallowtrans(gprec_w(M, 3)); /* need little accuracy */
  Mt = shallowconcat(Mt, conj_i(vecslice(Mt, r1+1, r1+r2)));
  for (l = 1; l < ncyc; l++)
  {
    GEN thiscyc = gel(cyclic, l);
    long k = thiscyc[1];
    GEN Nt = RgM_mul(shallowtrans(gel(auts, k)), Mt);
    GEN perm = gel(perms, k), permprec;
    pari_sp av2 = avma;
    for (i = 1; i < r1plusr2; i++, avma = av2)
    {
      GEN vec = gel(Nt, i), minnorm;
      minnorm = gnorml2(gsub(vec, gel(Mt, 1)));
      perm[i] = 1;
      for (j = 2; j <= N; j++)
      {
        GEN thisnorm = gnorml2(gsub(vec, gel(Mt, j)));
        if (gcmp(thisnorm, minnorm) < 0)
        {
          minnorm = thisnorm;
          perm[i] = j >= r1plusr2 ? r2-j : j;
        }
      }
    }
    for (permprec = perm, m = 2; m < lg(thiscyc); m++)
    {
      GEN thisperm = gel(perms, thiscyc[m]);
      for (i = 1; i < r1plusr2; i++)
      {
        long pp = labs(permprec[i]);
        thisperm[i] = permprec[i] < 0 ? -perm[pp] : perm[pp];
      }
      permprec = thisperm;
    }
  }
  avma = av;
  return perms;
}

/* Determine the field automorphisms and its matrix in the integral basis. */
static GEN
automorphism_matrices(GEN nf, GEN *invp, GEN *cycp)
{
  pari_sp av = avma;
  GEN auts = galoisconj(nf, NULL), mats, cyclic, cyclicidx;
  GEN invs;
  long nauts = lg(auts)-1, i, j, k, l;

  cyclic = cgetg(nauts+1, t_VEC);
  cyclicidx = zero_Flv(nauts);
  invs = zero_Flv(nauts-1);
  for (l = 1; l <= nauts; l++)
  {
    GEN aut = gel(auts, l);
    if (gequalX(aut)) { swap(gel(auts, l), gel(auts, nauts)); break; }
  }
  /* trivial automorphism is last */
  for (l = 1; l <= nauts; l++) gel(auts, l) = algtobasis(nf, gel(auts, l));
  /* Compute maximal cyclic subgroups */
  for (l = nauts; --l > 0; )
    if (!cyclicidx[l])
    {
      GEN elt = gel(auts, l), aut = elt, cyc = cgetg(nauts+1, t_VECSMALL);
      cyclicidx[l] = l;
      cyc[1] = l;
      j = 1;
      do
      {
        elt = galoisapply(nf, elt, aut);
        for (k = 1; k <= nauts; k++) if (gequal(elt, gel(auts, k))) break;
        cyclicidx[k] = l;
        cyc[++j] = k;
      }
      while (k != nauts);
      setlg(cyc, j);
      gel(cyclic, l) = cyc;
      /* Store the inverses */
      for (i = 1; i <= j/2; i++)
      {
        invs[cyc[i]] = cyc[j-i];
        invs[cyc[j-i]] = cyc[i];
      }
    }
  for (i = j = 1; i < nauts; i++)
    if (cyclicidx[i] == i) cyclic[j++] = cyclic[i];
  setlg(cyclic, j);
  mats = cgetg(nauts, t_VEC);
  while (--j > 0)
  {
    GEN cyc = gel(cyclic, j);
    long id = cyc[1];
    GEN M, Mi, aut = gel(auts, id);

    gel(mats, id) = Mi = M = nfgaloismatrix(nf, aut);
    for (i = 2; i < lg(cyc); i++)
    {
      Mi = ZM_mul(Mi, M);
      gel(mats, cyc[i]) = Mi;
    }
  }
  gerepileall(av, 3, &mats, &invs, &cyclic);
  if (invp) *invp = invs;
  if (cycp) *cycp = cyclic;
  return mats;
}

/* vP a list of maximal ideals above the same p from idealprimedec: f(P/p) is
 * increasing; 1 <= j <= #vP; orbit a zc of length <= #vP; auts a vector of
 * automorphisms in ZM form.
 * Set orbit[i] = 1 for all vP[i], i >= j, in the orbit of pr = vP[j] wrt auts.
 * N.B.1 orbit need not be initialized to 0: useful to incrementally run
 * through successive orbits
 * N.B.2 i >= j, so primes with index < j will be missed; run incrementally
 * starting from j = 1 ! */
static void
pr_orbit_fill(GEN orbit, GEN auts, GEN vP, long j)
{
  GEN pr = gel(vP,j), gen = pr_get_gen(pr);
  long i, l = lg(auts), J = lg(orbit), f = pr_get_f(pr);
  orbit[j] = 1;
  for (i = 1; i < l; i++)
  {
    GEN g = ZM_ZC_mul(gel(auts,i), gen);
    long k;
    for (k = j+1; k < J; k++)
    {
      GEN prk = gel(vP,k);
      if (pr_get_f(prk) > f) break; /* f(P[k]) increases with k */
      /* don't check that e matches: (almost) always 1 ! */
      if (!orbit[k] && ZC_prdvd(g, prk)) { orbit[k] = 1; break; }
    }
  }
}
/* remark: F->KCZ changes if be_honest() fails */
static int
be_honest(FB_t *F, GEN nf, GEN auts, FACT *fact)
{
  long ex, i, iz, nbtest;
  long lgsub = lg(F->subFB), KCZ0 = F->KCZ;
  long N = nf_get_degree(nf), prec = nf_get_prec(nf);
  GEN M = nf_get_M(nf), G = nf_get_G(nf);
  FP_t fp;
  pari_sp av;

  if (DEBUGLEVEL) {
    err_printf("Be honest for %ld primes from %ld to %ld\n", F->KCZ2 - F->KCZ,
               F->FB[ F->KCZ+1 ], F->FB[ F->KCZ2 ]);
  }
  minim_alloc(N+1, &fp.q, &fp.x, &fp.y, &fp.z, &fp.v);
  if (lg(auts) == 1) auts = NULL;
  av = avma;
  for (iz=F->KCZ+1; iz<=F->KCZ2; iz++, avma = av)
  {
    long p = F->FB[iz];
    GEN pr_orbit, P = F->LV[p];
    long j, J = lg(P); /* > 1 */
    /* the P|p, NP > C2 are assumed in subgroup generated by FB + last P
     * with NP <= C2 is unramified --> check all but last */
    if (pr_get_e(gel(P,J-1)) == 1) J--;
    if (J == 1) continue;
    if (DEBUGLEVEL>1) err_printf("%ld ", p);
    pr_orbit = auts? zero_zv(J-1): NULL;
    for (j = 1; j < J; j++)
    {
      GEN ideal, ideal0;
      if (pr_orbit)
      {
        if (pr_orbit[j]) continue;
        /* discard all primes in automorphism orbit simultaneously */
        pr_orbit_fill(pr_orbit, auts, P, j);
      }
      ideal = ideal0 = pr_hnf(nf,gel(P,j));
      for (nbtest=0;;)
      {
        if (Fincke_Pohst_ideal(NULL, F, nf, M, G, ideal, fact, 0, &fp,
                               NULL, prec, NULL, NULL)) break;
        if (++nbtest > maxtry_HONEST)
        {
          if (DEBUGLEVEL)
            pari_warn(warner,"be_honest() failure on prime %Ps\n", gel(P,j));
          return 0;
        }
        /* occurs at most once in the whole function */
        if (F->newpow) powFBgen(NULL, F, nf, auts);
        for (i = 1, ideal = ideal0; i < lgsub; i++)
        {
          long id = F->subFB[i];
          ex = random_bits(RANDOM_BITS);
          if (ex) ideal = idealHNF_mul(nf,ideal, gmael(F->id2,id,ex));
        }
        ideal = remove_content(ideal);
        if (expi(gcoeff(ideal,1,1)) > 100) ideal = idealred(nf, ideal);
      }
    }
    F->KCZ++; /* SUCCESS, "enlarge" factorbase */
  }
  F->KCZ = KCZ0; avma = av; return 1;
}

/* all primes with N(P) <= BOUND factor on factorbase ? */
void
bnftestprimes(GEN bnf, GEN BOUND)
{
  pari_sp av0 = avma, av;
  ulong count = 0;
  GEN auts, p, nf = bnf_get_nf(bnf), Vbase = bnf_get_vbase(bnf);
  GEN fb = gen_sort(Vbase, (void*)&cmp_prime_ideal, cmp_nodata); /*tablesearch*/
  ulong pmax = itou( pr_get_p(gel(fb, lg(fb)-1)) ); /*largest p in factorbase*/
  forprime_t S;
  FACT *fact;
  FB_t F;

  (void)recover_partFB(&F, Vbase, nf_get_degree(nf));
  fact = (FACT*)stack_malloc((F.KC+1)*sizeof(FACT));
  forprime_init(&S, gen_2, BOUND);
  auts = automorphism_matrices(nf, NULL, NULL);
  if (lg(auts) == 1) auts = NULL;
  av = avma;
  while (( p = forprime_next(&S) ))
  {
    GEN pr_orbit, vP;
    long j, J;

    if (DEBUGLEVEL == 1 && ++count > 1000)
    {
      err_printf("passing p = %Ps / %Ps\n", p, BOUND);
      count = 0;
    }
    avma = av;
    vP = idealprimedec_limit_norm(bnf, p, BOUND);
    J = lg(vP);
    /* if last is unramified, all P|p in subgroup generated by FB: skip last */
    if (J > 1 && pr_get_e(gel(vP,J-1)) == 1) J--;
    if (J == 1) continue;
    if (DEBUGLEVEL>1) err_printf("*** p = %Ps\n",p);
    pr_orbit = auts? zero_zv(J-1): NULL;
    for (j = 1; j < J; j++)
    {
      GEN P = gel(vP,j);
      long k;
      if (pr_orbit)
      {
        if (pr_orbit[j]) continue;
        /* discard all primes in automorphism orbit simultaneously */
        pr_orbit_fill(pr_orbit, auts, vP, j);
      }
      if (DEBUGLEVEL>1) err_printf("  Testing P = %Ps\n",P);
      if (abscmpiu(p, pmax) <= 0 && (k = tablesearch(fb, P, &cmp_prime_ideal)))
      { if (DEBUGLEVEL>1) err_printf("    #%ld in factor base\n",k); }
      else if (DEBUGLEVEL>1)
        err_printf("    is %Ps\n", isprincipal(bnf,P));
      else /* faster: don't compute result */
        (void)SPLIT(&F, nf, pr_hnf(nf,P), Vbase, fact);
    }
  }
  avma = av0;
}

/* A t_MAT of complex floats, in fact reals. Extract a submatrix B
 * whose columns are definitely non-0, i.e. gexpo(A[j]) >= -2
 *
 * If possible precision problem (t_REAL 0 with large exponent), set
 * *precpb to 1 */
static GEN
clean_cols(GEN A, int *precpb)
{
  long l = lg(A), h, i, j, k;
  GEN B;
  *precpb = 0;
  if (l == 1) return A;
  h = lgcols(A);;
  B = cgetg(l, t_MAT);
  for (i = k = 1; i < l; i++)
  {
    GEN Ai = gel(A,i);
    int non0 = 0;
    for (j = 1; j < h; j++)
    {
      GEN c = gel(Ai,j);
      if (gexpo(c) >= -2)
      {
        if (gequal0(c)) *precpb = 1; else non0 = 1;
      }
    }
    if (non0) gel(B, k++) = Ai;
  }
  setlg(B, k); return B;
}

static long
compute_multiple_of_R_pivot(GEN X, GEN x0/*unused*/, long ix, GEN c)
{
  GEN x = gel(X,ix);
  long i, k = 0, ex = - (long)HIGHEXPOBIT, lx = lg(x);
  (void)x0;
  for (i=1; i<lx; i++)
    if (!c[i] && !gequal0(gel(x,i)))
    {
      long e = gexpo(gel(x,i));
      if (e > ex) { ex = e; k = i; }
    }
  return (k && ex > -32)? k: lx;
}

/* A = complex logarithmic embeddings of units (u_j) found so far,
 * RU = R1+R2 = unit rank, N = field degree
 * need = unit rank defect
 * L = NULL (prec problem) or B^(-1) * A with approximate rational entries
 * (as t_REAL), B a submatrix of A, with (probably) maximal rank RU */
static GEN
compute_multiple_of_R(GEN A, long RU, long N, long *pneed, long *bit, GEN *ptL)
{
  GEN T, d, mdet, Im_mdet, kR, xreal, L;
  long i, j, r, R1 = 2*RU - N;
  int precpb;
  pari_sp av = avma;

  if (RU == 1) { *ptL = zeromat(0, lg(A)-1); return gen_1; }

  if (DEBUGLEVEL) err_printf("\n#### Computing regulator multiple\n");
  xreal = real_i(A); /* = (log |sigma_i(u_j)|) */
  mdet = clean_cols(xreal, &precpb);
  /* will cause precision to increase on later failure, but we may succeed! */
  *ptL = precpb? NULL: gen_1;
  T = cgetg(RU+1,t_COL);
  for (i=1; i<=R1; i++) gel(T,i) = gen_1;
  for (   ; i<=RU; i++) gel(T,i) = gen_2;
  mdet = shallowconcat(T, mdet); /* det(Span(mdet)) = N * R */

  /* could be using indexrank(), but need custom "get_pivot" function */
  d = RgM_pivots(mdet, NULL, &r, &compute_multiple_of_R_pivot);
  /* # of independent columns == unit rank ? */
  if (lg(mdet)-1 - r != RU)
  {
    if (DEBUGLEVEL)
      err_printf("Unit group rank = %ld < %ld\n",lg(mdet)-1 - r, RU);
    *pneed = RU - (lg(mdet)-1-r);
    avma = av; return NULL;
  }

  Im_mdet = cgetg(RU+1, t_MAT); /* extract independent columns */
  /* N.B: d[1] = 1, corresponding to T above */
  gel(Im_mdet, 1) = T;
  for (i = j = 2; i <= RU; j++)
    if (d[j]) gel(Im_mdet, i++) = gel(mdet,j);

  /* integral multiple of R: the cols we picked form a Q-basis, they have an
   * index in the full lattice. First column is T */
  kR = divru(det2(Im_mdet), N);
  /* R > 0.2 uniformly */
  if (!signe(kR) || expo(kR) < -3) { avma=av; *pneed = 0; return NULL; }

  setabssign(kR);
  L = RgM_inv(Im_mdet);
  if (!L) { *ptL = NULL; return kR; }
  /* estimate for # of correct bits in result */
  *bit = - gexpo(RgM_Rg_sub(RgM_mul(L,Im_mdet), gen_1));

  L = rowslice(L, 2, RU); /* remove first line */
  L = RgM_mul(L, xreal); /* approximate rational entries */
  gerepileall(av,2, &L, &kR);
  *ptL = L; return kR;
}

/* leave small integer n as is, convert huge n to t_REAL (for readability) */
static GEN
i2print(GEN n)
{ return lgefint(n) <= DEFAULTPREC? n: itor(n,LOWDEFAULTPREC); }

static long
bad_check(GEN c)
{
  long ec = gexpo(c);
  if (DEBUGLEVEL) err_printf("\n ***** check = %.28Pg\n",c);
  /* safe check for c < 0.75 : avoid underflow in gtodouble() */
  if (ec < -1 || (ec == -1 && gtodouble(c) < 0.75)) return fupb_PRECI;
  /* safe check for c > 1.3 : avoid overflow */
  if (ec > 0 || (ec == 0 && gtodouble(c) > 1.3)) return fupb_RELAT;
  return fupb_NONE;
}
/* Input:
 * lambda = approximate rational entries: coords of units found so far on a
 * sublattice of maximal rank (sublambda)
 * *ptkR = regulator of sublambda = multiple of regulator of lambda
 * Compute R = true regulator of lambda.
 *
 * If c := Rz ~ 1, by Dirichlet's formula, then lambda is the full group of
 * units AND the full set of relations for the class group has been computed.
 *
 * In fact z is a very rough approximation and we only expect 0.75 < Rz < 1.3
 * bit is an estimate for the actual accuracy of lambda
 *
 * Output: *ptkR = R, *ptU = basis of fundamental units (in terms lambda) */
static int
compute_R(GEN lambda, long RU, GEN z, long bit, GEN *ptL, GEN *ptkR)
{
  pari_sp av = avma;
  long r, reason;
  GEN L, H, D, den, R, c;

  *ptL = NULL;
  if (DEBUGLEVEL) { err_printf("\n#### Computing check\n"); err_flush(); }
  if (RU == 1) { *ptkR = gen_1; *ptL = lambda; return bad_check(z); }
  D = gmul2n(mpmul(*ptkR,z), 1); /* bound for denom(lambda) */
  if (expo(D) < 0 && rtodbl(D) < 0.95) return fupb_PRECI;
  lambda = bestappr(lambda,D);
  if (lg(lambda) == 1)
  {
    if (DEBUGLEVEL) err_printf("truncation error in bestappr\n");
    return fupb_PRECI;
  }
  den = Q_denom(lambda);
  if (mpcmp(den,D) > 0)
  {
    if (DEBUGLEVEL) err_printf("D = %Ps\nden = %Ps\n",D, i2print(den));
    return fupb_PRECI;
  }
  L = Q_muli_to_int(lambda, den);
  if (RU > 5) bit -= 64;
  else if (RU > 3) bit -= 32;
  if (gexpo(L) + expi(den) > bit)
  {
    if (DEBUGLEVEL) err_printf("dubious bestappr; den = %Ps\n", i2print(den));
    return fupb_PRECI;
  }
  H = ZM_hnf(L); r = lg(H)-1;
  if (!r || r != nbrows(H))
    R = gen_0; /* wrong rank */
  else
    R = gmul(*ptkR, gdiv(ZM_det_triangular(H), powiu(den, r)));
  /* R = tentative regulator; regulator > 0.2 uniformly */
  if (gexpo(R) < -3) {
    if (DEBUGLEVEL) err_printf("\n#### Tentative regulator: %.28Pg\n", R);
    avma = av; return fupb_PRECI;
  }
  c = gmul(R,z); /* should be n (= 1 if we are done) */
  if (DEBUGLEVEL) err_printf("\n#### Tentative regulator: %.28Pg\n", R);
  if ((reason = bad_check(c))) { avma = av; return reason; }
  *ptkR = R; *ptL = L; return fupb_NONE;
}

/* norm of an extended ideal I, whose 1st component is in integral HNF */
static GEN
idnorm(GEN I) { return ZM_det_triangular(gel(I,1)); }

/* find the smallest (wrt norm) among I, I^-1 and red(I^-1) */
static GEN
inverse_if_smaller(GEN nf, GEN I)
{
  GEN d, dmin, I1;

  dmin = idnorm(I);
  I1 = idealinv(nf,I); gel(I1,1) = Q_remove_denom(gel(I1,1), NULL);
  d = idnorm(I1); if (cmpii(d,dmin) < 0) {I=I1; dmin=d;}
  /* try reducing (often _increases_ the norm) */
  I1 = idealred(nf,I1);
  d = idnorm(I1); if (cmpii(d,dmin) < 0) I=I1;
  return I;
}

/* in place */
static void
neg_row(GEN U, long i)
{
  GEN c = U + lg(U)-1;
  for (; c>U; c--) gcoeff(c,i,0) = negi(gcoeff(c,i,0));
}

static void
setlg_col(GEN U, long l)
{
  GEN c = U + lg(U)-1;
  for (; c>U; c--) setlg(*c, l);
}

/* compute class group (clg1) + data for isprincipal (clg2) */
static void
class_group_gen(GEN nf,GEN W,GEN C,GEN Vbase,long prec, GEN nf0,
                GEN *ptclg1,GEN *ptclg2)
{
  GEN z, G, Ga, ga, GD, cyc, X, Y, D, U, V, Ur, Ui, Uir, I, J, arch;
  long i, j, lo, lo0;
  pari_timer T;

  if (DEBUGLEVEL) timer_start(&T);
  D = ZM_snfall(W,&U,&V); /* UWV=D, D diagonal, G = g Ui (G=new gens, g=old) */
  Ui = ZM_inv(U, NULL);
  lo0 = lo = lg(D);
 /* we could set lo = lg(cyc) and truncate all matrices below
  *   setlg_col(D && U && Y, lo) + setlg(D && V && X && Ui, lo)
  * but it's not worth the complication:
  * 1) gain is negligible (avoid computing z^0 if lo < lo0)
  * 2) when computing ga, the products XU and VY use the original matrices */
  Ur  = ZM_hnfdivrem(U, D, &Y);
  Uir = ZM_hnfdivrem(Ui,W, &X);
 /* [x] = logarithmic embedding of x (arch. component)
  * NB: z = idealred(I) --> I = y z[1], with [y] = - z[2]
  * P invertible diagonal matrix (\pm 1) which is only implicitly defined
  * G = g Uir P + [Ga],  Uir = Ui + WX
  * g = G P Ur  + [ga],  Ur  = U + DY */
  G = cgetg(lo,t_VEC);
  Ga= cgetg(lo,t_VEC);
  z = init_famat(NULL);
  if (!nf0) nf0 = nf;
  for (j=1; j<lo; j++)
  {
    GEN v = gel(Uir,j);
    GEN p1 = gel(v,1);
    gel(z,1) = gel(Vbase,1); I = idealpowred(nf0,z,p1);
    for (i=2; i<lo0; i++)
    {
      p1 = gel(v,i);
      if (signe(p1))
      {
        gel(z,1) = gel(Vbase,i);
        I = idealHNF_mulred(nf0, I, idealpowred(nf0,z,p1));
      }
    }
    J = inverse_if_smaller(nf0, I);
    if (J != I)
    { /* update wrt P */
      neg_row(Y ,j); gel(V,j) = ZC_neg(gel(V,j));
      neg_row(Ur,j); gel(X,j) = ZC_neg(gel(X,j));
    }
    gel(G,j) = gel(J,1); /* generator, order cyc[j] */
    arch = famat_to_arch(nf, gel(J,2), prec);
    if (!arch) pari_err_PREC("class_group_gen");
    gel(Ga,j) = gneg(arch);
  }
  /* at this point Y = PY, Ur = PUr, V = VP, X = XP */

  /* G D =: [GD] = g (UiP + W XP) D + [Ga]D = g W (VP + XP D) + [Ga]D
   * NB: DP = PD and Ui D = W V. gW is given by (first lo0-1 cols of) C
   */
  GD = gadd(act_arch(ZM_add(V, ZM_mul(X,D)), C), act_arch(D, Ga));
  /* -[ga] = [GD]PY + G PU - g = [GD]PY + [Ga] PU + gW XP PU
                               = gW (XP PUr + VP PY) + [Ga]PUr */
  ga = gadd(act_arch(ZM_add(ZM_mul(X,Ur), ZM_mul(V,Y)), C),
            act_arch(Ur, Ga));
  ga = gneg(ga);
  /* TODO: could (LLL)reduce ga and GD mod units ? */

  cyc = cgetg(lo,t_VEC); /* elementary divisors */
  for (j=1; j<lo; j++)
  {
    gel(cyc,j) = gcoeff(D,j,j);
    if (gequal1(gel(cyc,j)))
    { /* strip useless components */
      lo = j; setlg(cyc,lo); setlg_col(Ur,lo);
      setlg(G,lo); setlg(Ga,lo); setlg(GD,lo); break;
    }
  }
  *ptclg1 = mkvec3(ZM_det_triangular(W), cyc, G);
  *ptclg2 = mkvec3(Ur, ga, GD);
  if (DEBUGLEVEL) timer_printf(&T, "classgroup generators");
}

/* SMALLBUCHINIT */

static GEN
decodeprime(GEN T, GEN L, long n)
{
  long t = itos(T);
  return gmael(L, t/n, t%n + 1);
}
static GEN
codeprime(GEN L, long N, GEN pr)
{
  long p = pr_get_smallp(pr);
  return utoipos( N*p + pr_index(gel(L,p), pr)-1 );
}

static GEN
decode_pr_lists(GEN nf, GEN pfc)
{
  long i, n = nf_get_degree(nf), l = lg(pfc);
  GEN L, P = cgetg(l, t_VECSMALL), Vbase = cgetg(l, t_COL);

  for (i = 1; i < l; i++) P[i] = itou(gel(pfc,i)) / n;
  L = const_vec(vecsmall_max(P), NULL);
  for (i = 1; i < l; i++)
  {
    long p = P[i];
    if (!gel(L,p)) gel(L,p) = idealprimedec(nf, utoipos(p));
  }
  for (i = 1; i < l; i++) gel(Vbase,i) = decodeprime(gel(pfc,i), L, n);
  return Vbase;
}

static GEN
codeprimes(GEN Vbase, long N)
{
  GEN v, L = get_pr_lists(Vbase, N, 1);
  long i, l = lg(Vbase);
  v = cgetg(l, t_VEC);
  for (i=1; i<l; i++) gel(v,i) = codeprime(L, N, gel(Vbase,i));
  return v;
}

/* compute principal ideals corresponding to (gen[i]^cyc[i]) */
static GEN
makecycgen(GEN bnf)
{
  GEN cyc,gen,h,nf,y,GD;
  long e,i,l;

  if (DEBUGLEVEL) pari_warn(warner,"completing bnf (building cycgen)");
  nf = bnf_get_nf(bnf);
  cyc = bnf_get_cyc(bnf);
  gen = bnf_get_gen(bnf); GD = gmael(bnf,9,3);
  h = cgetg_copy(gen, &l);
  for (i=1; i<l; i++)
  {
    GEN gi = gel(gen,i), ci = gel(cyc,i);
    if (abscmpiu(ci, 5) < 0)
    {
      GEN N = ZM_det_triangular(gi);
      y = isprincipalarch(bnf,gel(GD,i), N, ci, gen_1, &e);
      if (y && fact_ok(nf,y,NULL,mkvec(gi),mkvec(ci)))
      {
        gel(h,i) = to_famat_shallow(y,gen_1);
        continue;
      }
    }
    y = isprincipalfact(bnf, NULL, mkvec(gi), mkvec(ci), nf_GENMAT|nf_FORCE);
    h[i] = y[2];
  }
  return h;
}

static GEN
get_y(GEN bnf, GEN W, GEN B, GEN C, GEN pFB, long j)
{
  GEN y, nf  = bnf_get_nf(bnf);
  long e, lW = lg(W)-1;
  GEN ex = (j<=lW)? gel(W,j): gel(B,j-lW);
  GEN P = (j<=lW)? NULL: gel(pFB,j);
  if (C)
  { /* archimedean embeddings known: cheap trial */
    GEN Nx = get_norm_fact_primes(pFB, ex, P);
    y = isprincipalarch(bnf,gel(C,j), Nx,gen_1, gen_1, &e);
    if (y && fact_ok(nf,y,P,pFB,ex)) return y;
  }
  y = isprincipalfact_or_fail(bnf, P, pFB, ex);
  return typ(y) == t_INT? y: gel(y,2);
}
/* compute principal ideals corresponding to bnf relations */
static GEN
makematal(GEN bnf)
{
  GEN W = bnf_get_W(bnf), B = bnf_get_B(bnf), C = bnf_get_C(bnf);
  GEN pFB, ma, retry;
  long lma, j, prec = 0;

  if (DEBUGLEVEL) pari_warn(warner,"completing bnf (building matal)");
  lma=lg(W)+lg(B)-1;
  pFB = bnf_get_vbase(bnf);
  ma = cgetg(lma,t_VEC);
  retry = vecsmalltrunc_init(lma);
  for (j=lma-1; j>0; j--)
  {
    pari_sp av = avma;
    GEN y = get_y(bnf, W, B, C, pFB, j);
    if (typ(y) == t_INT)
    {
      long E = itos(y);
      if (DEBUGLEVEL>1) err_printf("\n%ld done later at prec %ld\n",j,E);
      avma = av;
      vecsmalltrunc_append(retry, j);
      if (E > prec) prec = E;
    }
    else
    {
      if (DEBUGLEVEL>1) err_printf("%ld ",j);
      gel(ma,j) = gerepileupto(av,y);
    }
  }
  if (prec)
  {
    long k, l = lg(retry);
    GEN y, nf = bnf_get_nf(bnf);
    if (DEBUGLEVEL) pari_warn(warnprec,"makematal",prec);
    nf = nfnewprec_shallow(nf,prec);
    bnf = Buchall(nf, nf_FORCE, prec);
    if (DEBUGLEVEL) err_printf("makematal, adding missing entries:");
    for (k=1; k<l; k++)
    {
      pari_sp av = avma;
      long j = retry[k];
      y = get_y(bnf,W,B,NULL, pFB, j);
      if (typ(y) == t_INT) pari_err_PREC("makematal");
      if (DEBUGLEVEL>1) err_printf("%ld ",j);
      gel(ma,j) = gerepileupto(av,y);
    }
  }
  if (DEBUGLEVEL>1) err_printf("\n");
  return ma;
}

enum { MATAL = 1, CYCGEN, UNITS };

GEN
bnf_build_cycgen(GEN bnf)
{ return obj_checkbuild(bnf, CYCGEN, &makecycgen); }
GEN
bnf_build_matalpha(GEN bnf)
{ return obj_checkbuild(bnf, MATAL, &makematal); }
GEN
bnf_build_units(GEN bnf)
{ return obj_checkbuild(bnf, UNITS, &makeunits); }

static GEN
get_regulator(GEN mun)
{
  pari_sp av = avma;
  GEN R;

  if (lg(mun) == 1) return gen_1;
  R = det( rowslice(real_i(mun), 1, lgcols(mun)-2) );
  setabssign(R); return gerepileuptoleaf(av, R);
}

/* return corrected archimedian components for elts of x (vector)
 * (= log(sigma_i(x)) - log(|Nx|) / [K:Q]) */
static GEN
get_archclean(GEN nf, GEN x, long prec, int units)
{
  long k,N, la = lg(x);
  GEN M = cgetg(la,t_MAT);

  if (la == 1) return M;
  N = nf_get_degree(nf);
  for (k=1; k<la; k++)
  {
    pari_sp av = avma;
    GEN c = get_arch(nf, gel(x,k), prec);
    if (!c) return NULL;
    if (!units) {
      c = cleanarch(c, N, prec);
      if (!c) return NULL;
    }
    settyp(c,t_COL);
    gel(M,k) = gerepilecopy(av, c);
  }
  return M;
}

static void
my_class_group_gen(GEN bnf, long prec, GEN nf0, GEN *ptcl, GEN *ptcl2)
{
  GEN W = bnf_get_W(bnf), C = bnf_get_C(bnf), nf = bnf_get_nf(bnf);
  class_group_gen(nf,W,C,bnf_get_vbase(bnf),prec,nf0, ptcl,ptcl2);
}

GEN
bnfnewprec_shallow(GEN bnf, long prec)
{
  GEN nf0 = bnf_get_nf(bnf), nf, res, fu, mun, gac, matal, clgp, clgp2, y;
  long r1, r2, prec1;

  nf_get_sign(nf0, &r1, &r2);
  fu = bnf_build_units(bnf);
  fu = vecslice(fu, 2, lg(fu)-1);

  prec1 = prec;
  if (r1 + r2 > 1) {
    long e = gexpo(bnf_get_logfu(bnf)) + 1 - TWOPOTBITS_IN_LONG;
    if (e >= 0) prec += nbits2extraprec(e);
  }
  if (DEBUGLEVEL && prec1!=prec) pari_warn(warnprec,"bnfnewprec",prec);
  matal = bnf_build_matalpha(bnf);
  for(;;)
  {
    pari_sp av = avma;
    nf = nfnewprec_shallow(nf0,prec);
    mun = get_archclean(nf, fu, prec, 1);
    if (mun)
    {
      gac = get_archclean(nf, matal, prec, 0);
      if (gac) break;
    }
    avma = av; prec = precdbl(prec);
    if (DEBUGLEVEL) pari_warn(warnprec,"bnfnewprec(extra)",prec);
  }
  y = leafcopy(bnf);
  gel(y,3) = mun;
  gel(y,4) = gac;
  gel(y,7) = nf;
  my_class_group_gen(y,prec,nf0, &clgp,&clgp2);
  res = leafcopy(gel(bnf,8));
  gel(res,1) = clgp;
  gel(res,2) = get_regulator(mun);
  gel(y,8) = res;
  gel(y,9) = clgp2; return y;
}
GEN
bnfnewprec(GEN bnf, long prec)
{
  pari_sp av = avma;
  return gerepilecopy(av, bnfnewprec_shallow(checkbnf(bnf), prec));
}

GEN
bnrnewprec_shallow(GEN bnr, long prec)
{
  GEN y = cgetg(7,t_VEC);
  long i;
  gel(y,1) = bnfnewprec_shallow(bnr_get_bnf(bnr), prec);
  for (i=2; i<7; i++) gel(y,i) = gel(bnr,i);
  return y;
}
GEN
bnrnewprec(GEN bnr, long prec)
{
  GEN y = cgetg(7,t_VEC);
  long i;
  checkbnr(bnr);
  gel(y,1) = bnfnewprec(bnr_get_bnf(bnr), prec);
  for (i=2; i<7; i++) gel(y,i) = gcopy(gel(bnr,i));
  return y;
}

static GEN
get_clfu(GEN clgp, GEN reg, GEN zu, GEN fu)
{
  if (!fu) fu = cgetg(1,t_MAT);
  return mkvec5(clgp, reg, gen_1/*DUMMY*/, zu, fu);
}

static GEN
buchall_end(GEN nf,GEN res, GEN clg2, GEN W, GEN B, GEN A, GEN C,GEN Vbase)
{
  GEN z = obj_init(9, 3);
  gel(z,1) = W;
  gel(z,2) = B;
  gel(z,3) = A;
  gel(z,4) = C;
  gel(z,5) = Vbase;
  gel(z,6) = gen_0;
  gel(z,7) = nf;
  gel(z,8) = res;
  gel(z,9) = clg2;
  return z;
}

/* FIXME: obsolete function */
GEN
bnfcompress(GEN bnf)
{
  pari_sp av = avma;
  GEN nf, fu, y = cgetg(13,t_VEC);

  bnf = checkbnf(bnf);
  nf = bnf_get_nf(bnf);
  gel(y,1) = nf_get_pol(nf);
  gel(y,2) = gmael(nf,2,1);
  gel(y,3) = nf_get_disc(nf);
  gel(y,4) = nf_get_zk(nf);
  gel(y,5) = nf_get_roots(nf);
  gel(y,6) = gen_0; /* FIXME: unused */
  gel(y,7) = bnf_get_W(bnf);
  gel(y,8) = bnf_get_B(bnf);
  gel(y,9) = codeprimes(bnf_get_vbase(bnf), nf_get_degree(nf));
  gel(y,10) = mkvec2(utoipos(bnf_get_tuN(bnf)),
                     nf_to_scalar_or_basis(nf, bnf_get_tuU(bnf)));
  fu = bnf_build_units(bnf); fu = vecslice(fu,2,lg(fu)-1);
  gel(y,11) = fu;
  gel(y,12) = bnf_build_matalpha(bnf);
  return gerepilecopy(av, y);
}

/* FIXME: obsolete feature */
static GEN
sbnf2bnf(GEN sbnf, long prec)
{
  pari_sp av = avma;
  GEN ro, nf, A, fu, FU, C, clgp, clgp2, res, y, W, zu, matal, Vbase;
  long k, l;
  nfmaxord_t S;

  if (typ(sbnf) != t_VEC || lg(sbnf) != 13) pari_err_TYPE("bnfmake",sbnf);
  if (prec < DEFAULTPREC) prec = DEFAULTPREC;

  S.T0 = S.T = gel(sbnf,1);
  S.r1    = itos(gel(sbnf,2));
  S.dK    = gel(sbnf,3);
  S.basis = gel(sbnf,4);
  S.index = NULL;
  S.dT    = NULL;
  S.dKP   = NULL;
  S.basden= NULL;
  ro = gel(sbnf,5); if (prec > gprecision(ro)) ro = NULL;
  nf = nfmaxord_to_nf(&S, ro, prec);

  fu = gel(sbnf,11);
  A = get_archclean(nf, fu, prec, 1);
  if (!A) pari_err_PREC("bnfmake");

  prec = nf_get_prec(nf);
  matal = gel(sbnf,12);
  C = get_archclean(nf,matal,prec,0);
  if (!C) pari_err_PREC("bnfmake");

  Vbase = decode_pr_lists(nf, gel(sbnf,9));
  W = gel(sbnf,7);
  class_group_gen(nf,W,C,Vbase,prec,NULL, &clgp,&clgp2);

  zu = gel(sbnf,10);
  zu = mkvec2(gel(zu,1), nf_to_scalar_or_alg(nf, gel(zu,2)));
  FU = cgetg_copy(fu, &l);
  for (k=1; k < l; k++) gel(FU,k) = nf_to_scalar_or_alg(nf, gel(fu,k));

  res = get_clfu(clgp, get_regulator(A), zu, FU);
  y = buchall_end(nf,res,clgp2,W,gel(sbnf,8),A,C,Vbase);
  return gerepilecopy(av,y);
}

GEN
bnfinit0(GEN P, long flag, GEN data, long prec)
{
  double c1 = BNF_C1, c2 = BNF_C2;
  long fl, relpid = BNF_RELPID;

  if (typ(P) == t_VEC && lg(P) == 13) return sbnf2bnf(P, prec); /* sbnf */
  if (data)
  {
    long lx = lg(data);
    if (typ(data) != t_VEC || lx > 5) pari_err_TYPE("bnfinit",data);
    switch(lx)
    {
      case 4: relpid = itos(gel(data,3));
      case 3: c2 = gtodouble(gel(data,2));
      case 2: c1 = gtodouble(gel(data,1));
    }
  }
  switch(flag)
  {
    case 2:
    case 0: fl = 0; break;
    case 1: fl = nf_FORCE; break;
    default: pari_err_FLAG("bnfinit");
      return NULL; /* LCOV_EXCL_LINE */
  }
  return Buchall_param(P, c1, c2, relpid, fl, prec);
}
GEN
Buchall(GEN P, long flag, long prec)
{ return Buchall_param(P, BNF_C1, BNF_C2, BNF_RELPID, flag, prec); }

static GEN
Buchall_deg1(GEN nf)
{
  GEN v = cgetg(1,t_VEC), m = cgetg(1,t_MAT);
  GEN W, A, B, C, Vbase, res;
  GEN fu = v, R = gen_1, zu = mkvec2(gen_2, gen_m1);
  GEN clg1 = mkvec3(gen_1,v,v), clg2 = mkvec3(m,v,v);

  W = A = B = C = m;
  Vbase = cgetg(1,t_COL);
  res = get_clfu(clg1, R, zu, fu);
  return buchall_end(nf,res,clg2,W,B,A,C,Vbase);
}

/* return (small set of) indices of columns generating the same lattice as x.
 * Assume HNF(x) is inexpensive (few rows, many columns).
 * Dichotomy approach since interesting columns may be at the very end */
GEN
extract_full_lattice(GEN x)
{
  long dj, j, k, l = lg(x);
  GEN h, h2, H, v;

  if (l < 200) return NULL; /* not worth it */

  v = vecsmalltrunc_init(l);
  H = ZM_hnf(x);
  h = cgetg(1, t_MAT);
  dj = 1;
  for (j = 1; j < l; )
  {
    pari_sp av = avma;
    long lv = lg(v);

    for (k = 0; k < dj; k++) v[lv+k] = j+k;
    setlg(v, lv + dj);
    h2 = ZM_hnf(vecpermute(x, v));
    if (ZM_equal(h, h2))
    { /* these dj columns can be eliminated */
      avma = av; setlg(v, lv);
      j += dj;
      if (j >= l) break;
      dj <<= 1;
      if (j + dj >= l) { dj = (l - j) >> 1; if (!dj) dj = 1; }
    }
    else if (dj > 1)
    { /* at least one interesting column, try with first half of this set */
      avma = av; setlg(v, lv);
      dj >>= 1; /* > 0 */
    }
    else
    { /* this column should be kept */
      if (ZM_equal(h2, H)) break;
      h = h2; j++;
    }
  }
  return v;
}

static void
init_rel(RELCACHE_t *cache, FB_t *F, long add_need)
{
  const long n = F->KC + add_need; /* expected # of needed relations */
  long i, j, k, p;
  GEN c, P;
  GEN R;

  if (DEBUGLEVEL) err_printf("KCZ = %ld, KC = %ld, n = %ld\n", F->KCZ,F->KC,n);
  reallocate(cache, 10*n + 50); /* make room for lots of relations */
  cache->chk = cache->base;
  cache->end = cache->base + n;
  cache->relsup = add_need;
  cache->last = cache->base;
  cache->missing = lg(cache->basis) - 1;
  for (i = 1; i <= F->KCZ; i++)
  { /* trivial relations (p) = prod P^e */
    p = F->FB[i]; P = F->LV[p];
    if (!isclone(P)) continue;

    /* all prime divisors in FB */
    c = zero_Flv(F->KC); k = F->iLP[p];
    R = c; c += k;
    for (j = lg(P)-1; j; j--) c[j] = pr_get_e(gel(P,j));
    add_rel(cache, F, R, k+1, /*m*/NULL, 0);
  }
}

/* Let z = \zeta_n in nf. List of not-obviously-dependent generators for
 * cyclotomic units modulo torsion in Q(z) [independent when n a prime power]:
 * - z^a - 1,  n/(a,n) not a prime power, a \nmid n unless a=1,  1 <= a < n/2
 * - (Z^a - 1)/(Z - 1),  p^k || n, Z = z^{n/p^k}, (p,a) = 1, 1 < a <= (p^k-1)/2
 */
GEN
nfcyclotomicunits(GEN nf, GEN zu)
{
  long n = itos(gel(zu, 1)), n2, lP, i, a;
  GEN z, fa, P, E, L, mz, powz;
  if (n <= 6) return cgetg(1, t_VEC);

  z = algtobasis(nf,gel(zu, 2));
  if ((n & 3) == 2) { n = n >> 1; z = ZC_neg(z); } /* ensure n != 2 (mod 4) */
  n2 = n/2;
  mz = zk_multable(nf, z); /* multiplication by z */
  powz = cgetg(n2, t_VEC); gel(powz,1) = z;
  for (i = 2; i < n2; i++) gel(powz,i) = ZM_ZC_mul(mz, gel(powz,i-1));
  /* powz[i] = z^i */

  L = vectrunc_init(n);
  fa = factoru(n);
  P = gel(fa,1); lP = lg(P);
  E = gel(fa,2);
  for (i = 1; i < lP; i++)
  { /* second kind */
    long p = P[i], k = E[i], pk = upowuu(p,k), pk2 = (pk-1) / 2;
    GEN u = gen_1;
    for (a = 2; a <= pk2; a++)
    {
      u = nfadd(nf, u, gel(powz, (n/pk) * (a-1))); /* = (Z^a-1)/(Z-1) */
      if (a % p) vectrunc_append(L, u);
    }
  }
  if (lP > 2) for (a = 1; a < n2; a++)
  { /* first kind, when n not a prime power */
    ulong p;
    if (a > 1 && (n % a == 0 || uisprimepower(n/ugcd(a,n), &p))) continue;
    vectrunc_append(L, nfadd(nf, gel(powz, a), gen_m1));
  }
  return L;
}
static void
add_cyclotomic_units(GEN nf, GEN zu, RELCACHE_t *cache, FB_t *F)
{
  pari_sp av = avma;
  GEN L = nfcyclotomicunits(nf, zu);
  long i, l = lg(L);
  if (l > 1)
  {
    GEN R = zero_Flv(F->KC);
    for(i = 1; i < l; i++) add_rel(cache, F, R, F->KC+1, gel(L,i), 0);
  }
  avma = av;
}

static void
shift_embed(GEN G, GEN Gtw, long a, long r1)
{
  long j, k, l = lg(G);
  if (a <= r1)
    for (j=1; j<l; j++) gcoeff(G,a,j) = gcoeff(Gtw,a,j);
  else
  {
    k = (a<<1) - r1;
    for (j=1; j<l; j++)
    {
      gcoeff(G,k-1,j) = gcoeff(Gtw,k-1,j);
      gcoeff(G,k  ,j) = gcoeff(Gtw,k,  j);
    }
  }
}

/* G where embeddings a and b are multiplied by 2^10 */
static GEN
shift_G(GEN G, GEN Gtw, long a, long b, long r1)
{
  GEN g = RgM_shallowcopy(G);
  if (a != b) shift_embed(g,Gtw,a,r1);
  shift_embed(g,Gtw,b,r1); return g;
}

static void
compute_vecG(GEN nf, FB_t *F, long n)
{
  GEN G0, Gtw0, vecG, G = nf_get_G(nf);
  long e, i, j, ind, r1 = nf_get_r1(nf), r = lg(G)-1;
  if (n == 1) { F->G0 = G0 = ground(G); F->vecG = mkvec( G0 ); return; }
  for (e = 32;;)
  {
    G = gmul2n(G, e);
    G0 = ground(G); if (ZM_rank(G0) == r) break; /* maximal rank ? */
  }
  Gtw0 = ground(gmul2n(G, 10));
  vecG = cgetg(1 + n*(n+1)/2,t_VEC);
  for (ind=j=1; j<=n; j++)
    for (i=1; i<=j; i++) gel(vecG,ind++) = shift_G(G0,Gtw0,i,j,r1);
  F->G0 = G0; F->vecG = vecG;
}

static GEN
trim_list(FB_t *F)
{
  pari_sp av = avma;
  GEN L_jid = F->L_jid, present = zero_Flv(F->KC);
  long i, j, imax = minss(lg(L_jid), F->KC + 1);
  GEN minidx = F->minidx, idx = cgetg(imax, t_VECSMALL);

  for (i = j = 1; i < imax; i++)
  {
    long id = minidx[L_jid[i]];

    if (!present[id])
    {
      idx[j++] = L_jid[i];
      present[id] = 1;
    }
  }
  setlg(idx, j);
  return gerepileuptoleaf(av, idx);
}

static void
try_elt(RELCACHE_t *cache, FB_t *F, GEN nf, GEN x, FACT *fact)
{
  pari_sp av = avma;
  GEN R, Nx;
  long nz, tx = typ(x);

  if (tx == t_INT || tx == t_FRAC) return;
  if (tx != t_COL) x = algtobasis(nf, x);
  if (RgV_isscalar(x)) return;
  x = Q_primpart(x);
  Nx = nfnorm(nf, x);
  if (!can_factor(F, nf, NULL, x, Nx, fact)) return;

  /* smooth element */
  R = set_fact(F, fact, NULL, &nz);
  /* make sure we get maximal rank first, then allow all relations */
  (void) add_rel(cache, F, R, nz, x, 0);
  avma = av;
}


static long
scalar_bit(GEN x) { return bit_accuracy(gprecision(x)) - gexpo(x); }
static long
RgM_bit(GEN x, long bit)
{
  long i, j, m, b = bit, l = lg(x);
  if (l == 1) return b;
  m = lgcols(x);
  for (j = 1; j < l; j++)
    for (i = 1; i < m; i++ ) b = minss(b, scalar_bit(gcoeff(x,i,j)));
  return b;
}

GEN
Buchall_param(GEN P, double cbach, double cbach2, long nbrelpid, long flun, long prec)
{
  pari_timer T;
  pari_sp av0 = avma, av, av2;
  long PRECREG, N, R1, R2, RU, low, high, LIMC0, LIMC, LIMC2, LIMCMAX, zc, i;
  long LIMres, bit;
  long MAXDEPSIZESFB, MAXDEPSFB;
  long nreldep, sfb_trials, need, old_need, precdouble = 0, precadd = 0;
  long done_small, small_fail, fail_limit, squash_index, small_norm_prec;
  long flag_nfinit = 0;
  double LOGD, LOGD2, lim;
  GEN computed = NULL, zu, nf, M_sn, D, A, W, R, h, PERM, fu = NULL /*-Wall*/;
  GEN small_multiplier;
  GEN res, L, invhr, B, C, C0, lambda, dep, clg1, clg2, Vbase;
  GEN auts, cyclic;
  const char *precpb = NULL;
  int FIRST = 1, class1 = 0;
  nfmaxord_t nfT;
  RELCACHE_t cache;
  FB_t F;
  GRHcheck_t GRHcheck;
  FACT *fact;

  if (DEBUGLEVEL) timer_start(&T);
  P = get_nfpol(P, &nf);
  if (nf)
  {
    PRECREG = nf_get_prec(nf);
    D = nf_get_disc(nf);
  }
  else
  {
    PRECREG = maxss(prec, MEDDEFAULTPREC);
    nfinit_basic(&nfT, P);
    D = nfT.dK;
    if (!ZX_is_monic(nfT.T0))
    {
      pari_warn(warner,"non-monic polynomial in bnfinit, using polredbest");
      flag_nfinit = nf_RED;
    }
  }
  N = degpol(P);
  if (N <= 1)
  {
    if (!nf) nf = nfinit_complete(&nfT, flag_nfinit, PRECREG);
    return gerepilecopy(av0, Buchall_deg1(nf));
  }
  D = absi_shallow(D);
  LOGD = dbllog2(D) * M_LN2;
  LOGD2 = LOGD*LOGD;
  LIMCMAX = (long)(12.*LOGD2);
  /* In small_norm, LLL reduction produces v0 in I such that
   *     T2(v0) <= (4/3)^((n-1)/2) NI^(2/n) disc(K)^(1/n)
   * We consider v with T2(v) <= BMULT * T2(v0)
   * Hence Nv <= ((4/3)^((n-1)/2) * BMULT / n)^(n/2) NI sqrt(disc(K)).
   * NI <= LIMCMAX^2 */
  small_norm_prec = nbits2prec( BITS_IN_LONG +
    (N/2. * ((N-1)/2.*log(4./3) + log(BMULT/(double)N))
     + 2*log((double) LIMCMAX) + LOGD/2) / M_LN2 ); /* enough to compute norms */
  if (small_norm_prec > PRECREG) PRECREG = small_norm_prec;
  if (!nf)
    nf = nfinit_complete(&nfT, flag_nfinit, PRECREG);
  else if (nf_get_prec(nf) < PRECREG)
    nf = nfnewprec_shallow(nf, PRECREG);
  M_sn = nf_get_M(nf);
  if (PRECREG > small_norm_prec) M_sn = gprec_w(M_sn, small_norm_prec);

  zu = rootsof1(nf);
  gel(zu,2) = nf_to_scalar_or_alg(nf, gel(zu,2));

  auts = automorphism_matrices(nf, &F.invs, &cyclic);
  F.embperm = automorphism_perms(nf_get_M(nf), auts, cyclic, N);

  nf_get_sign(nf, &R1, &R2); RU = R1+R2;
  compute_vecG(nf, &F, minss(RU, 9));
  if (DEBUGLEVEL)
  {
    timer_printf(&T, "nfinit & rootsof1");
    err_printf("R1 = %ld, R2 = %ld\nD = %Ps\n",R1,R2, D);
  }
  if (LOGD < 20.) /* tiny disc, Minkowski *may* be smaller than Bach */
  {
    lim = exp(-N + R2 * log(4/M_PI) + LOGD/2) * sqrt(2*M_PI*N);
    if (lim < 3) lim = 3;
  }
  else /* to be ignored */
    lim = -1;
  if (cbach > 12.) {
    if (cbach2 < cbach) cbach2 = cbach;
    cbach = 12.;
  }
  if (cbach < 0.)
    pari_err_DOMAIN("Buchall","Bach constant","<",gen_0,dbltor(cbach));

  cache.base = NULL; F.subFB = NULL; F.LP = NULL;
  init_GRHcheck(&GRHcheck, N, R1, LOGD);
  high = low = LIMC0 = maxss((long)(cbach2*LOGD2), 1);
  while (!GRHchk(nf, &GRHcheck, high))
  {
    low = high;
    high *= 2;
  }
  while (high - low > 1)
  {
    long test = (low+high)/2;
    if (GRHchk(nf, &GRHcheck, test))
      high = test;
    else
      low = test;
  }
  if (high == LIMC0+1 && GRHchk(nf, &GRHcheck, LIMC0))
    LIMC2 = LIMC0;
  else
    LIMC2 = high;
  if (LIMC2 > LIMCMAX) LIMC2 = LIMCMAX;
  if (DEBUGLEVEL) err_printf("LIMC2 = %ld\n", LIMC2);
  if (LIMC2 < nthideal(&GRHcheck, nf, 1)) class1 = 1;
  if (DEBUGLEVEL && class1) err_printf("Class 1\n", LIMC2);
  LIMC0 = (long)(cbach*LOGD2);
  LIMC = cbach ? LIMC0 : LIMC2;
  LIMC = maxss(LIMC, nthideal(&GRHcheck, nf, N));
  if (DEBUGLEVEL) timer_printf(&T, "computing Bach constant");
  LIMres = primeneeded(N, R1, R2, LOGD);
  cache_prime_dec(&GRHcheck, LIMres, nf);
  /* invhr ~ 2^r1 (2pi)^r2 / sqrt(D) w * Res(zeta_K, s=1) = 1 / hR */
  invhr = gmul(gdiv(gmul2n(powru(mppi(DEFAULTPREC), R2), RU),
              mulri(gsqrt(D,DEFAULTPREC),gel(zu,1))),
              compute_invres(&GRHcheck, LIMres));
  if (DEBUGLEVEL) timer_printf(&T, "computing inverse of hR");
  av = avma;

START:
  if (DEBUGLEVEL) timer_start(&T);
  if (!FIRST) LIMC = bnf_increase_LIMC(LIMC,LIMCMAX);
  if (DEBUGLEVEL && LIMC > LIMC0)
    err_printf("%s*** Bach constant: %f\n", FIRST?"":"\n", LIMC/LOGD2);
  if (cache.base)
  {
    REL_t *rel;
    for (i = 1, rel = cache.base + 1; rel < cache.last; rel++)
      if (rel->m) i++;
    computed = cgetg(i, t_VEC);
    for (i = 1, rel = cache.base + 1; rel < cache.last; rel++)
      if (rel->m) gel(computed, i++) = rel->m;
    computed = gclone(computed);
    delete_cache(&cache);
  }
  FIRST = 0; avma = av;
  if (F.LP) delete_FB(&F);
  if (LIMC2 < LIMC) LIMC2 = LIMC;
  if (DEBUGLEVEL) { err_printf("LIMC = %ld, LIMC2 = %ld\n",LIMC,LIMC2); }

  FBgen(&F, nf, N, LIMC, LIMC2, &GRHcheck);
  if (!F.KC) goto START;
  av = avma;
  subFBgen(&F,auts,cyclic,lim < 0? LIMC2: mindd(lim,LIMC2),MINSFB);
  if (DEBUGLEVEL)
  {
    if (lg(F.subFB) > 1)
      timer_printf(&T, "factorbase (#subFB = %ld) and ideal permutations",
                       lg(F.subFB)-1);
    else
      timer_printf(&T, "factorbase (no subFB) and ideal permutations");
  }
  fact = (FACT*)stack_malloc((F.KC+1)*sizeof(FACT));
  PERM = leafcopy(F.perm); /* to be restored in case of precision increase */
  cache.basis = zero_Flm_copy(F.KC,F.KC);
  small_multiplier = zero_Flv(F.KC);
  F.id2 = zerovec(F.KC);
  MAXDEPSIZESFB = (lg(F.subFB) - 1) * DEPSIZESFBMULT;
  MAXDEPSFB = MAXDEPSIZESFB / DEPSFBDIV;
  done_small = 0; small_fail = 0; squash_index = 0;
  fail_limit = F.KC + 1;
  R = NULL; A = NULL;
  av2 = avma;
  init_rel(&cache, &F, RELSUP + RU-1); /* trivial relations */
  old_need = need = cache.end - cache.last;
  add_cyclotomic_units(nf, zu, &cache, &F);
  cache.end = cache.last + need;

  W = NULL; zc = 0;
  sfb_trials = nreldep = 0;

  if (computed)
  {
    for (i = 1; i < lg(computed); i++)
      try_elt(&cache, &F, nf, gel(computed, i), fact);
    if (isclone(computed)) gunclone(computed);
    if (DEBUGLEVEL && i > 1)
    {
      err_printf("\n");
      timer_printf(&T, "including already computed relations");
    }
    need = 0;
  }

  do
  {
    do
    {
      pari_sp av4 = avma;
      if (need > 0)
      {
        long oneed = cache.end - cache.last;
        /* Test below can be true if small_norm did not find enough linearly
         * dependent relations */
        if (need < oneed) need = oneed;
        pre_allocate(&cache, need+lg(auts)-1+(R ? lg(W)-1 : 0));
        cache.end = cache.last + need;
        F.L_jid = trim_list(&F);
      }
      if (need > 0 && nbrelpid > 0 && (done_small <= F.KC+1 || A) &&
          small_fail <= fail_limit &&
          cache.last < cache.base + 2*F.KC+2*RU+RELSUP /* heuristic */)
      {
        pari_sp av3 = avma;
        GEN p0 = NULL;
        long j, k;
        REL_t *last = cache.last;
        if (R && lg(W) > 1 && (done_small % 2))
        {
          /* We have full rank for class group and unit, however those
           * lattices are too small. The following tries to improve the
           * prime group lattice: it specifically looks for relations
           * involving the primes generating the class group. */
          long l = lg(W) - 1;
          /* We need lg(W)-1 relations to squash the class group. */
          F.L_jid = vecslice(F.perm, 1, l); cache.end = cache.last + l;
          /* Lie to the add_rel subsystem: pretend we miss relations involving
           * the primes generating the class group (and only those). */
          cache.missing = l;
          for ( ; l > 0; l--) mael(cache.basis, F.perm[l], F.perm[l]) = 0;
        }
        j = done_small % (F.KC+1);
        if (j)
        {
          long mj = small_multiplier[j];
          p0 = gel(F.LP, j);
          if (!A)
          {
            /* Prevent considering both P_iP_j and P_jP_i in small_norm */
            /* Since not all elements end up in F.L_jid (because they can
             * be eliminated by hnfspec/add or by trim_list, keep track
             * of which ideals are being considered at each run. */
            for (i = k = 1; i < lg(F.L_jid); i++)
              if (F.L_jid[i] > mj)
              {
                small_multiplier[F.L_jid[i]] = j;
                F.L_jid[k++] = F.L_jid[i];
              }
            setlg(F.L_jid, k);
          }
        }
        if (lg(F.L_jid) > 1)
          small_norm(&cache, &F, nf, nbrelpid, M_sn, fact, p0);
        avma = av3;
        if (!A && cache.last != last)
          small_fail = 0;
        else
          small_fail++;
        if (R && lg(W) > 1 && (done_small % 2))
        {
          long l = lg(W) - 1;
          for ( ; l > 0; l--) mael(cache.basis, F.perm[l], F.perm[l]) = 1;
          cache.missing = 0;
        }
        F.L_jid = F.perm;
        need = 0; cache.end = cache.last;
        done_small++;
        F.sfb_chg = 0;
      }
      if (need > 0)
      {
        /* Random relations */
        if (lg(F.subFB) == 1) goto START;
        nreldep++;
        if (nreldep > MAXDEPSIZESFB) {
          if (++sfb_trials > SFB_MAX && LIMC < LIMCMAX/6) goto START;
          F.sfb_chg = sfb_INCREASE;
          nreldep = 0;
        }
        else if (!(nreldep % MAXDEPSFB))
          F.sfb_chg = sfb_CHANGE;
        if (F.newpow)
        {
          F.sfb_chg = 0;
          if (DEBUGLEVEL) err_printf("\n");
        }
        if (F.sfb_chg && !subFB_change(&F)) goto START;
        if (F.newpow) {
          powFBgen(&cache, &F, nf, auts);
          MAXDEPSIZESFB = (lg(F.subFB) - 1) * DEPSIZESFBMULT;
          MAXDEPSFB = MAXDEPSIZESFB / DEPSFBDIV;
          if (DEBUGLEVEL) timer_printf(&T, "powFBgen");
        }
        if (!F.sfb_chg) rnd_rel(&cache, &F, nf, fact);
        F.L_jid = F.perm;
      }
      if (DEBUGLEVEL) timer_start(&T);
      if (precpb)
      {
        GEN nf0 = nf;
        if (precadd) { PRECREG += precadd; precadd = 0; }
        else           PRECREG = precdbl(PRECREG);
        if (DEBUGLEVEL)
        {
          char str[64]; sprintf(str,"Buchall_param (%s)",precpb);
          pari_warn(warnprec,str,PRECREG);
        }
        nf = gclone( nfnewprec_shallow(nf, PRECREG) );
        if (precdouble) gunclone(nf0);
        precdouble++; precpb = NULL;

        for (i = 1; i < lg(PERM); i++) F.perm[i] = PERM[i];
        cache.chk = cache.base; W = NULL; /* recompute arch components+reduce */
      }
      avma = av4;
      if (cache.chk != cache.last)
      { /* Reduce relation matrices */
        long l = cache.last - cache.chk + 1, j;
        GEN M = nf_get_M(nf), mat = cgetg(l, t_MAT), emb = cgetg(l, t_MAT);
        int first = (W == NULL); /* never reduced before */
        REL_t *rel;

        for (j=1,rel = cache.chk + 1; j < l; rel++,j++)
        {
          gel(mat,j) = rel->R;
          if (!rel->relaut)
            gel(emb,j) = get_log_embed(rel, M, RU, R1, PRECREG);
          else
            gel(emb,j) = perm_log_embed(gel(emb, j-rel->relorig),
                                        gel(F.embperm, rel->relaut));
        }
        if (DEBUGLEVEL) timer_printf(&T, "floating point embeddings");
        if (first) {
          C = emb;
          W = hnfspec_i(mat, F.perm, &dep, &B, &C, F.subFB ? lg(F.subFB)-1:0);
        }
        else
          W = hnfadd_i(W, F.perm, &dep, &B, &C, mat, emb);
        gerepileall(av2, 4, &W,&C,&B,&dep);
        cache.chk = cache.last;
        if (DEBUGLEVEL)
        {
          if (first)
            timer_printf(&T, "hnfspec [%ld x %ld]", lg(F.perm)-1, l-1);
          else
            timer_printf(&T, "hnfadd (%ld + %ld)", l-1, lg(dep)-1);
        }
      }
      else if (!W)
      {
        need = old_need;
        F.L_jid = vecslice(F.perm, 1, need);
        continue;
      }
      need = F.KC - (lg(W)-1) - (lg(B)-1);
      /* FIXME: replace by err(e_BUG,"") */
      if (!need && cache.missing)
      { /* The test above will never be true except if 27449|class number,
         * but the code implicitely assumes that if we have maximal rank
         * for the ideal lattice, then cache.missing == 0. */
        for (i = 1; cache.missing; i++)
          if (!mael(cache.basis, i, i))
          {
            long j;
            mael(cache.basis, i, i) = 1;
            cache.missing--;
            for (j = i+1; j <= F.KC; j++) mael(cache.basis, j, i) = 0;
          }
      }
      zc = (lg(C)-1) - (lg(B)-1) - (lg(W)-1);
      if (zc < RU-1)
      {
        /* need more columns for units */
        need += RU-1 - zc;
        if (need > F.KC) need = F.KC;
      }
      if (need)
      { /* dependent rows */
        F.L_jid = vecslice(F.perm, 1, need);
        vecsmall_sort(F.L_jid);
        if (need != old_need) nreldep = 0;
        old_need = need;
      }
      else
      {
        /* If the relation lattice is too small, check will be > 1 and we
         * will do a new run of small_norm/rnd_rel asking for 1 relation.
         * However they tend to give a relation involving the first element
         * of L_jid. We thus permute which element is the first of L_jid in
         * order to increase the probability of finding a good relation, i.e.
         * one that increases the relation lattice. */
        if (lg(W) > 2 && squash_index % (lg(W) - 1))
        {
          long j, l = lg(W) - 1;
          F.L_jid = leafcopy(F.perm);
          for (j = 1; j <= l; j++)
            F.L_jid[j] = F.perm[1 + (j + squash_index - 1) % l];
        }
        else
          F.L_jid = F.perm;
        squash_index++;
      }
    }
    while (need);
    if (!A)
    {
      small_fail = 0; fail_limit = maxss(F.KC / FAIL_DIVISOR, MINFAIL);
      old_need = 0;
    }
    A = vecslice(C, 1, zc); /* cols corresponding to units */
    bit = bit_accuracy(PRECREG);
    R = compute_multiple_of_R(A, RU, N, &need, &bit, &lambda);
    if (need < old_need) small_fail = 0;
    old_need = need;
    if (!lambda) { precpb = "bestappr"; continue; }
    if (!R)
    { /* not full rank for units */
      if (DEBUGLEVEL) err_printf("regulator is zero.\n");
      if (!need) precpb = "regulator";
      continue;
    }

    h = ZM_det_triangular(W);
    if (DEBUGLEVEL) err_printf("\n#### Tentative class number: %Ps\n", h);

    switch (compute_R(lambda, RU, mulir(h,invhr), RgM_bit(C, bit), &L, &R))
    {
      case fupb_RELAT:
        need = 1; /* not enough relations */
        continue;
      case fupb_PRECI: /* prec problem unless we cheat on Bach constant */
        if ((precdouble&7) == 7 && LIMC<=LIMCMAX/6) goto START;
        precpb = "compute_R";
        continue;
    }
    /* DONE */

    if (F.KCZ2 > F.KCZ)
    {
      if (F.sfb_chg && !subFB_change(&F)) goto START;
      if (!be_honest(&F, nf, auts, fact)) goto START;
      if (DEBUGLEVEL) timer_printf(&T, "to be honest");
    }
    F.KCZ2 = 0; /* be honest only once */

    /* fundamental units */
    {
      pari_sp av3 = avma;
      GEN AU, U, H, v = extract_full_lattice(L); /* L may be very large */
      long e;
      if (v)
      {
        A = vecpermute(A, v);
        L = vecpermute(L, v);
      }
      /* arch. components of fund. units */
      H = ZM_hnflll(L, &U, 1); U = vecslice(U, lg(U)-(RU-1), lg(U)-1);
      U = ZM_mul(U, ZM_lll(H, 0.99, LLL_IM|LLL_COMPATIBLE));
      AU = RgM_mul(A, U);
      A = cleanarch(AU, N, PRECREG);
      if (DEBUGLEVEL) timer_printf(&T, "cleanarch");
      if (!A) {
        precadd = nbits2extraprec( gexpo(AU) + 64 ) - gprecision(AU);
        if (precadd <= 0) precadd = 1;
        precpb = "cleanarch"; continue;
      }
      fu = getfu(nf, &A, &e, PRECREG);
      if (DEBUGLEVEL) timer_printf(&T, "getfu");
      if (!fu && (flun & nf_FORCE))
      { /* units not found but we want them */
        if (e > 0) pari_err_OVERFLOW("bnfinit [fundamental units too large]");
        if (e < 0) precadd = nbits2extraprec( (-e - (BITS_IN_LONG - 1)) + 64);
        avma = av3; precpb = "getfu"; continue;
      }
    }
    /* class group generators */
    i = lg(C)-zc; C += zc; C[0] = evaltyp(t_MAT)|evallg(i);
    C0 = C; C = cleanarch(C, N, PRECREG);
    if (!C) {
      precadd = nbits2extraprec( gexpo(C0) + 64 ) - gprecision(C0);
      if (precadd <= 0) precadd = 1;
      precpb = "cleanarch";
    }
  } while (need || precpb);

  delete_cache(&cache); delete_FB(&F); free_GRHcheck(&GRHcheck);
  Vbase = vecpermute(F.LP, F.perm);
  class_group_gen(nf,W,C,Vbase,PRECREG,NULL, &clg1, &clg2);
  res = get_clfu(clg1, R, zu, fu);
  res = buchall_end(nf,res,clg2,W,B,A,C,Vbase);
  res = gerepilecopy(av0, res); if (precdouble) gunclone(nf);
  return res;
}
