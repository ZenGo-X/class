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

/***********************************************************************/
/**                       PRIMES IN SUCCESSION                        **/
/***********************************************************************/

/* map from prime residue classes mod 210 to their numbers in {0...47}.
 * Subscripts into this array take the form ((k-1)%210)/2, ranging from
 * 0 to 104.  Unused entries are */
#define NPRC 128 /* non-prime residue class */

static unsigned char prc210_no[] = {
  0, NPRC, NPRC, NPRC, NPRC, 1, 2, NPRC, 3, 4, NPRC, /* 21 */
  5, NPRC, NPRC, 6, 7, NPRC, NPRC, 8, NPRC, 9, /* 41 */
  10, NPRC, 11, NPRC, NPRC, 12, NPRC, NPRC, 13, 14, NPRC, /* 63 */
  NPRC, 15, NPRC, 16, 17, NPRC, NPRC, 18, NPRC, 19, /* 83 */
  NPRC, NPRC, 20, NPRC, NPRC, NPRC, 21, NPRC, 22, 23, NPRC, /* 105 */
  24, 25, NPRC, 26, NPRC, NPRC, NPRC, 27, NPRC, NPRC, /* 125 */
  28, NPRC, 29, NPRC, NPRC, 30, 31, NPRC, 32, NPRC, NPRC, /* 147 */
  33, 34, NPRC, NPRC, 35, NPRC, NPRC, 36, NPRC, 37, /* 167 */
  38, NPRC, 39, NPRC, NPRC, 40, 41, NPRC, NPRC, 42, NPRC, /* 189 */
  43, 44, NPRC, 45, 46, NPRC, NPRC, NPRC, NPRC, 47, /* 209 */
};

/* first differences of the preceding */
static unsigned char prc210_d1[] = {
  10, 2, 4, 2, 4, 6, 2, 6, 4, 2, 4, 6, 6, 2, 6, 4, 2, 6,
  4, 6, 8, 4, 2, 4, 2, 4, 8, 6, 4, 6, 2, 4, 6,
  2, 6, 6, 4, 2, 4, 6, 2, 6, 4, 2, 4, 2, 10, 2,
};

/* return 0 for overflow */
ulong
unextprime(ulong n)
{
  long rc, rc0, rcd, rcn;

  switch(n) {
    case 0: case 1: case 2: return 2;
    case 3: return 3;
    case 4: case 5: return 5;
    case 6: case 7: return 7;
  }
#ifdef LONG_IS_64BIT
  if (n > (ulong)-59) return 0;
#else
  if (n > (ulong)-5) return 0;
#endif
  /* here n > 7 */
  n |= 1; /* make it odd */
  rc = rc0 = n % 210;
  /* find next prime residue class mod 210 */
  for(;;)
  {
    rcn = (long)(prc210_no[rc>>1]);
    if (rcn != NPRC) break;
    rc += 2; /* cannot wrap since 209 is coprime and rc odd */
  }
  if (rc > rc0) n += rc - rc0;
  /* now find an actual (pseudo)prime */
  for(;;)
  {
    if (uisprime(n)) break;
    rcd = prc210_d1[rcn];
    if (++rcn > 47) rcn = 0;
    n += rcd;
  }
  return n;
}

GEN
nextprime(GEN n)
{
  long rc, rc0, rcd, rcn;
  pari_sp av = avma;

  if (typ(n) != t_INT)
  {
    n = gceil(n);
    if (typ(n) != t_INT) pari_err_TYPE("nextprime",n);
  }
  if (signe(n) <= 0) { avma = av; return gen_2; }
  if (lgefint(n) == 3)
  {
    ulong k = unextprime(uel(n,2));
    avma = av;
    if (k) return utoipos(k);
#ifdef LONG_IS_64BIT
    return uutoi(1,13);
#else
    return uutoi(1,15);
#endif
  }
  /* here n > 7 */
  if (!mod2(n)) n = addui(1,n);
  rc = rc0 = umodiu(n, 210);
  /* find next prime residue class mod 210 */
  for(;;)
  {
    rcn = (long)(prc210_no[rc>>1]);
    if (rcn != NPRC) break;
    rc += 2; /* cannot wrap since 209 is coprime and rc odd */
  }
  if (rc > rc0) n = addui(rc - rc0, n);
  /* now find an actual (pseudo)prime */
  for(;;)
  {
    if (BPSW_psp(n)) break;
    rcd = prc210_d1[rcn];
    if (++rcn > 47) rcn = 0;
    n = addui(rcd, n);
  }
  if (avma == av) return icopy(n);
  return gerepileuptoint(av, n);
}

ulong
uprecprime(ulong n)
{
  long rc, rc0, rcd, rcn;
  { /* check if n <= 10 */
    if (n <= 1)  return 0;
    if (n == 2)  return 2;
    if (n <= 4)  return 3;
    if (n <= 6)  return 5;
    if (n <= 10) return 7;
  }
  /* here n >= 11 */
  if (!(n % 2)) n--;
  rc = rc0 = n % 210;
  /* find previous prime residue class mod 210 */
  for(;;)
  {
    rcn = (long)(prc210_no[rc>>1]);
    if (rcn != NPRC) break;
    rc -= 2; /* cannot wrap since 1 is coprime and rc odd */
  }
  if (rc < rc0) n += rc - rc0;
  /* now find an actual (pseudo)prime */
  for(;;)
  {
    if (uisprime(n)) break;
    if (--rcn < 0) rcn = 47;
    rcd = prc210_d1[rcn];
    n -= rcd;
  }
  return n;
}

GEN
precprime(GEN n)
{
  long rc, rc0, rcd, rcn;
  pari_sp av = avma;

  if (typ(n) != t_INT)
  {
    n = gfloor(n);
    if (typ(n) != t_INT) pari_err_TYPE("nextprime",n);
  }
  if (signe(n) <= 0) { avma = av; return gen_0; }
  if (lgefint(n) <= 3)
  {
    ulong k = uel(n,2);
    avma = av;
    return utoi(uprecprime(k));
  }
  if (!mod2(n)) n = subiu(n,1);
  rc = rc0 = umodiu(n, 210);
  /* find previous prime residue class mod 210 */
  for(;;)
  {
    rcn = (long)(prc210_no[rc>>1]);
    if (rcn != NPRC) break;
    rc -= 2; /* cannot wrap since 1 is coprime and rc odd */
  }
  if (rc0 > rc) n = subiu(n, rc0 - rc);
  /* now find an actual (pseudo)prime */
  for(;;)
  {
    if (BPSW_psp(n)) break;
    if (--rcn < 0) rcn = 47;
    rcd = prc210_d1[rcn];
    n = subiu(n, rcd);
  }
  if (avma == av) return icopy(n);
  return gerepileuptoint(av, n);
}

/* Find next single-word prime strictly larger than p.
 * If **d is non-NULL (somewhere in a diffptr), this is p + *(*d)++;
 * otherwise imitate nextprime().
 * *rcn = NPRC or the correct residue class for the current p; we'll use this
 * to track the current prime residue class mod 210 once we're out of range of
 * the diffptr table, and we'll update it before that if it isn't NPRC.
 *
 * *q is incremented whenever q!=NULL and we wrap from 209 mod 210 to
 * 1 mod 210
 * k =  second argument for Fl_MR_Jaeschke(). --GN1998Aug22 */
ulong
snextpr(ulong p, byteptr *d, long *rcn, long *q, long k)
{
  ulong n;
  if (**d)
  {
    byteptr dd = *d;
    long d1 = 0;

    NEXT_PRIME_VIADIFF(d1,dd);
    /* d1 = nextprime(p+1) - p */
    if (*rcn != NPRC)
    {
      while (d1 > 0)
      {
        d1 -= prc210_d1[*rcn];
        if (++*rcn > 47) { *rcn = 0; if (q) (*q)++; }
      }
      /* assert(d1 == 0) */
    }
    NEXT_PRIME_VIADIFF(p,*d);
    return p;
  }
  /* we are beyond the diffptr table */
  /* initialize */
  if (*rcn == NPRC) *rcn = prc210_no[(p % 210) >> 1]; /* != NPRC */
  /* look for the next one */
  n = p + prc210_d1[*rcn];
  if (++*rcn > 47) *rcn = 0;
  while (!Fl_MR_Jaeschke(n, k))
  {
    n += prc210_d1[*rcn];
    if (n <= 11) pari_err_OVERFLOW("snextpr");
    if (++*rcn > 47) { *rcn = 0; if (q) (*q)++; }
  }
  return n;
}

/********************************************************************/
/**                                                                **/
/**                     INTEGER FACTORIZATION                      **/
/**                                                                **/
/********************************************************************/
int factor_add_primes = 0, factor_proven = 0;

/***********************************************************************/
/**                                                                   **/
/**                 FACTORIZATION (ECM) -- GN Jul-Aug 1998            **/
/**   Integer factorization using the elliptic curves method (ECM).   **/
/**   ellfacteur() returns a non trivial factor of N, assuming N>0,   **/
/**   is composite, and has no prime divisor below 2^14 or so.        **/
/**   Thanks to Paul Zimmermann for much helpful advice and to        **/
/**   Guillaume Hanrot and Igor Schein for intensive testing          **/
/**                                                                   **/
/***********************************************************************/
#define nbcmax 64 /* max number of simultaneous curves */

static const ulong TB1[] = {
  142,172,208,252,305,370,450,545,661,801,972,1180,1430,
  1735,2100,2550,3090,3745,4540,5505,6675,8090,9810,11900,
  14420,17490,21200,25700,31160,37780UL,45810UL,55550UL,67350UL,
  81660UL,99010UL,120050UL,145550UL,176475UL,213970UL,259430UL,
  314550UL,381380UL,462415UL,560660UL,679780UL,824220UL,999340UL,
  1211670UL,1469110UL,1781250UL,2159700UL,2618600UL,3175000UL,
  3849600UL,4667500UL,5659200UL,6861600UL,8319500UL,10087100UL,
  12230300UL,14828900UL,17979600UL,21799700UL,26431500UL,
  32047300UL,38856400UL, /* 110 times that still fits into 32bits */
#ifdef LONG_IS_64BIT
  47112200UL,57122100UL,69258800UL,83974200UL,101816200UL,
  123449000UL,149678200UL,181480300UL,220039400UL,266791100UL,
  323476100UL,392204900UL,475536500UL,576573500UL,699077800UL,
  847610500UL,1027701900UL,1246057200UL,1510806400UL,1831806700UL,
  2221009800UL,2692906700UL,3265067200UL,3958794400UL,4799917500UL
#endif
};
static const ulong TB1_for_stage[] = {
 /* Start below the optimal B1 for finding factors which would just have been
  * missed by pollardbrent(), and escalate, changing curves to give good
  * coverage of the small factor ranges. Entries grow faster than what would
  * be optimal but a table instead of a 2D array keeps the code simple */
  500,520,560,620,700,800,900,1000,1150,1300,1450,1600,1800,2000,
  2200,2450,2700,2950,3250,3600,4000,4400,4850,5300,5800,6400,
  7100,7850,8700,9600,10600,11700,12900,14200,15700,17300,
  19000,21000,23200,25500,28000,31000,34500UL,38500UL,43000UL,
  48000UL,53800UL,60400UL,67750UL,76000UL,85300UL,95700UL,
  107400UL,120500UL,135400UL,152000UL,170800UL,191800UL,215400UL,
  241800UL,271400UL,304500UL,341500UL,383100UL,429700UL,481900UL,
  540400UL,606000UL,679500UL,761800UL,854100UL,957500UL,1073500UL
};

/* addition/doubling/multiplication of a point on an 'elliptic curve mod N'
 * may result in one of three things:
 * - a new bona fide point
 * - a point at infinity (denominator divisible by N)
 * - a point at infinity mod some p | N but finite mod q | N betraying itself
 *   by a denominator which has nontrivial gcd with N.
 *
 * In the second case, addition/doubling aborts, copying one of the summands
 * to the destination array of points unless they coincide.
 * Multiplication will stop at some unpredictable intermediate stage:  The
 * destination will contain _some_ multiple of the input point, but not
 * necessarily the desired one, which doesn't matter.  As long as we're
 * multiplying (B1 phase) we simply carry on with the next multiplier.
 * During the B2 phase, the only additions are the giant steps, and the
 * worst that can happen here is that we lose one residue class mod 210
 * of prime multipliers on 4 of the curves, so again, we ignore the problem
 * and just carry on.)
 *
 * Idea: select nbc curves mod N and one point P on each of them. For each
 * such P, compute [M]P = Q where M is the product of all powers <= B2 of
 * primes <= nextprime(B1). Then check whether [p]Q for p < nextprime(B2)
 * betrays a factor. This second stage looks separately at the primes in
 * each residue class mod 210, four curves at a time, and steps additively
 * to ever larger multipliers, by comparing X coordinates of points which we
 * would need to add in order to reach another prime multiplier in the same
 * residue class. 'Comparing' means that we accumulate a product of
 * differences of X coordinates, and from time to time take a gcd of this
 * product with N. Montgomery's multi-inverse trick is used heavily. */

/* *** auxiliary functions for ellfacteur: *** */
/* (Rx,Ry) <- (Px,Py)+(Qx,Qy) over Z/NZ, z=1/(Px-Qx). If Ry = NULL, don't set */
static void
FpE_add_i(GEN N, GEN z, GEN Px, GEN Py, GEN Qx, GEN Qy, GEN *Rx, GEN *Ry)
{
  GEN slope = modii(mulii(subii(Py, Qy), z), N);
  GEN t = subii(sqri(slope), addii(Qx, Px));
  affii(modii(t, N), *Rx);
  if (Ry) {
    t = subii(mulii(slope, subii(Px, *Rx)), Py);
    affii(modii(t, N), *Ry);
  }
}
/* X -> Z; cannot add on one of the curves: make sure Z contains
 * something useful before letting caller proceed */
static void
ZV_aff(long n, GEN *X, GEN *Z)
{
  if (X != Z) {
    long k;
    for (k = n; k--; ) affii(X[k],Z[k]);
  }
}

/* Parallel addition on nbc curves, assigning the result to locations at and
 * following *X3, *Y3. (If Y-coords of result not desired, set Y=NULL.)
 * Safe even if (X3,Y3) = (X2,Y2), _not_ if (X1,Y1). It is also safe to
 * overwrite Y2 with X3. If nbc1 < nbc, the first summand is
 * assumed to hold only nbc1 distinct points, repeated as often as we need
 * them  (to add one point on each of a few curves to several other points on
 * the same curves): only used with nbc1 = nbc or nbc1 = 4 | nbc.
 *
 * Return 0 [SUCCESS], 1 [N | den], 2 [gcd(den, N) is a factor of N, preserved
 * in gl.
 * Stack space is bounded by a constant multiple of lgefint(N)*nbc:
 * - Phase 2 creates 12 items on the stack per iteration, of which 4 are twice
 *   as long and 1 is thrice as long as N, i.e. 18 units per iteration.
 * - Phase  1 creates 4 units.
 * Total can be as large as 4*nbcmax + 18*8 units; ecm_elladd2() is
 * just as bad, and elldouble() comes to 3*nbcmax + 29*8 units. */
static int
ecm_elladd0(GEN N, GEN *gl, long nbc, long nbc1,
            GEN *X1, GEN *Y1, GEN *X2, GEN *Y2, GEN *X3, GEN *Y3)
{
  const ulong mask = (nbc1 == 4)? 3: ~0UL; /*nbc1 = 4 or nbc*/
  GEN W[2*nbcmax], *A = W+nbc; /* W[0],A[0] unused */
  long i;
  pari_sp av = avma;

  W[1] = subii(X1[0], X2[0]);
  for (i=1; i<nbc; i++)
  { /*prepare for multi-inverse*/
    A[i] = subii(X1[i&mask], X2[i]); /* don't waste time reducing mod N */
    W[i+1] = modii(mulii(A[i], W[i]), N);
  }
  if (!invmod(W[nbc], N, gl))
  {
    if (!equalii(N,*gl)) return 2;
    ZV_aff(nbc, X2,X3);
    if (Y3) ZV_aff(nbc, Y2,Y3);
    avma = av; return 1;
  }

  while (i--) /* nbc times */
  {
    pari_sp av2 = avma;
    GEN Px = X1[i&mask], Py = Y1[i&mask], Qx = X2[i], Qy = Y2[i];
    GEN z = i? mulii(*gl,W[i]): *gl; /*1/(Px-Qx)*/
    FpE_add_i(N,z,  Px,Py,Qx,Qy, X3+i, Y3? Y3+i: NULL);
    if (!i) break;
    avma = av2; *gl = modii(mulii(*gl, A[i]), N);
  }
  avma = av; return 0;
}

/* Shortcut, for use in cases where Y coordinates follow their corresponding
 * X coordinates, and first summand doesn't need to be repeated */
static int
ecm_elladd(GEN N, GEN *gl, long nbc, GEN *X1, GEN *X2, GEN *X3) {
  return ecm_elladd0(N, gl, nbc, nbc, X1, X1+nbc, X2, X2+nbc, X3, X3+nbc);
}

/* As ecm_elladd except it does twice as many additions (and hides even more
 * of the cost of the modular inverse); the net effect is the same as
 * ecm_elladd(nbc,X1,X2,X3) && ecm_elladd(nbc,X4,X5,X6). Safe to
 * have X2=X3, X5=X6, or X1,X2 coincide with X4,X5 in any order. */
static int
ecm_elladd2(GEN N, GEN *gl, long nbc,
            GEN *X1, GEN *X2, GEN *X3, GEN *X4, GEN *X5, GEN *X6)
{
  GEN *Y1 = X1+nbc, *Y2 = X2+nbc, *Y3 = X3+nbc;
  GEN *Y4 = X4+nbc, *Y5 = X5+nbc, *Y6 = X6+nbc;
  GEN W[4*nbcmax], *A = W+2*nbc; /* W[0],A[0] unused */
  long i, j;
  pari_sp av = avma;

  W[1] = subii(X1[0], X2[0]);
  for (i=1; i<nbc; i++)
  {
    A[i] = subii(X1[i], X2[i]); /* don't waste time reducing mod N here */
    W[i+1] = modii(mulii(A[i], W[i]), N);
  }
  for (j=0; j<nbc; i++,j++)
  {
    A[i] = subii(X4[j], X5[j]);
    W[i+1] = modii(mulii(A[i], W[i]), N);
  }
  if (!invmod(W[2*nbc], N, gl))
  {
    if (!equalii(N,*gl)) return 2;
    ZV_aff(2*nbc, X2,X3); /* hack: 2*nbc => copy Y2->Y3 */
    ZV_aff(2*nbc, X5,X6); /* also copy Y5->Y6 */
    avma = av; return 1;
  }

  while (j--) /* nbc times */
  {
    pari_sp av2 = avma;
    GEN Px = X4[j], Py = Y4[j], Qx = X5[j], Qy = Y5[j];
    GEN z = mulii(*gl,W[--i]); /*1/(Px-Qx)*/
    FpE_add_i(N,z, Px,Py, Qx,Qy, X6+j,Y6+j);
    avma = av2; *gl = modii(mulii(*gl, A[i]), N);
  }
  while (i--) /* nbc times */
  {
    pari_sp av2 = avma;
    GEN Px = X1[i], Py = Y1[i], Qx = X2[i], Qy = Y2[i];
    GEN z = i? mulii(*gl, W[i]): *gl; /*1/(Px-Qx)*/
    FpE_add_i(N,z, Px,Py, Qx,Qy, X3+i,Y3+i);
    if (!i) break;
    avma = av2; *gl = modii(mulii(*gl, A[i]), N);
  }
  avma = av; return 0;
}

/* Parallel doubling on nbc curves, assigning the result to locations at
 * and following *X2.  Safe to be called with X2 equal to X1.  Return
 * value as for ecm_elladd.  If we find a point at infinity mod N,
 * and if X1 != X2, we copy the points at X1 to X2. */
static int
elldouble(GEN N, GEN *gl, long nbc, GEN *X1, GEN *X2)
{
  GEN *Y1 = X1+nbc, *Y2 = X2+nbc;
  GEN W[nbcmax+1]; /* W[0] unused */
  long i;
  pari_sp av = avma;
  /*W[0] = gen_1;*/ W[1] = Y1[0];
  for (i=1; i<nbc; i++) W[i+1] = modii(mulii(Y1[i], W[i]), N);
  if (!invmod(W[nbc], N, gl))
  {
    if (!equalii(N,*gl)) return 2;
    ZV_aff(2*nbc,X1,X2); /* also copies Y1->Y2 */
    avma = av; return 1;
  }
  while (i--) /* nbc times */
  {
    pari_sp av2;
    GEN v, w, L, z = i? mulii(*gl,W[i]): *gl;
    if (i) *gl = modii(mulii(*gl, Y1[i]), N);
    av2 = avma;
    L = modii(mulii(addui(1, mului(3, Fp_sqr(X1[i],N))), z), N);
    if (signe(L)) /* half of zero is still zero */
      L = shifti(mod2(L)? addii(L, N): L, -1);
    v = modii(subii(sqri(L), shifti(X1[i],1)), N);
    w = modii(subii(mulii(L, subii(X1[i], v)), Y1[i]), N);
    affii(v, X2[i]);
    affii(w, Y2[i]);
    avma = av2;
  }
  avma = av; return 0;
}

/* Parallel multiplication by an odd prime k on nbc curves, storing the
 * result to locations at and following *X2. Safe to be called with X2 = X1.
 * Return values as ecm_elladd. Uses (a simplified variant of) Montgomery's
 * PRAC algorithm; see ftp://ftp.cwi.nl/pub/pmontgom/Lucas.ps.gz .
 * With thanks to Paul Zimmermann for the reference.  --GN1998Aug13 */
static int
get_rule(ulong d, ulong e)
{
  if (d <= e + (e>>2)) /* floor(1.25*e) */
  {
    if ((d+e)%3 == 0) return 0; /* rule 1 */
    if ((d-e)%6 == 0) return 1;  /* rule 2 */
  }
  /* d <= 4*e but no ofl */
  if ((d+3)>>2 <= e) return 2; /* rule 3, common case */
  if ((d&1)==(e&1))  return 1; /* rule 4 = rule 2 */
  if (!(d&1))        return 3; /* rule 5 */
  if (d%3 == 0)      return 4; /* rule 6 */
  if ((d+e)%3 == 0)  return 5; /* rule 7 */
  if ((d-e)%3 == 0)  return 6; /* rule 8 */
  /* when we get here, e is even, otherwise one of rules 4,5 would apply */
  return 7; /* rule 9 */
}

/* PRAC implementation notes - main changes against the paper version:
 * (1) The general function [m+n]P = f([m]P,[n]P,[m-n]P) collapses (for m!=n)
 * to an ecm_elladd() which does not depend on the third argument; thus
 * references to the third variable (C in the paper) can be eliminated.
 * (2) Since our multipliers are prime, the outer loop of the paper
 * version executes only once, and thus is invisible above.
 * (3) The first step in the inner loop of the paper version will always be
 * rule 3, but the addition requested by this rule amounts to a doubling, and
 * will always be followed by a swap, so we have unrolled this first iteration.
 * (4) Simplifications in rules 6 and 7 are possible given the above, and we
 * save one addition in each of the two cases.  NB none of the other
 * ecm_elladd()s in the loop can ever degenerate into an elldouble.
 * (5) I tried to optimize for rule 3, which is used more frequently than all
 * others together, but it didn't improve things, so I removed the nested
 * tight loop again.  --GN */
/* The main loop body of ellfacteur() runs _slower_ under PRAC than under a
 * straightforward left-shift binary multiplication when N has <30 digits and
 * B1 is small;  PRAC wins when N and B1 get larger.  Weird. --GN */
/* k>2 assumed prime, XAUX = scratchpad */
static int
ellmult(GEN N, GEN *gl, long nbc, ulong k, GEN *X1, GEN *X2, GEN *XAUX)
{
  ulong r, d, e, e1;
  int res;
  GEN *A = X2, *B = XAUX, *T = XAUX + 2*nbc;

  ZV_aff(2*nbc,X1,XAUX);
  /* first doubling picks up X1;  after this we'll be working in XAUX and
   * X2 only, mostly via A and B and T */
  if ((res = elldouble(N, gl, nbc, X1, X2)) != 0) return res;

  /* split the work at the golden ratio */
  r = (ulong)(k*0.61803398875 + .5);
  d = k - r;
  e = r - d; /* d+e == r, so no danger of ofl below */
  while (d != e)
  { /* apply one of the nine transformations from PM's Table 4. */
    switch(get_rule(d,e))
    {
    case 0: /* rule 1 */
      if ( (res = ecm_elladd(N, gl, nbc, A, B, T)) ) return res;
      if ( (res = ecm_elladd2(N, gl, nbc, T, A, A, T, B, B)) != 0) return res;
      e1 = d - e; d = (d + e1)/3; e = (e - e1)/3; break;
    case 1: /* rules 2 and 4 */
      if ( (res = ecm_elladd(N, gl, nbc, A, B, B)) ) return res;
      if ( (res = elldouble(N, gl, nbc, A, A)) ) return res;
      d = (d-e)>>1; break;
    case 3: /* rule 5 */
      if ( (res = elldouble(N, gl, nbc, A, A)) ) return res;
      d >>= 1; break;
    case 4: /* rule 6 */
      if ( (res = elldouble(N, gl, nbc, A, T)) ) return res;
      if ( (res = ecm_elladd(N, gl, nbc, T, A, A)) ) return res;
      if ( (res = ecm_elladd(N, gl, nbc, A, B, B)) ) return res;
      d = d/3 - e; break;
    case 2: /* rule 3 */
      if ( (res = ecm_elladd(N, gl, nbc, A, B, B)) ) return res;
      d -= e; break;
    case 5: /* rule 7 */
      if ( (res = elldouble(N, gl, nbc, A, T)) ) return res;
      if ( (res = ecm_elladd2(N, gl, nbc, T, A, A, T, B, B)) != 0) return res;
      d = (d - 2*e)/3; break;
    case 6: /* rule 8 */
      if ( (res = ecm_elladd(N, gl, nbc, A, B, B)) ) return res;
      if ( (res = elldouble(N, gl, nbc, A, T)) ) return res;
      if ( (res = ecm_elladd(N, gl, nbc, T, A, A)) ) return res;
      d = (d - e)/3; break;
    case 7: /* rule 9 */
      if ( (res = elldouble(N, gl, nbc, B, B)) ) return res;
      e >>= 1; break;
    }
    /* swap d <-> e and A <-> B if necessary */
    if (d < e) { lswap(d,e); pswap(A,B); }
  }
  return ecm_elladd(N, gl, nbc, XAUX, X2, X2);
}

struct ECM {
  pari_timer T;
  long nbc, nbc2, seed;
  GEN *X, *XAUX, *XT, *XD, *XB, *XB2, *XH, *Xh, *Yh;
};

/* memory layout in ellfacteur():  a large array of GEN pointers, and one
 * huge chunk of memory containing all the actual GEN (t_INT) objects.
 * nbc is constant throughout the invocation:
 * - The B1 stage of each iteration through the main loop needs little
 * space:  enough for the X and Y coordinates of the current points,
 * and twice as much again as scratchpad for ellmult().
 * - The B2 stage, starting from some current set of points Q, needs, in
 * succession:
 *   + space for [2]Q, [4]Q, ..., [10]Q, and [p]Q for building the helix;
 *   + space for 48*nbc X and Y coordinates to hold the helix.  This could
 *   re-use [2]Q,...,[8]Q, but only with difficulty, since we don't
 *   know in advance which residue class mod 210 our p is going to be in.
 *   It can and should re-use [p]Q, though;
 *   + space for (temporarily [30]Q and then) [210]Q, [420]Q, and several
 *   further doublings until the giant step multiplier is reached.  This
 *   can re-use the remaining cells from above.  The computation of [210]Q
 *   will have been the last call to ellmult() within this iteration of the
 *   main loop, so the scratchpad is now also free to be re-used. We also
 *   compute [630]Q by a parallel addition;  we'll need it later to get the
 *   baby-step table bootstrapped a little faster.
 *   + Finally, for no more than 4 curves at a time, room for up to 1024 X
 *   coordinates only: the Y coordinates needed whilst setting up this baby
 *   step table are temporarily stored in the upper half, and overwritten
 *   during the last series of additions.
 *
 * Graphically:  after end of B1 stage (X,Y are the coords of Q):
 * +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--
 * | X Y |  scratch  | [2]Q| [4]Q| [6]Q| [8]Q|[10]Q|    ...    | ...
 * +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--
 * *X    *XAUX *XT   *XD                                       *XB
 *
 * [30]Q is computed from [10]Q.  [210]Q can go into XY, etc:
 * +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--
 * |[210]|[420]|[630]|[840]|[1680,3360,6720,...,2048*210]      |bstp table...
 * +--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--+--
 * *X    *XAUX *XT   *XD      [*XG, somewhere here]            *XB .... *XH
 *
 * So we need (13 + 48) * 2 * nbc slots here + 4096 slots for the baby step
 * table (not all of which will be used when we start with a small B1, but
 * better to allocate and initialize ahead of time all the slots that might
 * be needed later).
 *
 * Note on memory locality:  During the B2 phase, accesses to the helix
 * (once it is set up) will be clustered by curves (4 out of nbc at a time).
 * Accesses to the baby steps table will wander from one end of the array to
 * the other and back, one such cycle per giant step, and during a full cycle
 * we would expect on the order of 2E4 accesses when using the largest giant
 * step size.  Thus we shouldn't be doing too bad with respect to thrashing
 * a 512KBy L2 cache.  However, we don't want the baby step table to grow
 * larger than this, even if it would reduce the number of EC operations by a
 * few more per cent for very large B2, lest cache thrashing slow down
 * everything disproportionally. --GN */
/* Auxiliary routines need < (3*nbc+240)*lN words on the PARI stack, in
 * addition to the spc*(lN+1) words occupied by our main table. */
static void
ECM_alloc(struct ECM *E, long lN)
{
  const long bstpmax = 1024; /* max number of baby step table entries */
  long spc = (13 + 48) * E->nbc2 + bstpmax * 4;
  long len = spc + 385 + spc*lN;
  long i, tw = evallg(lN) | evaltyp(t_INT);
  GEN w, *X = (GEN*)new_chunk(len);
  /* hack for X[i] = cgeti(lN). X = current point in B1 phase */
  w = (GEN)(X + spc + 385);
  for (i = spc-1; i >= 0; i--) { X[i] = w; *w = tw; w += lN; }
  E->X = X;
  E->XAUX = E->X    + E->nbc2; /* scratchpad for ellmult() */
  E->XT   = E->XAUX + E->nbc2; /* ditto, will later hold [3*210]Q */
  E->XD   = E->XT   + E->nbc2; /* room for various multiples */
  E->XB   = E->XD   + 10*E->nbc2; /* start of baby steps table */
  E->XB2  = E->XB   + 2 * bstpmax; /* middle of baby steps table */
  E->XH   = E->XB2  + 2 * bstpmax; /* end of bstps table, start of helix */
  E->Xh   = E->XH   + 48*E->nbc2; /* little helix, X coords */
  E->Yh   = E->XH   + 192;     /* ditto, Y coords */
  /* XG,YG set inside the main loop, since they depend on B2 */
  /* E.Xh range of 384 pointers not set; these will later duplicate the pointers
   * in the E.XH range, 4 curves at a time. Some of the cells reserved here for
   * the E.XB range will never be used, instead, we'll warp the pointers to
   * connect to (read-only) GENs in the X/E.XD range */
}
/* N.B. E->seed is not initialized here */
static void
ECM_init(struct ECM *E, GEN N, long nbc)
{
  if (nbc < 0)
  { /* choose a sensible default */
    const long size = expi(N) + 1;
    nbc = ((size >> 3) << 2) - 80;
    if (nbc < 8) nbc = 8;
  }
  if (nbc > nbcmax) nbc = nbcmax;
  E->nbc = nbc;
  E->nbc2 = nbc << 1;
  ECM_alloc(E, lgefint(N));
}

static GEN
ECM_loop(struct ECM *E, GEN N, ulong B1)
{
  const long MR_foolproof = 16;/* B1 phase, foolproof below 10^12 */
  const long MR_fast = 1; /* B2 phase, not foolproof, 2xfaster */
/* MR_fast will let thousands of composites slip through, which doesn't
 * harm ECM; but ellmult() in the B1 phase should only be fed actual primes */
  const ulong B2 = 110 * B1, B2_rt = usqrt(B2);
  const ulong nbc = E->nbc, nbc2 = E->nbc2;
  pari_sp av1, avtmp;
  byteptr d0, d = diffptr;
  long i, gse, gss, bstp, bstp0, rcn0, rcn;
  ulong B2_p, m, p, p0;
  GEN g, *XG, *YG;
  GEN *X = E->X, *XAUX = E->XAUX, *XT = E->XT, *XD = E->XD;
  GEN *XB = E->XB, *XB2 = E->XB2, *XH = E->XH, *Xh = E->Xh, *Yh = E->Yh;
  /* pick curves */
  for (i = nbc2; i--; ) affui(E->seed++, X[i]);
  /* pick giant step exponent and size */
  gse = B1 < 656
          ? (B1 < 200? 5: 6)
          : (B1 < 10500
            ? (B1 < 2625? 7: 8)
            : (B1 < 42000? 9: 10));
  gss = 1UL << gse;
  /* With 32 baby steps, a giant step corresponds to 32*420 = 13440,
   * appropriate for the smallest B2s. With 1024, a giant step will be 430080;
   * appropriate for B1 >~ 42000, where 512 baby steps would imply roughly
   * the same number of curve additions. */
  XG = XT + gse*nbc2; /* will later hold [2^(gse+1)*210]Q */
  YG = XG + nbc;

  if (DEBUGLEVEL >= 4) {
    err_printf("ECM: time = %6ld ms\nECM: B1 = %4lu,", timer_delay(&E->T), B1);
    err_printf("\tB2 = %6lu,\tgss = %4ld*420\n", B2, gss);
  }
  p = 0;
  NEXT_PRIME_VIADIFF(p,d);

  /* ---B1 PHASE--- */
  /* treat p=2 separately */
  B2_p = B2 >> 1;
  for (m=1; m<=B2_p; m<<=1)
  {
    int fl = elldouble(N, &g, nbc, X, X);
    if (fl > 1) return g; else if (fl) break;
  }
  rcn = NPRC; /* multipliers begin at the beginning */
  /* p=3,...,nextprime(B1) */
  while (p < B1 && p <= B2_rt)
  {
    pari_sp av2 = avma;
    p = snextpr(p, &d, &rcn, NULL, MR_foolproof);
    B2_p = B2/p; /* beware integer overflow on 32-bit CPUs */
    for (m=1; m<=B2_p; m*=p)
    {
      int fl = ellmult(N, &g, nbc, p, X, X, XAUX);
      if (fl > 1) return g; else if (fl) break;
      avma = av2;
    }
    avma = av2;
  }
  /* primes p larger than sqrt(B2) appear only to the 1st power */
  while (p < B1)
  {
    pari_sp av2 = avma;
    p = snextpr(p, &d, &rcn, NULL, MR_foolproof);
    if (ellmult(N, &g, nbc, p, X, X, XAUX) > 1) return g;
    avma = av2;
  }
  if (DEBUGLEVEL >= 4) {
    err_printf("ECM: time = %6ld ms, B1 phase done, ", timer_delay(&E->T));
    err_printf("p = %lu, setting up for B2\n", p);
  }

  /* ---B2 PHASE--- */
  /* compute [2]Q,...,[10]Q, needed to build the helix */
  if (elldouble(N, &g, nbc, X, XD) > 1) return g; /*[2]Q*/
  if (elldouble(N, &g, nbc, XD, XD + nbc2) > 1) return g; /*[4]Q*/
  if (ecm_elladd(N, &g, nbc,
        XD, XD + nbc2, XD + (nbc<<2)) > 1) return g; /* [6]Q */
  if (ecm_elladd2(N, &g, nbc,
        XD, XD + (nbc<<2), XT + (nbc<<3),
        XD + nbc2, XD + (nbc<<2), XD + (nbc<<3)) > 1)
    return g; /* [8]Q and [10]Q */
  if (DEBUGLEVEL >= 7) err_printf("\t(got [2]Q...[10]Q)\n");

  /* get next prime (still using the foolproof test) */
  p = snextpr(p, &d, &rcn, NULL, MR_foolproof);
  /* make sure we have the residue class number (mod 210) */
  if (rcn == NPRC)
  {
    rcn = prc210_no[(p % 210) >> 1];
    if (rcn == NPRC)
    {
      err_printf("ECM: %lu should have been prime but isn\'t\n", p);
      pari_err_BUG("ellfacteur");
    }
  }

  /* compute [p]Q and put it into its place in the helix */
  if (ellmult(N, &g, nbc, p, X, XH + rcn*nbc2, XAUX) > 1)
    return g;
  if (DEBUGLEVEL >= 7)
    err_printf("\t(got [p]Q, p = %lu = prc210_rp[%ld] mod 210)\n", p, rcn);

  /* save current p, d, and rcn;  we'll need them more than once below */
  p0 = p;
  d0 = d;
  rcn0 = rcn; /* remember where the helix wraps */
  bstp0 = 0; /* p is at baby-step offset 0 from itself */

  /* fill up the helix, stepping forward through the prime residue classes
   * mod 210 until we're back at the r'class of p0.  Keep updating p so
   * that we can print meaningful diagnostics if a factor shows up; don't
   * bother checking which of these p's are in fact prime */
  for (i = 47; i; i--) /* 47 iterations */
  {
    ulong dp = (ulong)prc210_d1[rcn];
    p += dp;
    if (rcn == 47)
    { /* wrap mod 210 */
      if (ecm_elladd(N, &g, nbc,
            XT+dp*nbc, XH+rcn*nbc2, XH) > 1) return g;
      rcn = 0; continue;
    }
    if (ecm_elladd(N, &g, nbc,
          XT+dp*nbc, XH+rcn*nbc2, XH+rcn*nbc2+nbc2) > 1)
      return g;
    rcn++;
  }
  if (DEBUGLEVEL >= 7) err_printf("\t(got initial helix)\n");
  /* compute [210]Q etc, needed for the baby step table */
  if (ellmult(N, &g, nbc, 3, XD + (nbc<<3), X, XAUX) > 1)
    return g;
  if (ellmult(N, &g, nbc, 7, X, X, XAUX) > 1)
    return g; /* [210]Q */
  /* this was the last call to ellmult() in the main loop body; may now
   * overwrite XAUX and slots XD and following */
  if (elldouble(N, &g, nbc, X, XAUX) > 1) return g; /* [420]Q */
  if (ecm_elladd(N, &g, nbc, X, XAUX, XT) > 1) return g;/*[630]Q*/
  if (ecm_elladd(N, &g, nbc, X, XT, XD) > 1) return g;  /*[840]Q*/
  for (i=1; i <= gse; i++)
    if (elldouble(N, &g, nbc, XT + i*nbc2, XD + i*nbc2) > 1)
      return g;
  /* (the last iteration has initialized XG to [210*2^(gse+1)]Q) */

  if (DEBUGLEVEL >= 4)
    err_printf("ECM: time = %6ld ms, entering B2 phase, p = %lu\n",
               timer_delay(&E->T), p);

  for (i = nbc - 4; i >= 0; i -= 4)
  { /* loop over small sets of 4 curves at a time */
    GEN *Xb;
    long j, k;
    if (DEBUGLEVEL >= 6)
      err_printf("ECM: finishing curves %ld...%ld\n", i, i+3);
    /* Copy relevant pointers from XH to Xh. Memory layout in XH:
     * nbc X coordinates, nbc Y coordinates for residue class
     * 1 mod 210, then the same for r.c. 11 mod 210, etc. Memory layout for
     * Xh is: four X coords for 1 mod 210, four for 11 mod 210, ..., four
     * for 209 mod 210, then the corresponding Y coordinates in the same
     * order. This allows a giant step on Xh using just three calls to
     * ecm_elladd0() each acting on 64 points in parallel */
    for (j = 48; j--; )
    {
      k = nbc2*j + i;
      m = j << 2; /* X coordinates */
      Xh[m]   = XH[k];   Xh[m+1] = XH[k+1];
      Xh[m+2] = XH[k+2]; Xh[m+3] = XH[k+3];
      k += nbc; /* Y coordinates */
      Yh[m]   = XH[k];   Yh[m+1] = XH[k+1];
      Yh[m+2] = XH[k+2]; Yh[m+3] = XH[k+3];
    }
    /* Build baby step table of X coords of multiples of [210]Q.  XB[4*j]
     * will point at X coords on four curves from [(j+1)*210]Q.  Until
     * we're done, we need some Y coords as well, which we keep in the
     * second half of the table, overwriting them at the end when gse=10.
     * Multiples which we already have  (by 1,2,3,4,8,16,...,2^gse) are
     * entered simply by copying the pointers, ignoring the few slots in w
     * that were initially reserved for them. Here are the initial entries */
    for (Xb=XB,k=2,j=i; k--; Xb=XB2,j+=nbc) /* first X, then Y coords */
    {
      Xb[0]  = X[j];      Xb[1]  = X[j+1]; /* [210]Q */
      Xb[2]  = X[j+2];    Xb[3]  = X[j+3];
      Xb[4]  = XAUX[j];   Xb[5]  = XAUX[j+1]; /* [420]Q */
      Xb[6]  = XAUX[j+2]; Xb[7]  = XAUX[j+3];
      Xb[8]  = XT[j];     Xb[9]  = XT[j+1]; /* [630]Q */
      Xb[10] = XT[j+2];   Xb[11] = XT[j+3];
      Xb += 4; /* points at [420]Q */
      /* ... entries at powers of 2 times 210 .... */
      for (m = 2; m < (ulong)gse+k; m++) /* omit Y coords of [2^gse*210]Q */
      {
        long m2 = m*nbc2 + j;
        Xb += (2UL<<m); /* points at [2^m*210]Q */
        Xb[0] = XAUX[m2];   Xb[1] = XAUX[m2+1];
        Xb[2] = XAUX[m2+2]; Xb[3] = XAUX[m2+3];
      }
    }
    if (DEBUGLEVEL >= 7)
      err_printf("\t(extracted precomputed helix / baby step entries)\n");
    /* ... glue in between, up to 16*210 ... */
    if (ecm_elladd0(N, &g, 12, 4, /* 12 pts + (4 pts replicated thrice) */
          XB + 12, XB2 + 12,
          XB,      XB2,
          XB + 16, XB2 + 16) > 1) return g; /*4+{1,2,3} = {5,6,7}*/
    if (ecm_elladd0(N, &g, 28, 4, /* 28 pts + (4 pts replicated 7fold) */
          XB + 28, XB2 + 28,
          XB,      XB2,
          XB + 32, XB2 + 32) > 1) return g;/*8+{1...7} = {9...15}*/
    /* ... and the remainder of the lot */
    for (m = 5; m <= (ulong)gse; m++)
    { /* fill in from 2^(m-1)+1 to 2^m-1 in chunks of 64 and 60 points */
      ulong m2 = 2UL << m; /* will point at 2^(m-1)+1 */
      for (j = 0; (ulong)j < m2-64; j+=64) /* executed 0 times when m = 5 */
      {
        if (ecm_elladd0(N, &g, 64, 4,
              XB + m2-4, XB2 + m2-4,
              XB + j,    XB2 + j,
              XB + m2+j, (m<(ulong)gse? XB2+m2+j: NULL)) > 1)
          return g;
      } /* j = m2-64 here, 60 points left */
      if (ecm_elladd0(N, &g, 60, 4,
            XB + m2-4, XB2 + m2-4,
            XB + j,    XB2 + j,
            XB + m2+j, (m<(ulong)gse? XB2+m2+j: NULL)) > 1)
        return g;
      /* when m=gse, drop Y coords of result, and when both equal 1024,
       * overwrite Y coords of second argument with X coords of result */
    }
    if (DEBUGLEVEL >= 7) err_printf("\t(baby step table complete)\n");
    /* initialize a few other things */
    bstp = bstp0;
    p = p0; d = d0; rcn = rcn0;
    g = gen_1; av1 = avma;
    /* scratchspace for prod (x_i-x_j) */
    avtmp = (pari_sp)new_chunk(8 * lgefint(N));
    /* The correct entry in XB to use depends on bstp and on where we are
     * on the helix. As we skip from prime to prime, bstp is incremented
     * by snextpr each time we wrap around through residue class number 0
     * (1 mod 210), but the baby step should not be taken until rcn>=rcn0,
     * i.e. until we pass again the residue class of p0.
     *
     * The correct signed multiplier is thus k = bstp - (rcn < rcn0),
     * and the offset from XB is four times (|k| - 1).  When k=0, we ignore
     * the current prime: if it had led to a factorization, this
     * would have been noted during the last giant step, or -- when we
     * first get here -- whilst initializing the helix.  When k > gss,
     * we must do a giant step and bump bstp back by -2*gss.
     *
     * The gcd of the product of X coord differences against N is taken just
     * before we do a giant step. */
    while (p < B2)
    {/* loop over probable primes p0 < p <= nextprime(B2), inserting giant
      * steps as necessary */
      p = snextpr(p, &d, &rcn, &bstp, MR_fast); /* next probable prime */
      /* work out the corresponding baby-step multiplier */
      k = bstp - (rcn < rcn0 ? 1 : 0);
      if (k > gss)
      { /* giant-step time, take gcd */
        g = gcdii(g, N);
        if (!is_pm1(g) && !equalii(g, N)) return g;
        g = gen_1; avma = av1;
        while (k > gss)
        { /* giant step */
          if (DEBUGLEVEL >= 7) err_printf("\t(giant step at p = %lu)\n", p);
          if (ecm_elladd0(N, &g, 64, 4, XG + i, YG + i,
                Xh, Yh, Xh, Yh) > 1) return g;
          if (ecm_elladd0(N, &g, 64, 4, XG + i, YG + i,
                Xh + 64, Yh + 64, Xh + 64, Yh + 64) > 1)
            return g;
          if (ecm_elladd0(N, &g, 64, 4, XG + i, YG + i,
                Xh + 128, Yh + 128, Xh + 128, Yh + 128) > 1)
            return g;
          bstp -= (gss << 1);
          k = bstp - (rcn < rcn0? 1: 0); /* recompute multiplier */
        }
      }
      if (!k) continue; /* point of interest is already in Xh */
      if (k < 0) k = -k;
      m = ((ulong)k - 1) << 2;
      /* accumulate product of differences of X coordinates */
      j = rcn<<2;
      avma = avtmp; /* go to garbage zone */
      g = modii(mulii(g, subii(XB[m],   Xh[j])), N);
      g = modii(mulii(g, subii(XB[m+1], Xh[j+1])), N);
      g = modii(mulii(g, subii(XB[m+2], Xh[j+2])), N);
      g = mulii(g, subii(XB[m+3], Xh[j+3]));
      avma = av1;
      g = modii(g, N);
    }
    avma = av1;
  }
  return NULL;
}

/* ellfacteur() tuned to be useful as a first stage before MPQS, especially for
 * large arguments, when 'insist' is false, and now also for the case when
 * 'insist' is true, vaguely following suggestions by Paul Zimmermann
 * (http://www.loria.fr/~zimmerma/records/ecmnet.html). --GN 1998Jul,Aug */
static GEN
ellfacteur(GEN N, int insist)
{
  const long size = expi(N) + 1;
  pari_sp av = avma;
  struct ECM E;
  long nbc, dsn, dsnmax, rep = 0;
  if (insist)
  {
    const long DSNMAX = numberof(TB1)-1;
    dsnmax = (size >> 2) - 10;
    if (dsnmax < 0) dsnmax = 0;
    else if (dsnmax > DSNMAX) dsnmax = DSNMAX;
    E.seed = 1 + (nbcmax<<7)*(size&0xffff); /* seed for choice of curves */

    dsn = (size >> 3) - 5;
    if (dsn < 0) dsn = 0; else if (dsn > 47) dsn = 47;
    /* pick up the torch where non-insistent stage would have given up */
    nbc = dsn + (dsn >> 2) + 9; /* 8 or more curves in parallel */
    nbc &= ~3; /* 4 | nbc */
  }
  else
  {
    dsn = (size - 140) >> 3;
    if (dsn < 0)
    {
#ifndef __EMX__ /* unless DOS/EMX: MPQS's disk access is abysmally slow */
      if (DEBUGLEVEL >= 4)
        err_printf("ECM: number too small to justify this stage\n");
      return NULL; /* too small, decline the task */
#endif
      dsn = 0;
    } else if (dsn > 12) dsn = 12;
    rep = (size <= 248 ?
           (size <= 176 ? (size - 124) >> 4 : (size - 148) >> 3) :
           (size - 224) >> 1);
#ifdef __EMX__ /* DOS/EMX: extra rounds (shun MPQS) */
    rep += 20;
#endif
    dsnmax = 72;
    /* Use disjoint sets of curves for non-insist and insist phases; moreover,
     * repeated calls acting on factors of the same original number should try
     * to use fresh curves. The following achieves this */
    E.seed = 1 + (nbcmax<<3)*(size & 0xf);
    nbc = -1;
  }
  ECM_init(&E, N, nbc);
  if (DEBUGLEVEL >= 4)
  {
    timer_start(&E.T);
    err_printf("ECM: working on %ld curves at a time; initializing", E.nbc);
    if (!insist)
    {
      if (rep == 1) err_printf(" for one round");
      else          err_printf(" for up to %ld rounds", rep);
    }
    err_printf("...\n");
  }
  if (dsn > dsnmax) dsn = dsnmax;
  for(;;)
  {
    ulong B1 = insist? TB1[dsn]: TB1_for_stage[dsn];
    GEN g = ECM_loop(&E, N, B1);
    if (g)
    {
      if (DEBUGLEVEL >= 4)
        err_printf("ECM: time = %6ld ms\n\tfound factor = %Ps\n",
                   timer_delay(&E.T), g);
      return gerepilecopy(av, g);
    }
    if (dsn < dsnmax)
    {
      if (insist) dsn++;
      else { dsn += 2; if (dsn > dsnmax) dsn = dsnmax; }
    }
    if (!insist && !--rep)
    {
      if (DEBUGLEVEL >= 4)
        err_printf("ECM: time = %6ld ms,\tellfacteur giving up.\n",
                   timer_delay(&E.T));
      avma = av; return NULL;
    }
  }
}
/* assume rounds >= 1, seed >= 1, B1 <= ULONG_MAX / 110 */
GEN
Z_ECM(GEN N, long rounds, long seed, ulong B1)
{
  pari_sp av = avma;
  struct ECM E;
  long i;
  E.seed = seed;
  ECM_init(&E, N, -1);
  if (DEBUGLEVEL >= 4) timer_start(&E.T);
  for (i = rounds; i--; )
  {
    GEN g = ECM_loop(&E, N, B1);
    if (g) return gerepilecopy(av, g);
  }
  avma = av; return NULL;
}

/***********************************************************************/
/**                                                                   **/
/**                FACTORIZATION (Pollard-Brent rho) --GN1998Jun18-26 **/
/**  pollardbrent() returns a nontrivial factor of n, assuming n is   **/
/**  composite and has no small prime divisor, or NULL if going on    **/
/**  would take more time than we want to spend.  Sometimes it finds  **/
/**  more than one factor, and returns a structure suitable for       **/
/**  interpretation by ifac_crack. (Cf Algo 8.5.2 in ACiCNT)          **/
/**                                                                   **/
/***********************************************************************/
#define VALUE(x) gel(x,0)
#define EXPON(x) gel(x,1)
#define CLASS(x) gel(x,2)

INLINE void
INIT(GEN x, GEN v, GEN e, GEN c) {
  VALUE(x) = v;
  EXPON(x) = e;
  CLASS(x) = c;
}
static void
ifac_delete(GEN x) { INIT(x,NULL,NULL,NULL); }

static void
rho_dbg(pari_timer *T, long c, long msg_mask)
{
  if (c & msg_mask) return;
  err_printf("Rho: time = %6ld ms,\t%3ld round%s\n",
             timer_delay(T), c, (c==1?"":"s"));
}

static void
one_iter(GEN *x, GEN *P, GEN x1, GEN n, long delta)
{
  *x = addis(remii(sqri(*x), n), delta);
  *P = modii(mulii(*P, subii(x1, *x)), n);
}
/* Return NULL when we run out of time, or a single t_INT containing a
 * nontrivial factor of n, or a vector of t_INTs, each triple of successive
 * entries containing a factor, an exponent (equal to one),  and a factor
 * class (NULL for unknown or zero for known composite),  matching the
 * internal representation used by the ifac_*() routines below. Repeated
 * factors may arise; the caller will sort the factors anyway. Result
 * is not gerepile-able (contains NULL) */
static GEN
pollardbrent_i(GEN n, long size, long c0, long retries)
{
  long tf = lgefint(n), delta, msg_mask, c, k, k1, l;
  pari_sp av;
  GEN x, x1, y, P, g, g1, res;
  pari_timer T;

  if (DEBUGLEVEL >= 4) timer_start(&T);
  c = c0 << 5; /* 2^5 iterations per round */
  msg_mask = (size >= 448? 0x1fff:
                           (size >= 192? (256L<<((size-128)>>6))-1: 0xff));
  y = cgeti(tf);
  x1= cgeti(tf);
  av = avma;

PB_RETRY:
 /* trick to make a 'random' choice determined by n.  Don't use x^2+0 or
  * x^2-2, ever.  Don't use x^2-3 or x^2-7 with a starting value of 2.
  * x^2+4, x^2+9 are affine conjugate to x^2+1, so don't use them either.
  *
  * (the point being that when we get called again on a composite cofactor
  * of something we've already seen, we had better avoid the same delta) */
  switch ((size + retries) & 7)
  {
    case 0:  delta=  1; break;
    case 1:  delta= -1; break;
    case 2:  delta=  3; break;
    case 3:  delta=  5; break;
    case 4:  delta= -5; break;
    case 5:  delta=  7; break;
    case 6:  delta= 11; break;
    /* case 7: */
    default: delta=-11; break;
  }
  if (DEBUGLEVEL >= 4)
  {
    if (!retries)
      err_printf("Rho: searching small factor of %ld-bit integer\n", size);
    else
      err_printf("Rho: restarting for remaining rounds...\n");
    err_printf("Rho: using X^2%+1ld for up to %ld rounds of 32 iterations\n",
               delta, c >> 5);
  }
  x = gen_2; P = gen_1; g1 = NULL; k = 1; l = 1;
  affui(2, y);
  affui(2, x1);
  for (;;) /* terminated under the control of c */
  { /* use the polynomial  x^2 + delta */
    one_iter(&x, &P, x1, n, delta);

    if ((--c & 0x1f)==0)
    { /* one round complete */
      g = gcdii(n, P); if (!is_pm1(g)) goto fin;
      if (c <= 0)
      { /* getting bored */
        if (DEBUGLEVEL >= 4)
          err_printf("Rho: time = %6ld ms,\tPollard-Brent giving up.\n",
                     timer_delay(&T));
        return NULL;
      }
      P = gen_1;
      if (DEBUGLEVEL >= 4) rho_dbg(&T, c0-(c>>5), msg_mask);
      affii(x,y); x = y; avma = av;
    }

    if (--k) continue; /* normal end of loop body */

    if (c & 0x1f) /* otherwise, we already checked */
    {
      g = gcdii(n, P); if (!is_pm1(g)) goto fin;
      P = gen_1;
    }

   /* Fast forward phase, doing l inner iterations without computing gcds.
    * Check first whether it would take us beyond the alloted time.
    * Fast forward rounds count only half (although they're taking
    * more like 2/3 the time of normal rounds).  This to counteract the
    * nuisance that all c0 between 4096 and 6144 would act exactly as
    * 4096;  with the halving trick only the range 4096..5120 collapses
    * (similarly for all other powers of two) */
    if ((c -= (l>>1)) <= 0)
    { /* got bored */
      if (DEBUGLEVEL >= 4)
        err_printf("Rho: time = %6ld ms,\tPollard-Brent giving up.\n",
                   timer_delay(&T));
      return NULL;
    }
    c &= ~0x1f; /* keep it on multiples of 32 */

    /* Fast forward loop */
    affii(x, x1); avma = av; x = x1;
    k = l; l <<= 1;
    /* don't show this for the first several (short) fast forward phases. */
    if (DEBUGLEVEL >= 4 && (l>>7) > msg_mask)
      err_printf("Rho: fast forward phase (%ld rounds of 64)...\n", l>>7);
    for (k1=k; k1; k1--)
    {
      one_iter(&x, &P, x1, n, delta);
      if ((k1 & 0x1f) == 0) gerepileall(av, 2, &x, &P);
    }
    if (DEBUGLEVEL >= 4 && (l>>7) > msg_mask)
      err_printf("Rho: time = %6ld ms,\t%3ld rounds, back to normal mode\n",
                 timer_delay(&T), c0-(c>>5));
    affii(x,y); P = gerepileuptoint(av, P); x = y;
  } /* forever */

fin:
  /* An accumulated gcd was > 1 */
  if  (!equalii(g,n))
  { /* if it isn't n, and looks prime, return it */
    if (MR_Jaeschke(g))
    {
      if (DEBUGLEVEL >= 4)
      {
        rho_dbg(&T, c0-(c>>5), 0);
        err_printf("\tfound factor = %Ps\n",g);
      }
      return g;
    }
    avma = av; g1 = icopy(g);  /* known composite, keep it safe */
    av = avma;
  }
  else g1 = n; /* and work modulo g1 for backtracking */

  /* Here g1 is known composite */
  if (DEBUGLEVEL >= 4 && size > 192)
    err_printf("Rho: hang on a second, we got something here...\n");
  x = y;
  for(;;)
  { /* backtrack until period recovered. Must terminate */
    x = addis(remii(sqri(x), g1), delta);
    g = gcdii(subii(x1, x), g1); if (!is_pm1(g)) break;

    if (DEBUGLEVEL >= 4 && (--c & 0x1f) == 0) rho_dbg(&T, c0-(c>>5), msg_mask);
  }

  if (g1 == n || equalii(g,g1))
  {
    if (g1 == n && equalii(g,g1))
    { /* out of luck */
      if (DEBUGLEVEL >= 4)
      {
        rho_dbg(&T, c0-(c>>5), 0);
        err_printf("\tPollard-Brent failed.\n");
      }
      if (++retries >= 4) pari_err_BUG("");
      goto PB_RETRY;
    }
    /* half lucky: we've split n, but g1 equals either g or n */
    if (DEBUGLEVEL >= 4)
    {
      rho_dbg(&T, c0-(c>>5), 0);
      err_printf("\tfound %sfactor = %Ps\n", (g1!=n ? "composite " : ""), g);
    }
    res = cgetg(7, t_VEC);
    /* g^1: known composite when g1!=n */
    INIT(res+1, g, gen_1, (g1!=n? gen_0: NULL));
    /* cofactor^1: status unknown */
    INIT(res+4, diviiexact(n,g), gen_1, NULL);
    return res;
  }
  /* g < g1 < n : our lucky day -- we've split g1, too */
  res = cgetg(10, t_VEC);
  /* unknown status for all three factors */
  INIT(res+1, g,                gen_1, NULL);
  INIT(res+4, diviiexact(g1,g), gen_1, NULL);
  INIT(res+7, diviiexact(n,g1), gen_1, NULL);
  if (DEBUGLEVEL >= 4)
  {
    rho_dbg(&T, c0-(c>>5), 0);
    err_printf("\tfound factors = %Ps, %Ps,\n\tand %Ps\n",
               gel(res,1), gel(res,4), gel(res,7));
  }
  return res;
}
/* Tuning parameter:  for input up to 64 bits long, we must not spend more
 * than a very short time, for fear of slowing things down on average.
 * With the current tuning formula, increase our efforts somewhat at 49 bit
 * input (an extra round for each bit at first),  and go up more and more
 * rapidly after we pass 80 bits.-- Changed this to adjust for the presence of
 * squfof, which will finish input up to 59 bits quickly. */
static GEN
pollardbrent(GEN n)
{
  const long tune_pb_min = 14; /* even 15 seems too much. */
  long c0, size = expi(n) + 1;
  if (size <= 28)
    c0 = 32;/* amounts very nearly to 'insist'. Now that we have squfof(), we
             * don't insist any more when input is 2^29 ... 2^32 */
  else if (size <= 42)
    c0 = tune_pb_min;
  else if (size <= 59) /* match squfof() cutoff point */
    c0 = tune_pb_min + ((size - 42)<<1);
  else if (size <= 72)
    c0 = tune_pb_min + size - 24;
  else if (size <= 301)
    /* nonlinear increase in effort, kicking in around 80 bits */
    /* 301 gives 48121 + tune_pb_min */
    c0 = tune_pb_min + size - 60 +
      ((size-73)>>1)*((size-70)>>3)*((size-56)>>4);
  else
    c0 = 49152; /* ECM is faster when it'd take longer */
  return pollardbrent_i(n, size, c0, 0);
}
GEN
Z_pollardbrent(GEN n, long rounds, long seed)
{
  pari_sp av = avma;
  GEN v = pollardbrent_i(n, expi(n)+1, rounds, seed);
  if (!v) return NULL;
  if (typ(v) == t_INT) v = mkvec2(v, diviiexact(n,v));
  else if (lg(v) == 7) v = mkvec2(gel(v,1), gel(v,4));
  else v = mkvec3(gel(v,1), gel(v,4), gel(v,7));
  return gerepilecopy(av, v);
}

/***********************************************************************/
/**              FACTORIZATION (Shanks' SQUFOF) --GN2000Sep30-Oct01   **/
/**  squfof() returns a nontrivial factor of n, assuming n is odd,    **/
/**  composite, not a pure square, and has no small prime divisor,    **/
/**  or NULL if it fails to find one.  It works on two discriminants  **/
/**  simultaneously  (n and 5n for n=1(4), 3n and 4n for n=3(4)).     **/
/**  Present implementation is limited to input <2^59, and works most **/
/**  of the time in signed arithmetic on integers <2^31 in absolute   **/
/**  size. (Cf. Algo 8.7.2 in ACiCNT)                                 **/
/***********************************************************************/

/* The following is invoked to walk back along the ambiguous cycle* until we
 * hit an ambiguous form and thus the desired factor, which it returns.  If it
 * fails for any reason, it returns 0.  It doesn't interfere with timing and
 * diagnostics, which it leaves to squfof().
 *
 * Before we invoke this, we've found a form (A, B, -C) with A = a^2, where a
 * isn't blacklisted and where gcd(a, B) = 1.  According to ACiCANT, we should
 * now proceed reducing the form (a, -B, -aC), but it is easy to show that the
 * first reduction step always sends this to (-aC, B, a), and the next one,
 * with q computed as usual from B and a (occupying the c position), gives a
 * reduced form, whose third member is easiest to recover by going back to D.
 * From this point onwards, we're once again working with single-word numbers.
 * No need to track signs, just work with the abs values of the coefficients. */
static long
squfof_ambig(long a, long B, long dd, GEN D)
{
  long b, c, q, qa, qc, qcb, a0, b0, b1, c0;
  long cnt = 0; /* count reduction steps on the cycle */

  q = (dd + (B>>1)) / a;
  qa = q * a;
  b = (qa - B) + qa; /* avoid overflow */
  {
    pari_sp av = avma;
    c = itos(divis(shifti(subii(D, sqrs(b)), -2), a));
    avma = av;
  }
#ifdef DEBUG_SQUFOF
  err_printf("SQUFOF: ambigous cycle of discriminant %Ps\n", D);
  err_printf("SQUFOF: Form on ambigous cycle (%ld, %ld, %ld)\n", a, b, c);
#endif

  a0 = a; b0 = b1 = b;        /* end of loop detection and safeguard */

  for (;;) /* reduced cycles are finite */
  { /* reduction step */
    c0 = c;
    if (c0 > dd)
      q = 1;
    else
      q = (dd + (b>>1)) / c0;
    if (q == 1)
    {
      qcb = c0 - b; b = c0 + qcb; c = a - qcb;
    }
    else
    {
      qc = q*c0; qcb = qc - b; b = qc + qcb; c = a - q*qcb;
    }
    a = c0;

    cnt++; if (b == b1) break;

    /* safeguard against infinite loop: recognize when we've walked the entire
     * cycle in vain. (I don't think this can actually happen -- exercise.) */
    if (b == b0 && a == a0) return 0;

    b1 = b;
  }
  q = a&1 ? a : a>>1;
  if (DEBUGLEVEL >= 4)
  {
    if (q > 1)
      err_printf("SQUFOF: found factor %ld from ambiguous form\n"
                 "\tafter %ld steps on the ambiguous cycle\n",
                 q / ugcd(q,15), cnt);
    else
      err_printf("SQUFOF: ...found nothing on the ambiguous cycle\n"
                 "\tafter %ld steps there\n", cnt);
    if (DEBUGLEVEL >= 6) err_printf("SQUFOF: squfof_ambig returned %ld\n", q);
  }
  return q;
}

#define SQUFOF_BLACKLIST_SZ 64

/* assume 2,3,5 do not divide n */
static GEN
squfof(GEN n)
{
  ulong d1, d2;
  long tf = lgefint(n), nm4, cnt = 0;
  long a1, b1, c1, dd1, L1, a2, b2, c2, dd2, L2, a, q, c, qc, qcb;
  GEN D1, D2;
  pari_sp av = avma;
  long blacklist1[SQUFOF_BLACKLIST_SZ], blacklist2[SQUFOF_BLACKLIST_SZ];
  long blp1 = 0, blp2 = 0;
  int act1 = 1, act2 = 1;

#ifdef LONG_IS_64BIT
  if (tf > 3 || (tf == 3 && uel(n,2)             >= (1UL << (BITS_IN_LONG-5))))
#else  /* 32 bits */
  if (tf > 4 || (tf == 4 && (ulong)(*int_MSW(n)) >= (1UL << (BITS_IN_LONG-5))))
#endif
    return NULL; /* n too large */

  /* now we have 5 < n < 2^59 */
  nm4 = mod4(n);
  if (nm4 == 1)
  { /* n = 1 (mod4):  run one iteration on D1 = n, another on D2 = 5n */
    D1 = n;
    D2 = mului(5,n); d2 = itou(sqrti(D2)); dd2 = (long)((d2>>1) + (d2&1));
    b2 = (long)((d2-1) | 1);        /* b1, b2 will always stay odd */
  }
  else
  { /* n = 3 (mod4):  run one iteration on D1 = 3n, another on D2 = 4n */
    D1 = mului(3,n);
    D2 = shifti(n,2); dd2 = itou(sqrti(n)); d2 =  dd2 << 1;
    b2 = (long)(d2 & (~1UL)); /* largest even below d2, will stay even */
  }
  d1 = itou(sqrti(D1));
  b1 = (long)((d1-1) | 1); /* largest odd number not exceeding d1 */
  c1 = itos(shifti(subii(D1, sqru((ulong)b1)), -2));
  if (!c1) pari_err_BUG("squfof [caller of] (n or 3n is a square)");
  c2 = itos(shifti(subii(D2, sqru((ulong)b2)), -2));
  if (!c2) pari_err_BUG("squfof [caller of] (5n is a square)");
  L1 = (long)usqrt(d1);
  L2 = (long)usqrt(d2);
  /* dd1 used to compute floor((d1+b1)/2) as dd1+floor(b1/2), without
   * overflowing the 31bit signed integer size limit. Same for dd2. */
  dd1 = (long) ((d1>>1) + (d1&1));
  a1 = a2 = 1;

  /* The two (identity) forms (a1,b1,-c1) and (a2,b2,-c2) are now set up.
   *
   * a1 and c1 represent the absolute values of the a,c coefficients; we keep
   * track of the sign separately, via the iteration counter cnt: when cnt is
   * even, c is understood to be negative, else c is positive and a < 0.
   *
   * L1, L2 are the limits for blacklisting small leading coefficients
   * on the principal cycle, to guarantee that when we find a square form,
   * its square root will belong to an ambiguous cycle  (i.e. won't be an
   * earlier form on the principal cycle).
   *
   * When n = 3(mod 4), D2 = 12(mod 16), and b^2 is always 0 or 4 mod 16.
   * It follows that 4*a*c must be 4 or 8 mod 16, respectively, so at most
   * one of a,c can be divisible by 2 at most to the first power.  This fact
   * is used a couple of times below.
   *
   * The flags act1, act2 remain true while the respective cycle is still
   * active;  we drop them to false when we return to the identity form with-
   * out having found a square form  (or when the blacklist overflows, which
   * shouldn't happen). */
  if (DEBUGLEVEL >= 4)
    err_printf("SQUFOF: entering main loop with forms\n"
               "\t(1, %ld, %ld) and (1, %ld, %ld)\n\tof discriminants\n"
               "\t%Ps and %Ps, respectively\n", b1, -c1, b2, -c2, D1, D2);

  /* MAIN LOOP: walk around the principal cycle looking for a square form.
   * Blacklist small leading coefficients.
   *
   * The reduction operator can be computed entirely in 32-bit arithmetic:
   * Let q = floor(floor((d1+b1)/2)/c1)  (when c1>dd1, q=1, which happens
   * often enough to special-case it).  Then the new b1 = (q*c1-b1) + q*c1,
   * which does not overflow, and the new c1 = a1 - q*(q*c1-b1), which is
   * bounded by d1 in abs size since both the old and the new a1 are positive
   * and bounded by d1. */
  while (act1 || act2)
  {
    if (act1)
    { /* send first form through reduction operator if active */
      c = c1;
      q = (c > dd1)? 1: (dd1 + (b1>>1)) / c;
      if (q == 1)
      { qcb = c - b1; b1 = c + qcb; c1 = a1 - qcb; }
      else
      { qc = q*c; qcb = qc - b1; b1 = qc + qcb; c1 = a1 - q*qcb; }
      a1 = c;

      if (a1 <= L1)
      { /* blacklist this */
        if (blp1 >= SQUFOF_BLACKLIST_SZ) /* overflows: shouldn't happen */
          act1 = 0; /* silently */
        else
        {
          if (DEBUGLEVEL >= 6)
            err_printf("SQUFOF: blacklisting a = %ld on first cycle\n", a1);
          blacklist1[blp1++] = a1;
        }
      }
    }
    if (act2)
    { /* send second form through reduction operator if active */
      c = c2;
      q = (c > dd2)? 1: (dd2 + (b2>>1)) / c;
      if (q == 1)
      { qcb = c - b2; b2 = c + qcb; c2 = a2 - qcb; }
      else
      { qc = q*c; qcb = qc - b2; b2 = qc + qcb; c2 = a2 - q*qcb; }
      a2 = c;

      if (a2 <= L2)
      { /* blacklist this */
        if (blp2 >= SQUFOF_BLACKLIST_SZ) /* overflows: shouldn't happen */
          act2 = 0; /* silently */
        else
        {
          if (DEBUGLEVEL >= 6)
            err_printf("SQUFOF: blacklisting a = %ld on second cycle\n", a2);
          blacklist2[blp2++] = a2;
        }
      }
    }

    /* bump counter, loop if this is an odd iteration (i.e. if the real
     * leading coefficients are negative) */
    if (++cnt & 1) continue;

    /* second half of main loop entered only when the leading coefficients
     * are positive (i.e., during even-numbered iterations) */

    /* examine first form if active */
    if (act1 && a1 == 1) /* back to identity */
    { /* drop this discriminant */
      act1 = 0;
      if (DEBUGLEVEL >= 4)
        err_printf("SQUFOF: first cycle exhausted after %ld iterations,\n"
                   "\tdropping it\n", cnt);
    }
    if (act1)
    {
      if (uissquareall((ulong)a1, (ulong*)&a))
      { /* square form */
        if (DEBUGLEVEL >= 4)
          err_printf("SQUFOF: square form (%ld^2, %ld, %ld) on first cycle\n"
                     "\tafter %ld iterations\n", a, b1, -c1, cnt);
        if (a <= L1)
        { /* blacklisted? */
          long j;
          for (j = 0; j < blp1; j++)
            if (a == blacklist1[j]) { a = 0; break; }
        }
        if (a > 0)
        { /* not blacklisted */
          q = ugcd(a, b1); /* imprimitive form? */
          if (q > 1)
          { /* q^2 divides D1 hence n [ assuming n % 3 != 0 ] */
            avma = av;
            if (DEBUGLEVEL >= 4) err_printf("SQUFOF: found factor %ld^2\n", q);
            return mkvec3(utoipos(q), gen_2, NULL);/* exponent 2, unknown status */
          }
          /* chase the inverse root form back along the ambiguous cycle */
          q = squfof_ambig(a, b1, dd1, D1);
          if (nm4 == 3 && q % 3 == 0) q /= 3;
          if (q > 1) { avma = av; return utoipos(q); } /* SUCCESS! */
        }
        else if (DEBUGLEVEL >= 4) /* blacklisted */
          err_printf("SQUFOF: ...but the root form seems to be on the "
                     "principal cycle\n");
      }
    }

    /* examine second form if active */
    if (act2 && a2 == 1) /* back to identity form */
    { /* drop this discriminant */
      act2 = 0;
      if (DEBUGLEVEL >= 4)
        err_printf("SQUFOF: second cycle exhausted after %ld iterations,\n"
                   "\tdropping it\n", cnt);
    }
    if (act2)
    {
      if (uissquareall((ulong)a2, (ulong*)&a))
      { /* square form */
        if (DEBUGLEVEL >= 4)
          err_printf("SQUFOF: square form (%ld^2, %ld, %ld) on second cycle\n"
                     "\tafter %ld iterations\n", a, b2, -c2, cnt);
        if (a <= L2)
        { /* blacklisted? */
          long j;
          for (j = 0; j < blp2; j++)
            if (a == blacklist2[j]) { a = 0; break; }
        }
        if (a > 0)
        { /* not blacklisted */
          q = ugcd(a, b2); /* imprimitive form? */
          /* NB if b2 is even, a is odd, so the gcd is always odd */
          if (q > 1)
          { /* q^2 divides D2 hence n [ assuming n % 5 != 0 ] */
            avma = av;
            if (DEBUGLEVEL >= 4) err_printf("SQUFOF: found factor %ld^2\n", q);
            return mkvec3(utoipos(q), gen_2, NULL);/* exponent 2, unknown status */
          }
          /* chase the inverse root form along the ambiguous cycle */
          q = squfof_ambig(a, b2, dd2, D2);
          if (nm4 == 1 && q % 5 == 0) q /= 5;
          if (q > 1) { avma = av; return utoipos(q); } /* SUCCESS! */
        }
        else if (DEBUGLEVEL >= 4)        /* blacklisted */
          err_printf("SQUFOF: ...but the root form seems to be on the "
                     "principal cycle\n");
      }
    }
  } /* end main loop */

  /* both discriminants turned out to be useless. */
  if (DEBUGLEVEL>=4) err_printf("SQUFOF: giving up\n");
  avma = av; return NULL;
}

/***********************************************************************/
/*                    DETECTING ODD POWERS  --GN1998Jun28              */
/*   Factoring engines like MPQS which ultimately rely on computing    */
/*   gcd(N, x^2-y^2) to find a nontrivial factor of N can't split      */
/*   N = p^k for an odd prime p, since (Z/p^k)^* is then cyclic. Here  */
/*   is an analogue of Z_issquareall() for 3rd, 5th and 7th powers.    */
/*   The general case is handled by is_kth_power                       */
/***********************************************************************/

/* Multistage sieve. First stages work mod 211, 209, 61, 203 in this order
 * (first reduce mod the product of these and then take the remainder apart).
 * Second stages use 117, 31, 43, 71. Moduli which are no longer interesting
 * are skipped. Everything is encoded in a table of 106 24-bit masks. We only
 * need the first half of the residues.  Three bits per modulus indicate which
 * residues are 7th (bit 2), 5th (bit 1) or 3rd (bit 0) powers; the eight
 * moduli above are assigned right-to-left. The table was generated using: */

#if 0
L = [71, 43, 31, [O(3^2),O(13)], [O(7),O(29)], 61, [O(11),O(19)], 211];
ispow(x, N, k)=
{
  if (type(N) == "t_INT", return (ispower(Mod(x,N), k)));
  for (i = 1, #N, if (!ispower(x + N[i], k), return (0))); 1
}
check(r) =
{
  print1("  0");
  for (i=1,#L,
    N = 0;
    if (ispow(r, L[i], 3), N += 1);
    if (ispow(r, L[i], 5), N += 2);
    if (ispow(r, L[i], 7), N += 4);
    print1(N);
  ); print("ul,  /* ", r, " */")
}
for (r = 0, 105, check(r))
#endif
static ulong powersmod[106] = {
  077777777ul,  /* 0 */
  077777777ul,  /* 1 */
  013562440ul,  /* 2 */
  012402540ul,  /* 3 */
  013562440ul,  /* 4 */
  052662441ul,  /* 5 */
  016603440ul,  /* 6 */
  016463450ul,  /* 7 */
  013573551ul,  /* 8 */
  012462540ul,  /* 9 */
  012462464ul,  /* 10 */
  013462771ul,  /* 11 */
  012406473ul,  /* 12 */
  012463641ul,  /* 13 */
  052463646ul,  /* 14 */
  012503446ul,  /* 15 */
  013562440ul,  /* 16 */
  052466440ul,  /* 17 */
  012472451ul,  /* 18 */
  012462454ul,  /* 19 */
  032463550ul,  /* 20 */
  013403664ul,  /* 21 */
  013463460ul,  /* 22 */
  032562565ul,  /* 23 */
  012402540ul,  /* 24 */
  052662441ul,  /* 25 */
  032672452ul,  /* 26 */
  013573551ul,  /* 27 */
  012467541ul,  /* 28 */
  012567640ul,  /* 29 */
  032706450ul,  /* 30 */
  012762452ul,  /* 31 */
  033762662ul,  /* 32 */
  012502562ul,  /* 33 */
  032463562ul,  /* 34 */
  013563440ul,  /* 35 */
  016663440ul,  /* 36 */
  036662550ul,  /* 37 */
  012462552ul,  /* 38 */
  033502450ul,  /* 39 */
  012462643ul,  /* 40 */
  033467540ul,  /* 41 */
  017403441ul,  /* 42 */
  017463462ul,  /* 43 */
  017472460ul,  /* 44 */
  033462470ul,  /* 45 */
  052566450ul,  /* 46 */
  013562640ul,  /* 47 */
  032403640ul,  /* 48 */
  016463450ul,  /* 49 */
  016463752ul,  /* 50 */
  033402440ul,  /* 51 */
  012462540ul,  /* 52 */
  012472540ul,  /* 53 */
  053562462ul,  /* 54 */
  012463465ul,  /* 55 */
  012663470ul,  /* 56 */
  052607450ul,  /* 57 */
  012566553ul,  /* 58 */
  013466440ul,  /* 59 */
  012502741ul,  /* 60 */
  012762744ul,  /* 61 */
  012763740ul,  /* 62 */
  012763443ul,  /* 63 */
  013573551ul,  /* 64 */
  013462471ul,  /* 65 */
  052502460ul,  /* 66 */
  012662463ul,  /* 67 */
  012662451ul,  /* 68 */
  012403550ul,  /* 69 */
  073567540ul,  /* 70 */
  072463445ul,  /* 71 */
  072462740ul,  /* 72 */
  012472442ul,  /* 73 */
  012462644ul,  /* 74 */
  013406650ul,  /* 75 */
  052463471ul,  /* 76 */
  012563474ul,  /* 77 */
  013503460ul,  /* 78 */
  016462441ul,  /* 79 */
  016462440ul,  /* 80 */
  012462540ul,  /* 81 */
  013462641ul,  /* 82 */
  012463454ul,  /* 83 */
  013403550ul,  /* 84 */
  057563540ul,  /* 85 */
  017466441ul,  /* 86 */
  017606471ul,  /* 87 */
  053666573ul,  /* 88 */
  012562561ul,  /* 89 */
  013473641ul,  /* 90 */
  032573440ul,  /* 91 */
  016763440ul,  /* 92 */
  016702640ul,  /* 93 */
  033762552ul,  /* 94 */
  012562550ul,  /* 95 */
  052402451ul,  /* 96 */
  033563441ul,  /* 97 */
  012663561ul,  /* 98 */
  012677560ul,  /* 99 */
  012462464ul,  /* 100 */
  032562642ul,  /* 101 */
  013402551ul,  /* 102 */
  032462450ul,  /* 103 */
  012467445ul,  /* 104 */
  032403440ul,  /* 105 */
};

static int
check_res(ulong x, ulong N, int shift, ulong *mask)
{
  long r = x%N; if ((ulong)r> (N>>1)) r = N - r;
  *mask &= (powersmod[r] >> shift);
  return *mask;
}

/* is x mod 211*209*61*203*117*31*43*71 a 3rd, 5th or 7th power ? */
int
uis_357_powermod(ulong x, ulong *mask)
{
  if (             !check_res(x, 211UL, 0, mask)) return 0;
  if (*mask & 3 && !check_res(x, 209UL, 3, mask)) return 0;
  if (*mask & 3 && !check_res(x,  61UL, 6, mask)) return 0;
  if (*mask & 5 && !check_res(x, 203UL, 9, mask)) return 0;
  if (*mask & 1 && !check_res(x, 117UL,12, mask)) return 0;
  if (*mask & 3 && !check_res(x,  31UL,15, mask)) return 0;
  if (*mask & 5 && !check_res(x,  43UL,18, mask)) return 0;
  if (*mask & 6 && !check_res(x,  71UL,21, mask)) return 0;
  return 1;
}
/* asume x > 0 and pt != NULL */
int
uis_357_power(ulong x, ulong *pt, ulong *mask)
{
  double logx;
  if (!odd(x))
  {
    long v = vals(x);
    if (v % 7) *mask &= ~4;
    if (v % 5) *mask &= ~2;
    if (v % 3) *mask &= ~1;
    if (!*mask) return 0;
  }
  if (!uis_357_powermod(x, mask)) return 0;
  logx = log((double)x);
  while (*mask)
  {
    long e, b;
    ulong y, ye;
    if (*mask & 1)      { b = 1; e = 3; }
    else if (*mask & 2) { b = 2; e = 5; }
    else                { b = 4; e = 7; }
    y = (ulong)(exp(logx / e) + 0.5);
    ye = upowuu(y,e);
    if (ye == x) { *pt = y; return e; }
#ifdef LONG_IS_64BIT
    if (ye > x) y--; else y++;
    ye = upowuu(y,e);
    if (ye == x) { *pt = y; return e; }
#endif
    *mask &= ~b; /* turn the bit off */
  }
  return 0;
}

#ifndef LONG_IS_64BIT
/* as above, split in two functions */
/* is x mod 211*209*61*203 a 3rd, 5th or 7th power ? */
static int
uis_357_powermod_32bit_1(ulong x, ulong *mask)
{
  if (             !check_res(x, 211UL, 0, mask)) return 0;
  if (*mask & 3 && !check_res(x, 209UL, 3, mask)) return 0;
  if (*mask & 3 && !check_res(x,  61UL, 6, mask)) return 0;
  if (*mask & 5 && !check_res(x, 203UL, 9, mask)) return 0;
  return 1;
}
/* is x mod 117*31*43*71 a 3rd, 5th or 7th power ? */
static int
uis_357_powermod_32bit_2(ulong x, ulong *mask)
{
  if (*mask & 1 && !check_res(x, 117UL,12, mask)) return 0;
  if (*mask & 3 && !check_res(x,  31UL,15, mask)) return 0;
  if (*mask & 5 && !check_res(x,  43UL,18, mask)) return 0;
  if (*mask & 6 && !check_res(x,  71UL,21, mask)) return 0;
  return 1;
}
#endif

/* Returns 3, 5, or 7 if x is a cube (but not a 5th or 7th power),  a 5th
 * power (but not a 7th),  or a 7th power, and in this case creates the
 * base on the stack and assigns its address to *pt.  Otherwise returns 0.
 * x must be of type t_INT and positive;  this is not checked.  The *mask
 * argument tells us which things to check -- bit 0: 3rd, bit 1: 5th,
 * bit 2: 7th pwr;  set a bit to have the corresponding power examined --
 * and is updated appropriately for a possible follow-up call */
int
is_357_power(GEN x, GEN *pt, ulong *mask)
{
  long lx = lgefint(x);
  ulong r;
  pari_sp av;
  GEN y;

  if (!*mask) return 0; /* useful when running in a loop */
  if (DEBUGLEVEL>4) err_printf("OddPwrs: examining %ld-bit integer\n", expi(x));
  if (lgefint(x) == 3) {
    ulong t;
    long e = uis_357_power(x[2], &t, mask);
    if (e)
    {
      if (pt) *pt = utoi(t);
      return e;
    }
    return 0;
  }
#ifdef LONG_IS_64BIT
  r = (lx == 3)? uel(x,2): umodiu(x, 6046846918939827UL);
  if (!uis_357_powermod(r, mask)) return 0;
#else
  r = (lx == 3)? uel(x,2): umodiu(x, 211*209*61*203);
  if (!uis_357_powermod_32bit_1(r, mask)) return 0;
  r = (lx == 3)? uel(x,2): umodiu(x, 117*31*43*71);
  if (!uis_357_powermod_32bit_2(r, mask)) return 0;
#endif
  av = avma;
  while (*mask)
  {
    long e, b;
    /* priority to higher powers: if we have a 21st, it is easier to rediscover
     * that its 7th root is a cube than that its cube root is a 7th power */
         if (*mask & 4) { b = 4; e = 7; }
    else if (*mask & 2) { b = 2; e = 5; }
    else                { b = 1; e = 3; }
    y = mpround( sqrtnr(itor(x, nbits2prec(64 + bit_accuracy(lx) / e)), e) );
    if (equalii(powiu(y,e), x))
    {
      if (!pt) { avma = av; return e; }
      avma = (pari_sp)y; *pt = gerepileuptoint(av, y);
      return e;
    }
    *mask &= ~b; /* turn the bit off */
    avma = av;
  }
  return 0;
}

/* Is x a n-th power ?
 * if d = NULL, n not necessarily prime, otherwise, n prime and d the
 * corresponding diffptr to go on looping over primes.
 * If pt != NULL, it receives the n-th root */
ulong
is_kth_power(GEN x, ulong n, GEN *pt)
{
  forprime_t T;
  long j;
  ulong q, residue;
  GEN y;
  pari_sp av = avma;

  (void)u_forprime_arith_init(&T, odd(n)? 2*n+1: n+1, ULONG_MAX, 1,n);
  /* we'll start at q, smallest prime >= n */

  /* Modular checks, use small primes q congruent 1 mod n */
  /* A non n-th power nevertheless passes the test with proba n^(-#checks),
   * We'd like this < 1e-6 but let j = floor(log(1e-6) / log(n)) which
   * ensures much less. */
  if (n < 16)
    j = 5;
  else if (n < 32)
    j = 4;
  else if (n < 101)
    j = 3;
  else if (n < 1001)
    j = 2;
  else if (n < 17886697) /* smallest such that smallest suitable q is > 2^32 */
    j = 1;
  else
    j = 0;
  for (; j > 0; j--)
  {
    if (!(q = u_forprime_next(&T))) break;
    /* q a prime = 1 mod n */
    residue = umodiu(x, q);
    if (residue == 0)
    {
      if (Z_lval(x,q) % n) { avma = av; return 0; }
      continue;
    }
    /* n-th power mod q ? */
    if (Fl_powu(residue, (q-1)/n, q) != 1) { avma = av; return 0; }
  }
  avma = av;

  if (DEBUGLEVEL>4) err_printf("\nOddPwrs: [%lu] passed modular checks\n",n);
  /* go to the horse's mouth... */
  y = roundr( sqrtnr(itor(x, nbits2prec((expi(x)+16*n)/n)), n) );
  if (!equalii(powiu(y, n), x)) {
    if (DEBUGLEVEL>4) err_printf("\tBut it wasn't a pure power.\n");
    avma = av; return 0;
  }
  if (!pt) avma = av; else { avma = (pari_sp)y; *pt = gerepileuptoint(av, y); }
  return 1;
}

/* is x a p^i-th power, p >= 11 prime ? Similar to is_357_power(), but instead
 * of the mask, we keep the current test exponent around. Cut off when
 * log_2 x^(1/k) < cutoffbits since we would have found it by trial division.
 * Everything needed here (primitive roots etc.) is computed from scratch on
 * the fly; compared to the size of numbers under consideration, these
 * word-sized computations take negligible time.
 * Any cutoffbits > 0 is safe, but direct root extraction attempts are faster
 * when trial division has been used to discover very small bases. We become
 * competitive at cutoffbits ~ 10 */
int
is_pth_power(GEN x, GEN *pt, forprime_t *T, ulong cutoffbits)
{
  long cnt=0, size = expi(x) /* not +1 */;
  ulong p;
  pari_sp av = avma;
  while ((p = u_forprime_next(T)) && size/p >= cutoffbits) {
    long v = 1;
    if (DEBUGLEVEL>5 && cnt++==2000)
      { cnt=0; err_printf("%lu%% ", 100*p*cutoffbits/size); }
    while (is_kth_power(x, p, pt)) {
      v *= p; x = *pt;
      size = expi(x);
    }
    if (v > 1)
    {
      if (DEBUGLEVEL>5) err_printf("\nOddPwrs: is a %ld power\n",v);
      return v;
    }
  }
  if (DEBUGLEVEL>5) err_printf("\nOddPwrs: not a power\n",p);
  avma = av; return 0; /* give up */
}

/***********************************************************************/
/**                FACTORIZATION  (master iteration)                  **/
/**      Driver for the various methods of finding large factors      **/
/**      (after trial division has cast out the very small ones).     **/
/**                        GN1998Jun24--30                            **/
/***********************************************************************/

/* Direct use:
 *  ifac_start_hint(n,moebius,hint) registers with the iterative factorizer
 *  - an integer n (without prime factors  < tridiv_bound(n))
 *  - registers whether or not we should terminate early if we find a square
 *    factor,
 *  - a hint about which method(s) to use.
 *  This must always be called first. If input is not composite, oo loop.
 *  The routine decomposes n nontrivially into a product of two factors except
 *  in squarefreeness ('Moebius') mode.
 *
 *  ifac_start(n,moebius) same using default hint.
 *
 *  ifac_primary_factor()  returns a prime divisor (not necessarily the
 *    smallest) and the corresponding exponent.
 *
 * Encapsulated user interface: Many arithmetic functions have a 'contributor'
 * ifac_xxx, to be called on any large composite cofactor left over after trial
 * division by small primes: xxx is one of moebius, issquarefree, totient, etc.
 *
 * We never test whether the input number is prime or composite, since
 * presumably it will have come out of the small factors finder stage
 * (which doesn't really exist yet but which will test the left-over
 * cofactor for primality once it does). */

/* The data structure in which we preserve whatever we know about our number N
 * is kept on the PARI stack, and updated as needed.
 * This makes the machinery re-entrant, and avoids memory leaks when a lengthy
 * factorization is interrupted. We try to keep the whole affair connected,
 * and the parent object is always older than its children.  This may in
 * rare cases lead to some extra copying around, and knowing what is garbage
 * at any given time is not trivial. See below for examples how to do it right.
 * (Connectedness is destroyed if callers of ifac_main() create stuff on the
 * stack in between calls. This is harmless as long as ifac_realloc() is used
 * to re-create a connected object at the head of the stack just before
 * collecting garbage.)
 * A t_INT may well have > 10^6 distinct prime factors larger than 2^16. Since
 * we need not find factors in order of increasing size, we must be prepared to
 * drag a very large amount of data around.  We start with a small structure
 * and extend it when necessary. */

/* The idea of the algorithm is:
 * Let N0 be whatever is currently left of N after dividing off all the
 * prime powers we have already returned to the caller.  Then we maintain
 * N0 as a product
 * (1) N0 = \prod_i P_i^{e_i} * \prod_j Q_j^{f_j} * \prod_k C_k^{g_k}
 * where the P_i and Q_j are distinct primes, each C_k is known composite,
 * none of the P_i divides any C_k, and we also know the total ordering
 * of all the P_i, Q_j and C_k; in particular, we will never try to divide
 * a C_k by a larger Q_j.  Some of the C_k may have common factors.
 *
 * Caveat implementor:  Taking gcds among C_k's is very likely to cost at
 * least as much time as dividing off any primes as we find them, and book-
 * keeping would be tough (since D=gcd(C_1,C_2) can still have common factors
 * with both C_1/D and C_2/D, and so on...).
 *
 * At startup, we just initialize the structure to
 * (2) N = C_1^1   (composite).
 *
 * Whenever ifac_primary_factor() or one of the arithmetic user interface
 * routines needs a primary factor, and the smallest thing in our list is P_1,
 * we return that and its exponent, and remove it from our list. (When nothing
 * is left, we return a sentinel value -- gen_1.  And in Moebius mode, when we
 * see something with exponent > 1, whether prime or composite, we return gen_0
 * or 0, depending on the function). In all other cases, ifac_main() iterates
 * the following steps until we have a P_1 in the smallest position.
 *
 * When the smallest item is C_1, as it is initially:
 * (3.1) Crack C_1 into a nontrivial product  U_1 * U_2  by whatever method
 * comes to mind for this size. (U for 'unknown'.)  Cracking will detect
 * perfect powers, so we may instead see a power of some U_1 here, or even
 * something of the form U_1^k*U_2^k; of course the exponent already attached
 * to C_1 is taken into account in the following.
 * (3.2) If we have U_1*U_2, sort the two factors (distinct: squares are caught
 * in stage 3.1). N.B. U_1 and U_2 are smaller than anything else in our list.
 * (3.3) Check U_1 and U_2 for primality, and flag them accordingly.
 * (3.4) Iterate.
 *
 * When the smallest item is Q_1:
 * This is the unpleasant case.  We go through the entire list and try to
 * divide Q_1 off each of the current C_k's, which usually fails, but may
 * succeed several times. When a division was successful, the corresponding
 * C_k is removed from our list, and the cofactor becomes a U_l for the moment
 * unless it is 1 (which happens when C_k was a power of Q_1).  When we're
 * through we upgrade Q_1 to P_1 status, then do a primality check on each U_l
 * and sort it back into the list either as a Q_j or as a C_k.  If during the
 * insertion sort we discover that some U_l equals some P_i or Q_j or C_k we
 * already have, we just add U_l's exponent to that of its twin. (The sorting
 * therefore happens before the primality test). Since this may produce one or
 * more elements smaller than the P_1 we just confirmed, we may have to repeat
 * the iteration.
 * A trick avoids some Q_1 instances: just after the sweep classifying
 * all current unknowns as either composites or primes, we do another downward
 * sweep beginning with the largest current factor and stopping just above the
 * largest current composite.  Every Q_j we pass is turned into a P_i.
 * (Different primes are automatically coprime among each other, and primes do
 * not divide smaller composites.)
 * NB: We have no use for comparing the square of a prime to N0.  Normally
 * we will get called after casting out only the smallest primes, and
 * since we cannot guarantee that we see the large prime factors in as-
 * cending order, we cannot stop when we find one larger than sqrt(N0). */

/* Data structure: We keep everything in a single t_VEC of t_INTs.  The
 * first 2 components are read-only:
 * 1) the first records whether we're doing full (NULL) or Moebius (gen_1)
 * factorization; in the latter case subroutines return a sentinel value as
 * soon as they spot an exponent > 1.
 * 2) the second records the hint from factorint()'s optional flag, for use by
 * ifac_crack().
 *
 * The remaining components (initially 15) are used in groups of three:
 * [ factor (t_INT), exponent (t_INT), factor class ], where factor class is
 *  NULL : unknown
 *  gen_0: known composite C_k
 *  gen_1: known prime Q_j awaiting trial division
 *  gen_2: finished prime P_i.
 * When during the division stage we re-sort a C_k-turned-U_l to a lower
 * position, we rotate any intervening material upward towards its old
 * slot.  When a C_k was divided down to 1, its slot is left empty at
 * first; similarly when the re-sorting detects a repeated factor.
 * After the sorting phase, we de-fragment the list and squeeze all the
 * occupied slots together to the high end, so that ifac_crack() has room
 * for new factors.  When this doesn't suffice, we abandon the current vector
 * and allocate a somewhat larger one, defragmenting again while copying.
 *
 * For internal use: note that all exponents will fit into C longs, given
 * PARI's lgefint field size.  When we work with them, we sometimes read
 * out the GEN pointer, and sometimes do an itos, whatever is more con-
 * venient for the task at hand. */

/*** Overview ***/

/* The '*where' argument in the following points into *partial at the first of
 * the three fields of the first occupied slot.  It's there because the caller
 * would already know where 'here' is, so we don't want to search for it again.
 * We do not preserve this from one user-interface call to the next. */

/* In the most common cases, control flows from the user interface to
 * ifac_main() and then to a succession of ifac_crack()s and ifac_divide()s,
 * with (typically) none of the latter finding anything. */

static long ifac_insert_multiplet(GEN *, GEN *, GEN, long);

#define LAST(x) x+lg(x)-3
#define FIRST(x) x+3

#define MOEBIUS(x) gel(x,1)
#define HINT(x) gel(x,2)

/* y <- x */
INLINE void
SHALLOWCOPY(GEN x, GEN y) {
  VALUE(y) = VALUE(x);
  EXPON(y) = EXPON(x);
  CLASS(y) = CLASS(x);
}
/* y <- x */
INLINE void
COPY(GEN x, GEN y) {
  icopyifstack(VALUE(x), VALUE(y));
  icopyifstack(EXPON(x), EXPON(y));
  CLASS(y) = CLASS(x);
}

/* Diagnostics */
static void
ifac_factor_dbg(GEN x)
{
  GEN c = CLASS(x), v = VALUE(x);
  if (c == gen_2) err_printf("IFAC: factor %Ps\n\tis prime (finished)\n", v);
  else if (c == gen_1) err_printf("IFAC: factor %Ps\n\tis prime\n", v);
  else if (c == gen_0) err_printf("IFAC: factor %Ps\n\tis composite\n", v);
}
static void
ifac_check(GEN partial, GEN where)
{
  if (!where || where < FIRST(partial) || where > LAST(partial))
    pari_err_BUG("ifac_check ['where' out of bounds]");
}
static void
ifac_print(GEN part, GEN where)
{
  long l = lg(part);
  GEN p;

  err_printf("ifac partial factorization structure: %ld slots, ", (l-3)/3);
  if (MOEBIUS(part)) err_printf("Moebius mode, ");
  err_printf("hint = %ld\n", itos(HINT(part)));
  ifac_check(part, where);
  for (p = part+3; p < part + l; p += 3)
  {
    GEN v = VALUE(p), e = EXPON(p), c = CLASS(p);
    const char *s = "";
    if (!v) { err_printf("[empty slot]\n"); continue; }
    if (c == NULL) s = "unknown";
    else if (c == gen_0) s = "composite";
    else if (c == gen_1) s = "unfinished prime";
    else if (c == gen_2) s = "prime";
    else pari_err_BUG("unknown factor class");
    err_printf("[%Ps, %Ps, %s]\n", v, e, s);
  }
  err_printf("Done.\n");
}

static const long decomp_default_hint = 0;
/* assume n > 0, which we can assign to */
/* return initial data structure, see ifac_crack() for the hint argument */
static GEN
ifac_start_hint(GEN n, int moebius, long hint)
{
  const long ifac_initial_length = 3 + 7*3;
  /* codeword, moebius, hint, 7 slots -- a 512-bit product of distinct 8-bit
   * primes needs at most 7 slots at a time) */
  GEN here, part = cgetg(ifac_initial_length, t_VEC);

  MOEBIUS(part) = moebius? gen_1 : NULL;
  HINT(part) = stoi(hint);
  if (isonstack(n)) n = absi(n);
  /* make copy, because we'll later want to replace it in place.
   * If it's not on stack, then we assume it is a clone made for us by
   * ifactor, and we assume the sign has already been set positive */
  /* fill first slot at the top end */
  here = part + ifac_initial_length - 3; /* LAST(part) */
  INIT(here, n,gen_1,gen_0); /* n^1: composite */
  while ((here -= 3) > part) ifac_delete(here);
  return part;
}
GEN
ifac_start(GEN n, int moebius)
{ return ifac_start_hint(n,moebius,decomp_default_hint); }

/* Return next nonempty slot after 'here', NULL if none exist */
static GEN
ifac_find(GEN partial)
{
  GEN scan, end = partial + lg(partial);

#ifdef IFAC_DEBUG
  ifac_check(partial, partial);
#endif
  for (scan = partial+3; scan < end; scan += 3)
    if (VALUE(scan)) return scan;
  return NULL;
}

/* Defragment: squeeze out unoccupied slots above *where. Unoccupied slots
 * arise when a composite factor dissolves completely whilst dividing off a
 * prime, or when ifac_resort() spots a coincidence and merges two factors.
 * Update *where */
static void
ifac_defrag(GEN *partial, GEN *where)
{
  GEN scan_new = LAST(*partial), scan_old;

  for (scan_old = scan_new; scan_old >= *where; scan_old -= 3)
  {
    if (!VALUE(scan_old)) continue; /* empty slot */
    if (scan_old < scan_new) SHALLOWCOPY(scan_old, scan_new);
    scan_new -= 3; /* point at next slot to be written */
  }
  scan_new += 3; /* back up to last slot written */
  *where = scan_new;
  while ((scan_new -= 3) > *partial) ifac_delete(scan_new); /* erase junk */
}

/* Move to a larger main vector, updating *where if it points into it, and
 * *partial in any case. Can be used as a specialized gcopy before
 * a gerepileupto() (pass 0 as the new length). Normally, one would pass
 * new_lg=1 to let this function guess the new size.  To be used sparingly.
 * Complex version of ifac_defrag(), combined with reallocation.  If new_lg
 * is 0, use the old length, so this acts just like gcopy except that the
 * 'where' pointer is carried along; if it is 1, we make an educated guess.
 * Exception:  If new_lg is 0, the vector is full to the brim, and the first
 * entry is composite, we make it longer to avoid being called again a
 * microsecond later. It is safe to call this with *where = NULL:
 * if it doesn't point anywhere within the old structure, it is left alone */
static void
ifac_realloc(GEN *partial, GEN *where, long new_lg)
{
  long old_lg = lg(*partial);
  GEN newpart, scan_new, scan_old;

  if (new_lg == 1)
    new_lg = 2*old_lg - 6;        /* from 7 slots to 13 to 25... */
  else if (new_lg <= old_lg)        /* includes case new_lg == 0 */
  {
    GEN first = *partial + 3;
    new_lg = old_lg;
    /* structure full and first entry composite or unknown */
    if (VALUE(first) && (CLASS(first) == gen_0 || CLASS(first)==NULL))
      new_lg += 6; /* give it a little more breathing space */
  }
  newpart = cgetg(new_lg, t_VEC);
  if (DEBUGMEM >= 3)
    err_printf("IFAC: new partial factorization structure (%ld slots)\n",
               (new_lg - 3)/3);
  MOEBIUS(newpart) = MOEBIUS(*partial);
  icopyifstack(HINT(*partial), HINT(newpart));
  /* Downward sweep through the old *partial. Pick up 'where' and carry it
   * over if we pass it. (Only useful if it pointed at a non-empty slot.)
   * Factors are COPY'd so that we again have a nice object (parent older
   * than children, connected), except the one factor that may still be living
   * in a clone where n originally was; exponents are similarly copied if they
   * aren't global constants; class-of-factor fields are global constants so we
   * need only copy them as pointers. Caller may then do a gerepileupto() */
  scan_new = newpart + new_lg - 3; /* LAST(newpart) */
  scan_old = *partial + old_lg - 3; /* LAST(*partial) */
  for (; scan_old > *partial + 2; scan_old -= 3)
  {
    if (*where == scan_old) *where = scan_new;
    if (!VALUE(scan_old)) continue; /* skip empty slots */
    COPY(scan_old, scan_new); scan_new -= 3;
  }
  scan_new += 3; /* back up to last slot written */
  while ((scan_new -= 3) > newpart) ifac_delete(scan_new);
  *partial = newpart;
}

/* Re-sort one (typically unknown) entry from washere to a new position,
 * rotating intervening entries upward to fill the vacant space. If the new
 * position is the same as the old one, or the new value of the entry coincides
 * with a value already occupying a lower slot, then we just add exponents (and
 * use the 'more known' class, and return 1 immediately when in Moebius mode).
 * Slots between *where and washere must be in sorted order, so a sweep using
 * this to re-sort several unknowns must proceed upward, see ifac_resort().
 * Bubble-sort-of-thing sort. Won't be exercised frequently, so this is ok */
static void
ifac_sort_one(GEN *where, GEN washere)
{
  GEN old, scan = washere - 3;
  GEN value, exponent, class0, class1;
  long cmp_res;

  if (scan < *where) return; /* nothing to do, washere==*where */
  value    = VALUE(washere);
  exponent = EXPON(washere);
  class0 = CLASS(washere);
  cmp_res = -1; /* sentinel */
  while (scan >= *where) /* at least once */
  {
    if (VALUE(scan))
    { /* current slot nonempty, check against where */
      cmp_res = cmpii(value, VALUE(scan));
      if (cmp_res >= 0) break; /* have found where to stop */
    }
    /* copy current slot upward by one position and move pointers down */
    SHALLOWCOPY(scan, scan+3);
    scan -= 3;
  }
  scan += 3;
  /* At this point there are the following possibilities:
   * 1) cmp_res == -1. Either value is less than that at *where, or *where was
   * pointing at vacant slots and any factors we saw en route were larger than
   * value. At any rate, scan == *where now, and scan is pointing at an empty
   * slot, into which we'll stash our entry.
   * 2) cmp_res == 0. The entry at scan-3 is the one, we compare class0
   * fields and add exponents, and put it all into the vacated scan slot,
   * NULLing the one at scan-3 (and possibly updating *where).
   * 3) cmp_res == 1. The slot at scan is the one to store our entry into. */
  if (cmp_res)
  {
    if (cmp_res < 0 && scan != *where)
      pari_err_BUG("ifact_sort_one [misaligned partial]");
    INIT(scan, value, exponent, class0); return;
  }
  /* case cmp_res == 0: repeated factor detected */
  if (DEBUGLEVEL >= 4)
    err_printf("IFAC: repeated factor %Ps\n\tin ifac_sort_one\n", value);
  old = scan - 3;
  /* if old class0 was composite and new is prime, or vice versa, complain
   * (and if one class0 was unknown and the other wasn't, use the known one) */
  class1 = CLASS(old);
  if (class0) /* should never be used */
  {
    if (class1)
    {
      if (class0 == gen_0 && class1 != gen_0)
        pari_err_BUG("ifac_sort_one (composite = prime)");
      else if (class0 != gen_0 && class1 == gen_0)
        pari_err_BUG("ifac_sort_one (prime = composite)");
      else if (class0 == gen_2)
        CLASS(scan) = class0;
    }
    else
      CLASS(scan) = class0;
  }
  /* else stay with the existing known class0 */
  CLASS(scan) = class1;
  /* in any case, add exponents */
  if (EXPON(old) == gen_1 && exponent == gen_1)
    EXPON(scan) = gen_2;
  else
    EXPON(scan) = addii(EXPON(old), exponent);
  /* move the value over and null out the vacated slot below */
  old = scan - 3;
  *scan = *old;
  ifac_delete(old);
  /* finally, see whether *where should be pulled in */
  if (old == *where) *where += 3;
}

/* Sort all current unknowns downward to where they belong. Sweeps in the
 * upward direction. Not needed after ifac_crack(), only when ifac_divide()
 * returned true. Update *where. */
static void
ifac_resort(GEN *partial, GEN *where)
{
  GEN scan, end;
  ifac_defrag(partial, where); end = LAST(*partial);
  for (scan = *where; scan <= end; scan += 3)
    if (VALUE(scan) && !CLASS(scan)) ifac_sort_one(where, scan); /*unknown*/
  ifac_defrag(partial, where); /* remove newly created gaps */
}

/* Let x be a t_INT known not to have small divisors (< 2^14). Return 0 if x
 * is a proven composite. Return 1 if we believe it to be prime (fully proven
 * prime if factor_proven is set).  */
int
ifac_isprime(GEN x)
{
  if (!BPSW_psp_nosmalldiv(x)) return 0; /* composite */
  if (factor_proven && ! BPSW_isprime(x))
  {
    pari_warn(warner,
              "IFAC: pseudo-prime %Ps\n\tis not prime. PLEASE REPORT!\n", x);
    return 0;
  }
  return 1;
}

static int
ifac_checkprime(GEN x)
{
  int res = ifac_isprime(VALUE(x));
  CLASS(x) = res? gen_1: gen_0;
  if (DEBUGLEVEL>2) ifac_factor_dbg(x);
  return res;
}

/* Determine primality or compositeness of all current unknowns, and set
 * class Q primes to finished (class P) if everything larger is already
 * known to be prime.  When after_crack >= 0, only look at the
 * first after_crack things in the list (do nothing when it's 0) */
static void
ifac_whoiswho(GEN *partial, GEN *where, long after_crack)
{
  GEN scan, scan_end = LAST(*partial);

#ifdef IFAC_DEBUG
  ifac_check(*partial, *where);
#endif
  if (after_crack == 0) return;
  if (after_crack > 0) /* check at most after_crack entries */
    scan = *where + 3*(after_crack - 1); /* assert(scan <= scan_end) */
  else
    for (scan = scan_end; scan >= *where; scan -= 3)
    {
      if (CLASS(scan))
      { /* known class of factor */
        if (CLASS(scan) == gen_0) break;
        if (CLASS(scan) == gen_1)
        {
          if (DEBUGLEVEL>=3)
          {
            err_printf("IFAC: factor %Ps\n\tis prime (no larger composite)\n",
                       VALUE(*where));
            err_printf("IFAC: prime %Ps\n\tappears with exponent = %ld\n",
                       VALUE(*where), itos(EXPON(*where)));
          }
          CLASS(scan) = gen_2;
        }
        continue;
      }
      if (!ifac_checkprime(scan)) break; /* must disable Q-to-P */
      CLASS(scan) = gen_2; /* P_i, finished prime */
      if (DEBUGLEVEL>2) ifac_factor_dbg(scan);
    }
  /* go on, Q-to-P trick now disabled */
  for (; scan >= *where; scan -= 3)
  {
    if (CLASS(scan)) continue;
    (void)ifac_checkprime(scan); /* Qj | Ck */
  }
}

/* Divide all current composites by first (prime, class Q) entry, updating its
 * exponent, and turning it into a finished prime (class P).  Return 1 if any
 * such divisions succeeded  (in Moebius mode, the update may then not have
 * been completed), or 0 if none of them succeeded.  Doesn't modify *where.
 * Here we normally do not check that the first entry is a not-finished
 * prime.  Stack management: we may allocate a new exponent */
static long
ifac_divide(GEN *partial, GEN *where, long moebius_mode)
{
  GEN scan, scan_end = LAST(*partial);
  long res = 0, exponent, newexp, otherexp;

#ifdef IFAC_DEBUG
  ifac_check(*partial, *where);
  if (CLASS(*where) != gen_1)
    pari_err_BUG("ifac_divide [division by composite or finished prime]");
  if (!VALUE(*where)) pari_err_BUG("ifac_divide [division by nothing]");
#endif
  newexp = exponent = itos(EXPON(*where));
  if (exponent > 1 && moebius_mode) return 1;
  /* should've been caught by caller */

  for (scan = *where+3; scan <= scan_end; scan += 3)
  {
    if (CLASS(scan) != gen_0) continue; /* the other thing ain't composite */
    otherexp = 0;
    /* divide in place to keep stack clutter minimal */
    while (dvdiiz(VALUE(scan), VALUE(*where), VALUE(scan)))
    {
      if (moebius_mode) return 1; /* immediately */
      if (!otherexp) otherexp = itos(EXPON(scan));
      newexp += otherexp;
    }
    if (newexp > exponent)        /* did anything happen? */
    {
      EXPON(*where) = (newexp == 2 ? gen_2 : utoipos(newexp));
      exponent = newexp;
      if (is_pm1((GEN)*scan)) /* factor dissolved completely */
      {
        ifac_delete(scan);
        if (DEBUGLEVEL >= 4)
          err_printf("IFAC: a factor was a power of another prime factor\n");
      } else {
        CLASS(scan) = NULL;        /* at any rate it's Unknown now */
        if (DEBUGLEVEL >= 4)
          err_printf("IFAC: a factor was divisible by another prime factor,\n"
                     "\tleaving a cofactor = %Ps\n", VALUE(scan));
      }
      res = 1;
      if (DEBUGLEVEL >= 5)
        err_printf("IFAC: prime %Ps\n\tappears at least to the power %ld\n",
                   VALUE(*where), newexp);
    }
  } /* for */
  CLASS(*where) = gen_2; /* make it a finished prime */
  if (DEBUGLEVEL >= 3)
    err_printf("IFAC: prime %Ps\n\tappears with exponent = %ld\n",
               VALUE(*where), newexp);
  return res;
}

/* found out our integer was factor^exp. Update */
static void
update_pow(GEN where, GEN factor, long exp, pari_sp *av)
{
  GEN ex = EXPON(where);
  if (DEBUGLEVEL>3)
    err_printf("IFAC: found %Ps =\n\t%Ps ^%ld\n", *where, factor, exp);
  affii(factor, VALUE(where)); avma = *av;
  if (ex == gen_1)
  { EXPON(where) = exp == 2? gen_2: utoipos(exp); *av = avma; }
  else if (ex == gen_2)
  { EXPON(where) = utoipos(exp<<1); *av = avma; }
  else
    affsi(exp * itos(ex), EXPON(where));
}
/* hint = 0 : Use a default strategy
 * hint & 1 : avoid MPQS
 * hint & 2 : avoid first-stage ECM (may fall back to ECM if MPQS gives up)
 * hint & 4 : avoid Pollard and SQUFOF stages.
 * hint & 8 : avoid final ECM; may flag a composite as prime. */
#define get_hint(partial) (itos(HINT(*partial)) & 15)

/* Split the first (composite) entry.  There _must_ already be room for another
 * factor below *where, and *where is updated. Two cases:
 * - entry = factor^k is a pure power: factor^k is inserted, leaving *where
 *   unchanged;
 * - entry = factor * cofactor (not necessarily coprime): both factors are
 *   inserted in the correct order, updating *where
 * The inserted factors class is set to unknown, they inherit the exponent
 * (or a multiple thereof) of their ancestor.
 *
 * Returns number of factors written into the structure, normally 2 (1 if pure
 * power, maybe > 2 if a factoring engine returned a vector of factors instead
 * of a single factor). Can reallocate the data structure in the
 * vector-of-factors case, not in the most common single-factor case.
 * Stack housekeeping:  this routine may create one or more objects  (a new
 * factor, or possibly several, and perhaps one or more new exponents > 2) */
static long
ifac_crack(GEN *partial, GEN *where, long moebius_mode)
{
  long cmp_res, hint = get_hint(partial);
  GEN factor, exponent;

#ifdef IFAC_DEBUG
  ifac_check(*partial, *where);
  if (*where < *partial + 6)
    pari_err_BUG("ifac_crack ['*where' out of bounds]");
  if (!(VALUE(*where)) || typ(VALUE(*where)) != t_INT)
    pari_err_BUG("ifac_crack [incorrect VALUE(*where)]");
  if (CLASS(*where) != gen_0)
    pari_err_BUG("ifac_crack [operand not known composite]");
#endif

  if (DEBUGLEVEL>2) {
    err_printf("IFAC: cracking composite\n\t%Ps\n", **where);
    if (DEBUGLEVEL>3) err_printf("IFAC: checking for pure square\n");
  }
  /* MPQS cannot factor prime powers. Look for pure powers even if MPQS is
   * blocked by hint: fast and useful in bounded factorization */
  {
    forprime_t T;
    ulong exp = 1, mask = 7;
    long good = 0;
    pari_sp av = avma;
    (void)u_forprime_init(&T, 11, ULONG_MAX);
    /* crack squares */
    while (Z_issquareall(VALUE(*where), &factor))
    {
      good = 1; /* remember we succeeded once */
      update_pow(*where, factor, 2, &av);
      if (moebius_mode) return 0; /* no need to carry on */
    }
    while ( (exp = is_357_power(VALUE(*where), &factor, &mask)) )
    {
      good = 1; /* remember we succeeded once */
      update_pow(*where, factor, exp, &av);
      if (moebius_mode) return 0; /* no need to carry on */
    }
    /* cutoff at 14 bits as trial division must have found everything below */
    while ( (exp = is_pth_power(VALUE(*where), &factor, &T, 15)) )
    {
      good = 1; /* remember we succeeded once */
      update_pow(*where, factor, exp, &av);
      if (moebius_mode) return 0; /* no need to carry on */
    }

    if (good && hint != 15 && ifac_checkprime(*where))
    { /* our composite was a prime power */
      if (DEBUGLEVEL>3)
        err_printf("IFAC: factor %Ps\n\tis prime\n", VALUE(*where));
      return 0; /* bypass subsequent ifac_whoiswho() call */
    }
  } /* pure power stage */

  factor = NULL;
  if (!(hint & 4))
  { /* pollardbrent() Rho usually gets a first chance */
    if (DEBUGLEVEL >= 4) err_printf("IFAC: trying Pollard-Brent rho method\n");
    factor = pollardbrent(VALUE(*where));
    if (!factor)
    { /* Shanks' squfof() */
      if (DEBUGLEVEL >= 4)
        err_printf("IFAC: trying Shanks' SQUFOF, will fail silently if input\n"
                   "      is too large for it.\n");
      factor = squfof(VALUE(*where));
    }
  }
  if (!factor && !(hint & 2))
  { /* First ECM stage */
    if (DEBUGLEVEL >= 4) err_printf("IFAC: trying Lenstra-Montgomery ECM\n");
    factor = ellfacteur(VALUE(*where), 0); /* do not insist */
  }
  if (!factor && !(hint & 1))
  { /* MPQS stage */
    if (DEBUGLEVEL >= 4) err_printf("IFAC: trying MPQS\n");
    factor = mpqs(VALUE(*where));
  }
  if (!factor)
  {
    if (!(hint & 8))
    { /* still no luck? Final ECM stage, guaranteed to succeed */
      if (DEBUGLEVEL >= 4)
        err_printf("IFAC: forcing ECM, may take some time\n");
      factor = ellfacteur(VALUE(*where), 1);
    }
    else
    { /* limited factorization */
      if (DEBUGLEVEL >= 2)
      {
        if (hint != 15)
          pari_warn(warner, "IFAC: unfactored composite declared prime");
        else
          pari_warn(warner, "IFAC: untested integer declared prime");

        /* don't print it out at level 3 or above, where it would appear
         * several times before and after this message already */
        if (DEBUGLEVEL == 2) err_printf("\t%Ps\n", VALUE(*where));
      }
      CLASS(*where) = gen_1; /* might as well trial-divide by it... */
      return 1;
    }
  }
  if (typ(factor) == t_VEC) /* delegate this case */
    return ifac_insert_multiplet(partial, where, factor, moebius_mode);
  /* typ(factor) == t_INT */
  /* got single integer back:  work out the cofactor (in place) */
  if (!dvdiiz(VALUE(*where), factor, VALUE(*where)))
  {
    err_printf("IFAC: factoring %Ps\n", VALUE(*where));
    err_printf("\tyielded 'factor' %Ps\n\twhich isn't!\n", factor);
    pari_err_BUG("factoring");
  }
  /* factoring engines report the factor found; tell about the cofactor */
  if (DEBUGLEVEL >= 4) err_printf("IFAC: cofactor = %Ps\n", VALUE(*where));

  /* The two factors are 'factor' and VALUE(*where), find out which is larger */
  cmp_res = cmpii(factor, VALUE(*where));
  CLASS(*where) = NULL; /* mark factor /cofactor 'unknown' */
  exponent = EXPON(*where);
  *where -= 3;
  CLASS(*where) = NULL; /* mark factor /cofactor 'unknown' */
  EXPON(*where) = isonstack(exponent)? icopy(exponent): exponent;
  if (cmp_res < 0)
    VALUE(*where) = factor; /* common case */
  else if (cmp_res > 0)
  { /* factor > cofactor, rearrange */
    GEN old = *where + 3;
    VALUE(*where) = VALUE(old); /* move cofactor pointer to lowest slot */
    VALUE(old) = factor; /* save factor */
  }
  else pari_err_BUG("ifac_crack [Z_issquareall miss]");
  return 2;
}

/* Gets called to complete ifac_crack's job when a factoring engine splits
 * the current factor into a product of three or more new factors. Makes room
 * for them if necessary, sorts them, gives them the right exponents and class.
 * Also returns the number of factors actually written, which may be less than
 * the number of components in facvec if there are duplicates.--- Vectors of
 * factors  (cf pollardbrent()) actually contain 'slots' of three GENs per
 * factor with the three fields interpreted as in our partial factorization
 * data structure.  Thus 'engines' can tell us what they already happen to
 * know about factors being prime or composite and/or appearing to a power
 * larger than the first.
 * Don't collect garbage.  No diagnostics: the factoring engine should have
 * printed what it found. facvec contains slots of three components per factor;
 * repeated factors are allowed  (and their classes shouldn't contradict each
 * other whereas their exponents will be added up) */
static long
ifac_insert_multiplet(GEN *partial, GEN *where, GEN facvec, long moebius_mode)
{
  long j,k=1, lfv=lg(facvec)-1, nf=lfv/3, room=(long)(*where-*partial);
  /* one of the factors will go into the *where slot, so room is now 3 times
   * the number of slots we can use */
  long needroom = lfv - room;
  GEN e, newexp, cur, sorted, auxvec = cgetg(nf+1, t_VEC), factor;
  long exponent = itos(EXPON(*where)); /* the old exponent */

  if (DEBUGLEVEL >= 5) /* squfof may return a single squared factor as a set */
    err_printf("IFAC: incorporating set of %ld factor(s)\n", nf);
  if (needroom > 0) /* one extra slot for paranoia, errm, future use */
    ifac_realloc(partial, where, lg(*partial) + needroom + 3);

  /* create sort permutation from the values of the factors */
  for (j=nf; j; j--) auxvec[j] = facvec[3*j-2]; /* just the pointers */
  sorted = indexsort(auxvec);
  /* and readjust the result for the triple spacing */
  for (j=nf; j; j--) sorted[j] = 3*sorted[j]-2;

  /* store factors, beginning at *where, and catching any duplicates */
  cur = facvec + sorted[nf];
  VALUE(*where) = VALUE(cur);
  newexp = EXPON(cur);
  if (newexp != gen_1) /* new exponent > 1 */
  {
    if (exponent == 1)
      e = isonstack(newexp)? icopy(newexp): newexp;
    else
      e = mului(exponent, newexp);
    EXPON(*where) = e;
  } /* if new exponent is 1, the old exponent already in place will do */
  CLASS(*where) = CLASS(cur);
  if (DEBUGLEVEL >= 6) err_printf("\tstored (largest) factor no. %ld...\n", nf);

  for (j=nf-1; j; j--)
  {
    cur = facvec + sorted[j];
    factor = VALUE(cur);
    if (equalii(factor, VALUE(*where)))
    {
      if (DEBUGLEVEL >= 6)
        err_printf("\tfactor no. %ld is a duplicate%s\n", j, (j>1? "...": ""));
      /* update exponent, ignore class which would already have been set,
       * then forget current factor */
      newexp = EXPON(cur);
      if (newexp != gen_1) /* new exp > 1 */
        e = addis(EXPON(*where), exponent * itos(newexp));
      else if (EXPON(*where) == gen_1 && exponent == 1)
        e = gen_2;
      else
        e = addis(EXPON(*where), exponent);
      EXPON(*where) = e;

      if (moebius_mode) return 0; /* stop now, but with exponent updated */
      continue;
    }

    *where -= 3;
    CLASS(*where) = CLASS(cur);        /* class as given */
    newexp = EXPON(cur);
    if (newexp != gen_1) /* new exp > 1 */
    {
      if (exponent == 1 && newexp == gen_2)
        e = gen_2;
      else /* exponent*newexp > 2 */
        e = mului(exponent, newexp);
    }
    else
      e = (exponent == 1 ? gen_1 :
            (exponent == 2 ? gen_2 :
               utoipos(exponent))); /* inherit parent's exponent */
    EXPON(*where) = e;
    /* keep components younger than *partial */
    VALUE(*where) = isonstack(factor) ? icopy(factor) : factor;
    k++;
    if (DEBUGLEVEL >= 6)
      err_printf("\tfactor no. %ld was unique%s\n", j, j>1? " (so far)...": "");
  }
  /* make the 'sorted' object safe for garbage collection (it should be in the
   * garbage zone from everybody's perspective, but it's easy to do it) */
  *sorted = evaltyp(t_INT) | evallg(nf+1);
  return k;
}

/* main loop:  iterate until smallest entry is a finished prime;  returns
 * a 'where' pointer, or NULL if nothing left, or gen_0 in Moebius mode if
 * we aren't squarefree */
static GEN
ifac_main(GEN *partial)
{
  const long moebius_mode = !!MOEBIUS(*partial);
  GEN here = ifac_find(*partial);
  long nf;

  if (!here) return NULL; /* nothing left */
  /* loop until first entry is a finished prime.  May involve reallocations,
   * thus updates of *partial */
  while (CLASS(here) != gen_2)
  {
    if (CLASS(here) == gen_0) /* composite: crack it */
    { /* make sure there's room for another factor */
      if (here < *partial + 6)
      {
        ifac_defrag(partial, &here);
        if (here < *partial + 6) ifac_realloc(partial, &here, 1); /* no luck */
      }
      nf = ifac_crack(partial, &here, moebius_mode);
      if (moebius_mode && EXPON(here) != gen_1) /* that was a power */
      {
        if (DEBUGLEVEL >= 3)
          err_printf("IFAC: main loop: repeated new factor\n\t%Ps\n", *here);
        return gen_0;
      }
      /* deal with the new unknowns.  No sort: ifac_crack did it */
      ifac_whoiswho(partial, &here, nf);
      continue;
    }
    if (CLASS(here) == gen_1) /* prime but not yet finished: finish it */
    {
      if (ifac_divide(partial, &here, moebius_mode))
      {
        if (moebius_mode)
        {
          if (DEBUGLEVEL >= 3)
            err_printf("IFAC: main loop: another factor was divisible by\n"
                       "\t%Ps\n", *here);
          return gen_0;
        }
        ifac_resort(partial, &here); /* sort new cofactors down */
        ifac_whoiswho(partial, &here, -1);
      }
      continue;
    }
    pari_err_BUG("ifac_main [non-existent factor class]");
  } /* while */
  if (moebius_mode && EXPON(here) != gen_1)
  {
    if (DEBUGLEVEL >= 3)
      err_printf("IFAC: after main loop: repeated old factor\n\t%Ps\n", *here);
    return gen_0;
  }
  if (DEBUGLEVEL >= 4)
  {
    nf = (*partial + lg(*partial) - here - 3)/3;
    if (nf)
      err_printf("IFAC: main loop: %ld factor%s left\n", nf, (nf>1)? "s": "");
    else
      err_printf("IFAC: main loop: this was the last factor\n");
  }
  if (factor_add_primes && !(get_hint(partial) & 8))
  {
    GEN p = VALUE(here);
    if (lgefint(p)>3 || uel(p,2) > 0x1000000UL) (void)addprimes(p);
  }
  return here;
}

/* Encapsulated routines */

/* prime/exponent pairs need to appear contiguously on the stack, but we also
 * need our data structure somewhere, and we don't know in advance how many
 * primes will turn up.  The following discipline achieves this:  When
 * ifac_decomp() is called, n should point at an object older than the oldest
 * small prime/exponent pair  (ifactor() guarantees this).
 * We allocate sufficient space to accommodate several pairs -- eleven pairs
 * ought to fit in a space not much larger than n itself -- before calling
 * ifac_start().  If we manage to complete the factorization before we run out
 * of space, we free the data structure and cull the excess reserved space
 * before returning.  When we do run out, we have to leapfrog to generate more
 * (guesstimating the requirements from what is left in the partial
 * factorization structure);  room for fresh pairs is allocated at the head of
 * the stack, followed by an ifac_realloc() to reconnect the data structure and
 * move it out of the way, followed by a few pointer tweaks to connect the new
 * pairs space to the old one. This whole affair translates into a surprisingly
 * compact routine. */

/* find primary factors of n; destroy n */
static long
ifac_decomp(GEN n, long hint)
{
  pari_sp av = avma;
  long nb = 0;
  GEN part, here, workspc, pairs = (GEN)av;

  /* workspc will be doled out in pairs of smaller t_INTs. For n = prod p^{e_p}
   * (p not necessarily prime), need room to store all p and e_p [ cgeti(3) ],
   * bounded by
   *    sum_{p | n} ( log_{2^BIL} (p) + 6 ) <= log_{2^BIL} n + 6 log_2 n */
  workspc = new_chunk((expi(n) + 1) * 7);
  part = ifac_start_hint(n, 0, hint);
  for (;;)
  {
    here = ifac_main(&part);
    if (!here) break;
    if (gc_needed(av,1))
    {
      long offset;
      if(DEBUGMEM>1)
      {
        pari_warn(warnmem,"[2] ifac_decomp");
        ifac_print(part, here);
      }
      ifac_realloc(&part, &here, 0);
      offset = here - part;
      part = gerepileupto((pari_sp)workspc, part);
      here = part + offset;
    }
    nb++;
    pairs = icopy_avma(VALUE(here), (pari_sp)pairs);
    pairs = icopy_avma(EXPON(here), (pari_sp)pairs);
    ifac_delete(here);
  }
  avma = (pari_sp)pairs;
  if (DEBUGLEVEL >= 3)
    err_printf("IFAC: found %ld large prime (power) factor%s.\n",
               nb, (nb>1? "s": ""));
  return nb;
}

/***********************************************************************/
/**            ARITHMETIC FUNCTIONS WITH EARLY-ABORT                  **/
/**  needing direct access to the factoring machinery to avoid work:  **/
/**  e.g. if we find a square factor, moebius returns 0, core doesn't **/
/**  need to factor it, etc.                                          **/
/***********************************************************************/
/* memory management */
static void
ifac_GC(pari_sp av, GEN *part)
{
  GEN here = NULL;
  if(DEBUGMEM>1) pari_warn(warnmem,"ifac_xxx");
  ifac_realloc(part, &here, 0);
  *part = gerepileupto(av, *part);
}

/* destroys n */
static long
ifac_moebius(GEN n)
{
  long mu = 1;
  pari_sp av = avma;
  GEN part = ifac_start(n, 1);
  for(;;)
  {
    long v;
    GEN p;
    if (!ifac_next(&part,&p,&v)) return v? 0: mu;
    mu = -mu;
    if (gc_needed(av,1)) ifac_GC(av,&part);
  }
}

int
ifac_read(GEN part, GEN *p, long *e)
{
  GEN here = ifac_find(part);
  if (!here) return 0;
  *p = VALUE(here);
  *e = EXPON(here)[2];
  return 1;
}
void
ifac_skip(GEN part)
{
  GEN here = ifac_find(part);
  if (here) ifac_delete(here);
}

/* destroys n */
static int
ifac_ispowerful(GEN n)
{
  pari_sp av = avma;
  GEN part = ifac_start(n, 0);
  for(;;)
  {
    long e;
    GEN p;
    if (!ifac_read(part,&p,&e)) return 1;
    /* power: skip */
    if (e != 1 || Z_isanypower(p,NULL)) { ifac_skip(part); continue; }
    if (!ifac_next(&part,&p,&e)) return 1;
    if (e == 1) return 0;
    if (gc_needed(av,1)) ifac_GC(av,&part);
  }
}
/* destroys n */
static GEN
ifac_core(GEN n)
{
  GEN m = gen_1, c = cgeti(lgefint(n));
  pari_sp av = avma;
  GEN part = ifac_start(n, 0);
  for(;;)
  {
    long e;
    GEN p;
    if (!ifac_read(part,&p,&e)) return m;
    /* square: skip */
    if (!odd(e) || Z_issquare(p)) { ifac_skip(part); continue; }
    if (!ifac_next(&part,&p,&e)) return m;
    if (odd(e)) m = mulii(m, p);
    if (gc_needed(av,1)) { affii(m,c); m=c; ifac_GC(av,&part); }
  }
}

/* Where to stop trial dividing in factorization. Guaranteed >= 2^14 */
ulong
tridiv_bound(GEN n)
{
  ulong l = (ulong)expi(n) + 1;
  if (l <= 32)  return 1UL<<14;
  if (l <= 512) return (l-16) << 10;
  return 1UL<<19; /* Rho is generally faster above this */
}

/* return a value <= (48 << 10) = 49152 < primelinit */
static ulong
utridiv_bound(ulong n)
{
#ifdef LONG_IS_64BIT
  if (n & HIGHMASK)
    return ((ulong)expu(n) + 1 - 16) << 10;
#else
  (void)n;
#endif
  return 1UL<<14;
}

/* destroys n */
static void
ifac_factoru(GEN n, long hint, GEN P, GEN E, long *pi)
{
  GEN part = ifac_start_hint(n, 0, hint);
  for(;;)
  {
    long v;
    GEN p;
    if (!ifac_next(&part,&p,&v)) return;
    P[*pi] = itou(p);
    E[*pi] = v;
    (*pi)++;
  }
}
/* destroys n */
static long
ifac_moebiusu(GEN n)
{
  GEN part = ifac_start(n, 1);
  long s = 1;
  for(;;)
  {
    long v;
    GEN p;
    if (!ifac_next(&part,&p,&v)) return v? 0: s;
    s = -s;
  }
}

INLINE ulong
u_forprime_next_fast(forprime_t *T)
{
  if (*(T->d))
  {
    NEXT_PRIME_VIADIFF(T->p, T->d);
    return T->p > T->b ? 0: T->p;
  }
  return u_forprime_next(T);
}

/* Factor n and output [p,e] where
 * p, e are vecsmall with n = prod{p[i]^e[i]} */
static GEN
factoru_sign(ulong n, ulong all, long hint)
{
  GEN f, E, E2, P, P2;
  pari_sp av;
  ulong p, lim;
  long i;
  forprime_t S;

  if (n == 0) retmkvec2(mkvecsmall(0), mkvecsmall(1));
  if (n == 1) retmkvec2(cgetg(1,t_VECSMALL), cgetg(1,t_VECSMALL));

  f = cgetg(3,t_VEC); av = avma;
  lim = all; if (!lim) lim = utridiv_bound(n);
  /* enough room to store <= 15 primes and exponents (OK if n < 2^64) */
  (void)new_chunk(16*2);
  P = cgetg(16, t_VECSMALL); i = 1;
  E = cgetg(16, t_VECSMALL);
  if (lim > 2)
  {
    long v = vals(n), oldi;
    if (v)
    {
      P[1] = 2; E[1] = v; i = 2;
      n >>= v; if (n == 1) goto END;
    }
    u_forprime_init(&S, 3, lim-1);
    oldi = i;
    while ( (p = u_forprime_next_fast(&S)) )
    {
      int stop;
      /* tiny integers without small factors are often primes */
      if (p == 673)
      {
        oldi = i;
        if (uisprime_661(n)) { P[i] = n; E[i] = 1; i++; goto END; }
      }
      v = u_lvalrem_stop(&n, p, &stop);
      if (v) {
        P[i] = p;
        E[i] = v; i++;
      }
      if (stop) {
        if (n != 1) { P[i] = n; E[i] = 1; i++; }
        goto END;
      }
    }
    if (oldi != i && uisprime_661(n)) { P[i] = n; E[i] = 1; i++; goto END; }
  }
  if (all)
  { /* smallfact: look for easy pure powers then stop */
#ifdef LONG_IS_64BIT
    ulong mask = all > 563 ? (all > 7129 ? 1: 3): 7;
#else
    ulong mask = all > 22 ? (all > 83 ? 1: 3): 7;
#endif
    long k = 1, ex;
    while (uissquareall(n, &n)) k <<= 1;
    while ( (ex = uis_357_power(n, &n, &mask)) ) k *= ex;
    P[i] = n; E[i] = k; i++; goto END;
  }
  {
    GEN perm;
    ifac_factoru(utoipos(n), hint, P, E, &i);
    setlg(P, i);
    perm = vecsmall_indexsort(P);
    P = vecsmallpermute(P, perm);
    E = vecsmallpermute(E, perm);
  }
END:
  avma = av;
  P2 = cgetg(i, t_VECSMALL); gel(f,1) = P2;
  E2 = cgetg(i, t_VECSMALL); gel(f,2) = E2;
  while (--i >= 1) { P2[i] = P[i]; E2[i] = E[i]; }
  return f;
}
GEN
factoru(ulong n)
{ return factoru_sign(n, 0, decomp_default_hint); }

long
moebiusu_fact(GEN f)
{
  GEN E = gel(f,2);
  long i, l = lg(E);
  for (i = 1; i < l; i++)
    if (E[i] > 1) return 0;
  return odd(l)? 1: -1;
}

long
moebiusu(ulong n)
{
  pari_sp av;
  ulong p;
  long s, v, test_prime;
  forprime_t S;

  switch(n)
  {
    case 0: (void)check_arith_non0(gen_0,"moebius");/*error*/
    case 1: return  1;
    case 2: return -1;
  }
  v = vals(n);
  if (v == 0)
    s = 1;
  else
  {
    if (v > 1) return 0;
    n >>= 1;
    s = -1;
  }
  av = avma;
  u_forprime_init(&S, 3, utridiv_bound(n));
  test_prime = 0;
  while ((p = u_forprime_next_fast(&S)))
  {
    int stop;
    /* tiny integers without small factors are often primes */
    if (p == 673)
    {
      test_prime = 0;
      if (uisprime_661(n)) { avma = av; return -s; }
    }
    v = u_lvalrem_stop(&n, p, &stop);
    if (v) {
      if (v > 1) { avma = av; return 0; }
      test_prime = 1;
      s = -s;
    }
    if (stop) { avma = av; return n == 1? s: -s; }
  }
  avma = av;
  if (test_prime && uisprime_661(n)) return -s;
  else
  {
    long t = ifac_moebiusu(utoipos(n));
    avma = av;
    if (t == 0) return 0;
    return (s == t)? 1: -1;
  }
}

long
moebius(GEN n)
{
  pari_sp av = avma;
  GEN F;
  ulong p;
  long i, l, s, v;
  forprime_t S;

  if ((F = check_arith_non0(n,"moebius")))
  {
    GEN E;
    F = clean_Z_factor(F);
    E = gel(F,2);
    l = lg(E);
    for(i = 1; i < l; i++)
      if (!equali1(gel(E,i))) { avma = av; return 0; }
    avma = av; return odd(l)? 1: -1;
  }
  if (lgefint(n) == 3) return moebiusu(uel(n,2));
  p = mod4(n); if (!p) return 0;
  if (p == 2) { s = -1; n = shifti(n, -1); } else { s = 1; n = icopy(n); }
  setabssign(n);

  u_forprime_init(&S, 3, tridiv_bound(n));
  while ((p = u_forprime_next_fast(&S)))
  {
    int stop;
    v = Z_lvalrem_stop(&n, p, &stop);
    if (v)
    {
      if (v > 1) { avma = av; return 0; }
      s = -s;
      if (stop) { avma = av; return is_pm1(n)? s: -s; }
    }
  }
  l = lg(primetab);
  for (i = 1; i < l; i++)
  {
    v = Z_pvalrem(n, gel(primetab,i), &n);
    if (v)
    {
      if (v > 1) { avma = av; return 0; }
      s = -s;
      if (is_pm1(n)) { avma = av; return s; }
    }
  }
  if (ifac_isprime(n)) { avma = av; return -s; }
  /* large composite without small factors */
  v = ifac_moebius(n);
  avma = av; return (s<0 ? -v : v); /* correct also if v==0 */
}

long
ispowerful(GEN n)
{
  pari_sp av = avma;
  GEN F;
  ulong p, bound;
  long i, l, v;
  forprime_t S;

  if ((F = check_arith_all(n, "ispowerful")))
  {
    GEN p, P = gel(F,1), E = gel(F,2);
    if (lg(P) == 1) return 1; /* 1 */
    p = gel(P,1);
    if (!signe(p)) return 1; /* 0 */
    i = is_pm1(p)? 2: 1; /* skip -1 */
    l = lg(E);
    for (; i < l; i++)
      if (equali1(gel(E,i))) return 0;
    return 1;
  }
  if (!signe(n)) return 1;

  if (mod4(n) == 2) return 0;
  n = shifti(n, -vali(n));
  if (is_pm1(n)) return 1;
  setabssign(n);
  bound = tridiv_bound(n);
  u_forprime_init(&S, 3, bound);
  while ((p = u_forprime_next_fast(&S)))
  {
    int stop;
    v = Z_lvalrem_stop(&n, p, &stop);
    if (v)
    {
      if (v == 1) { avma = av; return 0; }
      if (stop) { avma = av; return is_pm1(n); }
    }
  }
  l = lg(primetab);
  for (i = 1; i < l; i++)
  {
    v = Z_pvalrem(n, gel(primetab,i), &n);
    if (v)
    {
      if (v == 1) { avma = av; return 0; }
      if (is_pm1(n)) { avma = av; return 1; }
    }
  }
  /* no need to factor: must be p^2 or not powerful */
  if(cmpii(powuu(bound+1, 3), n) > 0) {
    long res = Z_issquare(n);
    avma = av; return res;
  }

  if (ifac_isprime(n)) { avma=av; return 0; }
  /* large composite without small factors */
  v = ifac_ispowerful(n);
  avma = av; return v;
}

ulong
coreu_fact(GEN f)
{
  GEN P = gel(f,1), E = gel(f,2);
  long i, l = lg(P), m = 1;
  for (i = 1; i < l; i++)
  {
    ulong p = P[i], e = E[i];
    if (e & 1) m *= p;
  }
  return m;
}
ulong
coreu(ulong n)
{
  if (n == 0) return 0;
  else
  {
    pari_sp av = avma;
    long m = coreu_fact(factoru(n));
    avma = av; return m;
  }
}
GEN
core(GEN n)
{
  pari_sp av = avma;
  GEN m, F;
  ulong p;
  long i, l, v;
  forprime_t S;

  if ((F = check_arith_all(n, "core")))
  {
    GEN p, x, P = gel(F,1), E = gel(F,2);
    long j = 1;
    if (lg(P) == 1) return gen_1;
    p = gel(P,1);
    if (!signe(p)) return gen_0;
    l = lg(P); x = cgetg(l, t_VEC);
    for (i = 1; i < l; i++)
      if (mpodd(gel(E,i))) gel(x,j++) = gel(P,i);
    setlg(x, j); return ZV_prod(x);
  }
  switch(lgefint(n))
  {
    case 2: return gen_0;
    case 3:
      p = coreu(uel(n,2));
      return signe(n) > 0? utoipos(p): utoineg(p);
  }

  m = signe(n) < 0? gen_m1: gen_1;
  n = absi_shallow(n);
  u_forprime_init(&S, 2, tridiv_bound(n));
  while ((p = u_forprime_next_fast(&S)))
  {
    int stop;
    v = Z_lvalrem_stop(&n, p, &stop);
    if (v)
    {
      if (v & 1) m = muliu(m, p);
      if (stop)
      {
        if (!is_pm1(n)) m = mulii(m, n);
        return gerepileuptoint(av, m);
      }
    }
  }
  l = lg(primetab);
  for (i = 1; i < l; i++)
  {
    GEN q = gel(primetab,i);
    v = Z_pvalrem(n, q, &n);
    if (v)
    {
      if (v & 1) m = mulii(m, q);
      if (is_pm1(n)) return gerepileuptoint(av, m);
    }
  }
  if (ifac_isprime(n)) { m = mulii(m, n); return gerepileuptoint(av, m); }
  if (m == gen_1) n = icopy(n); /* ifac_core destroys n */
  /* large composite without small factors */
  return gerepileuptoint(av, mulii(m, ifac_core(n)));
}

long
Z_issmooth(GEN m, ulong lim)
{
  pari_sp av=avma;
  ulong p = 2;
  forprime_t S;
  u_forprime_init(&S, 2, lim);
  while ((p = u_forprime_next_fast(&S)))
  {
    int stop;
    (void)Z_lvalrem_stop(&m, p, &stop);
    if (stop) { avma = av; return abscmpiu(m,lim)<=0; }
  }
  avma = av; return 0;
}

GEN
Z_issmooth_fact(GEN m, ulong lim)
{
  pari_sp av=avma;
  GEN F, P, E;
  ulong p;
  long i = 1, l = expi(m)+1;
  forprime_t S;
  P = cgetg(l, t_VECSMALL);
  E = cgetg(l, t_VECSMALL);
  F = mkmat2(P,E);
  u_forprime_init(&S, 2, lim);
  while ((p = u_forprime_next_fast(&S)))
  {
    long v;
    int stop;
    if ((v = Z_lvalrem_stop(&m, p, &stop)))
    {
      P[i] = p;
      E[i] = v; i++;
      if (stop)
      {
        if (abscmpiu(m,lim) > 0) break;
        P[i] = m[2];
        E[i] = 1; i++;
        setlg(P, i);
        setlg(E, i); avma = (pari_sp)F; return F;
      }
    }
  }
  avma = av; return NULL;
}

/***********************************************************************/
/**                                                                   **/
/**       COMPUTING THE MATRIX OF PRIME DIVISORS AND EXPONENTS        **/
/**                                                                   **/
/***********************************************************************/
static GEN
aux_end(GEN M, GEN n, long nb)
{
  GEN P,E, z = (GEN)avma;
  long i;

  if (n) gunclone(n);
  P = cgetg(nb+1,t_COL);
  E = cgetg(nb+1,t_COL);
  for (i=nb; i; i--)
  { /* allow a stackdummy in the middle */
    while (typ(z) != t_INT) z += lg(z);
    gel(E,i) = z; z += lg(z);
    gel(P,i) = z; z += lg(z);
  }
  gel(M,1) = P;
  gel(M,2) = E;
  return sort_factor(M, (void*)&abscmpii, cmp_nodata);
}

static void
STORE(long *nb, GEN x, long e) { (*nb)++; (void)x; (void)utoipos(e); }
static void
STOREu(long *nb, ulong x, long e) { STORE(nb, utoipos(x), e); }
static void
STOREi(long *nb, GEN x, long e) { STORE(nb, icopy(x), e); }
/* no prime less than p divides n */
static int
special_primes(GEN n, ulong p, long *nb, GEN T)
{
  long i, l = lg(T);
  if (l > 1)
  { /* pp = square of biggest p tried so far */
    long pp[] = { evaltyp(t_INT)|_evallg(4), 0,0,0 };
    pari_sp av = avma; affii(sqru(p), pp); avma = av;

    for (i = 1; i < l; i++)
      if (dvdiiz(n,gel(T,i), n))
      {
        long k = 1; while (dvdiiz(n,gel(T,i), n)) k++;
        STOREi(nb, gel(T,i), k);
        if (abscmpii(pp, n) > 0) return 1;
      }
  }
  return 0;
}

/* factor(sn*|n|), where sn = -1,1 or 0.
 * all != 0 : only look for prime divisors < all */
static GEN
ifactor_sign(GEN n, ulong all, long hint, long sn)
{
  GEN M, N;
  pari_sp av;
  long nb = 0, i;
  ulong lim;
  forprime_t T;

  if (!sn) retmkmat2(mkcol(gen_0), mkcol(gen_1));
  if (lgefint(n) == 3)
  { /* small integer */
    GEN f, Pf, Ef, P, E, F = cgetg(3, t_MAT);
    long l;
    av = avma;
    /* enough room to store <= 15 primes and exponents (OK if n < 2^64) */
    (void)new_chunk((15*3 + 15 + 1) * 2);
    f = factoru_sign(uel(n,2), all, hint);
    avma = av;
    Pf = gel(f,1);
    Ef = gel(f,2);
    l = lg(Pf);
    if (sn < 0)
    { /* add sign */
      long L = l+1;
      gel(F,1) = P = cgetg(L, t_COL);
      gel(F,2) = E = cgetg(L, t_COL);
      gel(P,1) = gen_m1; P++;
      gel(E,1) = gen_1;  E++;
    }
    else
    {
      gel(F,1) = P = cgetg(l, t_COL);
      gel(F,2) = E = cgetg(l, t_COL);
    }
    for (i = 1; i < l; i++)
    {
      gel(P,i) = utoipos(Pf[i]);
      gel(E,i) = utoipos(Ef[i]);
    }
    return F;
  }
  M = cgetg(3,t_MAT);
  if (sn < 0) STORE(&nb, utoineg(1), 1);
  if (is_pm1(n)) return aux_end(M,NULL,nb);

  n = N = gclone(n); setabssign(n);
  /* trial division bound */
  lim = all; if (!lim) lim = tridiv_bound(n);
  if (lim > 2)
  {
    ulong maxp, p;
    pari_sp av2;
    i = vali(n);
    if (i)
    {
      STOREu(&nb, 2, i);
      av = avma; affii(shifti(n,-i), n); avma = av;
    }
    if (is_pm1(n)) return aux_end(M,n,nb);
    /* trial division */
    maxp = maxprime();
    av = avma; u_forprime_init(&T, 3, minss(lim, maxp)); av2 = avma;
    /* first pass: known to fit in private prime table */
    while ((p = u_forprime_next_fast(&T)))
    {
      pari_sp av3 = avma;
      int stop;
      long k = Z_lvalrem_stop(&n, p, &stop);
      if (k)
      {
        affii(n, N); n = N; avma = av3;
        STOREu(&nb, p, k);
      }
      if (stop)
      {
        if (!is_pm1(n)) STOREi(&nb, n, 1);
        stackdummy(av, av2);
        return aux_end(M,n,nb);
      }
    }
    stackdummy(av, av2);
    if (lim > maxp)
    { /* second pass, usually empty: outside private prime table */
      av = avma; u_forprime_init(&T, maxp+1, lim); av2 = avma;
      while ((p = u_forprime_next(&T)))
      {
        pari_sp av3 = avma;
        int stop;
        long k = Z_lvalrem_stop(&n, p, &stop);
        if (k)
        {
          affii(n, N); n = N; avma = av3;
          STOREu(&nb, p, k);
        }
        if (stop)
        {
          if (!is_pm1(n)) STOREi(&nb, n, 1);
          stackdummy(av, av2);
          return aux_end(M,n,nb);
        }
      }
      stackdummy(av, av2);
    }
  }
  /* trial divide by the special primes */
  if (special_primes(n, lim, &nb, primetab))
  {
    if (!is_pm1(n)) STOREi(&nb, n, 1);
    return aux_end(M,n,nb);
  }

  if (all)
  { /* smallfact: look for easy pure powers then stop. Cf Z_isanypower */
    GEN x;
    long k;
    av = avma;
    k = isanypower_nosmalldiv(n, &x);
    if (k > 1) affii(x, n);
    avma = av; STOREi(&nb, n, k);
    if (DEBUGLEVEL >= 2) {
      pari_warn(warner,
        "IFAC: untested %ld-bit integer declared prime", expi(n));
      if (expi(n) <= 256)
        err_printf("\t%Ps\n", n);
    }
    return aux_end(M,n,nb);
  }
  if (ifac_isprime(n)) { STOREi(&nb, n, 1); return aux_end(M,n,nb); }
  nb += ifac_decomp(n, hint);
  return aux_end(M,n, nb);
}

static GEN
ifactor(GEN n, ulong all, long hint)
{ return ifactor_sign(n, all, hint, signe(n)); }

int
ifac_next(GEN *part, GEN *p, long *e)
{
  GEN here = ifac_main(part);
  if (here == gen_0) { *p = NULL; *e = 1; return 0; }
  if (!here) { *p = NULL; *e = 0; return 0; }
  *p = VALUE(here);
  *e = EXPON(here)[2];
  ifac_delete(here); return 1;
}

/* see before ifac_crack for current semantics of 'hint' (factorint's 'flag') */
GEN
factorint(GEN n, long flag)
{
  GEN F;
  if ((F = check_arith_all(n,"factorint"))) return gcopy(F);
  return ifactor(n,0,flag);
}

GEN
Z_factor_limit(GEN n, ulong all)
{
  if (!all) all = GP_DATA->primelimit + 1;
  return ifactor(n,all,decomp_default_hint);
}
GEN
absZ_factor_limit(GEN n, ulong all)
{
  if (!all) all = GP_DATA->primelimit + 1;
  return ifactor_sign(n,all,decomp_default_hint, signe(n)?1 : 0);
}
GEN
Z_factor(GEN n)
{ return ifactor(n,0,decomp_default_hint); }
GEN
absZ_factor(GEN n)
{ return ifactor_sign(n, 0, decomp_default_hint, signe(n)? 1: 0); }

/* Factor until the unfactored part is smaller than limit. Return the
 * factored part. Hence factorback(output) may be smaller than n */
GEN
Z_factor_until(GEN n, GEN limit)
{
  pari_sp av2, av = avma;
  ulong B = tridiv_bound(n);
  GEN q, part, F = ifactor(n, B, decomp_default_hint);
  GEN P = gel(F,1), E = gel(F,2);
  long l = lg(P);

  av2 = avma;
  q = gel(P,l-1);
  if (abscmpiu(q, B) <= 0 || cmpii(q, sqru(B)) < 0 || ifac_isprime(q))
  {
    avma = av2; return F;
  }
  /* q = composite unfactored part, remove from P/E */
  setlg(E,l-1);
  setlg(P,l-1);
  if (cmpii(q, limit) > 0)
  { /* factor further */
    long l2 = expi(q)+1;
    GEN  P2 = coltrunc_init(l2);
    GEN  E2 = coltrunc_init(l2);
    GEN  F2 = mkmat2(P2,E2);
    part = ifac_start(icopy(q), 0); /* ifac_next would destroy q */
    for(;;)
    {
      long e;
      GEN p;
      if (!ifac_next(&part,&p,&e)) break;
      vectrunc_append(P2, p);
      vectrunc_append(E2, utoipos(e));
      q = diviiexact(q, powiu(p, e));
      if (cmpii(q, limit) <= 0) break;
    }
    F2 = sort_factor(F2, (void*)&abscmpii, cmp_nodata);
    F = merge_factor(F, F2, (void*)&abscmpii, cmp_nodata);
  }
  return gerepilecopy(av, F);
}

static void
matsmalltrunc_append(GEN m, ulong p, ulong e)
{
  GEN P = gel(m,1), E = gel(m,2);
  long l = lg(P);
  P[l] = p; lg_increase(P);
  E[l] = e; lg_increase(E);
}
static GEN
matsmalltrunc_init(long l)
{
  GEN P = vecsmalltrunc_init(l);
  GEN E = vecsmalltrunc_init(l); return mkvec2(P,E);
}

/* If a <= c <= b , factoru(c) = L[c-a+1] */
GEN
vecfactoru_i(ulong a, ulong b)
{
  ulong N, k, p, n = b-a+1;
  GEN v = const_vecsmall(n, 1);
  GEN L = cgetg(n+1, t_VEC);
  forprime_t T;
  if (b < 510510UL) N = 7;
  else if (b < 9699690UL) N = 8;
#ifdef LONG_IS_64BIT
  else if (b < 223092870UL) N = 9;
  else if (b < 6469693230UL) N = 10;
  else if (b < 200560490130UL) N = 11;
  else if (b < 7420738134810UL) N = 12;
  else if (b < 304250263527210UL) N = 13;
  else N = 16; /* don't bother */
#else
  else N = 9;
#endif
  for (k = 1; k <= n; k++) gel(L,k) = matsmalltrunc_init(N);
  u_forprime_init(&T, 2, usqrt(b));
  while ((p = u_forprime_next(&T)))
  { /* p <= sqrt(b) */
    ulong pk = p, K = ulogint(b, p);
    for (k = 1; k <= K; k++)
    {
      ulong j, t = a / pk, ap = t * pk;
      if (ap < a) { ap += pk; t++; }
      /* t = (j+a-1) \ pk */
      for (j = ap-a+1; j <= n; j += pk, t++)
        if (t % p) { v[j] *= pk; matsmalltrunc_append(gel(L,j), p,k); }
      pk *= p;
    }
  }
  /* complete factorisation of non-sqrt(b)-smooth numbers */
  for (k = 1, N = a; k <= n; k++, N++)
    if (uel(v,k) != N) matsmalltrunc_append(gel(L,k), N/uel(v,k),1UL);
  return L;
}
GEN
vecfactoru(ulong a, ulong b)
{
  pari_sp av = avma;
  return gerepilecopy(av, vecfactoru_i(a,b));
}

/* Assume a and b odd, return L s.t. L[k] = factoru(a + 2*(k-1))
 * If a <= c <= b odd, factoru(c) = L[(c-a)>>1 + 1] */
GEN
vecfactoroddu_i(ulong a, ulong b)
{
  ulong N, k, p, n = ((b-a)>>1) + 1;
  GEN v = const_vecsmall(n, 1);
  GEN L = cgetg(n+1, t_VEC);
  forprime_t T;
  /* f(N)=my(a=primes(n+1));vecprod(a[2..#a]); */
  if (b < 255255UL) N = 6;
  else if (b < 4849845UL) N = 7;
  else if (b < 111546435UL) N = 8;
#ifdef LONG_IS_64BIT
  else if (b < 3234846615UL) N = 9;
  else if (b < 100280245065UL) N = 10;
  else if (b < 3710369067405UL) N = 11;
  else if (b < 152125131763605UL) N = 12;
  else N = 16; /* don't bother */
#else
  else N = 9;
#endif
  for (k = 1; k <= n; k++) gel(L,k) = matsmalltrunc_init(N);
  u_forprime_init(&T, 3, usqrt(b));
  while ((p = u_forprime_next(&T)))
  { /* p <= sqrt(b) */
    ulong pk = p, K = ulogint(b, p);
    for (k = 1; k <= K; k++)
    {
      ulong j, t = (a / pk) | 1UL, ap = t * pk;
      /* t and ap are odd, ap multiple of pk = p^k */
      if (ap < a) { ap += pk<<1; t+=2; }
      /* c=t*p^k by steps of 2*p^k; factorization of c*=p^k if (t,p)=1 */
      for (j = ((ap-a)>>1)+1; j <= n; j += pk, t+=2)
        if (t % p) { v[j] *= pk; matsmalltrunc_append(gel(L,j), p,k); }
      pk *= p;
    }
  }
  /* complete factorisation of non-sqrt(b)-smooth numbers */
  for (k = 1, N = a; k <= n; k++, N+=2)
    if (uel(v,k) != N) matsmalltrunc_append(gel(L,k), N/uel(v,k),1UL);
  return L;
}
GEN
vecfactoroddu(ulong a, ulong b)
{
  pari_sp av = avma;
  return gerepilecopy(av, vecfactoroddu_i(a,b));
}

/* If 0 <= a <= c <= b; L[c-a+1] = factoru(c)[,1] if c squarefree, else NULL */
GEN
vecfactorsquarefreeu(ulong a, ulong b)
{
  ulong N, k, p, n = b-a+1;
  GEN v = const_vecsmall(n, 1);
  GEN L = cgetg(n+1, t_VEC);
  forprime_t T;
  if (b < 510510UL) N = 7;
  else if (b < 9699690UL) N = 8;
#ifdef LONG_IS_64BIT
  else if (b < 223092870UL) N = 9;
  else if (b < 6469693230UL) N = 10;
  else if (b < 200560490130UL) N = 11;
  else if (b < 7420738134810UL) N = 12;
  else if (b < 304250263527210UL) N = 13;
  else N = 16; /* don't bother */
#else
  else N = 9;
#endif
  for (k = 1; k <= n; k++) gel(L,k) = vecsmalltrunc_init(N);
  u_forprime_init(&T, 2, usqrt(b));
  while ((p = u_forprime_next(&T)))
  { /* p <= sqrt(b), kill non-squarefree */
    ulong j, pk = p*p, t = a / pk, ap = t * pk;
    if (ap < a) { ap += pk; t++; }
    /* t = (j+a-1) \ pk */
    for (j = ap-a+1; j <= n; j += pk, t++) gel(L,j) = NULL;

    t = a / p; ap = t * p;
    if (ap < a) { ap += p; t++; }
    for (j = ap-a+1; j <= n; j += p, t++)
      if (gel(L,j)) { v[j] *= p; vecsmalltrunc_append(gel(L,j), p); }
  }
  /* complete factorisation of non-sqrt(b)-smooth numbers */
  for (k = 1, N = a; k <= n; k++, N++)
    if (gel(L,k) && uel(v,k) != N) vecsmalltrunc_append(gel(L,k), N/uel(v,k));
  return L;
}

GEN
vecsquarefreeu(ulong a, ulong b)
{
  ulong j, k, p, n = b-a+1;
  GEN L = const_vecsmall(n, 1);
  forprime_t T;
  u_forprime_init(&T, 2, usqrt(b));
  while ((p = u_forprime_next(&T)))
  { /* p <= sqrt(b), kill non-squarefree */
    ulong pk = p*p, t = a / pk, ap = t * pk;
    if (ap < a) { ap += pk; t++; }
    /* t = (j+a-1) \ pk */
    for (j = ap-a+1; j <= n; j += pk, t++) L[j] = 0;
  }
  for (k = j = 1; k <= n; k++)
    if (L[k]) L[j++] = a+k-1;
  setlg(L,j); return L;
}
