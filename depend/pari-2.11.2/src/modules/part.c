/* Copyright (C) 2002  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/* Original code contributed by: Ralf Stephan (ralf@ark.in-berlin.de).
 * Updated by Bill Allombert (2014) to use Selberg formula for L
 * following http://dx.doi.org/10.1112/S1461157012001088
 *
 * This program is basically the implementation of the script
 *
 * Psi(n, q) = my(a=sqrt(2/3)*Pi/q, b=n-1/24, c=sqrt(b));
 *             (sqrt(q)/(2*sqrt(2)*b*Pi))*(a*cosh(a*c)-(sinh(a*c)/c))
 * L(n,q)=sqrt(k/3)*sum(l=0,2*k-1,
          if(((3*l^2+l)/2+n)%k==0,(-1)^l*cos((6*l+1)/(6*k)*Pi)))
 * part(n) = round(sum(q=1,5 + 0.24*sqrt(n),L(n,q)*Psi(n,q)))
 *
 * only faster.
 *
 * ------------------------------------------------------------------
 *   The first restriction depends on Pari's maximum precision of floating
 * point reals, which is 268435454 bits in 2.2.4, since the algorithm needs
 * high precision exponentials. For that engine, the maximum possible argument
 * would be in [5*10^15,10^16], the computation of which would need days on
 * a ~1-GHz computer. */

#include "pari.h"
#include "paripriv.h"

/****************************************************************/

/* Given c = sqrt(2/3)*Pi*sqrt(N-1/24)
 * Psi(N, q) = my(a = c/q); sqrt(q) * (a*cosh(a) - sinh(a)) */
static GEN
psi(GEN c, ulong q, long prec)
{
  GEN a = divru(c, q), ea = mpexp(a), invea = invr(ea);
  GEN cha = shiftr(addrr(ea, invea), -1);  /* ch(a) */
  GEN sha = shiftr(subrr(ea, invea), -1);  /* sh(a) */
  return mulrr(sqrtr(stor(q,prec)), subrr(mulrr(a,cha), sha));
}

/* L(n,q)=sqrt(k/3)*sum(l=0,2*k-1,
          if(((3*l^2+l)/2+n)%k==0,(-1)^l*cos((6*l+1)/(6*k)*Pi)))
 * Never called with q < 3, so ignore this case */
static GEN
L(GEN n, ulong k, long bitprec)
{
  ulong r, l, m;
  long pr = nbits2prec(bitprec / k + k);
  GEN s = stor(0,pr), pi = mppi(pr);
  pari_sp av = avma;

  r = 2; m = umodiu(n,k);
  for (l = 0; l < 2*k; l++)
  {
    if (m == 0)
    {
      GEN c = mpcos(divru(mulru(pi, 6*l+1), 6*k));
      if (odd(l)) subrrz(s, c, s); else addrrz(s, c, s);
      avma = av;
    }
    m += r; if (m >= k) m -= k;
    r += 3; if (r >= k) r -= k;
  }
  /* multiply by sqrt(k/3) */
  return mulrr(s, sqrtr((k % 3)? rdivss(k,3,pr): utor(k/3,pr)));
}

/* Return a low precision estimate of log p(n). */
static GEN
estim(GEN n)
{
  pari_sp av = avma;
  GEN p1, pi = mppi (DEFAULTPREC);

  p1 = divru( itor(shifti(n,1), DEFAULTPREC), 3 );
  p1 = mpexp( mulrr(pi, sqrtr(p1)) ); /* exp(Pi * sqrt(2N/3)) */
  p1 = divri (shiftr(p1,-2), n);
  p1 = divrr(p1, sqrtr( stor(3,DEFAULTPREC) ));
  return gerepileupto(av, mplog(p1));
}

/* c = sqrt(2/3)*Pi*sqrt(n-1/24);  d = 1 / ((2*b)^(3/2) * Pi); */
static void
pinit(GEN n, GEN *c, GEN *d, ulong prec)
{
  GEN b = divru( itor( subiu(muliu(n,24), 1), prec ), 24 ); /* n - 1/24 */
  GEN sqrtb = sqrtr(b), Pi = mppi(prec), pi2sqrt2, pisqrt2d3;


  pisqrt2d3 = mulrr(Pi, sqrtr( divru(stor(2, prec), 3) ));
  pi2sqrt2  = mulrr(Pi, sqrtr( stor(8, prec) ));
  *c = mulrr(pisqrt2d3, sqrtb);
  *d = invr( mulrr(pi2sqrt2, mulrr(b,sqrtb)) );
}

/* part(n) = round(sum(q=1,5 + 0.24*sqrt(n), L(n,q)*Psi(n,q))) */
GEN
numbpart(GEN n)
{
  pari_sp ltop = avma, av;
  GEN sum, est, C, D, p1, p2;
  long prec, bitprec;
  ulong q;

  if (typ(n) != t_INT) pari_err_TYPE("partition function",n);
  if (signe(n) < 0) return gen_0;
  if (abscmpiu(n, 2) < 0) return gen_1;
  if (cmpii(n, uu32toi(0x38d7e, 0xa4c68000)) >= 0)
    pari_err_OVERFLOW("numbpart [n < 10^15]");
  est = estim(n);
  bitprec = (long)(rtodbl(est)/M_LN2) + 32;
  prec = nbits2prec(bitprec);
  pinit(n, &C, &D, prec);
  sum = cgetr (prec); affsr(0, sum);
  /* Because N < 10^16 and q < sqrt(N), q fits into a long
   * In fact q < 2 LONG_MAX / 3 */
  av = avma; togglesign(est);
  for (q = (ulong)(sqrt(gtodouble(n))*0.24 + 5); q >= 3; q--, avma=av)
  {
    GEN t = L(n, q, bitprec);
    if (abscmprr(t, mpexp(divru(est,q))) < 0) continue;

    t = mulrr(t, psi(gprec_w(C, nbits2prec(bitprec / q + 32)), q, prec));
    affrr(addrr(sum, t), sum);
  }
  p1 = addrr(sum, psi(C, 1, prec));
  p2 = psi(C, 2, prec);
  affrr(mod2(n)? subrr(p1,p2): addrr(p1,p2), sum);
  return gerepileuptoint (ltop, roundr(mulrr(D,sum)));
}

/* for loop over partitions of integer k.
 * nbounds can restrict partitions to have length between nmin and nmax
 * (the length is the number of non zero entries) and
 * abounds restrict to integers between amin and amax.
 *
 * Start from central partition.
 * By default, remove zero entries on the left.
 *
 * Algorithm:
 *
 * A partition of k is an increasing sequence v1,... vn with sum(vi)=k
 * The starting point is the minimal n-partition of k: a,...a,a+1,.. a+1
 * (a+1 is repeated r times with k = a * n + r).
 *
 * The procedure to obtain the next partition:
 * - find the last index i<n such that v{i-1} != v{i} (that is vi is the start
 * of the last constant range excluding vn).
 * - decrease vi by one, and set v{i+1},... v{n} to be a minimal partition (of
 * the right sum).
 *
 * Examples: we highlight the index i
 * 1 1 2 2 3
 *     ^
 * 1 1 1 3 3
 *       ^
 * 1 1 1 2 4
 *       ^
 * 1 1 1 1 5
 * ^
 * 0 2 2 2 3
 *   ^
 * This is recursive in nature. Restrictions on upper bounds of the vi or on
 * the length of the partitions are straightforward to take into account. */

static void
parse_interval(GEN a, long *amin, long *amax)
{
  switch (typ(a))
  {
  case t_INT:
    *amax = itos(a);
    break;
  case t_VEC:
    if (lg(a) != 3)
      pari_err_TYPE("forpart [expect vector of type [amin,amax]]",a);
    *amin = gtos(gel(a,1));
    *amax = gtos(gel(a,2));
    if (*amin>*amax || *amin<0 || *amax<=0)
      pari_err_TYPE("forpart [expect 0<=min<=max, 0<max]",a);
    break;
  default:
    pari_err_TYPE("forpart",a);
  }
}

void
forpart_init(forpart_t *T, long k, GEN abound, GEN nbound)
{

  /* bound on coefficients */
  T->amin=1;
  if (abound) parse_interval(abound,&T->amin,&T->amax);
  else T->amax = k;
  /* strip leading zeros ? */
  T->strip = (T->amin > 0) ? 1 : 0;
  /* bound on number of non-zero coefficients */
  T->nmin=0;
  if (nbound) parse_interval(nbound,&T->nmin,&T->nmax);
  else T->nmax = k;

  /* non empty if nmin*amin <= k <= amax*nmax */
  if ( T->amin*T->nmin > k || k > T->amax * T->nmax )
  {
    T->nmin = T->nmax = 0;
  }
  else
  {
    /* to reach nmin one must have k <= nmin*amax, otherwise increase nmin */
    if ( T->nmin * T->amax < k )
      T->nmin = 1 + (k - 1) / T->amax; /* ceil( k/tmax ) */
    /* decrease nmax (if strip): k <= amin*nmax */
    if (T->strip && T->nmax > k/T->amin)
      T->nmax = k / T->amin; /* strip implies amin>0 */ /* fixme: take ceil( ) */
    /* no need to change amin */
    /* decrease amax if amax + (nmin-1)*amin > k  */
    if ( T->amax + (T->nmin-1)* T->amin > k )
      T->amax = k - (T->nmin-1)* T->amin;
  }

  if ( T->amax < T->amin )
    T->nmin = T->nmax = 0;

  T->v = zero_zv(T->nmax); /* partitions will be of length <= nmax */
  T->k = k;
}

GEN
forpart_next(forpart_t *T)
{
  GEN v = T->v;
  long n = lg(v)-1;
  long i, s, a, k, vi, vn;

  if (n>0 && v[n])
  {
    /* find index to increase: i s.t. v[i+1],...v[n] is central a,..a,a+1,..a+1
       keep s = v[i] + v[i+1] + ... + v[n] */
    s = a = v[n];
    for(i = n-1; i>0 && v[i]+1 >= a; s += v[i--]);
    if (i == 0) {
      /* v is central [ a, a, .. a, a+1, .. a+1 ] */
      if ((n+1) * T->amin > s || n == T->nmax) return NULL;
      i = 1; n++;
      setlg(v, n+1);
      vi = T->amin;
    } else {
      s += v[i];
      vi = v[i]+1;
    }
  } else {
    /* init v */
    s = T->k;
    if (T->amin == 0) T->amin = 1;
    if (T->strip) { n = T->nmin; setlg(T->v, n+1); }
    if (s==0)
    {
      if (n==0 && T->nmin==0) {T->nmin++; return v;}
      return NULL;
    }
    if (n==0) return NULL;
    vi = T->amin;
    i = T->strip ? 1 : n + 1 - T->nmin; /* first non-zero index */
    if (s <= (n-i)*vi) return NULL;
  }
  /* now fill [ v[i],... v[n] ] with s, start at vi */
  vn = s - (n-i)*vi; /* expected value for v[n] */
  if (T->amax && vn > T->amax)
  {
    /* do not exceed amax */
    long ai, q, r;
    vn -= vi;
    ai = T->amax - vi;
    q = vn / ai; /* number of nmax */
    r = vn % ai; /* value before nmax */
    /* fill [ v[i],... v[n] ] as [ vi,... vi, vi+r, amax,... amax ] */
    while ( q-- ) v[n--] = T->amax;
    if ( n >= i ) v[n--] = vi + r;
    while ( n >= i ) v[n--] = vi;
  } else {
    /* fill as [ v[i], ... v[i], vn ] */
    for ( k=i; k<n; v[k++] = vi );
    v[n] = vn;
  }
  return v;
}

GEN
forpart_prev(forpart_t *T)
{
  GEN v = T->v;
  long n = lg(v)-1;
  long j, ni, q, r;
  long i, s;
  if (n>0 && v[n])
  {
    /* find index to decrease: start of last constant sequence, excluding v[n] */
    i = n-1; s = v[n];
    while (i>1 && (v[i-1]==v[i] || v[i+1]==T->amax))
      s+= v[i--];
    if (!i) return NULL;
    /* amax condition: cannot decrease i if maximal on the right */
    if ( v[i+1] == T->amax ) return NULL;
    /* amin condition: stop if below except if strip & try to remove */
    if (v[i] == T->amin) {
      if (!T->strip) return NULL;
      s += v[i]; v[i] = 0;
    } else {
      v[i]--; s++;
    }
    /* zero case... */
    if (v[i] == 0)
    {
      if (T->nmin > n-i) return NULL; /* need too many non zero coeffs */
      /* reduce size of v ? */
      if (T->strip) {
        i = 0; n--;
        setlg(v, n+1);
      }
    }
  } else
  {
    s = T->k;
    i = 0;
    if (s==0)
    {
      if (n==0 && T->nmin==0) {T->nmin++; return v;}
      return NULL;
    }
    if (n*T->amax < s || s < T->nmin*T->amin) return NULL;
  }
  /* set minimal partition of sum s starting from index i+1 */
  ni = n-i;
  q = s / ni;
  r = s % ni;
  for(j=i+1;   j<=n-r; j++) v[j]=q;
  for(j=n-r+1; j<=n;   j++) v[j]=q + 1;
  return v;
}

static long
countpart(long k, GEN abound, GEN nbound)
{
  pari_sp av = avma;
  long n;
  forpart_t T;
  if (k<0) return 0;
  forpart_init(&T, k, abound, nbound);
  for (n=0; forpart_next(&T); n++)
  avma = av;
  return n;
}

GEN
partitions(long k, GEN abound, GEN nbound)
{
  GEN v;
  forpart_t T;
  long i, n = countpart(k,abound,nbound);
  if (n==0) return cgetg(1, t_VEC);
  forpart_init(&T, k, abound, nbound);
  v = cgetg(n+1, t_VEC);
  for (i=1; i<=n; i++)
    gel(v,i)=zv_copy(forpart_next(&T));
  return v;
}

void
forpart(void *E, long call(void*, GEN), long k, GEN abound, GEN nbound)
{
  pari_sp av = avma;
  GEN v;
  forpart_t T;
  forpart_init(&T, k, abound, nbound);
  while ((v=forpart_next(&T)))
    if (call(E, v)) break;
  avma=av;
}

void
forpart0(GEN k, GEN code, GEN abound, GEN nbound)
{
  pari_sp av = avma;
  if (typ(k) != t_INT) pari_err_TYPE("forpart",k);
  if (signe(k)<0) return;
  push_lex(gen_0, code);
  forpart((void*)code, &gp_evalvoid, itos(k), abound, nbound);
  pop_lex(1);
  avma=av;
}
