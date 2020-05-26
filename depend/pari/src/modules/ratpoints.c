/* Copyright (C) 2017  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/* This file is based on ratpoints-2.1.3 by Michael Stoll, see
 * http://www.mathe2.uni-bayreuth.de/stoll/programs/
 * Original copyright / license: */
/***********************************************************************
 * ratpoints-2.1.3                                                     *
 * Copyright (C) 2008, 2009  Michael Stoll                             *
 *  - A program to find rational points on hyperelliptic curves        *
 *                                                                     *
 * This program is free software: you can redistribute it and/or       *
 * modify it under the terms of the GNU General Public License         *
 * as published by the Free Software Foundation, either version 2 of   *
 * the License, or (at your option) any later version.                 *
 ***********************************************************************/

#include "pari.h"
#include "paripriv.h"

#define pel(a,b)  gel((a),(b)+2)

#define RATPOINTS_ARRAY_SIZE 256           /* Array size in longs */
#define RATPOINTS_DEFAULT_SP1 9            /* Default value for sp1 */
#define RATPOINTS_DEFAULT_SP2 16           /* Default value for sp2 */
#define RATPOINTS_DEFAULT_NUM_PRIMES 28    /* Default value for num_primes */
#define RATPOINTS_DEFAULT_BIT_PRIMES 7     /* Default value for bit_primes */
#define RATPOINTS_DEFAULT_MAX_FORBIDDEN 30 /* Default value for max_forbidden */

typedef struct {double low; double up;} ratpoints_interval;

/* Define the flag bits for the flags component: */
#define RATPOINTS_NO_REVERSE      0x0004UL

#define RATPOINTS_FLAGS_INPUT_MASK (RATPOINTS_NO_REVERSE)

/* Flags bits for internal purposes */
#define RATPOINTS_REVERSED        0x0100UL
#define RATPOINTS_CHECK_DENOM     0x0200UL
#define RATPOINTS_USE_SQUARES     0x0400UL
#define RATPOINTS_USE_SQUARES1    0x0800UL

#define LONG_MASK (~(-(1UL<<TWOPOTBITS_IN_LONG)))

#define CEIL(a,b) (((a) <= 0) ? -(-(a) / (b)) : 1 + ((a)-1) / (b))

/* Some Macros for working with SSE registers */
#ifdef HAS_SSE2
#include <emmintrin.h>

#define AND(a,b) ((ratpoints_bit_array)__builtin_ia32_andps((__v4sf)(a), (__v4sf)(b)))
#define EXT0(a) ((ulong)__builtin_ia32_vec_ext_v2di((__v2di)(a), 0))
#define EXT1(a) ((ulong)__builtin_ia32_vec_ext_v2di((__v2di)(a), 1))
#define TEST(a) (EXT0(a) || EXT1(a))
#define RBA(a) ((__v2di){((long) a), ((long) a)})

/* Use SSE 128 bit registers for the bit arrays */
typedef __v2di ratpoints_bit_array;

#define RBA_LENGTH (128)
#define RBA_SHIFT (7)
#define RBA_ALIGN  (sizeof(ratpoints_bit_array))
#define RBA_MASK (~(-(1UL<<RBA_SHIFT)))

#else
/* Use ulong for the bit arrays */
typedef ulong ratpoints_bit_array;
#define AND(a,b) ((a)&(b))
#define EXT0(a) (a)
#define TEST(a) (a)
#define RBA(a) (a)

#define RBA_LENGTH BITS_IN_LONG
#define RBA_SHIFT TWOPOTBITS_IN_LONG
#define RBA_ALIGN  (sizeof(long))
#define RBA_MASK LONG_MASK

#endif

typedef struct { long p; long offset; ratpoints_bit_array *ptr; } sieve_spec;

typedef enum { num_all, num_even, num_odd, num_none } bit_selection;

typedef struct {
  long p; int *is_f_square;
  const long *inverses;
  long offset; ratpoints_bit_array** sieve;
} ratpoints_sieve_entry;

typedef struct { long p;
                 ulong *start;
                 ulong *end;
                 ulong *curr; }
               forbidden_entry;

typedef struct {
  GEN cof, listprime;
  ratpoints_interval *domain;
  long height, b_low, b_high, sp1, sp2, array_size;
  long num_inter, num_primes, bit_primes, max_forbidden;
  ulong flags;
/* from here: private data */
  GEN bc;
  ratpoints_sieve_entry *se_buffer;
  ratpoints_sieve_entry *se_next;
  ratpoints_bit_array *ba_buffer;
  ratpoints_bit_array *ba_next;
  int *int_buffer, *int_next;
  forbidden_entry *forb_ba;
  long *forbidden;
  GEN inverses, offsets, den_info, divisors;
  ulong **sieves0;
} ratpoints_args;

#ifdef HAS_SSE2
#define CODE_INIT_SIEVE_COPY for (a = 0; a < p; a++) si[a+p] = si[a];
#else
#define CODE_INIT_SIEVE_COPY
#endif

static ratpoints_bit_array *
#if defined(__GNUC__)
__attribute__((noinline))
#endif
sieve_init1(long p, ratpoints_sieve_entry *se1, long b1, ratpoints_args *args1)
{
  ratpoints_sieve_entry *se = se1;
  ratpoints_args *args = args1;
  register int *isfs = se->is_f_square;
  register long b = b1;
  long lmp = BITS_IN_LONG % p;
  long ldp = BITS_IN_LONG / p;
  long p1 = (ldp + 1) * p;
  long diff_shift = p1 & LONG_MASK;
  long diff = BITS_IN_LONG - diff_shift;
  register ulong help0;
  register long a;
  register long d = se->inverses[b];
  register long ab = 0; /* a/b mod p */
  register ulong test = 1UL;
  register ulong he0 = 0UL;
  for (a = 0; a < p; a++)
  {
    if (isfs[ab]) he0 |= test;
    ab += d;
    if (ab >= p) ab -= p;
    test <<= 1;
  }
  help0 = he0;
  {
    register ulong help1;
     /* repeat bit pattern floor(BITS_IN_LONG/p) times */
    register ulong pattern = help0;
    register long i;
    /* the p * (floor(BITS_IN_LONG/p) + 1) - BITS_IN_LONG
            = p - (BITS_IN_LONG mod p)
       upper bits into help[b][1] :
       shift away the  BITS_IN_LONG mod p  lower bits */
    help1 = pattern >> lmp;
    for (i = p; i < BITS_IN_LONG; i <<= 1)
      help0 |= help0 << i;
    { /* fill the bit pattern from help0/help1 into sieve[b][].
          sieve[b][a0] has the same semantics as help0/help1,
          but here, a0 runs from 0 to p-1 and all bits are filled. */
      register long a;
      ulong *si = (ulong *)args->ba_next;

      args->ba_next += p;
      /* copy the first chunk into sieve[b][] */
      si[0] = help0;
      /* now keep repeating the bit pattern,
         rotating it in help0/help1 */
      for (a = 1 ; a < p; a++)
      {
        register ulong temp = help0 >> diff;
        help0 = help1 | (help0 << diff_shift);
        si[a] = help0;
        help1 = temp;
      }
      CODE_INIT_SIEVE_COPY
      /* set sieve array */
      se->sieve[b] = (ratpoints_bit_array *)si;
      return (ratpoints_bit_array *)si;
    }
  }
}

/* This is for p > BITS_IN_LONG */
static ratpoints_bit_array *
#if defined(__GNUC__)
__attribute__((noinline))
#endif
sieve_init2(long p, ratpoints_sieve_entry *se1, long b1, ratpoints_args *args1)
{
  ratpoints_sieve_entry *se = se1;
  ratpoints_args *args = args1;
  register int *isfs = se->is_f_square;
  register long b = b1;
  /* long ldp = 0;  = BITS_IN_LONG / p */
  /* long p1 = p; = (ldp + 1) * p; */
  long wp = p >> TWOPOTBITS_IN_LONG;
  long diff_shift = p & LONG_MASK;
  long diff = BITS_IN_LONG - diff_shift;
  ulong help[(p>>TWOPOTBITS_IN_LONG) + 2];

  /* initialize help */
  {
    register ulong *he = &help[0];
    register ulong *he1 = &he[(p>>TWOPOTBITS_IN_LONG) + 2];
    while (he1 != he) { he1--; *he1 = 0UL; }
  }
  { register ulong work = 0UL;
    register long a;
    register long ab = 0; /* a/b mod p */
    register long d = se->inverses[b];
    register long n = 0;
    register ulong test = 1UL;
    for (a = 0; a < p; )
    {
      if (isfs[ab]) work |= test;
      ab += d;
      if (ab >= p) ab -= p;
      test <<= 1;
      a++;
      if ((a & LONG_MASK) == 0)
      { help[n] = work; n++; work = 0UL; test = 1UL; }
    }
    help[n] = work;
  }

  { /* fill the bit pattern from help[] into sieve[b][].
       sieve[b][a0] has the same semantics as help[b][a0],
       but here, a0 runs from 0 to p-1 and all bits are filled. */
    register ulong *si = (ulong *)args->ba_next;
    register long a1;
    register long a;

    args->ba_next += p;
    /* copy the first chunk from help[] into sieve[num][b][] */
    for (a = 0; a < wp; a++) si[a] = help[a];
    /* now keep repeating the bit pattern, rotating it in help */
    for (a1 = a ; a < p; a++)
    {
      register long t = (a1 == wp) ? 0 : a1+1;
      help[a1] |= help[t]<<diff_shift;
      si[a] = help[a1];
      a1 = t;
      help[a1] >>= diff;
    }
     CODE_INIT_SIEVE_COPY
    /* set sieve array */
    se->sieve[b] = (ratpoints_bit_array *)si;
    return (ratpoints_bit_array *)si;
  }
}

static GEN
gen_squares(GEN listprime)
{
  long nbprime = lg(listprime)-1;
  GEN sq = cgetg(nbprime+1, t_VEC);
  long n;
  for (n = 1; n <= nbprime; n++)
  {
    ulong i, p = uel(listprime,n);
    GEN w = zero_zv(p), work = w+1;
    work[0] = 1;
    /* record non-zero squares mod p, p odd */
    for (i = 1; i < p; i += 2) work[(i*i) % p] = 1;
    gel(sq, n) = w;
  }
  return sq;
}

static GEN
gen_offsets(GEN P)
{
  long n, l = lg(P);
  GEN of = cgetg(l, t_VEC);
  for (n = 1; n < l; n++)
  {
    ulong p = uel(P,n);
    uel(of, n) = Fl_inv((2*RBA_LENGTH)%p, p);
  }
  return of;
}

static GEN
gen_inverses(GEN P)
{
  long n, l = lg(P);
  GEN iv = cgetg(l, t_VEC);
  for (n = 1; n < l; n++)
  {
    ulong i, p = uel(P,n);
    GEN w = cgetg(p, t_VECSMALL);
    for (i = 1; i < p; i++) uel(w, i) = Fl_inv(i, p);
    gel(iv, n) = w;
  }
  return iv;
}

static ulong **
gen_sieves0(GEN listprime)
{
  long n;
  long nbprime = lg(listprime)-1;
  ulong ** si = (ulong**) new_chunk(nbprime+1);
  for (n = 1; n <= nbprime; n++)
  {
    ulong i, p = uel(listprime,n);
    ulong *w = (ulong *) stack_malloc_align(2*p*sizeof(ulong), RBA_ALIGN);
    for (i = 0; i < p; i++) uel(w,i) = ~0UL;
    for (i = 0; i < BITS_IN_LONG; i++)
      uel(w,(p*i)>>TWOPOTBITS_IN_LONG) &= ~(1UL<<((p*i) & LONG_MASK));
    for (i = 0; i < p; i++) uel(w,i+p) = uel(w,i);
    si[n] = w;
  }
  return si;
}

static void
gen_sieve(ratpoints_args *args)
{
  GEN listprimes = args->listprime;
  args->offsets = gen_offsets(listprimes);
  args->inverses = gen_inverses(listprimes);
  args->sieves0 = gen_sieves0(listprimes);
}

static GEN
ZX_positive_region(GEN P, long h, long bitprec)
{
  long prec = nbits2prec(bitprec);
  GEN it = mkvec2(stoi(-h),stoi(h));
  GEN R = ZX_Uspensky(P, it, 1, bitprec);
  long nR = lg(R)-1;
  long s = signe(poleval(P,gel(it,1)));
  long i=1, j;
  GEN iv, st, en;
  if (s<0 && nR==0) return NULL;
  iv = cgetg(((nR+1+(s>=0))>>1)+1, t_VEC);
  if (s>=0) st = itor(gel(it,1),prec);
  else    { st = gel(R,i); i++; }
  for (j=1; i<nR; j++)
  {
    gel(iv, j) = mkvec2(st, gel(R,i));
    st = gel(R,i+1);
    i+=2;
  }
  if (i==nR) en = gel(R,i); else en = itor(gel(it,2),prec);
  gel(iv,j) = mkvec2(st, en);
  return iv;
}

static long
posint(ratpoints_interval *ivlist, GEN P, long h)
{
  GEN R = ZX_positive_region(P, h, 53);
  const double eps = 1e-5;
  long nR, i;

  if (!R) return 0;
  nR = lg(R)-1;
  i = 1;
  for (i=1; i<=nR; i++)
  {
    ivlist[i-1].low = rtodbl(gmael(R,i,1))-eps;
    ivlist[i-1].up  = rtodbl(gmael(R,i,2))+eps;
  }
  return nR;
}

static long
ratpoints_compute_sturm(ratpoints_args *args)
{
  ratpoints_interval *ivlist = args->domain;
  args->num_inter = posint(ivlist, args->cof, (long) ivlist[0].up);
  return args->num_inter;
}

/**************************************************************************
 * Try to avoid divisions                                                 *
 **************************************************************************/
INLINE long
mod(long a, long b)
{
  long b1 = b << 4; /* b1 = 16*b */

  if (a < -b1) { a %= b; if (a < 0) { a += b; } return a ; }
  if (a < 0) { a += b1; }
  else { if (a >= b1) { return a % b; } }
  b1 >>= 1; /* b1 = 8*b */
  if (a >= b1) { a -= b1; }
  b1 >>= 1; /* b1 = 4*b */
  if (a >= b1) { a -= b1; }
  b1 >>= 1; /* b1 = 2*b */
  if (a >= b1) { a -= b1; }
  if (a >= b) { a -= b; }
  return a;
}

static void
set_bc(long b, ratpoints_args *args)
{
  GEN w0 = gen_1;
  GEN c = args->cof, bc;
  long k, degree = degpol(c);
  bc = cgetg(degree+2, t_POL);
  for (k = degree-1; k >= 0; k--)
  {
    w0 = muliu(w0, b);
    gel(bc,k+2) = mulii(gel(c,k+2), w0);
  }
  args->bc = bc;
}

/**************************************************************************
 * Check a `survivor' of the sieve if it really gives a point.            *
 **************************************************************************/

static long
_ratpoints_check_point(long a, long b, ratpoints_args *args, int *quit,
                 int process(long, long, GEN, void*, int*), void *info)
{
  pari_sp av = avma;
  GEN w0, w2, c = args->cof, bc = args->bc;
  long k, degree = degpol(c);
  int reverse = args->flags & RATPOINTS_REVERSED;

  /* Compute F(a, b), where F is the homogenized version of f
     of smallest possible even degree  */
  w2 = gel(c, degree+2);
  for (k = degree-1; k >= 0; k--)
  {
    w2 = mulis(w2, a);
    w2 = addii(w2, gel(bc,k+2));
  }
  if (odd(degree)) w2 = muliu(w2, b);
  /* check if f(x,z) is a square; if so, process the point(s) */
  if (signe(w2) >= 0 && Z_issquareall(w2, &w0))
  {
    if (reverse)
    {
      if (a >= 0) (void)process(b, a, w0, info, quit);
      else        (void)process(-b, -a, w0, info, quit);
    }
    else (void)process(a, b, w0, info, quit);
    if (!*quit && signe(w0) != 0)
    {
      GEN nw0 = negi(w0);
      if (reverse)
      {
        if (a >= 0) (void)process(b, a, nw0, info, quit);
        else        (void)process(-b, -a, nw0, info, quit);
      }
      else (void)process(a, b, nw0, info, quit);
    }
    return 1;
  }
  avma = av;
  return 0;
}

/**************************************************************************
 * The inner loop of the sieving procedure                                *
 **************************************************************************/
static long
_ratpoints_sift0(long b, long w_low, long w_high,
           ratpoints_args *args, bit_selection which_bits,
           ratpoints_bit_array *survivors, sieve_spec *sieves, int *quit,
           int process(long, long, GEN, void*, int*), void *info)
{
  long range = w_high - w_low;
  long sp1 = args->sp1;
  long sp2 = args->sp2;
  long i, n, nb = 0, absb = labs(b);
  ratpoints_bit_array *surv0;

  /* now do the sieving (fast!) */
  for (n = 0; n < sp1; n++)
  {
    ratpoints_bit_array *sieve_n = sieves[n].ptr;
    register long p = sieves[n].p;
    long r = mod(-w_low-sieves[n].offset, p);
    register ratpoints_bit_array *surv = survivors;

    if (w_high < w_low + r)
    { /* if we get here, r > 0, since w_high >= w_low always */
      register ratpoints_bit_array *siv1 = &sieve_n[p-r];
      register ratpoints_bit_array *siv0 = siv1 + range;

      while (siv1 != siv0) { *surv = AND(*surv, *siv1++); surv++; }
    }
    else
    {
      register ratpoints_bit_array *siv1 = &sieve_n[p-r];
      register ratpoints_bit_array *surv_end = &survivors[range - p];
      register long i;
      for (i = r; i; i--) { *surv = AND(*surv, *siv1++); surv++; }
      siv1 -= p;
      while (surv <= surv_end)
      {
        for (i = p; i; i--) { *surv = AND(*surv, *siv1++); surv++; }
        siv1 -= p;
      }
      surv_end += p;
      while (surv < surv_end) { *surv = AND(*surv, *siv1++); surv++; }
    }
  } /* for n */
  /* 2nd phase of the sieve: test each surviving bit array with more primes */
  surv0 = &survivors[0];
  for (i = w_low; i < w_high; i++)
  {
    register ratpoints_bit_array nums = *surv0++;
    sieve_spec *ssp = &sieves[sp1];
    register long n;

    for (n = sp2-sp1; n && TEST(nums); n--)
    {
      register long p = ssp->p;
      nums = AND(nums, ssp->ptr[mod(i + ssp->offset, p)]);
      ssp++;
    }

    /* Check the survivors of the sieve if they really give points */
    if (TEST(nums))
    {
      long a0, a, d;
#ifdef HAS_SSE2
      long da = (which_bits == num_all) ? RBA_LENGTH/2 : RBA_LENGTH;
#endif
           /* a will be the numerator corresponding to the selected bit */
      if (which_bits == num_all)
      {
        d = 1; a0 = i * RBA_LENGTH;
      }
      else
      {
        d = 2; a0 = i * 2 * RBA_LENGTH;
        if (which_bits == num_odd) a0++;
      }
      {
#ifdef HAS_SSE2
        ulong nums0 = EXT0(nums);
        ulong nums1 = EXT1(nums);
#else
        ulong nums0 = nums;
#endif

        for (a = a0; nums0; a += d, nums0 >>= 1)
        { /* test one bit */
          if (odd(nums0) && ugcd(labs(a), absb)==1)
          {
            if (!args->bc) set_bc(b, args);
            nb += _ratpoints_check_point(a, b, args, quit, process, info);
            if (*quit) return nb;
          }
        }
#ifdef HAS_SSE2
        for (a = a0 + da; nums1; a += d, nums1 >>= 1)
        { /* test one bit */
          if (odd(nums1) && ugcd(labs(a), absb)==1)
          {
            if (!args->bc) set_bc(b, args);
            nb += _ratpoints_check_point(a, b, args, quit, process, info);
            if (*quit) return nb;
          }
        }
#endif
      }
    }
  }
  return nb;
}

#define MAX_DIVISORS 512
 /* Maximal length of array for squarefree divisors of leading coefficient */

typedef struct { double r; ratpoints_sieve_entry *ssp; } entry;

static const int squares16[16] = {1,1,0,0,1,0,0,0,0,1,0,0,0,0,0,0};
 /* Says if a is a square mod 16, for a = 0..15 */

/**************************************************************************
 * Initialization and cleanup of ratpoints_args structure                 *
 **************************************************************************/

static ratpoints_sieve_entry*
alloc_sieve(long nbprime, long maxprime)
{
  long i;
  ratpoints_sieve_entry * s = (ratpoints_sieve_entry*)
                        stack_malloc(nbprime*sizeof(ratpoints_sieve_entry));
  for (i=0; i<nbprime; i++)
    s[i].sieve = (ratpoints_bit_array**) new_chunk(maxprime);
  return s;
}

/* NOTE: args->degree must be set */
static void
find_points_init(ratpoints_args *args, long bit_primes)
{
  long need = 0;
  long n, nbprime,maxprime;
  args->listprime = primes_interval_zv(3, 1<<bit_primes);
  nbprime = lg(args->listprime)-1;
  maxprime = args->listprime[nbprime];

  /* allocate space for se_buffer */
  args->se_buffer = alloc_sieve(nbprime, maxprime);
  args->se_next = args->se_buffer;
  for (n = 1; n <= nbprime; n++)
  {
    ulong p = args->listprime[n];
    need += p*p;
  }
  args->ba_buffer = (ratpoints_bit_array*)
     stack_malloc_align(need*sizeof(ratpoints_bit_array),RBA_ALIGN);
  args->ba_next = args->ba_buffer;

  /* allocate space for int_buffer */
  args->int_buffer = (int *) stack_malloc(nbprime*(maxprime+1)*sizeof(int));
  args->int_next = args->int_buffer;

  args->forb_ba   = (forbidden_entry*)
    stack_malloc((nbprime + 1)*sizeof(forbidden_entry));
  args->forbidden = new_chunk(nbprime + 1);
  gen_sieve(args);
  return;
}

/* f = leading coeff; b = b1*b2, b1 maximal with (b1, 2*f) = 1;
 * return Jacobi symbol (f, b1) */
INLINE int
rpjacobi(long b, GEN lcf)
{
  ulong f;
  b >>= vals(b);
  f = umodiu(lcf, b);
  return krouu(f, u_ppo(b,f));
}

/************************************************************************
 * Set up information on possible denominators                          *
 * when polynomial is of odd degree with leading coefficient != +-1     *
 ************************************************************************/

static void
setup_us1(ratpoints_args *args, GEN w0)
{
  GEN divisors;
  GEN F = Z_factor_limit(w0, 1000), P = gel(F,1), E = gel(F,2), S;
  long i, l = lg(P);
  if (cmpiu(gel(P,l-1), 1000) > 0)
    return;
  P = ZV_to_zv(P); E = ZV_to_zv(E);
  divisors  = cgetg(1+(1<<(l-1)), t_VECSMALL);
  /* factorization is complete, set up array of squarefree divisors */
  divisors[1] = 1;
  for (i = 1; i < l; i++)
  { /* multiply all divisors known so far by next prime */
    long k, n = 1<<(i-1);
    for (k=0; k<n; k++)
      uel(divisors,1+n+k) = uel(divisors,1+k) * P[i];
  }
  S = cgetg(l, t_VECSMALL);
  /* set slopes in den_info */
  for (i = 1; i < l; i++)
  { /* compute min{n : (d-k)*n > v_p(f_d) - v_p(f_k), k = 0,...,d-1} */
    GEN c = args->cof;
    long p = P[i], v = E[i];
    long k, n = 1, d = degpol(c);

    for (k = d - 1; k >= 0; k--)
    {
      long t = 1 + v - Z_lval(gel(c,k+2), p);
      long m = CEIL(t, (d - k));

      if (m > n) n = m;
    }
    S[i] = n;
  }
  args->divisors = divisors;
  args->flags |= RATPOINTS_USE_SQUARES1;
  args->den_info = mkvec3(P, E, S);
}

/************************************************************************
 * Consider 2-adic information                                          *
 ************************************************************************/

static bit_selection
get_2adic_info(ratpoints_args *args, ulong *den_bits,
               ratpoints_bit_array *num_bits)
{
  GEN c = args->cof;
  long degree = degpol(c);
  int is_f_square16[24];
  long *cmp = new_chunk(degree+1);
  long npe = 0, npo = 0;
  bit_selection result;
  long n, a, b;

  /* compute coefficients mod 16 */
  for (n = 0; n <= degree; n++) cmp[n] = Mod16(gel(c,n+2));
  for (a = 0 ; a < 16; a++)
  {
    ulong s = cmp[degree];
    long n;
    for (n = degree - 1 ; n >= 0 ; n--) s = s*a + cmp[n];
    s &= 0xf;
    if ((is_f_square16[a] = squares16[s])) { if (odd(a)) npo++; else npe++; }
  }

  /* even denominators:
     is_f_square16[16+k] says if f((2k+1)/2) is a square, k = 0..3
     is_f_square16[20+k] says if f((2k+1)/4) is a square, k = 0,1
     is_f_square16[22]   says if f(odd/8) is a square
     is_f_square16[23]   says if f(odd/2^n), n >= 4, can be a square */
  {
    long np1 = 0, np2 = 0, np3 = 0, np4 = 0;

    if (odd(degree))
    {
      long a, cf = 4*cmp[degree-1];

      if (degree >= 2) cf += 8*cmp[degree-2];
      for (a = 0; a < 4; a++)
      { /* Compute  2 c[d] k^d + 4 c[d-1] k^(d-1) + 8 c[d-2] k^(d-2), k = 2a+1.
           Note that k^d = k mod 8, k^(d-1) = 1 mod 8. */
        long k = 2*a+1;
        long s = (2*k*cmp[degree] + cf) & 0xf;
        if ((is_f_square16[16+a] = squares16[s])) np1++;
      }
      if ((is_f_square16[20] = squares16[(4*cmp[degree])  & 0xf])) np2++;
      if ((is_f_square16[21] = squares16[(12*cmp[degree]) & 0xf])) np2++;
      if ((is_f_square16[22] = squares16[(8*cmp[degree])  & 0xf])) np3++;
      is_f_square16[23] = 1; np4++;
    }
    else
    {
      long a, cf = (degree >= 2) ? 4*cmp[degree-2] : 0;

      if (degree >= 3) cf += 8*cmp[degree-3];
      for (a = 0; a < 4; a++)
      { /* compute c[d] k^d + 2 c[d-1] k^(d-1) + ... + 8 c[d-3] k^(d-3),
           k = 2a+1. Note that k^d = k^2 mod 16, k^(d-1) = k mod 8. */
        long k = 2*a+1;
        long s = ((cmp[degree]*k + 2*cmp[degree-1])*k + cf) & 0xf;
        if ((is_f_square16[16+a] = squares16[s])) np1++;
      }
      if ((is_f_square16[20] = squares16[(cmp[degree]+4*cmp[degree-1])  & 0xf]))
        np2++;
      if ((is_f_square16[21] = squares16[(cmp[degree]+12*cmp[degree-1]) & 0xf]))
        np2++;
      if ((is_f_square16[22] = squares16[(cmp[degree]+8*cmp[degree-1])  & 0xf]))
        np3++;
      if ((is_f_square16[23] = squares16[cmp[degree]])) np4++;
    }

    /* set den_bits */
    { ulong db = 0;
      long i;

      if (npe + npo > 0) db |= 0xaaaaUL; /* odd denominators */
      if (np1 > 0)       db |= 0x4444UL; /* v_2(den) = 1 */
      if (np2 > 0)       db |= 0x1010UL; /* v_2(den) = 2 */
      if (np3 > 0)       db |= 0x0100UL; /* v_2(den) = 3 */
      if (np4 > 0)       db |= 0x0001UL; /* v_2(den) >= 4 */
      if (db == 0) { *den_bits = 0UL; return num_none; }

      for (i = 16; i < BITS_IN_LONG; i <<= 1) db |= db << i;
      *den_bits = db;
    }
    result = (npe == 0) ? (npo == 0) ? num_none : num_odd
                        : (npo == 0) ? num_even : num_all;
  }

  /* set up num_bits[16] */

  /* odd denominators */
  switch(result)
  {
    case num_all:
      for (b = 1; b < 16; b += 2)
      {
        ulong work = 0, bit = 1;
        long i, invb = b; /* inverse of b mod 16 */
        if (b & 2) invb ^= 8;
        if (b & 4) invb ^= 8;
        for (i = 0; i < 16; i++)
        {
          if (is_f_square16[(invb*i) & 0xf]) work |= bit;
          bit <<= 1;
        }
        /* now repeat the 16 bits */
        for (i = 16; i < BITS_IN_LONG; i <<= 1) work |= work << i;
        num_bits[b] = RBA(work);
      }
      break;

    case num_odd:
      for (b = 1; b < 16; b += 2)
      {
        ulong work = 0, bit = 1;
        long i, invb = b; /* inverse of b mod 16 */
        if (b & 2) invb ^= 8;
        if (b & 4) invb ^= 8;
        for (i = 1; i < 16; i += 2)
        {
          if (is_f_square16[(invb*i) & 0xf]) work |= bit;
          bit <<= 1;
        }
        /* now repeat the 8 bits */
        for (i = 8; i < BITS_IN_LONG; i <<= 1) { work |= work << i; }
        num_bits[b] = RBA(work);
      }
      break;

    case num_even:
      for (b = 1; b < 16; b += 2)
      {
        ulong work = 0, bit = 1;
        long i, invb = b; /* inverse of b mod 16 */
        if (b & 2) invb ^= 8;
        if (b & 4) invb ^= 8;
        for (i = 0; i < 16; i += 2)
        {
          if (is_f_square16[(invb*i) & 0xf]) work |= bit;
          bit <<= 1;
        }
        /* now repeat the 8 bits */
        for (i = 8; i < BITS_IN_LONG; i <<= 1) work |= work << i;
        num_bits[b] = RBA(work);
      }
      break;

    case num_none:
      for (b = 1; b < 16; b += 2) num_bits[b] = RBA(0UL);
      break;
  }

  /* v_2(den) = 1 : only odd numerators */
  for (b = 1; b < 8; b += 2)
  {
    ulong work = 0, bit = 1;
    long i;
    for (i = 1; i < 16; i += 2)
    {
      if (is_f_square16[16 + (((b*i)>>1) & 0x3)]) work |= bit;
      bit <<= 1;
    }
    /* now repeat the 8 bits */
    for (i = 8; i < BITS_IN_LONG; i <<= 1) work |= work << i;
    num_bits[2*b] = RBA(work);
  }

  /* v_2(den) = 2 : only odd numerators */
  for (b = 1; b < 4; b += 2)
  {
    ulong work = 0, bit = 1;
    long i;
    for (i = 1; i < 8; i += 2)
    {
      if (is_f_square16[20 + (((b*i)>>1) & 0x1)]) work |= bit;
      bit <<= 1;
    }
    /* now repeat the 4 bits */
    for (i = 4; i < BITS_IN_LONG; i <<= 1) work |= work << i;
    num_bits[4*b] = RBA(work);
  }

  /* v_2(den) = 3, >= 4 : only odd numerators */
  num_bits[8] = (is_f_square16[22]) ? RBA(~(0UL)) : RBA(0UL);
  num_bits[0] = (is_f_square16[23]) ? RBA(~(0UL)) : RBA(0UL);

  return result;
}

/**************************************************************************
 * This is a comparison function needed for sorting in order to determine *
 * the `best' primes for sieving.                                         *
 **************************************************************************/

static int
compare_entries(const void *a, const void *b)
{
  double diff = ((entry *)a)->r - ((entry *)b)->r;
  return (diff > 0) ? 1 : (diff < 0) ? -1 : 0;
}

/************************************************************************
 * Collect the sieving information                                      *
 ************************************************************************/

static long
sieving_info(ratpoints_args *args,
             ratpoints_sieve_entry **sieve_list)
{
  GEN c = args->cof;
  GEN inverses = args->inverses, squares;
  GEN offsets = args->offsets;
  ulong ** sieves0 = args->sieves0;
  long degree = degpol(c);
  long fba = 0, fdc = 0;
  long pn, pnp = 0;
  long n;
  long nbprime = lg(args->listprime)-1;
  entry *prec = (entry*) stack_malloc(nbprime*sizeof(entry));
    /* This array is used for sorting in order to
       determine the `best' sieving primes. */

  forbidden_entry *forb_ba = args->forb_ba;
  long *forbidden = args->forbidden;
  ulong bound = (1UL)<<(BITS_IN_LONG - args->bit_primes);
  pari_sp av = avma;
  squares = gen_squares(args->listprime);

  /* initialize sieve in se_buffer */
  for (pn = 1; pn <= args->num_primes; pn++)
  {
    long coeffs_mod_p[degree+1]; /* The coefficients of f reduced modulo p */
    ulong a, p = args->listprime[pn], np;
    long n;
    int *is_f_square = args->int_next;

    args->int_next += p + 1; /* need space for (p+1) int's */

    /* compute coefficients mod p */
    for (n = 0; n <= degree; n++) coeffs_mod_p[n] = umodiu(pel(c,n), p);

    np = umael(squares,pn,coeffs_mod_p[0]+1);
    is_f_square[0] = np;
    for (a = 1 ; a < p; a++)
    {
      ulong s = coeffs_mod_p[degree];
      if ((degree+1)*args->bit_primes <= BITS_IN_LONG)
      {
        for (n = degree - 1 ; n >= 0 ; n--) s = s*a + coeffs_mod_p[n];
        /* here, s < p^(degree+1) <= max. long */
        s %= p;
      }
      else
      {
        for (n = degree - 1 ; n >= 0 ; n--)
        {
          s = s*a + coeffs_mod_p[n];
          if (s+1 >= bound) s %= p;
        }
        s %= p;
      }
      if ((is_f_square[a] = mael(squares,pn,s+1))) np++;
    }
    is_f_square[p] = odd(degree) || mael(squares,pn,coeffs_mod_p[degree]+1);

    /* check if there are no solutions mod p */
    if (np == 0 && !is_f_square[p]) { avma = av; return p; }

    /* Fill arrays with info for p */
    if (np < p)
    { /* only when there is some information */
      ulong i;
      ratpoints_sieve_entry *se = args->se_next;
      double r = is_f_square[p] ? ((double)(np*(p-1) + p))/((double)(p*p))
                                : (double)np/(double)p;
      prec[pnp].r = r;
      args->se_next ++;
      se->p = p;
      se->is_f_square = is_f_square;
      se->inverses = gel(inverses,pn);
      se->offset = offsets[pn];
      se->sieve[0] = (ratpoints_bit_array *)sieves0[pn];
      for (i = 1; i < p; i++) se->sieve[i] = NULL;
      prec[pnp].ssp = se;
      pnp++;
    }

    if ((args->flags & RATPOINTS_CHECK_DENOM)
         && fba + fdc < args->max_forbidden
         && !is_f_square[p])
    { /* record forbidden divisors of the denominator */
      if (coeffs_mod_p[degree] == 0)
      { /* leading coeff. divisible by p */
        GEN r;
        long v = Z_lvalrem(pel(c,degree), p, &r);

        if (odd(v) || !mael(squares,pn, umodiu(r,p)+1))
        { /* Can only get something when valuation is odd
             or when valuation is even and lcf is not a p-adic square.
             Compute smallest n such that if v(den) >= n, the leading
             term determines the valuation. Then we must have v(den) < n. */
          long k, n = 1;
          for (k = degree-1; k >= 0; k--)
          {
            if (coeffs_mod_p[k] == 0)
            {
              long t = 1 + v - Z_lval(pel(c,k), p);
              long m = CEIL(t, (degree-k));
              if (m > n) n = m;
            }
          }
          if (n == 1)
          {
            forb_ba[fba].p     = p;
            forb_ba[fba].start = sieves0[pn];
            forb_ba[fba].end   = sieves0[pn]+p;
            forb_ba[fba].curr  = forb_ba[fba].start;
            fba++;
          }
          else
          {
            forbidden[fdc] = upowuu(p, n);
            fdc++;
          }
        }
      }
      else /* leading coefficient is a non-square mod p */
      { /* denominator divisible by p is excluded */
        forb_ba[fba].p     = p;
        forb_ba[fba].start = sieves0[pn];
        forb_ba[fba].end   = sieves0[pn]+p;
        forb_ba[fba].curr  = forb_ba[fba].start;
        fba++;
      }
    }
  } /* end for pn */

  /* update sp2 and sp1 if necessary */
  if (args->sp2 > pnp)       args->sp2 = pnp;
  if (args->sp1 > args->sp2) args->sp1 = args->sp2;

  /* sort the array to get at the best primes */
  qsort(prec, pnp, sizeof(entry), compare_entries);

  /* put the sorted entries into sieve_list */
  for (n = 0; n < args->sp2; n++) sieve_list[n] = prec[n].ssp;

  /* terminate array of forbidden divisors */
  if (args->flags & RATPOINTS_CHECK_DENOM)
  {
    long n;

    for (n = args->num_primes+1;
        fba + fdc < args->max_forbidden && n <= nbprime; n++)
    {
      ulong p = args->listprime[n];

      if (p*p > (ulong) args->b_high) break;
      if (kroiu(pel(c,degree), p) == -1)
      {
        forb_ba[fba].p     = p;
        forb_ba[fba].start = sieves0[n];
        forb_ba[fba].end   = sieves0[n]+p;
        forb_ba[fba].curr  = forb_ba[fba].start;
        fba++;
      }
    }
    forb_ba[fba].p = 0; /* terminating zero */
    forbidden[fdc] = 0; /* terminating zero */
    args->max_forbidden = fba + fdc; /* note actual number */
  }

  if (fba + fdc == 0) args->flags &= ~RATPOINTS_CHECK_DENOM;
  avma = av; return 0;
}

/**************************************************************************
 * The sieving procedure itself                                           *
 **************************************************************************/
static void
sift(long b, ratpoints_bit_array *survivors, ratpoints_args *args,
     bit_selection which_bits, ratpoints_bit_array bits16,
     ratpoints_sieve_entry **sieve_list, long *bp_list, int *quit,
     int process(long, long, GEN, void*, int*), void *info)
{
  pari_sp av = avma;
  sieve_spec ssp[args->sp2];
  int do_setup = 1;
  long k, height = args->height, nb;

  if (odd(b) == 0) which_bits = num_odd; /* even denominator */

  /* Note that b is new */
  args->bc = NULL;
  nb = 0;

  for (k = 0; k < args->num_inter; k++)
  {
    ratpoints_interval inter = args->domain[k];
    long low, high;

    /* Determine relevant interval [low, high] of numerators. */
    if (b*inter.low <= -height)
      low = -height;
    else
    {
      if (b*inter.low > height) break;
      low = ceil(b*inter.low);
    }
    if (b*inter.up >= height)
      high = height;
    else
    {
      if (b*inter.up < -height) continue;
      high = floor(b*inter.up);
    }

    if (do_setup)
    { /* set up the sieve information */
      long n;

      do_setup = 0; /* only do it once for every b */
      for (n = 0; n < args->sp2; n++)
      {
        ratpoints_sieve_entry *se = sieve_list[n];
        long p = se->p;
        long bp = bp_list[n];
        ratpoints_bit_array *sptr;

        if (which_bits != num_all) /* divide by 2 mod p */
          bp = odd(bp) ? (bp+p) >> 1 : bp >> 1;
        sptr = se->sieve[bp];

        ssp[n].p = p;
        ssp[n].offset = (which_bits == num_odd) ? se->offset : 0;

        /* copy if already initialized, else initialize */
        ssp[n].ptr = sptr ? sptr : (p<BITS_IN_LONG?sieve_init1(p, se, bp, args)
                                                  :sieve_init2(p, se, bp, args));
      }
    }

    switch(which_bits)
    {
      case num_all: break;
      case num_none: break;
      case num_odd: low >>= 1; high--; high >>= 1; break;
      case num_even: low++; low >>= 1; high >>= 1; break;
    }

    /* now turn the bit interval into [low, high[ */
    high++;

    if (low < high)
    {
      long w_low, w_high, w_low0, w_high0, range = args->array_size;

      /* Now the range of longwords (= bit_arrays) */
      w_low = low >> RBA_SHIFT;
      w_high = (high + (long)(RBA_LENGTH-1)) >> RBA_SHIFT;
      w_low0 = w_low;
      w_high0 = w_low0 + range;
      for ( ; w_low0 < w_high; w_low0 = w_high0, w_high0 += range)
      {
        long i;
        if (w_high0 > w_high) { w_high0 = w_high; range = w_high0 - w_low0; }
        /* initialise the bits */
        for (i = range; i; i--) survivors[i-1] = bits16;
        /* boundary words */
        if (w_low0 == w_low)
        {
          long sh = low - RBA_LENGTH * w_low;
          ulong *survl = (ulong *)survivors;

#ifdef HAS_SSE2
          if (sh >= BITS_IN_LONG)
          {
            survl[0] = 0UL;
            survl[1] &= (~0UL)<<(sh - BITS_IN_LONG);
          }
          else
            survl[0] &= ~(0UL)<<sh;
#else
          survl[0] &= ~(0UL)<<sh;
#endif
        }
        if (w_high0 == w_high)
        {
          long sh = RBA_LENGTH * w_high - high;
          ulong *survl = (ulong *)&survivors[range-1];

#ifdef HAS_SSE2
          if (sh >= BITS_IN_LONG)
          {
            survl[0] &= ~(0UL)>>(sh - BITS_IN_LONG);
            survl[1] = 0UL;
          }
          else
            survl[1] &= ~(0UL)>>sh;
#else
          survl[0] &= ~(0UL)>>sh;
#endif
        }
        nb += _ratpoints_sift0(b, w_low0, w_high0, args, which_bits,
                         survivors, &ssp[0], quit, process, info);
        if (*quit) return;
      }
    }
  }
  if (nb==0) avma = av;
}

/**************************************************************************
 * Find points by looping over the denominators and sieving numerators    *
 **************************************************************************/
static void
find_points_work(ratpoints_args *args,
                 int process(long, long, GEN, void*, int*), void *info)
{
  int quit = 0;
  GEN c = args->cof;
  long degree = degpol(c);
  long nbprime = lg(args->listprime)-1;
  long height = args->height;

  int point_at_infty = 0; /* indicates if there are points at infinity */
  int lcfsq = Z_issquare(pel(c,degree));

  forbidden_entry *forb_ba = args->forb_ba;
  long *forbidden = args->forbidden;
    /* The forbidden divisors, a zero-terminated array.
       Used when degree is even and leading coefficient is not a square */

    /* These are used when degree is odd and leading coeff. is not +-1 */

  ratpoints_sieve_entry **sieve_list = (ratpoints_sieve_entry**)
     stack_malloc(nbprime*sizeof(ratpoints_sieve_entry*));
  bit_selection which_bits = num_all;
  ulong den_bits;
  ratpoints_bit_array num_bits[16];

  args->flags &= RATPOINTS_FLAGS_INPUT_MASK;
  args->flags |= RATPOINTS_CHECK_DENOM;

  /* initialize memory management */
  args->se_next = args->se_buffer;
  args->ba_next = args->ba_buffer;
  args->int_next = args->int_buffer;

  /* Some sanity checks */
  args->num_inter = 0;

  if (args->num_primes > nbprime) args->num_primes = nbprime;
  if (args->sp2 > args->num_primes) args->sp2 = args->num_primes;
  if (args->sp1 > args->sp2)        args->sp1 = args->sp2;

  if (args->b_low < 1)  args->b_low = 1;
  if (args->b_high < 1) args->b_high = height;
  if (args->b_high > height) args->b_high = height;
  if (args->max_forbidden < 0)
    args->max_forbidden = RATPOINTS_DEFAULT_MAX_FORBIDDEN;
  if (args->max_forbidden > nbprime)
    args->max_forbidden = nbprime;
  if (args->array_size <= 0) args->array_size = RATPOINTS_ARRAY_SIZE;
  {
    long s = 2*CEIL(height, BITS_IN_LONG);
    if (args->array_size > s) args->array_size = s;
  }
  /* Don't reverse if intervals are specified or limits for the denominator
     are given */
  if (args->num_inter > 0 || args->b_low > 1 || args->b_high < height)
    args->flags |= RATPOINTS_NO_REVERSE;

  /* Check if reversal of polynomial might be better:
   * case 1: degree is even, but trailing coefficient is zero
   * case 2: degree is even, leading coefficient is a square, but
   *         trailing coefficient is not
   * case 3: degree is odd, |leading coefficient| > 1,
   *         trailing coefficient is zero, |coeff. of x| = 1 */
  if (!(args->flags & RATPOINTS_NO_REVERSE))
  {
    if (!odd(degree))
    {
      if (signe(pel(c,0)) == 0)
      { /* case 1 */
        long n;
        args->flags |= RATPOINTS_REVERSED;
        for (n = 0; n < degree>>1; n++) swap(pel(c,n), pel(c,degree-n));
        degree--;
        setlg(c,degree+3);
      }
      else if (lcfsq && !Z_issquare(pel(c,0)))
      { /* case 2 */
        long n;
        args->flags |= RATPOINTS_REVERSED;
        for (n = 0; n < degree>>1; n++) swap(pel(c,n), pel(c,degree-n));
        lcfsq = 0;
      }
    }
    else
    { /* odd degree, case 3*/
      if (!is_pm1(pel(c,degree)) && !signe(pel(c,0)) && is_pm1(pel(c,1)))
      {
        long n;
        args->flags |= RATPOINTS_REVERSED;
        for (n = 1; n < degree>>1; n++) swap(pel(c,n),pel(c,degree+1-n));
      }
    }
  }

  /* Deal with the intervals */
  if (args->num_inter == 0)
  { /* default interval (effectively ]-oo,oo[) if none is given */
    args->domain = (ratpoints_interval*) stack_malloc(2*degree*sizeof(ratpoints_interval));
    args->domain[0].low = -height; args->domain[0].up = height;
    args->num_inter = 1;
  }

  ratpoints_compute_sturm(args);

  /* Point(s) at infinity? */
  if (odd(degree) || lcfsq)
  {
    args->flags &= ~RATPOINTS_CHECK_DENOM;
    point_at_infty = 1;
  }

  /* Can use only squares as denoms if degree is odd and poly is +-monic */
  if (odd(degree))
  {
    GEN w1 = pel(c,degree);
    if (is_pm1(w1))
      args->flags |= RATPOINTS_USE_SQUARES;
    else /* set up information on divisors of leading coefficient */
      setup_us1(args, absi_shallow(w1));
  }

  /* deal with f mod powers of 2 */
  which_bits = get_2adic_info(args, &den_bits, &num_bits[0]);
  /* which_bits says whether to consider even and/or odd numerators
   * when the denominator is odd.
   *
   * Bit k in den_bits is 0 if b congruent to k mod BITS_IN_LONG need
   * not be considered as a denominator.
   *
   * Bit k in num_bits[b] is 0 is numerators congruent to
   *  k (which_bits = den_all)
   *  2k (which_bits = den_even)
   *  2k+1 (which_bits = den_odd)
   * need not be considered for denominators congruent to b mod 16. */

  /* set up the sieve data structure */
  if (sieving_info(args, sieve_list)) return;

  /* deal with point(s) at infinity */
  if (point_at_infty)
  {
    long a = 1, b = 0;

    if (args->flags & RATPOINTS_REVERSED) { a = 0; b = 1; }
    if (odd(degree))
      (void)process(a, b, gen_0, info, &quit);
    else
    {
      GEN w0 = sqrti(pel(c,degree));
      (void)process(a, b, w0, info, &quit);
      (void)process(a, b, negi(w0), info, &quit);
    }
    if (quit) return;
  }
  /* now do the sieving */
  {
    ratpoints_bit_array *survivors = (ratpoints_bit_array *)
      stack_malloc_align((args->array_size)*sizeof(ratpoints_bit_array), RBA_ALIGN);
    if (args->flags & (RATPOINTS_USE_SQUARES | RATPOINTS_USE_SQUARES1))
    {
      if (args->flags & RATPOINTS_USE_SQUARES)
      /* need only take squares as denoms */
      {
        long b, bb;
        long bp_list[args->sp2];
        long last_b = args->b_low;
        long n;
        for (n = 0; n < args->sp2; n++)
          bp_list[n] = mod(args->b_low, sieve_list[n]->p);

        for (b = 1; bb = b*b, bb <= args->b_high; b++)
          if (bb >= args->b_low)
          {
            ratpoints_bit_array bits = num_bits[bb & 0xf];
            if (TEST(bits))
            {
              long n;
              long d = bb - last_b;

              /* fill bp_list */
              for (n = 0; n < args->sp2; n++)
                bp_list[n] = mod(bp_list[n] + d, sieve_list[n]->p);
              last_b = bb;

              sift(bb, survivors, args, which_bits, bits,
                   sieve_list, &bp_list[0], &quit, process, info);
              if (quit) break;
            }
          }
      }
      else /* args->flags & RATPOINTS_USE_SQUARES1 */
      {
        GEN den_info = args->den_info;
        GEN divisors = args->divisors;
        long ld = lg(divisors);
        long k;
        long b, bb;
        long bp_list[args->sp2];

        for (k = 1; k < ld; k++)
        {
          long d = divisors[k];
          long last_b = d;
          long n;
          if (d > args->b_high) continue;
          for (n = 0; n < args->sp2; n++)
            bp_list[n] = mod(d, sieve_list[n]->p);

          for (b = 1; bb = d*b*b, bb <= args->b_high; b++)
          {
            if (bb >= args->b_low)
            {
              int flag = 1;
              ratpoints_bit_array bits = num_bits[bb & 0xf];

              if (EXT0(bits))
              {
                long i, n, l = lg(gel(den_info,1));
                long d = bb - last_b;

                /* fill bp_list */
                for (n = 0; n < args->sp2; n++)
                  bp_list[n] = mod(bp_list[n] + d, sieve_list[n]->p);
                last_b = bb;

                for(i = 1; i < l; i++)
                {
                  long v = z_lval(bb, mael(den_info,1,i));
                  if((v >= mael(den_info,3,i))
                      && odd(v + (mael(den_info,2,i)))) { flag = 0; break; }
                }
                if (flag)
                {
                  sift(bb, survivors, args, which_bits, bits,
                       sieve_list, &bp_list[0], &quit, process, info);
                  if (quit) break;
                }
              }
            }
          }
          if (quit) break;
        }
      }
    }
    else
    {
      if (args->flags & RATPOINTS_CHECK_DENOM)
      {
        long *forb;
        long b;
        long bp_list[args->sp2];
        long last_b = args->b_low;
        ulong b_bits;
        long n;
        for (n = 0; n < args->sp2; n++)
          bp_list[n] = mod(args->b_low, sieve_list[n]->p);
        {
          forbidden_entry *fba = &forb_ba[0];
          long b_low = args->b_low;
          long w_low = (b_low-1) >> TWOPOTBITS_IN_LONG;

          b_bits = den_bits;
          while (fba->p)
          {
            fba->curr = fba->start + mod(w_low, fba->p);
            b_bits &= *(fba->curr);
            fba++;
          }
          b_bits >>= (b_low-1) & LONG_MASK;
        }

        for (b = args->b_low; b <= args->b_high; b++)
        {
          ratpoints_bit_array bits = num_bits[b & 0xf];

          if ((b & LONG_MASK) == 0)
          { /* next b_bits */
            forbidden_entry *fba = &forb_ba[0];

            b_bits = den_bits;
            while (fba->p)
            {
              fba->curr++;
              if (fba->curr == fba->end) fba->curr = fba->start;
              b_bits &= *(fba->curr);
              fba++;
            }
          }
          else
            b_bits >>= 1;

          if (odd(b_bits) && EXT0(bits))
          { /* check if denominator is excluded */
            for (forb = &forbidden[0] ; *forb && (b % (*forb)); forb++)
              continue;
            if (*forb == 0 && rpjacobi(b, pel(c,degree)) == 1)
            {
              long n, d = b - last_b;

              /* fill bp_list */
              for (n = 0; n < args->sp2; n++)
              {
                long bp = bp_list[n] + d;
                long p = sieve_list[n]->p;

                while (bp >= p) bp -= p;
                bp_list[n] = bp;
              }
              last_b = b;

              sift(b, survivors, args, which_bits, bits,
                   sieve_list, &bp_list[0], &quit, process, info);
              if (quit) break;
            }
          }
        }
      } /* if (args->flags & RATPOINTS_CHECK_DENOM) */
      else
      {
        long b, n;
        long bp_list[args->sp2];
        long last_b = args->b_low;
        for (n = 0; n < args->sp2; n++)
          bp_list[n] = mod(args->b_low, sieve_list[n]->p);
        for (b = args->b_low; b <= args->b_high; b++)
        {
          ratpoints_bit_array bits = num_bits[b & 0xf];
          if (EXT0(bits))
          {
            long n;
            long d = b - last_b;

            /* fill bp_list */
            for (n = 0; n < args->sp2; n++)
            {
              long bp = bp_list[n] + d;
              long p = sieve_list[n]->p;

              while (bp >= p) bp -= p;
              bp_list[n] = bp;
            }
            last_b = b;

            sift(b, survivors, args, which_bits, bits,
                 sieve_list, &bp_list[0], &quit, process, info);
            if (quit) break;
          }
        }
      }
    }
  }
}

static GEN
vec_append_grow(GEN z, long i, GEN x)
{
  long n = lg(z)-1;
  if (i > n)
  {
    n <<= 1;
    z = vec_lengthen(z,n);
  }
  gel(z,i) = x;
  return z;
}

struct points
{
  GEN z;
  long i, f;
};

static int
process(long a, long b, GEN y, void *info0, int *quit)
{
  struct points *p = (struct points *) info0;
  if (b==0 && (p->f&2L)) return 0;
  *quit = (p->f&1);
  p->z = vec_append_grow(p->z, ++p->i, mkvec3(stoi(a),y,stoi(b)));
  return 1;
}

static GEN
ZX_hyperellratpoints(GEN P, GEN h, long flag)
{
  pari_sp av = avma;
  ratpoints_args args;
  struct points data;
  ulong flags = 0;

  if (!ZX_is_squarefree(P))
    pari_err_DOMAIN("hyperellratpoints","issquarefree(pol)","=",gen_0, P);
  if (typ(h)==t_INT && signe(h)>0)
  {
    long H = itos(h);
    args.height        = H;
    args.b_low         = 1;
    args.b_high        = H;
  } else if (typ(h)==t_VEC && lg(h)==3)
  {
    args.height        = gtos(gel(h,1));
    if (typ(gel(h,2))==t_INT)
    {
      args.b_low         = 1;
      args.b_high        = itos(gel(h,2));
    } else if (typ(gel(h,2))==t_VEC && lg(gel(h,2))==3)
    {
      args.b_low         = gtos(gmael(h,2,1));
      args.b_high        = gtos(gmael(h,2,2));
    } else pari_err_TYPE("hyperellratpoints",h);
  } else pari_err_TYPE("hyperellratpoints",h);

  find_points_init(&args, RATPOINTS_DEFAULT_BIT_PRIMES);

  args.cof           = shallowcopy(P);
  args.num_inter     = 0;
  args.sp1           = RATPOINTS_DEFAULT_SP1;
  args.sp2           = RATPOINTS_DEFAULT_SP2;
  args.array_size    = RATPOINTS_ARRAY_SIZE;
  args.num_primes    = RATPOINTS_DEFAULT_NUM_PRIMES;
  args.bit_primes    = RATPOINTS_DEFAULT_BIT_PRIMES;
  args.max_forbidden = RATPOINTS_DEFAULT_MAX_FORBIDDEN;
  args.flags         = flags;
  data.z = cgetg(17,t_VEC);
  data.i = 0;
  data.f = flag;
  find_points_work(&args, process, (void *)&data);

  setlg(data.z, data.i+1);
  return gerepilecopy(av, data.z);
}

static GEN
ZX_homogenous_evalpow(GEN Q, GEN A, GEN B)
{
  pari_sp av = avma;
  long i, d = degpol(Q);
  GEN s = gel(Q, d+2);
  for (i = d-1; i >= 0; i--)
    s = addii(mulii(s, A), mulii(gel(B,d+1-i), gel(Q,i+2)));
  return gerepileuptoint(av, s);
}

static GEN
to_ZX(GEN a, long v) { return typ(a)==t_INT? scalarpol(a,v): a; }

static int
hyperell_check(GEN PQ, GEN *P, GEN *Q)
{
  *P = *Q = NULL;
  if (typ(PQ) == t_POL)
  {
    if (!RgX_is_ZX(PQ)) return 0;
    *P = PQ;
  }
  else
  {
    long v = gvar(PQ);
    if (v == NO_VARIABLE || typ(PQ) != t_VEC || lg(PQ) != 3) return 0;
    *P = to_ZX(gel(PQ,1), v); if (!RgX_is_ZX(*P)) return 0;
    *Q = to_ZX(gel(PQ,2), v); if (!RgX_is_ZX(*Q)) return 0;
    if (!signe(*Q)) *Q = NULL;
  }
  return 1;
}

GEN
hyperellratpoints(GEN PQ, GEN h, long flag)
{
  pari_sp av = avma;
  GEN P, Q, H, L;
  long i, l, dy, dQ;

  if (flag<0 || flag>1) pari_err_FLAG("ellratpoints");
  if (!hyperell_check(PQ, &P, &Q)) pari_err_TYPE("hyperellratpoints",PQ);
  if (!Q)
  {
    L = ZX_hyperellratpoints(P, h, flag|2L);
    dy = (degpol(P)+1)>>1;
    l = lg(L);
    for (i = 1; i < l; i++)
    {
      GEN Li = gel(L,i), x = gel(Li,1), y = gel(Li,2), z = gel(Li,3);
      gel(L,i) = mkvec2(gdiv(x,z), gdiv(y, powiu(z, dy)));
    }
    return gerepilecopy(av, L);
  }
  H = ZX_add(ZX_shifti(P,2), ZX_sqr(Q));
  dy = (degpol(H)+1)>>1; dQ = degpol(Q);
  L = ZX_hyperellratpoints(H, h, flag|2L);
  l = lg(L);
  for (i = 1; i < l; i++)
  {
    GEN Li = gel(L,i), x = gel(Li,1), y = gel(Li,2), z = gel(Li,3);
    GEN B = gpowers(z, dQ);
    GEN Qx = gdiv(ZX_homogenous_evalpow(Q, x, B), gel(B, dQ+1));
    gel(L,i) = mkvec2(gdiv(x,z), gmul2n(gsub(gdiv(y,powiu(z, dy)),Qx),-1));
  }
  return gerepilecopy(av, L);
}

GEN
ellratpoints(GEN E, GEN h, long flag)
{
  pari_sp av = avma;
  GEN L, a1, a3;
  long i, l;
  checkell_Q(E);
  if (flag<0 || flag>1) pari_err_FLAG("ellratpoints");
  if (!RgV_is_ZV(vecslice(E,1,5))) pari_err_TYPE("ellratpoints",E);
  a1 = ell_get_a1(E);
  a3 = ell_get_a3(E);
  L = ZX_hyperellratpoints(ec_bmodel(E), h, flag|2L);
  l = lg(L);
  for (i = 1; i < l; i++)
  {
    GEN P, Li = gel(L,i), x = gel(Li,1), y = gel(Li,2), z = gel(Li,3);
    if (!signe(z))
      P = ellinf();
    else
    {
      GEN z2 = sqri(z);
      y = subii(y, addii(mulii(a1, mulii(x,z)), mulii(a3,z2)));
      P = mkvec2(gdiv(x,z), gdiv(y,shifti(z2,1)));
    }
    gel(L,i) = P;
  }
  return gerepilecopy(av, L);
}
