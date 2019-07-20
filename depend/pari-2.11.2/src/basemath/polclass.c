/* Copyright (C) 2014  The PARI group.

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

#define dbg_printf(lvl) if (DEBUGLEVEL >= (lvl) + 3) err_printf

/*
 * SECTION: Functions dedicated to finding a j-invariant with a given
 * trace.
 */

/* TODO: This code is shared with
 * torsion_compatible_with_characteristic() in 'torsion.c'. */
static void
hasse_bounds(long *low, long *high, long p)
{
  long two_sqrt_p = usqrt(4*p);
  *low = p + 1 - two_sqrt_p;
  *high = p + 1 + two_sqrt_p;
}

/* a / b : a and b are from factoru and b must divide a exactly */
INLINE GEN
famatsmall_divexact(GEN a, GEN b)
{
  GEN a1 = gel(a,1), a2 = gel(a,2), c1, c2;
  GEN b1 = gel(b,1), b2 = gel(b,2);
  long i, j, k, la = lg(a1);
  c1 = cgetg(la, t_VECSMALL);
  c2 = cgetg(la, t_VECSMALL);
  for (i = j = k = 1; j < la; j++)
  {
    c1[k] = a1[j];
    c2[k] = a2[j];
    if (a1[j] == b1[i]) { c2[k] -= b2[i++]; if (!c2[k]) continue; }
    k++;
  }
  setlg(c1, k);
  setlg(c2, k); return mkvec2(c1,c2);
}

/* This is Sutherland, 2009, TestCurveOrder.
 *
 * [a4, a6] and p specify an elliptic curve over FF_p.  N0,N1 are the two
 * possible curve orders, and n0,n1 their factoru */
static long
test_curve_order(norm_eqn_t ne, ulong a4, ulong a6,
  long N0, long N1, GEN n0, GEN n1, const long hasse[2])
{
  pari_sp ltop = avma, av;
  ulong a4t, a6t, p = ne->p, pi = ne->pi, T = ne->T, swapped = 0;
  long m0, m1, hasse_low, hasse_high;

  if (p <= 11) {
    long card = (long)p + 1 - Fl_elltrace(a4, a6, p);
    return card == N0 || card == N1;
  }
  /* [a4, a6] is the given curve and [a4t, a6t] is its quadratic twist */
  Fl_elltwist_disc(a4, a6, T, p, &a4t, &a6t);

  m0 = m1 = 1;
  if (N0 + N1 != 2 * (long)p + 2) pari_err_BUG("test_curve_order");

  hasse_low = hasse[0];
  hasse_high = hasse[1];
  for (av = avma;;)
  {
    GEN pt, Q, fa0;
    long a1, x, n_s;

    pt = random_Flj_pre(a4, a6, p, pi);
    Q = Flj_mulu_pre(pt, m0, a4, p, pi);
    fa0 = m0 == 1? n0: famatsmall_divexact(n0, factoru(m0));
    n_s = Flj_order_ufact(Q, N0 / m0, fa0, a4, p, pi);
    if (n_s == 0) {
      /* If m0 divides N1 and m1 divides N0 and N0 < N1, then swap */
      if (!swapped && N1 % m0 == 0 && N0 % m1 == 0) {
        swapspec(n0, n1, N0, N1);
        swapped = 1; continue;
      }
      avma = ltop; return 0;
    }

    m0 *= n_s;
    a1 = (2 * p + 2) % m1;
    x = (hasse_low + m0 - 1) / m0; /* using ceil(n/d) = (n + d - 1)/d */
    x *= m0;
    for ( ; x <= hasse_high; x += m0)
      if ((x % m1) == a1 && x != N0 && x != N1) break;
    /* every x in N was either N0 or N1, so we return true */
    if (x > hasse_high) { avma = ltop; return 1; }

    lswap(a4, a4t);
    lswap(a6, a6t);
    lswap(m0, m1); avma = av;
  }
}

static GEN
random_FleV(GEN x, GEN a6, ulong p, ulong pi)
{ pari_APPLY_type(t_VEC, random_Fle_pre(uel(x,i), uel(a6,i), p, pi)) }

/**
 * START Code from AVSs "torcosts.h"
 */

struct torctab_rec {
  int m;
  int fix2, fix3;
  int N;
  int s2_flag;
  int t3_flag;
  double rating;
};

/*
  These costs assume p=2 mod 3, 3 mod 4 and not 1 mod N
*/

static struct torctab_rec torctab1[] = {
{ 11, 1, 1, 11, 1, 1, 0.047250 },
{ 33, 1, 0, 11, 1, 2, 0.047250 },
{ 22, 1, 1, 11, 3, 1, 0.055125 },
{ 66, 1, 0, 11, 3, 2, 0.055125 },
{ 11, 1, 0, 11, 1, 0, 0.058000 },
{ 13, 1, 1, 13, 1, 1, 0.058542 },
{ 39, 1, 0, 13, 1, 2, 0.058542 },
{ 22, 0, 1, 11, 2, 1, 0.061333 },
{ 66, 0, 0, 11, 2, 2, 0.061333 },
{ 22, 1, 0, 11, 3, 0, 0.061750 },
{ 14, 1, 1, 14, 3, 1, 0.062500 },
{ 42, 1, 0, 14, 3, 2, 0.062500 },
{ 26, 1, 1, 13, 3, 1, 0.064583 },
{ 78, 1, 0, 13, 3, 2, 0.064583 },
{ 28, 0, 1, 14, 4, 1, 0.065625 },
{ 84, 0, 0, 14, 4, 2, 0.065625 },
{ 7, 1, 1, 7, 1, 1, 0.068750 },
{ 13, 1, 0, 13, 1, 0, 0.068750 },
{ 21, 1, 0, 7, 1, 2, 0.068750 },
{ 26, 1, 0, 13, 3, 0, 0.069583 },
{ 17, 1, 1, 17, 1, 1, 0.069687 },
{ 51, 1, 0, 17, 1, 2, 0.069687 },
{ 11, 0, 1, 11, 0, 1, 0.072500 },
{ 33, 0, 0, 11, 0, 2, 0.072500 },
{ 44, 1, 0, 11, 130, 0, 0.072667 },
{ 52, 0, 1, 13, 4, 1, 0.073958 },
{ 156, 0, 0, 13, 4, 2, 0.073958 },
{ 34, 1, 1, 17, 3, 1, 0.075313 },
{ 102, 1, 0, 17, 3, 2, 0.075313 },
{ 15, 1, 0, 15, 1, 0, 0.075625 },
{ 13, 0, 1, 13, 0, 1, 0.076667 },
{ 39, 0, 0, 13, 0, 2, 0.076667 },
{ 44, 0, 0, 11, 4, 0, 0.076667 },
{ 30, 1, 0, 15, 3, 0, 0.077188 },
{ 22, 0, 0, 11, 2, 0, 0.077333 },
{ 34, 1, 0, 17, 3, 0, 0.077969 },
{ 17, 1, 0, 17, 1, 0, 0.078750 },
{ 14, 0, 1, 14, 0, 1, 0.080556 },
{ 28, 0, 0, 14, 4, 0, 0.080556 },
{ 42, 0, 0, 14, 0, 2, 0.080556 },
{ 7, 1, 0, 7, 1, 0, 0.080833 },
{ 9, 1, 0, 9, 1, 0, 0.080833 },
{ 68, 0, 1, 17, 4, 1, 0.081380 },
{ 204, 0, 0, 17, 4, 2, 0.081380 },
{ 52, 0, 0, 13, 4, 0, 0.082292 },
{ 10, 1, 1, 10, 3, 1, 0.084687 },
{ 17, 0, 1, 17, 0, 1, 0.084687 },
{ 51, 0, 0, 17, 0, 2, 0.084687 },
{ 20, 0, 1, 10, 4, 1, 0.085938 },
{ 60, 0, 0, 10, 4, 2, 0.085938 },
{ 19, 1, 1, 19, 1, 1, 0.086111 },
{ 57, 1, 0, 19, 1, 2, 0.086111 },
{ 68, 0, 0, 17, 4, 0, 0.088281 },
{ 38, 1, 1, 19, 3, 1, 0.089514 },
{ 114, 1, 0, 19, 3, 2, 0.089514 },
{ 20, 0, 0, 10, 4, 0, 0.090625 },
{ 36, 0, 0, 18, 4, 0, 0.090972 },
{ 26, 0, 0, 13, 2, 0, 0.091667 },
{ 11, 0, 0, 11, 0, 0, 0.092000 },
{ 19, 1, 0, 19, 1, 0, 0.092778 },
{ 38, 1, 0, 19, 3, 0, 0.092778 },
{ 14, 1, 0, 7, 3, 0, 0.092917 },
{ 18, 1, 0, 9, 3, 0, 0.092917 },
{ 76, 0, 1, 19, 4, 1, 0.095255 },
{ 228, 0, 0, 19, 4, 2, 0.095255 },
{ 10, 0, 1, 10, 0, 1, 0.096667 },
{ 13, 0, 0, 13, 0, 0, 0.096667 },
{ 30, 0, 0, 10, 0, 2, 0.096667 },
{ 19, 0, 1, 19, 0, 1, 0.098333 },
{ 57, 0, 0, 19, 0, 2, 0.098333 },
{ 17, 0, 0, 17, 0, 0, 0.100000 },
{ 23, 1, 1, 23, 1, 1, 0.100227 },
{ 69, 1, 0, 23, 1, 2, 0.100227 },
{ 7, 0, 1, 7, 0, 1, 0.100833 },
{ 21, 0, 0, 7, 0, 2, 0.100833 },
{ 76, 0, 0, 19, 4, 0, 0.102083 },
{ 14, 0, 0, 14, 0, 0, 0.102222 },
{ 18, 0, 0, 9, 2, 0, 0.102222 },
{ 5, 1, 1, 5, 1, 1, 0.103125 },
{ 46, 1, 1, 23, 3, 1, 0.104318 },
{ 138, 1, 0, 23, 3, 2, 0.104318 },
{ 23, 1, 0, 23, 1, 0, 0.105682 },
{ 46, 1, 0, 23, 3, 0, 0.106705 },
{ 92, 0, 1, 23, 4, 1, 0.109091 },
{ 276, 0, 0, 23, 4, 2, 0.109091 },
{ 19, 0, 0, 19, 0, 0, 0.110000 },
{ 23, 0, 1, 23, 0, 1, 0.112273 },
{ 69, 0, 0, 23, 0, 2, 0.112273 },
{ 7, 0, 0, 7, 0, 0, 0.113333 },
{ 9, 0, 0, 9, 0, 0, 0.113333 },
{ 92, 0, 0, 23, 4, 0, 0.113826 },
{ 16, 0, 1, 16, 0, 1, 0.118125 },
{ 48, 0, 0, 16, 0, 2, 0.118125 },
{ 5, 1, 0, 5, 1, 0, 0.121250 },
{ 15, 0, 0, 15, 0, 0, 0.121250 },
{ 10, 0, 0, 10, 0, 0, 0.121667 },
{ 23, 0, 0, 23, 0, 0, 0.123182 },
{ 12, 0, 0, 12, 0, 0, 0.141667 },
{ 5, 0, 1, 5, 0, 1, 0.145000 },
{ 16, 0, 0, 16, 0, 0, 0.145000 },
{ 8, 0, 1, 8, 0, 1, 0.151250 },
{ 29, 1, 1, 29, 1, 1, 0.153036 },
{ 87, 1, 0, 29, 1, 2, 0.153036 },
{ 25, 0, 0, 25, 0, 0, 0.155000 },
{ 58, 1, 1, 29, 3, 1, 0.156116 },
{ 174, 1, 0, 29, 3, 2, 0.156116 },
{ 29, 1, 0, 29, 1, 0, 0.157500 },
{ 58, 1, 0, 29, 3, 0, 0.157500 },
{ 116, 0, 1, 29, 4, 1, 0.161086 },
{ 29, 0, 1, 29, 0, 1, 0.163393 },
{ 87, 0, 0, 29, 0, 2, 0.163393 },
{ 116, 0, 0, 29, 4, 0, 0.163690 },
{ 5, 0, 0, 5, 0, 0, 0.170000 },
{ 8, 0, 0, 8, 0, 0, 0.170000 },
{ 29, 0, 0, 29, 0, 0, 0.171071 },
{ 31, 1, 1, 31, 1, 1, 0.186583 },
{ 93, 1, 0, 31, 1, 2, 0.186583 },
{ 62, 1, 1, 31, 3, 1, 0.189750 },
{ 186, 1, 0, 31, 3, 2, 0.189750 },
{ 31, 1, 0, 31, 1, 0, 0.191333 },
{ 62, 1, 0, 31, 3, 0, 0.192167 },
{ 124, 0, 1, 31, 4, 1, 0.193056 },
{ 31, 0, 1, 31, 0, 1, 0.195333 },
{ 93, 0, 0, 31, 0, 2, 0.195333 },
{ 124, 0, 0, 31, 4, 0, 0.197917 },
{ 2, 1, 1, 2, 3, 1, 0.200000 },
{ 6, 1, 0, 2, 3, 2, 0.200000 },
{ 31, 0, 0, 31, 0, 0, 0.206667 },
{ 4, 1, 1, 4, 130, 1, 0.214167 },
{ 6, 0, 0, 6, 0, 0, 0.226667 },
{ 3, 1, 0, 3, 1, 0, 0.230000 },
{ 4, 0, 1, 4, 0, 1, 0.241667 },
{ 4, 1, 0, 2, 130, 0, 0.266667 },
{ 4, 0, 0, 4, 0, 0, 0.283333 },
{ 3, 0, 0, 3, 0, 0, 0.340000 },
{ 1, 1, 1, 1, 1, 1, 0.362500 },
{ 2, 0, 1, 2, 0, 1, 0.386667 },
{ 1, 1, 0, 1, 1, 0, 0.410000 },
{ 2, 0, 0, 2, 0, 0, 0.453333 },
};

static struct torctab_rec torctab2[] = {
{ 11, 1, 1, 11, 1, 1, 0.047250 },
{ 33, 1, 0, 11, 1, 2, 0.047250 },
{ 22, 1, 1, 11, 3, 1, 0.055125 },
{ 66, 1, 0, 11, 3, 2, 0.055125 },
{ 13, 1, 1, 13, 1, 1, 0.057500 },
{ 39, 1, 0, 13, 1, 2, 0.057500 },
{ 11, 1, 0, 11, 1, 0, 0.058000 },
{ 22, 0, 1, 11, 2, 1, 0.061333 },
{ 66, 0, 0, 11, 2, 2, 0.061333 },
{ 14, 1, 1, 14, 3, 1, 0.061458 },
{ 42, 1, 0, 14, 3, 2, 0.061458 },
{ 22, 1, 0, 11, 3, 0, 0.061750 },
{ 26, 1, 1, 13, 3, 1, 0.064062 },
{ 78, 1, 0, 13, 3, 2, 0.064062 },
{ 28, 0, 1, 14, 4, 1, 0.065625 },
{ 84, 0, 0, 14, 4, 2, 0.065625 },
{ 13, 1, 0, 13, 1, 0, 0.066667 },
{ 26, 1, 0, 13, 3, 0, 0.069583 },
{ 17, 1, 1, 17, 1, 1, 0.069687 },
{ 51, 1, 0, 17, 1, 2, 0.069687 },
{ 11, 0, 1, 11, 0, 1, 0.070000 },
{ 33, 0, 0, 11, 0, 2, 0.070000 },
{ 7, 1, 1, 7, 1, 1, 0.070417 },
{ 21, 1, 0, 7, 1, 2, 0.070417 },
{ 15, 1, 0, 15, 1, 0, 0.072500 },
{ 52, 0, 1, 13, 4, 1, 0.073090 },
{ 156, 0, 0, 13, 4, 2, 0.073090 },
{ 34, 1, 1, 17, 3, 1, 0.074219 },
{ 102, 1, 0, 17, 3, 2, 0.074219 },
{ 7, 1, 0, 7, 1, 0, 0.076667 },
{ 13, 0, 1, 13, 0, 1, 0.076667 },
{ 39, 0, 0, 13, 0, 2, 0.076667 },
{ 44, 0, 0, 11, 4, 0, 0.076667 },
{ 17, 1, 0, 17, 1, 0, 0.077188 },
{ 22, 0, 0, 11, 2, 0, 0.077333 },
{ 34, 1, 0, 17, 3, 0, 0.077969 },
{ 30, 1, 0, 15, 3, 0, 0.080312 },
{ 14, 0, 1, 14, 0, 1, 0.080556 },
{ 28, 0, 0, 14, 4, 0, 0.080556 },
{ 42, 0, 0, 14, 0, 2, 0.080556 },
{ 9, 1, 0, 9, 1, 0, 0.080833 },
{ 68, 0, 1, 17, 4, 1, 0.081380 },
{ 204, 0, 0, 17, 4, 2, 0.081380 },
{ 52, 0, 0, 13, 4, 0, 0.082292 },
{ 10, 1, 1, 10, 3, 1, 0.083125 },
{ 20, 0, 1, 10, 4, 1, 0.083333 },
{ 60, 0, 0, 10, 4, 2, 0.083333 },
{ 17, 0, 1, 17, 0, 1, 0.084687 },
{ 51, 0, 0, 17, 0, 2, 0.084687 },
{ 19, 1, 1, 19, 1, 1, 0.084722 },
{ 57, 1, 0, 19, 1, 2, 0.084722 },
{ 11, 0, 0, 11, 0, 0, 0.087000 },
{ 68, 0, 0, 17, 4, 0, 0.088281 },
{ 38, 1, 1, 19, 3, 1, 0.090139 },
{ 114, 1, 0, 19, 3, 2, 0.090139 },
{ 36, 0, 0, 18, 4, 0, 0.090972 },
{ 19, 1, 0, 19, 1, 0, 0.091389 },
{ 26, 0, 0, 13, 2, 0, 0.091667 },
{ 13, 0, 0, 13, 0, 0, 0.092500 },
{ 38, 1, 0, 19, 3, 0, 0.092778 },
{ 14, 1, 0, 7, 3, 0, 0.092917 },
{ 18, 1, 0, 9, 3, 0, 0.092917 },
{ 20, 0, 0, 10, 4, 0, 0.095833 },
{ 76, 0, 1, 19, 4, 1, 0.096412 },
{ 228, 0, 0, 19, 4, 2, 0.096412 },
{ 17, 0, 0, 17, 0, 0, 0.096875 },
{ 19, 0, 1, 19, 0, 1, 0.098056 },
{ 57, 0, 0, 19, 0, 2, 0.098056 },
{ 23, 1, 1, 23, 1, 1, 0.100682 },
{ 69, 1, 0, 23, 1, 2, 0.100682 },
{ 7, 0, 1, 7, 0, 1, 0.100833 },
{ 21, 0, 0, 7, 0, 2, 0.100833 },
{ 30, 0, 0, 15, 2, 0, 0.100833 },
{ 76, 0, 0, 19, 4, 0, 0.102083 },
{ 14, 0, 0, 14, 0, 0, 0.102222 },
{ 5, 1, 1, 5, 1, 1, 0.103125 },
{ 46, 1, 1, 23, 3, 1, 0.104034 },
{ 138, 1, 0, 23, 3, 2, 0.104034 },
{ 23, 1, 0, 23, 1, 0, 0.104545 },
{ 7, 0, 0, 7, 0, 0, 0.105000 },
{ 10, 0, 1, 10, 0, 1, 0.105000 },
{ 16, 0, 1, 16, 0, 1, 0.105417 },
{ 48, 0, 0, 16, 0, 2, 0.105417 },
{ 46, 1, 0, 23, 3, 0, 0.106705 },
{ 18, 0, 0, 9, 2, 0, 0.107778 },
{ 92, 0, 1, 23, 4, 1, 0.108239 },
{ 276, 0, 0, 23, 4, 2, 0.108239 },
{ 19, 0, 0, 19, 0, 0, 0.110000 },
{ 23, 0, 1, 23, 0, 1, 0.111136 },
{ 69, 0, 0, 23, 0, 2, 0.111136 },
{ 9, 0, 0, 9, 0, 0, 0.113333 },
{ 10, 0, 0, 10, 0, 0, 0.113333 },
{ 92, 0, 0, 23, 4, 0, 0.113826 },
{ 5, 1, 0, 5, 1, 0, 0.115000 },
{ 15, 0, 0, 15, 0, 0, 0.115000 },
{ 23, 0, 0, 23, 0, 0, 0.120909 },
{ 8, 0, 1, 8, 0, 1, 0.126042 },
{ 24, 0, 0, 8, 0, 2, 0.126042 },
{ 16, 0, 0, 16, 0, 0, 0.127188 },
{ 8, 0, 0, 8, 0, 0, 0.141667 },
{ 25, 0, 1, 25, 0, 1, 0.144000 },
{ 5, 0, 1, 5, 0, 1, 0.151250 },
{ 12, 0, 0, 12, 0, 0, 0.152083 },
{ 29, 1, 1, 29, 1, 1, 0.153929 },
{ 87, 1, 0, 29, 1, 2, 0.153929 },
{ 25, 0, 0, 25, 0, 0, 0.155000 },
{ 58, 1, 1, 29, 3, 1, 0.155045 },
{ 174, 1, 0, 29, 3, 2, 0.155045 },
{ 29, 1, 0, 29, 1, 0, 0.156429 },
{ 58, 1, 0, 29, 3, 0, 0.157857 },
{ 116, 0, 1, 29, 4, 1, 0.158631 },
{ 116, 0, 0, 29, 4, 0, 0.163542 },
{ 29, 0, 1, 29, 0, 1, 0.164286 },
{ 87, 0, 0, 29, 0, 2, 0.164286 },
{ 29, 0, 0, 29, 0, 0, 0.169286 },
{ 5, 0, 0, 5, 0, 0, 0.170000 },
{ 31, 1, 1, 31, 1, 1, 0.187000 },
{ 93, 1, 0, 31, 1, 2, 0.187000 },
{ 62, 1, 1, 31, 3, 1, 0.188500 },
{ 186, 1, 0, 31, 3, 2, 0.188500 },
{ 31, 1, 0, 31, 1, 0, 0.191333 },
{ 62, 1, 0, 31, 3, 0, 0.192083 },
{ 124, 0, 1, 31, 4, 1, 0.193472 },
{ 31, 0, 1, 31, 0, 1, 0.196167 },
{ 93, 0, 0, 31, 0, 2, 0.196167 },
{ 124, 0, 0, 31, 4, 0, 0.197083 },
{ 2, 1, 1, 2, 3, 1, 0.200000 },
{ 6, 1, 0, 2, 3, 2, 0.200000 },
{ 31, 0, 0, 31, 0, 0, 0.205000 },
{ 6, 0, 0, 6, 0, 0, 0.226667 },
{ 3, 1, 0, 3, 1, 0, 0.230000 },
{ 4, 0, 1, 4, 0, 1, 0.241667 },
{ 4, 0, 0, 4, 0, 0, 0.283333 },
{ 3, 0, 0, 3, 0, 0, 0.340000 },
{ 1, 1, 1, 1, 1, 1, 0.362500 },
{ 2, 0, 1, 2, 0, 1, 0.370000 },
{ 1, 1, 0, 1, 1, 0, 0.385000 },
{ 2, 0, 0, 2, 0, 0, 0.453333 },
};

static struct torctab_rec torctab3[] = {
{ 66, 1, 0, 11, 3, 2, 0.040406 },
{ 33, 1, 0, 11, 1, 2, 0.043688 },
{ 78, 1, 0, 13, 3, 2, 0.045391 },
{ 132, 1, 0, 11, 130, 2, 0.046938 },
{ 39, 1, 0, 13, 1, 2, 0.047656 },
{ 102, 1, 0, 17, 3, 2, 0.049922 },
{ 42, 1, 0, 14, 3, 2, 0.050000 },
{ 51, 1, 0, 17, 1, 2, 0.051680 },
{ 132, 0, 0, 11, 4, 2, 0.052188 },
{ 156, 1, 0, 13, 130, 2, 0.053958 },
{ 156, 0, 0, 13, 4, 2, 0.054818 },
{ 84, 1, 0, 14, 130, 2, 0.055000 },
{ 15, 1, 0, 15, 1, 0, 0.056719 },
{ 204, 0, 0, 17, 4, 2, 0.057227 },
{ 114, 1, 0, 19, 3, 2, 0.057500 },
{ 11, 1, 0, 11, 1, 0, 0.058000 },
{ 66, 0, 0, 11, 2, 2, 0.058000 },
{ 57, 1, 0, 19, 1, 2, 0.059062 },
{ 30, 1, 0, 15, 3, 0, 0.059063 },
{ 84, 0, 0, 14, 4, 2, 0.060677 },
{ 22, 1, 0, 11, 3, 0, 0.061750 },
{ 78, 0, 0, 13, 2, 2, 0.063542 },
{ 228, 0, 0, 19, 4, 2, 0.063889 },
{ 21, 1, 0, 7, 1, 2, 0.065000 },
{ 138, 1, 0, 23, 3, 2, 0.065028 },
{ 69, 1, 0, 23, 1, 2, 0.066903 },
{ 13, 1, 0, 13, 1, 0, 0.068750 },
{ 102, 0, 0, 17, 2, 2, 0.068906 },
{ 26, 1, 0, 13, 3, 0, 0.069583 },
{ 51, 0, 0, 17, 0, 2, 0.070312 },
{ 60, 1, 0, 15, 130, 0, 0.071094 },
{ 276, 0, 0, 23, 4, 2, 0.071236 },
{ 39, 0, 0, 13, 0, 2, 0.071250 },
{ 33, 0, 0, 11, 0, 2, 0.072750 },
{ 44, 1, 0, 11, 130, 0, 0.073500 },
{ 60, 0, 0, 15, 4, 0, 0.073828 },
{ 9, 1, 0, 9, 1, 0, 0.074097 },
{ 30, 0, 0, 15, 2, 0, 0.075625 },
{ 57, 0, 0, 19, 0, 2, 0.075625 },
{ 7, 1, 0, 7, 1, 0, 0.076667 },
{ 44, 0, 0, 11, 4, 0, 0.076667 },
{ 22, 0, 0, 11, 2, 0, 0.077333 },
{ 17, 1, 0, 17, 1, 0, 0.078750 },
{ 34, 1, 0, 17, 3, 0, 0.078750 },
{ 69, 0, 0, 23, 0, 2, 0.079943 },
{ 28, 0, 0, 14, 4, 0, 0.080556 },
{ 42, 0, 0, 14, 0, 2, 0.080833 },
{ 52, 0, 0, 13, 4, 0, 0.082292 },
{ 14, 1, 1, 14, 3, 1, 0.083333 },
{ 36, 0, 0, 18, 4, 0, 0.083391 },
{ 18, 1, 0, 9, 3, 0, 0.085174 },
{ 68, 0, 0, 17, 4, 0, 0.089583 },
{ 15, 0, 0, 15, 0, 0, 0.090938 },
{ 19, 1, 0, 19, 1, 0, 0.091389 },
{ 26, 0, 0, 13, 2, 0, 0.091667 },
{ 11, 0, 0, 11, 0, 0, 0.092000 },
{ 13, 0, 0, 13, 0, 0, 0.092500 },
{ 38, 1, 0, 19, 3, 0, 0.092778 },
{ 14, 1, 0, 7, 3, 0, 0.092917 },
{ 18, 0, 0, 9, 2, 0, 0.093704 },
{ 174, 1, 0, 29, 3, 2, 0.095826 },
{ 20, 0, 0, 10, 4, 0, 0.095833 },
{ 96, 1, 0, 16, 133, 2, 0.096562 },
{ 21, 0, 0, 21, 0, 0, 0.096875 },
{ 87, 1, 0, 29, 1, 2, 0.096964 },
{ 17, 0, 0, 17, 0, 0, 0.100000 },
{ 348, 0, 0, 29, 4, 2, 0.100558 },
{ 76, 0, 0, 19, 4, 0, 0.100926 },
{ 14, 0, 0, 14, 0, 0, 0.102222 },
{ 9, 0, 0, 9, 0, 0, 0.103889 },
{ 46, 1, 0, 23, 3, 0, 0.105114 },
{ 23, 1, 0, 23, 1, 0, 0.105682 },
{ 48, 0, 0, 16, 0, 2, 0.106406 },
{ 87, 0, 0, 29, 0, 2, 0.107545 },
{ 19, 0, 0, 19, 0, 0, 0.107778 },
{ 7, 0, 0, 7, 0, 0, 0.113333 },
{ 10, 0, 0, 10, 0, 0, 0.113333 },
{ 92, 0, 0, 23, 4, 0, 0.113636 },
{ 12, 0, 0, 12, 0, 0, 0.114062 },
{ 5, 1, 0, 5, 1, 0, 0.115000 },
{ 186, 1, 0, 31, 3, 2, 0.115344 },
{ 93, 1, 0, 31, 1, 2, 0.118125 },
{ 23, 0, 0, 23, 0, 0, 0.120909 },
{ 93, 0, 0, 31, 0, 2, 0.128250 },
{ 16, 0, 0, 16, 0, 0, 0.138750 },
{ 25, 0, 0, 25, 0, 0, 0.155000 },
{ 58, 1, 0, 29, 3, 0, 0.155714 },
{ 29, 1, 0, 29, 1, 0, 0.158214 },
{ 3, 1, 0, 3, 1, 0, 0.163125 },
{ 116, 0, 0, 29, 4, 0, 0.163690 },
{ 5, 0, 0, 5, 0, 0, 0.170000 },
{ 6, 0, 0, 6, 0, 0, 0.170000 },
{ 8, 0, 0, 8, 0, 0, 0.170000 },
{ 29, 0, 0, 29, 0, 0, 0.172857 },
{ 31, 1, 0, 31, 1, 0, 0.191333 },
{ 62, 1, 0, 31, 3, 0, 0.191750 },
{ 124, 0, 0, 31, 4, 0, 0.197917 },
{ 31, 0, 0, 31, 0, 0, 0.201667 },
{ 3, 0, 0, 3, 0, 0, 0.236250 },
{ 4, 0, 0, 4, 0, 0, 0.262500 },
{ 2, 1, 1, 2, 3, 1, 0.317187 },
{ 1, 1, 0, 1, 1, 0, 0.410000 },
{ 2, 0, 0, 2, 0, 0, 0.453333 },
};

static struct torctab_rec torctab4[] = {
{ 66, 1, 0, 11, 3, 2, 0.041344 },
{ 33, 1, 0, 11, 1, 2, 0.042750 },
{ 78, 1, 0, 13, 3, 2, 0.045781 },
{ 39, 1, 0, 13, 1, 2, 0.046875 },
{ 264, 1, 0, 11, 131, 2, 0.049043 },
{ 42, 1, 0, 14, 3, 2, 0.050000 },
{ 102, 1, 0, 17, 3, 2, 0.050508 },
{ 51, 1, 0, 17, 1, 2, 0.051094 },
{ 528, 1, 0, 11, 132, 2, 0.052891 },
{ 132, 0, 0, 11, 4, 2, 0.052969 },
{ 168, 1, 0, 14, 131, 2, 0.053965 },
{ 156, 0, 0, 13, 4, 2, 0.054948 },
{ 336, 1, 0, 14, 132, 2, 0.056120 },
{ 15, 1, 0, 15, 1, 0, 0.056719 },
{ 66, 0, 0, 11, 2, 2, 0.057000 },
{ 114, 1, 0, 19, 3, 2, 0.057812 },
{ 11, 1, 0, 11, 1, 0, 0.058000 },
{ 204, 0, 0, 17, 4, 2, 0.058203 },
{ 57, 1, 0, 19, 1, 2, 0.058542 },
{ 84, 0, 0, 14, 4, 2, 0.059375 },
{ 30, 1, 0, 15, 3, 0, 0.061406 },
{ 22, 1, 0, 11, 3, 0, 0.063000 },
{ 78, 0, 0, 13, 2, 2, 0.063542 },
{ 138, 1, 0, 23, 3, 2, 0.064815 },
{ 21, 1, 0, 7, 1, 2, 0.065000 },
{ 228, 0, 0, 19, 4, 2, 0.065104 },
{ 69, 1, 0, 23, 1, 2, 0.066477 },
{ 13, 1, 0, 13, 1, 0, 0.068750 },
{ 102, 0, 0, 17, 2, 2, 0.068906 },
{ 51, 0, 0, 17, 0, 2, 0.069141 },
{ 26, 1, 0, 13, 3, 0, 0.070625 },
{ 276, 0, 0, 23, 4, 2, 0.071236 },
{ 39, 0, 0, 13, 0, 2, 0.071250 },
{ 33, 0, 0, 11, 0, 2, 0.072750 },
{ 60, 0, 0, 15, 4, 0, 0.073828 },
{ 9, 1, 0, 9, 1, 0, 0.074097 },
{ 57, 0, 0, 19, 0, 2, 0.074583 },
{ 30, 0, 0, 15, 2, 0, 0.075625 },
{ 44, 0, 0, 11, 4, 0, 0.076667 },
{ 17, 1, 0, 17, 1, 0, 0.077188 },
{ 22, 0, 0, 11, 2, 0, 0.077333 },
{ 69, 0, 0, 23, 0, 2, 0.080114 },
{ 36, 0, 0, 18, 4, 0, 0.080208 },
{ 34, 1, 0, 17, 3, 0, 0.080312 },
{ 28, 0, 0, 14, 4, 0, 0.080556 },
{ 7, 1, 0, 7, 1, 0, 0.080833 },
{ 52, 0, 0, 13, 4, 0, 0.082292 },
{ 42, 0, 0, 14, 0, 2, 0.082500 },
{ 14, 1, 1, 14, 3, 1, 0.083333 },
{ 15, 0, 0, 15, 0, 0, 0.086250 },
{ 18, 1, 0, 9, 3, 0, 0.087083 },
{ 26, 0, 0, 13, 2, 0, 0.088889 },
{ 68, 0, 0, 17, 4, 0, 0.089583 },
{ 48, 1, 0, 16, 132, 2, 0.089844 },
{ 19, 1, 0, 19, 1, 0, 0.091389 },
{ 11, 0, 0, 11, 0, 0, 0.092000 },
{ 38, 1, 0, 19, 3, 0, 0.092917 },
{ 18, 0, 0, 9, 2, 0, 0.093704 },
{ 14, 1, 0, 7, 3, 0, 0.095000 },
{ 96, 1, 0, 16, 133, 2, 0.095391 },
{ 20, 0, 0, 10, 4, 0, 0.095833 },
{ 174, 1, 0, 29, 3, 2, 0.095893 },
{ 13, 0, 0, 13, 0, 0, 0.096667 },
{ 17, 0, 0, 17, 0, 0, 0.096875 },
{ 21, 0, 0, 21, 0, 0, 0.096875 },
{ 87, 1, 0, 29, 1, 2, 0.097366 },
{ 48, 0, 0, 16, 0, 2, 0.097969 },
{ 24, 1, 0, 12, 131, 0, 0.098789 },
{ 76, 0, 0, 19, 4, 0, 0.100926 },
{ 348, 0, 0, 29, 4, 2, 0.101116 },
{ 14, 0, 0, 14, 0, 0, 0.102222 },
{ 9, 0, 0, 9, 0, 0, 0.103889 },
{ 23, 1, 0, 23, 1, 0, 0.104545 },
{ 46, 1, 0, 23, 3, 0, 0.105682 },
{ 12, 0, 0, 12, 0, 0, 0.106250 },
{ 87, 0, 0, 29, 0, 2, 0.108348 },
{ 19, 0, 0, 19, 0, 0, 0.110000 },
{ 7, 0, 0, 7, 0, 0, 0.113333 },
{ 10, 0, 0, 10, 0, 0, 0.113333 },
{ 92, 0, 0, 23, 4, 0, 0.113826 },
{ 186, 1, 0, 31, 3, 2, 0.116094 },
{ 93, 1, 0, 31, 1, 2, 0.116813 },
{ 23, 0, 0, 23, 0, 0, 0.120909 },
{ 5, 1, 0, 5, 1, 0, 0.121250 },
{ 93, 0, 0, 31, 0, 2, 0.127625 },
{ 16, 0, 0, 16, 0, 0, 0.132917 },
{ 8, 0, 0, 8, 0, 0, 0.141667 },
{ 25, 0, 0, 25, 0, 0, 0.152500 },
{ 58, 1, 0, 29, 3, 0, 0.157946 },
{ 29, 1, 0, 29, 1, 0, 0.158393 },
{ 116, 0, 0, 29, 4, 0, 0.162946 },
{ 3, 1, 0, 3, 1, 0, 0.163125 },
{ 29, 0, 0, 29, 0, 0, 0.169286 },
{ 5, 0, 0, 5, 0, 0, 0.170000 },
{ 6, 0, 0, 6, 0, 0, 0.170000 },
{ 31, 1, 0, 31, 1, 0, 0.191333 },
{ 62, 1, 0, 31, 3, 0, 0.192083 },
{ 124, 0, 0, 31, 4, 0, 0.196389 },
{ 31, 0, 0, 31, 0, 0, 0.205000 },
{ 3, 0, 0, 3, 0, 0, 0.255000 },
{ 4, 0, 0, 4, 0, 0, 0.262500 },
{ 2, 1, 1, 2, 3, 1, 0.325000 },
{ 1, 1, 0, 1, 1, 0, 0.385000 },
{ 2, 0, 0, 2, 0, 0, 0.420000 },
};

#define TWIST_DOUBLE_RATIO              (9.0/16.0)

static long
torsion_constraint(struct torctab_rec *torctab, long ltorc, double tormod[], long n, long m)
{
  long i, b = -1;
  double rb = -1.;
  for (i = 0 ; i < ltorc ; i++)
  {
    struct torctab_rec *ti = torctab + i;
    if ( ! (n%ti->m) && ( !ti->fix2 || (n%(2*ti->m)) ) && ( ! ti->fix3 || (n%(3*ti->m)) ) )
      if ( n == m || ( ! (m%ti->m) && ( !ti->fix2 || (m%(2*ti->m)) ) && ( ! ti->fix3 || (m%(3*ti->m)) ) ) )
      {
        double ri = ti->rating*tormod[ti->N];
        if ( b < 0 || ri < rb ) {  b = i; rb = ri; }
      }
  }
  if (b < 0) pari_err_BUG("find_rating");
  return b;
}

static void
best_torsion_constraint(ulong p, long t, int *ptwist, ulong *ptor, int *ps2, int *pt3)
{
  struct torctab_rec *torctab;
  double tormod[32];
  long ltorc;
  long n1, n2;
  long b, b1, b2, b12;
  long i;

  if ( (p%3)==2 ) {
    if ( (p&3)==3 ) {
      torctab = torctab1;
      ltorc = sizeof(torctab1)/sizeof(*torctab1);
    } else {
      torctab = torctab2;
      ltorc = sizeof(torctab2)/sizeof(*torctab2);
    }
  } else {
    if ( (p&3)==3 ) {
      torctab = torctab3;
      ltorc = sizeof(torctab3)/sizeof(*torctab3);
    } else {
      torctab = torctab4;
      ltorc = sizeof(torctab4)/sizeof(*torctab4);
    }
  }
  for ( i = 0 ; i < 32 ; i++ ) tormod[i] = 1.0;
  if ( (p%5)==1 ) tormod[5] = tormod[10] = tormod[15] = 6.0/5.0;
  if ( (p%7)==1 ) tormod[7] = tormod[14] = 8.0/7.0;
  if ( (p%11)== 1 ) tormod[11] = 12.0/11.0;
  if ( (p%13)==1 ) tormod[13] = 14.0/13.0;
  if ( (p%17)==1 ) tormod[17] = 18.0/17.0;
  if ( (p%19)==1 ) tormod[19] = 20.0/19.0;
  if ( (p%23)==1 ) tormod[23] = 24.0/23.0;
  if ( (p%29)==1 ) tormod[29] = 30.0/29.0;
  if ( (p%31)==1 ) tormod[31] = 32.0/31.0;

  n1 = p+1-t;
  n2 = p+1+t;
  b12 = -1;
  b1  = torsion_constraint(torctab, ltorc, tormod, n1, n1);
  b2  = torsion_constraint(torctab, ltorc, tormod, n2, n2);
  b12 = torsion_constraint(torctab, ltorc, tormod, n1, n2);
  if ( b1 > b2 ) {
    if ( torctab[b2].rating / TWIST_DOUBLE_RATIO > torctab[b12].rating )
      *ptwist = 3;
    else
      *ptwist = 2;
  } else
    if ( torctab[b1].rating / TWIST_DOUBLE_RATIO > torctab[b12].rating )
      *ptwist = 3;
    else
      *ptwist = 1;
  b = *ptwist ==1 ? b1: *ptwist ==2 ? b2: b12;
  *ptor = torctab[b].N; *ps2 = torctab[b].s2_flag; *pt3 = torctab[b].t3_flag;
}

/* This is Sutherland 2009 Algorithm 1.1 */
static long
find_j_inv_with_given_trace(
  ulong *j_t, norm_eqn_t ne, long rho_inv, long max_curves)
{
  pari_sp ltop = avma, av;
  long curves_tested = 0, batch_size;
  long N0, N1, hasse[2];
  GEN n0, n1;
  long i, found = 0;
  ulong p = ne->p, pi = ne->pi;
  long t = ne->t;
  ulong p1 = p + 1, a4, a6, m, N;
  GEN A4, A6, tx, ty;
  int s2_flag, t3_flag, twist;

  if (p == 2 || p == 3) {
    if (t == 0) pari_err_BUG("find_j_inv_with_given_trace");
    *j_t = t; return 1;
  }

  N0 = (long)p1 - t; n0 = factoru(N0);
  N1 = (long)p1 + t; n1 = factoru(N1);

  best_torsion_constraint(p, t, &twist, &m, &s2_flag, &t3_flag);
  N = p1 - (twist<3 ? (twist==1 ? t: -t): 0);

  /* Select batch size so that we have roughly a 50% chance of finding
   * a good curve in a batch. */
  batch_size = 1.0 + rho_inv / (2.0 * m);
  A4 = cgetg(batch_size + 1, t_VECSMALL);
  A6 = cgetg(batch_size + 1, t_VECSMALL);
  tx = cgetg(batch_size + 1, t_VECSMALL);
  ty = cgetg(batch_size + 1, t_VECSMALL);

  dbg_printf(2)("  Selected torsion constraint m = %lu and batch "
                "size = %ld\n", m, batch_size);
  hasse_bounds(&hasse[0], &hasse[1], p);
  av = avma;
  while (!found && (max_curves <= 0 || curves_tested < max_curves))
  {
    GEN Pp1, Pt;
    random_curves_with_m_torsion((ulong *)(A4 + 1), (ulong *)(A6 + 1),
                                 (ulong *)(tx + 1), (ulong *)(ty + 1),
                                 batch_size, m, p);
    Pp1 = random_FleV(A4, A6, p, pi);
    Pt = gcopy(Pp1);
    FleV_mulu_pre_inplace(Pp1, N, A4, p, pi);
    if (twist >= 3) FleV_mulu_pre_inplace(Pt, t, A4,  p, pi);
    for (i = 1; i <= batch_size; ++i) {
      ++curves_tested;
      a4 = A4[i];
      a6 = A6[i]; if (a4 == 0 || a6 == 0) continue;

      if (( (twist >= 3 && mael(Pp1,i,1) == mael(Pt,i,1))
         || (twist < 3 && umael(Pp1,i,1) == p))
          && test_curve_order(ne, a4, a6, N0, N1, n0, n1, hasse)) {
        *j_t = Fl_ellj_pre(a4, a6, p, pi);
        found = 1; break;
      }
    }
    avma = av;
  }
  avma = ltop; return curves_tested;
}

/*
 * SECTION: Functions for dealing with polycyclic presentations.
 */

static GEN
next_generator(GEN DD, long D, ulong u, long filter, GEN *genred, long *P)
{
  pari_sp av = avma;
  ulong p = (ulong)*P;
  while (1)
  {
    p = unextprime(p + 1);
    if (p > LONG_MAX) pari_err_BUG("next_generator");
    if (kross(D, (long)p) != -1 && u % p != 0 && filter % p != 0)
    {
      GEN gen = primeform_u(DD, p);
      /* If gen is in the principal class, skip it */
      *genred = redimag(gen);
      if (!equali1(gel(*genred,1))) { *P = (long)p; return gen; }
      avma = av;
    }
  }
}

INLINE long *
evec_ri_mutate(long r[], long i)
{ return r + (i * (i - 1) >> 1); }

INLINE const long *
evec_ri(const long r[], long i)
{ return r + (i * (i - 1) >> 1); }

/* Reduces evec e so that e[i] < n[i] (assume e[i] >= 0) using pcp(n,r,k).
 * No check for overflow, this could be an issue for large groups */
INLINE void
evec_reduce(long e[], const long n[], const long r[], long k)
{
  long i, j, q;
  const long *ri;
  if (!k) return;
  for (i = k - 1; i > 0; i--) {
    if (e[i] >= n[i]) {
      q = e[i] / n[i];
      ri = evec_ri(r, i);
      for (j = 0; j < i; j++) e[j] += q * ri[j];
      e[i] -= q * n[i];
    }
  }
  e[0] %= n[0];
}

/* Computes e3 = log(a^e1*a^e2) in terms of the given polycyclic
 * presentation (here a denotes the implicit vector of generators) */
INLINE void
evec_compose(long e3[],
  const long e1[], const long e2[], const long n[],const long r[], long k)
{
    long i;
    for (i = 0; i < k; i++) e3[i] = e1[i] + e2[i];
    evec_reduce(e3, n, r, k);
}

/* Converts an evec to an integer index corresponding to the
 * multi-radix representation of the evec with moduli corresponding to
 * the subgroup orders m[i] */
INLINE long
evec_to_index(const long e[], const long m[], long k)
{
  long i, index = e[0];
  for (i = 1; i < k; i++) index += e[i] * m[i - 1];
  return index;
}

INLINE void
evec_copy(long f[], const long e[], long k)
{
  long i;
  for (i = 0; i < k; ++i) f[i] = e[i];
}

INLINE void
evec_clear(long e[], long k)
{
  long i;
  for (i = 0; i < k; ++i) e[i] = 0;
}

/* e1 and e2 may overlap */
/* Note that this function is not very efficient because it does not know the
 * orders of the elements in the presentation, only the relative orders */
INLINE void
evec_inverse(long e2[], const long e1[], const long n[], const long r[], long k)
{
  pari_sp av = avma;
  long i, *e3, *e4;

  e3 = new_chunk(k);
  e4 = new_chunk(k);
  evec_clear(e4, k);
  evec_copy(e3, e1, k);
  /* We have e1 + e4 = e3 which we maintain throughout while making e1
   * the zero vector */
  for (i = k - 1; i >= 0; i--) if (e3[i])
  {
    e4[i] += n[i] - e3[i];
    evec_reduce(e4, n, r, k);
    e3[i] = n[i];
    evec_reduce(e3, n, r, k);
  }
  evec_copy(e2, e4, k);
  avma = av;
}

/* e1 and e2 may overlap */
/* This is a faster way to compute inverses, if the presentation
 * element orders are known (these are specified in the array o, the
 * array n holds the relative orders) */
INLINE void
evec_inverse_o(
  long e2[],
  const long e1[], const long n[], const long o[], const long r[], long k)
{
  long j;
  for (j = 0; j < k; j++) e2[j] = (e1[j] ? o[j] - e1[j] : 0);
  evec_reduce(e2, n, r, k);
}

/* Computes the order of the group element a^e using the pcp (n,r,k) */
INLINE long
evec_order(const long e[], const long n[], const long r[], long k)
{
  pari_sp av = avma;
  long *f = new_chunk(k);
  long i, j, o, m;

  evec_copy(f, e, k);
  for (o = 1, i = k - 1; i >= 0; i--) if (f[i])
  {
    m = n[i] / ugcd(f[i], n[i]);
    for (j = 0; j < k; j++) f[j] *= m;
    evec_reduce(f, n, r, k);
    o *= m;
  }
  avma = av; return o;
}

/* Computes orders o[] for each generator using relative orders n[]
 * and power relations r[] */
INLINE void
evec_orders(long o[], const long n[], const long r[], long k)
{
  pari_sp av = avma;
  long i, *e = new_chunk(k);

  evec_clear(e, k);
  for (i = 0; i < k; i++) {
    e[i] = 1;
    if (i) e[i - 1] = 0;
    o[i] = evec_order(e, n, r, k);
  }
  avma = av;
}

INLINE int
evec_equal(const long e1[], const long e2[], long k)
{
  long j;
  for (j = 0; j < k; ++j)
    if (e1[j] != e2[j]) break;
  return j == k;
}

INLINE void
index_to_evec(long e[], long index, const long m[], long k)
{
  long i;
  for (i = k - 1; i > 0; --i) {
    e[i] = index / m[i - 1];
    index -= e[i] * m[i - 1];
  }
  e[0] = index;
}

INLINE void
evec_n_to_m(long m[], const long n[], long k)
{
  long i;
  m[0] = n[0];
  for (i = 1; i < k; ++i) m[i] = m[i - 1] * n[i];
}


/* Based on logfac() in Sutherland's classpoly package.
 * Ramanujan approximation to log(n!), accurate to O(1/n^3) */
INLINE double
logfac(long n)
{
  const double HALFLOGPI = 0.57236494292470008707171367567653;
  return n * log((double) n) - (double) n +
    log((double) n * (1.0 + 4.0 * n * (1.0 + 2.0 * n))) / 6.0 +
    HALFLOGPI;
}

/* This is based on Sutherland 2009, Lemma 8 (p31). */
static double
upper_bound_on_classpoly_coeffs(long D, long h, GEN qfinorms)
{
  const double LOG2E = 1.44269504088896340735992468100189;
  pari_sp ltop = avma;
  GEN C = dbltor(2114.567);
  double Mk, m, logbinom;
  GEN tmp = mulrr(mppi(LOWDEFAULTPREC), sqrtr(stor(-D, LOWDEFAULTPREC)));
  /* We treat this case separately since the table is not initialised when
   * h = 1. This is the same as in the for loop below but with ak = 1. */
  double log2Mk = dbllog2r(mpadd(mpexp(tmp), C));
  double res = log2Mk;
  ulong maxak = 1;
  double log2Mh = log2Mk;

  pari_sp btop = avma;
  long k;
  for (k = 2; k <= h; ++k) {
    ulong ak = uel(qfinorms, k);
    /* exp(tmp/a[k]) can overflow for even moderate discriminants, so we need
     * to use t_REALs instead of doubles.  Sutherland has a (more complicated)
     * implementation in the classpoly package which should be consulted if
     * this ever turns out to be a bottleneck.
     *
     * One idea to avoid t_REALs is the following: we have
     * log(e^x + C) - x <= log(2) ~ 0.69 for x >= log(C) ~ 0.44 and
     * the difference is basically zero for x slightly bigger than log(C).
     * Hence for large discriminants, we have x = \pi\sqrt{-D}/ak >> log(C)
     * and so we could approximate log(e^x + C) by x. */
    log2Mk = dbllog2r(mpadd(mpexp(divru(tmp, ak)), C));
    res += log2Mk;
    if (ak > maxak) { maxak = ak; log2Mh = log2Mk; }
    avma = btop;
  }

  Mk = pow(2.0, log2Mh);
  m = floor((h + 1)/(Mk + 1.0));
  /* This line computes "log2(itos(binomialuu(h, m)))".  The smallest
   * fundamental discriminant for which logbinom is not zero is
   * -1579751. */
  logbinom = (m > 0 && m < h)
    ? LOG2E * (logfac(h) - logfac(m) - logfac(h - m))
    : 0;
  avma = ltop;
  return res + logbinom - m * log2Mh + 2.0;
}

INLINE long
distinct_inverses(const long f[], const long ef[], const long ei[],
  const long n[], const long o[], const long r[], long k, long L0, long i)
{
  pari_sp av = avma;
  long j, *e2, *e3;

  if ( ! ef[i] || (L0 && ef[0])) return 0;
  for (j = i + 1; j < k; ++j)
    if (ef[j]) break;
  if (j < k) return 0;

  e2 = new_chunk(k);
  evec_copy(e2, ef, i);
  e2[i] = o[i] - ef[i];
  for (j = i + 1; j < k; ++j) e2[j] = 0;
  evec_reduce(e2, n, r, k);

  if (evec_equal(ef, e2, k)) { avma = av; return 0; }

  e3 = new_chunk(k);
  evec_inverse_o(e3, ef, n, o, r, k);
  if (evec_equal(e2, e3, k)) { avma = av; return 0; }

  if (f) {
    evec_compose(e3, f, ei, n, r, k);
    if (evec_equal(e2, e3, k)) { avma = av; return 0; }

    evec_inverse_o(e3, e3, n, o, r, k);
    if (evec_equal(e2, e3, k)) { avma = av; return 0; }
  }
  avma = av; return 1;
}

INLINE long
next_prime_evec(long *qq, long f[], const long m[], long k,
  hashtable *tbl, long D, GEN DD, long u, long lvl, long ubound)
{
  pari_sp av = avma;
  hashentry *he;
  GEN P;
  long idx, q = *qq;

  do q = unextprime(q + 1);
  while (!(u % q) || kross(D, q) == -1 || !(lvl % q) || !(D % (q * q)));
  if (q > ubound) return 0;
  *qq = q;

  /* Get evec f corresponding to q */
  P = redimag(primeform_u(DD, q));
  he = hash_search(tbl, P);
  if (!he) pari_err_BUG("next_prime_evec");
  idx = itos((GEN) he->val);
  index_to_evec(f, idx, m, k);
  avma = av; return 1;
}

/* Return 1 on success, 0 on failure. */
static int
orient_pcp(classgp_pcp_t G, long *ni, long D, long u, hashtable *tbl)
{
  pari_sp av = avma;
  /* 199 seems to suffice, but can be increased if necessary */
  enum { MAX_ORIENT_P = 199 };
  const long *L = G->L, *n = G->n, *r = G->r, *m = G->m, *o = G->o;
  long i, *ps = G->orient_p, *qs = G->orient_q, *reps = G->orient_reps;
  long *ef, *e, *ei, *f, k = G->k, lvl = modinv_level(G->inv);
  GEN DD = stoi(D);

  memset(ps, 0, k * sizeof(long));
  memset(qs, 0, k * sizeof(long));
  memset(reps, 0, k * k * sizeof(long));

  for (i = 0; i < k; ++i) { ps[i] = -1; if (o[i] > 2) break; }
  for (++i; i < k; ++i) ps[i] = (o[i] > 2) ? 0 : -1; /* ps[i] = -!(o[i] > 2); */

  e = new_chunk(k);
  ei = new_chunk(k);
  f = new_chunk(k);

  for (i = 0; i < k; ++i) {
    long p;
    if (ps[i]) continue;
    p = L[i];
    ef = &reps[i * k];
    while (!ps[i]) {
      if (!next_prime_evec(&p, ef, m, k, tbl, D, DD, u, lvl, MAX_ORIENT_P))
        break;
      evec_inverse_o(ei, ef, n, o, r, k);
      if (!distinct_inverses(NULL, ef, ei, n, o, r, k, G->L0, i)) continue;
      ps[i] = p;
      qs[i] = 1;
    }
    if (ps[i]) continue;

    p = unextprime(L[i] + 1);
    while (!ps[i]) {
      long q;

      if (!next_prime_evec(&p, e, m, k, tbl, D, DD, u, lvl, MAX_ORIENT_P))
        break;
      evec_inverse_o(ei, e, n, o, r, k);

      q = L[i];
      while (!qs[i]) {
        if (!next_prime_evec(&q, f, m, k, tbl, D, DD, u, lvl, p - 1)) break;
        evec_compose(ef, e, f, n, r, k);
        if (!distinct_inverses(f, ef, ei, n, o, r, k, G->L0, i)) continue;
        ps[i] = p;
        qs[i] = q;
      }
    }
    if (!ps[i]) return 0;
  }
  if (ni) {
    GEN N = qfb_nform(D, *ni);
    hashentry *he = hash_search(tbl, N);
    if (!he) pari_err_BUG("orient_pcp");
    *ni = itos((GEN) he->val);
  }
  avma = av; return 1;
}

/* We must avoid situations where L_i^{+/-2} = L_j^2 (or = L_0*L_j^2
 * if ell0 flag is set), with |L_i| = |L_j| = 4 (or have 4th powers in
 * <L0> but not 2nd powers in <L0>) and j < i */
/* These cases cause problems when enumerating roots via gcds */
/* returns the index of the first bad generator, or -1 if no bad
 * generators are found */
static long
classgp_pcp_check_generators(const long *n, long *r, long k, long L0)
{
  pari_sp av = avma;
  long *e1, i, i0, j, s;
  const long *ei;

  s = !!L0;
  e1 = new_chunk(k);

  for (i = s + 1; i < k; i++) {
    if (n[i] != 2) continue;
    ei = evec_ri(r, i);
    for (j = s; j < i; j++)
      if (ei[j]) break;
    if (j == i) continue;
    for (i0 = s; i0 < i; i0++) {
      if ((4 % n[i0])) continue;
      evec_clear(e1, k);
      e1[i0] = 4;
      evec_reduce(e1, n, r, k);
      for (j = s; j < i; j++)
        if (e1[j]) break;
      if (j < i) continue; /* L_i0^4 is not trivial or in <L_0> */
      evec_clear(e1, k);
      e1[i0] = 2;
      evec_reduce(e1, n, r, k); /* compute L_i0^2 */
      for (j = s; j < i; j++)
        if (e1[j] != ei[j]) break;
      if (j == i) return i;
      evec_inverse(e1, e1, n, r, k); /* compute L_i0^{-2} */
      for (j = s; j < i; j++)
        if (e1[j] != ei[j]) break;
      if (j == i) return i;
    }
  }
  avma = av; return -1;
}

static void
pcp_alloc_and_set(
  classgp_pcp_t G, const long *L, const long *n, const long *r, long k)
{
  /* classgp_pcp contains 6 arrays of length k (L, m, n, o, orient_p, orient_q),
   * one of length binom(k, 2) (r) and one of length k^2 (orient_reps) */
  long rlen = k * (k - 1) / 2, datalen = 6 * k + rlen + k * k;
  G->_data = newblock(datalen);
  G->L = G->_data;
  G->m = G->L + k;
  G->n = G->m + k;
  G->o = G->n + k;
  G->r = G->o + k;
  G->orient_p = G->r + rlen;
  G->orient_q = G->orient_p + k;
  G->orient_reps = G->orient_q + k;
  G->k = k;

  evec_copy(G->L, L, k);
  evec_copy(G->n, n, k);
  evec_copy(G->r, r, rlen);
  evec_orders(G->o, n, r, k);
  evec_n_to_m(G->m, n, k);
}

static void
classgp_pcp_clear(classgp_pcp_t G)
{ if (G->_data) killblock(G->_data); }

/* This is Sutherland 2009, Algorithm 2.2 (p16). */
static void
classgp_make_pcp(
  classgp_pcp_t G, double *height, long *ni,
  long h, long D, ulong u, long inv, long Lfilter, long orient)
{
  enum { MAX_GENS = 16, MAX_RLEN = MAX_GENS * (MAX_GENS - 1) / 2 };
  pari_sp av = avma, bv;
  long curr_p, h2, nelts, lvl = modinv_level(inv);
  GEN DD, ident, T, v;
  hashtable *tbl;
  long i, L1, L2;
  long k, L[MAX_GENS], n[MAX_GENS], r[MAX_RLEN];

  memset(G, 0, sizeof *G);

  G->D = D;
  G->h = h;
  G->inv = inv;
  G->L0 = (modinv_is_double_eta(inv) && modinv_ramified(D, inv))
    ? modinv_degree(NULL, NULL, inv) : 0;
  G->enum_cnt = h / (1 + !!G->L0);
  G->Lfilter = ulcm(Lfilter, lvl);

  if (h == 1) {
    if (G->L0) pari_err_BUG("classgp_pcp");
    G->k = 0;
    G->_data = NULL;
    v = const_vecsmall(1, 1);
    *height = upper_bound_on_classpoly_coeffs(D, h, v);
    /* NB: No need to set *ni when h = 1 */
    avma = av; return;
  }

  DD = stoi(D);
  bv = avma;
  while (1) {
    k = 0;
    /* Hash table has a QFI as a key and the (boxed) index of that QFI
     * in T as its value */
    tbl = hash_create(h, (ulong(*)(void*)) hash_GEN,
                         (int(*)(void*,void*))&gequal, 1);
    ident = redimag(primeform_u(DD, 1));
    hash_insert(tbl, ident, gen_0);

    T = vectrunc_init(h + 1);
    vectrunc_append(T, ident);
    nelts = 1;
    curr_p = 1;

    while (nelts < h) {
      GEN gamma_i, beta;
      hashentry *e;
      long N = glength(T), Tlen = N, ri = 1;

      if (k == MAX_GENS) pari_err_IMPL("classgp_pcp");

      if (nelts == 1 && G->L0) {
        curr_p = G->L0;
        gamma_i = qfb_nform(D, curr_p);
        beta = redimag(gamma_i);
        if (equali1(gel(beta, 1)))
        {
          curr_p = 1;
          gamma_i = next_generator(DD, D, u, G->Lfilter, &beta, &curr_p);
        }
      } else
        gamma_i = next_generator(DD, D, u, G->Lfilter, &beta, &curr_p);
      while ((e = hash_search(tbl, beta)) == NULL) {
        long j;
        for (j = 1; j <= N; ++j) {
          GEN t = qficomp(beta, gel(T, j));
          vectrunc_append(T, t);
          hash_insert(tbl, t, stoi(Tlen++));
        }
        beta = qficomp(beta, gamma_i);
        ++ri;
      }
      if (ri > 1) {
        long j, si;
        L[k] = curr_p;
        n[k] = ri;
        nelts *= ri;

        /* This is to reset the curr_p counter when we have G->L0 != 0
         * in the first position of L. */
        if (curr_p == G->L0) curr_p = 1;

        N = 1;
        si = itos((GEN) e->val);
        for (j = 0; j < k; ++j) {
          evec_ri_mutate(r, k)[j] = (si / N) % n[j];
          N *= n[j];
        }
        ++k;
      }
    }

    if ((i = classgp_pcp_check_generators(n, r, k, G->L0)) < 0) {
      pcp_alloc_and_set(G, L, n, r, k);
      if (!orient || orient_pcp(G, ni, D, u, tbl)) break;
      G->Lfilter *= G->L[0];
      classgp_pcp_clear(G);
    } else if (log2(G->Lfilter) + log2(L[i]) >= BITS_IN_LONG)
      pari_err_IMPL("classgp_pcp");
    else
      G->Lfilter *= L[i];
    avma = bv;
  }

  v = cgetg(h + 1, t_VECSMALL);
  v[1] = 1;
  for (i = 2; i <= h; ++i) uel(v,i) = itou(gmael(T,i,1));

  h2 = G->L0 ? h / 2 : h;
  *height = upper_bound_on_classpoly_coeffs(D, h2, v);

  /* The norms of the last one or two generators. */
  L1 = L[k - 1];
  L2 = k > 1 ? L[k - 2] : 1;
  /* 4 * L1^2 * L2^2 must fit in a ulong */
  if (2 * (1 + log2(L1) + log2(L2)) >= BITS_IN_LONG)
    pari_err_IMPL("classgp_pcp");

  if (G->L0 && (G->L[0] != G->L0 || G->o[0] != 2))
    pari_err_BUG("classgp_pcp");

  avma = av; return;
}

INLINE ulong
classno_wrapper(long D)
{
  pari_sp av = avma;
  GEN clsgp = quadclassunit0(stoi(D), 0, NULL, DEFAULTPREC);
  ulong h = itou(gel(clsgp, 1));
  avma = av; return h;
}

/*
 * SECTION: Functions for calculating class polynomials.
 */

/* NB: Sutherland defines V_MAX to be 1200 with saying why. */
#define V_MAX 1200

#define NSMALL_PRIMES 11
static const long SMALL_PRIMES[11] = {
  2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31
};

static long
is_smooth_enough(ulong *factors, long v)
{
  long i;
  *factors = 0;
  for (i = 0; i < NSMALL_PRIMES; ++i) {
    long p = SMALL_PRIMES[i];
    if (v % p == 0) *factors |= 1UL << i;
    while (v % p == 0) v /= p;
    if (v == 1) break;
  }
  return v == 1;
}

/* Hurwitz class number of |D| assuming hclassno() and attached
 * conversion to double costs much more than unegisfundamental(). */
INLINE double
hclassno_wrapper(long D, long h)
{
  /* TODO: Can probably calculate hurwitz faster using -D, factor(u)
   * and classno(D). */
  pari_sp av = avma;
  ulong abs_D = D < 0 ? -D : D;
  double hurwitz;

  if (h && unegisfundamental(abs_D))
    hurwitz = (double) h;
  else
    hurwitz = rtodbl(gtofp(hclassno(utoi(abs_D)), DEFAULTPREC));
  avma = av; return hurwitz;
}


/* This is Sutherland 2009, Algorithm 2.1 (p8).
 * NB: This function is not gerepileupto-safe. */
static GEN
select_classpoly_prime_pool(
  double min_prime_bits, double delta, classgp_pcp_t G)
{
  pari_sp av;
  double prime_bits = 0.0, hurwitz, z;
  ulong i;
  /* t_min[v] will hold the lower bound of the t we need to look at
   * for a given v. */
  ulong t_min[V_MAX], t_size_lim;
  GEN res;
  long D = G->D, inv = G->inv;

  if (delta <= 0) pari_err_BUG("select_suitable_primes");
  hurwitz = hclassno_wrapper(D, G->h);

  res = cgetg(1, t_VEC);
  /* Initialise t_min to be all 2's.  This avoids trace 0 and trace 1 curves */
  for (i = 0; i < V_MAX; ++i) t_min[i] = 2;

  /* maximum possible trace = sqrt(2^BIL - D) */
  t_size_lim = 2.0 * sqrt((double)((1UL << (BITS_IN_LONG - 2)) - (((ulong)-D) >> 2)));

  av = avma;
  for (z = -D / (2.0 * hurwitz); ; z *= delta + 1.0) {
    /* v_bound_aux = -4 z H(-D). */
    double v_bound_aux = -4.0 * z * hurwitz;
    ulong v;
    dbg_printf(1)("z = %.2f\n", z);
    for (v = 1; ; ++v) {
      ulong pcount = 0, t, t_max, vfactors;
      ulong m_vsqr_D = v * v * (ulong)(-D);
      /* hurwitz_ratio_bound = 11 * log(log(v + 4))^2 */
      double hurwitz_ratio_bound = log(log(v + 4.0)), max_p, H;
      hurwitz_ratio_bound *= 11.0 * hurwitz_ratio_bound;

      if (v >= v_bound_aux * hurwitz_ratio_bound / D || v >= V_MAX) break;

      if ( ! is_smooth_enough(&vfactors, v)) continue;
      H = hclassno_wrapper(m_vsqr_D, 0);

      /* t <= 2 sqrt(p) and p <= z H(-v^2 D) and
       *
       *   H(-v^2 D) < vH(-D) (11 log(log(v + 4))^2)
       *
       * This last term is v * hurwitz * hurwitz_ratio_bound. */
      max_p = z * v * hurwitz * hurwitz_ratio_bound;
      t_max = 2.0 * mindd(sqrt((double)((1UL << (BITS_IN_LONG - 2)) - (m_vsqr_D >> 2))),
                          sqrt(max_p));
      for (t = t_min[v]; t <= t_max; ++t) {
        ulong possible_4p = t * t + m_vsqr_D;
        if (possible_4p % 4 == 0) {
          ulong possible_p = possible_4p / 4;
          if (uisprime(possible_p) && modinv_good_prime(inv, possible_p)) {
            long p = possible_p;
            double rho_inv = p / H;
            GEN hit;

            hit = mkvecsmall5(p, t, v, (long)rho_inv, vfactors);
            /* FIXME: Avoid doing GC for every prime as here. */
            res = gerepileupto(av, gconcat(res, hit));
            prime_bits += log2(p);
            ++pcount;
          }
        }
      }
      t_min[v] = t_max + 1;

      if (pcount) {
        dbg_printf(2)("  Found %lu primes for v = %lu.\n", pcount, v);
        if (gc_needed(av, 2))
          res = gerepilecopy(av, res);
      }
      if (prime_bits > min_prime_bits) {
        dbg_printf(1)("Found %ld primes; total size %.2f bits.\n",
                    glength(res), prime_bits);
        return gerepilecopy(av, res);
      }
    }
    /* Have we exhausted all possible solutions that fit in machine words? */
    if (t_min[1] >= t_size_lim) {
      char *err = stack_sprintf("class polynomial of discriminant %ld", D);
      pari_err(e_ARCH, err);
    }
  }
}

INLINE int
cmp_small(long a, long b)
{ return a>b? 1: (a<b? -1: 0); }

static int
primecmp(void *data, GEN v1, GEN v2)
{ (void)data; return cmp_small(v1[4], v2[4]); }


static long
height_margin(long inv, long D)
{
  (void)D;
  /* NB: avs just uses a height margin of 256 for everyone and everything. */
  if (inv == INV_F) return 64;  /* checked for discriminants up to -350000 */
  if (inv == INV_G2) return 5;
  if (inv != INV_J) return 256; /* TODO: This should be made more accurate */
  return 0;
}

static GEN
select_classpoly_primes(
  ulong *vfactors, ulong *biggest_v,
  long k, double delta, classgp_pcp_t G, double height)
{
  pari_sp av = avma;
  long i, s, D = G->D, inv = G->inv;
  ulong biggest_p;
  double prime_bits, min_prime_bits, b;
  GEN prime_pool;

  if (k < 2) pari_err_BUG("select_suitable_primes");

  s = modinv_height_factor(inv);
  b = height / s + height_margin(inv, D);
  dbg_printf(1)("adjusted height = %.2f\n", b);
  min_prime_bits = k * b;

  prime_pool = select_classpoly_prime_pool(min_prime_bits, delta, G);

  /* FIXME: Apply torsion constraints */
  /* FIXME: Rank elts of res according to cost/benefit ratio */
  gen_sort_inplace(prime_pool, NULL, primecmp, NULL);

  prime_bits = 0.0;
  biggest_p = gel(prime_pool, 1)[1];
  *biggest_v = gel(prime_pool, 1)[3];
  *vfactors = 0;
  for (i = 1; i < lg(prime_pool); ++i) {
    ulong p = gel(prime_pool, i)[1];
    ulong v = gel(prime_pool, i)[3];
    prime_bits += log2(p);
    *vfactors |= gel(prime_pool, i)[5];
    if (p > biggest_p) biggest_p = p;
    if (v > *biggest_v) *biggest_v = v;
    if (prime_bits > b) break;
  }
  dbg_printf(1)("Selected %ld primes; largest is %lu ~ 2^%.2f\n",
             i, biggest_p, log2(biggest_p));
  return gerepilecopy(av, vecslice0(prime_pool, 1, i));
}

/* This is Sutherland 2009 Algorithm 1.2. */
static long
oneroot_of_classpoly(
  ulong *j_endo, int *endo_cert, ulong j, norm_eqn_t ne, GEN jdb)
{
  pari_sp av = avma;
  long nfactors, L_bound, i;
  ulong p = ne->p, pi = ne->pi;
  GEN factw, factors, u_levels, vdepths;

  if (j == 0 || j == 1728 % p) pari_err_BUG("oneroot_of_classpoly");

  *endo_cert = 1;
  if (ne->u * ne->v == 1) { *j_endo = j; return 1; }

  /* TODO: Precalculate all this data further up */
  factw = factoru(ne->u * ne->v);
  factors = gel(factw, 1);
  nfactors = lg(factors) - 1;
  u_levels = cgetg(nfactors + 1, t_VECSMALL);
  for (i = 1; i <= nfactors; ++i)
    u_levels[i] = z_lval(ne->u, gel(factw, 1)[i]);
  vdepths = gel(factw, 2);

  /* FIXME: This should be bigger */
  L_bound = maxdd(log((double) -ne->D), (double)ne->v);

  /* Iterate over the primes L dividing w */
  for (i = 1; i <= nfactors; ++i) {
    pari_sp bv = avma;
    GEN phi;
    long jlvl, lvl_diff, depth = vdepths[i];
    long L = factors[i];
    if (L > L_bound) { *endo_cert = 0; break; }

    phi = polmodular_db_getp(jdb, L, p);

    /* TODO: See if I can reuse paths created in j_level_in_volcano()
     * later in {ascend,descend}_volcano(), perhaps by combining the
     * functions into one "adjust_level" function. */
    jlvl = j_level_in_volcano(phi, j, p, pi, L, depth);
    lvl_diff = u_levels[i] - jlvl;

    if (lvl_diff < 0)
      /* j's level is less than v(u) so we must ascend */
      j = ascend_volcano(phi, j, p, pi, jlvl, L, depth, -lvl_diff);
    else if (lvl_diff > 0)
      /* otherwise j's level is greater than v(u) so we descend */
      j = descend_volcano(phi, j, p, pi, jlvl, L, depth, lvl_diff);
    avma = bv;
  }
  avma = av;
  /* At this point the probability that j has the wrong endomorphism
   * ring is about \sum_{p|u_compl} 1/p (and u_compl must be bigger
   * than L_bound, so pretty big), so just return it and rely on
   * detection code in enum_j_with_endo_ring().  Detection is that we
   * hit a previously found j-invariant earlier than expected.  OR, we
   * evaluate class polynomials of the suborders at j and if any are
   * zero then j must be chosen again.  */
  *j_endo = j;
  return j != 0 && j != 1728 % p;
}

INLINE long
vecsmall_isin_skip(GEN v, long x, long k)
{
  long i, l = lg(v);
  for (i = k; i < l; ++i)
    if (v[i] == x) return i;
  return 0;
}

INLINE ulong
select_twisting_param(ulong p)
{
  ulong T;
  do T = random_Fl(p); while (krouu(T, p) != -1);
  return T;
}

INLINE void
setup_norm_eqn(norm_eqn_t ne, long D, long u, GEN norm_eqn)
{
  ne->D = D;
  ne->u = u;
  ne->t = norm_eqn[2];
  ne->v = norm_eqn[3];
  ne->p = (ulong) norm_eqn[1];
  ne->pi = get_Fl_red(ne->p);
  ne->s2 = Fl_2gener_pre(ne->p, ne->pi);
  ne->T = select_twisting_param(ne->p);
}

INLINE ulong
Flv_powsum_pre(GEN v, ulong n, ulong p, ulong pi)
{
  long i, l = lg(v);
  ulong psum = 0;
  for (i = 1; i < l; ++i)
    psum = Fl_add(psum, Fl_powu_pre(uel(v,i), n, p, pi), p);
  return psum;
}

INLINE int
modinv_has_sign_ambiguity(long inv)
{
  switch (inv) {
  case INV_F:
  case INV_F3:
  case INV_W2W3E2:
  case INV_W2W7E2:
  case INV_W2W3:
  case INV_W2W5:
  case INV_W2W7:
  case INV_W3W3:
  case INV_W2W13:
  case INV_W3W7: return 1;
  }
  return 0;
}

INLINE int
modinv_units(int inv)
{ return modinv_is_double_eta(inv) || modinv_is_Weber(inv); }

INLINE int
adjust_signs(GEN js, ulong p, ulong pi, long inv, GEN T, long e)
{
  long negate = 0;
  long h = lg(js) - 1;
  if ((h & 1) && modinv_units(inv)) {
    ulong prod = Flv_prod_pre(js, p, pi);
    if (prod != p - 1) {
      if (prod != 1) pari_err_BUG("adjust_signs: constant term is not +/-1");
      negate = 1;
    }
  } else {
    ulong tp, t;
    tp = umodiu(T, p);
    t = Flv_powsum_pre(js, e, p, pi);
    if (t == 0) return 0;
    if (t != tp) {
      if (Fl_neg(t, p) != tp) pari_err_BUG("adjust_signs: incorrect trace");
      negate = 1;
    }
  }
  if (negate) Flv_neg_inplace(js, p);
  return 1;
}

static ulong
find_jinv(
  long *trace_tries, long *endo_tries, int *cert,
  norm_eqn_t ne, long inv, long rho_inv, GEN jdb)
{
  long found, ok = 1;
  ulong j, r;
  do {
    do {
      long tries;
      ulong j_t = 0;
      /* TODO: Set batch size according to expected number of tries and
       * experimental cost/benefit analysis. */
      tries = find_j_inv_with_given_trace(&j_t, ne, rho_inv, 0);
      if (j_t == 0)
        pari_err_BUG("polclass0: Couldn't find j-invariant with given trace.");
      dbg_printf(2)("  j-invariant %ld has trace +/-%ld (%ld tries, 1/rho = %ld)\n",
          j_t, ne->t, tries, rho_inv);
      *trace_tries += tries;

      found = oneroot_of_classpoly(&j, cert, j_t, ne, jdb);
      ++*endo_tries;
    } while (!found);

    if (modinv_is_double_eta(inv))
      ok = modfn_unambiguous_root(&r, inv, j, ne, jdb);
    else
      r = modfn_root(j, ne, inv);
  } while (!ok);
  return r;
}

static GEN
polclass_roots_modp(
  long *n_trace_curves,
  norm_eqn_t ne, long rho_inv, classgp_pcp_t G, GEN db)
{
  pari_sp av = avma;
  ulong j = 0;
  long inv = G->inv, endo_tries = 0;
  int endo_cert;
  GEN res, jdb, fdb;

  jdb = polmodular_db_for_inv(db, INV_J);
  fdb = polmodular_db_for_inv(db, inv);

  dbg_printf(2)("p = %ld, t = %ld, v = %ld\n", ne->p, ne->t, ne->v);

  do {
    j = find_jinv(n_trace_curves, &endo_tries, &endo_cert, ne, inv, rho_inv, jdb);

    res = enum_roots(j, ne, fdb, G);
    if ( ! res && endo_cert) pari_err_BUG("polclass_roots_modp");
    if (res && ! endo_cert && vecsmall_isin_skip(res, res[1], 2))
    {
      avma = av;
      res = NULL;
    }
  } while (!res);

  dbg_printf(2)("  j-invariant %ld has correct endomorphism ring "
             "(%ld tries)\n", j, endo_tries);
  dbg_printf(4)("  all such j-invariants: %Ps\n", res);
  return gerepileupto(av, res);
}

INLINE int
modinv_inverted_involution(long inv)
{ return modinv_is_double_eta(inv); }

INLINE int
modinv_negated_involution(long inv)
{ /* determined by trial and error */
  return inv == INV_F || inv == INV_W3W5 || inv == INV_W3W7
    || inv == INV_W3W3 || inv == INV_W5W7;
}

/* Return true iff Phi_L(j0, j1) = 0. */
INLINE long
verify_edge(ulong j0, ulong j1, ulong p, ulong pi, long L, GEN fdb)
{
  pari_sp av = avma;
  GEN phi = polmodular_db_getp(fdb, L, p);
  GEN f = Flm_Fl_polmodular_evalx(phi, L, j1, p, pi);
  ulong r = Flx_eval_pre(f, j0, p, pi);
  avma = av; return !r;
}

INLINE long
verify_2path(
  ulong j1, ulong j2, ulong p, ulong pi, long L1, long L2, GEN fdb)
{
  pari_sp av = avma;
  GEN phi1 = polmodular_db_getp(fdb, L1, p);
  GEN phi2 = polmodular_db_getp(fdb, L2, p);
  GEN f = Flm_Fl_polmodular_evalx(phi1, L1, j1, p, pi);
  GEN g = Flm_Fl_polmodular_evalx(phi2, L2, j2, p, pi);
  GEN d = Flx_gcd(f, g, p);
  long n = degpol(d);
  if (n >= 2) n = Flx_nbroots(d, p);
  avma = av; return n;
}

static long
oriented_n_action(
  const long *ni, classgp_pcp_t G, GEN v, ulong p, ulong pi, GEN fdb)
{
  pari_sp av = avma;
  long i, j, k = G->k;
  long nr = k * (k - 1) / 2;
  const long *n = G->n, *m = G->m, *o = G->o, *r = G->r,
    *ps = G->orient_p, *qs = G->orient_q, *reps = G->orient_reps;
  long *signs = new_chunk(k);
  long *e = new_chunk(k);
  long *rels = new_chunk(nr);

  evec_copy(rels, r, nr);

  for (i = 0; i < k; ++i) {
    /* If generator doesn't require orientation, continue; power rels already
     * copied to *rels in initialisation */
    if (ps[i] <= 0) { signs[i] = 1; continue; }
    /* Get rep of orientation element and express it in terms of the
     * (partially) oriented presentation */
    for (j = 0; j < i; ++j) {
      long t = reps[i * k + j];
      e[j] = (signs[j] < 0 ? o[j] - t : t);
    }
    e[j] = reps[i * k + j];
    for (++j; j < k; ++j) e[j] = 0;
    evec_reduce(e, n, rels, k);
    j = evec_to_index(e, m, k);

    /* FIXME: These calls to verify_edge recalculate powers of v[0]
     * and v[j] over and over again, they also reduce Phi_{ps[i]} modulo p over
     * and over again.  Need to cache these things! */
    if (qs[i] > 1)
      signs[i] =
        (verify_2path(uel(v,1), uel(v,j+1), p, pi, ps[i], qs[i], fdb) ? 1 : -1);
    else
      /* Verify ps[i]-edge to orient ith generator */
      signs[i] =
        (verify_edge(uel(v,1), uel(v,j+1), p, pi, ps[i], fdb) ? 1 : -1);
    /* Update power relation */
    for (j = 0; j < i; ++j) {
      long t = evec_ri(r, i)[j];
      e[j] = (signs[i] * signs[j] < 0 ? o[j] - t : t);
    }
    while (j < k) e[j++] = 0;
    evec_reduce(e, n, rels, k);
    for (j = 0; j < i; ++j) evec_ri_mutate(rels, i)[j] = e[j];
    /* TODO: This is a sanity check, can be removed if everything is working */
    for (j = 0; j <= i; ++j) {
      long t = reps[i * k + j];
      e[j] = (signs[j] < 0 ? o[j] - t : t);
    }
    while (j < k) e[j++] = 0;
    evec_reduce(e, n, rels, k);
    j = evec_to_index(e, m, k);
    if (qs[i] > 1) {
      if (!verify_2path(uel(v,1), uel(v, j+1), p, pi, ps[i], qs[i], fdb))
        pari_err_BUG("oriented_n_action");
    } else {
      if (!verify_edge(uel(v,1), uel(v, j+1), p, pi, ps[i], fdb))
        pari_err_BUG("oriented_n_action");
    }
  }

  /* Orient representation of [N] relative to the torsor <signs, rels> */
  for (i = 0; i < k; ++i) e[i] = (signs[i] < 0 ? o[i] - ni[i] : ni[i]);
  evec_reduce(e, n, rels, k);
  avma = av; return evec_to_index(e, m, k);
}

/* F = double_eta_raw(inv) */
INLINE void
adjust_orientation(GEN F, long inv, GEN v, long e, ulong p, ulong pi)
{
  ulong j0 = uel(v, 1), je = uel(v, e);

  if (!modinv_j_from_2double_eta(F, inv, NULL, j0, je, p, pi)) {
    if (modinv_inverted_involution(inv)) Flv_inv_pre_inplace(v, p, pi);
    if (modinv_negated_involution(inv)) Flv_neg_inplace(v, p);
  }
}

static void
polclass_psum(
  GEN *psum, long *d, GEN roots, GEN primes, GEN pilist, ulong h, long inv)
{
  /* Number of consecutive CRT stabilisations before we assume we have
   * the correct answer. */
  enum { MIN_STAB_CNT = 3 };
  pari_sp av = avma, btop;
  GEN ps, psum_sqr, P;
  long i, e, stabcnt, nprimes = lg(primes) - 1;

  if ((h & 1) && modinv_units(inv)) { *psum = gen_1; *d = 0; return; }
  e = -1;
  ps = cgetg(nprimes+1, t_VECSMALL);
  do {
    e += 2;
    for (i = 1; i <= nprimes; ++i)
    {
      GEN roots_modp = gel(roots, i);
      ulong p = uel(primes, i), pi = uel(pilist, i);
      uel(ps, i) = Flv_powsum_pre(roots_modp, e, p, pi);
    }
    btop = avma;
    psum_sqr = Z_init_CRT(0, 1);
    P = gen_1;
    for (i = 1, stabcnt = 0; stabcnt < MIN_STAB_CNT && i <= nprimes; ++i)
    {
      ulong p = uel(primes, i), pi = uel(pilist, i);
      ulong ps2 = Fl_sqr_pre(uel(ps, i), p, pi);
      ulong stab = Z_incremental_CRT(&psum_sqr, ps2, &P, p);
      /* stabcnt = stab * (stabcnt + 1) */
      if (stab) ++stabcnt; else stabcnt = 0;
      if (gc_needed(av, 2)) gerepileall(btop, 2, &psum_sqr, &P);
    }
    if (stabcnt == 0 && nprimes >= MIN_STAB_CNT)
      pari_err_BUG("polclass_psum");
  } while (!signe(psum_sqr));

  if ( ! Z_issquareall(psum_sqr, psum)) pari_err_BUG("polclass_psum");

  dbg_printf(1)("Classpoly power sum (e = %ld) is %Ps; found with %.2f%% of the primes\n",
      e, *psum, 100 * (i - 1) / (double) nprimes);
  *psum = gerepileupto(av, *psum);
  *d = e;
}

static GEN
polclass_small_disc(long D, long inv, long xvar)
{
  if (D == -3) return pol_x(xvar);
  if (D == -4) {
    switch (inv) {
    case INV_J: return deg1pol(gen_1, stoi(-1728), xvar);
    case INV_G2:return deg1pol(gen_1, stoi(-12), xvar);
    default: /* no other invariants for which we can calculate H_{-4}(X) */
      pari_err_BUG("polclass_small_disc");
    }
  }
  return NULL;
}

GEN
polclass0(long D, long inv, long xvar, GEN *db)
{
  pari_sp av = avma;
  GEN primes;
  long n_curves_tested = 0;
  long nprimes, s, i, j, del, ni, orient;
  GEN P, H, plist, pilist;
  ulong u, L, maxL, vfactors, biggest_v;
  long h, p1, p2, filter = 1;
  classgp_pcp_t G;
  double height;
  static const long k = 2;
  static const double delta = 0.5;

  if (D >= -4) return polclass_small_disc(D, inv, xvar);

  (void) corediscs(D, &u);
  h = classno_wrapper(D);

  dbg_printf(1)("D = %ld, conductor = %ld, inv = %ld\n", D, u, inv);

  ni = modinv_degree(&p1, &p2, inv);
  orient = modinv_is_double_eta(inv) && kross(D, p1) && kross(D, p2);

  classgp_make_pcp(G, &height, &ni, h, D, u, inv, filter, orient);
  primes = select_classpoly_primes(&vfactors, &biggest_v, k, delta, G, height);

  /* Prepopulate *db with all the modpolys we might need */
  /* TODO: Clean this up; in particular, note that u is factored later on. */
  /* This comes from L_bound in oneroot_of_classpoly() above */
  maxL = maxdd(log((double) -D), (double)biggest_v);
  if (u > 1) {
    for (L = 2; L <= maxL; L = unextprime(L + 1))
      if (!(u % L)) polmodular_db_add_level(db, L, INV_J);
  }
  for (i = 0; vfactors; ++i) {
    if (vfactors & 1UL)
      polmodular_db_add_level(db, SMALL_PRIMES[i], INV_J);
    vfactors >>= 1;
  }
  if (p1 > 1) polmodular_db_add_level(db, p1, INV_J);
  if (p2 > 1) polmodular_db_add_level(db, p2, INV_J);
  s = !!G->L0;
  polmodular_db_add_levels(db, G->L + s, G->k - s, inv);
  if (orient) {
    for (i = 0; i < G->k; ++i)
    {
      if (G->orient_p[i] > 1) polmodular_db_add_level(db, G->orient_p[i], inv);
      if (G->orient_q[i] > 1) polmodular_db_add_level(db, G->orient_q[i], inv);
    }
  }
  nprimes = lg(primes) - 1;
  H = cgetg(nprimes + 1, t_VEC);
  plist = cgetg(nprimes + 1, t_VECSMALL);
  pilist = cgetg(nprimes + 1, t_VECSMALL);
  for (i = 1; i <= nprimes; ++i) {
    long rho_inv = gel(primes, i)[4];
    norm_eqn_t ne;
    setup_norm_eqn(ne, D, u, gel(primes, i));

    gel(H, i) = polclass_roots_modp(&n_curves_tested, ne, rho_inv, G, *db);
    uel(plist, i) = ne->p;
    uel(pilist, i) = ne->pi;
    if (DEBUGLEVEL>2 && (i & 3L)==0) err_printf(" %ld%%", i*100/nprimes);
  }
  dbg_printf(0)("\n");

  if (orient) {
    GEN nvec = new_chunk(G->k);
    GEN fdb = polmodular_db_for_inv(*db, inv);
    GEN F = double_eta_raw(inv);
    index_to_evec((long *)nvec, ni, G->m, G->k);
    for (i = 1; i <= nprimes; ++i) {
      GEN v = gel(H, i);
      ulong p = uel(plist, i), pi = uel(pilist, i);
      long oni = oriented_n_action(nvec, G, v, p, pi, fdb);
      adjust_orientation(F, inv, v, oni + 1, p, pi);
    }
  }

  if (modinv_has_sign_ambiguity(inv)) {
    GEN psum;
    long e;
    polclass_psum(&psum, &e, H, plist, pilist, h, inv);
    for (i = 1; i <= nprimes; ++i) {
      GEN v = gel(H, i);
      ulong p = uel(plist, i), pi = uel(pilist, i);
      if (!adjust_signs(v, p, pi, inv, psum, e))
        uel(plist, i) = 0;
    }
  }

  for (i = 1, j = 1, del = 0; i <= nprimes; ++i) {
    GEN v = gel(H, i), pol;
    ulong p = uel(plist, i);
    if (!p) { del++; continue; }
    pol = Flv_roots_to_pol(v, p, xvar);
    uel(plist, j) = p;
    gel(H, j++) = Flx_to_Flv(pol, lg(pol) - 2);
  }
  setlg(H,nprimes+1-del);
  setlg(plist,nprimes+1-del);
  classgp_pcp_clear(G);

  dbg_printf(1)("Total number of curves tested: %ld\n", n_curves_tested);
  H = ncV_chinese_center(H, plist, &P);
  dbg_printf(1)("Result height: %.2f\n",
             dbllog2r(itor(gsupnorm(H, DEFAULTPREC), DEFAULTPREC)));
  return gerepilecopy(av, RgV_to_RgX(H, xvar));
}

void
check_modinv(long inv)
{
  switch (inv) {
  case INV_J:
  case INV_F:
  case INV_F2:
  case INV_F3:
  case INV_F4:
  case INV_G2:
  case INV_W2W3:
  case INV_F8:
  case INV_W3W3:
  case INV_W2W5:
  case INV_W2W7:
  case INV_W3W5:
  case INV_W3W7:
  case INV_W2W3E2:
  case INV_W2W5E2:
  case INV_W2W13:
  case INV_W2W7E2:
  case INV_W3W3E2:
  case INV_W5W7:
  case INV_W3W13:
    break;
  default:
    pari_err_DOMAIN("polmodular", "inv", "invalid invariant", stoi(inv), gen_0);
  }
}

GEN
polclass(GEN DD, long inv, long xvar)
{
  GEN db, H;
  long dummy, D;

  if (xvar < 0) xvar = 0;
  check_quaddisc_imag(DD, &dummy, "polclass");
  check_modinv(inv);

  D = itos(DD);
  if (!modinv_good_disc(inv, D))
    pari_err_DOMAIN("polclass", "D", "incompatible with given invariant", stoi(inv), DD);

  db = polmodular_db_init(inv);
  H = polclass0(D, inv, xvar, &db);
  gunclone_deep(db); return H;
}
