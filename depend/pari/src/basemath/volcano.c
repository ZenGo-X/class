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

/* FIXME: Implement {ascend,descend}_volcano() in terms of the "new"
 * volcano traversal functions at the bottom of the file. */

/* Is j = 0 or 1728 (mod p)? */
INLINE int
is_j_exceptional(ulong j, ulong p) { return j == 0 || j == 1728 % p; }

INLINE long
node_degree(GEN phi, long L, ulong j, ulong p, ulong pi)
{
  pari_sp av = avma;
  long n = Flx_nbroots(Flm_Fl_polmodular_evalx(phi, L, j, p, pi), p);
  avma = av; return n;
}

/* Given an array path = [j0, j1] of length 2, return the polynomial
 *
 *   \Phi_L(X, j1) / (X - j0)
 *
 * where \Phi_L(X, Y) is the modular polynomial of level L.  An error
 * is raised if X - j0 does not divide \Phi_L(X, j1) */
INLINE GEN
nhbr_polynomial(ulong path[], GEN phi, ulong p, ulong pi, long L)
{
  pari_sp ltop = avma;
  GEN modpol = Flm_Fl_polmodular_evalx(phi, L, path[0], p, pi);
  ulong rem;
  GEN nhbr_pol = Flx_div_by_X_x(modpol, path[-1], p, &rem);
  /* If disc End(path[0]) <= L^2, it's possible for path[0] to appear among the
   * roots of nhbr_pol. This should have been obviated by earlier choices */
  if (rem) pari_err_BUG("nhbr_polynomial: invalid preceding j");
  return gerepileupto(ltop, nhbr_pol);
}

/* Path is an array with space for at least max_len+1 * elements, whose first
 * and second elements are the beginning of the path.  I.e., the path starts
 *   (path[0], path[1])
 * If the result is less than max_len, then the last element of path is on the
 * floor.  If the result equals max_len, then it is unknown whether the last
 * element of path is on the floor or not */
static long
extend_path(ulong path[], GEN phi, ulong p, ulong pi, long L, long max_len)
{
  pari_sp av = avma;
  long d = 1;
  for ( ; d < max_len; d++)
  {
    GEN nhbr_pol = nhbr_polynomial(path + d, phi, p, pi, L);
    ulong nhbr = Flx_oneroot(nhbr_pol, p);
    avma = av;
    if (nhbr == p) break; /* no root: we are on the floor. */
    path[d+1] = nhbr;
  }
  return d;
}

/* This is Sutherland 2009 Algorithm Ascend (p12) */
ulong
ascend_volcano(GEN phi, ulong j, ulong p, ulong pi, long level, long L,
  long depth, long steps)
{
  pari_sp ltop = avma, av;
  /* path will never hold more than max_len < depth elements */
  GEN path_g = cgetg(depth + 2, t_VECSMALL);
  ulong *path = zv_to_ulongptr(path_g);
  long max_len = depth - level;
  int first_iter = 1;

  if (steps <= 0 || max_len < 0) pari_err_BUG("ascend_volcano: bad params");
  av = avma;
  while (steps--)
  {
    GEN nhbr_pol = first_iter? Flm_Fl_polmodular_evalx(phi, L, j, p, pi)
                             : nhbr_polynomial(path+1, phi, p, pi, L);
    GEN nhbrs = Flx_roots(nhbr_pol, p);
    long nhbrs_len = lg(nhbrs)-1, i;
    pari_sp btop = avma;
    path[0] = j;
    first_iter = 0;

    j = nhbrs[nhbrs_len];
    for (i = 1; i < nhbrs_len; i++)
    {
      ulong next_j = nhbrs[i], last_j;
      long len;
      if (is_j_exceptional(next_j, p))
      {
        /* Fouquet & Morain, Section 4.3, if j = 0 or 1728, then it is on the
         * surface.  So we just return it. */
        if (steps)
          pari_err_BUG("ascend_volcano: Got to the top with more steps to go!");
        j = next_j; break;
      }
      path[1] = next_j;
      len = extend_path(path, phi, p, pi, L, max_len);
      last_j = path[len];
      if (len == max_len
          /* Ended up on the surface */
          && (is_j_exceptional(last_j, p)
              || node_degree(phi, L, last_j, p, pi) > 1)) { j = next_j; break; }
      avma = btop;
    }
    path[1] = j; /* For nhbr_polynomial() at the top. */

    max_len++; avma = av;
  }
  avma = ltop; return j;
}

static void
random_distinct_neighbours_of(ulong *nhbr1, ulong *nhbr2,
  GEN phi, ulong j, ulong p, ulong pi, long L, long must_have_two_neighbours)
{
  pari_sp av = avma;
  GEN modpol = Flm_Fl_polmodular_evalx(phi, L, j, p, pi);
  ulong rem;
  *nhbr1 = Flx_oneroot(modpol, p);
  if (*nhbr1 == p) pari_err_BUG("random_distinct_neighbours_of [no neighbour]");
  modpol = Flx_div_by_X_x(modpol, *nhbr1, p, &rem);
  *nhbr2 = Flx_oneroot(modpol, p);
  if (must_have_two_neighbours && *nhbr2 == p)
    pari_err_BUG("random_distinct_neighbours_of [single neighbour]");
  avma = av;
}


/*
 * This is Sutherland 2009 Algorithm Descend (p12).
 */
ulong
descend_volcano(GEN phi, ulong j, ulong p, ulong pi,
  long level, long L, long depth, long steps)
{
  pari_sp ltop = avma;
  GEN path_g;
  ulong *path, res;
  long max_len;

  if (steps <= 0 || level + steps > depth) pari_err_BUG("descend_volcano");
  max_len = depth - level;
  path_g = cgetg(max_len + 1 + 1, t_VECSMALL);
  path = zv_to_ulongptr(path_g);
  path[0] = j;
  /* level = 0 means we're on the volcano surface... */
  if (!level)
  {
    /* Look for any path to the floor. One of j's first three neighbours leads
     * to the floor, since at most two neighbours are on the surface. */
    GEN nhbrs = Flx_roots(Flm_Fl_polmodular_evalx(phi, L, j, p, pi), p);
    long i;
    for (i = 1; i <= 3; i++)
    {
      long len;
      path[1] = nhbrs[i];
      len = extend_path(path, phi, p, pi, L, max_len);
      /* If nhbrs[i] took us to the floor: */
      if (len < max_len || node_degree(phi, L, path[len], p, pi) == 1) break;
    }
    if (i > 3) pari_err_BUG("descend_volcano [2]");
  }
  else
  {
    ulong nhbr1, nhbr2;
    long len;
    random_distinct_neighbours_of(&nhbr1, &nhbr2, phi, j, p, pi, L, 1);
    path[1] = nhbr1;
    len = extend_path(path, phi, p, pi, L, max_len);
    /* If last j isn't on the floor */
    if (len == max_len   /* Ended up on the surface. */
        && (is_j_exceptional(path[len], p)
            || node_degree(phi, L, path[len], p, pi) != 1)) {
      /* The other neighbour leads to the floor */
      path[1] = nhbr2;
      (void) extend_path(path, phi, p, pi, L, steps);
    }
  }
  res = path[steps]; avma = ltop; return res;
}


long
j_level_in_volcano(
  GEN phi, ulong j, ulong p, ulong pi, long L, long depth)
{
  pari_sp av = avma;
  GEN chunk;
  ulong *path1, *path2;
  long lvl;

  /* Fouquet & Morain, Section 4.3, if j = 0 or 1728 then it is on the
   * surface.  Also, if the volcano depth is zero then j has level 0 */
  if (depth == 0 || is_j_exceptional(j, p)) return 0;

  chunk = new_chunk(2 * (depth + 1));
  path1 = (ulong *) &chunk[0];
  path2 = (ulong *) &chunk[depth + 1];
  path1[0] = path2[0] = j;
  random_distinct_neighbours_of(&path1[1], &path2[1], phi, j, p, pi, L, 0);
  if (path2[1] == p)
    lvl = depth; /* Only one neighbour => j is on the floor => level = depth */
   else
   {
    long path1_len = extend_path(path1, phi, p, pi, L, depth);
    long path2_len = extend_path(path2, phi, p, pi, L, path1_len);
    lvl = depth - path2_len;
  }
  avma = av; return lvl;
}

#define vecsmall_len(v) (lg(v) - 1)

INLINE GEN
Flx_remove_root(GEN f, ulong a, ulong p)
{
  ulong r;
  GEN g = Flx_div_by_X_x(f, a, p, &r);
  if (r) pari_err_BUG("Flx_remove_root");
  return g;
}

INLINE GEN
get_nbrs(GEN phi, long L, ulong J, const ulong *xJ, ulong p, ulong pi)
{
  pari_sp av = avma;
  GEN f = Flm_Fl_polmodular_evalx(phi, L, J, p, pi);
  if (xJ) f = Flx_remove_root(f, *xJ, p);
  return gerepileupto(av, Flx_roots(f, p));
}

/* Return a path of length n along the surface of an L-volcano of height h
 * starting from surface node j0.  Assumes (D|L) = 1 where D = disc End(j0).
 *
 * Actually, if j0's endomorphism ring is a suborder, we return the
 * corresponding shorter path. W must hold space for n + h nodes.
 *
 * TODO: have two versions of this function: one that assumes J has the correct
 * endomorphism ring (hence avoiding several branches in the inner loop) and a
 * second that does not and accordingly checks for repetitions */
static long
surface_path(
  ulong W[],
  long n, GEN phi, long L, long h, ulong J, const ulong *nJ, ulong p, ulong pi)
{
  pari_sp av = avma, bv;
  GEN T, v;
  long j, k, w, x;
  ulong W0;

  W[0] = W0 = J;
  if (n == 1) return 1;

  T = cgetg(h+2, t_VEC); bv = avma;
  v = get_nbrs(phi, L, J, nJ, p, pi);
  /* Insert known neighbour first */
  if (nJ) v = gerepileupto(bv, vecsmall_prepend(v, *nJ));
  gel(T,1) = v;
  k = vecsmall_len(v);

  switch (k) {
  case 0: pari_err_BUG("surface_path"); /* We must always have neighbours */
  case 1:
    /* If volcano is not flat, then we must have more than one neighbour */
    if (h) pari_err_BUG("surface_path");
    W[1] = uel(v, 1);
    avma = av;
    /* Check for bad endo ring */
    if (W[1] == W[0]) return 1;
    return 2;
  case 2:
    /* If L=2 the only way we can have 2 neighbours is if we have a double root
     * which can only happen for |D| <= 16 (Thm 2.2 of Fouquet-Morain)
     * and if it does we must have a 2-cycle. Happens for D=-15. */
    if (L == 2)
    { /* The double root is the neighbour on the surface, with exactly one
       * neighbour other than J; the other neighbour of J has either 0 or 2
       * neighbours that are not J */
      GEN u = get_nbrs(phi, L, uel(v, 1), &J, p, pi);
      long n = vecsmall_len(u) - !!vecsmall_isin(u, J);
      W[1] = n == 1 ? uel(v,1) : uel(v,2);
      avma = av; return 2;
    }
    /* Volcano is not flat but found only 2 neighbours for the surface node J */
    if (h) pari_err_BUG("surface_path");

    W[1] = uel(v,1); /* TODO: Can we use the other root uel(v,2) somehow? */
    for (w = 2; w < n; w++)
    {
      v = get_nbrs(phi, L, W[w-1], &W[w-2], p, pi);
      /* A flat volcano must have exactly one non-previous neighbour */
      if (vecsmall_len(v) != 1) pari_err_BUG("surface_path");
      W[w] = uel(v, 1);
      /* Detect cycle in case J doesn't have the right endo ring. */
      avma = av; if (W[w] == W0) return w;
    }
    avma = av; return n;
  }
  if (!h) pari_err_BUG("surface_path"); /* Can't have a flat volcano if k > 2 */

  /* At this point, each surface node has L+1 distinct neighbours, 2 of which
   * are on the surface */
  w = 1;
  for (x = 0;; x++)
  {
    /* Get next neighbour of last known surface node to attempt to
     * extend the path. */
    W[w] = umael(T, ((w-1) % h) + 1, x + 1);

    /* Detect cycle in case the given J didn't have the right endo ring */
    if (W[w] == W0) { avma = av; return w; }

    /* If we have to test the last neighbour, we know it's on the
     * surface, and if we're done there's no need to extend. */
    if (x == k-1 && w == n-1) { avma = av; return n; }

    /* Walk forward until we hit the floor or finish. */
    /* NB: We don't keep the stack clean here; usage is in the order of Lh,
     * i.e. L roots for each level of the volcano of height h. */
    for (j = w;;)
    {
      long m;
      /* We must get 0 or L neighbours here. */
      v = get_nbrs(phi, L, W[j], &W[j-1], p, pi);
      m = vecsmall_len(v);
      if (!m) {
        /* We hit the floor: save the neighbours of W[w-1] and dump the rest */
        GEN nbrs = gel(T, ((w-1) % h) + 1);
        gel(T, ((w-1) % h) + 1) = gerepileupto(bv, nbrs);
        break;
      }
      if (m != L) pari_err_BUG("surface_path");

      gel(T, (j % h) + 1) = v;

      W[++j] = uel(v, 1);
      /* If we have our path by h nodes, we know W[w] is on the surface */
      if (j == w + h) {
        ++w;
        /* Detect cycle in case the given J didn't have the right endo ring */
        if (W[w] == W0) { avma = av; return w; }
        x = 0; k = L;
      }
      if (w == n) { avma = av; return w; }
    }
  }
}

long
next_surface_nbr(
  ulong *nJ,
  GEN phi, long L, long h, ulong J, const ulong *pJ, ulong p, ulong pi)
{
  pari_sp av = avma, bv;
  GEN S;
  ulong *P;
  long i, k;

  S = get_nbrs(phi, L, J, pJ, p, pi);
  k = vecsmall_len(S);
  /* If there is a double root and pJ is set, then k will be zero. */
  if (!k) { avma = av; return 0; }
  if (k == 1 || ( ! pJ && k == 2)) { *nJ = uel(S, 1); avma = av; return 1; }
  if (!h) pari_err_BUG("next_surface_nbr");

  P = (ulong *) new_chunk(h + 1); bv = avma;
  P[0] = J;
  for (i = 0; i < k; i++)
  {
    long j;
    P[1] = uel(S, i + 1);
    for (j = 1; j <= h; j++)
    {
      GEN T = get_nbrs(phi, L, P[j], &P[j - 1], p, pi);
      if (!vecsmall_len(T)) break;
      P[j + 1] = uel(T, 1);
    }
    if (j < h) pari_err_BUG("next_surface_nbr");
    avma = bv; if (j > h) break;
  }
  /* TODO: We could save one get_nbrs call by iterating from i up to k-1 and
   * assume that the last (kth) nbr is the one we want. For now we're careful
   * and check that this last nbr really is on the surface */
  if (i == k) pari_err_BUG("next_surf_nbr");
  *nJ = uel(S, i+1); avma = av; return 1;
}

/* Return the number of distinct neighbours (1 or 2) */
INLINE long
common_nbr(ulong *nbr,
  ulong J1, GEN Phi1, long L1,
  ulong J2, GEN Phi2, long L2, ulong p, ulong pi)
{
  pari_sp av = avma;
  GEN d, f, g, r;
  long rlen;

  g = Flm_Fl_polmodular_evalx(Phi1, L1, J1, p, pi);
  f = Flm_Fl_polmodular_evalx(Phi2, L2, J2, p, pi);
  d = Flx_gcd(f, g, p);
  if (degpol(d) == 1) { *nbr = Flx_deg1_root(d, p); avma = av; return 1; }
  if (degpol(d) != 2) pari_err_BUG("common_neighbour");
  r = Flx_roots(d, p);
  rlen = vecsmall_len(r);
  if (!rlen) pari_err_BUG("common_neighbour");
  /* rlen is 1 or 2 depending on whether the root is unique or not. */
  nbr[0] = uel(r, 1);
  nbr[1] = uel(r, rlen); avma = av; return rlen;
}

/* Return gcd(Phi1(X,J1)/(X - J0), Phi2(X,J2)). Not stack clean. */
INLINE GEN
common_nbr_pred_poly(
  ulong J1, GEN Phi1, long L1,
  ulong J2, GEN Phi2, long L2, ulong J0, ulong p, ulong pi)
{
  GEN f, g;

  g = Flm_Fl_polmodular_evalx(Phi1, L1, J1, p, pi);
  g = Flx_remove_root(g, J0, p);
  f = Flm_Fl_polmodular_evalx(Phi2, L2, J2, p, pi);
  return Flx_gcd(f, g, p);
}

/* Find common neighbour of J1 and J2, where J0 is an L1 predecessor of J1.
 * Return 1 if successful, 0 if not. */
INLINE int
common_nbr_pred(ulong *nbr,
  ulong J1, GEN Phi1, long L1,
  ulong J2, GEN Phi2, long L2, ulong J0, ulong p, ulong pi)
{
  pari_sp av = avma;
  GEN d = common_nbr_pred_poly(J1, Phi1, L1, J2, Phi2, L2, J0, p, pi);
  int res = (degpol(d) == 1);
  if (res) *nbr = Flx_deg1_root(d, p);
  avma = av; return res;
}

INLINE long
common_nbr_verify(ulong *nbr,
  ulong J1, GEN Phi1, long L1,
  ulong J2, GEN Phi2, long L2, ulong J0, ulong p, ulong pi)
{
  pari_sp av = avma;
  GEN d = common_nbr_pred_poly(J1, Phi1, L1, J2, Phi2, L2, J0, p, pi);

  if (!degpol(d)) { avma = av; return 0; }
  if (degpol(d) > 1) pari_err_BUG("common_neighbour_verify");
  *nbr = Flx_deg1_root(d, p);
  avma = av; return 1;
}

INLINE ulong
Flm_Fl_polmodular_evalxy(GEN Phi, long L, ulong x, ulong y, ulong p, ulong pi)
{
  pari_sp av = avma;
  GEN f = Flm_Fl_polmodular_evalx(Phi, L, x, p, pi);
  ulong r = Flx_eval_pre(f, y, p, pi);
  avma = av; return r;
}

/* Find a common L1-neighbor of J1 and L2-neighbor of J2, given J0 an
 * L2-neighbor of J1 and an L1-neighbor of J2. Return 1 if successful, 0
 * otherwise. Will only fail if initial J-invariant had the wrong endo ring */
INLINE int
common_nbr_corner(ulong *nbr,
  ulong J1, GEN Phi1, long L1, long h1,
  ulong J2, GEN Phi2, long L2, ulong J0, ulong p, ulong pi)
{
  ulong nbrs[2];
  if (common_nbr(nbrs, J1,Phi1,L1, J2,Phi2,L2, p, pi) == 2)
  {
    ulong nJ1, nJ2;
    if (!next_surface_nbr(&nJ2, Phi1, L1, h1, J2, &J0, p, pi) ||
        !next_surface_nbr(&nJ1, Phi1, L1, h1, nbrs[0], &J1, p, pi)) return 0;

    if (Flm_Fl_polmodular_evalxy(Phi2, L2, nJ1, nJ2, p, pi))
      nbrs[0] = nbrs[1];
    else if (!next_surface_nbr(&nJ1, Phi1, L1, h1, nbrs[1], &J1, p, pi) ||
             !Flm_Fl_polmodular_evalxy(Phi2, L2, nJ1, nJ2, p, pi)) return 0;
  }
  *nbr = nbrs[0]; return 1;
}

/* Enumerate a surface L1-cycle using gcds with Phi_L2, where c_L2=c_L1^e and
 * |c_L1|=n, where c_a is the class of the pos def reduced primeform <a,b,c>.
 * Assumes n > e > 1 and roots[0],...,roots[e-1] are already present in W */
static long
surface_gcd_cycle(
  ulong W[], ulong V[], long n,
  GEN Phi1, long L1, GEN Phi2, long L2, long e, ulong p, ulong pi)
{
  pari_sp av = avma;
  long i1, i2, j1, j2;

  i1 = j2 = 0;
  i2 = j1 = e - 1;
  /* If W != V we assume V actually points to an L2-isogenous parallel L1-path.
   * e should be 2 in this case */
  if (W != V) { i1 = j1+1; i2 = n-1; }
  do {
    ulong t0, t1, t2, h10, h11, h20, h21;
    long k;
    GEN f, g, h1, h2;

    f = Flm_Fl_polmodular_evalx(Phi2, L2, V[i1], p, pi);
    g = Flm_Fl_polmodular_evalx(Phi1, L1, W[j1], p, pi);
    g = Flx_remove_root(g, W[j1 - 1], p);
    h1 = Flx_gcd(f, g, p);
    if (degpol(h1) != 1) break; /* Error */
    h11 = Flx_coeff(h1, 1);
    h10 = Flx_coeff(h1, 0); avma = av;

    f = Flm_Fl_polmodular_evalx(Phi2, L2, V[i2], p, pi);
    g = Flm_Fl_polmodular_evalx(Phi1, L1, W[j2], p, pi);
    k = j2 + 1;
    if (k == n) k = 0;
    g = Flx_remove_root(g, W[k], p);
    h2 = Flx_gcd(f, g, p);
    if (degpol(h2) != 1) break; /* Error */
    h21 = Flx_coeff(h2, 1);
    h20 = Flx_coeff(h2, 0); avma = av;

    i1++; i2--; if (i2 < 0) i2 = n-1;
    j1++; j2--; if (j2 < 0) j2 = n-1;

    t0 = Fl_mul_pre(h11, h21, p, pi);
    t1 = Fl_inv(t0, p);
    t0 = Fl_mul_pre(t1, h21, p, pi);
    t2 = Fl_mul_pre(t0, h10, p, pi);
    W[j1] = Fl_neg(t2, p);
    t0 = Fl_mul_pre(t1, h11, p, pi);
    t2 = Fl_mul_pre(t0, h20, p, pi);
    W[j2] = Fl_neg(t2, p);
  } while (j2 > j1 + 1);
  /* Usually the loop exits when j2 = j1 + 1, in which case we return n.
   * If we break early because of an error, then (j2 - (j1+1)) > 0 is the
   * number of elements we haven't calculated yet, and we return n minus that
   * quantity */
  avma = av; return n - j2 + (j1 + 1);
}

static long
surface_gcd_path(
  ulong W[], ulong V[], long n,
  GEN Phi1, long L1, GEN Phi2, long L2, long e, ulong p, ulong pi)
{
  pari_sp av = avma;
  long i, j;

  i = 0; j = e;
  /* If W != V then assume V actually points to a L2-isogenous
   * parallel L1-path.  e should be 2 in this case */
  if (W != V) i = j;
  while (j < n)
  {
    GEN f, g, d;

    f = Flm_Fl_polmodular_evalx(Phi2, L2, V[i], p, pi);
    g = Flm_Fl_polmodular_evalx(Phi1, L1, W[j - 1], p, pi);
    g = Flx_remove_root(g, W[j - 2], p);
    d = Flx_gcd(f, g, p);
    if (degpol(d) != 1) break; /* Error */
    W[j] = Flx_deg1_root(d, p);
    i++; j++; avma = av;
  }
  avma = av; return j;
}

/* Given a path V of length n on an L1-volcano, and W[0] L2-isogenous to V[0],
 * extends the path W to length n on an L1-volcano, with W[i] L2-isogenous
 * to V[i]. Uses gcds unless L2 is too large to make it helpful. Always uses
 * GCD to get W[1] to ensure consistent orientation.
 *
 * Returns the new length of W. This will almost always be n, but could be
 * lower if V was started with a J-invariant with bad endomorphism ring */
INLINE long
surface_parallel_path(
  ulong W[], ulong V[], long n,
  GEN Phi1, long L1, GEN Phi2, long L2, ulong p, ulong pi, long cycle)
{
  ulong W2, nbrs[2];
  if (common_nbr(nbrs, W[0], Phi1, L1, V[1], Phi2, L2, p, pi) == 2)
  {
    if (n <= 2) return 1; /* Error: Two choices with n = 2; ambiguous */
    if (!common_nbr_verify(&W2,nbrs[0], Phi1,L1,V[2], Phi2,L2,W[0], p,pi))
      nbrs[0] = nbrs[1]; /* nbrs[1] must be the correct choice */
    else if (common_nbr_verify(&W2,nbrs[1], Phi1,L1,V[2], Phi2,L2,W[0], p,pi))
      return 1; /* Error: Both paths extend successfully */
  }
  W[1] = nbrs[0];
  if (n <= 2) return n;
  return cycle? surface_gcd_cycle(W, V, n, Phi1, L1, Phi2, L2, 2, p, pi)
              : surface_gcd_path (W, V, n, Phi1, L1, Phi2, L2, 2, p, pi);
}

GEN
enum_roots(ulong J0, norm_eqn_t ne, GEN fdb, classgp_pcp_t G)
{
  /* MAX_HEIGHT >= max_{p,n} val_p(n) where p and n are ulongs */
  enum { MAX_HEIGHT = BITS_IN_LONG };
  pari_sp av, ltop = avma;
  long s = !!G->L0;
  long *n = G->n + s, *L = G->L + s, *o = G->o + s, k = G->k - s;
  long i, t, vlen, *e, *h, *off, *poff, *M, N = G->enum_cnt;
  ulong p = ne->p, pi = ne->pi, *roots;
  GEN Phi, vshape, vp, ve, roots_;

  if (!k) return mkvecsmall(J0);

  roots_ = cgetg(N + MAX_HEIGHT, t_VECSMALL);
  roots = zv_to_ulongptr(roots_);
  av = avma;

  /* TODO: Shouldn't be factoring this every time. Store in *ne? */
  vshape = factoru(ne->v);
  vp = gel(vshape, 1);
  ve = gel(vshape, 2);

  vlen = vecsmall_len(vp);
  Phi = new_chunk(k);
  e = new_chunk(k);
  off = new_chunk(k);
  poff = new_chunk(k);
  /* TODO: Surely we can work these out ahead of time? */
  /* h[i] is the valuation of p[i] in v */
  h = new_chunk(k);
  for (i = 0; i < k; ++i) {
    h[i] = 0;
    for (t = 1; t <= vlen; ++t)
      if (vp[t] == L[i]) { h[i] = uel(ve, t); break; }
    e[i] = 0;
    off[i] = 0;
    gel(Phi, i) = polmodular_db_getp(fdb, L[i], p);
  }

  M = new_chunk(k);
  for (M[0] = 1, i = 1; i < k; ++i) M[i] = M[i-1] * n[i-1];

  t = surface_path(roots, n[0], gel(Phi, 0), L[0], h[0], J0, NULL, p, pi);
  /* Error: J0 has bad endo ring */
  if (t < n[0]) { avma = ltop; return NULL; }
  if (k == 1) { avma = av; setlg(roots_, t + 1); return roots_; }

  i = 1;
  while (i < k) {
    long j, t0;
    for (j = i + 1; j < k && ! e[j]; ++j);
    if (j < k) {
      if (e[i]) {
        if (! common_nbr_pred(
              &roots[t], roots[off[i]], gel(Phi,i), L[i],
              roots[t - M[j]], gel(Phi, j), L[j], roots[poff[i]], p, pi)) {
          break; /* Error: J0 has bad endo ring */
        }
      } else if ( ! common_nbr_corner(
            &roots[t], roots[off[i]], gel(Phi,i), L[i], h[i],
            roots[t - M[j]], gel(Phi, j), L[j], roots[poff[j]], p, pi)) {
        break; /* Error: J0 has bad endo ring */
      }
    } else if ( ! next_surface_nbr(
          &roots[t], gel(Phi,i), L[i], h[i],
          roots[off[i]], e[i] ? &roots[poff[i]] : NULL, p, pi))
      break; /* Error: J0 has bad endo ring */
    if (roots[t] == roots[0]) break; /* Error: J0 has bad endo ring */

    poff[i] = off[i];
    off[i] = t;
    e[i]++;
    for (j = i-1; j; --j) { e[j] = 0; off[j] = off[j+1]; }

    t0 = surface_parallel_path(&roots[t], &roots[poff[i]], n[0],
        gel(Phi, 0), L[0], gel(Phi, i), L[i], p, pi, n[0] == o[0]);
    if (t0 < n[0]) break; /* Error: J0 has bad endo ring */

    /* TODO: Do I need to check if any of the new roots is a repeat in
     * the case where J0 has bad endo ring? */
    t += n[0];
    for (i = 1; i < k && e[i] == n[i]-1; i++);
  }
  /* Check if J0 had wrong endo ring */
  if (t != N) { avma = ltop; return NULL; }
  avma = av; setlg(roots_, t + 1); return roots_;
}
