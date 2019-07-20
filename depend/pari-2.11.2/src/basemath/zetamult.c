/* Copyright (C) 2000  The PARI group.
This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/********************************************************************/
/**                                                                **/
/**             MULTIPLE ZETA VALUES (AKHILESH ALGORITHM)          **/
/**                                                                **/
/********************************************************************/
#include "pari.h"
#include "paripriv.h"

static long
la(long e, long f) { return (e == f)? 2: (e? 1: 3); }
static GEN
lamul(long la, GEN s)
{
  switch(la)
  {
    case 2: return gmul2n(s,1);
    case 3: return gmulgs(s,3);
    default: return s;
  }
}

/* dual of evec[1..l-1] */
static GEN
revslice(GEN evec, long l)
{
  GEN res = cgetg(l, t_VECSMALL);
  long i;
  for (i = 1; i < l; ++i) res[i] = 1 - evec[l-i];
  return res;
}

/* N.B. evec[ne] = 1 */
static GEN
etoa(GEN evec)
{
  long ct = 0, ctold = 0, i = 1, le = lg(evec);
  GEN avec = cgetg(le, t_VECSMALL);
  while (++ct < le)
    if (evec[ct] == 1) { avec[i++] = ct - ctold; ctold = ct; }
  setlg(avec, i); return avec;
}

static GEN
atoe(GEN avec)
{
  long i, l = lg(avec);
  GEN evec = cgetg(l, t_VEC);
  for (i = 1; i < l; i++) { long a = avec[i]; gel(evec,i) = vecsmall_ei(a,a); }
  return shallowconcat1(evec);
}

/* vphi[i] contains phip(j,avec[i..r]) for 1<= j < L
 * vpow[a][j] = j^-a as a t_INT or t_REAL; j < L */
static GEN
phip(GEN avec, GEN vpow)
{
  long i, r = lg(avec) - 1;
  GEN vphi = cgetg(r+1, t_VEC);
  gel(vphi, r) = gel(vpow, avec[r]);
  for (i = r-1; i >= 1; i--)
  {
    GEN t, u, phi = gel(vphi,i+1), pow = gel(vpow, avec[i]);
    long j, L = lg(pow);
    gel(vphi, i) = u = cgetg(L, t_VEC);
    gel(u,1) = gen_0;
    gel(u,2) = (i==r-1)? gel(pow,2): gen_0;
    t = gel(phi,1); /* 0 or 1 */
    for (j = 3; j < L; j++)
    {
      t = mpadd(t, gel(phi,j-1));
      gel(u,j) = mpmul(t, gel(pow,j)); /* t / j^avec[i] */
    }
  }
  return vphi;
}

/* Return 1 if vec2 RHS of vec1, -1 if vec1 RHS of vec2, 0 else */
static long
isrhs(GEN v1, GEN v2)
{
  long s = 1, i, l1 = lg(v1), l2 = lg(v2);
  if (l1 < l2) { s = -1; swap(v1,v2); lswap(l1,l2); }
  for (i = l2-1; i >= 1; --i)
    if (v2[i] != v1[l1-l2+i]) return 0;
  return s;
}

static long
istruerhs(GEN v1, GEN v2)
{
  long i, l1 = lg(v1), l2 = lg(v2);
  if (l1 < l2) return 0;
  for (i = l2-1; i >= 1; --i)
    if (v2[i] != v1[l1-l2+i]) return 0;
  return l1-l2+1;
}

/* a is a rhs of a unique v[m] */
static GEN
isinphi(GEN v, GEN a, GEN vphi)
{
  long m, l = lg(v);
  for (m = 1; m < l; m++)
  {
    long s = istruerhs(gel(v,m), a);
    if (s) return gmael(vphi,m,s);
  }
  return NULL; /* LCOV_EXCL_LINE */
}

/* If v RHS of LR[i] for some i, return LR. If LR[i] RHS (strict) of v, replace
 * LR[i] by v. If none, add v to LR. */
static GEN
addevec(GEN LR, GEN v)
{
  long s, i, l1 = lg(LR);
  for (i = 1; i < l1; i++)
  {
    s = isrhs(gel(LR,i), v);
    if (s == 1) return LR;
    if (s ==-1) { gel(LR,i) = v; return LR; }
  }
  return vec_append(LR,v);
}

/* N > 2 */
static GEN
get_vbin(long N, long prec)
{
  GEN v = cgetg(N+1, t_VEC);
  long n;
  gel(v,1) = gen_0; /* unused */
  gel(v,2) = invr(utor(6,prec));
  for (n = 3; n <= N; n++) gel(v,n) = divru(mulru(gel(v,n-1), n), 4*n-2);
  return v;
}
/* m < k */
static GEN
zetamultinit_i(long k, long m, long bitprec)
{
  long i, N, prec;
  GEN vpow = cgetg(m+1, t_VEC);

  bitprec += 64*(1+(k>>5));
  prec = nbits2prec(bitprec);
  N = 5 + bitprec/2;
  gel(vpow,1) = vecpowug(N, gen_m1, prec);
  for (i = 2; i <= m; i++)
  {
    GEN pow = cgetg(N+1, t_VEC), powm = gel(vpow,i-1);
    long j;
    gel(pow,1) = gen_1;
    gel(pow,2) = real2n(-i, prec);
    for (j = 3; j <= N; j++) gel(pow,j) = divru(gel(powm,j), j);
    gel(vpow,i) = pow;
  }
  return mkvec2(vpow, get_vbin(N, prec));
}
GEN
zetamultinit(long k, long prec)
{
  pari_sp av = avma;
  if (k <= 0) pari_err_DOMAIN("zetamultinit", "weight", "<=", gen_0, stoi(k));
  return gerepilecopy(av, zetamultinit_i(k, k-1, prec2nbits(prec)));
}
GEN
zetamult0(GEN avec, GEN T, long prec)
{
  pari_sp ltop = avma;
  long k, n, i, j, l, lbin;
  GEN vpow, vphi, vbin, S, s, LR, MA, MR, evec = gen_0;

  avec = zetamultconvert(avec, 1);
  if (lg(avec) == 1) return gen_1;
  evec = atoe(avec);
  k = lg(evec)-1; /* weight */
  LR = cgetg(1, t_VEC);
  MA = cgetg(k, t_VEC);
  MR = cgetg(k, t_VEC);
  for (i = 1; i < k; ++i)
  {
    gel(MA,i) = etoa(revslice(evec, i+1));
    gel(MR,i) = etoa(vecslice(evec, i+1, k));
    LR = addevec(addevec(LR, gel(MA,i)), gel(MR,i));
  }
  if (!T)
  {
    long m = vecvecsmall_max(LR); /* < k */
    T = zetamultinit_i(k, m, prec2nbits(prec));
  }
  else
  {
    long M;
    if (typ(T) != t_VEC || lg(T) != 3) pari_err_TYPE("zetamult", T);
    M = lg(gel(T,1)); /* need M > m, which is < k */
    if (M < k) pari_err_DOMAIN("zetamult", "weight", ">", utoi(M), utoi(k));
  }
  vpow = gel(T,1);
  vbin = gel(T,2);
  l = lg(LR); vphi = cgetg(l, t_VEC);
  for (j = 1; j < l; j++) gel(vphi,j) = phip(gel(LR,j), vpow);
  lbin = lg(vbin);
  S = cgetg(lbin, t_VEC);
  for (i = 1; i < k; i++)
  {
    long LA = la(evec[i],evec[i+1]);
    GEN phi1 = isinphi(LR, gel(MA,i), vphi);
    GEN phi2 = isinphi(LR, gel(MR,i), vphi);
    if (i == 1)
      for (n = 1; n < lbin; n++)
        gel(S,n) = lamul(LA, mpmul(gel(phi1,n), gel(phi2,n)));
    else
      for (n = 1; n < lbin; n++)
        gel(S,n) = mpadd(gel(S,n), lamul(LA, mpmul(gel(phi1,n), gel(phi2,n))));
  }
  s = gmul2n(gel(S,1), -1);
  for (n = 2; n < lbin; n++) s = gadd(s, mpmul(gel(S,n), gel(vbin,n)));
  return gerepileuptoleaf(ltop, rtor(s,prec));
}
GEN
zetamult(GEN avec, long prec) { return zetamult0(avec, NULL, prec); }

/**************************************************************/
/*                         ALL MZV's                          */
/**************************************************************/

/* vecsmall to binary */
static long
myfd(GEN evec, long ini, long fin)
{
  long i, s = 0;
  for (i = ini; i <= fin; ++i) s = evec[i] | (s << 1);
  return s;
}

/* Given admissible evec w = 0e_2....e_{k-1}1, compute a,b,v such that
 * w=0{1}_{b-1}v{0}_{a-1}1 with v empty or admissible.
 * Input: binary vector evec */
static void
findabv(GEN w, long *pa, long *pb, long *pminit, long *pmmid, long *pmfin)
{
  long le = lg(w) - 2;
  if (le == 0)
  {
    *pa = 1;
    *pb = 1;
    *pminit = 2;
    *pmfin = 2;
    *pmmid = 1;
  }
  else
  {
    long a, b, j, lv;
    for (j = 1; j <= le; ++j)
      if (!w[j+1]) break;
    b = j;
    for (j = le; j >= 1; --j)
      if (w[j+1]) break;
    a = le + 1 - j;
    lv = le + 2 - a - b;
    if (lv > 0)
    {
      long v = myfd(w, b + 1, le - a + 2);
      *pa = a;
      *pb = b;
      *pminit = (((1 << b) - 1) << (lv - 1)) + (v/2) + 2;
      *pmfin = (((1 << (lv - 1)) + v) << (a - 1)) + 2;
      *pmmid = (1 << (lv - 2)) + (v/2) + 2;
    }
    else
    {
      *pa = a;
      *pb = b;
      *pminit = (1 << (b - 1)) + 1;
      *pmfin = (a == 1) ? 2 : (1 << (a - 2)) + 2;
      *pmmid = 1;
    }
  }
}

/* Returns 'all':
* all[1] contains zeta(emptyset)_{n-1,n-1},
* all[2] contains zeta({0})_{n-1,n-1}=zeta({1})_{n-1,n-1} for n >= 2,
* all[m+2][n] : 1 <= m < 2^{k-2}, 1 <= n <= N + 1
* contains zeta(w)_{n-1,n-1}, w corresponding to m,n
* all[m+2] : 2^{k-2} <= m < 2^{k-1} contains zeta(w), w corresponding to m
(code: w=0y1 iff m=1y). */
static GEN
fillall(long k, long bitprec)
{
  long N = 1 + bitprec/2, prec = nbits2prec(bitprec);
  long k1, j, n, m, mbar = 0, K = 1 << (k - 1), K2 = K/2;
  GEN all, v, p1, p2, r1, pab, S;

  r1 = real_1(prec);
  pab = cgetg(N+1, t_VEC); gel(pab, 1) = gen_0; /* not needed */
  for (n = 2; n <= N; n++) gel(pab, n) = powersr(divru(r1, n), k);
  /* 1/n^a = gmael(pab, n, a + 1) */
  all = cgetg(K + 2, t_VEC);
  gel(all,1) = v = cgetg(N+1, t_VEC);
  gel(v,1) = gen_0; /* unused */
  gel(v,2) = real2n(-1,prec);
  gel(v,3) = invr(utor(6,prec)); /* cf get_vbin: shifted by 1 :-( */
  for (n = 3; n < N; n++) gel(v,n+1) = divru(mulru(gel(v,n), n), 4*n-2);

  gel(all,2) = p1 = cgetg(N+1, t_VEC);
  gel(p1,1) = gen_0; /* unused */
  for (j = 2; j <= N; j++) gel(p1,j) = divru(gel(v,j), j-1);

  for (m = 1; m < K2; m++)
  {
    gel(all, m+2) = p1 = cgetg(N+1, t_VEC);
    for (n = 1; n < N; n++) gel(p1, n) = cgetr(prec);
    gel(p1, n) = gen_0;
  }
  for (m = K2; m < K; m++) gel(all, m+2) = utor(0, prec);
  for (k1 = 2; k1 <= k; k1++)
  { /* Assume length evec < k1 filled */
    /* If evec = 0e_2...e_{k_1-1}1 then m = (1e_2...e_{k_1-1})_2 */
    GEN w = cgetg(k1, t_VECSMALL);
    long M = 1 << (k1 - 2);
    pari_sp av = avma;
    for (m = M; m < 2*M; m++)
    {
      GEN pinit, pfin, pmid;
      long comp, a, b, minit, mfin, mmid, mc = m, ii = 0;
      p1 = gel(all, m + 2);
      for (j = k1 - 1; j >= 2; --j)
      {
        w[j] = mc & 1;
        ii = (1 - w[j]) | (ii<<1);
        mc >>= 1;
      }
      mbar = M + ii;
      comp = mbar - m;
      if (comp < 0) continue;
      p2 = gel(all, mbar + 2);
      findabv(w, &a,&b,&minit,&mmid,&mfin);
      pinit= gel(all, minit);
      pfin = gel(all, mfin);
      pmid = gel(all, mmid);
      for (n = N-1; n > 1; n--, avma = av)
      {
        GEN t = mpmul(gel(pinit,n+1), gmael(pab, n, a+1));
        GEN u = mpmul(gel(pfin, n+1), gmael(pab, n, b+1));
        GEN v = mpmul(gel(pmid, n+1), gmael(pab, n, a+b+1));
        S = mpadd(k1 < k ? gel(p1, n+1) : p1, mpadd(mpadd(t, u), v));
        if (!signe(S)) S = gen_0;
        mpaff(S, k1 < k ? gel(p1, n) : p1);
        if (comp > 0 && k1 < k) mpaff(S, gel(p2, n));
      }
      { /* n = 1: same formula simplifies */
        GEN t = gel(pinit,2), u = gel(pfin,2), v = gel(pmid,2);
        S = mpadd(k1 < k ? gel(p1,2) : p1, mpadd(mpadd(t, u), v));
        if (!signe(S)) S = gen_0;
        mpaff(S, k1 < k ? gel(p1,1) : p1);
        if (comp > 0 && k1 < k) mpaff(S, gel(p2, 1));
        avma = av;
      }
      if (comp > 0 && k1 == k) mpaff(p1, p2);
    }
  }
  for (j = 1; j < K; j++)
    gel(all, j) = j < K2 ? gmael(all, j+2, 1) : gel(all, j+2);
  setlg(all, K); return all;
}

GEN
zetamultall(long k, long prec)
{
  pari_sp av = avma;
  if (k < 1) pari_err_DOMAIN("zetamultall", "k", "<", gen_1, stoi(k));
  if (k >= 64) pari_err_OVERFLOW("zetamultall");
  return gerepilecopy(av, fillall(k, prec2nbits(prec) + 32));
}

/* m > 0 */
static GEN
mtoevec(GEN m)
{
  GEN e = vecsmall_append(binary_zv(m), 1);
  e[1] = 0; return e;
}

static GEN
etoindex(GEN evec)
{
  long k = lg(evec) - 1;
  return utoipos((1 << (k-2)) + myfd(evec, 2, k-1));
}

/* Conversions: types are evec, avec, m (if evec=0y1, m=(1y)_2).
   fl is respectively 0, 1, 2. Type of a is autodetected. */
GEN
zetamultconvert(GEN a, long fl)
{
  pari_sp av = avma;
  long i, l;
  if (fl < 0 || fl > 2) pari_err_FLAG("zetamultconvert");
  switch(typ(a))
  {
    case t_INT:
      if (signe(a) <= 0) pari_err_TYPE("zetamultconvert",a);
      switch (fl)
      {
        case 0: a = mtoevec(a); break;
        case 1: a = etoa(mtoevec(a)); break;
        case 2: a = icopy(a); break;
      }
      break;
    case t_VEC: case t_COL: case t_VECSMALL:
      a = gtovecsmall(a);
      l = lg(a);
      if (a[1] == 0)
      {
        if (!a[l-1]) pari_err_TYPE("zetamultconvert", a);
        for (i = 1; i < l; i++)
          if (a[i] & ~1UL) pari_err_TYPE("zetamultconvert", a);
        switch (fl)
        {
          case 1: a = etoa(a); break;
          case 2: a = etoindex(a);
        }
      }
      else
      {
        if (a[1] < 2) pari_err_TYPE("zetamultconvert", a);
        for (i = 2; i < l; i++)
          if (a[i] <= 0) pari_err_TYPE("zetamultconvert", a);
        switch (fl)
        {
          case 0: a = atoe(a); break;
          case 2: a = etoindex(atoe(a));
        }
      }
      break;
    default: pari_err_TYPE("zetamultconvert", a);
  }
  return gerepileuptoleaf(av, a);
}
