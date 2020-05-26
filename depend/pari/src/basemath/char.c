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

/*********************************************************************/
/**                                                                 **/
/**                  GENERIC ABELIAN CHARACTERS                     **/
/**                                                                 **/
/*********************************************************************/
/* check whether G is a znstar */
int
checkznstar_i(GEN G)
{
  return (typ(G) == t_VEC && lg(G) == 6
      && typ(znstar_get_faN(G)) == t_VEC
      && typ(gel(G,1)) == t_VEC && lg(gel(G,1)) == 3);
}

int
char_check(GEN cyc, GEN chi)
{ return typ(chi) == t_VEC && lg(chi) == lg(cyc) && RgV_is_ZV(chi); }

/* Shallow; return [ d[1],  d[1]/d[2],...,d[1]/d[n] ] */
GEN
cyc_normalize(GEN d)
{
  long i, l = lg(d);
  GEN C, D;
  if (l == 1) return mkvec(gen_1);
  D = cgetg(l, t_VEC); gel(D,1) = C = gel(d,1);
  for (i = 2; i < l; i++) gel(D,i) = diviiexact(C, gel(d,i));
  return D;
}

/* chi character [D,C] given by chi(g_i) = \zeta_D^C[i] for all i, return
 * [d,c] such that chi(g_i) = \zeta_d^c[i] for all i and d minimal */
GEN
char_simplify(GEN D, GEN C)
{
  GEN d = D;
  if (lg(C) == 1) d = gen_1;
  else
  {
    GEN t = gcdii(d, ZV_content(C));
    if (!equali1(t))
    {
      long tc = typ(C);
      C = ZC_Z_divexact(C, t); settyp(C, tc);
      d = diviiexact(d, t);
    }
  }
  return mkvec2(d,C);
}

/* Shallow; ncyc from cyc_normalize(): ncyc[1] = cyc[1],
 * ncyc[i] = cyc[i]/cyc[1] for i > 1; chi character on G ~ cyc.
 * Return [d,c] such that: chi( g_i ) = e(chi[i] / cyc[i]) = e(c[i]/ d) */
GEN
char_normalize(GEN chi, GEN ncyc)
{
  long i, l = lg(chi);
  GEN c = cgetg(l, t_VEC);
  if (l > 1) {
    gel(c,1) = gel(chi,1);
    for (i = 2; i < l; i++) gel(c,i) = mulii(gel(chi,i), gel(ncyc,i));
  }
  return char_simplify(gel(ncyc,1), c);
}

/* Called by function 's'. x is a group object affording ".cyc" method, and
 * chi an abelian character. Return NULL if the group is (Z/nZ)^* [special
 * case more character types allowed] and x.cyc otherwise */
static GEN
get_cyc(GEN x, GEN chi, const char *s)
{
  if (nftyp(x) == typ_BIDZ)
  {
    if (!zncharcheck(x, chi)) pari_err_TYPE(s, chi);
    return NULL;
  }
  else
  {
    if (typ(x) != t_VEC || !RgV_is_ZV(x)) x = member_cyc(x);
    if (!char_check(x, chi)) pari_err_TYPE(s, chi);
    return x;
  }
}

/* conjugate character [ZV/ZC] */
GEN
charconj(GEN cyc, GEN chi)
{
  long i, l;
  GEN z = cgetg_copy(chi, &l);
  for (i = 1; i < l; i++)
  {
    GEN c = gel(chi,i);
    gel(z,i) = signe(c)? subii(gel(cyc,i), c): gen_0;
  }
  return z;
}
GEN
charconj0(GEN x, GEN chi)
{
  GEN cyc = get_cyc(x, chi, "charconj");
  return cyc? charconj(cyc, chi): zncharconj(x, chi);
}

GEN
charorder(GEN cyc, GEN x)
{
  pari_sp av = avma;
  long i, l = lg(cyc);
  GEN f = gen_1;
  for (i = 1; i < l; i++)
    if (signe(gel(x,i)))
    {
      GEN c, o = gel(cyc,i);
      c = gcdii(o, gel(x,i));
      if (!is_pm1(c)) o = diviiexact(o,c);
      f = lcmii(f, o);
    }
  return gerepileuptoint(av, f);
}
GEN
charorder0(GEN x, GEN chi)
{
  GEN cyc = get_cyc(x, chi, "charorder");
  return cyc? charorder(cyc, chi): zncharorder(x, chi);
}

/* chi character of abelian G: chi[i] = chi(z_i), where G = \oplus Z/cyc[i] z_i.
 * Return Ker chi */
GEN
charker(GEN cyc, GEN chi)
{
  long i, l = lg(cyc);
  GEN nchi, ncyc, m, U;

  if (l == 1) return cgetg(1,t_MAT); /* trivial subgroup */
  ncyc = cyc_normalize(cyc);
  nchi = char_normalize(chi, ncyc);
  m = shallowconcat(gel(nchi,2), gel(nchi,1));
  U = gel(ZV_extgcd(m), 2); setlg(U,l);
  for (i = 1; i < l; i++) setlg(U[i], l);
  return hnfmodid(U, gel(ncyc,1));
}
GEN
charker0(GEN x, GEN chi)
{
  GEN cyc = get_cyc(x, chi, "charker");
  return cyc? charker(cyc, chi): zncharker(x, chi);
}

GEN
charpow(GEN cyc, GEN a, GEN N)
{
  long i, l;
  GEN v = cgetg_copy(a, &l);
  for (i = 1; i < l; i++) gel(v,i) = Fp_mul(gel(a,i), N, gel(cyc,i));
  return v;
}
GEN
charmul(GEN cyc, GEN a, GEN b)
{
  long i, l;
  GEN v = cgetg_copy(a, &l);
  for (i = 1; i < l; i++) gel(v,i) = Fp_add(gel(a,i), gel(b,i), gel(cyc,i));
  return v;
}
GEN
chardiv(GEN cyc, GEN a, GEN b)
{
  long i, l;
  GEN v = cgetg_copy(a, &l);
  for (i = 1; i < l; i++) gel(v,i) = Fp_sub(gel(a,i), gel(b,i), gel(cyc,i));
  return v;
}
GEN
charpow0(GEN x, GEN a, GEN N)
{
  GEN cyc = get_cyc(x, a, "charpow");
  return cyc? charpow(cyc, a, N): zncharpow(x, a, N);
}
GEN
charmul0(GEN x, GEN a, GEN b)
{
  const char *s = "charmul";
  GEN cyc = get_cyc(x, a, s);
  if (!cyc)
  {
    if (!zncharcheck(x, b)) pari_err_TYPE(s, b);
    return zncharmul(x, a, b);
  }
  else
  {
    if (!char_check(cyc, b)) pari_err_TYPE(s, b);
    return charmul(cyc, a, b);
  }
}
GEN
chardiv0(GEN x, GEN a, GEN b)
{
  const char *s = "chardiv";
  GEN cyc = get_cyc(x, a, s);
  if (!cyc)
  {
    if (!zncharcheck(x, b)) pari_err_TYPE(s, b);
    return znchardiv(x, a, b);
  }
  else
  {
    if (!char_check(cyc, b)) pari_err_TYPE(s, b);
    return chardiv(cyc, a, b);
  }
}

static GEN
chareval_i(GEN nchi, GEN dlog, GEN z)
{
  GEN o, q, r, b = gel(nchi,1);
  GEN a = FpV_dotproduct(gel(nchi,2), dlog, b);
  /* image is a/b in Q/Z */
  if (!z) return gdiv(a,b);
  if (typ(z) == t_INT)
  {
    q = dvmdii(z, b, &r);
    if (signe(r)) pari_err_TYPE("chareval", z);
    return mulii(a, q);
  }
  /* return z^(a*o/b), assuming z^o = 1 and b | o */
  if (typ(z) != t_VEC || lg(z) != 3) pari_err_TYPE("chareval", z);
  o = gel(z,2); if (typ(o) != t_INT) pari_err_TYPE("chareval", z);
  q = dvmdii(o, b, &r); if (signe(r)) pari_err_TYPE("chareval", z);
  q = mulii(a, q); /* in [0, o[ since a is reduced mod b */
  z = gel(z,1);
  if (typ(z) == t_VEC)
  {
    if (itos_or_0(o) != lg(z)-1) pari_err_TYPE("chareval", z);
    return gcopy(gel(z, itos(q)+1));
  }
  else
    return gpow(z, q, DEFAULTPREC);
}

static GEN
not_coprime(GEN z)
{ return (!z || typ(z) == t_INT)? gen_m1: gen_0; }

static GEN
get_chi(GEN cyc, GEN chi)
{
  if (!char_check(cyc,chi)) pari_err_TYPE("chareval", chi);
  return char_normalize(chi, cyc_normalize(cyc));
}
/* G a bnr.  FIXME: horribly inefficient to check that (x,N)=1, what to do ? */
static int
bnr_coprime(GEN G, GEN x)
{
  GEN t, N = gel(bnr_get_mod(G), 1);
  if (typ(x) == t_INT) /* shortcut */
  {
    t = gcdii(gcoeff(N,1,1), x);
    if (equali1(t)) return 1;
    t = idealadd(G, N, x);
    return equali1(gcoeff(t,1,1));
  }
  x = idealnumden(G, x);
  t = idealadd(G, N, gel(x,1));
  if (!equali1(gcoeff(t,1,1))) return 0;
  t = idealadd(G, N, gel(x,2));
  return equali1(gcoeff(t,1,1));
}
GEN
chareval(GEN G, GEN chi, GEN x, GEN z)
{
  pari_sp av = avma;
  GEN nchi, L;

  switch(nftyp(G))
  {
    case typ_BNR:
      if (!bnr_coprime(G, x)) return not_coprime(z);
      L = isprincipalray(G, x);
      nchi = get_chi(bnr_get_cyc(G), chi);
      break;
    case typ_BNF:
      L = isprincipal(G, x);
      nchi = get_chi(bnf_get_cyc(G), chi);
      break;
    case typ_BIDZ:
      if (checkznstar_i(G)) return gerepileupto(av, znchareval(G, chi, x, z));
      /* don't implement chars on general bid: need an nf... */
    default:
      pari_err_TYPE("chareval", G);
      return NULL;/* LCOV_EXCL_LINE */
  }
  return gerepileupto(av, chareval_i(nchi, L, z));
}

/* nchi = [ord,D] a quasi-normalized character (ord may be a multiple of
 * the character order); return v such that v[n] = -1 if (n,N) > 1 else
 * chi(n) = e(v[n]/ord), 1 <= n <= N */
GEN
ncharvecexpo(GEN G, GEN nchi)
{
  long N = itou(znstar_get_N(G)), ord = itou(gel(nchi,1)), i, j, l;
  GEN cyc, gen, d, t, t1, t2, t3, e, u, u1, u2, u3;
  GEN D = gel(nchi,2), v = const_vecsmall(N,-1);
  pari_sp av = avma;
  if (typ(D) == t_COL) {
    cyc = znstar_get_conreycyc(G);
    gen = znstar_get_conreygen(G);
  } else {
    cyc = znstar_get_cyc(G);
    gen = znstar_get_gen(G);
  }
  l = lg(cyc);
  e = u = cgetg(N+1,t_VECSMALL);
  d = t = cgetg(N+1,t_VECSMALL);
  *++d = 1;
  *++e = 0; v[*d] = *e;
  for (i = 1; i < l; i++)
  {
    ulong g = itou(gel(gen,i)), c = itou(gel(cyc,i)), x = itou(gel(D,i));
    for (t1=t,u1=u,j=c-1; j; j--,t1=t2,u1=u2)
      for (t2=d,u2=e, t3=t1,u3=u1; t3<t2; )
      {
        *++d = Fl_mul(*++t3, g, N);
        *++e = Fl_add(*++u3, x, ord); v[*d] = *e;
      }
  }
  avma = av; return v;
}

/*****************************************************************************/

static ulong
lcmuu(ulong a, ulong b) { return (a/ugcd(a,b)) * b; }
static ulong
zv_charorder(GEN cyc, GEN x)
{
  long i, l = lg(cyc);
  ulong f = 1;
  for (i = 1; i < l; i++)
    if (x[i])
    {
      ulong o = cyc[i];
      f = lcmuu(f, o / ugcd(o, x[i]));
    }
  return f;
}

/* N > 0 */
GEN
coprimes_zv(ulong N)
{
  GEN v = const_vecsmall(N,1);
  pari_sp av = avma;
  GEN P = gel(factoru(N),1);
  long i, l = lg(P);
  for (i = 1; i < l; i++)
  {
    ulong p = P[i], j;
    for (j = p; j <= N; j += p) v[j] = 0;
  }
  avma = av; return v;
}
/* cf zv_cyc_minimal: return k such that g*k is minimal (wrt lex) */
long
zv_cyc_minimize(GEN cyc, GEN g, GEN coprime)
{
  pari_sp av = avma;
  long d, k, e, i, maxi, k0, bestk, l = lg(g), o = lg(coprime)-1;
  GEN best, gk, gd;
  ulong t;
  if (o == 1) return 1;
  for (i = 1; i < l; i++)
    if (g[i]) break;
  if (g[i] == 1) return 1;
  k0 = Fl_invgen(g[i], cyc[i], &t);
  d = cyc[i] / (long)t;
  if (k0 > 1) g = vecmoduu(Flv_Fl_mul(g, k0, cyc[i]), cyc);
  for (i++; i < l; i++)
    if (g[i]) break;
  if (i == l) return k0;
  cyc = vecslice(cyc,i,l-1);
  g   = vecslice(g,  i,l-1);
  e = cyc[1];
  gd = Flv_Fl_mul(g, d, e);
  bestk = 1; best = g; maxi = e/ugcd(d,e);
  for (gk = g, k = d+1, i = 1; i < maxi; k += d, i++)
  {
    long ko = k % o;
    gk = Flv_add(gk, gd, e); if (!ko || !coprime[ko]) continue;
    gk = vecmoduu(gk, cyc);
    if (vecsmall_lexcmp(gk, best) < 0) { best = gk; bestk = k; }
  }
  avma = av; return bestk == 1? k0: Fl_mul(k0, bestk, o);
}
/* g of order o in abelian group G attached to cyc. Is g a minimal generator
 * [wrt lex order] of the cyclic subgroup it generates;
 * coprime = coprimes_zv(o) */
long
zv_cyc_minimal(GEN cyc, GEN g, GEN coprime)
{
  pari_sp av = avma;
  long i, maxi, d, k, e, l = lg(g), o = lg(coprime)-1; /* elt order */
  GEN gd, gk;
  if (o == 1) return 1;
  for (k = 1; k < l; k++)
    if (g[k]) break;
  if (g[k] == 1) return 1;
  if (cyc[k] % g[k]) return 0;
  d = cyc[k] / g[k]; /* > 1 */
  for (k++; k < l; k++) /* skip following 0s */
    if (g[k]) break;
  if (k == l) return 1;
  cyc = vecslice(cyc,k,l-1);
  g   = vecslice(g,  k,l-1);
  e = cyc[1];
  /* find k in (Z/e)^* such that g*k mod cyc is lexicographically minimal,
   * k = 1 mod d to fix the first non-zero entry */
  gd = Flv_Fl_mul(g, d, e); maxi = e/ugcd(d,e);
  for (gk = g, k = d+1, i = 1; i < maxi; i++, k += d)
  {
    long ko = k % o;
    gk = Flv_add(gk, gd, e); if (!coprime[ko]) continue;
    gk = vecmoduu(gk, cyc);
    if (vecsmall_lexcmp(gk, g) < 0) { avma = av; return 0; }
  }
  avma = av; return 1;
}

static GEN
coprime_tables(long N)
{
  GEN D = divisorsu(N), v = const_vec(N, NULL);
  long i, l = lg(D);
  for (i = 1; i < l; i++) gel(v, D[i]) = coprimes_zv(D[i]);
  return v;
}
/* enumerate all group elements, modulo (Z/cyc[1])^* */
static GEN
cyc2elts_normal(GEN cyc, long maxord, GEN ORD)
{
  long i, n, o, N, j = 1;
  GEN z, vcoprime;

  if (typ(cyc) != t_VECSMALL) cyc = gtovecsmall(cyc);
  n = lg(cyc)-1;
  if (n == 0) return cgetg(1, t_VEC);
  N = zv_prod(cyc);
  z = cgetg(N+1, t_VEC);
  if (1 <= maxord && (!ORD|| zv_search(ORD,1)))
    gel(z,j++) = zero_zv(n);
  vcoprime = coprime_tables(cyc[1]);
  for (i = n; i > 0; i--)
  {
    GEN cyc0 = vecslice(cyc,i+1,n), pre = zero_zv(i);
    GEN D = divisorsu(cyc[i]), C = cyc2elts(cyc0);
    long s, t, lD = lg(D), nC = lg(C)-1; /* remove last element */
    for (s = 1; s < lD-1; s++)
    {
      long o0 = D[lD-s]; /* cyc[i] / D[s] */
      if (o0 > maxord) continue;
      pre[i] = D[s];
      if (!ORD || zv_search(ORD,o0))
      {
        GEN c = vecsmall_concat(pre, zero_zv(n-i));
        gel(z,j++) = c;
      }
      for (t = 1; t < nC; t++)
      {
        GEN chi0 = gel(C,t);
        o = lcmuu(o0, zv_charorder(cyc0,chi0));
        if (o <= maxord && (!ORD || zv_search(ORD,o)))
        {
          GEN c = vecsmall_concat(pre, chi0);
          if (zv_cyc_minimal(cyc, c, gel(vcoprime,o))) gel(z,j++) = c;
        }
      }
    }
  }
  setlg(z,j); return z;
}

GEN
chargalois(GEN G, GEN ORD)
{
  pari_sp av = avma;
  long maxord, i, l;
  GEN v, cyc = (typ(G) == t_VEC && RgV_is_ZVpos(G))? G: member_cyc(G);
  if (lg(cyc) == 1) retmkvec(cgetg(1,t_VEC));
  maxord = itou(gel(cyc,1));
  if (ORD && gequal0(ORD)) ORD = NULL;
  if (ORD)
    switch(typ(ORD))
    {
      long l;
      case t_VEC:
        ORD = ZV_to_zv(ORD);
      case t_VECSMALL:
        ORD = leafcopy(ORD);
        vecsmall_sort(ORD);
        l = lg(ORD);
        if (l == 1) return cgetg(1, t_VECSMALL);
        maxord = minss(maxord, ORD[l-1]);
        break;
      case t_INT:
        maxord = minss(maxord, itos(ORD));
        ORD = NULL;
        break;
      default: pari_err_TYPE("chargalois", ORD);
    }
  v = cyc2elts_normal(cyc, maxord, ORD); l = lg(v);
  for(i = 1; i < l; i++) gel(v,i) = zv_to_ZV(gel(v,i));
  return gerepileupto(av, v);
}

/*********************************************************************/
/**                                                                 **/
/**                  (Z/NZ)^* AND DIRICHLET CHARACTERS              **/
/**                                                                 **/
/*********************************************************************/

GEN
znstar0(GEN N, long flag)
{
  GEN F = NULL, P, E, cyc, gen, mod, G;
  long i, i0, l, nbprimes;
  pari_sp av = avma;

  if (flag && flag != 1) pari_err_FLAG("znstar");
  if ((F = check_arith_all(N,"znstar")))
  {
    F = clean_Z_factor(F);
    N = typ(N) == t_VEC? gel(N,1): factorback(F);
  }
  if (!signe(N))
  {
    if (flag) pari_err_IMPL("znstar(0,1)");
    avma = av;
    retmkvec3(gen_2, mkvec(gen_2), mkvec(gen_m1));
  }
  N = absi_shallow(N);
  if (abscmpiu(N,2) <= 0)
  {
    G = mkvec3(gen_1, cgetg(1,t_VEC), cgetg(1,t_VEC));
    if (flag)
    {
      GEN v = const_vec(6,cgetg(1,t_VEC));
      gel(v,3) = cgetg(1,t_MAT);
      F = equali1(N)? mkvec2(cgetg(1,t_COL),cgetg(1,t_VECSMALL))
                    : mkvec2(mkcol(gen_2), mkvecsmall(1));
      G = mkvec5(mkvec2(N,mkvec(gen_0)), G, F, v, cgetg(1,t_MAT));
    }
    return gerepilecopy(av,G);
  }
  if (!F) F = Z_factor(N);
  P = gel(F,1); nbprimes = lg(P)-1;
  E = ZV_to_nv( gel(F,2) );
  switch(mod8(N))
  {
    case 0:
      P = shallowconcat(gen_2,P);
      E = vecsmall_prepend(E, E[1]); /* add a copy of p=2 row */
      i = 2; /* 2 generators at 2 */
      break;
    case 4:
      i = 1; /* 1 generator at 2 */
      break;
    case 2: case 6:
      P = vecsplice(P,1);
      E = vecsplice(E,1); /* remove 2 */
      i = 0; /* no generator at 2 */
      break;
    default:
      i = 0; /* no generator at 2 */
      break;
  }
  l = lg(P);
  cyc = cgetg(l,t_VEC);
  gen = cgetg(l,t_VEC);
  mod = cgetg(l,t_VEC);
  /* treat p=2 first */
  if (i == 2)
  {
    long v2 = E[1];
    GEN q = int2n(v2);
    gel(cyc,1) = gen_2;
    gel(gen,1) = subiu(q,1); /* -1 */
    gel(mod,1) = q;
    gel(cyc,2) = int2n(v2-2);
    gel(gen,2) = utoipos(5); /* Conrey normalization */
    gel(mod,2) = q;
    i0 = 3;
  }
  else if (i == 1)
  {
    gel(cyc,1) = gen_2;
    gel(gen,1) = utoipos(3);
    gel(mod,1) = utoipos(4);
    i0 = 2;
  }
  else
    i0 = 1;
  /* odd primes, fill remaining entries */
  for (i = i0; i < l; i++)
  {
    long e = E[i];
    GEN p = gel(P,i), q = powiu(p, e-1), Q = mulii(p, q);
    gel(cyc,i) = subii(Q, q); /* phi(p^e) */
    gel(gen,i) = pgener_Zp(p);/* Conrey normalization, for e = 1 also */
    gel(mod,i) = Q;
  }
  /* gen[i] has order cyc[i] and generates (Z/mod[i]Z)^* */
  if (nbprimes > 1) /* lift generators to (Z/NZ)^*, = 1 mod N/mod[i] */
    for (i=1; i<l; i++)
    {
      GEN Q = gel(mod,i), g = gel(gen,i), qinv = Fp_inv(Q, diviiexact(N,Q));
      g = addii(g, mulii(mulii(subsi(1,g),qinv),Q));
      gel(gen,i) = modii(g, N);
    }

  /* cyc[i] > 1 and remain so in the loop, gen[i] = 1 mod (N/mod[i]) */
  if (!flag)
  { /* update generators in place; about twice faster */
    G = gen;
    for (i=l-1; i>=2; i--)
    {
      GEN ci = gel(cyc,i), gi = gel(G,i);
      long j;
      for (j=i-1; j>=1; j--) /* we want cyc[i] | cyc[j] */
      {
        GEN cj = gel(cyc,j), gj, qj, v, d;

        d = bezout(ci,cj,NULL,&v); /* > 1 */
        if (absequalii(ci, d)) continue; /* ci | cj */
        if (absequalii(cj, d)) { /* cj | ci */
          swap(gel(G,j),gel(G,i));
          gi = gel(G,i);
          swap(gel(cyc,j),gel(cyc,i));
          ci = gel(cyc,i); continue;
        }

        qj = diviiexact(cj,d);
        gel(cyc,j) = mulii(ci,qj);
        gel(cyc,i) = d;

        /* [1,v*cj/d; 0,1]*[1,0;-1,1]*diag(cj,ci)*[ci/d,-v; cj/d,u]
         * = diag(lcm,gcd), with u ci + v cj = d */
        gj = gel(G,j);
        /* (gj, gi) *= [1,0; -1,1]^-1 */
        gj = Fp_mul(gj, gi, N); /* order ci*qj = lcm(ci,cj) */
        /* (gj,gi) *= [1,v*qj; 0,1]^-1 */
        togglesign_safe(&v);
        if (signe(v) < 0) v = modii(v,ci); /* >= 0 to avoid inversions */
        gel(G,i) = gi = Fp_mul(gi, Fp_pow(gj, mulii(qj, v), N), N);
        gel(G,j) = gj;
        ci = d; if (absequaliu(ci, 2)) break;
      }
    }
    G = mkvec3(ZV_prod(cyc), cyc, FpV_to_mod(G,N));
  }
  else
  { /* keep matrices between generators, return an 'init' structure */
    GEN D, U, Ui, fao = cgetg(l, t_VEC), lo = cgetg(l, t_VEC);
    F = mkvec2(P, E);
    D = ZV_snf_group(cyc,&U,&Ui);
    for (i = 1; i < l; i++)
    {
      GEN t = gen_0, p = gel(P,i), p_1 = subiu(p,1);
      long e = E[i];
      gel(fao,i) = get_arith_ZZM(p_1);
      if (e >= 2 && !absequaliu(p,2))
      {
        GEN q = gel(mod,i), g = Fp_pow(gel(gen,i),p_1,q);
        if (e == 2)
          t = Fp_inv(diviiexact(subiu(g,1), p), p);
        else
          t = ginv(Qp_log(cvtop(g,p,e)));
      }
      gel(lo,i) = t;
    }
    G = cgetg(l, t_VEC);
    for (i = 1; i < l; i++) gel(G,i) = FpV_factorback(gen, gel(Ui,i), N);
    G = mkvec3(ZV_prod(D), D, G);
    G = mkvec5(mkvec2(N,mkvec(gen_0)), G, F,
               mkvecn(6,mod,fao,Ui,gen,cyc,lo), U);
  }
  return gerepilecopy(av, G);
}
GEN
znstar(GEN N) { return znstar0(N, 0); }

/* g has order 2^(e-2), g,h = 1 (mod 4); return x s.t. g^x = h (mod 2^e) */
static GEN
Zideallog_2k(GEN h, GEN g, long e, GEN pe)
{
  GEN a = Fp_log(h, g, int2n(e-2), pe);
  if (typ(a) != t_INT) return NULL;
  return a;
}

/* ord = get_arith_ZZM(p-1), simplified form of znlog_rec: g is known
 * to be a primitive root mod p^e; lo = 1/log_p(g^(p-1)) */
static GEN
Zideallog_pk(GEN h, GEN g, GEN p, long e, GEN pe, GEN ord, GEN lo)
{
  GEN gp = (e == 1)? g: modii(g, p);
  GEN hp = (e == 1)? h: modii(h, p);
  GEN a = Fp_log(hp, gp, ord, p);
  if (typ(a) != t_INT) return NULL;
  if (e > 1)
  { /* find a s.t. g^a = h (mod p^e), p odd prime, e > 0, (h,p) = 1 */
    /* use p-adic log: O(log p + e) mul*/
    GEN b, p_1 = gel(ord,1);
    h = Fp_mul(h, Fp_pow(g, negi(a), pe), pe);
    /* g,h = 1 mod p; compute b s.t. h = g^b */
    if (e == 2) /* simpler */
      b = Fp_mul(diviiexact(subiu(h,1), p), lo, p);
    else
      b = padic_to_Q(gmul(Qp_log(cvtop(h, p, e)), lo));
    a = addii(a, mulii(p_1, b));
  }
  return a;
}

int
znconrey_check(GEN cyc, GEN chi)
{ return typ(chi) == t_COL && lg(chi) == lg(cyc) && RgV_is_ZV(chi); }

int
zncharcheck(GEN G, GEN chi)
{
  switch(typ(chi))
  {
    case t_INT: return 1;
    case t_COL: return znconrey_check(znstar_get_conreycyc(G), chi);
    case t_VEC: return char_check(znstar_get_cyc(G), chi);
  }
  return 0;
}

GEN
znconreyfromchar_normalized(GEN bid, GEN chi)
{
  GEN nchi, U = znstar_get_U(bid);
  long l = lg(chi);
  if (l == 1) retmkvec2(gen_1,cgetg(1,t_VEC));
  if (!RgV_is_ZV(chi) || lgcols(U) != l) pari_err_TYPE("lfunchiZ", chi);
  nchi = char_normalize(chi, cyc_normalize(znstar_get_cyc(bid)));
  gel(nchi,2) = ZV_ZM_mul(gel(nchi,2),U); return nchi;
}

GEN
znconreyfromchar(GEN bid, GEN chi)
{
  GEN nchi = znconreyfromchar_normalized(bid, chi);
  GEN v = char_denormalize(znstar_get_conreycyc(bid), gel(nchi,1), gel(nchi,2));
  settyp(v, t_COL); return v;
}

/* discrete log on canonical "primitive root" generators
 * Allow log(x) instead of x [usual discrete log on bid's generators */
GEN
znconreylog(GEN bid, GEN x)
{
  pari_sp av = avma;
  GEN N, L, F, P,E, y, pe, fao, gen, lo, cycg;
  long i, l;
  if (!checkznstar_i(bid)) pari_err_TYPE("znconreylog", bid);
  N = znstar_get_N(bid);
  if (typ(N) != t_INT) pari_err_TYPE("znconreylog", N);
  if (abscmpiu(N, 2) <= 0) return cgetg(1, t_COL);
  cycg = znstar_get_conreycyc(bid);
  switch(typ(x))
  {
    GEN Ui;
    case t_INT:
      if (!signe(x)) pari_err_COPRIME("znconreylog", x, N);
      break;
    case t_COL: /* log_bid(x) */
      Ui = znstar_get_Ui(bid);
      if (!RgV_is_ZV(x) || lg(x) != lg(Ui)) pari_err_TYPE("znconreylog", x);
      return gerepileupto(av, vecmodii(ZM_ZC_mul(Ui,x), cycg));
    case t_VEC:
      return gerepilecopy(av, znconreyfromchar(bid, x));
    default: pari_err_TYPE("znconreylog", x);
  }
  F = znstar_get_faN(bid); /* factor(N) */
  P = gel(F, 1); /* prime divisors of N */
  E = gel(F, 2); /* exponents */
  L = gel(bid,4);
  pe = znstar_get_pe(bid);
  fao = gel(L,2);
  gen = znstar_get_conreygen(bid); /* local generators of (Z/p^k)^* */
  lo = gel(L,6); /* 1/log_p((g_i)^(p_i-1)) */

  l = lg(gen); i = 1;
  y = cgetg(l, t_COL);
  if (!mod2(N) && !mod2(x)) pari_err_COPRIME("znconreylog", x, N);
  if (absequaliu(gel(P,1), 2) && E[1] >= 2)
  {
    if (E[1] == 2)
      gel(y,i++) = mod4(x) == 1? gen_0: gen_1;
    else
    {
      GEN a, x2, q2 = gel(pe,1);
      x2 = modii(x, q2);
      if (mod4(x) == 1) /* 1 or 5 mod 8*/
        gel(y,i++) = gen_0;
      else /* 3 or 7 */
      { gel(y,i++) = gen_1; x2 = subii(q2, x2); }
      /* x2 = 5^x mod q */
      a = Zideallog_2k(x2, gel(gen,i), E[1], q2);
      if (!a) pari_err_COPRIME("znconreylog", x, N);
      gel(y, i++) = a;
    }
  }
  while (i < l)
  {
    GEN p = gel(P,i), q = gel(pe,i), xpe = modii(x, q);
    GEN a = Zideallog_pk(xpe, gel(gen,i), p, E[i], q, gel(fao,i), gel(lo,i));
    if (!a) pari_err_COPRIME("znconreylog", x, N);
    gel(y, i++) = a;
  }
  return gerepilecopy(av, y);
}
GEN
Zideallog(GEN bid, GEN x)
{
  pari_sp av = avma;
  GEN y = znconreylog(bid, x), U = znstar_get_U(bid);
  return gerepileupto(av, ZM_ZC_mul(U, y));
}
GEN
znlog0(GEN h, GEN g, GEN o)
{
  if (typ(g) == t_VEC)
  {
    GEN N;
    if (o) pari_err_TYPE("znlog [with znstar]", o);
    if (!checkznstar_i(g)) pari_err_TYPE("znlog", h);
    N = znstar_get_N(g);
    h = Rg_to_Fp(h,N);
    return Zideallog(g, h);
  }
  return znlog(h, g, o);
}

GEN
znconreyexp(GEN bid, GEN x)
{
  pari_sp av = avma;
  long i, l;
  GEN N, pe, gen, cycg, v, vmod;
  int e2;
  if (!checkznstar_i(bid)) pari_err_TYPE("znconreyexp", bid);
  cycg = znstar_get_conreycyc(bid);
  switch(typ(x))
  {
    case t_VEC:
      x = znconreylog(bid, x);
      break;
    case t_COL:
      if (RgV_is_ZV(x) && lg(x) == lg(cycg)) break;
    default: pari_err_TYPE("znconreyexp",x);
  }
  pe = znstar_get_pe(bid);
  gen = znstar_get_conreygen(bid); /* local generators of (Z/p^k)^* */
  cycg = znstar_get_conreycyc(bid);
  l = lg(x); v = cgetg(l, t_VEC);
  N = znstar_get_N(bid);
  e2 = !mod8(N); /* 2 generators at p = 2 */
  for (i = 1; i < l; i++)
  {
    GEN q, g, m;
    if (i == 1 && e2) { gel(v,1) = NULL; continue; }
    q = gel(pe,i);
    g = gel(gen,i);
    m = modii(gel(x,i), gel(cycg,i));
    m = Fp_pow(g, m, q);
    if (i == 2 && e2 && signe(gel(x,1))) m = Fp_neg(m, q);
    gel(v,i) = mkintmod(m, q);
  }
  if (e2) v = vecsplice(v, 1);
  v = chinese1_coprime_Z(v);
  vmod = gel(v,1);
  v = gel(v,2);
  if (mpodd(v) || mpodd(N)) return gerepilecopy(av, v);
  /* handle N = 2 mod 4 */
  return gerepileuptoint(av, addii(v, vmod));
}

/* Return Dirichlet character \chi_q(m,.), where bid = znstar(q);
 * m is either a t_INT, or a t_COL [Conrey logarithm] */
GEN
znconreychar(GEN bid, GEN m)
{
  pari_sp av = avma;
  GEN c, d, nchi;

  if (!checkznstar_i(bid)) pari_err_TYPE("znconreychar", bid);
  switch(typ(m))
  {
    case t_COL:
    case t_INT:
      nchi = znconrey_normalized(bid,m); /* images of primroot gens */
      break;
    default:
      pari_err_TYPE("znconreychar",m);
      return NULL;/*LCOV_EXCL_LINE*/
  }
  d = gel(nchi,1);
  c = ZV_ZM_mul(gel(nchi,2), znstar_get_Ui(bid)); /* images of bid gens */
  return gerepilecopy(av, char_denormalize(znstar_get_cyc(bid),d,c));
}

/* chi a t_INT or Conrey log describing a character. Return conductor, as an
 * integer if primitive; as a t_VEC [N,factor(N)] if not. Set *pm=m to the
 * attached primitive character: chi(g_i) = m[i]/ord(g_i)
 * Caller should use znconreylog_normalize(BID, m), once BID(conductor) is
 * computed (wasteful to do it here since BID is shared by many characters) */
GEN
znconreyconductor(GEN bid, GEN chi, GEN *pm)
{
  pari_sp av = avma;
  GEN q, m, F, P, E;
  long i, j, l;
  int e2, primitive = 1;

  if (!checkznstar_i(bid)) pari_err_TYPE("znconreyconductor", bid);
  if (typ(chi) == t_COL)
  {
    if (!znconrey_check(znstar_get_conreycyc(bid), chi))
      pari_err_TYPE("znconreyconductor",chi);
  }
  else
    chi = znconreylog(bid, chi);
  l = lg(chi);
  F = znstar_get_faN(bid);
  P = gel(F,1);
  E = gel(F,2);
  if (l == 1)
  {
    avma = av;
    if (pm) *pm = cgetg(1,t_COL);
    if (lg(P) == 1) return gen_1;
    retmkvec2(gen_1, trivial_fact());
  }
  P = leafcopy(P);
  E = leafcopy(E);
  m = cgetg(l, t_COL);
  e2 = (E[1] >= 3 && absequaliu(gel(P,1),2));
  i = j = 1;
  if (e2)
  { /* two generators at p=2 */
    GEN a1 = gel(chi,1), a = gel(chi,2);
    i = 3;
    if (!signe(a))
    {
      e2 =  primitive = 0;
      if (signe(a1))
      { /* lose one generator */
        E[1] = 2;
        gel(m,1) = a1;
        j = 2;
      }
      /* else lose both */
    }
    else
    {
      long v = Z_pvalrem(a, gen_2, &a);
      if (v) { E[1] -= v; E[2] = E[1]; primitive = 0; }
      gel(m,1) = a1;
      gel(m,2) = a;
      j = 3;
    }
  }
  l = lg(P);
  for (; i < l; i++)
  {
    GEN p = gel(P,i), a = gel(chi,i);
    /* image of g_i in Q/Z is a/cycg[i], cycg[i] = order(g_i) */
    if (!signe(a)) primitive = 0;
    else
    {
      long v = Z_pvalrem(a, p, &a);
      E[j] = E[i]; if (v) { E[j] -= v; primitive = 0; }
      gel(P,j) = gel(P,i);
      gel(m,j) = a; j++;
    }
  }
  setlg(m,j);
  setlg(P,j);
  setlg(E,j);
  if (pm) *pm = m; /* attached primitive  character */
  if (primitive)
  {
    q = znstar_get_N(bid);
    if (mod4(q) == 2) primitive = 0;
  }
  if (!primitive)
  {
    if (e2)
    { /* remove duplicate p=2 row from factorization */
      P = vecsplice(P,1);
      E = vecsplice(E,1);
    }
    E = zc_to_ZC(E);
    q = mkvec2(factorback2(P,E), mkmat2(P,E));
  }
  gerepileall(av, pm? 2: 1, &q, pm);
  return q;
}

GEN
zncharinduce(GEN G, GEN chi, GEN N)
{
  pari_sp av = avma;
  GEN q, faq, P, E, Pq, Eq, CHI;
  long i, j, l;
  int e2;

  if (!checkznstar_i(G)) pari_err_TYPE("zncharinduce", G);
  if (!zncharcheck(G, chi)) pari_err_TYPE("zncharinduce", chi);
  q = znstar_get_N(G);
  if (typ(chi) != t_COL) chi = znconreylog(G, chi);
  if (checkznstar_i(N))
  {
    GEN faN = znstar_get_faN(N);
    P = gel(faN,1); l = lg(P);
    E = gel(faN,2);
    N = znstar_get_N(N);
    if (l > 2 && equalii(gel(P,1),gel(P,2)))
    { /* remove duplicate 2 */
      l--;
      P = vecsplice(P,1);
      E = vecsplice(E,1);
    }
  }
  else
  {
    GEN faN = check_arith_pos(N, "zncharinduce");
    if (!faN) faN = Z_factor(N);
    else
      N = (typ(N) == t_VEC)? gel(N,1): factorback(faN);
    P = gel(faN,1);
    E = gel(faN,2);
  }
  if (!dvdii(N,q)) pari_err_DOMAIN("zncharinduce", "N % q", "!=", gen_0, N);
  if (mod4(N) == 2)
  { /* remove 2 */
    if (lg(P) > 1 && absequaliu(gel(P,1), 2))
    {
      P = vecsplice(P,1);
      E = vecsplice(E,1);
    }
    N = shifti(N,-1);
  }
  l = lg(P);
  /* q = N or q = 2N, N odd */
  if (cmpii(N,q) <= 0) return gerepilecopy(av, chi);
  /* N > 1 => l > 1*/
  if (typ(E) != t_VECSMALL) E = ZV_to_zv(E);
  e2 = (E[1] >= 3 && absequaliu(gel(P,1),2)); /* 2 generators at 2 mod N */
  if (ZV_equal0(chi))
  {
    avma = av;
    return equali1(N)? cgetg(1, t_COL): zerocol(l+e2 - 1);
  }

  faq = znstar_get_faN(G);
  Pq = gel(faq,1);
  Eq = gel(faq,2);
  CHI = cgetg(l+e2, t_COL);
  i = j = 1;
  if (e2)
  {
    i = 2; j = 3;
    if (absequaliu(gel(Pq,1), 2))
    {
      if (Eq[1] >= 3)
      { /* 2 generators at 2 mod q */
        gel(CHI,1) = gel(chi,1);
        gel(CHI,2) = shifti(gel(chi,2), E[1]-Eq[1]);
      }
      else if (Eq[1] == 2)
      { /* 1 generator at 2 mod q */
        gel(CHI,1) = gel(chi,1);
        gel(CHI,2) = gen_0;
      }
      else
        gel(CHI,1) = gel(CHI,2) = gen_0;
    }
    else
      gel(CHI,1) = gel(CHI,2) = gen_0;
  }
  for (; i < l; i++,j++)
  {
    GEN p = gel(P,i);
    long k = ZV_search(Pq, p);
    gel(CHI,j) = k? mulii(gel(chi,k), powiu(p, E[i]-Eq[k])): gen_0;
  }
  return gerepilecopy(av, CHI);
}

/* m a Conrey log [on the canonical primitive roots], cycg the primitive
 * roots orders */
GEN
znconreylog_normalize(GEN G, GEN m)
{
  GEN cycg = znstar_get_conreycyc(G);
  long i, l;
  GEN d, M = cgetg_copy(m, &l);
  if (typ(cycg) != t_VEC || lg(cycg) != l)
    pari_err_TYPE("znconreylog_normalize",mkvec2(m,cycg));
  for (i = 1; i < l; i++) gel(M,i) = gdiv(gel(m,i), gel(cycg,i));
  /* m[i]: image of primroot generators g_i in Q/Z */
  M = Q_remove_denom(M, &d);
  return mkvec2(d? d: gen_1, M);
}

/* return normalized character on Conrey generators attached to chi: Conrey
 * label (t_INT), char on (SNF) G.gen* (t_VEC), or Conrey log (t_COL) */
GEN
znconrey_normalized(GEN G, GEN chi)
{
  switch(typ(chi))
  {
    case t_INT: /* Conrey label */
      return znconreylog_normalize(G, znconreylog(G, chi));
    case t_COL: /* Conrey log */
      if (!RgV_is_ZV(chi)) break;
      return znconreylog_normalize(G, chi);
    case t_VEC: /* char on G.gen */
      if (!RgV_is_ZV(chi)) break;
      return znconreyfromchar_normalized(G, chi);
  }
  pari_err_TYPE("znchareval",chi);
  return NULL;/* LCOV_EXCL_LINE */
}

/* return 1 iff chi(-1) = -1, and 0 otherwise */
long
zncharisodd(GEN G, GEN chi)
{
  long i, l, s;
  GEN N;
  if (!checkznstar_i(G)) pari_err_TYPE("zncharisodd", G);
  if (!zncharcheck(G, chi)) pari_err_TYPE("zncharisodd", chi);
  if (typ(chi) != t_COL) chi = znconreylog(G, chi);
  N = znstar_get_N(G);
  l = lg(chi);
  s = 0;
  if (!mod8(N))
  {
    s = mpodd(gel(chi,1));
    i = 3;
  }
  else
    i = 1;
  for (; i < l; i++) s += mpodd(gel(chi,i));
  return odd(s);
}

GEN
znchartokronecker(GEN G, GEN chi, long flag)
{
  pari_sp av = avma;
  long s;
  GEN F, o;

  if (flag && flag != 1) pari_err_FLAG("znchartokronecker");
  s = zncharisodd(G, chi)? -1: 1;
  if (typ(chi) != t_COL) chi = znconreylog(G, chi);
  o = zncharorder(G, chi);
  if (abscmpiu(o,2) > 0) { avma = av; return gen_0; }
  F = znconreyconductor(G, chi, NULL);
  if (typ(F) == t_INT)
  {
    if (s < 0) F = negi(F);
    return gerepileuptoint(av, F);
  }
  F = gel(F,1);
  F = (s < 0)? negi(F): icopy(F);
  if (!flag)
  {
    GEN MF = znstar_get_faN(G), P = gel(MF,1);
    long i, l = lg(P);
    for (i = 1; i < l; i++)
    {
      GEN p = gel(P,i);
      if (!dvdii(F,p)) F = mulii(F,sqri(p));
    }
  }
  return gerepileuptoint(av, F);
}

/* (D/.) as a character mod N; assume |D| divides N and D = 0,1 mod 4*/
GEN
znchar_quad(GEN G, GEN D)
{
  GEN cyc = znstar_get_conreycyc(G);
  GEN gen = znstar_get_conreygen(G);
  long i, l = lg(cyc);
  GEN chi = cgetg(l, t_COL);
  for (i = 1; i < l; i++)
  {
    long k = kronecker(D, gel(gen,i));
    gel(chi,i) = (k==1)? gen_0: shifti(gel(cyc,i), -1);
  }
  return chi;
}

GEN
znchar(GEN D)
{
  pari_sp av = avma;
  GEN G, chi;
  switch(typ(D))
  {
    case t_INT:
      if (!signe(D) || Mod4(D) > 1) pari_err_TYPE("znchar", D);
      G = znstar0(D,1);
      chi = mkvec2(G, znchar_quad(G,D));
      break;
    case t_INTMOD:
      G = znstar0(gel(D,1), 1);
      chi = mkvec2(G, znconreylog(G, gel(D,2)));
      break;
    case t_VEC:
      if (checkMF_i(D)) { chi = vecslice(MF_get_CHI(D),1,2); break; }
      else if (checkmf_i(D)) { chi = vecslice(mf_get_CHI(D),1,2); break; }
      if (lg(D) != 3) pari_err_TYPE("znchar", D);
      G = gel(D,1);
      if (!checkznstar_i(G)) pari_err_TYPE("znchar", D);
      chi = gel(D,2);
      if (typ(chi) == t_VEC && lg(chi) == 3 && is_vec_t(typ(gel(chi,2))))
      { /* normalized character */
        GEN n = gel(chi,1), chic = gel(chi,2);
        GEN cyc = typ(chic)==t_VEC? znstar_get_cyc(G): znstar_get_conreycyc(G);
        if (!char_check(cyc, chic)) pari_err_TYPE("znchar",D);
        chi = char_denormalize(cyc, n, chic);
      }
      if (!zncharcheck(G, chi)) pari_err_TYPE("znchar", D);
      chi = mkvec2(G,chi); break;
    default:
      pari_err_TYPE("znchar", D);
      return NULL; /*LCOV_EXCL_LINE*/
  }
  return gerepilecopy(av, chi);
}

/* G a znstar, not stack clean */
GEN
znchareval(GEN G, GEN chi, GEN n, GEN z)
{
  GEN nchi, N = znstar_get_N(G);
  /* avoid division by 0 */
  if (typ(n) == t_FRAC && !equali1(gcdii(gel(n,2), N))) return not_coprime(z);
  n = Rg_to_Fp(n, N);
  if (!equali1(gcdii(n, N))) return not_coprime(z);
  /* nchi: normalized character on Conrey generators */
  nchi = znconrey_normalized(G, chi);
  return chareval_i(nchi, znconreylog(G,n), z);
}

/* G is a znstar, chi a Dirichlet character */
GEN
zncharconj(GEN G, GEN chi)
{
  switch(typ(chi))
  {
    case t_INT: chi = znconreylog(G, chi); /* fall through */
    case t_COL: return charconj(znstar_get_conreycyc(G), chi);
    case t_VEC: return charconj(znstar_get_cyc(G), chi);
  }
  pari_err_TYPE("zncharconj",chi);
  return NULL; /*LCOV_EXCL_LINE*/
}

/* G is a znstar, chi a Dirichlet character */
GEN
zncharorder(GEN G,  GEN chi)
{
  switch(typ(chi))
  {
    case t_INT: chi = znconreylog(G, chi); /*fall through*/
    case t_COL: return charorder(znstar_get_conreycyc(G), chi);
    case t_VEC: return charorder(znstar_get_cyc(G), chi);
    default: pari_err_TYPE("zncharorder",chi);
             return NULL; /* LCOV_EXCL_LINE */
  }
}

/* G is a znstar, chi a Dirichlet character */
GEN
zncharker(GEN G, GEN chi)
{
  if (typ(chi) != t_VEC) chi = znconreychar(G, chi);
  return charker(znstar_get_cyc(G), chi);
}

/* G is a znstar, 'a' is a Dirichlet character */
GEN
zncharpow(GEN G, GEN a, GEN n)
{
  switch(typ(a))
  {
    case t_INT: return Fp_pow(a, n, znstar_get_N(G));
    case t_VEC: return charpow(znstar_get_cyc(G), a, n);
    case t_COL: return charpow(znstar_get_conreycyc(G), a, n);
    default: pari_err_TYPE("znchapow",a);
             return NULL; /* LCOV_EXCL_LINE */
  }
}
/* G is a znstar, 'a' and 'b' are Dirichlet character */
GEN
zncharmul(GEN G, GEN a, GEN b)
{
  long ta = typ(a), tb = typ(b);
  if (ta == tb) switch(ta)
  {
    case t_INT: return Fp_mul(a, b, znstar_get_N(G));
    case t_VEC: return charmul(znstar_get_cyc(G), a, b);
    case t_COL: return charmul(znstar_get_conreycyc(G), a, b);
    default: pari_err_TYPE("zncharmul",a);
             return NULL; /* LCOV_EXCL_LINE */
  }
  if (ta != t_COL) a = znconreylog(G, a);
  if (tb != t_COL) b = znconreylog(G, b);
  return charmul(znstar_get_conreycyc(G), a, b);
}

/* G is a znstar, 'a' and 'b' are Dirichlet character */
GEN
znchardiv(GEN G, GEN a, GEN b)
{
  long ta = typ(a), tb = typ(b);
  if (ta == tb) switch(ta)
  {
    case t_INT: return Fp_div(a, b, znstar_get_N(G));
    case t_VEC: return chardiv(znstar_get_cyc(G), a, b);
    case t_COL: return chardiv(znstar_get_conreycyc(G), a, b);
    default: pari_err_TYPE("znchardiv",a);
             return NULL; /* LCOV_EXCL_LINE */
  }
  if (ta != t_COL) a = znconreylog(G, a);
  if (tb != t_COL) b = znconreylog(G, b);
  return chardiv(znstar_get_conreycyc(G), a, b);
}

/* CHI mod N = \prod_p p^e; let CHI = \prod CHI_p, CHI_p mod p^e
 * return \prod_{p | (Q,N)} CHI_p. E.g if Q = p, return chi_p */
GEN
znchardecompose(GEN G, GEN chi, GEN Q)
{
  GEN c, P, E, F;
  long l, lP, i;

  if (!checkznstar_i(G)) pari_err_TYPE("znchardecompose", G);
  if (typ(Q) != t_INT) pari_err_TYPE("znchardecompose", Q);
  if (typ(chi) == t_COL)
  { if (!zncharcheck(G, chi)) pari_err_TYPE("znchardecompose", chi); }
  else
    chi = znconreylog(G, chi);
  l = lg(chi);
  F = znstar_get_faN(G);
  c = zerocol(l-1);
  P = gel(F,1); /* prime divisors of N */
  lP = lg(P);
  E = gel(F,2); /* exponents */
  for (i = 1; i < lP; i++)
  {
    GEN p = gel(P,i);
    if (i == 1 && equaliu(p,2) && E[1] >= 3)
    {
      if (!mpodd(Q))
      {
        gel(c,1) = icopy(gel(chi,1));
        gel(c,2) = icopy(gel(chi,2));
      }
      i = 2; /* skip P[2] = P[1] = 2 */
    }
    else
      if (dvdii(Q, p)) gel(c,i) = icopy(gel(chi,i));
  }
  return c;
}

GEN
zncharconductor(GEN G, GEN chi)
{
  pari_sp av = avma;
  GEN F = znconreyconductor(G, chi, NULL);
  if (typ(F) == t_INT) return F;
  return gerepilecopy(av, gel(F,1));
}
GEN
znchartoprimitive(GEN G, GEN chi)
{
  pari_sp av = avma;
  GEN chi0, F = znconreyconductor(G, chi, &chi0);
  if (typ(F) == t_INT)
    chi = mkvec2(G,chi);
  else
    chi = mkvec2(znstar0(F,1), chi0);
  return gerepilecopy(av, chi);
}
