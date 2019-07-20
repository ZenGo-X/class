/* Copyright (C) 2011  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA. */

#include "pari.h"
#include "paripriv.h"

/* Adapted from shp_package/moments by Robert Pollack
 * http://www.math.mcgill.ca/darmon/programs/shp/shp.html */
static GEN mskinit(ulong N, long k, long sign);
static GEN mshecke_i(GEN W, ulong p);
static GEN ZSl2_star(GEN v);
static GEN getMorphism(GEN W1, GEN W2, GEN v);
static GEN voo_act_Gl2Q(GEN g, long k);

/* Input: P^1(Z/NZ) (formed by create_p1mod)
   Output: # P^1(Z/NZ) */
static long
p1_size(GEN p1N) { return lg(gel(p1N,1)) - 1; }
static ulong
p1N_get_N(GEN p1N) { return gel(p1N,3)[2]; }
static GEN
p1N_get_hash(GEN p1N) { return gel(p1N,2); }
static GEN
p1N_get_fa(GEN p1N) { return gel(p1N,4); }
static GEN
p1N_get_div(GEN p1N) { return gel(p1N,5); }
static GEN
p1N_get_invsafe(GEN p1N) { return gel(p1N,6); }
static GEN
p1N_get_inverse(GEN p1N) { return gel(p1N,7); }

/* ms-specific accessors */
/* W = msinit, return the output of msinit_N */
static GEN
get_msN(GEN W) { return lg(W) == 4? gel(W,1): W; }
static GEN
msN_get_p1N(GEN W) { return gel(W,1); }
static GEN
msN_get_genindex(GEN W) { return gel(W,5); }
static GEN
msN_get_E2fromE1(GEN W) { return gel(W,7); }
static GEN
msN_get_annT2(GEN W) { return gel(W,8); }
static GEN
msN_get_annT31(GEN W) { return gel(W,9); }
static GEN
msN_get_singlerel(GEN W) { return gel(W,10); }
static GEN
msN_get_section(GEN W) { return gel(W,12); }

static GEN
ms_get_p1N(GEN W) { return msN_get_p1N(get_msN(W)); }
static long
ms_get_N(GEN W) { return p1N_get_N(ms_get_p1N(W)); }
static GEN
ms_get_hashcusps(GEN W) { W = get_msN(W); return gel(W,16); }
static GEN
ms_get_section(GEN W) { return msN_get_section(get_msN(W)); }
static GEN
ms_get_genindex(GEN W) { return msN_get_genindex(get_msN(W)); }
static long
ms_get_nbgen(GEN W) { return lg(ms_get_genindex(W))-1; }
static long
ms_get_nbE1(GEN W)
{
  GEN W11;
  W = get_msN(W); W11 = gel(W,11);
  return W11[4] - W11[3];
}

/* msk-specific accessors */
static long
msk_get_dim(GEN W) { return gmael(W,3,2)[2]; }
static GEN
msk_get_basis(GEN W) { return gmael(W,3,1); }
static long
msk_get_weight(GEN W) { return gmael(W,3,2)[1]; }
static long
msk_get_sign(GEN W)
{
  GEN t = gel(W,2);
  return typ(t)==t_INT? 0: itos(gel(t,1));
}
static GEN
msk_get_star(GEN W) { return gmael(W,2,2); }
static GEN
msk_get_starproj(GEN W) { return gmael(W,2,3); }

static int
is_Qevproj(GEN x)
{ return typ(x) == t_VEC && lg(x) == 5 && typ(gel(x,1)) == t_MAT; }
long
msdim(GEN W)
{
  if (is_Qevproj(W)) return lg(gel(W,1)) - 1;
  checkms(W);
  if (!msk_get_sign(W)) return msk_get_dim(W);
  return lg(gel(msk_get_starproj(W), 1)) - 1;
}
long
msgetlevel(GEN W) { checkms(W); return ms_get_N(W); }
long
msgetweight(GEN W) { checkms(W); return msk_get_weight(W); }
long
msgetsign(GEN W) { checkms(W); return msk_get_sign(W); }

void
checkms(GEN W)
{
  if (typ(W) != t_VEC || lg(W) != 4)
    pari_err_TYPE("checkms [please apply msinit]", W);
}

/** MODULAR TO SYM **/

/* q a t_FRAC or t_INT */
static GEN
Q_log_init(ulong N, GEN q)
{
  long l, n;
  GEN Q;

  q = gboundcf(q, 0);
  l = lg(q);
  Q = cgetg(l, t_VECSMALL);
  Q[1] = 1;
  for (n=2; n <l; n++) Q[n] = umodiu(gel(q,n), N);
  for (n=3; n < l; n++)
    Q[n] = Fl_add(Fl_mul(Q[n], Q[n-1], N), Q[n-2], N);
  return Q;
}

/** INIT MODSYM STRUCTURE, WEIGHT 2 **/

/* num = [Gamma : Gamma_0(N)] = N * Prod_{p|N} (1+p^-1) */
static ulong
count_Manin_symbols(ulong N, GEN P)
{
  long i, l = lg(P);
  ulong num = N;
  for (i = 1; i < l; i++) { ulong p = P[i]; num *= p+1; num /= p; }
  return num;
}
/* returns the list of "Manin symbols" (c,d) in (Z/NZ)^2, (c,d,N) = 1
 * generating H^1(X_0(N), Z) */
static GEN
generatemsymbols(ulong N, ulong num, GEN divN)
{
  GEN ret = cgetg(num+1, t_VEC);
  ulong c, d, curn = 0;
  long i, l;
  /* generate Manin-symbols in two lists: */
  /* list 1: (c:1) for 0 <= c < N */
  for (c = 0; c < N; c++) gel(ret, ++curn) = mkvecsmall2(c, 1);
  if (N == 1) return ret;
  /* list 2: (c:d) with 1 <= c < N, c | N, 0 <= d < N, gcd(d,N) > 1, gcd(c,d)=1.
   * Furthermore, d != d0 (mod N/c) with c,d0 already in the list */
  l = lg(divN) - 1;
  /* c = 1 first */
  gel(ret, ++curn) = mkvecsmall2(1,0);
  for (d = 2; d < N; d++)
    if (ugcd(d,N) != 1UL)
      gel(ret, ++curn) = mkvecsmall2(1,d);
  /* omit c = 1 (first) and c = N (last) */
  for (i=2; i < l; i++)
  {
    ulong Novc, d0;
    c = divN[i];
    Novc = N / c;
    for (d0 = 2; d0 <= Novc; d0++)
    {
      ulong k, d = d0;
      if (ugcd(d, Novc) == 1UL) continue;
      for (k = 0; k < c; k++, d += Novc)
        if (ugcd(c,d) == 1UL)
        {
          gel(ret, ++curn) = mkvecsmall2(c,d);
          break;
        }
    }
  }
  if (curn != num) pari_err_BUG("generatemsymbols [wrong number of symbols]");
  return ret;
}

static GEN
inithashmsymbols(ulong N, GEN symbols)
{
  GEN H = zerovec(N);
  long k, l = lg(symbols);
  /* skip the (c:1), 0 <= c < N and (1:0) */
  for (k=N+2; k < l; k++)
  {
    GEN s = gel(symbols, k);
    ulong c = s[1], d = s[2], Novc = N/c;
    if (gel(H,c) == gen_0) gel(H,c) = const_vecsmall(Novc+1,0);
    if (c != 1) { d %= Novc; if (!d) d = Novc; }
    mael(H, c, d) = k;
  }
  return H;
}

/** Helper functions for Sl2(Z) / Gamma_0(N) **/
/* M a 2x2 ZM in SL2(Z) */
static GEN
SL2_inv(GEN M)
{
  GEN a = gcoeff(M,1,1), b = gcoeff(M,1,2);
  GEN c = gcoeff(M,2,1), d = gcoeff(M,2,2);
  return mkmat22(d,negi(b), negi(c),a);
}
/* SL2_inv(M)[2] */
static GEN
SL2_inv2(GEN M)
{
  GEN a = gcoeff(M,1,1), b = gcoeff(M,1,2);
  return mkcol2(negi(b),a);
}
/* M a 2x2 mat2 in SL2(Z) */
static GEN
sl2_inv(GEN M)
{
  long a=coeff(M,1,1), b=coeff(M,1,2), c=coeff(M,2,1), d=coeff(M,2,2);
  return mkvec2(mkvecsmall2(d, -c), mkvecsmall2(-b, a));
}
/* Return the mat2 [a,b; c,d], not a zm to avoid GP problems */
static GEN
mat2(long a, long b, long c, long d)
{ return mkvec2(mkvecsmall2(a,c), mkvecsmall2(b,d)); }
static GEN
mat2_to_ZM(GEN M)
{
  GEN A = gel(M,1), B = gel(M,2);
  retmkmat2(mkcol2s(A[1],A[2]), mkcol2s(B[1],B[2]));
}

/* Input: a = 2-vector = path = {r/s,x/y}
 * Output: either [r,x;s,y] or [-r,x;-s,y], whichever has determinant > 0 */
static GEN
path_to_ZM(GEN a)
{
  GEN v = gel(a,1), w = gel(a,2);
  long r = v[1], s = v[2], x = w[1], y = w[2];
  if (cmpii(mulss(r,y), mulss(x,s)) < 0) { r = -r; s = -s; }
  return mkmat22(stoi(r),stoi(x),stoi(s),stoi(y));
}
static GEN
path_to_zm(GEN a)
{
  GEN v = gel(a,1), w = gel(a,2);
  long r = v[1], s = v[2], x = w[1], y = w[2];
  if (cmpii(mulss(r,y), mulss(x,s)) < 0) { r = -r; s = -s; }
  return mat2(r,x,s,y);
}
/* path from c1 to c2 */
static GEN
mkpath(GEN c1, GEN c2) { return mat2(c1[1], c2[1], c1[2], c2[2]); }
static long
cc(GEN M) { GEN v = gel(M,1); return v[2]; }
static long
dd(GEN M) { GEN v = gel(M,2); return v[2]; }

/*Input: a,b = 2 paths, N = integer
 *Output: 1 if the a,b are \Gamma_0(N)-equivalent; 0 otherwise */
static int
gamma_equiv(GEN a, GEN b, ulong N)
{
  pari_sp av = avma;
  GEN m = path_to_zm(a);
  GEN n = path_to_zm(b);
  GEN d = subii(mulss(cc(m),dd(n)), mulss(dd(m),cc(n)));
  ulong res = umodiu(d, N);
  avma = av; return res == 0;
}
/* Input: a,b = 2 paths that are \Gamma_0(N)-equivalent, N = integer
 * Output: M in \Gamma_0(N) such that Mb=a */
static GEN
gamma_equiv_matrix(GEN a, GEN b)
{
  GEN m = path_to_ZM(a);
  GEN n = path_to_ZM(b);
  return ZM_mul(m, SL2_inv(n));
}

/*************/
/* P^1(Z/NZ) */
/*************/
/* a != 0 in Z/NZ. Return v in (Z/NZ)^* such that av = gcd(a, N) (mod N)*/
static ulong
Fl_inverse(ulong a, ulong N) { ulong g; return Fl_invgen(a,N,&g); }

/* Input: N = integer
 * Output: creates P^1(Z/NZ) = [symbols, H, N]
 *   symbols: list of vectors [x,y] that give a set of representatives
 *            of P^1(Z/NZ)
 *   H: an M by M grid whose value at the r,c-th place is the index of the
 *      "standard representative" equivalent to [r,c] occuring in the first
 *      list. If gcd(r,c,N) > 1 the grid has value 0. */
static GEN
create_p1mod(ulong N)
{
  GEN fa = factoru(N), div = divisorsu_fact(fa);
  ulong i, nsym = count_Manin_symbols(N, gel(fa,1));
  GEN symbols = generatemsymbols(N, nsym, div);
  GEN H = inithashmsymbols(N,symbols);
  GEN invsafe = cgetg(N, t_VECSMALL), inverse = cgetg(N, t_VECSMALL);
  for (i = 1; i < N; i++)
  {
    invsafe[i] = Fl_invsafe(i,N);
    inverse[i] = Fl_inverse(i,N);
  }
  return mkvecn(7, symbols, H, utoipos(N), fa, div, invsafe, inverse);
}

/* Let (c : d) in P1(Z/NZ).
 * If c = 0 return (0:1). If d = 0 return (1:0).
 * Else replace by (cu : du), where u in (Z/NZ)^* such that C := cu = gcd(c,N).
 * In create_p1mod(), (c : d) is represented by (C:D) where D = du (mod N/c)
 * is smallest such that gcd(C,D) = 1. Return (C : du mod N/c), which need
 * not belong to P1(Z/NZ) ! A second component du mod N/c = 0 is replaced by
 * N/c in this case to avoid problems with array indices */
static void
p1_std_form(long *pc, long *pd, GEN p1N)
{
  ulong N = p1N_get_N(p1N);
  ulong u;
  *pc = smodss(*pc, N); if (!*pc) { *pd = 1; return; }
  *pd = smodss(*pd, N); if (!*pd) { *pc = 1; return; }
  u = p1N_get_invsafe(p1N)[*pd];
  if (u) { *pc = Fl_mul(*pc,u,N); *pd = 1; return; } /* (d,N) = 1 */

  u = p1N_get_inverse(p1N)[*pc];
  if (u > 1) { *pc = Fl_mul(*pc,u,N); *pd = Fl_mul(*pd,u,N); }
  /* c | N */
  if (*pc != 1) *pd %= (N / *pc);
  if (!*pd) *pd = N / *pc;
}

/* Input: v = [x,y] = elt of P^1(Z/NZ) = class in Gamma_0(N) \ PSL2(Z)
 * Output: returns the index of the standard rep equivalent to v */
static long
p1_index(long x, long y, GEN p1N)
{
  ulong N = p1N_get_N(p1N);
  GEN H = p1N_get_hash(p1N);

  p1_std_form(&x, &y, p1N);
  if (y == 1) return x+1;
  if (y == 0) return N+1;
  if (mael(H,x,y) == 0) pari_err_BUG("p1_index");
  return mael(H,x,y);
}

/* Cusps for \Gamma_0(N) */

/* \sum_{d | N} \phi(gcd(d, N/d)), using multiplicativity. fa = factor(N) */
ulong
mfnumcuspsu_fact(GEN fa)
{
  GEN P = gel(fa,1), E = gel(fa,2);
  long i, l = lg(P);
  ulong T = 1;
  for (i = 1; i < l; i++)
  {
    long e = E[i], e2 = e >> 1; /* floor(E[i] / 2) */
    ulong p = P[i];
    if (odd(e))
      T *= 2 * upowuu(p, e2);
    else
      T *= (p+1) * upowuu(p, e2-1);
  }
  return T;
}
ulong
mfnumcuspsu(ulong n)
{
  pari_sp av = avma;
  ulong t = mfnumcuspsu_fact( factoru(n) );
  avma = av; return t;
}
/* \sum_{d | N} \phi(gcd(d, N/d)), using multiplicativity. fa = factor(N) */
GEN
mfnumcusps_fact(GEN fa)
{
  GEN P = gel(fa,1), E = gel(fa,2), T = gen_1;
  long i, l = lg(P);
  for (i = 1; i < l; i++)
  {
    GEN p = gel(P,i), c;
    long e = itos(gel(E,i)), e2 = e >> 1; /* floor(E[i] / 2) */
    if (odd(e))
      c = shifti(powiu(p, e2), 1);
    else
      c = mulii(addiu(p,1), powiu(p, e2-1));
    T = T? mulii(T, c): c;
  }
  return T? T: gen_1;
}
GEN
mfnumcusps(GEN n)
{
  pari_sp av = avma;
  GEN F = check_arith_pos(n,"mfnumcusps");
  if (!F)
  {
    if (lgefint(n) == 3) return utoi( mfnumcuspsu(n[2]) );
    F = absZ_factor(n);
  }
  return gerepileuptoint(av, mfnumcusps_fact(F));
}


/* to each cusp in \Gamma_0(N) P1(Q), represented by p/q, we associate a
 * unique index. Canonical representative: (1:0) or (p:q) with q | N, q < N,
 * p defined modulo d := gcd(N/q,q), (p,d) = 1.
 * Return [[N, nbcusps], H, cusps]*/
static GEN
inithashcusps(GEN p1N)
{
  ulong N = p1N_get_N(p1N);
  GEN div = p1N_get_div(p1N), H = zerovec(N+1);
  long k, ind, l = lg(div), ncusp = mfnumcuspsu_fact(p1N_get_fa(p1N));
  GEN cusps = cgetg(ncusp+1, t_VEC);

  gel(H,1) = mkvecsmall2(0/*empty*/, 1/* first cusp: (1:0) */);
  gel(cusps, 1) = mkvecsmall2(1,0);
  ind = 2;
  for (k=1; k < l-1; k++) /* l-1: remove q = N */
  {
    ulong p, q = div[k], d = ugcd(q, N/q);
    GEN h = const_vecsmall(d+1,0);
    gel(H,q+1) = h ;
    for (p = 0; p < d; p++)
      if (ugcd(p,d) == 1)
      {
        h[p+1] = ind;
        gel(cusps, ind) = mkvecsmall2(p,q);
        ind++;
      }
  }
  return mkvec3(mkvecsmall2(N,ind-1), H, cusps);
}
/* c = [p,q], (p,q) = 1, return a canonical representative for
 * \Gamma_0(N)(p/q) */
static GEN
cusp_std_form(GEN c, GEN S)
{
  long p, N = gel(S,1)[1], q = smodss(c[2], N);
  ulong u, d;
  if (q == 0) return mkvecsmall2(1, 0);
  p = smodss(c[1], N);
  u = Fl_inverse(q, N);
  q = Fl_mul(q,u, N);
  d = ugcd(q, N/q);
  return mkvecsmall2(Fl_div(p % d,u % d, d), q);
}
/* c = [p,q], (p,q) = 1, return the index of the corresponding cusp.
 * S from inithashcusps */
static ulong
cusp_index(GEN c, GEN S)
{
  long p, q;
  GEN H = gel(S,2);
  c = cusp_std_form(c, S);
  p = c[1]; q = c[2];
  if (!mael(H,q+1,p+1)) pari_err_BUG("cusp_index");
  return mael(H,q+1,p+1);
}

/* M a square invertible ZM, return a ZM iM such that iM M = M iM = d.Id */
static GEN
ZM_inv_denom(GEN M)
{
  GEN diM, iM = ZM_inv(M, &diM);
  return mkvec2(iM, diM);
}
/* return M^(-1) v, dinv = ZM_inv_denom(M) OR Qevproj_init(M) */
static GEN
ZC_apply_dinv(GEN dinv, GEN v)
{
  GEN x, c, iM;
  if (lg(dinv) == 3)
  {
    iM = gel(dinv,1);
    c = gel(dinv,2);
  }
  else
  { /* Qevproj_init */
    iM = gel(dinv,2);
    c = gel(dinv,3);
    v = typ(v) == t_MAT? rowpermute(v, gel(dinv,4))
                       : vecpermute(v, gel(dinv,4));
  }
  x = RgM_RgC_mul(iM, v);
  if (!isint1(c)) x = RgC_Rg_div(x, c);
  return x;
}

/* M an n x d ZM of rank d (basis of a Q-subspace), n >= d.
 * Initialize a projector on M */
GEN
Qevproj_init(GEN M)
{
  GEN v, perm, MM, iM, diM;
  v = ZM_indexrank(M); perm = gel(v,1);
  MM = rowpermute(M, perm); /* square invertible */
  iM = ZM_inv(MM, &diM);
  return mkvec4(M, iM, diM, perm);
}

/* same with typechecks */
static GEN
Qevproj_init0(GEN M)
{
  switch(typ(M))
  {
    case t_VEC:
      if (lg(M) == 5) return M;
      break;
    case t_COL:
      M = mkmat(M);/*fall through*/
    case t_MAT:
      M = Q_primpart(M);
      RgM_check_ZM(M,"Qevproj_init");
      return Qevproj_init(M);
  }
  pari_err_TYPE("Qevproj_init",M);
  return NULL;
}

/* T an n x n QM, pro = Qevproj_init(M), pro2 = Qevproj_init(M2); TM \subset M2.
 * Express these column vectors on M2's basis */
static GEN
Qevproj_apply2(GEN T, GEN pro, GEN pro2)
{
  GEN M = gel(pro,1), iM = gel(pro2,2), ciM = gel(pro2,3), perm = gel(pro2,4);
  return RgM_Rg_div(RgM_mul(iM, RgM_mul(rowpermute(T,perm), M)), ciM);
}
/* T an n x n QM, stabilizing d-dimensional Q-vector space spanned by the
 * d columns of M, pro = Qevproj_init(M). Return dxd matrix of T acting on M */
GEN
Qevproj_apply(GEN T, GEN pro) { return Qevproj_apply2(T, pro, pro); }
/* Qevproj_apply(T,pro)[,k] */
GEN
Qevproj_apply_vecei(GEN T, GEN pro, long k)
{
  GEN M = gel(pro,1), iM = gel(pro,2), ciM = gel(pro,3), perm = gel(pro,4);
  GEN v = RgM_RgC_mul(iM, RgM_RgC_mul(rowpermute(T,perm), gel(M,k)));
  return RgC_Rg_div(v, ciM);
}

static GEN
QM_ker_r(GEN M) { return ZM_ker(Q_primpart(M)); }
static GEN
QM_image(GEN A)
{
  A = vec_Q_primpart(A);
  return vecpermute(A, ZM_indeximage(A));
}

static int
cmp_dim(void *E, GEN a, GEN b)
{
  long k;
  (void)E;
  a = gel(a,1);
  b = gel(b,1); k = lg(a)-lg(b);
  return k? ((k > 0)? 1: -1): 0;
}

/* FIXME: could use ZX_roots for deglim = 1 */
static GEN
ZX_factor_limit(GEN T, long deglim, long *pl)
{
  GEN fa = ZX_factor(T), P, E;
  long i, l;
  P = gel(fa,1); *pl = l = lg(P);
  if (deglim <= 0) return fa;
  E = gel(fa,2);
  for (i = 1; i < l; i++)
    if (degpol(gel(P,i)) > deglim) break;
  setlg(P,i);
  setlg(E,i); return fa;
}

/* Decompose the subspace H (Qevproj format) in simple subspaces.
 * Eg for H = msnew */
static GEN
mssplit_i(GEN W, GEN H, long deglim)
{
  ulong p, N = ms_get_N(W);
  long first, dim;
  forprime_t S;
  GEN T1 = NULL, T2 = NULL, V;
  dim = lg(gel(H,1))-1;
  V = vectrunc_init(dim+1);
  if (!dim) return V;
  (void)u_forprime_init(&S, 2, ULONG_MAX);
  vectrunc_append(V, H);
  first = 1; /* V[1..first-1] contains simple subspaces */
  while ((p = u_forprime_next(&S)))
  {
    GEN T;
    long j, lV;
    if (N % p == 0) continue;
    if (T1 && T2) {
      T = RgM_add(T1,T2);
      T2 = NULL;
    } else {
      T2 = T1;
      T1 = T = mshecke(W, p, NULL);
    }
    lV = lg(V);
    for (j = first; j < lV; j++)
    {
      pari_sp av = avma;
      long lP;
      GEN Vj = gel(V,j), P = gel(Vj,1);
      GEN TVj = Qevproj_apply(T, Vj); /* c T | V_j */
      GEN ch = QM_charpoly_ZX(TVj), fa = ZX_factor_limit(ch,deglim, &lP);
      GEN F = gel(fa, 1), E = gel(fa, 2);
      long k, lF = lg(F);
      if (lF == 2 && lP == 2)
      {
        if (isint1(gel(E,1)))
        { /* simple subspace */
          swap(gel(V,first), gel(V,j));
          first++;
        }
        else
          avma = av;
      }
      else if (lF == 1) /* discard V[j] */
      { swap(gel(V,j), gel(V,lg(V)-1)); setlg(V, lg(V)-1); }
      else
      { /* can split Vj */
        GEN pows;
        long D = 1;
        for (k = 1; k < lF; k++)
        {
          long d = degpol(gel(F,k));
          if (d > D) D = d;
        }
        /* remove V[j] */
        swap(gel(V,j), gel(V,lg(V)-1)); setlg(V, lg(V)-1);
        pows = RgM_powers(TVj, minss((long)2*sqrt((double)D), D));
        for (k = 1; k < lF; k++)
        {
          GEN f = gel(F,k);
          GEN K = QM_ker_r( RgX_RgMV_eval(f, pows)) ; /* Ker f(TVj) */
          GEN p = vec_Q_primpart( RgM_mul(P, K) );
          vectrunc_append(V, Qevproj_init(p));
          if (lg(K) == 2 || isint1(gel(E,k)))
          { /* simple subspace */
            swap(gel(V,first), gel(V, lg(V)-1));
            first++;
          }
        }
        if (j < first) j = first;
      }
    }
    if (first >= lg(V)) {
      gen_sort_inplace(V, NULL, cmp_dim, NULL);
      return V;
    }
  }
  pari_err_BUG("subspaces not found");
  return NULL;
}
GEN
mssplit(GEN W, GEN H, long deglim)
{
  pari_sp av = avma;
  checkms(W);
  if (!msk_get_sign(W))
    pari_err_DOMAIN("mssplit","abs(sign)","!=",gen_1,gen_0);
  if (!H) H = msnew(W);
  H = Qevproj_init0(H);
  return gerepilecopy(av, mssplit_i(W,H,deglim));
}

/* proV = Qevproj_init of a Hecke simple subspace, return [ a_n, n <= B ] */
static GEN
msqexpansion_i(GEN W, GEN proV, ulong B)
{
  ulong p, N = ms_get_N(W), sqrtB;
  long i, d, k = msk_get_weight(W);
  forprime_t S;
  GEN T1=NULL, T2=NULL, TV=NULL, ch=NULL, v, dTiv, Tiv, diM, iM, L;
  switch(B)
  {
    case 0: return cgetg(1,t_VEC);
    case 1: return mkvec(gen_1);
  }
  (void)u_forprime_init(&S, 2, ULONG_MAX);
  while ((p = u_forprime_next(&S)))
  {
    GEN T;
    if (N % p == 0) continue;
    if (T1 && T2)
    {
      T = RgM_add(T1,T2);
      T2 = NULL;
    }
    else
    {
      T2 = T1;
      T1 = T = mshecke(W, p, NULL);
    }
    TV = Qevproj_apply(T, proV); /* T | V */
    ch = QM_charpoly_ZX(TV);
    if (ZX_is_irred(ch)) break;
    ch = NULL;
  }
  if (!ch) pari_err_BUG("q-Expansion not found");
  /* T generates the Hecke algebra (acting on V) */
  d = degpol(ch);
  v = vec_ei(d, 1); /* take v = e_1 */
  Tiv = cgetg(d+1, t_MAT); /* Tiv[i] = T^(i-1)v */
  gel(Tiv, 1) = v;
  for (i = 2; i <= d; i++) gel(Tiv, i) = RgM_RgC_mul(TV, gel(Tiv,i-1));
  Tiv = Q_remove_denom(Tiv, &dTiv);
  iM = ZM_inv(Tiv, &diM);
  if (dTiv) diM = gdiv(diM, dTiv);
  L = const_vec(B,NULL);
  sqrtB = usqrt(B);
  gel(L,1) = d > 1? mkpolmod(gen_1,ch): gen_1;
  for (p = 2; p <= B; p++)
  {
    pari_sp av = avma;
    GEN T, u, Tv, ap, P;
    ulong m;
    if (gel(L,p)) continue;  /* p not prime */
    T = mshecke(W, p, NULL);
    Tv = Qevproj_apply_vecei(T, proV, 1); /* Tp.v */
    /* Write Tp.v = \sum u_i T^i v */
    u = RgC_Rg_div(RgM_RgC_mul(iM, Tv), diM);
    ap = gerepilecopy(av, RgV_to_RgX(u, 0));
    if (d > 1)
      ap = mkpolmod(ap,ch);
    else
      ap = simplify_shallow(ap);
    gel(L,p) = ap;
    if (!(N % p))
    { /* p divides the level */
      ulong C = B/p;
      for (m=1; m<=C; m++)
        if (gel(L,m)) gel(L,m*p) = gmul(gel(L,m), ap);
      continue;
    }
    P = powuu(p,k-1);
    if (p <= sqrtB) {
      ulong pj, oldpj = 1;
      for (pj = p; pj <= B; oldpj=pj, pj *= p)
      {
        GEN apj = (pj==p)? ap
                         : gsub(gmul(ap,gel(L,oldpj)), gmul(P,gel(L,oldpj/p)));
        gel(L,pj) = apj;
        for (m = B/pj; m > 1; m--)
          if (gel(L,m) && m%p) gel(L,m*pj) = gmul(gel(L,m), apj);
      }
    } else {
      gel(L,p) = ap;
      for (m = B/p; m > 1; m--)
        if (gel(L,m)) gel(L,m*p) = gmul(gel(L,m), ap);
    }
  }
  return L;
}
GEN
msqexpansion(GEN W, GEN proV, ulong B)
{
  pari_sp av = avma;
  checkms(W);
  proV = Qevproj_init0(proV);
  return gerepilecopy(av, msqexpansion_i(W,proV,B));
}

static GEN
Qevproj_apply0(GEN T, GEN pro)
{
  GEN iM = gel(pro,2), perm = gel(pro,4);
  return vec_Q_primpart(ZM_mul(iM, rowpermute(T,perm)));
}
/* T a ZC or ZM */
GEN
Qevproj_down(GEN T, GEN pro)
{
  GEN iM = gel(pro,2), ciM = gel(pro,3), perm = gel(pro,4);
  if (typ(T) == t_COL)
    return RgC_Rg_div(ZM_ZC_mul(iM, vecpermute(T,perm)), ciM);
  else
    return RgM_Rg_div(ZM_mul(iM, rowpermute(T,perm)), ciM);
}

static GEN
Qevproj_star(GEN W, GEN H)
{
  long s = msk_get_sign(W);
  if (s)
  { /* project on +/- component */
    GEN A = RgM_mul(msk_get_star(W), H);
    A = (s > 0)? gadd(A, H): gsub(A, H);
    /* Im(star + sign) = Ker(star - sign) */
    H = QM_image(A);
    H = Qevproj_apply0(H, msk_get_starproj(W));
  }
  return H;
}

static GEN
Tp_matrices(ulong p)
{
  GEN v = cgetg(p+2, t_VEC);
  ulong i;
  for (i = 1; i <= p; i++) gel(v,i) = mat2(1, i-1, 0, p);
  gel(v,i) = mat2(p, 0, 0, 1);
  return v;
}
static GEN
Up_matrices(ulong p)
{
  GEN v = cgetg(p+1, t_VEC);
  ulong i;
  for (i = 1; i <= p; i++) gel(v,i) = mat2(1, i-1, 0, p);
  return v;
}

/* M = N/p. Classes of Gamma_0(M) / Gamma_O(N) when p | M */
static GEN
NP_matrices(ulong M, ulong p)
{
  GEN v = cgetg(p+1, t_VEC);
  ulong i;
  for (i = 1; i <= p; i++) gel(v,i) = mat2(1, 0, (i-1)*M, 1);
  return v;
}
/* M = N/p. Extra class of Gamma_0(M) / Gamma_O(N) when p \nmid M */
static GEN
NP_matrix_extra(ulong M, ulong p)
{
  long w,z, d = cbezout(p, -M, &w, &z);
  if (d != 1) return NULL;
  return mat2(w,z,M,p);
}
static GEN
WQ_matrix(long N, long Q)
{
  long w,z, d = cbezout(Q, N/Q, &w, &z);
  if (d != 1) return NULL;
  return mat2(Q,1,-N*z,Q*w);
}

GEN
msnew(GEN W)
{
  pari_sp av = avma;
  GEN S = mscuspidal(W, 0);
  ulong N = ms_get_N(W);
  long s = msk_get_sign(W), k = msk_get_weight(W);
  if (N > 1 && (!uisprime(N) || (k == 12 || k > 14)))
  {
    GEN p1N = ms_get_p1N(W), P = gel(p1N_get_fa(p1N), 1);
    long i, nP = lg(P)-1;
    GEN v = cgetg(2*nP + 1, t_COL);
    S = gel(S,1); /* Q basis */
    for (i = 1; i <= nP; i++)
    {
      pari_sp av = avma, av2;
      long M = N/P[i];
      GEN T1,Td, Wi = mskinit(M, k, s);
      GEN v1 = NP_matrices(M, P[i]);
      GEN vd = Up_matrices(P[i]);
      /* p^2 \nmid N */
      if (M % P[i])
      {
        v1 = shallowconcat(v1, mkvec(NP_matrix_extra(M,P[i])));
        vd = shallowconcat(vd, mkvec(WQ_matrix(N,P[i])));
      }
      T1 = getMorphism(W, Wi, v1);
      Td = getMorphism(W, Wi, vd);
      if (s)
      {
        T1 = Qevproj_apply2(T1, msk_get_starproj(W), msk_get_starproj(Wi));
        Td = Qevproj_apply2(Td, msk_get_starproj(W), msk_get_starproj(Wi));
      }
      av2 = avma;
      T1 = RgM_mul(T1,S);
      Td = RgM_mul(Td,S);  /* multiply by S = restrict to mscusp */
      gerepileallsp(av, av2, 2, &T1, &Td);
      gel(v,2*i-1) = T1;
      gel(v,2*i)   = Td;
    }
    S = ZM_mul(S, QM_ker_r(matconcat(v))); /* Snew */
    S = Qevproj_init(vec_Q_primpart(S));
  }
  return gerepilecopy(av, S);
}

/* Solve the Manin relations for a congruence subgroup \Gamma by constructing
 * a well-formed fundamental domain for the action of \Gamma on upper half
 * space. See
 * Pollack and Stevens, Overconvergent modular symbols and p-adic L-functions
 * Annales scientifiques de l'ENS 44, fascicule 1 (2011), 1-42
 * http://math.bu.edu/people/rpollack/Papers/Overconvergent_modular_symbols_and_padic_Lfunctions.pdf
 *
 * FIXME: Implemented for \Gamma = \Gamma_0(N) only. */

#if 0 /* Pollack-Stevens shift their paths so as to solve equations of the
         form f(z+1) - f(z) = g. We don't (to avoid mistakes) so we will
         have to solve eqs of the form f(z-1) - f(z) = g */
/* c = a/b; as a t_VECSMALL [a,b]; return c-1 as a t_VECSMALL */
static GEN
Shift_left_cusp(GEN c) { long a=c[1], b=c[2]; return mkvecsmall2(a - b, b); }
/* c = a/b; as a t_VECSMALL [a,b]; return c+1 as a t_VECSMALL */
static GEN
Shift_right_cusp(GEN c) { long a=c[1], b=c[2]; return mkvecsmall2(a + b, b); }
/*Input: path = [r,s] (thought of as a geodesic between these points)
 *Output: The path shifted by one to the left, i.e. [r-1,s-1] */
static GEN
Shift_left(GEN path)
{
  GEN r = gel(path,1), s = gel(path,2);
  return mkvec2(Shift_left_cusp(r), Shift_left_cusp(s)); }
/*Input: path = [r,s] (thought of as a geodesic between these points)
 *Output: The path shifted by one to the right, i.e. [r+1,s+1] */
GEN
Shift_right(GEN path)
{
  GEN r = gel(path,1), s = gel(path,2);
  return mkvec2(Shift_right_cusp(r), Shift_right_cusp(s)); }
#endif

/* linked lists */
typedef struct list_t { GEN data; struct list_t *next; } list_t;
static list_t *
list_new(GEN x)
{
  list_t *L = (list_t*)stack_malloc(sizeof(list_t));
  L->data = x;
  L->next = NULL; return L;
}
static void
list_insert(list_t *L, GEN x)
{
  list_t *l = list_new(x);
  l->next = L->next;
  L->next = l;
}

/*Input: N > 1, p1N = P^1(Z/NZ)
 *Output: a connected fundamental domain for the action of \Gamma_0(N) on
 *  upper half space.  When \Gamma_0(N) is torsion free, the domain has the
 *  property that all of its vertices are cusps.  When \Gamma_0(N) has
 *  three-torsion, 2 extra triangles need to be added.
 *
 * The domain is constructed by beginning with the triangle with vertices 0,1
 * and oo.  Each adjacent triangle is successively tested to see if it contains
 * points not \Gamma_0(N) equivalent to some point in our region.  If a
 * triangle contains new points, it is added to the region.  This process is
 * continued until the region can no longer be extended (and still be a
 * fundamental domain) by added an adjacent triangle.  The list of cusps
 * between 0 and 1 are then returned
 *
 * Precisely, the function returns a list such that the elements of the list
 * with odd index are the cusps in increasing order.  The even elements of the
 * list are either an "x" or a "t".  A "t" represents that there is an element
 * of order three such that its fixed point is in the triangle directly
 * adjacent to the our region with vertices given by the cusp before and after
 * the "t".  The "x" represents that this is not the case. */
enum { type_X, type_DO /* ? */, type_T };
static GEN
form_list_of_cusps(ulong N, GEN p1N)
{
  pari_sp av = avma;
  long i, position, nbC = 2;
  GEN v, L;
  list_t *C, *c;
  /* Let t be the index of a class in PSL2(Z) / \Gamma in our fixed enumeration
   * v[t] != 0 iff it is the class of z tau^r for z a previous alpha_i
   * or beta_i.
   * For \Gamma = \Gamma_0(N), the enumeration is given by p1_index.
   * We write cl(gamma) = the class of gamma mod \Gamma */
  v = const_vecsmall(p1_size(p1N), 0);
  i = p1_index( 0, 1, p1N); v[i] = 1;
  i = p1_index( 1,-1, p1N); v[i] = 2;
  i = p1_index(-1, 0, p1N); v[i] = 3;
  /* the value is unused [debugging]: what matters is whether it is != 0 */
  position = 4;
  /* at this point, Fund = R, v contains the classes of Id, tau, tau^2 */

  C  = list_new(mkvecsmall3(0,1, type_X));
  list_insert(C, mkvecsmall3(1,1,type_DO));
  /* C is a list of triples[a,b,t], where c = a/b is a cusp, and t is the type
   * of the path between c and the PREVIOUS cusp in the list, coded as
   *   type_DO = "?", type_X = "x", type_T = "t"
   * Initially, C = [0/1,"?",1/1]; */

  /* loop through the current set of cusps C and check to see if more cusps
   * should be added */
  for (;;)
  {
    int done = 1;
    for (c = C; c; c = c->next)
    {
      GEN cusp1, cusp2, gam;
      long pos, b1, b2, b;

      if (!c->next) break;
      cusp1 = c->data; /* = a1/b1 */
      cusp2 = (c->next)->data; /* = a2/b2 */
      if (cusp2[3] != type_DO) continue;

      /* gam (oo -> 0) = (cusp2 -> cusp1), gam in PSL2(Z) */
      gam = path_to_zm(mkpath(cusp2, cusp1)); /* = [a2,a1;b2,b1] */
      /* we have normalized the cusp representation so that a1 b2 - a2 b1 = 1 */
      b1 = coeff(gam,2,1); b2 = coeff(gam,2,2);
      /* gam.1  = (a1 + a2) / (b1 + b2) */
      b = b1 + b2;
      /* Determine whether the adjacent triangle *below* (cusp1->cusp2)
       * should be added */
      pos = p1_index(b1,b2, p1N); /* did we see cl(gam) before ? */
      if (v[pos])
        cusp2[3] = type_X; /* NO */
      else
      { /* YES */
        ulong B1, B2;
        v[pos] = position;
        i = p1_index(-(b1+b2), b1, p1N); v[i] = position+1;
        i = p1_index(b2, -(b1+b2), p1N); v[i] = position+2;
        /* add cl(gam), cl(gam*TAU), cl(gam*TAU^2) to v */
        position += 3;
        /* gam tau gam^(-1) in \Gamma ? */
        B1 = smodss(b1, N);
        B2 = smodss(b2, N);
        if ((Fl_sqr(B2,N) + Fl_sqr(B1,N) + Fl_mul(B1,B2,N)) % N == 0)
          cusp2[3] = type_T;
        else
        {
          long a1 = coeff(gam, 1,1), a2 = coeff(gam, 1,2);
          long a = a1 + a2; /* gcd(a,b) = 1 */
          list_insert(c, mkvecsmall3(a,b,type_DO));
          c = c->next;
          nbC++;
          done = 0;
        }
      }
    }
    if (done) break;
  }
  L = cgetg(nbC+1, t_VEC); i = 1;
  for (c = C; c; c = c->next) gel(L,i++) = c->data;
  return gerepilecopy(av, L);
}

/* W an msN. M in PSL2(Z). Return index of M in P1^(Z/NZ) = Gamma0(N) \ PSL2(Z),
 * and M0 in Gamma_0(N) such that M = M0 * M', where M' = chosen
 * section( PSL2(Z) -> P1^(Z/NZ) ). */
static GEN
Gamma0N_decompose(GEN W, GEN M, long *index)
{
  GEN p1N = msN_get_p1N(W), W3 = gel(W,3), section = msN_get_section(W);
  GEN A;
  ulong N = p1N_get_N(p1N);
  ulong c = umodiu(gcoeff(M,2,1), N);
  ulong d = umodiu(gcoeff(M,2,2), N);
  long s, ind = p1_index(c, d, p1N); /* as an elt of P1(Z/NZ) */
  *index = W3[ind]; /* as an elt of F, E2, ... */
  M = ZM_zm_mul(M, sl2_inv(gel(section,ind)));
  /* normalize mod +/-Id */
  A = gcoeff(M,1,1);
  s = signe(A);
  if (s < 0)
    M = ZM_neg(M);
  else if (!s)
  {
    GEN C = gcoeff(M,2,1);
    if (signe(C) < 0) M = ZM_neg(M);
  }
  return M;
}
/* W an msN; as above for a path. Return [[ind], M] */
static GEN
path_Gamma0N_decompose(GEN W, GEN path)
{
  GEN p1N = msN_get_p1N(W);
  GEN p1index_to_ind = gel(W,3);
  GEN section = msN_get_section(W);
  GEN M = path_to_zm(path);
  long p1index = p1_index(cc(M), dd(M), p1N);
  long ind = p1index_to_ind[p1index];
  GEN M0 = ZM_zm_mul(mat2_to_ZM(M), sl2_inv(gel(section,p1index)));
  return mkvec2(mkvecsmall(ind), M0);
}

/*Form generators of H_1(X_0(N),{cusps},Z)
*
*Input: N = integer > 1, p1N = P^1(Z/NZ)
*Output: [cusp_list,E,F,T2,T3,E1] where
*  cusps_list = list of cusps describing fundamental domain of
*    \Gamma_0(N).
*  E = list of paths in the boundary of the fundamental domains and oriented
*    clockwise such that they do not contain a point
*    fixed by an element of order 2 and they are not an edge of a
*    triangle containing a fixed point of an element of order 3
*  F = list of paths in the interior of the domain with each
*    orientation appearing separately
* T2 = list of paths in the boundary of domain containing a point fixed
*    by an element of order 2 (oriented clockwise)
* T3 = list of paths in the boundard of domain which are the edges of
*    some triangle containing a fixed point of a matrix of order 3 (both
*    orientations appear)
* E1 = a sublist of E such that every path in E is \Gamma_0(N)-equivalent to
*    either an element of E1 or the flip (reversed orientation) of an element
*    of E1.
* (Elements of T2 are \Gamma_0(N)-equivalent to their own flip.)
*
* sec = a list from 1..#p1N of matrices describing a section of the map
*   SL_2(Z) to P^1(Z/NZ) given by [a,b;c,d]-->[c,d].
*   Given our fixed enumeration of P^1(Z/NZ), the j-th element of the list
*   represents the image of the j-th element of P^1(Z/NZ) under the section. */

/* insert path in set T */
static void
set_insert(hashtable *T, GEN path)
{ hash_insert(T, path,  (void*)(T->nb + 1)); }

static GEN
hash_to_vec(hashtable *h)
{
  GEN v = cgetg(h->nb + 1, t_VEC);
  ulong i;
  for (i = 0; i < h->len; i++)
  {
    hashentry *e = h->table[i];
    while (e)
    {
      GEN key = (GEN)e->key;
      long index = (long)e->val;
      gel(v, index) = key;
      e = e->next;
    }
  }
  return v;
}

static long
path_to_p1_index(GEN path, GEN p1N)
{
  GEN M = path_to_zm(path);
  return p1_index(cc(M), dd(M), p1N);
}

/* Pollack-Stevens sets */
typedef struct PS_sets_t {
  hashtable *F, *T2, *T31, *T32, *E1, *E2;
  GEN E2fromE1, stdE1;
} PS_sets_t;

static hashtable *
set_init(long max)
{ return hash_create(max, (ulong(*)(void*))&hash_GEN,
                          (int(*)(void*,void*))&gidentical, 1); }
/* T = E2fromE1[i] = [c, gamma] */
static ulong
E2fromE1_c(GEN T) { return itou(gel(T,1)); }
static GEN
E2fromE1_Zgamma(GEN T) { return gel(T,2); }
static GEN
E2fromE1_gamma(GEN T) { return gcoeff(gel(T,2),1,1); }

static void
insert_E(GEN path, PS_sets_t *S, GEN p1N)
{
  GEN rev = vecreverse(path);
  long std = path_to_p1_index(rev, p1N);
  GEN v = gel(S->stdE1, std);
  if (v)
  { /* [s, p1], where E1[s] is the path p1 = vecreverse(path) mod \Gamma */
    GEN gamma, p1 = gel(v,2);
    long r, s = itou(gel(v,1));

    set_insert(S->E2, path);
    r = S->E2->nb;
    if (gel(S->E2fromE1, r) != gen_0) pari_err_BUG("insert_E");

    gamma = gamma_equiv_matrix(rev, p1);
    /* reverse(E2[r]) = gamma * E1[s] */
    gel(S->E2fromE1, r) = mkvec2(utoipos(s), to_famat_shallow(gamma,gen_m1));
  }
  else
  {
    set_insert(S->E1, path);
    std = path_to_p1_index(path, p1N);
    gel(S->stdE1, std) = mkvec2(utoipos(S->E1->nb), path);
  }
}

static GEN
cusp_infinity(void) { return mkvecsmall2(1,0); }

static void
form_E_F_T(ulong N, GEN p1N, GEN *pC, PS_sets_t *S)
{
  GEN C, cusp_list = form_list_of_cusps(N, p1N);
  long nbgen = lg(cusp_list)-1, nbmanin = p1_size(p1N), r, s, i;
  hashtable *F, *T2, *T31, *T32, *E1, *E2;

  *pC = C = cgetg(nbgen+1, t_VEC);
  for (i = 1; i <= nbgen; i++)
  {
    GEN c = gel(cusp_list,i);
    gel(C,i) = mkvecsmall2(c[1], c[2]);
  }
  S->F  = F  = set_init(nbmanin);
  S->E1 = E1 = set_init(nbgen);
  S->E2 = E2 = set_init(nbgen);
  S->T2 = T2 = set_init(nbgen);
  S->T31 = T31 = set_init(nbgen);
  S->T32 = T32 = set_init(nbgen);

  /* T31 represents the three torsion paths going from left to right */
  /* T32 represents the three torsion paths going from right to left */
  for (r = 1; r < nbgen; r++)
  {
    GEN c2 = gel(cusp_list,r+1);
    if (c2[3] == type_T)
    {
      GEN c1 = gel(cusp_list,r), path = mkpath(c1,c2), path2 = vecreverse(path);
      set_insert(T31, path);
      set_insert(T32, path2);
    }
  }

  /* to record relations between E2 and E1 */
  S->E2fromE1 = zerovec(nbgen);
  S->stdE1 = const_vec(nbmanin, NULL);

  /* Assumption later: path [oo,0] is E1[1], path [1,oo] is E2[1] */
  {
    GEN oo = cusp_infinity();
    GEN p1 = mkpath(oo, mkvecsmall2(0,1)); /* [oo, 0] */
    GEN p2 = mkpath(mkvecsmall2(1,1), oo); /* [1, oo] */
    insert_E(p1, S, p1N);
    insert_E(p2, S, p1N);
  }

  for (r = 1; r < nbgen; r++)
  {
    GEN c1 = gel(cusp_list,r);
    for (s = r+1; s <= nbgen; s++)
    {
      pari_sp av = avma;
      GEN c2 = gel(cusp_list,s), path;
      GEN d = subii(mulss(c1[1],c2[2]), mulss(c1[2],c2[1]));
      avma = av;
      if (!is_pm1(d)) continue;

      path = mkpath(c1,c2);
      if (r+1 == s)
      {
        GEN w = path;
        ulong hash = T31->hash(w); /* T31, T32 use the same hash function */
        if (!hash_search2(T31, w, hash) && !hash_search2(T32, w, hash))
        {
          if (gamma_equiv(path, vecreverse(path), N))
            set_insert(T2, path);
          else
            insert_E(path, S, p1N);
        }
      } else {
        set_insert(F, mkvec2(path, mkvecsmall2(r,s)));
        set_insert(F, mkvec2(vecreverse(path), mkvecsmall2(s,r)));
      }
    }
  }
  setlg(S->E2fromE1, E2->nb+1);
}

/* v = \sum n_i g_i, g_i in Sl(2,Z), return \sum n_i g_i^(-1) */
static GEN
ZSl2_star(GEN v)
{
  long i, l;
  GEN w, G;
  if (typ(v) == t_INT) return v;
  G = gel(v,1);
  w = cgetg_copy(G, &l);
  for (i = 1; i < l; i++)
  {
    GEN g = gel(G,i);
    if (typ(g) == t_MAT) g = SL2_inv(g);
    gel(w,i) = g;
  }
  return ZG_normalize(mkmat2(w, gel(v,2)));
}

/* Input: h = set of unimodular paths, p1N = P^1(Z/NZ) = Gamma_0(N)\PSL2(Z)
 * Output: Each path is converted to a matrix and then an element of P^1(Z/NZ)
 * Append the matrix to W[12], append the index that represents
 * these elements of P^1 (the classes mod Gamma_0(N) via our fixed
 * enumeration to W[2]. */
static void
paths_decompose(GEN W, hashtable *h, int flag)
{
  GEN p1N = ms_get_p1N(W), section = ms_get_section(W);
  GEN v = hash_to_vec(h);
  long i, l = lg(v);
  for (i = 1; i < l; i++)
  {
    GEN e = gel(v,i);
    GEN M = path_to_zm(flag? gel(e,1): e);
    long index = p1_index(cc(M), dd(M), p1N);
    vecsmalltrunc_append(gel(W,2), index);
    gel(section, index) = M;
  }
}
static void
fill_W2_W12(GEN W, PS_sets_t *S)
{
  GEN p1N = msN_get_p1N(W);
  long n = p1_size(p1N);
  gel(W, 2) = vecsmalltrunc_init(n+1);
  gel(W,12) = cgetg(n+1, t_VEC);
  /* F contains [path, [index cusp1, index cusp2]]. Others contain paths only */
  paths_decompose(W, S->F, 1);
  paths_decompose(W, S->E2, 0);
  paths_decompose(W, S->T32, 0);
  paths_decompose(W, S->E1, 0);
  paths_decompose(W, S->T2, 0);
  paths_decompose(W, S->T31, 0);
}

/* x t_VECSMALL, corresponds to a map x(i) = j, where 1 <= j <= max for all i
 * Return y s.t. y[j] = i or 0 (not in image) */
static GEN
reverse_list(GEN x, long max)
{
  GEN y = const_vecsmall(max, 0);
  long r, lx = lg(x);
  for (r = 1; r < lx; r++) y[ x[r] ] = r;
  return y;
}

/* go from C[a] to C[b]; return the indices of paths
 * E.g. if a < b
 *   (C[a]->C[a+1], C[a+1]->C[a+2], ... C[b-1]->C[b])
 * (else reverse direction)
 * = b - a paths */
static GEN
F_indices(GEN W, long a, long b)
{
  GEN v = cgetg(labs(b-a) + 1, t_VEC);
  long s, k = 1;
  if (a < b) {
    GEN index_forward = gel(W,13);
    for (s = a; s < b; s++) gel(v,k++) = gel(index_forward,s);
  } else {
    GEN index_backward = gel(W,14);
    for (s = a; s > b; s--) gel(v,k++) = gel(index_backward,s);
  }
  return v;
}
/* go from C[a] to C[b] via oo; return the indices of paths
 * E.g. if a < b
 *   (C[a]->C[a-1], ... C[2]->C[1],
 *    C[1]->oo, oo-> C[end],
 *    C[end]->C[end-1], ... C[b+1]->C[b])
 *  a-1 + 2 + end-(b+1)+1 = end - b + a + 1 paths  */
static GEN
F_indices_oo(GEN W, long end, long a, long b)
{
  GEN index_oo = gel(W,15);
  GEN v = cgetg(end-labs(b-a)+1 + 1, t_VEC);
  long s, k = 1;

  if (a < b) {
    GEN index_backward = gel(W,14);
    for (s = a; s > 1; s--) gel(v,k++) = gel(index_backward,s);
    gel(v,k++) = gel(index_backward,1); /* C[1] -> oo */
    gel(v,k++) = gel(index_oo,2); /* oo -> C[end] */
    for (s = end; s > b; s--) gel(v,k++) = gel(index_backward,s);
  } else {
    GEN index_forward = gel(W,13);
    for (s = a; s < end; s++) gel(v,k++) = gel(index_forward,s);
    gel(v,k++) = gel(index_forward,end); /* C[end] -> oo */
    gel(v,k++) = gel(index_oo,1); /* oo -> C[1] */
    for (s = 1; s < b; s++) gel(v,k++) = gel(index_forward,s);
  }
  return v;
}
/* index of oo -> C[1], oo -> C[end] */
static GEN
indices_oo(GEN W, GEN C)
{
  long end = lg(C)-1;
  GEN w, v = cgetg(2+1, t_VEC), oo = cusp_infinity();
  w = mkpath(oo, gel(C,1)); /* oo -> C[1]=0 */
  gel(v,1) = path_Gamma0N_decompose(W, w);
  w = mkpath(oo, gel(C,end)); /* oo -> C[end]=1 */
  gel(v,2) = path_Gamma0N_decompose(W, w);
  return v;
}

/* index of C[1]->C[2], C[2]->C[3], ... C[end-1]->C[end], C[end]->oo
 * Recall that C[1] = 0, C[end] = 1 */
static GEN
indices_forward(GEN W, GEN C)
{
  long s, k = 1, end = lg(C)-1;
  GEN v = cgetg(end+1, t_VEC);
  for (s = 1; s <= end; s++)
  {
    GEN w = mkpath(gel(C,s), s == end? cusp_infinity(): gel(C,s+1));
    gel(v,k++) = path_Gamma0N_decompose(W, w);
  }
  return v;
}
/* index of C[1]->oo, C[2]->C[1], ... C[end]->C[end-1] */
static GEN
indices_backward(GEN W, GEN C)
{
  long s, k = 1, end = lg(C)-1;
  GEN v = cgetg(end+1, t_VEC);
  for (s = 1; s <= end; s++)
  {
    GEN w = mkpath(gel(C,s), s == 1? cusp_infinity(): gel(C,s-1));
    gel(v,k++) = path_Gamma0N_decompose(W, w);
  }
  return v;
}

/*[0,-1;1,-1]*/
static GEN
mkTAU()
{ return mkmat22(gen_0,gen_m1, gen_1,gen_m1); }
/* S */
static GEN
mkS()
{ return mkmat22(gen_0,gen_1, gen_m1,gen_0); }
/* N = integer > 1. Returns data describing Delta_0 = Z[P^1(Q)]_0 seen as
 * a Gamma_0(N) - module. */
static GEN
msinit_N(ulong N)
{
  GEN p1N, C, vecF, vecT2, vecT31, TAU, W, W2, singlerel, annT2, annT31;
  GEN F_index;
  ulong r, s, width;
  long nball, nbgen, nbp1N;
  hashtable *F, *T2, *T31, *T32, *E1, *E2;
  PS_sets_t S;

  W = zerovec(16);
  gel(W,1) = p1N = create_p1mod(N);
  gel(W,16)= inithashcusps(p1N);
  TAU = mkTAU();
  if (N == 1)
  {
    gel(W,5) = mkvecsmall(1);
    /* cheat because sets are not disjoint if N=1 */
    gel(W,11) = mkvecsmall5(0, 0, 1, 1, 2);
    gel(W,12) = mkvec(mat2(1,0,0,1));
    gel(W,8) = mkvec( mkmat22(gen_1,gen_1, mkS(),gen_1) );
    gel(W,9) = mkvec( mkmat2(mkcol3(gen_1,TAU,ZM_sqr(TAU)),
                             mkcol3(gen_1,gen_1,gen_1)) );
    return W;
  }
  nbp1N = p1_size(p1N);
  form_E_F_T(N,p1N, &C, &S);
  E1  = S.E1;
  E2  = S.E2;
  T31 = S.T31;
  T32 = S.T32;
  F   = S.F;
  T2  = S.T2;
  nbgen = lg(C)-1;

 /* Put our paths in the order: F,E2,T32,E1,T2,T31
  * W2[j] associates to the j-th element of this list its index in P1. */
  fill_W2_W12(W, &S);
  W2 = gel(W, 2);
  nball = lg(W2)-1;
  gel(W,3) = reverse_list(W2, nbp1N);
  gel(W,5) = vecslice(gel(W,2), F->nb + E2->nb + T32->nb + 1, nball);
  gel(W,4) = reverse_list(gel(W,5), nbp1N);
  gel(W,13) = indices_forward(W, C);
  gel(W,14) = indices_backward(W, C);
  gel(W,15) = indices_oo(W, C);
  gel(W,11) = mkvecsmall5(F->nb,
                          F->nb + E2->nb,
                          F->nb + E2->nb + T32->nb,
                          F->nb + E2->nb + T32->nb + E1->nb,
                          F->nb + E2->nb + T32->nb + E1->nb + T2->nb);
  /* relations between T32 and T31 [not stored!]
   * T32[i] = - T31[i] */

  /* relations of F */
  width = E1->nb + T2->nb + T31->nb;
  /* F_index[r] = [index_1, ..., index_k], where index_i is the p1_index()
   * of the elementary unimodular path between 2 consecutive cusps
   * [in E1,E2,T2,T31 or T32] */
  F_index = cgetg(F->nb+1, t_VEC);
  vecF = hash_to_vec(F);
  for (r = 1; r <= F->nb; r++)
  {
    GEN w = gel(gel(vecF,r), 2);
    long a = w[1], b = w[2], d = labs(b - a);
    /* c1 = cusp_list[a],  c2 = cusp_list[b], ci != oo */
    gel(F_index,r) = (nbgen-d >= d-1)? F_indices(W, a,b)
                                     : F_indices_oo(W, lg(C)-1,a,b);
  }

  singlerel = cgetg(width+1, t_VEC);
  /* form the single boundary relation */
  for (s = 1; s <= E2->nb; s++)
  { /* reverse(E2[s]) = gamma * E1[c] */
    GEN T = gel(S.E2fromE1,s), gamma = E2fromE1_gamma(T);
    gel(singlerel, E2fromE1_c(T)) = mkmat22(gen_1,gen_1, gamma,gen_m1);
  }
  for (r = E1->nb + 1; r <= width; r++) gel(singlerel, r) = gen_1;

  /* form the 2-torsion relations */
  annT2 = cgetg(T2->nb+1, t_VEC);
  vecT2 = hash_to_vec(T2);
  for (r = 1; r <= T2->nb; r++)
  {
    GEN w = gel(vecT2,r);
    GEN gamma = gamma_equiv_matrix(vecreverse(w), w);
    gel(annT2, r) = mkmat22(gen_1,gen_1, gamma,gen_1);
  }

  /* form the 3-torsion relations */
  annT31 = cgetg(T31->nb+1, t_VEC);
  vecT31 = hash_to_vec(T31);
  for (r = 1; r <= T31->nb; r++)
  {
    GEN M = path_to_ZM( vecreverse(gel(vecT31,r)) );
    GEN gamma = ZM_mul(ZM_mul(M, TAU), SL2_inv(M));
    gel(annT31, r) = mkmat2(mkcol3(gen_1,gamma,ZM_sqr(gamma)),
                            mkcol3(gen_1,gen_1,gen_1));
  }
  gel(W,6) = F_index;
  gel(W,7) = S.E2fromE1;
  gel(W,8) = annT2;
  gel(W,9) = annT31;
  gel(W,10)= singlerel;
  return W;
}
static GEN
cusp_to_P1Q(GEN c) { return c[2]? gdivgs(stoi(c[1]), c[2]): mkoo(); }
static GEN
mspathgens_i(GEN W)
{
  GEN R, r, g, section, gen, annT2, annT31;
  long i, l;
  checkms(W); W = get_msN(W);
  section = msN_get_section(W);
  gen = ms_get_genindex(W);
  l = lg(gen);
  g = cgetg(l,t_VEC);
  for (i = 1; i < l; i++)
  {
    GEN p = gel(section,gen[i]);
    gel(g,i) = mkvec2(cusp_to_P1Q(gel(p,1)), cusp_to_P1Q(gel(p,2)));
  }
  annT2 = msN_get_annT2(W);
  annT31= msN_get_annT31(W);
  if (ms_get_N(W) == 1)
  {
    R = cgetg(3, t_VEC);
    gel(R,1) = mkvec( mkvec2(gel(annT2,1), gen_1) );
    gel(R,2) = mkvec( mkvec2(gel(annT31,1), gen_1) );
  }
  else
  {
    GEN singlerel = msN_get_singlerel(W);
    long j, nbT2 = lg(annT2)-1, nbT31 = lg(annT31)-1, nbE1 = ms_get_nbE1(W);
    R = cgetg(nbT2+nbT31+2, t_VEC);
    l = lg(singlerel);
    r = cgetg(l, t_VEC);
    for (i = 1; i <= nbE1; i++)
      gel(r,i) = mkvec2(gel(singlerel, i), utoi(i));
    for (; i < l; i++)
      gel(r,i) = mkvec2(gen_1, utoi(i));
    gel(R,1) = r; j = 2;
    for (i = 1; i <= nbT2; i++,j++)
      gel(R,j) = mkvec( mkvec2(gel(annT2,i), utoi(i + nbE1)) );
    for (i = 1; i <= nbT31; i++,j++)
      gel(R,j) = mkvec( mkvec2(gel(annT31,i), utoi(i + nbE1 + nbT2)) );
  }
  return mkvec2(g,R);
}
GEN
mspathgens(GEN W)
{
  pari_sp av = avma;
  return gerepilecopy(av, mspathgens_i(W));
}
/* Modular symbols in weight k: Hom_Gamma(Delta, Q[x,y]_{k-2}) */
/* A symbol phi is represented by the {phi(g_i)}, {phi(g'_i)}, {phi(g''_i)}
 * where the {g_i, g'_i, g''_i} are the Z[\Gamma]-generators of Delta,
 * g_i corresponds to E1, g'_i to T2, g''_i to T31.
 */

/* FIXME: export. T^1, ..., T^n */
static GEN
RgX_powers(GEN T, long n)
{
  GEN v = cgetg(n+1, t_VEC);
  long i;
  gel(v, 1) = T;
  for (i = 1; i < n; i++) gel(v,i+1) = RgX_mul(gel(v,i), T);
  return v;
}

/* g = [a,b;c,d] a mat2. Return (X^{k-2} | g)(X,Y)[X = 1]. */
static GEN
voo_act_Gl2Q(GEN g, long k)
{
  GEN mc = stoi(-coeff(g,2,1)), d = stoi(coeff(g,2,2));
  return RgX_to_RgC(gpowgs(deg1pol_shallow(mc, d, 0), k-2), k-1);
}

struct m_act {
  long dim, k, p;
  GEN q;
  GEN(*act)(struct m_act *,GEN);
};

/* g = [a,b;c,d]. Return (P | g)(X,Y)[X = 1] = P(dX - cY, -b X + aY)[X = 1],
 * for P = X^{k-2}, X^{k-3}Y, ..., Y^{k-2} */
GEN
RgX_act_Gl2Q(GEN g, long k)
{
  GEN a,b,c,d, V1,V2,V;
  long i;
  if (k == 2) return matid(1);
  a = gcoeff(g,1,1); b = gcoeff(g,1,2);
  c = gcoeff(g,2,1); d = gcoeff(g,2,2);
  V1 = RgX_powers(deg1pol_shallow(gneg(c), d, 0), k-2); /* d - c Y */
  V2 = RgX_powers(deg1pol_shallow(a, gneg(b), 0), k-2); /*-b + a Y */
  V = cgetg(k, t_MAT);
  gel(V,1)   = RgX_to_RgC(gel(V1, k-2), k-1);
  for (i = 1; i < k-2; i++)
  {
    GEN v1 = gel(V1, k-2-i); /* (d-cY)^(k-2-i) */
    GEN v2 = gel(V2, i); /* (-b+aY)^i */
    gel(V,i+1) = RgX_to_RgC(RgX_mul(v1,v2), k-1);
  }
  gel(V,k-1) = RgX_to_RgC(gel(V2, k-2), k-1);
  return V; /* V[i+1] = X^i | g */
}
/* z in Z[Gl2(Q)], return the matrix of z acting on V */
static GEN
act_ZGl2Q(GEN z, struct m_act *T, hashtable *H)
{
  GEN S = NULL, G, E;
  pari_sp av;
  long l, j;
  /* paranoia: should not occur */
  if (typ(z) == t_INT) return scalarmat_shallow(z, T->dim);
  G = gel(z,1); l = lg(G);
  E = gel(z,2); av = avma;
  for (j = 1; j < l; j++)
  {
    GEN M, g = gel(G,j), n = gel(E,j);
    if (typ(g) == t_INT) /* = 1 */
      M = n; /* n*Id_dim */
    else
    { /*search in H succeeds because of preload*/
      M = H? (GEN)hash_search(H,g)->val: T->act(T,g);
      if (is_pm1(n))
      { if (signe(n) < 0) M = RgM_neg(M); }
      else
        M = RgM_Rg_mul(M, n);
    }
    if (!S) { S = M; continue; }
    S = gadd(S, M);
    if (gc_needed(av,1))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"act_ZGl2Q, j = %ld",j);
      S = gerepileupto(av, S);
    }
  }
  return gerepilecopy(av, S);
}
static GEN
_RgX_act_Gl2Q(struct m_act *S, GEN z) { return RgX_act_Gl2Q(z, S->k); }
/* acting on (X^{k-2},...,Y^{k-2}) */
GEN
RgX_act_ZGl2Q(GEN z, long k)
{
  struct m_act T;
  T.k = k;
  T.dim = k-1;
  T.act=&_RgX_act_Gl2Q;
  return act_ZGl2Q(z, &T, NULL);
}

/* First pass, identify matrices in Sl_2 to convert to operators;
 * insert operators in hashtable. This allows GC in act_ZGl2Q */
static void
hash_preload(GEN M, struct m_act *S, hashtable *H)
{
  if (typ(M) != t_INT)
  {
    ulong h = H->hash(M);
    hashentry *e = hash_search2(H, M, h);
    if (!e) hash_insert2(H, M, S->act(S,M), h);
  }
}
/* z a sparse operator */
static void
hash_vecpreload(GEN z, struct m_act *S, hashtable *H)
{
  GEN G = gel(z,1);
  long i, l = lg(G);
  for (i = 1; i < l; i++) hash_preload(gel(G,i), S, H);
}
static void
ZGl2QC_preload(struct m_act *S, GEN v, hashtable *H)
{
  GEN val = gel(v,2);
  long i, l = lg(val);
  for (i = 1; i < l; i++) hash_vecpreload(gel(val,i), S, H);
}
/* Given a sparse vector of elements in Z[G], convert it to a (sparse) vector
 * of operators on V (given by t_MAT) */
static void
ZGl2QC_to_act(struct m_act *S, GEN v, hashtable *H)
{
  GEN val = gel(v,2);
  long i, l = lg(val);
  for (i = 1; i < l; i++) gel(val,i) = act_ZGl2Q(gel(val,i), S, H);
}

/* For all V[i] in Z[\Gamma], find the P such that  P . V[i]^* = 0;
 * write P in basis X^{k-2}, ..., Y^{k-2} */
static GEN
ZGV_tors(GEN V, long k)
{
  long i, l = lg(V);
  GEN v = cgetg(l, t_VEC);
  for (i = 1; i < l; i++)
  {
    GEN a = ZSl2_star(gel(V,i));
    gel(v,i) = ZM_ker(RgX_act_ZGl2Q(a,k));
  }
  return v;
}

static long
set_from_index(GEN W11, long i)
{
  if (i <= W11[1]) return 1;
  if (i <= W11[2]) return 2;
  if (i <= W11[3]) return 3;
  if (i <= W11[4]) return 4;
  if (i <= W11[5]) return 5;
  return 6;
}

/* det M = 1 */
static void
treat_index(GEN W, GEN M, long index, GEN v)
{
  GEN W11 = gel(W,11);
  long shift = W11[3]; /* #F + #E2 + T32 */
  switch(set_from_index(W11, index))
  {
    case 1: /*F*/
    {
      GEN F_index = gel(W,6), ind = gel(F_index, index);
      long j, l = lg(ind);
      for (j = 1; j < l; j++)
      {
        GEN IND = gel(ind,j), M0 = gel(IND,2);
        long index = mael(IND,1,1);
        treat_index(W, ZM_mul(M,M0), index, v);
      }
      break;
    }

    case 2: /*E2, E2[r] + gamma * E1[s] = 0 */
    {
      long r = index - W11[1];
      GEN z = gel(msN_get_E2fromE1(W), r);

      index = E2fromE1_c(z);
      M = G_ZG_mul(M, E2fromE1_Zgamma(z)); /* M * (-gamma) */
      gel(v, index) = ZG_add(gel(v, index), M);
      break;
    }

    case 3: /*T32, T32[i] = -T31[i] */
    {
      long T3shift = W11[5] - W11[2]; /* #T32 + #E1 + #T2 */
      index += T3shift;
      index -= shift;
      gel(v, index) = ZG_add(gel(v, index), to_famat_shallow(M,gen_m1));
      break;
    }
    default: /*E1,T2,T31*/
      index -= shift;
      gel(v, index) = ZG_add(gel(v, index), to_famat_shallow(M,gen_1));
      break;
  }
}
static void
treat_index_trivial(GEN v, GEN W, long index)
{
  GEN W11 = gel(W,11);
  long shift = W11[3]; /* #F + #E2 + T32 */
  switch(set_from_index(W11, index))
  {
    case 1: /*F*/
    {
      GEN F_index = gel(W,6), ind = gel(F_index, index);
      long j, l = lg(ind);
      for (j = 1; j < l; j++)
      {
        GEN IND = gel(ind,j);
        treat_index_trivial(v, W, mael(IND,1,1));
      }
      break;
    }

    case 2: /*E2, E2[r] + gamma * E1[s] = 0 */
    {
      long r = index - W11[1];
      long s = E2fromE1_c(gel(msN_get_E2fromE1(W), r));
      v[s]--;
      break;
    }

    case 3: case 5: case 6: /*T32,T2,T31*/
      break;

    case 4: /*E1*/
      v[index-shift]++;
      break;
  }
}

static GEN
M2_log(GEN W, GEN M)
{
  GEN a = gcoeff(M,1,1), b = gcoeff(M,1,2);
  GEN c = gcoeff(M,2,1), d = gcoeff(M,2,2);
  GEN  u, v, D, V;
  long index, s;

  W = get_msN(W);
  V = zerovec(ms_get_nbgen(W));

  D = subii(mulii(a,d), mulii(b,c));
  s = signe(D);
  if (!s) return V;
  if (is_pm1(D))
  { /* shortcut, no need to apply Manin's trick */
    if (s < 0) { b = negi(b); d = negi(d); }
    M = Gamma0N_decompose(W, mkmat22(a,b, c,d), &index);
    treat_index(W, M, index, V);
  }
  else
  {
    GEN U, B, P, Q, PQ, C1,C2;
    long i, l;
    (void)bezout(a,c,&u,&v);
    B = addii(mulii(b,u), mulii(d,v));
    /* [u,v;-c,a] [a,b; c,d] = [1,B; 0,D], i.e. M = U [1,B;0,D] */
    U = mkmat22(a,negi(v), c,u);

    /* {1/0 -> B/D} as \sum g_i, g_i unimodular paths */
    PQ = ZV_allpnqn( gboundcf(gdiv(B,D), 0) );
    P = gel(PQ,1); l = lg(P);
    Q = gel(PQ,2);
    C1 = gel(U,1);
    for (i = 1; i < l; i++, C1 = C2)
    {
      GEN M;
      C2 = ZM_ZC_mul(U, mkcol2(gel(P,i), gel(Q,i)));
      if (!odd(i)) C1 = ZC_neg(C1);
      M = Gamma0N_decompose(W, mkmat2(C1,C2), &index);
      treat_index(W, M, index, V);
    }
  }
  return V;
}

/* express +oo->q=a/b in terms of the Z[G]-generators, trivial action */
static void
Q_log_trivial(GEN v, GEN W, GEN q)
{
  GEN Q, W3 = gel(W,3), p1N = msN_get_p1N(W);
  ulong c,d, N = p1N_get_N(p1N);
  long i, lx;

  Q = Q_log_init(N, q);
  lx = lg(Q);
  c = 0;
  for (i = 1; i < lx; i++, c = d)
  {
    long index;
    d = Q[i];
    if (c && !odd(i)) c = N - c;
    index = W3[ p1_index(c,d,p1N) ];
    treat_index_trivial(v, W, index);
  }
}
static void
M2_log_trivial(GEN V, GEN W, GEN M)
{
  GEN p1N = gel(W,1), W3 = gel(W,3);
  ulong N = p1N_get_N(p1N);
  GEN a = gcoeff(M,1,1), b = gcoeff(M,1,2);
  GEN c = gcoeff(M,2,1), d = gcoeff(M,2,2);
  GEN  u, v, D;
  long index, s;

  D = subii(mulii(a,d), mulii(b,c));
  s = signe(D);
  if (!s) return;
  if (is_pm1(D))
  { /* shortcut, not need to apply Manin's trick */
    if (s < 0) d = negi(d);
    index = W3[ p1_index(umodiu(c,N),umodiu(d,N),p1N) ];
    treat_index_trivial(V, W, index);
  }
  else
  {
    GEN U, B, P, Q, PQ;
    long i, l;
    if (!signe(c)) { Q_log_trivial(V,W,gdiv(b,d)); return; }
    (void)bezout(a,c,&u,&v);
    B = addii(mulii(b,u), mulii(d,v));
    /* [u,v;-c,a] [a,b; c,d] = [1,B; 0,D], i.e. M = U [1,B;0,D] */
    U = mkvec2(c, u);

    /* {1/0 -> B/D} as \sum g_i, g_i unimodular paths */
    PQ = ZV_allpnqn( gboundcf(gdiv(B,D), 0) );
    P = gel(PQ,1); l = lg(P);
    Q = gel(PQ,2);
    for (i = 1; i < l; i++, c = d)
    {
      d = addii(mulii(gel(U,1),gel(P,i)), mulii(gel(U,2),gel(Q,i)));
      if (!odd(i)) c = negi(c);
      index = W3[ p1_index(umodiu(c,N),umodiu(d,N),p1N) ];
      treat_index_trivial(V, W, index);
    }
  }
}

static GEN
cusp_to_ZC(GEN c)
{
  switch(typ(c))
  {
    case t_INFINITY:
      return mkcol2(gen_1,gen_0);
    case t_INT:
      return mkcol2(c,gen_1);
    case t_FRAC:
      return mkcol2(gel(c,1),gel(c,2));
    case t_VECSMALL:
      return mkcol2(stoi(c[1]), stoi(c[2]));
    default:
      pari_err_TYPE("mspathlog",c);
      return NULL;
  }
}
static GEN
path2_to_M2(GEN p)
{ return mkmat2(cusp_to_ZC(gel(p,1)), cusp_to_ZC(gel(p,2))); }
static GEN
path_to_M2(GEN p)
{
  if (lg(p) != 3) pari_err_TYPE("mspathlog",p);
  switch(typ(p))
  {
    case t_MAT:
      RgM_check_ZM(p,"mspathlog");
      break;
    case t_VEC:
      p = path2_to_M2(p);
      break;
    default: pari_err_TYPE("mspathlog",p);
  }
  return p;
}
/* Expresses path p as \sum x_i g_i, where the g_i are our distinguished
 * generators and x_i \in Z[\Gamma]. Returns [x_1,...,x_n] */
GEN
mspathlog(GEN W, GEN p)
{
  pari_sp av = avma;
  checkms(W);
  return gerepilecopy(av, M2_log(W, path_to_M2(p)));
}

/** HECKE OPERATORS **/
/* [a,b;c,d] * cusp */
static GEN
cusp_mul(long a, long b, long c, long d, GEN cusp)
{
  long x = cusp[1], y = cusp[2];
  long A = a*x+b*y, B = c*x+d*y, u = cgcd(A,B);
  if (u != 1) { A /= u; B /= u; }
  return mkcol2s(A, B);
}
/* f in Gl2(Q), act on path (zm), return path_to_M2(f.path) */
static GEN
Gl2Q_act_path(GEN f, GEN path)
{
  long a = coeff(f,1,1), b = coeff(f,1,2);
  long c = coeff(f,2,1), d = coeff(f,2,2);
  GEN c1 = cusp_mul(a,b,c,d, gel(path,1));
  GEN c2 = cusp_mul(a,b,c,d, gel(path,2));
  return mkmat2(c1,c2);
}

static GEN
init_act_trivial(GEN W) { return const_vecsmall(ms_get_nbE1(W), 0); }
static GEN
mspathlog_trivial(GEN W, GEN p)
{
  GEN v;
  W = get_msN(W);
  v = init_act_trivial(W);
  M2_log_trivial(v, W, path_to_M2(p));
  return v;
}

/* map from W1=Hom(Delta_0(N1),Q) -> W2=Hom(Delta_0(N2),Q), weight 2,
 * trivial action. v a Gl2_Q or a t_VEC of Gl2_Q (\sum v[i] in Z[Gl2(Q)]).
 * Return the matrix attached to the action of v. */
static GEN
getMorphism_trivial(GEN WW1, GEN WW2, GEN v)
{
  GEN T, section, gen, W1 = get_msN(WW1), W2 = get_msN(WW2);
  long j, lv, d2;
  if (ms_get_N(W1) == 1) return cgetg(1,t_MAT);
  if (ms_get_N(W2) == 1) return zeromat(0, ms_get_nbE1(W1));
  section = msN_get_section(W2);
  gen = msN_get_genindex(W2);
  d2 = ms_get_nbE1(W2);
  T = cgetg(d2+1, t_MAT);
  lv = lg(v);
  for (j = 1; j <= d2; j++)
  {
    GEN w = gel(section, gen[j]);
    GEN t = init_act_trivial(W1);
    pari_sp av = avma;
    long l;
    for (l = 1; l < lv; l++) M2_log_trivial(t, W1, Gl2Q_act_path(gel(v,l), w));
    gel(T,j) = t; avma = av;
  }
  return shallowtrans(zm_to_ZM(T));
}

static GEN
RgV_sparse(GEN v, GEN *pind)
{
  long i, l, k;
  GEN w = cgetg_copy(v,&l), ind = cgetg(l, t_VECSMALL);
  for (i = k = 1; i < l; i++)
  {
    GEN c = gel(v,i);
    if (typ(c) == t_INT) continue;
    gel(w,k) = c; ind[k] = i; k++;
  }
  setlg(w,k); setlg(ind,k);
  *pind = ind; return w;
}

static int
mat2_isidentity(GEN M)
{
  GEN A = gel(M,1), B = gel(M,2);
  return A[1] == 1 && A[2] == 0 && B[1] == 0 && B[2] == 1;
}
/* path a mat22/mat22s, return log(f.path)^* . f in sparse form */
static GEN
M2_logf(GEN Wp, GEN path, GEN f)
{
  pari_sp av = avma;
  GEN ind, L;
  long i, l;
  if (f)
    path = Gl2Q_act_path(f, path);
  else if (typ(gel(path,1)) == t_VECSMALL)
    path = path2_to_M2(path);
  L = M2_log(Wp, path);
  L = RgV_sparse(L,&ind); l = lg(L);
  for (i = 1; i < l; i++) gel(L,i) = ZSl2_star(gel(L,i));
  if (f) ZGC_G_mul_inplace(L, mat2_to_ZM(f));
  return gerepilecopy(av, mkvec2(ind,L));
}

static hashtable *
Gl2act_cache(long dim) { return set_init(dim*10); }

/* f zm/ZM in Gl_2(Q), acts from the left on Delta, which is generated by
 * (g_i) as Z[Gamma1]-module, and by (G_i) as Z[Gamma2]-module.
 * We have f.G_j = \sum_i \lambda_{i,j} g_i,   \lambda_{i,j} in Z[Gamma1]
 * For phi in Hom_Gamma1(D,V), g in D, phi | f is in Hom_Gamma2(D,V) and
 *  (phi | f)(G_j) = phi(f.G_j) | f
 *                 = phi( \sum_i \lambda_{i,j} g_i ) | f
 *                 = \sum_i phi(g_i) | (\lambda_{i,j}^* f)
 *                 = \sum_i phi(g_i) | \mu_{i,j}(f)
 * More generally
 *  (\sum_k (phi |v_k))(G_j) = \sum_i phi(g_i) | \Mu_{i,j}
 * with \Mu_{i,j} = \sum_k \mu{i,j}(v_k)
 * Return the \Mu_{i,j} matrix as vector of sparse columns of operators on V */
static GEN
init_dual_act(GEN v, GEN W1, GEN W2, struct m_act *S)
{
  GEN section = ms_get_section(W2), gen = ms_get_genindex(W2);
  /* HACK: the actions we consider in dimension 1 are trivial and in
   * characteristic != 2, 3 => torsion generators are 0
   * [satisfy e.g. (1+gamma).g = 0 => \phi(g) | 1+gamma  = 0 => \phi(g) = 0 */
  long j, lv = lg(v), dim = S->dim == 1? ms_get_nbE1(W2): lg(gen)-1;
  GEN T = cgetg(dim+1, t_VEC);
  hashtable *H = Gl2act_cache(dim);
  for (j = 1; j <= dim; j++)
  {
    pari_sp av = avma;
    GEN w = gel(section, gen[j]); /* path_to_zm( E1/T2/T3 element ) */
    GEN t = NULL;
    long k;
    for (k = 1; k < lv; k++)
    {
      GEN tk, f = gel(v,k);
      if (typ(gel(f,1)) != t_VECSMALL) f = ZM_to_zm(f);
      if (mat2_isidentity(f)) f = NULL;
      tk = M2_logf(W1, w, f); /* mu_{.,j}(v[k]) as sparse vector */
      t = t? ZGCs_add(t, tk): tk;
    }
    gel(T,j) = gerepilecopy(av, t);
  }
  for (j = 1; j <= dim; j++)
  {
    ZGl2QC_preload(S, gel(T,j), H);
    ZGl2QC_to_act(S, gel(T,j), H);
  }
  return T;
}

/* modular symbol given by phi[j] = \phi(G_j)
 * \sum L[i]*phi[i], L a sparse column of operators */
static GEN
dense_act_col(GEN col, GEN phi)
{
  GEN s = NULL, colind = gel(col,1), colval = gel(col,2);
  long i, l = lg(colind), lphi = lg(phi);
  for (i = 1; i < l; i++)
  {
    long a = colind[i];
    GEN t;
    if (a >= lphi) break; /* happens if k=2: torsion generator t omitted */
    t = gel(phi, a); /* phi(G_a) */
    t = RgM_RgC_mul(gel(colval,i), t);
    s = s? RgC_add(s, t): t;
  }
  return s;
}
/* modular symbol given by \phi( G[ind[j]] ) = val[j]
 * \sum L[i]*phi[i], L a sparse column of operators */
static GEN
sparse_act_col(GEN col, GEN phi)
{
  GEN s = NULL, colind = gel(col,1), colval = gel(col,2);
  GEN ind = gel(phi,2), val = gel(phi,3);
  long a, l = lg(ind);
  if (lg(gel(phi,1)) == 1) return RgM_RgC_mul(gel(colval,1), gel(val,1));
  for (a = 1; a < l; a++)
  {
    GEN t = gel(val, a); /* phi(G_i) */
    long i = zv_search(colind, ind[a]);
    if (!i) continue;
    t = RgM_RgC_mul(gel(colval,i), t);
    s = s? RgC_add(s, t): t;
  }
  return s;
}
static int
phi_sparse(GEN phi) { return typ(gel(phi,1)) == t_VECSMALL; }
/* phi in Hom_Gamma1(Delta, V), return the matrix whose colums are the
 *   \sum_i phi(g_i) | \mu_{i,j} = (phi|f)(G_j),
 * see init_dual_act. */
static GEN
dual_act(long dimV, GEN act, GEN phi)
{
  long l = lg(act), j;
  GEN v = cgetg(l, t_MAT);
  GEN (*ACT)(GEN,GEN) = phi_sparse(phi)? sparse_act_col: dense_act_col;
  for (j = 1; j < l; j++)
  {
    pari_sp av = avma;
    GEN s = ACT(gel(act,j), phi);
    gel(v,j) = s? gerepileupto(av,s): zerocol(dimV);
  }
  return v;
}

/* in level N > 1 */
static void
msk_get_st(GEN W, long *s, long *t)
{ GEN st = gmael(W,3,3); *s = st[1]; *t = st[2]; }
static GEN
msk_get_link(GEN W) { return gmael(W,3,4); }
static GEN
msk_get_inv(GEN W) { return gmael(W,3,5); }
/* \phi in Hom(Delta, V), \phi(G_k) = phi[k]. Write \phi as
 *   \sum_{i,j} mu_{i,j} phi_{i,j}, mu_{i,j} in Q */
static GEN
getMorphism_basis(GEN W, GEN phi)
{
  GEN R, Q, Ls, T0, T1, Ts, link, basis, inv = msk_get_inv(W);
  long i, j, r, s, t, dim, lvecT;

  if (ms_get_N(W) == 1) return ZC_apply_dinv(inv, gel(phi,1));
  lvecT = lg(phi);
  basis = msk_get_basis(W);
  dim = lg(basis)-1;
  R = zerocol(dim);
  msk_get_st(W, &s, &t);
  link = msk_get_link(W);
  for (r = 2; r < lvecT; r++)
  {
    GEN Tr, L;
    if (r == s) continue;
    Tr = gel(phi,r); /* Phi(G_r), r != 1,s */
    L = gel(link, r);
    Q = ZC_apply_dinv(gel(inv,r), Tr);
    /* write Phi(G_r) as sum_{a,b} mu_{a,b} Phi_{a,b}(G_r) */
    for (j = 1; j < lg(L); j++) gel(R, L[j]) = gel(Q,j);
  }
  Ls = gel(link, s);
  T1 = gel(phi,1); /* Phi(G_1) */
  gel(R, Ls[t]) = gel(T1, 1);

  T0 = NULL;
  for (i = 2; i < lg(link); i++)
  {
    GEN L;
    if (i == s) continue;
    L = gel(link,i);
    for (j =1 ; j < lg(L); j++)
    {
      long n = L[j]; /* phi_{i,j} = basis[n] */
      GEN mu_ij = gel(R, n);
      GEN phi_ij = gel(basis, n), pols = gel(phi_ij,3);
      GEN z = RgC_Rg_mul(gel(pols, 3), mu_ij);
      T0 = T0? RgC_add(T0, z): z; /* += mu_{i,j} Phi_{i,j} (G_s) */
    }
  }
  Ts = gel(phi,s); /* Phi(G_s) */
  if (T0) Ts = RgC_sub(Ts, T0);
  /* solve \sum_{j!=t} mu_{s,j} Phi_{s,j}(G_s) = Ts */
  Q = ZC_apply_dinv(gel(inv,s), Ts);
  for (j = 1; j < t; j++) gel(R, Ls[j]) = gel(Q,j);
  /* avoid mu_{s,t} */
  for (j = t; j < lg(Q); j++) gel(R, Ls[j+1]) = gel(Q,j);
  return R;
}

/* a = s(g_i) for some modular symbol s; b in Z[G]
 * return s(b.g_i) = b^* . s(g_i) */
static GEN
ZGl2Q_act_s(GEN b, GEN a, long k)
{
  if (typ(b) == t_INT)
  {
    if (!signe(b)) return gen_0;
    switch(typ(a))
    {
      case t_POL:
        a = RgX_to_RgC(a, k-1); /*fall through*/
      case t_COL:
        a = RgC_Rg_mul(a,b);
        break;
      default: a = scalarcol_shallow(b,k-1);
    }
  }
  else
  {
    b = RgX_act_ZGl2Q(ZSl2_star(b), k);
    switch(typ(a))
    {
      case t_POL:
        a = RgX_to_RgC(a, k-1); /*fall through*/
      case t_COL:
        a = RgM_RgC_mul(b,a);
        break;
      default: a = RgC_Rg_mul(gel(b,1),a);
    }
  }
  return a;
}

static int
checksymbol(GEN W, GEN s)
{
  GEN t, annT2, annT31, singlerel;
  long i, k, l, nbE1, nbT2, nbT31;
  k = msk_get_weight(W);
  W = get_msN(W);
  nbE1 = ms_get_nbE1(W);
  singlerel = gel(W,10);
  l = lg(singlerel);
  if (k == 2)
  {
    for (i = nbE1+1; i < l; i++)
      if (!gequal0(gel(s,i))) return 0;
    return 1;
  }
  annT2 = msN_get_annT2(W); nbT2 = lg(annT2)-1;
  annT31 = msN_get_annT31(W);nbT31 = lg(annT31)-1;
  t = NULL;
  for (i = 1; i < l; i++)
  {
    GEN a = gel(s,i);
    a = ZGl2Q_act_s(gel(singlerel,i), a, k);
    t = t? gadd(t, a): a;
  }
  if (!gequal0(t)) return 0;
  for (i = 1; i <= nbT2; i++)
  {
    GEN a = gel(s,i + nbE1);
    a = ZGl2Q_act_s(gel(annT2,i), a, k);
    if (!gequal0(a)) return 0;
  }
  for (i = 1; i <= nbT31; i++)
  {
    GEN a = gel(s,i + nbE1 + nbT2);
    a = ZGl2Q_act_s(gel(annT31,i), a, k);
    if (!gequal0(a)) return 0;
  }
  return 1;
}
GEN
msissymbol(GEN W, GEN s)
{
  long k, nbgen;
  checkms(W);
  k = msk_get_weight(W);
  nbgen = ms_get_nbgen(W);
  switch(typ(s))
  {
    case t_VEC: /* values s(g_i) */
      if (lg(s)-1 != nbgen) return gen_0;
      break;
    case t_COL:
      if (msk_get_sign(W))
      {
        GEN star = gel(msk_get_starproj(W), 1);
        if (lg(star) == lg(s)) return gen_1;
      }
      if (k == 2) /* on the dual basis of (g_i) */
      {
        if (lg(s)-1 != nbgen) return gen_0;
      }
      else
      {
        GEN basis = msk_get_basis(W);
        return (lg(s) == lg(basis))? gen_1: gen_0;
      }
      break;
    case t_MAT:
    {
      long i, l = lg(s);
      GEN v = cgetg(l, t_VEC);
      for (i = 1; i < l; i++) gel(v,i) = msissymbol(W,gel(s,i))? gen_1: gen_0;
      return v;
    }
    default: return gen_0;
  }
  return checksymbol(W,s)? gen_1: gen_0;
}

/* map op: W1 = Hom(Delta_0(N1),V) -> W2 = Hom(Delta_0(N2),V), given by
 * \sum v[i], v[i] in Gl2(Q) */
static GEN
getMorphism(GEN W1, GEN W2, GEN v)
{
  struct m_act S;
  GEN B1, M, act;
  long a, l, k = msk_get_weight(W1);
  if (k == 2) return getMorphism_trivial(W1,W2,v);
  S.k = k;
  S.dim = k-1;
  S.act = &_RgX_act_Gl2Q;
  act = init_dual_act(v,W1,W2,&S);
  B1 = msk_get_basis(W1);
  l = lg(B1); M = cgetg(l, t_MAT);
  for (a = 1; a < l; a++)
  {
    pari_sp av = avma;
    GEN phi = dual_act(S.dim, act, gel(B1,a));
    GEN D = getMorphism_basis(W2, phi);
    gel(M,a) = gerepilecopy(av, D);
  }
  return M;
}
static GEN
msendo(GEN W, GEN v) { return getMorphism(W, W, v); }

static GEN
endo_project(GEN W, GEN e, GEN H)
{
  if (msk_get_sign(W)) e = Qevproj_apply(e, msk_get_starproj(W));
  if (H) e = Qevproj_apply(e, Qevproj_init0(H));
  return e;
}
static GEN
mshecke_i(GEN W, ulong p)
{
  GEN v = ms_get_N(W) % p? Tp_matrices(p): Up_matrices(p);
  return msendo(W,v);
}
GEN
mshecke(GEN W, long p, GEN H)
{
  pari_sp av = avma;
  GEN T;
  checkms(W);
  if (p <= 1) pari_err_PRIME("mshecke",stoi(p));
  T = mshecke_i(W,p);
  T = endo_project(W,T,H);
  return gerepilecopy(av, T);
}

static GEN
msatkinlehner_i(GEN W, long Q)
{
  long N = ms_get_N(W);
  GEN v;
  if (Q == 1) return matid(msk_get_dim(W));
  if (Q == N) return msendo(W, mkvec(mat2(0,1,-N,0)));
  if (N % Q) pari_err_DOMAIN("msatkinlehner","N % Q","!=",gen_0,stoi(Q));
  v = WQ_matrix(N, Q);
  if (!v) pari_err_DOMAIN("msatkinlehner","gcd(Q,N/Q)","!=",gen_1,stoi(Q));
  return msendo(W,mkvec(v));
}
GEN
msatkinlehner(GEN W, long Q, GEN H)
{
  pari_sp av = avma;
  GEN w;
  long k;
  checkms(W);
  k = msk_get_weight(W);
  if (Q <= 0) pari_err_DOMAIN("msatkinlehner","Q","<=",gen_0,stoi(Q));
  w = msatkinlehner_i(W,Q);
  w = endo_project(W,w,H);
  if (k > 2 && Q != 1) w = RgM_Rg_div(w, powuu(Q,(k-2)>>1));
  return gerepilecopy(av, w);
}

static GEN
msstar_i(GEN W) { return msendo(W, mkvec(mat2(-1,0,0,1))); }
GEN
msstar(GEN W, GEN H)
{
  pari_sp av = avma;
  GEN s;
  checkms(W);
  s = msstar_i(W);
  s = endo_project(W,s,H);
  return gerepilecopy(av, s);
}

#if 0
/* is \Gamma_0(N) cusp1 = \Gamma_0(N) cusp2 ? */
static int
iscuspeq(ulong N, GEN cusp1, GEN cusp2)
{
  long p1, q1, p2, q2, s1, s2, d;
  p1 = cusp1[1]; p2 = cusp2[1];
  q1 = cusp1[2]; q2 = cusp2[2];
  d = Fl_mul(smodss(q1,N),smodss(q2,N), N);
  d = ugcd(d, N);

  s1 = q1 > 2? Fl_inv(smodss(p1,q1), q1): 1;
  s2 = q2 > 2? Fl_inv(smodss(p2,q2), q2): 1;
  return Fl_mul(s1,q2,d) == Fl_mul(s2,q1,d);
}
#endif

/* return E_c(r) */
static GEN
get_Ec_r(GEN c, long k)
{
  long p = c[1], q = c[2], u, v;
  GEN gr;
  (void)cbezout(p, q, &u, &v);
  gr = mat2(p, -v, q, u); /* g . (1:0) = (p:q) */
  return voo_act_Gl2Q(sl2_inv(gr), k);
}
/* N > 1; returns the modular symbol attached to the cusp c := p/q via the rule
 * E_c(path from a to b in Delta_0) := E_c(b) - E_c(a), where
 * E_c(r) := 0 if r != c mod Gamma
 *           v_oo | gamma_r^(-1)
 * where v_oo is stable by T = [1,1;0,1] (i.e x^(k-2)) and
 * gamma_r . (1:0) = r, for some gamma_r in SL_2(Z) * */
static GEN
msfromcusp_trivial(GEN W, GEN c)
{
  GEN section = ms_get_section(W), gen = ms_get_genindex(W);
  GEN S = ms_get_hashcusps(W);
  long j, ic = cusp_index(c, S), l = ms_get_nbE1(W)+1;
  GEN phi = cgetg(l, t_COL);
  for (j = 1; j < l; j++)
  {
    GEN vj, g = gel(section, gen[j]); /* path_to_zm(generator) */
    GEN c1 = gel(g,1), c2 = gel(g,2);
    long i1 = cusp_index(c1, S);
    long i2 = cusp_index(c2, S);
    if (i1 == ic)
      vj = (i2 == ic)?  gen_0: gen_1;
    else
      vj = (i2 == ic)? gen_m1: gen_0;
    gel(phi, j) = vj;
  }
  return phi;
}
static GEN
msfromcusp_i(GEN W, GEN c)
{
  GEN section, gen, S, phi;
  long j, ic, l, k = msk_get_weight(W);
  if (k == 2)
  {
    long N = ms_get_N(W);
    return N == 1? cgetg(1,t_COL): msfromcusp_trivial(W, c);
  }
  k = msk_get_weight(W);
  section = ms_get_section(W);
  gen = ms_get_genindex(W);
  S = ms_get_hashcusps(W);
  ic = cusp_index(c, S);
  l = lg(gen);
  phi = cgetg(l, t_COL);
  for (j = 1; j < l; j++)
  {
    GEN vj = NULL, g = gel(section, gen[j]); /* path_to_zm(generator) */
    GEN c1 = gel(g,1), c2 = gel(g,2);
    long i1 = cusp_index(c1, S);
    long i2 = cusp_index(c2, S);
    if (i1 == ic) vj = get_Ec_r(c1, k);
    if (i2 == ic)
    {
      GEN s = get_Ec_r(c2, k);
      vj = vj? gsub(vj, s): gneg(s);
    }
    if (!vj) vj = zerocol(k-1);
    gel(phi, j) = vj;
  }
  return getMorphism_basis(W, phi);
}
GEN
msfromcusp(GEN W, GEN c)
{
  pari_sp av = avma;
  long N;
  checkms(W);
  N = ms_get_N(W);
  switch(typ(c))
  {
    case t_INFINITY:
      c = mkvecsmall2(1,0);
      break;
    case t_INT:
      c = mkvecsmall2(smodis(c,N), 1);
      break;
    case t_FRAC:
      c = mkvecsmall2(smodis(gel(c,1),N), smodis(gel(c,2),N));
      break;
    default:
      pari_err_TYPE("msfromcusp",c);
  }
  return gerepilecopy(av, msfromcusp_i(W,c));
}

static GEN
mseisenstein_i(GEN W)
{
  GEN M, S = ms_get_hashcusps(W), cusps = gel(S,3);
  long i, l = lg(cusps);
  if (msk_get_weight(W)==2) l--;
  M = cgetg(l, t_MAT);
  for (i = 1; i < l; i++) gel(M,i) = msfromcusp_i(W, gel(cusps,i));
  return Qevproj_star(W, QM_image(M));
}
GEN
mseisenstein(GEN W)
{
  pari_sp av = avma;
  checkms(W);
  return gerepilecopy(av, Qevproj_init(mseisenstein_i(W)));
}

/* upper bound for log_2 |charpoly(T_p|S)|, where S is a cuspidal subspace of
 * dimension d, k is the weight */
#if 0
static long
TpS_char_bound(ulong p, long k, long d)
{ /* |eigenvalue| <= 2 p^(k-1)/2 */
  return d * (2 + (log2((double)p)*(k-1))/2);
}
#endif
static long
TpE_char_bound(ulong p, long k, long d)
{ /* |eigenvalue| <= 2 p^(k-1) */
  return d * (2 + log2((double)p)*(k-1));
}

GEN
mscuspidal(GEN W, long flag)
{
  pari_sp av = avma;
  GEN S, E, M, T, TE, chE;
  long bit;
  forprime_t F;
  ulong p, N;
  pari_timer ti;

  E = mseisenstein(W);
  N = ms_get_N(W);
  (void)u_forprime_init(&F, 2, ULONG_MAX);
  while ((p = u_forprime_next(&F)))
    if (N % p) break;
  if (DEBUGLEVEL) timer_start(&ti);
  T = mshecke(W, p, NULL);
  if (DEBUGLEVEL) timer_printf(&ti,"Tp, p = %ld", p);
  TE = Qevproj_apply(T, E); /* T_p | E */
  if (DEBUGLEVEL) timer_printf(&ti,"Qevproj_init(E)");
  bit = TpE_char_bound(p, msk_get_weight(W), lg(TE)-1);
  chE = QM_charpoly_ZX_bound(TE, bit);
  chE = ZX_radical(chE);
  M = RgX_RgM_eval(chE, T);
  S = Qevproj_init(QM_image(M));
  return gerepilecopy(av, flag? mkvec2(S,E): S);
}

/** INIT ELLSYM STRUCTURE **/
/* V a vector of ZM. If all of them have 0 last row, return NULL.
 * Otherwise return [m,i,j], where m = V[i][last,j] contains the value
 * of smallest absolute value */
static GEN
RgMV_find_non_zero_last_row(long offset, GEN V)
{
  long i, lasti = 0, lastj = 0, lV = lg(V);
  GEN m = NULL;
  for (i = 1; i < lV; i++)
  {
    GEN M = gel(V,i);
    long j, n, l = lg(M);
    if (l == 1) continue;
    n = nbrows(M);
    for (j = 1; j < l; j++)
    {
      GEN a = gcoeff(M, n, j);
      if (!gequal0(a) && (!m || abscmpii(a, m) < 0))
      {
        m = a; lasti = i; lastj = j;
        if (is_pm1(m)) goto END;
      }
    }
  }
END:
  if (!m) return NULL;
  return mkvec2(m, mkvecsmall2(lasti+offset, lastj));
}
/* invert the d_oo := (\gamma_oo - 1) operator, acting on
 * [x^(k-2), ..., y^(k-2)] */
static GEN
Delta_inv(GEN doo, long k)
{
  GEN M = RgX_act_ZGl2Q(doo, k);
  M = RgM_minor(M, k-1, 1); /* 1st column and last row are 0 */
  return ZM_inv_denom(M);
}
/* The ZX P = \sum a_i x^i y^{k-2-i} is given by the ZV [a_0, ..., a_k-2]~,
 * return Q and d such that P = doo Q + d y^k-2, where d in Z and Q */
static GEN
doo_decompose(GEN dinv, GEN P, GEN *pd)
{
  long l = lg(P); *pd = gel(P, l-1);
  P = vecslice(P, 1, l-2);
  return shallowconcat(gen_0, ZC_apply_dinv(dinv, P));
}

static GEN
get_phi_ij(long i,long j,long n, long s,long t,GEN P_st,GEN Q_st,GEN d_st,
           GEN P_ij, GEN lP_ij, GEN dinv)
{
  GEN ind, pols;
  if (i == s && j == t)
  {
    ind = mkvecsmall(1);
    pols = mkvec(scalarcol_shallow(gen_1, lg(P_st)-1)); /* x^{k-2} */
  }
  else
  {
    GEN d_ij, Q_ij = doo_decompose(dinv, lP_ij, &d_ij);
    GEN a = ZC_Z_mul(P_ij, d_st);
    GEN b = ZC_Z_mul(P_st, negi(d_ij));
    GEN c = RgC_sub(RgC_Rg_mul(Q_ij, d_st), RgC_Rg_mul(Q_st, d_ij));
    if (i == s) { /* j != t */
      ind = mkvecsmall2(1, s);
      pols = mkvec2(c, ZC_add(a, b));
    } else {
      ind = mkvecsmall3(1, i, s);
      pols = mkvec3(c, a, b); /* image of g_1, g_i, g_s */
    }
    pols = Q_primpart(pols);
  }
  return mkvec3(mkvecsmall3(i,j,n), ind, pols);
}

static GEN
mskinit_trivial(GEN WN)
{
  long dim = ms_get_nbE1(WN);
  return mkvec3(WN, gen_0, mkvec2(gen_0,mkvecsmall2(2, dim)));
}
/* sum of #cols of the matrices contained in V */
static long
RgMV_dim(GEN V)
{
  long l = lg(V), d = 0, i;
  for (i = 1; i < l; i++) d += lg(gel(V,i)) - 1;
  return d;
}
static GEN
mskinit_nontrivial(GEN WN, long k)
{
  GEN annT2 = gel(WN,8), annT31 = gel(WN,9), singlerel = gel(WN,10);
  GEN link, basis, monomials, Inv;
  long nbE1 = ms_get_nbE1(WN);
  GEN dinv = Delta_inv(ZG_neg( ZSl2_star(gel(singlerel,1)) ), k);
  GEN p1 = cgetg(nbE1+1, t_VEC), remove;
  GEN p2 = ZGV_tors(annT2, k);
  GEN p3 = ZGV_tors(annT31, k);
  GEN gentor = shallowconcat(p2, p3);
  GEN P_st, lP_st, Q_st, d_st;
  long n, i, dim, s, t, u;
  gel(p1, 1) = cgetg(1,t_MAT); /* dummy */
  for (i = 2; i <= nbE1; i++) /* skip 1st element = (\gamma_oo-1)g_oo */
  {
    GEN z = gel(singlerel, i);
    gel(p1, i) = RgX_act_ZGl2Q(ZSl2_star(z), k);
  }
  remove = RgMV_find_non_zero_last_row(nbE1, gentor);
  if (!remove) remove = RgMV_find_non_zero_last_row(0, p1);
  if (!remove) pari_err_BUG("msinit [no y^k-2]");
  remove = gel(remove,2); /* [s,t] */
  s = remove[1];
  t = remove[2];
  /* +1 because of = x^(k-2), but -1 because of Manin relation */
  dim = (k-1)*(nbE1-1) + RgMV_dim(p2) + RgMV_dim(p3);
  /* Let (g_1,...,g_d) be the Gamma-generators of Delta, g_1 = g_oo.
   * We describe modular symbols by the collection phi(g_1), ..., phi(g_d)
   * \in V := Q[x,y]_{k-2}, with right Gamma action.
   * For each i = 1, .., d, let V_i \subset V be the Q-vector space of
   * allowed values for phi(g_i): with basis (P^{i,j}) given by the monomials
   * x^(j-1) y^{k-2-(j-1)}, j = 1 .. k-1
   * (g_i in E_1) or the solution of the torsion equations (1 + gamma)P = 0
   * (g_i in T2) or (1 + gamma + gamma^2)P = 0 (g_i in T31). All such P
   * are chosen in Z[x,y] with Q_content 1.
   *
   * The Manin relation (singlerel) is of the form \sum_i \lambda_i g_i = 0,
   * where \lambda_i = 1 if g_i in T2 or T31, and \lambda_i = (1 - \gamma_i)
   * for g_i in E1.
   *
   * If phi \in Hom_Gamma(Delta, V), it is defined by phi(g_i) := P_i in V
   * with \sum_i P_i . \lambda_i^* = 0, where (\sum n_i g_i)^* :=
   * \sum n_i \gamma_i^(-1).
   *
   * We single out gamma_1 / g_1 (g_oo in Pollack-Stevens paper) and
   * write P_{i,j} \lambda_i^* =  Q_{i,j} (\gamma_1 - 1)^* + d_{i,j} y^{k-2}
   * where d_{i,j} is a scalar and Q_{i,j} in V; we normalize Q_{i,j} to
   * that the coefficient of x^{k-2} is 0.
   *
   * There exist (s,t) such that d_{s,t} != 0.
   * A Q-basis of the (dual) space of modular symbols is given by the
   * functions phi_{i,j}, 2 <= i <= d, 1 <= j <= k-1, mapping
   *  g_1 -> d_{s,t} Q_{i,j} - d_{i,j} Q_{s,t} + [(i,j)=(s,t)] x^{k-2}
   * If i != s
   *   g_i -> d_{s,t} P_{i,j}
   *   g_s -> - d_{i,j} P_{s,t}
   * If i = s, j != t
   *   g_i -> d_{s,t} P_{i,j} - d_{i,j} P_{s,t}
   * And everything else to 0. Again we normalize the phi_{i,j} such that
   * their image has content 1. */
  monomials = matid(k-1); /* represent the monomials x^{k-2}, ... , y^{k-2} */
  if (s <= nbE1) /* in E1 */
  {
    P_st = gel(monomials, t);
    lP_st = gmael(p1, s, t); /* P_{s,t} lambda_s^* */
  }
  else /* in T2, T31 */
  {
    P_st = gmael(gentor, s - nbE1, t);
    lP_st = P_st;
  }
  Q_st = doo_decompose(dinv, lP_st, &d_st);
  basis = cgetg(dim+1, t_VEC);
  link = cgetg(nbE1 + lg(gentor), t_VEC);
  gel(link,1) = cgetg(1,t_VECSMALL); /* dummy */
  n = 1;
  for (i = 2; i <= nbE1; i++)
  {
    GEN L = cgetg(k, t_VECSMALL);
    long j;
    /* link[i][j] = n gives correspondance between phi_{i,j} and basis[n] */
    gel(link,i) = L;
    for (j = 1; j < k; j++)
    {
      GEN lP_ij = gmael(p1, i, j); /* P_{i,j} lambda_i^* */
      GEN P_ij = gel(monomials,j);
      L[j] = n;
      gel(basis, n) = get_phi_ij(i,j,n, s,t, P_st, Q_st, d_st, P_ij, lP_ij, dinv);
      n++;
    }
  }
  for (u = 1; u < lg(gentor); u++,i++)
  {
    GEN V = gel(gentor,u);
    long j, lV = lg(V);
    GEN L = cgetg(lV, t_VECSMALL);
    gel(link,i) = L;
    for (j = 1; j < lV; j++)
    {
      GEN lP_ij = gel(V, j); /* P_{i,j} lambda_i^* = P_{i,j} */
      GEN P_ij = lP_ij;
      L[j] = n;
      gel(basis, n) = get_phi_ij(i,j,n, s,t, P_st, Q_st, d_st, P_ij, lP_ij, dinv);
      n++;
    }
  }
  Inv = cgetg(lg(link), t_VEC);
  gel(Inv,1) = cgetg(1, t_MAT); /* dummy */
  for (i = 2; i < lg(link); i++)
  {
    GEN M, inv, B = gel(link,i);
    long j, lB = lg(B);
    if (i == s) { B = vecsplice(B, t); lB--; } /* remove phi_st */
    M = cgetg(lB, t_MAT);
    for (j = 1; j < lB; j++)
    {
      GEN phi_ij = gel(basis, B[j]), pols = gel(phi_ij,3);
      gel(M, j) = gel(pols, 2); /* phi_ij(g_i) */
    }
    if (i <= nbE1 && i != s) /* maximal rank k-1 */
      inv = ZM_inv_denom(M);
    else /* i = s (rank k-2) or from torsion: rank k/3 or k/2 */
      inv = Qevproj_init(M);
    gel(Inv,i) = inv;
  }
  return mkvec3(WN, gen_0, mkvec5(basis, mkvecsmall2(k, dim), mkvecsmall2(s,t),
                                  link, Inv));
}
static GEN
add_star(GEN W, long sign)
{
  GEN s = msstar_i(W);
  GEN K = sign? QM_ker_r(gsubgs(s, sign)): cgetg(1,t_MAT);
  gel(W,2) = mkvec3(stoi(sign), s, Qevproj_init(K));
  return W;
}
/* WN = msinit_N(N) */
static GEN
mskinit(ulong N, long k, long sign)
{
  GEN W, WN = msinit_N(N);
  if (N == 1)
  {
    GEN basis, M = RgXV_to_RgM(mfperiodpolbasis(k, 0), k-1);
    GEN T = cgetg(1, t_VECSMALL), ind = mkvecsmall(1);
    long i, l = lg(M);
    basis = cgetg(l, t_VEC);
    for (i = 1; i < l; i++) gel(basis,i) = mkvec3(T, ind, mkvec(gel(M,i)));
    W = mkvec3(WN, gen_0, mkvec5(basis, mkvecsmall2(k, l-1), mkvecsmall2(0,0),
                                 gen_0, Qevproj_init(M)));
  }
  else
    W = k == 2? mskinit_trivial(WN)
              : mskinit_nontrivial(WN, k);
  return add_star(W, sign);
}
GEN
msinit(GEN N, GEN K, long sign)
{
  pari_sp av = avma;
  GEN W;
  long k;
  if (typ(N) != t_INT) pari_err_TYPE("msinit", N);
  if (typ(K) != t_INT) pari_err_TYPE("msinit", K);
  k = itos(K);
  if (k < 2) pari_err_DOMAIN("msinit","k", "<", gen_2,K);
  if (odd(k)) pari_err_IMPL("msinit [odd weight]");
  if (signe(N) <= 0) pari_err_DOMAIN("msinit","N", "<=", gen_0,N);
  W = mskinit(itou(N), k, sign);
  return gerepilecopy(av, W);
}

/* W = msinit, xpm integral modular symbol of weight 2, c t_FRAC
 * Return image of <oo->c> */
static GEN
Q_xpm(GEN W, GEN xpm, GEN c)
{
  pari_sp av = avma;
  GEN v;
  W = get_msN(W);
  v = init_act_trivial(W);
  Q_log_trivial(v, W, c); /* oo -> (a:b), c = a/b */
  return gerepileuptoint(av, ZV_zc_mul(xpm, v));
}

static GEN
eval_single(GEN s, long k, GEN B, long v)
{
  long i, l;
  GEN A = cgetg_copy(s,&l);
  for (i=1; i<l; i++) gel(A,i) = ZGl2Q_act_s(gel(B,i), gel(s,i), k);
  A = RgV_sum(A);
  if (is_vec_t(typ(A))) A = RgV_to_RgX(A, v);
  return A;
}
/* Evaluate symbol s on mspathlog B (= sum p_i g_i, p_i in Z[G]). Allow
 * s = t_MAT [ collection of symbols, return a vector ]*/
static GEN
mseval_by_values(GEN W, GEN s, GEN p, long v)
{
  long i, l, k = msk_get_weight(W);
  GEN A;
  if (k == 2)
  { /* trivial represention: don't bother with Z[G] */
    GEN B = mspathlog_trivial(W,p);
    if (typ(s) != t_MAT) return RgV_zc_mul(s,B);
    l = lg(s); A = cgetg(l, t_VEC);
    for (i = 1; i < l; i++) gel(A,i) = RgV_zc_mul(gel(s,i), B);
  }
  else
  {
    GEN B = mspathlog(W,p);
    if (typ(s) != t_MAT) return eval_single(s, k, B, v);
    l = lg(s); A = cgetg(l, t_VEC);
    for (i = 1; i < l; i++) gel(A,i) = eval_single(gel(s,i), k, B, v);
  }
  return A;
}

/* express symbol on the basis phi_{i,j} */
static GEN
symtophi(GEN W, GEN s)
{
  GEN e, basis = msk_get_basis(W);
  long i, l = lg(basis);
  if (lg(s) != l) pari_err_TYPE("mseval",s);
  e = zerovec(ms_get_nbgen(W));
  for (i=1; i<l; i++)
  {
    GEN phi, ind, pols, c = gel(s,i);
    long j, m;
    if (gequal0(c)) continue;
    phi = gel(basis,i);
    ind = gel(phi,2); m = lg(ind);
    pols = gel(phi,3);
    for (j=1; j<m; j++)
    {
      long t = ind[j];
      gel(e,t) = gadd(gel(e,t), gmul(c, gel(pols,j)));
    }
  }
  return e;
}
/* evaluate symbol s on path p */
GEN
mseval(GEN W, GEN s, GEN p)
{
  pari_sp av = avma;
  long i, k, l, v = 0;
  checkms(W);
  k = msk_get_weight(W);
  switch(typ(s))
  {
    case t_VEC: /* values s(g_i) */
      if (lg(s)-1 != ms_get_nbgen(W)) pari_err_TYPE("mseval",s);
      if (!p) return gcopy(s);
      v = gvar(s);
      break;
    case t_COL:
      if (msk_get_sign(W))
      {
        GEN star = gel(msk_get_starproj(W), 1);
        if (lg(star) == lg(s)) s = RgM_RgC_mul(star, s);
      }
      if (k == 2) /* on the dual basis of (g_i) */
      {
        if (lg(s)-1 != ms_get_nbE1(W)) pari_err_TYPE("mseval",s);
        if (!p) return gtrans(s);
      }
      else
        s = symtophi(W,s);
      break;
    case t_MAT:
      l = lg(s);
      if (!p)
      {
        GEN v = cgetg(l, t_VEC);
        for (i = 1; i < l; i++) gel(v,i) = mseval(W, gel(s,i), NULL);
        return v;
      }
      if (l == 1) return cgetg(1, t_VEC);
      if (msk_get_sign(W))
      {
        GEN star = gel(msk_get_starproj(W), 1);
        if (lg(star) == lgcols(s)) s = RgM_mul(star, s);
      }
      if (k == 2)
      { if (nbrows(s) != ms_get_nbE1(W)) pari_err_TYPE("mseval",s); }
      else
      {
        GEN t = cgetg(l, t_MAT);
        for (i = 1; i < l; i++) gel(t,i) = symtophi(W,gel(s,i));
        s = t;
      }
      break;
    default: pari_err_TYPE("mseval",s);
  }
  if (p)
    s = mseval_by_values(W, s, p, v);
  else
  {
    l = lg(s);
    for (i = 1; i < l; i++)
    {
      GEN c = gel(s,i);
      if (!isintzero(c)) gel(s,i) = RgV_to_RgX(gel(s,i), v);
    }
  }
  return gerepilecopy(av, s);
}

static GEN
allxpm(GEN W, GEN xpm, long f)
{
  GEN v, L = coprimes_zv(f);
  long a, nonzero = 0;
  v = const_vec(f, NULL);
  for (a = 1; a <= f; a++)
  {
    GEN c;
    if (!L[a]) continue;
    c = Q_xpm(W, xpm, sstoQ(a, f));
    if (!gequal0(c)) { gel(v,a) = c; nonzero = 1; }
  }
  return nonzero? v: NULL;
}
/* \sum_{a mod f} chi(a) x(a/f) */
static GEN
seval(GEN G, GEN chi, GEN vx)
{
  GEN vZ, T, s = gen_0, go = zncharorder(G,chi);
  long i, l = lg(vx), o = itou(go);
  T = polcyclo(o,0);
  vZ = mkvec2(RgXQ_powers(RgX_rem(pol_x(0), T), o-1, T), go);
  for (i = 1; i < l; i++)
  {
    GEN x = gel(vx,i);
    if (x) s = gadd(s, gmul(x, znchareval(G, chi, utoi(i), vZ)));
  }
  return gequal0(s)? NULL: poleval(s, rootsof1u_cx(o, DEFAULTPREC));
}

static long
nb_components(GEN E) { return signe(ell_get_disc(E)) > 0? 2: 1; }
/* E minimal */
static GEN
ellperiod(GEN E, long s)
{
  GEN w = ellR_omega(E,DEFAULTPREC);
  if (s == 1)
    w = gel(w,1);
  else if (nb_components(E) == 2)
    w = gneg(gel(w,2));
  else
    w = mkcomplex(gen_0, gneg(gmul2n(imag_i(gel(w,2)), 1)));
  return w;
}

/* Let W = msinit(conductor(E), 2), xpm an integral modular symbol with the same
 * eigenvalues as L_E. There exist a unique C such that
 *   C*L(E,(D/.),1)_{xpm} = L(E,(D/.),1) / w1(E_D) != 0, for all D fundamental,
 * sign(D) = s, and such that E_D has rank 0. Return C * ellperiod(E,s) */
static GEN
ell_get_Cw(GEN LE, GEN W, GEN xpm, long s)
{
  long f, NE = ms_get_N(W);
  const long bit = 64;

  for (f = 1;; f++)
  { /* look for chi with conductor f coprime to N(E) and parity s
     * such that L(E,chi,1) != 0 */
    pari_sp av = avma;
    GEN vchi, vx, G;
    long l, i;
    if ((f & 3) == 2 || ugcd(NE,f) != 1) continue;
    vx = allxpm(W, xpm, f); if (!vx) continue;
    G = znstar0(utoipos(f),1);
    vchi = chargalois(G,NULL); l = lg(vchi);
    for (i = 1; i < l; i++)
    {
      pari_sp av2 = avma;
      GEN tau, z, S, L, chi = gel(vchi,i);
      long o = zncharisodd(G,chi);
      if ((s > 0 && o) || (s < 0 && !o)
          || itos(zncharconductor(G, chi)) != f) continue;
      S = seval(G, chi, vx);
      if (!S) { avma = av2; continue; }

      L = lfuntwist(LE, mkvec2(G, zncharconj(G,chi)));
      z = lfun(L, gen_1, bit);
      tau = znchargauss(G, chi, gen_1, bit);
      return gdiv(gmul(z, tau), S); /* C * w */
    }
    avma = av;
  }
}
static GEN
ell_get_scale(GEN LE, GEN W, long sign, GEN x)
{
  if (sign)
    return ell_get_Cw(LE, W, gel(x,1), sign);
  else
  {
    GEN Cwp = ell_get_Cw(LE, W, gel(x,1), 1);
    GEN Cwm = ell_get_Cw(LE, W, gel(x,2),-1);
    return mkvec2(Cwp, Cwm);
  }
}
/* E minimal */
static GEN
msfromell_scale(GEN x, GEN Cw, GEN E, long s)
{
  GEN B = int2n(32);
  if (s)
  {
    GEN C = gdiv(Cw, ellperiod(E,s));
    return ZC_Q_mul(gel(x,1), bestappr(C,B));
  }
  else
  {
    GEN xp = gel(x,1), Cp = gdiv(gel(Cw,1), ellperiod(E, 1)), L;
    GEN xm = gel(x,2), Cm = gdiv(gel(Cw,2), ellperiod(E,-1));
    xp = ZC_Q_mul(xp, bestappr(Cp,B));
    xm = ZC_Q_mul(xm, bestappr(Cm,B));
    if (signe(ell_get_disc(E)) > 0)
      L = mkmat2(xp, xm); /* E(R) has 2 connected components */
    else
      L = mkmat2(gsub(xp,xm), gmul2n(xm,1));
    return mkvec3(xp, xm, L);
  }
}
/* v != 0 */
static GEN
Flc_normalize(GEN v, ulong p)
{
  long i, l = lg(v);
  for (i = 1; i < l; i++)
    if (v[i])
    {
      if (v[i] != 1) v = Flv_Fl_div(v, v[i], p);
      return v;
    }
  return NULL;
}
/* K \cap Ker M  [F_l vector spaces]. K = NULL means full space */
static GEN
msfromell_ker(GEN K, GEN M, ulong l)
{
  GEN B, Ml = ZM_to_Flm(M, l);
  if (K) Ml = Flm_mul(Ml, K, l);
  B = Flm_ker(Ml, l);
  if (!K) K = B;
  else if (lg(B) < lg(K))
    K = Flm_mul(K, B, l);
  return K;
}
/* K = \cap_p Ker(T_p - a_p), 2-dimensional. Set *xl to the 1-dimensional
 * Fl-basis  such that star . xl = sign . xl if sign != 0 and
 * star * xl[1] = xl[1]; star * xl[2] = -xl[2] if sign = 0 */
static void
msfromell_l(GEN *pxl, GEN K, GEN star, long sign, ulong l)
{
  GEN s = ZM_to_Flm(star, l);
  GEN a = gel(K,1), Sa = Flm_Flc_mul(s,a,l);
  GEN b = gel(K,2);
  GEN t = Flv_add(a,Sa,l), xp, xm;
  if (zv_equal0(t))
  {
    xm = a;
    xp = Flv_add(b,Flm_Flc_mul(s,b,l), l);
  }
  else
  {
    xp = t; t = Flv_sub(a, Sa, l);
    xm = zv_equal0(t)? Flv_sub(b, Flm_Flc_mul(s,b,l), l): t;
  }
  /* xp = 0 on Im(S - 1), xm = 0 on Im(S + 1) */
  if (sign > 0)
    *pxl = mkmat(Flc_normalize(xp, l));
  else if (sign < 0)
    *pxl = mkmat(Flc_normalize(xm, l));
  else
    *pxl = mkmat2(Flc_normalize(xp, l), Flc_normalize(xm, l));
}
/* return a primitive symbol */
static GEN
msfromell_ratlift(GEN x, GEN q)
{
  GEN B = sqrti(shifti(q,-1));
  GEN r = FpM_ratlift(x, q, B, B, NULL);
  if (r) r = Q_primpart(r);
  return r;
}
static int
msfromell_check(GEN x, GEN vT, GEN star, long sign)
{
  long i, l;
  GEN sx;
  if (!x) return 0;
  l = lg(vT);
  for (i = 1; i < l; i++)
  {
    GEN T = gel(vT,i);
    if (!gequal0(ZM_mul(T, x))) return 0; /* fail */
  }
  sx = ZM_mul(star,x);
  if (sign)
    return ZV_equal(gel(sx,1), sign > 0? gel(x,1): ZC_neg(gel(x,1)));
  else
    return ZV_equal(gel(sx,1),gel(x,1)) && ZV_equal(gel(sx,2),ZC_neg(gel(x,2)));
}
GEN
msfromell(GEN E0, long sign)
{
  pari_sp av = avma, av2;
  GEN T, Cw, E, NE, star, q, vT, xl, xr, W, x = NULL, K = NULL;
  long lE, single;
  ulong p, l, N;
  forprime_t S, Sl;

  if (typ(E0) != t_VEC) pari_err_TYPE("msfromell",E0);
  lE = lg(E0);
  if (lE == 1) return cgetg(1,t_VEC);
  single = (typ(gel(E0,1)) != t_VEC);
  E = single ? E0: gel(E0,1);
  NE = ellQ_get_N(E);
  /* must make it integral for ellap; we have minimal model at hand */
  T = obj_check(E, Q_MINIMALMODEL); if (lg(T) != 2) E = gel(T,3);
  N = itou(NE); av2 = avma;
  W = gerepilecopy(av2, mskinit(N,2,0));
  star = msk_get_star(W);
  init_modular_small(&Sl);
  /* loop for p <= count_Manin_symbols(N) / 6 would be enough */
  (void)u_forprime_init(&S, 2, ULONG_MAX);
  vT = cgetg(1, t_VEC);
  l = u_forprime_next(&Sl);
  while( (p = u_forprime_next(&S)) )
  {
    GEN M;
    if (N % p == 0) continue;
    av2 = avma;
    M = RgM_Rg_sub_shallow(mshecke_i(W, p), ellap(E, utoipos(p)));
    M = gerepilecopy(av2, M);
    vT = shallowconcat(vT, mkvec(M)); /* for certification at the end */
    K = msfromell_ker(K, M, l);
    if (lg(K) == 3) break;
  }
  if (!p) pari_err_BUG("msfromell: ran out of primes");

  /* mod one l should be enough */
  msfromell_l(&xl, K, star, sign, l);
  x = ZM_init_CRT(xl, l);
  q = utoipos(l);
  xr = msfromell_ratlift(x, q);
  /* paranoia */
  while (!msfromell_check(xr, vT, star, sign) && (l = u_forprime_next(&Sl)) )
  {
    GEN K = NULL;
    long i, lvT = lg(vT);
    for (i = 1; i < lvT; i++)
    {
      K = msfromell_ker(K, gel(vT,i), l);
      if (lg(K) == 3) break;
    }
    if (i >= lvT) { x = NULL; continue; }
    msfromell_l(&xl, K, star, sign, l);
    ZM_incremental_CRT(&x, xl, &q, l);
    xr = msfromell_ratlift(x, q);
  }
  /* linear form = 0 on all Im(Tp - ap) and Im(S - sign) if sign != 0 */
  Cw = ell_get_scale(lfuncreate(E), W, sign, xr);
  if (single)
    x = msfromell_scale(xr, Cw, E, sign);
  else
  { /* assume all E0[i] isogenous, given by minimal models */
    GEN v = cgetg(lE, t_VEC);
    long i;
    for (i=1; i<lE; i++) gel(v,i) = msfromell_scale(xr, Cw, gel(E0,i), sign);
    x = v;
  }
  return gerepilecopy(av, mkvec2(W, x));
}

GEN
msfromhecke(GEN W, GEN v, GEN H)
{
  pari_sp av = avma;
  long i, l = lg(v);
  GEN K = NULL;
  checkms(W);
  if (typ(v) != t_VEC) pari_err_TYPE("msfromhecke",v);
  for (i = 1; i < l; i++)
  {
    GEN K2, T, p, P, c = gel(v,i);
    if (typ(c) != t_VEC || lg(c) != 3) pari_err_TYPE("msfromhecke",v);
    p = gel(c,1);
    if (typ(p) != t_INT) pari_err_TYPE("msfromhecke",v);
    P = gel(c,2);
    switch(typ(P))
    {
      case t_INT:
        P = deg1pol_shallow(gen_1, negi(P), 0);
        break;
      case t_POL:
        if (RgX_is_ZX(P)) break;
      default:
        pari_err_TYPE("msfromhecke",v);
    };
    T = mshecke(W, itos(p), H);
    T = Q_primpart(RgX_RgM_eval(P, T));
    if (K) T = ZM_mul(T,K);
    K2 = ZM_ker(T);
    if (!K) K = K2;
    else if (lg(K2) < lg(K)) K = ZM_mul(K,K2);
  }
  return gerepilecopy(av, K);
}

/* OVERCONVERGENT MODULAR SYMBOLS */

static GEN
mspadic_get_Wp(GEN W) { return gel(W,1); }
static GEN
mspadic_get_Tp(GEN W) { return gel(W,2); }
static GEN
mspadic_get_bin(GEN W) { return gel(W,3); }
static GEN
mspadic_get_actUp(GEN W) { return gel(W,4); }
static GEN
mspadic_get_q(GEN W) { return gel(W,5); }
static long
mspadic_get_p(GEN W) { return gel(W,6)[1]; }
static long
mspadic_get_n(GEN W) { return gel(W,6)[2]; }
static long
mspadic_get_flag(GEN W) { return gel(W,6)[3]; }
static GEN
mspadic_get_M(GEN W) { return gel(W,7); }
static GEN
mspadic_get_C(GEN W) { return gel(W,8); }
static long
mspadic_get_weight(GEN W) { return msk_get_weight(mspadic_get_Wp(W)); }

void
checkmspadic(GEN W)
{
  if (typ(W) != t_VEC || lg(W) != 9) pari_err_TYPE("checkmspadic",W);
  checkms(mspadic_get_Wp(W));
}

/* f in M_2(Z) \cap GL_2(Q), p \nmid a [ and for the result to mean anything
 * p | c, but not needed here]. Return the matrix M in M_D(Z), D = M+k-1
 * such that, if v = \int x^i d mu, i < D, is a vector of D moments of mu,
 * then M * v is the vector of moments of mu | f  mod p^D */
static GEN
moments_act_i(struct m_act *S, GEN f)
{
  long j, k = S->k, D = S->dim;
  GEN a = gcoeff(f,1,1), b = gcoeff(f,1,2);
  GEN c = gcoeff(f,2,1), d = gcoeff(f,2,2);
  GEN u, z, q = S->q, mat = cgetg(D+1, t_MAT);

  a = modii(a,q);
  c = modii(c,q);
  z = FpX_powu(deg1pol(c,a,0), k-2, q); /* (a+cx)^(k-2) */
  /* u := (b+dx) / (a+cx) mod (q,x^D) = (b/a +d/a*x) / (1 - (-c/a)*x) */
  if (!equali1(a))
  {
    GEN ai = Fp_inv(a,q);
    b = Fp_mul(b,ai,q);
    c = Fp_mul(c,ai,q);
    d = Fp_mul(d,ai,q);
  }
  u = deg1pol_shallow(d, b, 0);
  /* multiply by 1 / (1 - (-c/a)*x) */
  if (signe(c))
  {
    GEN C = Fp_neg(c,q), v = cgetg(D+2,t_POL);
    v[1] = evalsigne(1)|evalvarn(0);
    gel(v, 2) = gen_1; gel(v, 3) = C;
    for (j = 4; j < D+2; j++)
    {
      GEN t = Fp_mul(gel(v,j-1), C, q);
      if (!signe(t)) { setlg(v,j); break; }
      gel(v,j) = t;
    }
    u = FpXn_mul(u, v, D, q);
  }
  for (j = 1; j <= D; j++)
  {
    gel(mat,j) = RgX_to_RgC(z, D); /* (a+cx)^(k-2) * ((b+dx)/(a+cx))^(j-1) */
    if (j != D) z = FpXn_mul(z, u, D, q);
  }
  return shallowtrans(mat);
}
static GEN
moments_act(struct m_act *S, GEN f)
{ pari_sp av = avma; return gerepilecopy(av, moments_act_i(S,f)); }
static GEN
init_moments_act(GEN W, long p, long n, GEN q, GEN v)
{
  struct m_act S;
  long k = msk_get_weight(W);
  S.p = p;
  S.k = k;
  S.q = q;
  S.dim = n+k-1;
  S.act = &moments_act; return init_dual_act(v,W,W,&S);
}

static void
clean_tail(GEN phi, long c, GEN q)
{
  long a, l = lg(phi);
  for (a = 1; a < l; a++)
  {
    GEN P = FpV_red(gel(phi,a), q); /* phi(G_a) = vector of moments */
    long j, lP = lg(P);
    for (j = c; j < lP; j++) gel(P,j) = gen_0; /* reset garbage to 0 */
    gel(phi,a) = P;
  }
}
/* concat z to all phi[i] */
static GEN
concat2(GEN phi, GEN z)
{
  long i, l;
  GEN v = cgetg_copy(phi,&l);
  for (i = 1; i < l; i++) gel(v,i) = shallowconcat(gel(phi,i), z);
  return v;
}
static GEN
red_mod_FilM(GEN phi, ulong p, long k, long flag)
{
  long a, l;
  GEN den = gen_1, v = cgetg_copy(phi, &l);
  if (flag)
  {
    phi = Q_remove_denom(phi, &den);
    if (!den) { den = gen_1; flag = 0; }
  }
  for (a = 1; a < l; a++)
  {
    GEN P = gel(phi,a), q = den;
    long j;
    for (j = lg(P)-1; j >= k+1; j--)
    {
      q = muliu(q,p);
      gel(P,j) = modii(gel(P,j),q);
    }
    q = muliu(q,p);
    for (     ; j >= 1; j--)
      gel(P,j) = modii(gel(P,j),q);
    gel(v,a) = P;
  }
  if (flag) v = gdiv(v, den);
  return v;
}

/* denom(C) | p^(2(k-1) - v_p(ap)) */
static GEN
oms_dim2(GEN W, GEN phi, GEN C, GEN ap)
{
  long t, i, k = mspadic_get_weight(W);
  long p = mspadic_get_p(W), n = mspadic_get_n(W);
  GEN phi1 = gel(phi,1), phi2 = gel(phi,2);
  GEN v, q = mspadic_get_q(W);
  GEN act = mspadic_get_actUp(W);

  t = signe(ap)? Z_lval(ap,p) : k-1;
  phi1 = concat2(phi1, zerovec(n));
  phi2 = concat2(phi2, zerovec(n));
  for (i = 1; i <= n; i++)
  {
    phi1 = dual_act(k-1, act, phi1);
    phi1 = dual_act(k-1, act, phi1);
    clean_tail(phi1, k + i*t, q);

    phi2 = dual_act(k-1, act, phi2);
    phi2 = dual_act(k-1, act, phi2);
    clean_tail(phi2, k + i*t, q);
  }
  C = gpowgs(C,n);
  v = RgM_RgC_mul(C, mkcol2(phi1,phi2));
  phi1 = red_mod_FilM(gel(v,1), p, k, 1);
  phi2 = red_mod_FilM(gel(v,2), p, k, 1);
  return mkvec2(phi1,phi2);
}

/* flag = 0 iff alpha is a p-unit */
static GEN
oms_dim1(GEN W, GEN phi, GEN alpha, long flag)
{
  long i, k = mspadic_get_weight(W);
  long p = mspadic_get_p(W), n = mspadic_get_n(W);
  GEN q = mspadic_get_q(W);
  GEN act = mspadic_get_actUp(W);
  phi = concat2(phi, zerovec(n));
  for (i = 1; i <= n; i++)
  {
    phi = dual_act(k-1, act, phi);
    clean_tail(phi, k + i, q);
  }
  phi = gmul(lift_shallow(gpowgs(alpha,n)), phi);
  phi = red_mod_FilM(phi, p, k, flag);
  return mkvec(phi);
}

/* lift polynomial P in RgX[X,Y]_{k-2} to a distribution \mu such that
 * \int (Y - X z)^(k-2) d\mu(z) = P(X,Y)
 * Return the t_VEC of k-1 first moments of \mu: \int z^i d\mu(z), 0<= i < k-1.
 *   \sum_j (-1)^(k-2-j) binomial(k-2,j) Y^j \int z^(k-2-j) d\mu(z) = P(1,Y)
 * Input is P(1,Y), bin = vecbinomial(k-2): bin[j] = binomial(k-2,j-1) */
static GEN
RgX_to_moments(GEN P, GEN bin)
{
  long j, k = lg(bin);
  GEN Pd, Bd;
  if (typ(P) != t_POL) P = scalarpol(P,0);
  P = RgX_to_RgC(P, k-1); /* deg <= k-2 */
  settyp(P, t_VEC);
  Pd = P+1;  /* Pd[i] = coeff(P,i) */
  Bd = bin+1;/* Bd[i] = binomial(k-2,i) */
  for (j = 1; j < k-2; j++)
  {
    GEN c = gel(Pd,j);
    if (odd(j)) c = gneg(c);
    gel(Pd,j) = gdiv(c, gel(Bd,j));
  }
  return vecreverse(P);
}
static GEN
RgXC_to_moments(GEN v, GEN bin)
{
  long i, l;
  GEN w = cgetg_copy(v,&l);
  for (i=1; i<l; i++) gel(w,i) = RgX_to_moments(gel(v,i),bin);
  return w;
}

/* W an mspadic, assume O[2] is integral, den is the cancelled denominator
 * or NULL, L = log(path)^* in sparse form */
static GEN
omseval_int(struct m_act *S, GEN PHI, GEN L, hashtable *H)
{
  long i, l;
  GEN v = cgetg_copy(PHI, &l);
  ZGl2QC_to_act(S, L, H); /* as operators on V */
  for (i = 1; i < l; i++)
  {
    GEN T = dense_act_col(L, gel(PHI,i));
    gel(v,i) = T? FpC_red(T,S->q): zerocol(S->dim);
  }
  return v;
}

GEN
msomseval(GEN W, GEN phi, GEN path)
{
  struct m_act S;
  pari_sp av = avma;
  GEN v, Wp;
  long n, vden;
  checkmspadic(W);
  if (typ(phi) != t_COL || lg(phi) != 4)  pari_err_TYPE("msomseval",phi);
  vden = itos(gel(phi,2));
  phi = gel(phi,1);
  n = mspadic_get_n(W);
  Wp= mspadic_get_Wp(W);
  S.k = mspadic_get_weight(W);
  S.p = mspadic_get_p(W);
  S.q = powuu(S.p, n+vden);
  S.dim = n + S.k - 1;
  S.act = &moments_act;
  path = path_to_M2(path);
  v = omseval_int(&S, phi, M2_logf(Wp,path,NULL), NULL);
  return gerepilecopy(av, v);
}
/* W = msinit(N,k,...); if flag < 0 or flag >= k-1, allow all symbols;
 * else commit to v_p(a_p) <= flag (ordinary if flag = 0)*/
GEN
mspadicinit(GEN W, long p, long n, long flag)
{
  pari_sp av = avma;
  long a, N, k;
  GEN P, C, M, bin, Wp, Tp, q, pn, actUp, teich, pas;

  checkms(W);
  N = ms_get_N(W);
  k = msk_get_weight(W);
  if (flag < 0) flag = 1; /* worst case */
  else if (flag >= k) flag = k-1;

  bin = vecbinomial(k-2);
  Tp = mshecke(W, p, NULL);
  if (N % p == 0)
  {
    if ((N/p) % p == 0) pari_err_IMPL("mspadicinit when p^2 | N");
    /* a_p != 0 */
    Wp = W;
    M = gen_0;
    flag = (k-2) / 2; /* exact valuation */
    /* will multiply by matrix with denominator p^(k-2)/2 in mspadicint.
     * Except if p = 2 (multiply by alpha^2) */
    if (p == 2) n += k-2; else n += (k-2)/2;
    pn = powuu(p,n);
    /* For accuracy mod p^n, oms_dim1 require p^(k/2*n) */
    q = powiu(pn, k/2);
  }
  else
  { /* p-stabilize */
    long s = msk_get_sign(W);
    GEN M1, M2;

    Wp = mskinit(N*p, k, s);
    M1 = getMorphism(W, Wp, mkvec(mat2(1,0,0,1)));
    M2 = getMorphism(W, Wp, mkvec(mat2(p,0,0,1)));
    if (s)
    {
      GEN SW = msk_get_starproj(W), SWp = msk_get_starproj(Wp);
      M1 = Qevproj_apply2(M1, SW, SWp);
      M2 = Qevproj_apply2(M2, SW, SWp);
    }
    M = mkvec2(M1,M2);
    n += Z_lval(Q_denom(M), p); /*den. introduced by p-stabilization*/
    /* in supersingular case: will multiply by matrix with denominator p^k
     * in mspadicint. Except if p = 2 (multiply by alpha^2) */
    if (flag) { if (p == 2) n += 2*k-2; else n += k; }
    pn = powuu(p,n);
    /* For accuracy mod p^n, supersingular require p^((2k-1-v_p(a_p))*n) */
    if (flag) /* k-1 also takes care of a_p = 0. Worst case v_p(a_p) = flag */
      q = powiu(pn, 2*k-1 - flag);
    else
      q = pn;
  }
  actUp = init_moments_act(Wp, p, n, q, Up_matrices(p));

  if (p == 2) C = gen_0;
  else
  {
    pas = matpascal(n);
    teich = teichmullerinit(p, n+1);
    P = gpowers(utoipos(p), n);
    C = cgetg(p, t_VEC);
    for (a = 1; a < p; a++)
    { /* powb[j+1] = ((a - w(a)) / p)^j mod p^n */
      GEN powb = Fp_powers(diviuexact(subui(a, gel(teich,a)), p), n, pn);
      GEN Ca = cgetg(n+2, t_VEC);
      long j, r, ai = Fl_inv(a, p); /* a^(-1) */
      gel(C,a) = Ca;
      for (j = 0; j <= n; j++)
      {
        GEN Caj = cgetg(j+2, t_VEC);
        GEN atij = gel(teich, Fl_powu(ai,j,p));/* w(a)^(-j) = w(a^(-j) mod p) */
        gel(Ca,j+1) = Caj;
        for (r = 0; r <= j; r++)
        {
          GEN c = Fp_mul(gcoeff(pas,j+1,r+1), gel(powb, j-r+1), pn);
          c = Fp_mul(c,atij,pn); /* binomial(j,r)*b^(j-r)*w(a)^(-j) mod p^n */
          gel(Caj,r+1) = mulii(c, gel(P,j+1)); /* p^j * c mod p^(n+j) */
        }
      }
    }
  }
  return gerepilecopy(av, mkvecn(8, Wp,Tp, bin, actUp, q,
                                 mkvecsmall3(p,n,flag), M, C));
}

#if 0
/* assume phi an ordinary OMS */
static GEN
omsactgl2(GEN W, GEN phi, GEN M)
{
  GEN q, Wp, act;
  long p, k, n;
  checkmspadic(W);
  Wp = mspadic_get_Wp(W);
  p = mspadic_get_p(W);
  k = mspadic_get_weight(W);
  n = mspadic_get_n(W);
  q = mspadic_get_q(W);
  act = init_moments_act(Wp, p, n, q, M);
  phi = gel(phi,1);
  return dual_act(k-1, act, gel(phi,1));
}
#endif

static GEN
eigenvalue(GEN T, GEN x)
{
  long i, l = lg(x);
  for (i = 1; i < l; i++)
    if (!isintzero(gel(x,i))) break;
  if (i == l) pari_err_DOMAIN("mstooms", "phi", "=", gen_0, x);
  return gdiv(RgMrow_RgC_mul(T,x,i), gel(x,i));
}

/* p coprime to ap, return unit root of x^2 - ap*x + p^(k-1), accuracy p^n */
GEN
mspadic_unit_eigenvalue(GEN ap, long k, GEN p, long n)
{
  GEN sqrtD, D = subii(sqri(ap), shifti(powiu(p,k-1),2));
  if (absequaliu(p,2))
  {
    n++; sqrtD = Zp_sqrt(D, p, n);
    if (mod4(sqrtD) != mod4(ap)) sqrtD = negi(sqrtD);
  }
  else
    sqrtD = Zp_sqrtlift(D, ap, p, n);
  /* sqrtD = ap (mod p) */
  return gmul2n(gadd(ap, cvtop(sqrtD,p,n)), -1);
}

/* W = msinit(N,k,...); phi = T_p/U_p - eigensymbol */
GEN
mstooms(GEN W, GEN phi)
{
  pari_sp av = avma;
  GEN Wp, bin, Tp, c, alpha, ap, phi0, M;
  long k, p, vden;

  checkmspadic(W);
  if (typ(phi) != t_COL)
  {
    if (!is_Qevproj(phi)) pari_err_TYPE("mstooms",phi);
    phi = gel(phi,1);
    if (lg(phi) != 2) pari_err_TYPE("mstooms [dim_Q (eigenspace) > 1]",phi);
    phi = gel(phi,1);
  }

  Wp = mspadic_get_Wp(W);
  Tp = mspadic_get_Tp(W);
  bin = mspadic_get_bin(W);
  k = msk_get_weight(Wp);
  p = mspadic_get_p(W);
  M = mspadic_get_M(W);

  phi = Q_remove_denom(phi, &c);
  ap = eigenvalue(Tp, phi);
  vden = c? Z_lvalrem(c, p, &c): 0;

  if (typ(M) == t_INT)
  { /* p | N */
    GEN c1;
    alpha = ap;
    alpha = ginv(alpha);
    phi0 = mseval(Wp, phi, NULL);
    phi0 = RgXC_to_moments(phi0, bin);
    phi0 = Q_remove_denom(phi0, &c1);
    if (c1) { vden += Z_lvalrem(c1, p, &c1); c = mul_denom(c,c1); }
    if (umodiu(ap,p)) /* p \nmid a_p */
      phi = oms_dim1(W, phi0, alpha, 0);
    else
    {
      phi = oms_dim1(W, phi0, alpha, 1);
      phi = Q_remove_denom(phi, &c1);
      if (c1) { vden += Z_lvalrem(c1, p, &c1); c = mul_denom(c,c1); }
    }
  }
  else
  { /* p-stabilize */
    GEN M1, M2, phi1, phi2, c1;
    if (typ(M) != t_VEC || lg(M) != 3) pari_err_TYPE("mstooms",W);
    M1 = gel(M,1);
    M2 = gel(M,2);

    phi1 = RgM_RgC_mul(M1, phi);
    phi2 = RgM_RgC_mul(M2, phi);
    phi1 = mseval(Wp, phi1, NULL);
    phi2 = mseval(Wp, phi2, NULL);

    phi1 = RgXC_to_moments(phi1, bin);
    phi2 = RgXC_to_moments(phi2, bin);
    phi = Q_remove_denom(mkvec2(phi1,phi2), &c1);
    phi1 = gel(phi,1);
    phi2 = gel(phi,2);
    if (c1) { vden += Z_lvalrem(c1, p, &c1); c = mul_denom(c,c1); }
    /* all polynomials multiplied by c p^vden */
    if (umodiu(ap, p))
    {
      alpha = mspadic_unit_eigenvalue(ap, k, utoipos(p), mspadic_get_n(W));
      alpha = ginv(alpha);
      phi0 = gsub(phi1, gmul(lift_shallow(alpha),phi2));
      phi = oms_dim1(W, phi0, alpha, 0);
    }
    else
    { /* p | ap, alpha = [a_p, -1; p^(k-1), 0] */
      long flag = mspadic_get_flag(W);
      if (!flag || (signe(ap) && Z_lval(ap,p) < flag))
        pari_err_TYPE("mstooms [v_p(ap) > mspadicinit flag]", phi);
      alpha = mkmat22(ap,gen_m1, powuu(p, k-1),gen_0);
      alpha = ginv(alpha);
      phi = oms_dim2(W, mkvec2(phi1,phi2), gsqr(alpha), ap);
      phi = Q_remove_denom(phi, &c1);
      if (c1) { vden += Z_lvalrem(c1, p, &c1); c = mul_denom(c,c1); }
    }
  }
  if (vden) c = mul_denom(c, powuu(p,vden));
  if (p == 2) alpha = gsqr(alpha);
  if (c) alpha = gdiv(alpha,c);
  if (typ(alpha) == t_MAT)
  { /* express in basis (omega,-p phi(omega)) */
    gcoeff(alpha,2,1) = gdivgs(gcoeff(alpha,2,1), -p);
    gcoeff(alpha,2,2) = gdivgs(gcoeff(alpha,2,2), -p);
    /* at the end of mspadicint we shall multiply result by [1,0;0,-1/p]*alpha
     * vden + k is the denominator of this matrix */
  }
  /* phi is integral-valued */
  return gerepilecopy(av, mkcol3(phi, stoi(vden), alpha));
}

/* HACK: the v[j] have different lengths */
static GEN
FpVV_dotproduct(GEN v, GEN w, GEN p)
{
  long j, l = lg(v);
  GEN T = cgetg(l, t_VEC);
  for (j = 1; j < l; j++) gel(T,j) = FpV_dotproduct(gel(v,j),w,p);
  return T;
}

/* \int (-4z)^j given \int z^j */
static GEN
twistmoment_m4(GEN v)
{
  long i, l;
  GEN w = cgetg_copy(v, &l);
  for (i = 1; i < l; i++)
  {
    GEN c = gel(v,i);
    if (i > 1) c = gmul2n(c, (i-1)<<1);
    gel(w,i) = odd(i)? c: gneg(c);
  }
  return w;
}
/* \int (4z)^j given \int z^j */
static GEN
twistmoment_4(GEN v)
{
  long i, l;
  GEN w = cgetg_copy(v, &l);
  for (i = 1; i < l; i++)
  {
    GEN c = gel(v,i);
    if (i > 1) c = gmul2n(c, (i-1)<<1);
    gel(w,i) = c;
  }
  return w;
}
/* W an mspadic, phi eigensymbol, p \nmid D. Return C(x) mod FilM */
GEN
mspadicmoments(GEN W, GEN PHI, long D)
{
  pari_sp av = avma;
  long na, ia, b, lphi, aD = labs(D), pp, p, k, n, vden;
  GEN Wp, Dact, vL, v, C, pn, phi;
  struct m_act S;
  hashtable *H;

  checkmspadic(W);
  Wp = mspadic_get_Wp(W);
  p = mspadic_get_p(W);
  k = mspadic_get_weight(W);
  n = mspadic_get_n(W);
  C = mspadic_get_C(W);
  if (typ(PHI) != t_COL || lg(PHI) != 4 || typ(gel(PHI,1)) != t_VEC)
    PHI = mstooms(W, PHI);
  vden = itos( gel(PHI,2) );
  phi = gel(PHI,1); lphi = lg(phi);
  if (p == 2) { na = 2; pp = 4; }
  else        { na = p-1; pp = p; }
  pn = powuu(p, n + vden);

  S.p = p;
  S.k = k;
  S.q = pn;
  S.dim = n+k-1;
  S.act = &moments_act;
  H = Gl2act_cache(ms_get_nbgen(Wp));
  if (D == 1) Dact = NULL;
  else
  {
    GEN gaD = utoi(aD), Dk = Fp_pows(stoi(D), 2-k, pn);
    if (!sisfundamental(D)) pari_err_TYPE("mspadicmoments", stoi(D));
    if (D % p == 0) pari_err_DOMAIN("mspadicmoments","p","|", stoi(D), utoi(p));
    Dact = cgetg(aD, t_VEC);
    for (b = 1; b < aD; b++)
    {
      GEN z = NULL;
      long s = kross(D, b);
      if (s)
      {
        pari_sp av2 = avma;
        GEN d;
        z = moments_act_i(&S, mkmat22(gaD,utoipos(b), gen_0,gaD));
        d = s > 0? Dk: Fp_neg(Dk, pn);
        z = equali1(d)? gerepilecopy(av2, z)
                      : gerepileupto(av2, FpM_Fp_mul(z, d, pn));
      }
      gel(Dact,b) = z;
    }
  }
  vL = cgetg(na+1,t_VEC);
  /* first pass to precompute log(paths), preload matrices and allow GC later */
  for (ia = 1; ia <= na; ia++)
  {
    GEN path, La;
    long a = (p == 2 && ia == 2)? -1: ia;
    if (Dact)
    { /* twist by D */
      La = cgetg(aD, t_VEC);
      for (b = 1; b < aD; b++)
      {
        GEN Actb = gel(Dact,b);
        if (!Actb) continue;
        /* oo -> a/pp + b/|D|*/
        path = mkmat22(gen_1, addii(mulss(a, aD), muluu(pp, b)),
                       gen_0, muluu(pp, aD));
        gel(La,b) = M2_logf(Wp,path,NULL);
        ZGl2QC_preload(&S, gel(La,b), H);
      }
    }
    else
    {
      path = mkmat22(gen_1,stoi(a), gen_0, utoipos(pp));
      La = M2_logf(Wp,path,NULL);
      ZGl2QC_preload(&S, La, H);
    }
    gel(vL,ia) = La;
  }
  v = cgetg(na+1,t_VEC);
  /* second pass, with GC */
  for (ia = 1; ia <= na; ia++)
  {
    pari_sp av2 = avma;
    GEN vca, Ca = gel(C,ia), La = gel(vL,ia), va = cgetg(lphi, t_VEC);
    long i;
    if (!Dact) vca = omseval_int(&S, phi, La, H);
    else
    { /* twist by D */
      vca = cgetg(lphi,t_VEC);
      for (b = 1; b < aD; b++)
      {
        GEN T, Actb = gel(Dact,b);
        if (!Actb) continue;
        T = omseval_int(&S, phi, gel(La,b), H);
        for (i = 1; i < lphi; i++)
        {
          GEN z = FpM_FpC_mul(Actb, gel(T,i), pn);
          gel(vca,i) = b==1? z: ZC_add(gel(vca,i), z);
        }
      }
    }
    if (p != 2)
    { for (i=1; i<lphi; i++) gel(va,i) = FpVV_dotproduct(Ca,gel(vca,i),pn); }
    else if (ia == 1) /* \tilde{a} = 1 */
    { for (i=1; i<lphi; i++) gel(va,i) = twistmoment_4(gel(vca,i)); }
    else /* \tilde{a} = -1 */
    { for (i=1; i<lphi; i++) gel(va,i) = twistmoment_m4(gel(vca,i)); }
    gel(v,ia) = gerepilecopy(av2, va);
  }
  return gerepilecopy(av, mkvec3(v, gel(PHI,3), mkvecsmall4(p,n+vden,n,D)));
}
static void
checkoms(GEN v)
{
  if (typ(v) != t_VEC || lg(v) != 4 || typ(gel(v,1)) != t_VEC
      || typ(gel(v,3))!=t_VECSMALL)
    pari_err_TYPE("checkoms [apply mspadicmoments]", v);
}
static long
oms_get_p(GEN oms) { return gel(oms,3)[1]; }
static long
oms_get_n(GEN oms) { return gel(oms,3)[2]; }
static long
oms_get_n0(GEN oms) { return gel(oms,3)[3]; }
static long
oms_get_D(GEN oms) { return gel(oms,3)[4]; }
static int
oms_is_supersingular(GEN oms) { GEN v = gel(oms,1); return lg(gel(v,1)) == 3; }

/* sum(j = 1, n, (-1)^(j+1)/j * x^j) */
static GEN
log1x(long n)
{
  long i, l = n+3;
  GEN v = cgetg(l, t_POL);
  v[1] = evalvarn(0)|evalsigne(1); gel(v,2) = gen_0;
  for (i = 3; i < l; i++) gel(v,i) = ginv(stoi(odd(i)? i-2: 2-i));
  return v;
}

/* S = (1+x)^zk log(1+x)^logj (mod x^(n+1)) */
static GEN
xlog1x(long n, long zk, long logj, long *pteich)
{
  GEN S = logj? RgXn_powu_i(log1x(n), logj, n+1): NULL;
  if (zk)
  {
    GEN L = deg1pol_shallow(gen_1, gen_1, 0); /* x+1 */
    *pteich += zk;
    if (zk < 0) { L = RgXn_inv(L,n+1); zk = -zk; }
    if (zk != 1) L = RgXn_powu_i(L, zk, n+1);
    S = S? RgXn_mul(S, L, n+1): L;
  }
  return S;
}

/* oms from mspadicmoments; integrate teichmuller^i * S(x) [S = NULL: 1]*/
static GEN
mspadicint(GEN oms, long teichi, GEN S)
{
  pari_sp av = avma;
  long p = oms_get_p(oms), n = oms_get_n(oms), n0 = oms_get_n0(oms);
  GEN vT = gel(oms,1), alpha = gel(oms,2), gp = utoipos(p);
  long loss = S? Z_lval(Q_denom(S), p): 0;
  long nfinal = minss(n-loss, n0);
  long i, la, l = lg(gel(vT,1));
  GEN res = cgetg(l, t_COL), teich = NULL;

  if (S) S = RgX_to_RgC(S,lg(gmael(vT,1,1))-1);
  if (p == 2)
  {
    la = 3; /* corresponds to [1,-1] */
    teichi &= 1;
  }
  else
  {
    la = p; /* corresponds to [1,2,...,p-1] */
    teichi = smodss(teichi, p-1);
    if (teichi) teich = teichmullerinit(p, n);
  }
  for (i=1; i<l; i++)
  {
    pari_sp av2 = avma;
    GEN s = gen_0;
    long ia;
    for (ia = 1; ia < la; ia++)
    { /* Ta[j+1] correct mod p^n */
      GEN Ta = gmael(vT,ia,i), v = S? RgV_dotproduct(Ta, S): gel(Ta,1);
      if (teichi && ia != 1)
      {
        if (p != 2)
          v = gmul(v, gel(teich, Fl_powu(ia,teichi,p)));
        else
          if (teichi) v = gneg(v);
      }
      s = gadd(s, v);
    }
    s = gadd(s, zeropadic(gp,nfinal));
    gel(res,i) = gerepileupto(av2, s);
  }
  return gerepileupto(av, gmul(alpha, res));
}
/* integrate P = polynomial in log(x); vlog[j+1] = mspadicint(0,log(1+x)^j) */
static GEN
mspadicint_RgXlog(GEN P, GEN vlog)
{
  long i, d = degpol(P);
  GEN s = gmul(gel(P,2), gel(vlog,1));
  for (i = 1; i <= d; i++) s = gadd(s, gmul(gel(P,i+2), gel(vlog,i+1)));
  return s;
};

/* oms from mspadicmoments */
GEN
mspadicseries(GEN oms, long teichi)
{
  pari_sp av = avma;
  GEN S, L, X, vlog, s, s2, u, logu, bin;
  long j, p, m, n, step, stop;
  checkoms(oms);
  n = oms_get_n0(oms);
  if (n < 1)
  {
    s = zeroser(0,0);
    if (oms_is_supersingular(oms)) s = mkvec2(s,s);
    return gerepilecopy(av, s);
  }
  p = oms_get_p(oms);
  vlog = cgetg(n+1, t_VEC);
  step = p == 2? 2: 1;
  stop = 0;
  S = NULL;
  L = log1x(n);
  for (j = 0; j < n; j++)
  {
    if (j) stop += step + u_lval(j,p); /* = step*j + v_p(j!) */
    if (stop >= n) break;
    /* S = log(1+x)^j */
    gel(vlog,j+1) = mspadicint(oms,teichi,S);
    S = S? RgXn_mul(S, L, n+1): L;
  }
  m = j;
  u = utoipos(p == 2? 5: 1+p);
  logu = glog(cvtop(u, utoipos(p), 4*m), 0);
  X = gdiv(pol_x(0), logu);
  s = cgetg(m+1, t_VEC);
  s2 = oms_is_supersingular(oms)? cgetg(m+1, t_VEC): NULL;
  bin = pol_1(0);
  for (j = 0; j < m; j++)
  { /* bin = binomial(x/log(1+p+O(p^(4*n))), j) mod x^m */
    GEN a, v = mspadicint_RgXlog(bin, vlog);
    int done = 1;
    gel(s,j+1) = a = gel(v,1);
    if (!gequal0(a) || valp(a) > 0) done = 0; else setlg(s,j+1);
    if (s2)
    {
      gel(s2,j+1) = a = gel(v,2);
      if (!gequal0(a) || valp(a) > 0) done = 0; else setlg(s2,j+1);
    }
    if (done || j == m-1) break;
    bin = RgXn_mul(bin, gdivgs(gsubgs(X, j), j+1), m);
  }
  s = RgV_to_ser(s,0,lg(s)+1);
  if (s2) { s2 = RgV_to_ser(s2,0,lg(s2)+1); s = mkvec2(s, s2); }
  if (kross(oms_get_D(oms), p) >= 0) return gerepilecopy(av, s);
  return gerepileupto(av, gneg(s));
}
void
mspadic_parse_chi(GEN s, GEN *s1, GEN *s2)
{
  if (!s) *s1 = *s2 = gen_0;
  else switch(typ(s))
  {
    case t_INT: *s1 = *s2 = s; break;
    case t_VEC:
      if (lg(s) == 3)
      {
        *s1 = gel(s,1);
        *s2 = gel(s,2);
        if (typ(*s1) == t_INT && typ(*s2) == t_INT) break;
      }
    default: pari_err_TYPE("mspadicL",s);
             *s1 = *s2 = NULL;
  }
}
/* oms from mspadicmoments
 * r-th derivative of L(f,chi^s,psi) in direction <chi>
   - s \in Z_p \times \Z/(p-1)\Z, s-> chi^s=<\chi>^s_1 omega^s_2)
   - Z -> Z_p \times \Z/(p-1)\Z par s-> (s, s mod p-1).
 */
GEN
mspadicL(GEN oms, GEN s, long r)
{
  pari_sp av = avma;
  GEN s1, s2, z, S;
  long p, n, teich;
  checkoms(oms);
  p = oms_get_p(oms);
  n = oms_get_n(oms);
  mspadic_parse_chi(s, &s1,&s2);
  teich = umodiu(subii(s2,s1), p==2? 2: p-1);
  S = xlog1x(n, itos(s1), r, &teich);
  z = mspadicint(oms, teich, S);
  if (lg(z) == 2) z = gel(z,1);
  if (kross(oms_get_D(oms), p) < 0) z = gneg(z);
  return gerepilecopy(av, z);
}

/****************************************************************************/

struct siegel
{
  GEN V, Ast;
  long N; /* level */
  long oo; /* index of the [oo,0] path */
  long k1, k2; /* two distinguished indices */
  long n; /* #W, W = initial segment [in siegelstepC] already normalized */
};

static void
siegel_init(struct siegel *C, GEN M)
{
  GEN CPI, CP, MM, V, W, Ast;
  GEN m = gel(M,11), M2 = gel(M,2), S = msN_get_section(M);
  GEN E2fromE1 = msN_get_E2fromE1(M);
  long m0 = lg(M2)-1;
  GEN E2  = vecslice(M2, m[1]+1, m[2]);/* E2 */
  GEN E1T = vecslice(M2, m[3]+1, m0); /* E1,T2,T31 */
  GEN L = shallowconcat(E1T, E2);
  long i, l = lg(L), n = lg(E1T)-1, lE = lg(E2);

  Ast = cgetg(l, t_VECSMALL);
  for (i = 1; i < lE; ++i)
  {
    long j = E2fromE1_c(gel(E2fromE1,i));
    Ast[n+i] = j;
    Ast[j] = n+i;
  }
  for (; i<=n; ++i) Ast[i] = i;
  MM = cgetg (l,t_VEC);

  for (i = 1; i < l; i++)
  {
    GEN c = gel(S, L[i]);
    long c12, c22, c21 = ucoeff(c,2,1);
    if (!c21) { gel(MM,i) = gen_0; continue; }
    c22 = ucoeff(c,2,2);
    if (!c22) { gel(MM,i) = gen_m1; continue; }
    c12 = ucoeff(c,1,2);
    gel(MM,i) = gdivgs(stoi(c12), c22); /* right extremity > 0 */
  }
  CP = indexsort(MM);
  CPI = cgetg(l, t_VECSMALL);
  V = cgetg(l, t_VEC);
  W = cgetg(l, t_VECSMALL);
  for (i = 1; i < l; ++i)
  {
    gel(V,i) = mat2_to_ZM(gel(S, L[CP[i]]));
    CPI[CP[i]] = i;
  }
  for (i = 1; i < l; ++i) W[CPI[i]] = CPI[Ast[i]];
  C->V = V;
  C->Ast = W;
  C->n = 0;
  C->oo = 2;
  C->N = ms_get_N(M);
}

static double
ZMV_size(GEN v)
{
  long i, l = lg(v);
  GEN z = cgetg(l, t_VECSMALL);
  for (i = 1; i < l; i++) z[i] = gexpo(gel(v,i));
  return ((double)zv_sum(z)) / (4*(l-1));
}

/* apply permutation perm to struct S. Don't follow k1,k2 */
static void
siegel_perm0(struct siegel *S, GEN perm)
{
  long i, l = lg(S->V);
  GEN V2 = cgetg(l, t_VEC), Ast2 = cgetg(l, t_VECSMALL);
  GEN V = S->V, Ast = S->Ast;

  for (i = 1; i < l; i++) gel(V2,perm[i]) = gel(V,i);
  for (i = 1; i < l; i++) Ast2[perm[i]] = perm[Ast[i]];
  S->oo = perm[S->oo];
  S->Ast = Ast2;
  S->V = V2;
}
/* apply permutation perm to full struct S */
static void
siegel_perm(struct siegel *S, GEN perm)
{
  siegel_perm0(S, perm);
  S->k1 = perm[S->k1];
  S->k2 = perm[S->k2];
}
/* cyclic permutation of lg = l-1 moving a -> 1, a+1 -> 2, etc.  */
static GEN
rotate_perm(long l, long a)
{
  GEN p = cgetg(l, t_VECSMALL);
  long i, j = 1;
  for (i = a; i < l; i++) p[i] = j++;
  for (i = 1; i < a; i++) p[i] = j++;
  return p;
}

/* a1 < c1 <= a2 < c2*/
static GEN
basic_op_perm(long l, long a1, long a2, long c1, long c2)
{
  GEN p = cgetg(l, t_VECSMALL);
  long i, j = 1;
  p[a1] = j++;
  for (i = c1; i < a2; i++)   p[i] = j++;
  for (i = a1+1; i < c1; i++) p[i] = j++;
  p[a2] = j++;
  for (i = c2; i < l; i++)    p[i] = j++;
  for (i = 1; i < a1; i++)    p[i] = j++;
  for (i = a2+1; i < c2; i++) p[i] = j++;
  return p;
}
static GEN
basic_op_perm_elliptic(long l, long a1)
{
  GEN p = cgetg(l, t_VECSMALL);
  long i, j = 1;
  p[a1] = j++;
  for (i = 1; i < a1; i++)   p[i] = j++;
  for (i = a1+1; i < l; i++) p[i] = j++;
  return p;
}
static GEN
ZM2_rev(GEN T) { return mkmat2(gel(T,2), ZC_neg(gel(T,1))); }

/* In place, V = vector of consecutive paths, between x <= y.
 * V[x..y-1] <- g*V[x..y-1] */
static void
path_vec_mul(GEN V, long x, long y, GEN g)
{
  long j;
  GEN M;
  if (x == y) return;
  M = gel(V,x); gel(V,x) = ZM_mul(g,M);
  for (j = x+1; j < y; j++) /* V[j] <- g*V[j], optimized */
  {
    GEN Mnext = gel(V,j); /* Mnext[,1] = M[,2] */
    GEN gM = gel(V,j-1), u = gel(gM,2);
    if (!ZV_equal(gel(M,2), gel(Mnext,1))) u = ZC_neg(u);
    gel(V,j) = mkmat2(u, ZM_ZC_mul(g,gel(Mnext,2)));
    M = Mnext;
  }
}

static long prev(GEN V, long i) { return (i == 1)? lg(V)-1: i-1; }
static long next(GEN V, long i) { return (i == lg(V)-1)? 1: i+1; }
static GEN
ZM_det2(GEN u, GEN v)
{
  GEN a = gel(u,1), c = gel(u,2);
  GEN b = gel(v,1), d = gel(v,2); return subii(mulii(a,d), mulii(b,c));
}
static GEN
ZM2_det(GEN T) { return ZM_det2(gel(T,1),gel(T,2)); }
static void
fill1(GEN V, long a)
{
  long p = prev(V,a), n = next(V,a);
  GEN u = gmael(V,p,2), v = gmael(V,n,1);
  if (signe(ZM_det2(u,v)) < 0) v = ZC_neg(v);
  gel(V,a) = mkmat2(u, v);
}
/* a1 < a2 */
static void
fill2(GEN V, long a1, long a2)
{
  if (a2 != a1+1) { fill1(V,a1); fill1(V,a2); } /* non adjacent, reconnect */
  else /* parabolic */
  {
    long p = prev(V,a1), n = next(V,a2);
    GEN u, v, C = gmael(V,a1,2), mC = ZC_neg(C); /* = \pm V[a2][1] */
    u = gmael(V,p,2); v = (signe(ZM_det2(u,C)) < 0)? mC: C;
    gel(V,a1) = mkmat2(u,v);
    v = gmael(V,n,1); u = (signe(ZM_det2(C,v)) < 0)? mC: C;
    gel(V,a2) = mkmat2(u,v);
  }
}

/* DU = det(U), return g = T*U^(-1) or NULL if not in Gamma0(N); if N = 0,
 * only test whether g is integral */
static GEN
ZM2_div(GEN T, GEN U, GEN DU, long N)
{
  GEN a=gcoeff(U,1,1), b=gcoeff(U,1,2), c=gcoeff(U,2,1), d=gcoeff(U,2,2);
  GEN e=gcoeff(T,1,1), f=gcoeff(T,1,2), g=gcoeff(T,2,1), h=gcoeff(T,2,2);
  GEN A, B, C, D, r;

  C = dvmdii(subii(mulii(d,g), mulii(c,h)), DU, &r);
  if (r != gen_0 || (N && smodis(C,N))) return NULL;
  A = dvmdii(subii(mulii(d,e), mulii(c,f)), DU, &r);
  if (r != gen_0) return NULL;
  B = dvmdii(subii(mulii(a,f), mulii(b,e)), DU, &r);
  if (r != gen_0) return NULL;
  D = dvmdii(subii(mulii(a,h), mulii(g,b)), DU, &r);
  if (r != gen_0) return NULL;
  return mkmat22(A,B,C,D);
}

static GEN
get_g(struct siegel *S, long a1)
{
  long a2 = S->Ast[a1];
  GEN a = gel(S->V,a1), ar = ZM2_rev(gel(S->V,a2)), Dar = ZM2_det(ar);
  GEN g = ZM2_div(a, ar, Dar, S->N);
  if (!g)
  {
    GEN tau = mkmat22(gen_0,gen_m1, gen_1,gen_m1); /*[0,-1;1,-1]*/
    g = ZM2_div(ZM_mul(ar, tau), ar, Dar, 0);
  }
  return g;
}
/* input V = (X1 a X2 | X3 a^* X4) + Ast
 * a1 = index of a
 * a2 = index of a^*, inferred from a1. We must have a != a^*
 * c1 = first cut [ index of first path in X3 ]
 * c2 = second cut [ either in X4 or X1, index of first path ]
 * Assume a < a^* (cf Paranoia below): c1 or c2 must be in
 *    ]a,a^*], and the other in the "complement" ]a^*,a] */
static void
basic_op(struct siegel *S, long a1, long c1, long c2)
{
  long l = lg(S->V), a2 = S->Ast[a1];
  GEN g;

  if (a1 == a2)
  { /* a = a^* */
    g = get_g(S, a1);
    path_vec_mul(S->V, a1+1, l, g);
    siegel_perm(S, basic_op_perm_elliptic(l, a1));
    /* fill the hole left at a1, reconnect the path */
    fill1(S->V, a1); return;
  }

  /* Paranoia: (a,a^*) conjugate, call 'a' the first one */
  if (a2 < a1) lswap(a1,a2);
  /* Now a1 < a2 */
  if (c1 <= a1 || c1 > a2) lswap(c1,c2); /* ensure a1 < c1 <= a2 */
  if (c2 < a1)
  { /* if cut c2 is in X1 = X11|X12, rotate to obtain
       (a X2 | X3 a^* X4 X11|X12): then a1 = 1 */
    GEN p = rotate_perm(l, a1);
    siegel_perm(S, p);
    a1 = 1; /* = p[a1] */
    a2 = S->Ast[1]; /* > a1 */
    c1 = p[c1];
    c2 = p[c2];
  }
  /* Now a1 < c1 <= a2 < c2; a != a^* */
  g = get_g(S, a1);
  if (S->oo >= c1 && S->oo < c2) /* W inside [c1..c2[ */
  { /* c2 -> c1 excluding a1 */
    GEN gi = SL2_inv(g); /* g a^* = a; gi a = a^* */
    path_vec_mul(S->V, 1, a1, gi);
    path_vec_mul(S->V, a1+1, c1, gi);
    path_vec_mul(S->V, c2, l, gi);
  }
  else
  { /* c1 -> c2 excluding a2 */
    path_vec_mul(S->V, c1, a2, g);
    path_vec_mul(S->V, a2+1, c2, g);
  }
  siegel_perm(S, basic_op_perm(l, a1,a2, c1,c2));
  /* fill the holes left at a1,a2, reconnect the path */
  fill2(S->V, a1, a2);
}
/* a = a^* (elliptic case) */
static void
basic_op_elliptic(struct siegel *S, long a1)
{
  long l = lg(S->V);
  GEN g = get_g(S, a1);
  path_vec_mul(S->V, a1+1, l, g);
  siegel_perm(S, basic_op_perm_elliptic(l, a1));
  /* fill the hole left at a1 (now at 1), reconnect the path */
  fill1(S->V, 1);
}

/* input V = W X a b Y a^* Z b^* T, W already normalized
 * X = [n+1, k1-1], Y = [k2+1, Ast[k1]-1],
 * Z = [Ast[k1]+1, Ast[k2]-1], T = [Ast[k2]+1, oo].
 * Assume that X doesn't start by c c^* or a b a^* b^*. */
static void
siegelstep(struct siegel *S)
{
  if (S->Ast[S->k1] == S->k1)
  {
    basic_op_elliptic(S, S->k1);
    S->n++;
  }
  else if (S->Ast[S->k1] == S->k1+1)
  {
    basic_op(S, S->k1, S->Ast[S->k1], 1); /* 1: W starts there */
    S->n += 2;
  }
  else
  {
    basic_op(S, S->k2, S->Ast[S->k1], 1); /* 1: W starts there */
    basic_op(S, S->k1, S->k2, S->Ast[S->k2]);
    basic_op(S, S->Ast[S->k2], S->k2, S->Ast[S->k1]);
    basic_op(S, S->k1, S->Ast[S->k1], S->Ast[S->k2]);
    S->n += 4;
  }
}

/* normalize hyperbolic polygon */
static void
mssiegel(struct siegel *S)
{
  pari_sp av = avma;
  long k, t, nv;
#ifdef COUNT
  long countset[16];
  for (k = 0; k < 16; k++) countset[k] = 0;
#endif

  nv = lg(S->V)-1;
  if (DEBUGLEVEL>1) err_printf("nv = %ld, expo = %.2f\n", nv,ZMV_size(S->V));
  t = 0;
  while (S->n < nv)
  {
    if (S->Ast[S->n+1] == S->n+1) { S->n++; continue; }
    if (S->Ast[S->n+1] == S->n+2) { S->n += 2; continue; }
    if (S->Ast[S->n+1] == S->n+3 && S->Ast[S->n+2] == S->n+4) { S->n += 4; continue; }
    k = nv;
    while (k > S->n)
    {
      if (S->Ast[k] == k) { k--; continue; }
      if (S->Ast[k] == k-1) { k -= 2; continue; }
      if (S->Ast[k] == k-2 && S->Ast[k-1] == k-3) { k -= 4; continue; }
      break;
    }
    if (k != nv) { siegel_perm0(S, rotate_perm(nv+1, k+1)); S->n += nv-k; }

    for (k = S->n+1; k <= nv; k++)
      if (S->Ast[k] <= k) { t = S->Ast[k]; break; }
    S->k1 = t;
    S->k2 = t+1;
#ifdef COUNT
    countset[ ((S->k1-1 == S->n)
              | ((S->k2 == S->Ast[S->k1]-1) << 1)
              | ((S->Ast[S->k1] == S->Ast[S->k2]-1) << 2)
              | ((S->Ast[S->k2] == nv) << 3)) ]++;
#endif
    siegelstep(S);
    if (gc_needed(av,2))
    {
      if(DEBUGMEM>1) pari_warn(warnmem,"mspolygon, n = %ld",S->n);
      gerepileall(av, 2, &S->V, &S->Ast);
    }
  }
  if (DEBUGLEVEL>1) err_printf("expo = %.2f\n", ZMV_size(S->V));
#ifdef COUNT
  for (k = 0; k < 16; k++)
    err_printf("%3ld: %6ld\n", k, countset[k]);
#endif
}

/* return a vector of char */
static GEN
Ast2v(GEN Ast)
{
  long j = 0, k, l = lg(Ast);
  GEN v = const_vec(l-1, NULL);
  for (k=1; k < l; k++)
  {
    char *sj;
    if (gel(v,k)) continue;
    j++;
    sj = stack_sprintf("$%ld$", j);
    gel(v,k) = (GEN)sj;
    if (Ast[k] != k) gel(v,Ast[k]) = (GEN)stack_sprintf("$%ld^*$", j);
  }
  return v;
};
static GEN
M2Q(GEN p) { GEN c = gel(p,1); return gdiv(gel(c,1), gel(c,2)); }

static void
maybe_decorate(pari_str *s, GEN Ast, GEN G, long k, double c)
{
  GEN g;
  if (Ast[k] != k) return;
  g = ZM_sqr(gel(G,k));
  if (gequal1(g) || gequalm1(g)) /* \pm Id */
    str_printf(s, " node [midway] {$\\circ$}\n");
  else
    str_printf(s, ";\n \\draw (start) arc (180:60:%.4f) node {$\\bullet$} arc (120:0:%.4f)\n",2*c/3,2*c/3);
}
static GEN
polygon2tex(GEN V, GEN Ast, GEN G)
{
  pari_sp av = avma;
  GEN v = Ast2v(Ast);
  pari_str s;
  long j, l = lg(V), flag;
  double c;
  str_init(&s, 1);
  flag = (l <= 16);
  str_puts(&s, "\n\\begin{tikzpicture}[scale=10]\n");
  str_puts(&s, "\\draw (0,0.5)--(0,0) node [very near start, right] {$1^*$} node [below] {$0$}");
  for (j=4; j < l; j++)
  {
    GEN a = M2Q(gel(V,j-1)), b = M2Q(gel(V,j));
    c = gtodouble(gsub(b,a)) / 2;

    str_printf(&s, "node (start) {} arc (180:0:%.4f)\n", c);
    if (flag)
    {
      long sb = itos(numer_i(b));
      long sa = itos(denom_i(b));
      str_printf(&s, "node [midway, above] {%s} node [below]{$\\frac{%ld}{%ld}$}\n",
                 (char*)gel(v,j-1), sb, sa);
    }
    maybe_decorate(&s,Ast,G,j-1,c);
  }
  c = (1- gtodouble(M2Q(gel(V,l-1)))) / 2;
  str_printf(&s, "node (start) {} arc (180:0:%.4f)\n", c);
  if (flag) str_printf(&s, "node [midway, above] {%s}", (char*)gel(v,l-1));
  maybe_decorate(&s,Ast,G,l-1,c);
  str_printf(&s,"node [below] {$1$} -- (1,0.5) node [very near end, left] {$1$};");
  str_printf(&s, "\n\\end{tikzpicture}");
  return gerepileuptoleaf(av, strtoGENstr(s.string));
}

static GEN
circle2tex(GEN Ast, GEN G)
{
  pari_sp av = avma;
  GEN v = Ast2v(Ast);
  pari_str s;
  long u, n = lg(Ast)-1;
  const double ang = 360./n;

  if (n > 30)
  {
    v = const_vec(n, (GEN)"");
    gel(v,1) = (GEN)"$(1,\\infty)$";
  }
  str_init(&s, 1);
  str_puts(&s, "\n\\begingroup\n\
  \\def\\geo#1#2{(#2:1) arc (90+#2:270+#1:{tan((#2-#1)/2)})}\n\
  \\def\\sgeo#1#2{(#2:1) -- (#1:1)}\n\
  \\def\\unarc#1#2#3{({#1 * #3}:1.2) node {#2}}\n\
  \\def\\cell#1#2{({#1 * #2}:0.95) circle(0.05)}\n\
  \\def\\link#1#2#3#4#5{\\unarc{#1}{#2}{#5}\\geo{#1*#5}{#3*#5}\\unarc{#3}{#4}{#5}}\n\
  \\def\\slink#1#2#3#4#5{\\unarc{#1}{#2}{#5}\\sgeo{#1*#5}{#3*#5}\\unarc{#3}{#4}{#5}}");

  str_puts(&s, "\n\\begin{tikzpicture}[scale=4]\n");
  str_puts(&s, "\\draw (0, 0) circle(1);\n");
  for (u=1; u <= n; u++)
  {
    if (Ast[u] == u)
    {
      str_printf(&s,"\\draw\\unarc{%ld}{%s}{%.4f}; \\draw\\cell{%ld}{%.4f};\n",
                 u, v[u], ang, u, ang);
      if (ZM_isscalar(gpowgs(gel(G,u),3), NULL))
        str_printf(&s,"\\fill \\cell{%ld}{%.4f};\n", u, ang);
    }
    else if(Ast[u] > u)
      str_printf(&s, "\\draw \\%slink {%ld}{%s}{%ld}{%s}{%.4f};\n",
                     Ast[u]-u==n/2? "s": "", u, v[u], Ast[u], v[Ast[u]], ang);
  }
  str_printf(&s, "\\end{tikzpicture}\\endgroup");
  return gerepileuptoleaf(av, strtoGENstr(s.string));
}

GEN
mspolygon(GEN M, long flag)
{
  pari_sp av = avma;
  struct siegel T;
  long i, l;
  GEN v, G, msN;
  if (typ(M) == t_INT)
  {
    long N = itos(M);
    if (N <= 0) pari_err_DOMAIN("msinit","N", "<=", gen_0,M);
    msN = msinit_N(N);
  }
  else { checkms(M); msN = get_msN(M); }
  if (flag < 0 || flag > 3) pari_err_FLAG("mspolygon");
  if (ms_get_N(msN) == 1)
  {
    GEN S = mkS();
    T.V = mkvec2(matid(2), S);
    T.Ast = mkvecsmall2(1,2);
    G = mkvec2(S, mkTAU());
  }
  else
  {
    siegel_init(&T, msN);
    l = lg(T.V);
    if (flag & 1)
    {
      long oo2 = 0;
      mssiegel(&T);
      for (i = 1; i < l; i++)
      {
        GEN c = gel(T.V, i);
        GEN c22 = gcoeff(c,2,2); if (!signe(c22)) { oo2 = i; break; }
      }
      if (!oo2) pari_err_BUG("mspolygon");
      siegel_perm0(&T, rotate_perm(l, oo2));
    }
    G = cgetg(l, t_VEC);
    for (i = 1; i < l; i++) gel(G,i) = get_g(&T, i);
  }
  if (flag & 2)
    v = mkvec5(T.V, T.Ast, G, polygon2tex(T.V,T.Ast,G), circle2tex(T.Ast,G));
  else
    v = mkvec3(T.V, T.Ast, G);
  return gerepilecopy(av, v);
}

#if 0
static int
iselliptic(GEN Ast, long i) { return i == Ast[i]; }
static int
isparabolic(GEN Ast, long i)
{ long i2 = Ast[i]; return (i2 == i+1 || i2 == i-1); }
#endif

/* M from msinit, F QM maximal rank */
GEN
mslattice(GEN M, GEN F)
{
  pari_sp av = avma;
  long i, ivB, j, k, l, lF;
  GEN D, U, G, A, vB, m, d;

  checkms(M);
  if (!F) F = gel(mscuspidal(M, 0), 1);
  else
  {
    if (is_Qevproj(F)) F = gel(F,1);
    if (typ(F) != t_MAT) pari_err_TYPE("mslattice",F);
  }
  lF = lg(F); if (lF == 1) return cgetg(1, t_MAT);
  D = mspolygon(M,0);
  k = msk_get_weight(M);
  F = vec_Q_primpart(F);
  if (typ(F)!=t_MAT || !RgM_is_ZM(F)) pari_err_TYPE("mslattice",F);
  G = gel(D,3); l = lg(G);
  A = gel(D,2);
  vB = cgetg(l, t_COL);
  d = mkcol2(gen_0,gen_1);
  m = mkmat2(d, d);
  for (i = ivB = 1; i < l; i++)
  {
    GEN B, vb, g = gel(G,i);
    if (A[i] < i) continue;
    gel(m,2) = SL2_inv2(g);
    vb = mseval(M, F, m);
    if (k == 2) B = vb;
    else
    {
      long lB;
      B = RgXV_to_RgM(vb, k-1);
      /* add coboundaries */
      B = shallowconcat(B, RgM_Rg_sub(RgX_act_Gl2Q(g, k), gen_1));
      /* beware: the basis for RgX_act_Gl2Q is (X^(k-2),...,Y^(k-2)) */
      lB = lg(B);
      for (j = 1; j < lB; j++) gel(B,j) = vecreverse(gel(B,j));
    }
    gel(vB, ivB++) = B;
  }
  setlg(vB, ivB);
  vB = shallowmatconcat(vB);
  if (ZM_equal0(vB)) return gerepilecopy(av, F);

  (void)QM_ImQ_hnfall(vB, &U, 0);
  if (k > 2) U = rowslice(U, 1, lgcols(U)-k); /* remove coboundary part */
  U = Q_remove_denom(U, &d);
  F = ZM_hnf(ZM_mul(F, U));
  if (d) F = RgM_Rg_div(F, d);
  return gerepileupto(av, F);
}

/**** Petersson scalar product ****/

/* oo -> g^(-1) oo */
static GEN
cocycle(GEN g)
{ return mkmat22(gen_1, gcoeff(g,2,2), gen_0, negi(gcoeff(g,2,1))); }

/* C = vecbinome(k-2) */
static GEN
bil(GEN P, GEN Q, GEN C)
{
  long i, n = lg(C)-2; /* k - 2 */
  GEN s;
  if (!n) return gmul(P,Q);
  if (typ(P) != t_POL) P = scalarpol_shallow(P,0);
  if (typ(Q) != t_POL) Q = scalarpol_shallow(Q,0);
  s = gen_0;
  for (i = 0; i <= n; i++)
  {
    GEN t = gdiv(gmul(RgX_coeff(P,i), RgX_coeff(Q, n-i)), gel(C,i+1));
    s = odd(i)? gsub(s, t): gadd(s, t);
  }
  return s;
}

static void
mspetersson_i(GEN W, GEN F, GEN G, GEN *pvf, GEN *pvg, GEN *pC)
{
  GEN WN = get_msN(W), annT2, annT31, section, c, vf, vg;
  long i, n1, n2, n3;

  annT2 = msN_get_annT2(WN);
  annT31 = msN_get_annT31(WN);
  section = msN_get_section(WN);

  if (ms_get_N(WN) == 1)
  {
    vf = cgetg(3, t_VEC);
    vg = cgetg(3, t_VEC);
    gel(vf,1) = mseval(W, F, gel(section,1));
    gel(vf,2) = gneg(gel(vf,1));
    n1 = 0;
  }
  else
  {
    GEN singlerel = msN_get_singlerel(WN);
    GEN gen = msN_get_genindex(WN);
    long l = lg(gen);
    vf = cgetg(l, t_VEC);
    vg = cgetg(l, t_VEC); /* generators of Delta ordered as E1,T2,T31 */
    for (i = 1; i < l; i++) gel(vf, i) = mseval(W, F, gel(section,gen[i]));
    n1 = ms_get_nbE1(WN); /* E1 */
    for (i = 1; i <= n1; i++)
    {
      c = cocycle(gcoeff(gel(singlerel,i),2,1));
      gel(vg, i) = mseval(W, G, c);
    }
  }
  n2 = lg(annT2)-1; /* T2 */
  for (i = 1; i <= n2; i++)
  {
    c = cocycle(gcoeff(gel(annT2,i), 2,1));
    gel(vg, i+n1) = gmul2n(mseval(W, G, c), -1);
  }
  n3 = lg(annT31)-1; /* T31 */
  for (i = 1; i <= n3; i++)
  {
    GEN f;
    c = cocycle(gcoeff(gel(annT31,i), 2,1));
    f = mseval(W, G, c);
    c = cocycle(gcoeff(gel(annT31,i), 3,1));
    gel(vg, i+n1+n2) = gdivgs(gadd(f, mseval(W, G, c)), 3);
  }
  *pC = vecbinome(msk_get_weight(W) - 2);
  *pvf = vf;
  *pvg = vg;
}

/* Petersson product on Hom_G(Delta_0, V_k) */
GEN
mspetersson(GEN W, GEN F, GEN G)
{
  pari_sp av = avma;
  GEN vf, vg, C;
  long k, l, tG, tF;
  checkms(W);
  if (!F) F = matid(msdim(W));
  if (!G) G = F;
  tF = typ(F);
  tG = typ(G);
  if (tF == t_MAT && tG != t_MAT) pari_err_TYPE("mspetersson",G);
  if (tG == t_MAT && tF != t_MAT) pari_err_TYPE("mspetersson",F);
  mspetersson_i(W, F, G, &vf, &vg, &C);
  l = lg(vf);
  if (tF != t_MAT)
  { /* <F,G>, two symbols */
    GEN s = gen_0;
    for (k = 1; k < l; k++) s = gadd(s, bil(gel(vf,k), gel(vg,k), C));
    return gerepileupto(av, s);
  }
  else if (F != G)
  { /* <(f_1,...,f_m), (g_1,...,g_n)> */
    long iF, iG, lF = lg(F), lG = lg(G);
    GEN M = cgetg(lG, t_MAT);
    for (iG = 1; iG < lG; iG++)
    {
      GEN c = cgetg(lF, t_COL);
      gel(M,iG) = c;
      for (iF = 1; iF < lF; iF++)
      {
        GEN s = gen_0;
        for (k = 1; k < l; k++)
          s = gadd(s, bil(gmael(vf,k,iF), gmael(vg,k,iG), C));
        gel(c,iF) = s; /* M[iF,iG] = <F[iF], G[iG] > */
      }
    }
    return gerepilecopy(av, M);
  }
  else
  { /* <(f_1,...,f_n), (f_1,...,f_n)> */
    long iF, iG, n = lg(F)-1;
    GEN M = zeromatcopy(n,n);
    for (iG = 1; iG <= n; iG++)
      for (iF = iG+1; iF <= n; iF++)
      {
        GEN s = gen_0;
        for (k = 1; k < l; k++)
          s = gadd(s, bil(gmael(vf,k,iF), gmael(vg,k,iG), C));
        gcoeff(M,iF,iG) = s; /* <F[iF], F[iG] > */
        gcoeff(M,iG,iF) = gneg(s);
      }
    return gerepilecopy(av, M);
  }
}
