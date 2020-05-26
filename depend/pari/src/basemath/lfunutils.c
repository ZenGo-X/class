/* Copyright (C) 2015  The PARI group.

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
/**                 L-functions: Applications                      **/
/**                                                                **/
/********************************************************************/

#include "pari.h"
#include "paripriv.h"

static GEN
tag(GEN x, long t) { return mkvec2(mkvecsmall(t), x); }

/* v a t_VEC of length > 1 */
static int
is_tagged(GEN v)
{
  GEN T = gel(v,1);
  return (typ(T)==t_VEC && lg(T)==3 && typ(gel(T,1))==t_VECSMALL);
}
static void
checkldata(GEN ldata)
{
  GEN vga, w, N;
#if 0 /* assumed already checked and true */
  long l = lg(ldata);
  if (typ(ldata)!=t_VEC || l < 7 || l > 8 || !is_tagged(ldata))
    pari_err_TYPE("checkldata", ldata);
#endif
  vga = ldata_get_gammavec(ldata);
  if (typ(vga) != t_VEC) pari_err_TYPE("checkldata [gammavec]",vga);
  w = gel(ldata, 4); /* FIXME */
  switch(typ(w))
  {
    case t_INT: break;
    case t_VEC: if (lg(w) == 3 && typ(gel(w,1)) == t_INT) break;
    default: pari_err_TYPE("checkldata [weight]",w);
  }
  N = ldata_get_conductor(ldata);
  if (typ(N) != t_INT) pari_err_TYPE("checkldata [conductor]",N);
}

/* data may be either an object (polynomial, elliptic curve, etc...)
 * or a description vector [an,sd,Vga,k,conductor,rootno,{poles}]. */
GEN
lfuncreate(GEN data)
{
  long lx = lg(data);
  if (typ(data)==t_VEC && (lx == 7 || lx == 8))
  {
    GEN ldata;
    if (is_tagged(data)) ldata = gcopy(data);
    else
    { /* tag first component as t_LFUN_GENERIC */
      ldata = gcopy(data);
      gel(ldata, 1) = tag(gel(ldata,1), t_LFUN_GENERIC);
      if (typ(gel(ldata, 2))!=t_INT)
        gel(ldata, 2) = tag(gel(ldata,2), t_LFUN_GENERIC);
    }
    checkldata(ldata); return ldata;
  }
  return lfunmisc_to_ldata(data);
}

/********************************************************************/
/**                     Simple constructors                        **/
/********************************************************************/

static GEN
vecan_conj(GEN an, long n, long prec)
{
  GEN p1 = ldata_vecan(gel(an,1), n, prec);
  return typ(p1) == t_VEC? conj_i(p1): p1;
}

static GEN
vecan_mul(GEN an, long n, long prec)
{
  GEN p1 = ldata_vecan(gel(an,1), n, prec);
  GEN p2 = ldata_vecan(gel(an,2), n, prec);
  if (typ(p1) == t_VECSMALL) p1 = vecsmall_to_vec(p1);
  if (typ(p2) == t_VECSMALL) p2 = vecsmall_to_vec(p2);
  return dirmul(p1, p2);
}

static GEN
lfunconvol(GEN a1, GEN a2)
{ return tag(mkvec2(a1, a2), t_LFUN_MUL); }

static GEN
vecan_div(GEN an, long n, long prec)
{
  GEN p1 = ldata_vecan(gel(an,1), n, prec);
  GEN p2 = ldata_vecan(gel(an,2), n, prec);
  if (typ(p1) == t_VECSMALL) p1 = vecsmall_to_vec(p1);
  if (typ(p2) == t_VECSMALL) p2 = vecsmall_to_vec(p2);
  return dirdiv(p1, p2);
}

static GEN
lfunconvolinv(GEN a1, GEN a2)
{ return tag(mkvec2(a1,a2), t_LFUN_DIV); }

static GEN
lfunconj(GEN a1)
{ return tag(mkvec(a1), t_LFUN_CONJ); }

static GEN
lfuncombdual(GEN fun(GEN, GEN), GEN ldata1, GEN ldata2)
{
  GEN a1 = ldata_get_an(ldata1), a2 = ldata_get_an(ldata2);
  GEN b1 = ldata_get_dual(ldata1), b2 = ldata_get_dual(ldata2);
  if (typ(b1)==t_INT && typ(b2)==t_INT)
    return utoi(signe(b1) && signe(b2));
  else
  {
    if (typ(b1)==t_INT) b1 = signe(b1) ? lfunconj(a1): a1;
    if (typ(b2)==t_INT) b2 = signe(b2) ? lfunconj(a2): a2;
    return fun(b1, b2);
  }
}

static GEN
vecan_twist(GEN an, long n, long prec)
{
  GEN p1 = ldata_vecan(gel(an,1), n, prec);
  GEN p2 = ldata_vecan(gel(an,2), n, prec);
  long i;
  GEN V;
  if (typ(p1) == t_VECSMALL) p1 = vecsmall_to_vec(p1);
  if (typ(p2) == t_VECSMALL) p2 = vecsmall_to_vec(p2);
  V = cgetg(n+1, t_VEC);
  for(i = 1; i <= n ; i++)
    gel(V, i) = gmul(gel(p1, i), gel(p2, i));
  return V;
}

static GEN
lfunmulpoles(GEN ldata1, GEN ldata2, long bitprec)
{
  long k = ldata_get_k(ldata1), l, j;
  GEN r1 = ldata_get_residue(ldata1);
  GEN r2 = ldata_get_residue(ldata2), r;

  if (r1 && typ(r1) != t_VEC) r1 = mkvec(mkvec2(stoi(k), r1));
  if (r2 && typ(r2) != t_VEC) r2 = mkvec(mkvec2(stoi(k), r2));
  if (!r1)
  {
    if (!r2) return NULL;
    r1 = lfunrtopoles(r2);
  }
  else
  {
    r1 = lfunrtopoles(r1);
    if (r2) r1 = setunion(r1, lfunrtopoles(r2));
  }
  l = lg(r1); r = cgetg(l, t_VEC);
  for (j = 1; j < l; j++)
  {
    GEN be = gel(r1,j);
    GEN z1 = lfun(ldata1,be,bitprec), z2 = lfun(ldata2,be,bitprec);
    if (typ(z1) == t_SER && typ(z2) == t_SER)
    { /* pole of both, recompute to needed seriesprecision */
      long e = valp(z1) + valp(z2);
      GEN b = RgX_to_ser(deg1pol_shallow(gen_1, be, 0), 3-e);
      z1 = lfun(ldata1,b,bitprec);
      z2 = lfun(ldata2,b,bitprec);
    }
    gel(r,j) = mkvec2(be, gmul(z1, z2));
  }
  return r;
}

GEN
lfunmul(GEN ldata1, GEN ldata2, long bitprec)
{
  pari_sp ltop = avma;
  GEN r, N, Vga, eno, a1a2, b1b2, LD;
  long k;
  ldata1 = lfunmisc_to_ldata_shallow(ldata1);
  ldata2 = lfunmisc_to_ldata_shallow(ldata2);
  k = ldata_get_k(ldata1);
  if (ldata_get_k(ldata2) != k)
    pari_err_OP("lfunmul [weight]",ldata1, ldata2);
  r = lfunmulpoles(ldata1, ldata2, bitprec);
  N = gmul(ldata_get_conductor(ldata1), ldata_get_conductor(ldata2));
  Vga = shallowconcat(ldata_get_gammavec(ldata1), ldata_get_gammavec(ldata2));
  Vga = sort(Vga);
  eno = gmul(ldata_get_rootno(ldata1), ldata_get_rootno(ldata2));
  a1a2 = lfunconvol(ldata_get_an(ldata1), ldata_get_an(ldata2));
  b1b2 = lfuncombdual(lfunconvol, ldata1, ldata2);
  LD = mkvecn(7, a1a2, b1b2, Vga, stoi(k), N, eno, r);
  if (!r) setlg(LD,7);
  return gerepilecopy(ltop, LD);
}

static GEN
lfundivpoles(GEN ldata1, GEN ldata2, long bitprec)
{
  long k = ldata_get_k(ldata1), i, j, l;
  GEN r1 = ldata_get_residue(ldata1);
  GEN r2 = ldata_get_residue(ldata2), r;

  if (r1 && typ(r1) != t_VEC) r1 = mkvec(mkvec2(stoi(k), r1));
  if (r2 && typ(r2) != t_VEC) r2 = mkvec(mkvec2(stoi(k), r2));
  if (!r1) return NULL;
  r1 = lfunrtopoles(r1);
  l = lg(r1); r = cgetg(l, t_VEC);
  for (i = j = 1; j < l; j++)
  {
    GEN be = gel(r1,j);
    GEN z = gdiv(lfun(ldata1,be,bitprec), lfun(ldata2,be,bitprec));
    if (valp(z) < 0) gel(r,i++) = mkvec2(be, z);
  }
  if (i == 1) return NULL;
  setlg(r, i); return r;
}

GEN
lfundiv(GEN ldata1, GEN ldata2, long bitprec)
{
  pari_sp ltop = avma;
  GEN r, N, v, v1, v2, eno, a1a2, b1b2, LD, eno2;
  long k, j, j1, j2, l1, l2;
  ldata1 = lfunmisc_to_ldata_shallow(ldata1);
  ldata2 = lfunmisc_to_ldata_shallow(ldata2);
  k = ldata_get_k(ldata1);
  if (ldata_get_k(ldata2) != k)
    pari_err_OP("lfundiv [weight]",ldata1, ldata2);
  r = lfundivpoles(ldata1, ldata2, bitprec);
  N = gdiv(ldata_get_conductor(ldata1), ldata_get_conductor(ldata2));
  if (typ(N) != t_INT) pari_err_OP("lfundiv [conductor]",ldata1, ldata2);
  a1a2 = lfunconvolinv(ldata_get_an(ldata1), ldata_get_an(ldata2));
  b1b2 = lfuncombdual(lfunconvolinv, ldata1, ldata2);
  eno2 = ldata_get_rootno(ldata2);
  eno = isintzero(eno2)? gen_0: gdiv(ldata_get_rootno(ldata1), eno2);
  v1 = shallowcopy(ldata_get_gammavec(ldata1));
  v2 = ldata_get_gammavec(ldata2);
  l1 = lg(v1); l2 = lg(v2);
  for (j2 = 1; j2 < l2; j2++)
  {
    for (j1 = 1; j1 < l1; j1++)
      if (gel(v1,j1) && gequal(gel(v1,j1), gel(v2,j2)))
      {
        gel(v1,j1) = NULL; break;
      }
    if (j1 == l1) pari_err_OP("lfundiv [Vga]",ldata1, ldata2);
  }
  v = cgetg(l1-l2+1, t_VEC);
  for (j1 = j = 1; j1 < l1; j1++)
    if (gel(v1, j1)) gel(v,j++) = gel(v1,j1);

  LD = mkvecn(7, a1a2, b1b2, v, stoi(k), N, eno, r);
  if (!r) setlg(LD,7);
  return gerepilecopy(ltop, LD);
}

static GEN
gamma_imagchi(GEN gam, long w)
{
  long i, j, k=1, l;
  GEN g = cgetg_copy(gam, &l);
  gam = shallowcopy(gam);
  for (i = l-1; i>=1; i--)
  {
    GEN al = gel(gam, i);
    if (al)
    {
      GEN N = gaddsg(w,gmul2n(real_i(al),1));
      if (gcmpgs(N,2) > 0)
      {
        GEN bl = gsubgs(al, 1);
        for (j=1; j < i; j++)
          if (gel(gam,j) && gequal(gel(gam,j), bl))
          { gel(gam,j) = NULL; break; }
        if (j==i) return NULL;
        gel(g, k++) = al;
        gel(g, k++) = bl;
      } else if (gequal0(N))
        gel(g, k++) = gaddgs(al, 1);
      else if (gequal1(N))
        gel(g, k++) = gsubgs(al, 1);
      else return NULL;
    }
  }
  return sort(g);
}

GEN
lfuntwist(GEN ldata1, GEN chi)
{
  pari_sp ltop = avma;
  GEN L, N, N1, N2, a, a1, a2, b, b1, b2, gam, gam1, gam2;
  GEN ldata2;
  long d1, k, t;
  ldata1 = lfunmisc_to_ldata_shallow(ldata1);
  ldata2 = lfunmisc_to_ldata_shallow(chi);
  t = ldata_get_type(ldata2);
  if (t == t_LFUN_ZETA)
    return gerepilecopy(ltop, ldata1);
  if (t != t_LFUN_CHIZ && t != t_LFUN_KRONECKER)
    pari_err_TYPE("lfuntwist", chi);
  N1 = ldata_get_conductor(ldata1);
  N2 = ldata_get_conductor(ldata2);
  if (!gequal1(gcdii(N1, N2)))
    pari_err_IMPL("lfuntwist (conductors not coprime)");
  k = ldata_get_k(ldata1);
  d1 = ldata_get_degree(ldata1);
  N = gmul(N1, gpowgs(N2, d1));
  gam1 = ldata_get_gammavec(ldata1);
  gam2 = ldata_get_gammavec(ldata2);
  if (gequal0(gel(gam2, 1)))
    gam = gam1;
  else
    gam = gamma_imagchi(ldata_get_gammavec(ldata1), k-1);
  if (!gam) pari_err_IMPL("lfuntwist (gammafactors)");
  a1 = ldata_get_an(ldata1);
  a2 = ldata_get_an(ldata2);
  b1 = ldata_get_dual(ldata1);
  b2 = ldata_get_dual(ldata2);
  a = tag(mkvec2(a1, a2), t_LFUN_TWIST);
  if (typ(b1)==t_INT)
    b = signe(b1) && signe(b2) ? gen_0: gen_1;
  else
    b = tag(mkvec2(b1,lfunconj(a2)), t_LFUN_TWIST);
  L = mkvecn(6, a, b, gam, stoi(k), N, gen_0);
  return gerepilecopy(ltop, L);
}

/*****************************************************************/
/*  L-series from closure                                        */
/*****************************************************************/
static GEN
localfactor(void *E, GEN p, long n)
{
  GEN s = closure_callgen2((GEN)E, p, utoi(n));
  return direuler_factor(s, n);
}
static GEN
vecan_closure(GEN a, long L, long prec)
{
  long ta = typ(a);
  GEN gL, Sbad = NULL;

  if (!L) return cgetg(1,t_VEC);
  if (ta == t_VEC)
  {
    long l = lg(a);
    if (l == 1) pari_err_TYPE("vecan_closure", a);
    ta = typ(gel(a,1));
    /* regular vector, return it */
    if (ta != t_CLOSURE) return vecslice(a, 1, minss(L,l-1));
    if (l != 3) pari_err_TYPE("vecan_closure", a);
    Sbad = gel(a,2);
    if (typ(Sbad) != t_VEC) pari_err_TYPE("vecan_closure", a);
    a = gel(a,1);
  }
  else if (ta != t_CLOSURE) pari_err_TYPE("vecan_closure", a);
  push_localprec(prec);
  gL = stoi(L);
  switch(closure_arity(a))
  {
    case 2:
      a = direuler_bad((void*)a, localfactor, gen_2, gL,gL, Sbad);
      break;
    case 1:
      a = closure_callgen1(a, gL);
      if (typ(a) != t_VEC) pari_err_TYPE("vecan_closure", a);
      break;
    default: pari_err_TYPE("vecan_closure [wrong arity]", a);
      a = NULL; /*LCOV_EXCL_LINE*/
  }
  pop_localprec(); return a;
}

/*****************************************************************/
/*  L-series of Dirichlet characters.                            */
/*****************************************************************/

static GEN
lfunzeta(void)
{
  GEN zet = mkvecn(7, NULL, gen_0, NULL, gen_1, gen_1, gen_1, gen_1);
  gel(zet,1) = tag(gen_1, t_LFUN_ZETA);
  gel(zet,3) = mkvec(gen_0);
  return zet;
}
static GEN
lfunzetainit(GEN dom, long der, long bitprec)
{ return lfuninit(lfunzeta(), dom, der, bitprec); }

static GEN
vecan_Kronecker(GEN D, long n)
{
  GEN v = cgetg(n+1, t_VECSMALL);
  ulong Du = itou_or_0(D);
  long i, id, d = Du ? minuu(Du, n): n;
  for (i = 1; i <= d; i++) v[i] = krois(D,i);
  for (id = i; i <= n; i++,id++) /* periodic mod d */
  {
    if (id > d) id = 1;
    gel(v, i) = gel(v, id);
  }
  return v;
}

static GEN
lfunchiquad(GEN D)
{
  GEN r;
  if (equali1(D)) return lfunzeta();
  if (!isfundamental(D)) pari_err_TYPE("lfunchiquad [not primitive]", D);
  r = mkvecn(6, NULL, gen_0, NULL, gen_1, NULL, gen_1);
  gel(r,1) = tag(icopy(D), t_LFUN_KRONECKER);
  gel(r,3) = mkvec(signe(D) < 0? gen_1: gen_0);
  gel(r,5) = mpabs(D);
  return r;
}

/* Begin Hecke characters. Here a character is assumed to be given by a
   vector on the generators of the ray class group clgp of CL_m(K).
   If clgp = [h,[d1,...,dk],[g1,...,gk]] with dk|...|d2|d1, a character chi
   is given by [a1,a2,...,ak] such that chi(gi)=\zeta_di^ai. */

/* Value of CHI on x, coprime to bnr.mod */
static GEN
chigeneval(GEN logx, GEN nchi, GEN z, long prec)
{
  pari_sp av = avma;
  GEN d = gel(nchi,1);
  GEN e = FpV_dotproduct(gel(nchi,2), logx, d);
  if (typ(z) != t_VEC)
    return gerepileupto(av, gpow(z, e, prec));
  else
  {
    ulong i = itou(e);
    avma = av; return gel(z, i+1);
  }
}

/* return x + yz; y != 0; z = 0,1 "often"; x = 0 "often" */
static GEN
gaddmul(GEN x, GEN y, GEN z)
{
  pari_sp av;
  if (typ(z) == t_INT)
  {
    if (!signe(z)) return x;
    if (equali1(z)) return gadd(x,y);
  }
  if (isintzero(x)) return gmul(y,z);
  av = avma;
  return gerepileupto(av, gadd(x, gmul(y,z)));
}

static GEN
vecan_chiZ(GEN an, long n, long prec)
{
  forprime_t iter;
  GEN G = gel(an,1);
  GEN nchi = gel(an,2), gord = gel(nchi,1), z;
  GEN gp = cgetipos(3), v = vec_ei(n, 1);
  GEN N = znstar_get_N(G);
  long ord = itos_or_0(gord);
  ulong Nu = itou_or_0(N);
  long i, id, d = Nu ? minuu(Nu, n): n;
  ulong p;

  if (ord && n > (ord>>4))
  {
    GEN w = ncharvecexpo(G, nchi);
    z = grootsof1(ord, prec);
    for (i = 1; i <= d; i++)
      if (w[i] >= 0) gel(v, i) = gel(z, w[i]+1);
  }
  else
  {
    z = rootsof1_cx(gord, prec);
    u_forprime_init(&iter, 2, d);
    while ((p = u_forprime_next(&iter)))
    {
      GEN ch;
      ulong k;
      if (!umodiu(N,p)) continue;
      gp[2] = p;
      ch = chigeneval(znconreylog(G, gp), nchi, z, prec);
      gel(v, p)  = ch;
      for (k = 2*p; k <= (ulong)d; k += p)
        gel(v, k) = gaddmul(gel(v, k), ch, gel(v, k/p));
    }
  }
  for (id = i = d+1; i <= n; i++,id++) /* periodic mod d */
  {
    if (id > d) id = 1;
    gel(v, i) = gel(v, id);
  }
  return v;
}

static GEN
vecan_chigen(GEN an, long n, long prec)
{
  forprime_t iter;
  GEN bnr = gel(an,1), nf = bnr_get_nf(bnr);
  GEN nchi = gel(an,2), gord = gel(nchi,1), z;
  GEN gp = cgetipos(3), v = vec_ei(n, 1);
  GEN N = gel(bnr_get_mod(bnr), 1), NZ = gcoeff(N,1,1);
  long ord = itos_or_0(gord);
  ulong p;

  if (ord && n > (ord>>4))
    z = grootsof1(ord, prec);
  else
    z = rootsof1_cx(gord, prec);

  if (nf_get_degree(nf) == 1)
  {
    ulong Nu = itou_or_0(NZ);
    long i, id, d = Nu ? minuu(Nu, n): n;
    u_forprime_init(&iter, 2, d);
    while ((p = u_forprime_next(&iter)))
    {
      GEN ch;
      ulong k;
      if (!umodiu(NZ,p)) continue;
      gp[2] = p;
      ch = chigeneval(isprincipalray(bnr,gp), nchi, z, prec);
      gel(v, p)  = ch;
      for (k = 2*p; k <= (ulong)d; k += p)
        gel(v, k) = gaddmul(gel(v, k), ch, gel(v, k/p));
    }
    for (id = i = d+1; i <= n; i++,id++) /* periodic mod d */
    {
      if (id > d) id = 1;
      gel(v, i) = gel(v, id);
    }
  }
  else
  {
    GEN BOUND = stoi(n);
    u_forprime_init(&iter, 2, n);
    while ((p = u_forprime_next(&iter)))
    {
      GEN L;
      long j;
      int check = !umodiu(NZ,p);
      gp[2] = p;
      L = idealprimedec_limit_norm(nf, gp, BOUND);
      for (j = 1; j < lg(L); j++)
      {
        GEN pr = gel(L, j), ch;
        ulong k, q;
        if (check && idealval(nf, N, pr)) continue;
        ch = chigeneval(isprincipalray(bnr,pr), nchi, z, prec);
        q = upr_norm(pr);
        gel(v, q) = gadd(gel(v, q), ch);
        for (k = 2*q; k <= (ulong)n; k += q)
          gel(v, k) = gaddmul(gel(v, k), ch, gel(v, k/q));
      }
    }
  }
  return v;
}

static GEN lfunzetak_i(GEN T);
static GEN
vec01(long r1, long r2)
{
  long d = r1+r2, i;
  GEN v = cgetg(d+1,t_VEC);
  for (i = 1; i <= r1; i++) gel(v,i) = gen_0;
  for (     ; i <= d;  i++) gel(v,i) = gen_1;
  return v;
}

/* G is a bid of nftyp typ_BIDZ */
static GEN
lfunchiZ(GEN G, GEN chi)
{
  pari_sp av = avma;
  GEN sig = NULL;
  GEN N = bid_get_ideal(G), nchi, r;
  int real;

  if (typ(N) != t_INT) pari_err_TYPE("lfunchiZ", G);
  if (equali1(N)) return lfunzeta();
  if (typ(chi) != t_COL) chi = znconreylog(G,chi);
  N = znconreyconductor(G, chi, &chi);
  if (typ(N) != t_INT)
  {
    if (equali1(gel(N,1))) { avma = av; return lfunzeta(); }
    G = znstar0(N, 1);
    N = gel(N,1);
  }
  /* chi now primitive on G */
  switch(itou_or_0(zncharorder(G, chi)))
  {
    case 1: avma = av; return lfunzeta();
    case 2: if (zncharisodd(G,chi)) N = negi(N);
            return gerepileupto(av, lfunchiquad(N));
  }
  sig = mkvec( zncharisodd(G, chi)? gen_1: gen_0 );
  nchi = znconreylog_normalize(G, chi);
  real = abscmpiu(gel(nchi,1), 2) <= 0;
  r = mkvecn(6, tag(mkvec2(G,nchi), t_LFUN_CHIZ),
                real? gen_0: gen_1, sig, gen_1, N, gen_0);
  return gerepilecopy(av, r);
}

static GEN
lfunchigen(GEN bnr, GEN CHI)
{
  pari_sp av = avma;
  GEN v;
  GEN N, sig, Ldchi, nf, nchi, NN;
  long r1, r2, n1;
  int real;

  if (nftyp(bnr) == typ_BIDZ) return lfunchiZ(bnr, CHI);

  v = bnrconductor_i(bnr, CHI, 2);
  bnr = gel(v,2);
  CHI = gel(v,3); /* now CHI is primitive wrt bnr */

  nf = bnr_get_nf(bnr);
  N = bnr_get_mod(bnr);
  n1 = lg(vec01_to_indices(gel(N,2))) - 1; /* vecsum(N[2]) */
  N = gel(N,1);
  NN = mulii(idealnorm(nf, N), absi_shallow(nf_get_disc(nf)));
  if (equali1(NN)) return gerepileupto(av, lfunzeta());
  if (ZV_equal0(CHI)) return gerepilecopy(av, lfunzetak_i(bnr));
  nf_get_sign(nf, &r1, &r2);
  sig = vec01(r1+r2-n1, r2+n1);
  nchi = char_normalize(CHI, cyc_normalize(bnr_get_cyc(bnr)));
  real = abscmpiu(gel(nchi,1), 2) <= 0;
  Ldchi = mkvecn(6, tag(mkvec2(bnr, nchi), t_LFUN_CHIGEN),
                    real? gen_0: gen_1, sig, gen_1, NN, gen_0);
  return gerepilecopy(av, Ldchi);
}

/* Find all characters of clgp whose kernel contain group given by HNF H.
 * Set *pcnj[i] if chi[i] is not real */
static GEN
chigenkerfind(GEN bnr, GEN H, GEN *pcnj)
{
  GEN res, cnj, L = bnrchar(bnr, H, NULL), cyc = bnr_get_cyc(bnr);
  long i, k, l = lg(L);

  res = cgetg(l, t_VEC);
  *pcnj = cnj = cgetg(l, t_VECSMALL);
  for (i = k = 1; i < l; i++)
  {
    GEN chi = gel(L,i), c = charconj(cyc, chi);
    long fl = ZV_cmp(c, chi);
    if (fl < 0) continue; /* keep one char in pair of conjugates */
    gel(res, k) = chi;
    cnj[k] = fl; k++;
  }
  setlg(cnj, k);
  setlg(res, k); return res;
}

static GEN
lfunzetak_i(GEN T)
{
  GEN Vga, N, nf, bnf = checkbnf_i(T), r = gen_0/*unknown*/;
  long r1, r2;

  if (bnf)
    nf = bnf_get_nf(bnf);
  else
  {
    nf = checknf_i(T);
    if (!nf) nf = T = nfinit(T, DEFAULTPREC);
  }
  nf_get_sign(nf,&r1,&r2);
  N = absi_shallow(nf_get_disc(nf));
  if (bnf)
  {
    GEN h = bnf_get_no(bnf);
    GEN R = bnf_get_reg(bnf);
    long prec = nf_get_prec(nf);
    r = gdiv(gmul(mulir(shifti(h, r1+r2), powru(mppi(prec), r2)), R),
             mulur(bnf_get_tuN(bnf), gsqrt(N, prec)));
  }
  Vga = vec01(r1+r2,r2);
  return mkvecn(7, tag(T,t_LFUN_NF), gen_0, Vga, gen_1, N, gen_1, r);
}
static GEN
lfunzetak(GEN T)
{ pari_sp ltop = avma; return gerepilecopy(ltop, lfunzetak_i(T)); }

/* bnf = NULL: base field = Q */
GEN
lfunabelianrelinit(GEN nfabs, GEN bnf, GEN polrel, GEN dom, long der, long bitprec)
{
  pari_sp ltop = avma;
  GEN cond, chi, cnj, res, bnr, M, domain;
  long l, i;
  long v = -1;

  if (bnf) bnf = checkbnf(bnf);
  else
  {
    v = fetch_var();
    bnf = Buchall(pol_x(v), 0, nbits2prec(bitprec));
  }
  if (typ(polrel) != t_POL) pari_err_TYPE("lfunabelianrelinit", polrel);
  cond = rnfconductor(bnf, polrel);
  chi = chigenkerfind(gel(cond,2), gel(cond,3), &cnj);
  bnr = Buchray(bnf, gel(cond,1), nf_INIT);
  l = lg(chi); res = cgetg(l, t_VEC);
  for (i = 1; i < l; ++i)
  {
    GEN L = lfunchigen(bnr, gel(chi,i));
    gel(res, i) = lfuninit(L, dom, der, bitprec);
  }
  if (v >= 0) delete_var();
  M = mkvec3(res, const_vecsmall(l-1, 1), cnj);
  domain = mkvec2(dom, mkvecsmall2(der, bitprec));
  return gerepilecopy(ltop, lfuninit_make(t_LDESC_PRODUCT, lfunzetak_i(nfabs), M, domain));
}

/*****************************************************************/
/*                 Dedekind zeta functions                       */
/*****************************************************************/
static GEN
dirzetak0(GEN nf, ulong N)
{
  GEN vect, c, c2, T = nf_get_pol(nf), index = nf_get_index(nf);
  pari_sp av = avma, av2;
  const ulong SQRTN = usqrt(N);
  ulong i, p, lx;
  long court[] = {evaltyp(t_INT)|_evallg(3), evalsigne(1)|evallgefint(3),0};
  forprime_t S;

  c  = cgetalloc(t_VECSMALL, N+1);
  c2 = cgetalloc(t_VECSMALL, N+1);
  c2[1] = c[1] = 1; for (i=2; i<=N; i++) c[i] = 0;
  u_forprime_init(&S, 2, N); av2 = avma;
  while ( (p = u_forprime_next(&S)) )
  {
    avma = av2;
    if (umodiu(index, p)) /* p does not divide index */
      vect = gel(Flx_degfact(ZX_to_Flx(T,p), p),1);
    else
    {
      court[2] = p;
      vect = idealprimedec_degrees(nf,court);
    }
    lx = lg(vect);
    if (p <= SQRTN)
      for (i=1; i<lx; i++)
      {
        ulong qn, q = upowuu(p, vect[i]); /* Norm P[i] */
        if (!q || q > N) break;
        memcpy(c2 + 2, c + 2, (N-1)*sizeof(long));
        /* c2[i] <- c[i] + sum_{k = 1}^{v_q(i)} c[i/q^k] for all i <= N */
        for (qn = q; qn <= N; qn *= q)
        {
          ulong k0 = N/qn, k, k2; /* k2 = k*qn */
          for (k = k0, k2 = k*qn; k > 0; k--, k2 -=qn) c2[k2] += c[k];
          if (q > k0) break; /* <=> q*qn > N */
        }
        swap(c, c2);
      }
    else /* p > sqrt(N): simpler */
      for (i=1; i<lx; i++)
      {
        ulong k, k2; /* k2 = k*p */
        if (vect[i] > 1) break;
        /* c2[i] <- c[i] + sum_{k = 1}^{v_q(i)} c[i/q^k] for all i <= N */
        for (k = N/p, k2 = k*p; k > 0; k--, k2 -= p) c[k2] += c[k];
      }
  }
  avma = av;
  pari_free(c2); return c;
}

GEN
dirzetak(GEN nf, GEN b)
{
  GEN z, c;
  long n;

  if (typ(b) != t_INT) pari_err_TYPE("dirzetak",b);
  if (signe(b) <= 0) return cgetg(1,t_VEC);
  nf = checknf(nf);
  n = itou_or_0(b); if (!n) pari_err_OVERFLOW("dirzetak");
  c = dirzetak0(nf, n);
  z = vecsmall_to_vec(c); pari_free(c); return z;
}

static GEN
linit_get_mat(GEN linit)
{
  if (linit_get_type(linit)==t_LDESC_PRODUCT)
    return lfunprod_get_fact(linit_get_tech(linit));
  else
    return mkvec3(mkvec(linit), mkvecsmall(1), mkvecsmall(0));
}

static GEN
lfunproduct(GEN ldata, GEN linit1, GEN linit2, GEN domain)
{
  GEN M1 = linit_get_mat(linit1);
  GEN M2 = linit_get_mat(linit2);
  GEN M3 = mkvec3(shallowconcat(gel(M1, 1), gel(M2, 1)),
                  vecsmall_concat(gel(M1, 2), gel(M2, 2)),
                  vecsmall_concat(gel(M1, 3), gel(M2, 3)));
  return lfuninit_make(t_LDESC_PRODUCT, ldata, M3, domain);
}

static GEN
lfunzetakinit_raw(GEN T, GEN dom, long der, long bitprec)
{
  pari_sp ltop = avma;
  GEN ldata = lfunzetak_i(T);
  return gerepileupto(ltop, lfuninit(ldata, dom, der, bitprec));
}

static GEN
lfunzetakinit_quotient(GEN nf, GEN polk, GEN dom, long der, long bitprec)
{
  pari_sp av = avma;
  GEN ak, an, nfk, Vga, ldata, N, Lk, LKk, domain;
  long r1k, r2k, r1, r2;

  nf_get_sign(nf,&r1,&r2);
  nfk = nfinit(polk, nbits2prec(bitprec));
  Lk = lfunzetakinit(nfk, dom, der, 0, bitprec); /* zeta_k */
  nf_get_sign(nfk,&r1k,&r2k);
  Vga = vec01((r1+r2) - (r1k+r2k), r2-r2k);
  N = absi_shallow(diviiexact(nf_get_disc(nf), nf_get_disc(nfk)));
  ak = nf_get_degree(nf)==1 ? tag(gen_1, t_LFUN_ZETA): tag(nfk, t_LFUN_NF);
  an = tag(mkvec2(tag(nf,t_LFUN_NF), ak), t_LFUN_DIV);
  ldata = mkvecn(6, an, gen_0, Vga, gen_1, N, gen_1);
  LKk = lfuninit(ldata, dom, der, bitprec); /* zeta_K/zeta_k */
  domain = mkvec2(dom, mkvecsmall2(der, bitprec));
  return gerepilecopy(av, lfunproduct(lfunzetak_i(nf), Lk, LKk, domain));
}

static GEN
lfunzetakinit_artin(GEN nf, GEN gal, GEN dom, long der, long bitprec);

static GEN
lfunzetakinit_Galois(GEN nf, GEN gal, GEN dom, long der, long bitprec)
{
  GEN grp = galois_group(gal);
  if (group_isabelian(grp))
    return lfunabelianrelinit(nf, NULL, gal_get_pol(gal), dom, der, bitprec);
  else return lfunzetakinit_artin(nf, gal, dom, der, bitprec);
}

GEN
lfunzetakinit(GEN NF, GEN dom, long der, long flag, long bitprec)
{
  GEN nf = checknf(NF);
  GEN G, nfs, sbg;
  long lf, d = nf_get_degree(nf);
  if (d == 1) return lfunzetainit(dom, der, bitprec);
  G = galoisinit(nf, NULL);
  if (!isintzero(G))
    return lfunzetakinit_Galois(nf, G, dom, der, bitprec);
  nfs = nfsubfields(nf, 0); lf = lg(nfs)-1;
  sbg = gmael(nfs,lf-1,1);
  if (flag && d > 4*degpol(sbg))
    return lfunzetakinit_raw(nf, dom, der, bitprec);
  return lfunzetakinit_quotient(nf, sbg, dom, der, bitprec);
}

/***************************************************************/
/*             Elliptic Curves and Modular Forms               */
/***************************************************************/

static GEN
lfunellnf(GEN e)
{
  pari_sp av = avma;
  GEN ldata = cgetg(7, t_VEC), nf = ellnf_get_nf(e);
  GEN N = gel(ellglobalred(e), 1);
  long n = nf_get_degree(nf);
  gel(ldata, 1) = tag(e, t_LFUN_ELL);
  gel(ldata, 2) = gen_0;
  gel(ldata, 3) = vec01(n, n);
  gel(ldata, 4) = gen_2;
  gel(ldata, 5) = mulii(idealnorm(nf,N), sqri(nf_get_disc(nf)));
  gel(ldata, 6) = stoi(ellrootno_global(e));
  return gerepilecopy(av, ldata);
}

static GEN
lfunellQ(GEN e)
{
  pari_sp av = avma;
  GEN ldata = cgetg(7, t_VEC);
  gel(ldata, 1) = tag(ellanal_globalred(e, NULL), t_LFUN_ELL);
  gel(ldata, 2) = gen_0;
  gel(ldata, 3) = mkvec2(gen_0, gen_1);
  gel(ldata, 4) = gen_2;
  gel(ldata, 5) = ellQ_get_N(e);
  gel(ldata, 6) = stoi(ellrootno_global(e));
  return gerepilecopy(av, ldata); /* ellanal_globalred not gerepile-safe */
}

static GEN
lfunell(GEN e)
{
  long t = ell_get_type(e);
  switch(t)
  {
    case t_ELL_Q: return lfunellQ(e);
    case t_ELL_NF:return lfunellnf(e);
  }
  pari_err_TYPE("lfun",e);
  return NULL; /*LCOV_EXCL_LINE*/
}

static GEN
ellsympow_gamma(long m)
{
  GEN V = cgetg(m+2, t_VEC);
  long i = 1, j;
  if (!odd(m)) gel(V, i++) = stoi(-2*(m>>2));
  for (j = (m+1)>>1; j > 0; i+=2, j--)
  {
    gel(V,i)   = stoi(1-j);
    gel(V,i+1) = stoi(1-j+1);
  }
  return V;
}

static GEN
ellsympow_trace(GEN p, GEN t, long m)
{
  long k, n = m >> 1;
  GEN tp = gpowers0(sqri(t), n, odd(m)? t: NULL);
  GEN pp = gen_1, b = gen_1, r = gel(tp,n+1);
  for(k=1; k<=n; k++)
  {
    GEN s;
    pp = mulii(pp, p);
    b  = diviuexact(muliu(b, (m-(2*k-1))*(m-(2*k-2))), k*(m-(k-1)));
    s = mulii(mulii(b, gel(tp,1+n-k)), pp);
    r = odd(k) ? subii(r, s): addii(r, s);
  }
  return r;
}

static GEN
ellsympow_abelian(GEN p, GEN ap, long m, long o)
{
  pari_sp av = avma;
  long i, M, n = (m+1)>>1;
  GEN pk, tv, pn, pm, F, v;
  if (!odd(o))
  {
    if (odd(m)) return pol_1(0);
    M = m >> 1; o >>= 1;
  }
  else
    M = m * ((o+1) >> 1);
  pk = gpowers(p,n); pn = gel(pk,n+1);
  tv = cgetg(m+2,t_VEC);
  gel(tv, 1) = gen_2;
  gel(tv, 2) = ap;
  for (i = 3; i <= m+1; i++)
    gel(tv,i) = subii(mulii(ap,gel(tv,i-1)), mulii(p,gel(tv,i-2)));
  pm = odd(m)? mulii(gel(pk,n), pn): sqri(pn); /* cheap p^m */
  F = deg2pol_shallow(pm, gen_0, gen_1, 0);
  v = odd(m) ? pol_1(0): deg1pol_shallow(negi(pn), gen_1, 0);
  for (i = M % o; i < n; i += o) /* o | m-2*i */
  {
    gel(F,3) = negi(mulii(gel(tv,m-2*i+1), gel(pk,i+1)));
    v = ZX_mul(v, F);
  }
  return gerepilecopy(av, v);
}

static GEN
ellsympow(void *E, GEN p, long n)
{
  pari_sp av = avma;
  GEN v =(GEN) E, ap = ellap(gel(v,1), p);
  ulong m = itou(gel(v,2));
  if (n <= 2)
  {
    GEN t = ellsympow_trace(p, ap, m);
    return deg1pol_shallow(t, gen_1, 0);
  }
  else
    return gerepileupto(av, RgXn_inv_i(ellsympow_abelian(p, ap, m, 1), n));
}

static GEN
vecan_ellsympow(GEN an, long n)
{
  GEN nn = utoi(n), crvm = gel(an,1), bad = gel(an,2);
  return direuler_bad((void*)crvm, &ellsympow, gen_2, nn, nn, bad);
}

static long
ellsympow_betam(long o, long m)
{
  const long c3[]={3, -1, 1};
  const long c12[]={6, -2, 2, 0, 4, -4};
  const long c24[]={12, -2, -4, 6, 4, -10};
  if (!odd(o) && odd(m)) return 0;
  switch(o)
  {
    case 1:  return m+1;
    case 2:  return m+1;
    case 3:  case 6: return (m+c3[m%3])/3;
    case 4:  return m%4 == 0 ? (m+2)/2: m/2;
    case 8:  return m%4 == 0 ? (m+4)/4: (m-2)/4;
    case 12: return (m+c12[(m%12)/2])/6;
    case 24: return (m+c24[(m%12)/2])/12;
  }
  return 0;
}

static long
ellsympow_epsm(long o, long m)
{
  return m+1-ellsympow_betam(o, m);
}

static GEN
ellsympow_multred(GEN E, GEN p, long m, long vN, long *cnd, long *w)
{
  if (vN==1) /* mult red*/
  {
    *cnd = m;
    *w = odd(m) ? ellrootno(E, p): 1;
    if (odd(m) && signe(ellap(E,p))==-1)
      return deg1pol_shallow(gen_1, gen_1, 0);
    else
      return deg1pol_shallow(gen_m1, gen_1, 0);
  } else
  {
    *cnd = odd(m)? m+1: m;
    *w  = odd(m) && odd((m+1)>>1) ? ellrootno(E, p): 1;
    if (odd(m) && equaliu(p,2))
      *cnd += ((m+1)>>1)*(vN-2);
    return odd(m)? pol_1(0): deg1pol_shallow(gen_m1, gen_1, 0);
  }
}

static GEN
ellsympow_nonabelian(GEN p, long m, long bet)
{
 GEN pm = powiu(p, m), F;
 if (odd(m)) return gpowgs(deg2pol_shallow(pm, gen_0, gen_1, 0), bet>>1);
 F = gpowgs(deg2pol_shallow(negi(pm), gen_0, gen_1, 0), bet>>1);
 if (!odd(bet)) return F;
 if (m%4==2)
   return gmul(F, deg1pol_shallow(powiu(p, m>>1), gen_1, 0));
 else
   return gmul(F, deg1pol_shallow(negi(powiu(p, m>>1)), gen_1, 0));
}

static long
safe_Z_pvalrem(GEN n, GEN p, GEN *pr)
{ return signe(n)==0? -1: Z_pvalrem(n, p, pr); }

static GEN
c4c6_ap(GEN c4, GEN c6, GEN p)
{
  GEN N = Fp_ellcard(Fp_muls(c4,-27,p), Fp_muls(c6, -54, p), p);
  return subii(addis(p, 1), N);
}

static GEN
ellsympow_abelian_twist(GEN E, GEN p, long m, long o)
{
  GEN ap;
  GEN c4 = ell_get_c4(E), c6 = ell_get_c6(E);
  GEN c4t, c6t;
  long v4 = safe_Z_pvalrem(c4, p, &c4t);
  long v6 = safe_Z_pvalrem(c6, p, &c6t);
  if (v6>=0 && (v4==-1 || 3*v4>=2*v6)) c6 = c6t;
  if (v4>=0 && (v6==-1 || 3*v4<=2*v6)) c4 = c4t;
  ap = c4c6_ap(c4, c6, p);
  return ellsympow_abelian(p, ap, m, o);
}

static GEN
ellsympow_goodred(GEN E, GEN p, long m, long *cnd, long *w)
{
  long o = 12/cgcd(12, Z_pval(ell_get_disc(E), p));
  long bet = ellsympow_betam(o, m);
  long eps = m + 1 - bet;
  *w = odd(m) && odd(eps>>1) ? ellrootno(E,p): 1;
  *cnd = eps;
  if (umodiu(p, o) == 1)
    return ellsympow_abelian_twist(E, p, m, o);
  else
    return ellsympow_nonabelian(p, m, bet);
}

static long
ellsympow_inertia3(GEN E, long vN)
{
  long vD = Z_lval(ell_get_disc(E), 3);
  if (vN==2) return vD%2==0 ? 2: 4;
  if (vN==4) return vD%4==0 ? 3: 6;
  if (vN==3 || vN==5) return 12;
  return 0;
}

static long
ellsympow_deltam3(long o, long m, long vN)
{
  if (o==3 || o==6) return ellsympow_epsm(3, m);
  if (o==12 && vN ==3) return (ellsympow_epsm(3, m))/2;
  if (o==12 && vN ==5) return (ellsympow_epsm(3, m))*3/2;
  return 0;
}

static long
ellsympow_isabelian3(GEN E)
{
  ulong c4 = umodiu(ell_get_c4(E),81), c6 = umodiu(ell_get_c6(E), 243);
  return (c4 == 27 || (c4%27==9 && (c6==108 || c6==135)));
}

static long
ellsympow_rootno3(GEN E, GEN p, long o, long m)
{
  const long  w6p[]={1,-1,-1,-1,1,1};
  const long  w6n[]={-1,1,-1,1,-1,1};
  const long w12p[]={1,1,-1,1,1,1};
  const long w12n[]={-1,-1,-1,-1,-1,1};
  long w = ellrootno(E, p), mm = (m%12)>>1;
  switch(o)
  {
    case 2: return m%4== 1 ? -1: 1;
    case 6:  return w == 1 ? w6p[mm]: w6n[mm];
    case 12: return w == 1 ? w12p[mm]: w12n[mm];
    default: return 1;
  }
}

static GEN
ellsympow_goodred3(GEN E, GEN F, GEN p, long m, long vN, long *cnd, long *w)
{
  long o = ellsympow_inertia3(E, vN);
  long bet = ellsympow_betam(o, m);
  *cnd = m + 1 - bet + ellsympow_deltam3(o, m, vN);
  *w = odd(m)? ellsympow_rootno3(E, p, o, m): 1;
  if (o==1 || o==2)
    return ellsympow_abelian(p, ellap(F, p), m, o);
  if ((o==3 || o==6) && ellsympow_isabelian3(F))
    return ellsympow_abelian(p, p, m, o);
  else
    return ellsympow_nonabelian(p, m, bet);
}

static long
ellsympow_inertia2(GEN F, long vN)
{
  long vM = itos(gel(elllocalred(F, gen_2),1));
  GEN c6 = ell_get_c6(F);
  long v6 = signe(c6) ? vali(c6): 24;
  if (vM==0) return vN==0 ? 1: 2;
  if (vM==2) return vN==2 ? 3: 6;
  if (vM==5) return 8;
  if (vM==8) return v6>=9? 8: 4;
  if (vM==3 || vN==7) return 24;
  return 0;
}

static long
ellsympow_deltam2(long o, long m, long vN)
{
  if ((o==2 || o==6) && vN==4) return ellsympow_epsm(2, m);
  if ((o==2 || o==6) && vN==6) return 2*ellsympow_epsm(2, m);
  if (o==4) return 2*ellsympow_epsm(4, m)+ellsympow_epsm(2, m);
  if (o==8 && vN==5) return ellsympow_epsm(8, m)+ellsympow_epsm(2, m)/2;
  if (o==8 && vN==6) return ellsympow_epsm(8, m)+ellsympow_epsm(2, m);
  if (o==8 && vN==8) return ellsympow_epsm(8, m)+ellsympow_epsm(4, m)+ellsympow_epsm(2, m);
  if (o==24 && vN==3) return (2*ellsympow_epsm(8, m)+ellsympow_epsm(2, m))/6;
  if (o==24 && vN==4) return (ellsympow_epsm(8, m)+ellsympow_epsm(2, m)*2)/3;
  if (o==24 && vN==6) return (ellsympow_epsm(8, m)+ellsympow_epsm(2, m)*5)/3;
  if (o==24 && vN==7) return (ellsympow_epsm(8, m)*10+ellsympow_epsm(2, m)*5)/6;
  return 0;
}

static long
ellsympow_isabelian2(GEN F)
{ return umodi2n(ell_get_c4(F),7) == 96; }

static long
ellsympow_rootno2(GEN E, long vN, long m, long bet)
{
  long eps2 = (m + 1 - bet)>>1;
  long eta = odd(vN) && m%8==3 ? -1 : 1;
  long w2 = odd(eps2) ? ellrootno(E, gen_2): 1;
  return eta == w2 ? 1 : -1;
}

static GEN
ellsympow_goodred2(GEN E, GEN F, GEN p, long m, long vN, long *cnd, long *w)
{
  long o = ellsympow_inertia2(F, vN);
  long bet = ellsympow_betam(o, m);
  *cnd = m + 1 - bet + ellsympow_deltam2(o, m, vN);
  *w = odd(m) ? ellsympow_rootno2(E, vN, m, bet): 1;
  if (o==1 || o==2)
    return ellsympow_abelian(p, ellap(F, p), m, o);
  if (o==4 && ellsympow_isabelian2(F))
    return ellsympow_abelian(p, p, m, o);
  else
    return ellsympow_nonabelian(p, m, bet);
}

static GEN
ellminimaldotwist(GEN E, GEN *pD, long prec)
{
  GEN D = ellminimaltwistcond(E), Et = elltwist(E, D), Etmin;
  if (pD) *pD = D;
  Et = ellinit(Et, NULL, prec);
  Etmin = ellminimalmodel(Et, NULL);
  obj_free(Et); return Etmin;
}

/* Based on
Symmetric powers of elliptic curve L-functions,
Phil Martin and Mark Watkins, ANTS VII
<http://magma.maths.usyd.edu.au/users/watkins/papers/antsVII.pdf>
with thanks to Mark Watkins. BA20180402
*/
static GEN
lfunellsympow(GEN e, ulong m)
{
  pari_sp av = avma;
  GEN B, N, Nfa, pr, ex, ld, bad, ejd, et, pole;
  long i, l, mero, w = (m&7)==1 || (m&7)==3 ? -1: 1;
  checkell_Q(e);
  e = ellminimalmodel(e, NULL);
  ejd = Q_denom(ell_get_j(e));
  mero = m==0 || (m%4==0 && ellQ_get_CM(e)<0);
  ellQ_get_Nfa(e, &N, &Nfa);
  pr = gel(Nfa,1);
  ex = gel(Nfa,2); l = lg(pr);
  if (ugcd(umodiu(N,6), 6) == 1)
    et = NULL;
  else
    et = ellminimaldotwist(e, NULL, DEFAULTPREC);
  B = gen_1;
  bad = cgetg(l, t_VEC);
  for (i=1; i<l; i++)
  {
    long vN = itos(gel(ex,i));
    GEN p = gel(pr,i), eul;
    long cnd, wp;
    if (dvdii(ejd, p))
      eul = ellsympow_multred(e, p, m, vN, &cnd, &wp);
    else if (equaliu(p, 2))
      eul = ellsympow_goodred2(e, et, p, m, vN, &cnd, &wp);
    else if (equaliu(p, 3))
      eul = ellsympow_goodred3(e, et, p, m, vN, &cnd, &wp);
    else
      eul = ellsympow_goodred(e, p, m, &cnd, &wp);
    gel(bad, i) = mkvec2(p, ginv(eul));
    B = mulii(B, powiu(p,cnd));
    w *= wp;
  }
  pole = mero ? mkvec(mkvec2(stoi(1+(m>>1)),gen_0)): NULL;
  ld = mkvecn(mero? 7: 6, tag(mkvec2(mkvec2(e,utoi(m)),bad), t_LFUN_SYMPOW_ELL),
        gen_0, ellsympow_gamma(m), stoi(m+1), B, stoi(w), pole);
  if (et) obj_free(et);
  return gerepilecopy(av, ld);
}

GEN
lfunsympow(GEN ldata, ulong m)
{
  ldata = lfunmisc_to_ldata_shallow(ldata);
  if (ldata_get_type(ldata) != t_LFUN_ELL)
    pari_err_IMPL("lfunsympow");
  return lfunellsympow(gel(ldata_get_an(ldata), 2), m);
}

GEN
lfunmfspec(GEN lmisc, long bitprec)
{
  pari_sp ltop = avma;
  GEN Vga, linit, ldataf, veven, vodd, om, op, eps, dom;
  long k, k2, j;

  ldataf = lfunmisc_to_ldata_shallow(lmisc);
  k = ldata_get_k(ldataf);
  dom = mkvec3(dbltor(k/2.), dbltor((k-2)/2.), gen_0);
  if (is_linit(lmisc) && linit_get_type(lmisc) == t_LDESC_INIT
      && sdomain_isincl(k, dom, lfun_get_dom(linit_get_tech(lmisc))))
    linit = lmisc;
  else
    linit = lfuninit(ldataf, dom, 0, bitprec);
  Vga = ldata_get_gammavec(ldataf);
  if (!gequal(Vga, mkvec2(gen_0,gen_1)))
    pari_err_TYPE("lfunmfspec", lmisc);
  if (odd(k)) pari_err_IMPL("odd weight in lfunmfspec");
  k2 = k/2;
  vodd = cgetg(k2+1, t_VEC);
  veven = cgetg(k2, t_VEC);
  for (j=1; j <= k2; ++j) gel(vodd,j) = lfunlambda(linit, stoi(2*j-1), bitprec);
  for (j=1; j < k2; ++j) gel(veven,j) = lfunlambda(linit, stoi(2*j), bitprec);
  if (k > 2)
  {
    om = gel(veven,1);
    veven = gdiv(veven, om);
    op = gel(vodd,2);
  }
  else
  { /* veven empty */
    om = gen_1;
    op = gel(vodd,1);
  }
  if (maxss(gexpo(imag_i(om)), gexpo(imag_i(op))) > -bitprec/2)
    pari_err_TYPE("lfunmfspec", lmisc);
  vodd = gdiv(vodd, op);
  eps = int2n(bitprec/4);
  veven= bestappr(veven, eps);
  vodd = bestappr(vodd, eps);
  return gerepilecopy(ltop, mkvec4(veven, vodd, om, op));
}

static long
ellsymsq_bad2(GEN c4, GEN c6, long e)
{
  switch (e)
  {
    case 2: return 1;
    case 3: return 0;
    case 5: return 0;
    case 7: return 0;
    case 8:
      if (dvdiu(c6,512)) return 0;
      return umodiu(c4,128)==32 ? 1 : -1;
    default: return 0;
  }
}
static long
ellsymsq_bad3(GEN c4, GEN c6, long e)
{
  long c6_243, c4_81;
  switch (e)
  {
    case 2: return 1;
    case 3: return 0;
    case 5: return 0;
    case 4:
      c4_81 = umodiu(c4,81);
      if (c4_81 == 27) return -1;
      if (c4_81%27 != 9) return 1;
      c6_243 = umodiu(c6,243);
      return (c6_243==108 || c6_243==135)? -1: 1;
    default: return 0;
  }
}
static int
c4c6_testp(GEN c4, GEN c6, GEN p)
{ GEN p2 = sqri(p); return (dvdii(c6,p2) && !dvdii(c4,p2)); }
/* assume e = v_p(N) >= 2 */
static long
ellsymsq_badp(GEN c4, GEN c6, GEN p, long e)
{
  if (absequaliu(p, 2)) return ellsymsq_bad2(c4, c6, e);
  if (absequaliu(p, 3)) return ellsymsq_bad3(c4, c6, e);
  switch(umodiu(p, 12UL))
  {
    case 1: return -1;
    case 5: return c4c6_testp(c4,c6,p)? -1: 1;
    case 7: return c4c6_testp(c4,c6,p)?  1:-1;
    default:return 1; /* p%12 = 11 */
  }
}
static GEN
lfunellsymsqmintwist(GEN e)
{
  pari_sp av = avma;
  GEN N, Nfa, P, E, V, c4, c6, ld;
  long i, l, k;
  checkell_Q(e);
  e = ellminimalmodel(e, NULL);
  ellQ_get_Nfa(e, &N, &Nfa);
  c4 = ell_get_c4(e);
  c6 = ell_get_c6(e);
  P = gel(Nfa,1); l = lg(P);
  E = gel(Nfa,2);
  V = cgetg(l, t_VEC);
  for (i=k=1; i<l; i++)
  {
    GEN p = gel(P,i);
    long a, e = itos(gel(E,i));
    if (e == 1) continue;
    a = ellsymsq_badp(c4, c6, p, e);
    gel(V,k++) = mkvec2(p, stoi(a));
  }
  setlg(V, k);
  ld = lfunellsympow(e, 2);
  return gerepilecopy(av, mkvec2(ld, V));
}

static GEN
mfpeters(GEN ldata2, GEN fudge, GEN N, long k, long bitprec)
{
  GEN t, L = real_i(lfun(ldata2, stoi(k), bitprec));
  long prec = nbits2prec(bitprec);
  t = powrs(mppi(prec), k+1); shiftr_inplace(t, 2*k-1); /* Pi/2 * (4Pi)^k */
  return gmul(gdiv(gmul(mulii(N,mpfact(k-1)), fudge), t), L);
}

/* Assume E to be twist-minimal */
static GEN
lfunellmfpetersmintwist(GEN E, long bitprec)
{
  pari_sp av = avma;
  GEN symsq, veceuler, N = ellQ_get_N(E), fudge = gen_1;
  long j, k = 2;
  symsq = lfunellsymsqmintwist(E);
  veceuler = gel(symsq,2);
  for (j = 1; j < lg(veceuler); j++)
  {
    GEN v = gel(veceuler,j), p = gel(v,1), q = powis(p,1-k);
    long s = signe(gel(v,2));
    if (s) fudge = gmul(fudge, s==1 ? gaddsg(1, q): gsubsg(1, q));
  }
  return gerepileupto(av, mfpeters(gel(symsq,1),fudge,N,k,bitprec));
}

/* From Christophe Delaunay, http://delaunay.perso.math.cnrs.fr/these.pdf */
static GEN
elldiscfix(GEN E, GEN Et, GEN D)
{
  GEN N = ellQ_get_N(E), Nt = ellQ_get_N(Et);
  GEN P = gel(absZ_factor(D), 1);
  GEN f = gen_1;
  long i, l = lg(P);
  for (i=1; i < l; i++)
  {
    GEN r, p = gel(P,i);
    long v = Z_pval(N, p), vt = Z_pval(Nt, p);
    if (v <= vt) continue;
    /* v > vt */
    if (absequaliu(p, 2))
    {
      if (vt == 0 && v >= 4)
        r = shifti(subsi(9, sqri(ellap(Et, p))), v-3);  /* 9=(2+1)^2 */
      else if (vt == 1)
        r = gmul2n(utoipos(3), v-3);  /* not in Z if v=2 */
      else if (vt >= 2)
        r = int2n(v-vt);
      else
        r = gen_1; /* vt = 0, 1 <= v <= 3 */
    }
    else if (vt >= 1)
      r = gdiv(subiu(sqri(p), 1), p);
    else
      r = gdiv(mulii(subiu(p, 1), subii(sqri(addiu(p, 1)), sqri(ellap(Et, p)))), p);
    f = gmul(f, r);
  }
  return f;
}

GEN
lfunellmfpeters(GEN E, long bitprec)
{
  pari_sp ltop = avma;
  GEN D, Et = ellminimaldotwist(E, &D, nbits2prec(bitprec));
  GEN nor = lfunellmfpetersmintwist(Et, bitprec);
  GEN nor2 = gmul(nor, elldiscfix(E, Et, D));
  obj_free(Et); return gerepileupto(ltop, nor2);
}

/*************************************************************/
/*               Genus 2 curves                              */
/*************************************************************/

static void
Flv_diffnext(GEN d, ulong p)
{
  long j, n = lg(d)-1;
  for(j = n; j>=2; j--)
    uel(d,j) = Fl_add(uel(d,j), uel(d,j-1), p);
}

static GEN
Flx_difftable(GEN P, ulong p)
{
  long i, n = degpol(P);
  GEN V = cgetg(n+2, t_VECSMALL);
  uel(V, n+1) = Flx_constant(P);
  for(i = n; i >= 1; i--)
  {
    P = Flx_diff1(P, p);
    uel(V, i) = Flx_constant(P);
  }
  return V;
}

static long
Flx_genus2trace_naive(GEN H, ulong p)
{
  pari_sp av = avma;
  ulong i, j;
  long a, n = degpol(H);
  GEN k = const_vecsmall(p, -1), d;
  k[1] = 0;
  for (i=1, j=1; i < p; i += 2, j = Fl_add(j, i, p))
    k[j+1] = 1;
  a = n == 5 ? 0: k[1+Flx_lead(H)];
  d = Flx_difftable(H, p);
  for (i=0; i < p; i++)
  {
    a += k[1+uel(d,n+1)];
    Flv_diffnext(d, p);
  }
  avma = av;
  return a;
}

static GEN
dirgenus2(void *E, GEN p, long n)
{
  pari_sp av = avma;
  GEN Q = (GEN) E;
  GEN f;
  if (n > 2)
    f = RgX_recip(hyperellcharpoly(gmul(Q,gmodulo(gen_1, p))));
  else
  {
    ulong pp = itou(p);
    GEN Qp = ZX_to_Flx(Q, pp);
    long t = Flx_genus2trace_naive(Qp, pp);
    f = deg1pol_shallow(stoi(t), gen_1, 0);
  }
  return gerepileupto(av, RgXn_inv_i(f, n));
}

static GEN
vecan_genus2(GEN an, long L)
{
  GEN Q = gel(an,1), bad = gel(an, 2);
  return direuler_bad((void*)Q, dirgenus2, gen_2, stoi(L), NULL, bad);
}

static GEN
genus2_redmodel(GEN P, GEN p)
{
  GEN M = FpX_factor(P, p);
  GEN F = gel(M,1), E = gel(M,2);
  long i, k, r = lg(F);
  GEN U = scalarpol(leading_coeff(P), varn(P));
  GEN G = cgetg(r, t_COL);
  for (i=1, k=0; i<r; i++)
  {
    if (E[i]>1)
      gel(G,++k) = gel(F,i);
    if (odd(E[i]))
      U = FpX_mul(U, gel(F,i), p);
  }
  setlg(G,++k);
  return mkvec2(G,U);
}

static GEN
oneminusxd(long d)
{
  return gsub(gen_1, pol_xn(d, 0));
}

static GEN
ellfromeqncharpoly(GEN P, GEN Q, GEN p)
{
  long v;
  GEN E, F, t, y;
  v = fetch_var();
  y = pol_x(v);
  F = gsub(gadd(ZX_sqr(y), gmul(y, Q)), P);
  E = ellinit(ellfromeqn(F), p, DEFAULTPREC);
  delete_var();
  t = ellap(E, p);
  obj_free(E);
  return mkpoln(3, gen_1, negi(t), p);
}

static GEN
genus2_eulerfact(GEN P, GEN p)
{
  GEN Pp = FpX_red(P, p);
  GEN GU = genus2_redmodel(Pp, p);
  long d = 6-degpol(Pp), v = d/2, w = odd(d);
  GEN abe, tor;
  GEN ki, kp = pol_1(0), kq = pol_1(0);
  GEN F = gel(GU,1), Q = gel(GU,2);
  long dQ = degpol(Q), lF = lg(F)-1;

  abe = dQ >= 5 ? RgX_recip(hyperellcharpoly(gmul(Q,gmodulo(gen_1,p))))
      : dQ >= 3 ? RgX_recip(ellfromeqncharpoly(Q,gen_0,p))
                : pol_1(0);
  ki = dQ != 0 ? oneminusxd(1)
              : Fp_issquare(gel(Q,2),p) ? ZX_sqr(oneminusxd(1))
                                        : oneminusxd(2);
  if (lF)
  {
    long i;
    for(i=1; i <= lF; i++)
    {
      GEN Fi = gel(F, i);
      long d = degpol(Fi);
      GEN e = FpX_rem(Q, Fi, p);
      GEN kqf = lgpol(e)==0 ? oneminusxd(d):
                FpXQ_issquare(e, Fi, p) ? ZX_sqr(oneminusxd(d))
                                        : oneminusxd(2*d);
      kp = gmul(kp, oneminusxd(d));
      kq = gmul(kq, kqf);
    }
  }
  if (v)
  {
    GEN kqoo = w==1 ? oneminusxd(1):
               Fp_issquare(leading_coeff(Q), p)? ZX_sqr(oneminusxd(1))
                                              : oneminusxd(2);
    kp = gmul(kp, oneminusxd(1));
    kq = gmul(kq, kqoo);
  }
  tor = RgX_div(ZX_mul(oneminusxd(1), kq), ZX_mul(ki, kp));
  return ginv( ZX_mul(abe, tor) );
}

static GEN
F2x_genus2_find_trans(GEN P, GEN Q, GEN F)
{
  pari_sp av = avma;
  long i, d = F2x_degree(F), v = P[1];
  GEN M, C, V;
  M = cgetg(d+1, t_MAT);
  for (i=1; i<=d; i++)
  {
    GEN Mi = F2x_rem(F2x_add(F2x_shift(Q,i-1), monomial_F2x(2*i-2,v)), F);
    gel(M,i) = F2x_to_F2v(Mi, d);
  }
  C = F2x_to_F2v(F2x_rem(P, F), d);
  V = F2m_F2c_invimage(M, C);
  return gerepileuptoleaf(av, F2v_to_F2x(V, v));
}

static GEN
F2x_genus2_trans(GEN P, GEN Q, GEN H)
{
  return F2x_add(P,F2x_add(F2x_mul(H,Q), F2x_sqr(H)));
}

static GEN
F2x_genus_redoo(GEN P, GEN Q, long k)
{
  if (F2x_degree(P)==2*k)
  {
    long c = F2x_coeff(P,2*k-1), dQ = F2x_degree(Q);
    if ((dQ==k-1 && c==1) || (dQ<k-1 && c==0))
     return F2x_genus2_trans(P, Q, monomial_F2x(k, P[1]));
  }
  return P;
}

static GEN
F2x_pseudodisc(GEN P, GEN Q)
{
  GEN dP = F2x_deriv(P), dQ = F2x_deriv(Q);
  return F2x_gcd(Q, F2x_add(F2x_mul(P, F2x_sqr(dQ)), F2x_sqr(dP)));
}

static GEN
F2x_genus_red(GEN P, GEN Q)
{
  long dP, dQ;
  GEN F, FF;
  P = F2x_genus_redoo(P, Q, 3);
  P = F2x_genus_redoo(P, Q, 2);
  P = F2x_genus_redoo(P, Q, 1);
  dP = F2x_degree(P);
  dQ = F2x_degree(Q);
  FF = F = F2x_pseudodisc(P,Q);
  while(F2x_degree(F)>0)
  {
    GEN M = gel(F2x_factor(F),1);
    long i, l = lg(M);
    for(i=1; i<l; i++)
    {
      GEN R = F2x_sqr(gel(M,i));
      GEN H = F2x_genus2_find_trans(P, Q, R);
      P = F2x_div(F2x_genus2_trans(P, Q, H), R);
      Q = F2x_div(Q, gel(M,i));
    }
    F = F2x_pseudodisc(P, Q);
  }
  return mkvec4(P,Q,FF,mkvecsmall2(dP,dQ));
}

/* Number of solutions of x^2+b*x+c */
static long
F2xqX_quad_nbroots(GEN b, GEN c, GEN T)
{
  if (lgpol(b) > 0)
  {
    GEN d = F2xq_div(c, F2xq_sqr(b, T), T);
    return F2xq_trace(d, T)? 0: 2;
  }
  else
    return 1;
}

static GEN
genus2_redmodel2(GEN P)
{
  GEN Q = pol_0(varn(P));
  GEN P2 = ZX_to_F2x(P);
  while (F2x_issquare(P2))
  {
    GEN H = F2x_to_ZX(F2x_sqrt(P2));
    GEN P1 = ZX_sub(P, ZX_sqr(H));
    GEN Q1 = ZX_add(Q, ZX_mulu(H, 2));
    if ((signe(P1)==0 ||  ZX_lval(P1,2)>=2)
     && (signe(Q1)==0 ||  ZX_lval(Q1,2)>=1))
    {
      P = ZX_shifti(P1, -2);
      Q = ZX_shifti(Q1, -1);
      P2= ZX_to_F2x(P);
    } else break;
  }
  return mkvec2(P,Q);
}

static GEN
genus2_eulerfact2(GEN PQ)
{
  GEN V = F2x_genus_red(ZX_to_F2x(gel(PQ, 1)), ZX_to_F2x(gel(PQ, 2)));
  GEN P = gel(V, 1), Q = gel(V, 2);
  GEN F = gel(V, 3), v = gel(V, 4);
  GEN abe, tor;
  GEN ki, kp = pol_1(0), kq = pol_1(0);
  long dP = F2x_degree(P), dQ = F2x_degree(Q), d = maxss(dP, 2*dQ);
  if (!lgpol(F)) return pol_1(0);
  ki = dQ!=0 || dP>0 ? oneminusxd(1):
      dP==-1 ? ZX_sqr(oneminusxd(1)): oneminusxd(2);
  abe = d>=5? RgX_recip(hyperellcharpoly(gmul(PQ,gmodulss(1,2)))):
        d>=3? RgX_recip(ellfromeqncharpoly(F2x_to_ZX(P), F2x_to_ZX(Q), gen_2)):
        pol_1(0);
  if (lgpol(F))
  {
    GEN M = gel(F2x_factor(F), 1);
    long i, lF = lg(M)-1;
    for(i=1; i <= lF; i++)
    {
      GEN Fi = gel(M, i);
      long d = F2x_degree(Fi);
      long nb  = F2xqX_quad_nbroots(F2x_rem(Q, Fi), F2x_rem(P, Fi), Fi);
      GEN kqf = nb==1 ? oneminusxd(d):
                nb==2 ? ZX_sqr(oneminusxd(d))
                      : oneminusxd(2*d);
      kp = gmul(kp, oneminusxd(d));
      kq = gmul(kq, kqf);
    }
  }
  if (maxss(v[1],2*v[2])<5)
  {
    GEN kqoo = v[1]>2*v[2] ? oneminusxd(1):
               v[1]<2*v[2] ? ZX_sqr(oneminusxd(1))
                           : oneminusxd(2);
    kp = gmul(kp, oneminusxd(1));
    kq = gmul(kq, kqoo);
  }
  tor = RgX_div(ZX_mul(oneminusxd(1),kq), ZX_mul(ki, kp));
  return ginv( ZX_mul(abe, tor) );
}

GEN
lfungenus2(GEN G)
{
  pari_sp ltop = avma;
  GEN Ldata;
  GEN gr = genus2red(G, NULL);
  GEN N  = gel(gr, 1), M = gel(gr, 2), Q = gel(gr, 3), L = gel(gr, 4);
  GEN PQ = genus2_redmodel2(Q);
  GEN e;
  long i, lL = lg(L), ram2;
  ram2 = absequaliu(gmael(M,1,1),2);
  if (ram2 && equalis(gmael(M,2,1),-1))
    pari_warn(warner,"unknown valuation of conductor at 2");
  e = cgetg(lL+(ram2?0:1), t_VEC);
  gel(e,1) = mkvec2(gen_2, ram2 ? genus2_eulerfact2(PQ)
           : ginv( RgX_recip(hyperellcharpoly(gmul(PQ,gmodulss(1,2))))) );
  for(i = ram2? 2: 1; i < lL; i++)
  {
    GEN Li = gel(L, i);
    GEN p = gel(Li, 1);
    gel(e, ram2 ? i: i+1) = mkvec2(p, genus2_eulerfact(Q,p));
  }
  Ldata = mkvecn(6, tag(mkvec2(Q,e), t_LFUN_GENUS2),
      gen_0, mkvec4(gen_0, gen_0, gen_1, gen_1), gen_2, N, gen_0);
  return gerepilecopy(ltop, Ldata);
}

/*************************************************************/
/*                        ETA QUOTIENTS                      */
/* An eta quotient is a matrix with 2 columns [m, r_m] with  */
/* m >= 1 representing f(\tau)=\prod_m\eta(m\tau)^{r_m}.     */
/*************************************************************/

/* eta(x^v) + O(x^L) */
GEN
eta_ZXn(long v, long L)
{
  long n, k = 0, v2 = 2*v, bn = v, cn = 0;
  GEN P;
  if (!L) return zeropol(0);
  P = cgetg(L+2,t_POL); P[1] = evalsigne(1);
  for(n = 0; n < L; n++) gel(P,n+2) = gen_0;
  for(n = 0;; n++, bn += v2, cn += v)
  { /* k = v * (3*n-1) * n / 2; bn = v * (2*n+1); cn = v * n */
    long k2;
    gel(P, k+2) = odd(n)? gen_m1: gen_1;
    k2 = k+cn; if (k2 >= L) break;
    k = k2;
    /* k = v * (3*n+1) * n / 2 */;
    gel(P, k+2) = odd(n)? gen_m1: gen_1;
    k2 = k+bn; if (k2 >= L) break;
    k = k2;
  }
  setlg(P, k+3); return P;
}
GEN
eta_product_ZXn(GEN eta, long L)
{
  pari_sp av = avma;
  GEN P = NULL, D = gel(eta,1), R = gel(eta,2);
  long i, l = lg(D);
  for (i = 1; i < l; ++i)
  {
    GEN Q = eta_ZXn(D[i], L);
    long r = R[i];
    if (r < 0) { Q = RgXn_inv_i(Q, L); r = -r; }
    if (r != 1) Q = RgXn_powu_i(Q, r, L);
    P = P? ZXn_mul(P, Q, L): Q;
    if (gc_needed(av,1) && i > 1)
    {
      if (DEBUGMEM>1) pari_warn(warnmem,"eta_product_ZXn");
      P = gerepilecopy(av, P);
    }
  }
  return P;
}
static GEN
vecan_eta(GEN an, long L)
{
  GEN v = RgX_to_RgC(eta_product_ZXn(an, L), L);
  settyp(v, t_VEC); return v;
}

/* return 1 if cuspidal, 0 if holomorphic, -1 otherwise */
static int
etacuspidal(GEN N, GEN k, GEN B, GEN R, GEN NB)
{
  long i, j, lD, l, cusp = 1;
  GEN D;
  if (gsigne(k) < 0) return -1;
  D = divisors(N); lD = lg(D); l = lg(B);
  for (i = 1; i < lD; i++)
  {
    GEN t = gen_0, d = gel(D,i);
    long s;
    for (j = 1; j < l; j++)
      t = addii(t, mulii(gel(NB,j), mulii(gel(R,j), sqri(gcdii(d, gel(B,j))))));
    s = signe(t);
    if (s < 0) return -1;
    if (!s) cusp = 0;
  }
  return cusp;
}
/* u | 24, level = u*N0, N0 = lcm(B), NB[i] = N0/B[i] */
static int
etaselfdual(GEN B, GEN R, GEN NB, ulong u)
{
  long i, l = lg(B);
  for (i = 1; i < l; ++i)
  {
    GEN t = muliu(gel(NB,i), u); /* *pN / B[i] */
    long j = ZV_search(B, t);
    if (!j || !equalii(gel(R,i),gel(R,j))) return 0;
  }
  return 1;
}
/* return Nebentypus of eta quotient, k2 = 2*k integral */
static GEN
etachar(GEN B, GEN R, GEN k2)
{
  long i, l = lg(B);
  GEN P = gen_1;
  for (i = 1; i < l; ++i) if (mpodd(gel(R,i))) P = mulii(P, gel(B,i));
  switch(Mod4(k2))
  {
    case 0: break;
    case 2:  P = negi(P); break;
    default: P = shifti(P, 1); break;
  }
  return coredisc(P);
}
/* Return 0 if not on gamma_0(N). Sets conductor, modular weight, character,
 * canonical matrix, v_q(eta), sd = 1 iff self-dual, cusp = 1 iff cuspidal
 * [0 if holomorphic at all cusps, else -1] */
long
etaquotype(GEN *peta, GEN *pN, GEN *pk, GEN *CHI, long *pv, long *sd,
           long *cusp)
{
  GEN B, R, S, T, N, NB, eta = *peta;
  long l, i, u, S24;

  if (lg(eta) != 3) pari_err_TYPE("lfunetaquo", eta);
  switch(typ(eta))
  {
    case t_VEC: eta = mkmat2(mkcol(gel(eta,1)), mkcol(gel(eta,2))); break;
    case t_MAT: break;
    default: pari_err_TYPE("lfunetaquo", eta);
  }
  if (!RgV_is_ZVpos(gel(eta,1)) || !RgV_is_ZV(gel(eta,2)))
    pari_err_TYPE("lfunetaquo", eta);
  *peta = eta = famat_reduce(eta);
  B = gel(eta,1); l = lg(B); /* sorted in increasing order */
  R = gel(eta,2);
  N = glcm0(B, NULL);
  NB = cgetg(l, t_VEC);
  for (i = 1; i < l; i++) gel(NB,i) = diviiexact(N, gel(B,i));
  S = gen_0; T = gen_0; u = 0;
  for (i = 1; i < l; ++i)
  {
    GEN b = gel(B,i), r = gel(R,i);
    S = addii(S, mulii(b, r));
    T = addii(T, r);
    u += umodiu(r,24) * umodiu(gel(NB,i), 24);
  }
  S = divis_rem(S, 24, &S24);
  if (S24) return 0; /* non-integral valuation at oo */
  u %= 24; if (u < 0) u += 24;
  u = 24/ugcd(24, u);
  *pN = muliu(N, u); /* level */
  *pk = gmul2n(T,-1); /* weight */
  *pv = itos(S); /* valuation */
  if (cusp) *cusp = etacuspidal(*pN, *pk, B, R, NB);
  if (sd) *sd = etaselfdual(B, R, NB, u);
  if (CHI) *CHI = etachar(B, R, T);
  return 1;
}

GEN
lfunetaquo(GEN eta0)
{
  pari_sp ltop = avma;
  GEN Ldata, N, BR, k, eta = eta0;
  long v, sd, cusp;
  if (!etaquotype(&eta, &N, &k, NULL, &v, &sd, &cusp))
    pari_err_TYPE("lfunetaquo", eta0);
  if (!cusp) pari_err_IMPL("noncuspidal eta quotient");
  if (v != 1) pari_err_IMPL("valuation != 1");
  if (!sd) pari_err_IMPL("non self-dual eta quotient");
  if (typ(k) != t_INT) pari_err_TYPE("lfunetaquo [non-integral weight]", eta0);
  BR = mkvec2(ZV_to_zv(gel(eta,1)), ZV_to_zv(gel(eta,2)));
  Ldata = mkvecn(6, tag(BR,t_LFUN_ETA), gen_0, mkvec2(gen_0,gen_1), k,N, gen_1);
  return gerepilecopy(ltop, Ldata);
}

static GEN
vecan_qf(GEN Q, long L)
{
  GEN v, w = qfrep0(Q, utoi(L), 1);
  long i;
  v = cgetg(L+1, t_VEC);
  for (i = 1; i <= L; i++) gel(v,i) = utoi(2 * w[i]);
  return v;
}

long
qf_iseven(GEN M)
{
  long i, l = lg(M);
  for (i=1; i<l; i++)
    if (mpodd(gcoeff(M,i,i))) return 0;
  return 1;
}

GEN
lfunqf(GEN M, long prec)
{
  pari_sp ltop = avma;
  long n, k;
  GEN D, d, Mi, Ldata, poles, res0, res2, eno, dual;

  if (typ(M) != t_MAT) pari_err_TYPE("lfunqf", M);
  if (!RgM_is_ZM(M))   pari_err_TYPE("lfunqf [not integral]", M);
  n = lg(M)-1;
  if (odd(n)) pari_err_TYPE("lfunqf [odd dimension]", M);
  k = n >> 1;
  M = Q_primpart(M);
  Mi = ZM_inv(M, &d); /* d M^(-1) */
  if (!qf_iseven(M)) { M = gmul2n(M, 1); d = shifti(d,1); }
  if (!qf_iseven(Mi)){ Mi= gmul2n(Mi,1); d = shifti(d,1); }
  /* det(Mi) = d^n/det(M), D^2 = det(Mi)/det(M) */
  D = gdiv(powiu(d,k), ZM_det(M));
  if (!issquareall(D, &eno)) eno = gsqrt(D, prec);
  dual = gequal1(D) ? gen_0: tag(Mi, t_LFUN_QF);
  res0 = RgX_to_ser(deg1pol_shallow(gen_m2, gen_0, 0), 3);
  setvalp(res0, -1);
  res2 = RgX_to_ser(deg1pol_shallow(gmulgs(eno,2), gen_0, 0), 3);
  setvalp(res2, -1);
  poles = mkcol2(mkvec2(stoi(k),res2), mkvec2(gen_0,res0));
  Ldata = mkvecn(7, tag(M, t_LFUN_QF), dual,
       mkvec2(gen_0, gen_1), stoi(k), d, eno, poles);
  return gerepilecopy(ltop, Ldata);
}

/********************************************************************/
/**  Artin L function, based on a GP script by Charlotte Euvrard   **/
/********************************************************************/

static GEN
artin_charfromgens(GEN G, GEN M)
{
  GEN R, V, ord = gal_get_orders(G), grp = gal_get_group(G);
  long i, j, k, n = lg(ord)-1, m = lg(grp)-1;

  if (lg(M)-1 != n) pari_err_DIM("lfunartin");
  R = cgetg(m+1, t_VEC);
  gel(R, 1) = matid(lg(gel(M, 1))-1);
  for (i = 1, k = 1; i <= n; ++i)
  {
    long c = k*(ord[i] - 1);
    gel(R, ++k) = gel(M, i);
    for (j = 2; j <= c; ++j) gel(R, ++k) = gmul(gel(R,j), gel(M,i));
  }
  V = cgetg(m+1, t_VEC);
  for (i = 1; i <= m; i++) gel(V, gel(grp,i)[1]) = gtrace(gel(R,i));
  return V;
}

static GEN
galois_get_conj(GEN G)
{
  GEN grp = gal_get_group(G);
  long i, k, r = lg(grp)-1;
  GEN b = zero_F2v(r);
  for (k = 2; k <= r; ++k)
  {
    GEN g = gel(grp,k);
    if (!F2v_coeff(b,g[1]) && g[g[1]]==1)
    {
      pari_sp av = avma;
      GEN F = galoisfixedfield(G, g, 1, -1);
      if (ZX_sturmpart(F, NULL) > 0) { avma = av; return g; }
      for (i = 1; i<=r; i++)
      {
        GEN h = gel(grp, i);
        long t = h[1];
        while (h[t]!=1) t = h[t];
        F2v_set(b, h[g[t]]);
      }
      avma = av;
    }
  }
  pari_err_BUG("galois_get_conj");
  return NULL;
}

static GEN  cyclotoi(GEN v) { return simplify_shallow(lift_shallow(v)); }
static long cyclotos(GEN v) { return gtos(cyclotoi(v)); }
static long char_dim(GEN ch) { return cyclotos(gel(ch,1)); }

static GEN
artin_gamma(GEN N, GEN G, GEN ch)
{
  long a, t, d = char_dim(ch);
  if (nf_get_r2(N) == 0) return vec01(d, 0);
  a = galois_get_conj(G)[1];
  t = cyclotos(gel(ch,a));
  return vec01((d+t) / 2, (d-t) / 2);
}

static long
artin_dim(GEN ind, GEN ch)
{
  long n = lg(ch)-1;
  GEN elts = group_elts(ind, n);
  long i, d = lg(elts)-1;
  GEN s = gen_0;
  for(i=1; i<=d; i++)
    s = gadd(s, gel(ch, gel(elts,i)[1]));
  return gtos(gdivgs(cyclotoi(s), d));
}

static GEN
artin_ind(GEN elts, GEN ch, GEN p)
{
  long i, d = lg(elts)-1;
  GEN s = gen_0;
  for(i=1; i<=d; i++)
    s = gadd(s, gel(ch, gmul(gel(elts,i),p)[1]));
  return gdivgs(s, d);
}

static GEN
artin_ram(GEN nf, GEN gal, GEN aut, GEN pr, GEN ramg, GEN ch, long d)
{
  pari_sp av = avma;
  long i, v, n;
  GEN p, q, V, elts;
  if (d==0) return pol_1(0);
  n = degpol(gal_get_pol(gal));
  q = p = idealramfrobenius_aut(nf, gal, pr, ramg, aut);
  elts = group_elts(gel(ramg,2), n);
  v = fetch_var_higher();
  V = cgetg(d+3, t_POL);
  V[1] = evalsigne(1)|evalvarn(v);
  gel(V,2) = gen_0;
  for(i=1; i<=d; i++)
  {
    gel(V,i+2) = gdivgs(artin_ind(elts, ch, q), -i);
    q = gmul(q, p);
  }
  delete_var();
  V = RgXn_exp(V,d+1);
  setvarn(V,0); return gerepileupto(av, ginv(V));
}

/* [Artin conductor, vec of [p, Lp]] */
static GEN
artin_badprimes(GEN N, GEN G, GEN aut, GEN ch)
{
  pari_sp av = avma;
  long i, d = char_dim(ch);
  GEN P = gel(absZ_factor(nf_get_disc(N)), 1);
  long lP = lg(P);
  GEN B = cgetg(lP, t_VEC), C = cgetg(lP, t_VEC);

  for (i = 1; i < lP; ++i)
  {
    GEN p = gel(P, i), pr = idealprimedec_galois(N, p);
    GEN J = idealramgroups_aut(N, G, pr, aut);
    GEN G0 = gel(J,2); /* inertia group */
    long lJ = lg(J);
    long sdec = artin_dim(G0, ch);
    long ndec = group_order(G0);
    long j, v = ndec * (d - sdec);
    for (j = 3; j < lJ; ++j)
    {
      GEN Jj = gel(J, j);
      long s = artin_dim(Jj, ch);
      v += group_order(Jj) * (d - s);
    }
    gel(C, i) = powiu(p, v/ndec);
    gel(B, i) = mkvec2(p, artin_ram(N, G, aut, pr, J, ch, sdec));
  }
  return gerepilecopy(av, mkvec2(ZV_prod(C), B));
}

struct dir_artin
{
  GEN nf, G, V, aut;
};

/* p does not divide nf.index */
static GEN
idealfrobenius_easy(GEN nf, GEN gal, GEN aut, GEN T, GEN p)
{
  long i, l = lg(aut), f = degpol(T);
  GEN D, Dzk, DzkT, DXp, grp = gal_get_group(gal);
  pari_sp av = avma;
  if (f==1) return gel(grp,1);
  Dzk = nf_get_zkprimpart(nf);
  D = modii(nf_get_zkden(nf), p);
  DzkT = RgV_to_RgM(FqV_red(Dzk, T, p), f);
  DXp = RgX_to_RgC(FpX_Frobenius(T, p), f);
  if (!equali1(D)) DXp = FpC_Fp_mul(DXp, D, p);
  for(i=1; i < l; i++)
  {
    GEN g = gel(grp,i);
    if (perm_order(g)==f)
    {
      GEN A = FpM_FpC_mul(DzkT, gel(aut,g[1]), p);
      if (ZV_equal(A, DXp)) {avma = av; return g; }
    }
  }
  return NULL; /* LCOV_EXCL_LINE */
}
/* true nf; p divides nf.index, pr/p unramified */
static GEN
idealfrobenius_hard(GEN nf, GEN gal, GEN aut, GEN pr)
{
  long i, l = lg(aut), f = pr_get_f(pr);
  GEN modpr, p, T, X, Xp, pi, grp = gal_get_group(gal);
  pari_sp av = avma;
  if (f==1) return gel(grp,1);
  pi = pr_get_gen(pr);
  modpr = zkmodprinit(nf, pr);
  p = modpr_get_p(modpr);
  T = modpr_get_T(modpr);
  X = modpr_genFq(modpr);
  Xp = FpX_Frobenius(T, p);
  for (i = 1; i < l; i++)
  {
    GEN g = gel(grp,i);
    if (perm_order(g)==f)
    {
      GEN S = gel(aut,g[1]);
      GEN A = nf_to_Fq(nf, zk_galoisapplymod(nf,X,S,p), modpr);
      /* sigma(X) = X^p (mod pr) and sigma(pi) in pr */
      if (ZX_equal(A, Xp) && (f == nf_get_degree(nf) ||
          ZC_prdvd(zk_galoisapplymod(nf,pi,S,p),pr))) { avma=av; return g; }
    }
  }
  return NULL; /* LCOV_EXCL_LINE */
}

static GEN
dirartin(void *E, GEN p, long n)
{
  pari_sp av = avma;
  struct dir_artin *d = (struct dir_artin *) E;
  GEN nf = d->nf, pr, frob;
  /* pick one maximal ideal in the conjugacy class above p */
  GEN T = nf_get_pol(nf);
  if (!dvdii(nf_get_index(nf), p))
  { /* simple case */
    GEN F = FpX_factor(T, p), P = gmael(F,1,1);
    frob = idealfrobenius_easy(nf, d->G, d->aut, P, p);
  }
  else
  {
    pr = idealprimedec_galois(nf,p);
    frob = idealfrobenius_hard(nf, d->G, d->aut, pr);
  }
  avma = av; return RgXn_inv(gel(d->V, frob[1]), n);
}

static GEN
vecan_artin(GEN an, long L, long prec)
{
  struct dir_artin d;
  GEN A, Sbad = gel(an,5);
  long n = itos(gel(an,6)), isreal = lg(an)<8 ? 0: !itos(gel(an,7));
  d.nf = gel(an,1); d.G = gel(an,2); d.V = gel(an,3); d.aut = gel(an,4);
  A = lift_shallow(direuler_bad(&d, dirartin, gen_2, stoi(L), NULL, Sbad));
  A = RgXV_RgV_eval(A, grootsof1(n, prec));
  if (isreal) A = real_i(A);
  return A;
}

static GEN
char_expand(GEN conj, GEN ch)
{
  long i, l = lg(conj);
  GEN V = cgetg(l, t_COL);
  for (i=1; i<l; i++) gel(V,i) = gel(ch, conj[i]);
  return V;
}

static GEN
handle_zeta(long n, GEN ch, long *m)
{
  GEN c;
  long t, i, l = lg(ch);
  GEN dim = cyclotoi(vecsum(ch));
  if (typ(dim) != t_INT)
    pari_err_DOMAIN("lfunartin","chi","is not a", strtoGENstr("character"), ch);
  t = itos(dim);
  if (t < 0 || t % n)
    pari_err_DOMAIN("lfunartin","chi","is not a", strtoGENstr("character"), ch);
  if (t == 0) { *m = 0; return ch; }
  *m = t / n;
  c = cgetg(l, t_COL);
  for (i=1; i<l; i++)
    gel(c,i) = gsubgs(gel(ch,i), *m);
  return c;
}

static int
cyclo_is_real(GEN v, GEN ix)
{
  pari_sp av = avma;
  int s = gequal(poleval(lift_shallow(v), ix), v);
  avma = av; return s;
}

static int
char_is_real(GEN ch, GEN mod)
{
  long i, l = lg(ch);
  GEN ix = QXQ_inv(pol_x(varn(mod)), mod);
  for (i=1; i<l; i++)
    if (!cyclo_is_real(gel(ch,i), ix))
      return 0;
  return 1;
}

GEN
lfunartin(GEN nf, GEN gal, GEN ch, long o, long bitprec)
{
  pari_sp av = avma;
  GEN bc, V, aut, mod, Ldata = NULL, chx, cc, conj, repr;
  long tmult, var;
  nf = checknf(nf);
  checkgal(gal);
  var = gvar(ch);
  if (var == 0) pari_err_PRIORITY("lfunartin",ch,"=",0);
  if (var < 0) var = 1;
  if (!is_vec_t(typ(ch))) pari_err_TYPE("lfunartin", ch);
  cc = group_to_cc(gal);
  conj = gel(cc,2);
  repr = gel(cc,3);
  mod = mkpolmod(gen_1, polcyclo(o, var));
  if (lg(ch)>1 && typ(gel(ch,1))==t_MAT)
    chx = artin_charfromgens(gal, gmul(ch,mod));
  else
  {
    if (lg(repr) != lg(ch)) pari_err_DIM("lfunartin");
    chx = char_expand(conj, gmul(ch,mod));
  }
  chx = handle_zeta(nf_get_degree(nf), chx, &tmult);
  ch = shallowextract(chx, repr);
  if (!gequal0(chx))
  {
    GEN real = char_is_real(chx, gel(mod,1))? gen_0: gen_1;
    aut = nfgaloispermtobasis(nf, gal);
    V = gmul(char_expand(conj, galoischarpoly(gal, ch, o)), mod);
    bc = artin_badprimes(nf, gal, aut, chx);
    Ldata = mkvecn(6,
      tag(mkcoln(7, nf, gal, V, aut, gel(bc, 2), stoi(o), real), t_LFUN_ARTIN),
      real, artin_gamma(nf, gal, chx), gen_1, gel(bc,1), gen_0);
  }
  if (tmult==0 && Ldata==NULL) pari_err_TYPE("lfunartin",ch);
  if (tmult)
  {
    long i;
    if (Ldata==NULL) { Ldata = lfunzeta(); tmult--; }
    for(i=1; i<=tmult; i++)
      Ldata = lfunmul(Ldata, gen_1, bitprec);
  }
  return gerepilecopy(av, Ldata);
}

static GEN
lfunzetakinit_artin(GEN nf, GEN gal, GEN dom, long der, long bitprec)
{
  pari_sp ltop = avma;
  GEN To = galoischartable(gal), T = gel(To, 1);
  long o = itos(gel(To, 2));
  GEN F, E, M, domain;
  long i, l = lg(T);
  F = cgetg(l, t_VEC);
  E = cgetg(l, t_VECSMALL);
  for (i = 1; i < l; ++i)
  {
    GEN L = lfunartin(nf, gal, gel(T,i), o, bitprec);
    gel(F, i) = lfuninit(L, dom, der, bitprec);
    E[i] = char_dim(gel(T,i));
  }
  domain = mkvec2(dom, mkvecsmall2(der, bitprec));
  M = mkvec3(F, E, zero_zv(l-1));
  return gerepilecopy(ltop, lfuninit_make(t_LDESC_PRODUCT, lfunzetak_i(nf),
                                          M, domain));
}

/********************************************************************/
/**                    High-level Constructors                     **/
/********************************************************************/
enum { t_LFUNMISC_POL, t_LFUNMISC_CHIQUAD, t_LFUNMISC_CHICONREY,
       t_LFUNMISC_CHIGEN, t_LFUNMISC_ELLINIT, t_LFUNMISC_ETAQUO };
static long
lfundatatype(GEN data)
{
  long l;
  switch(typ(data))
  {
    case t_INT: return t_LFUNMISC_CHIQUAD;
    case t_INTMOD: return t_LFUNMISC_CHICONREY;
    case t_POL: return t_LFUNMISC_POL;
    case t_VEC:
      if (checknf_i(data)) return t_LFUNMISC_POL;
      l = lg(data);
      if (l == 17) return t_LFUNMISC_ELLINIT;
      if (l == 3 && typ(gel(data,1)) == t_VEC) return t_LFUNMISC_CHIGEN;
      break;
  }
  return -1;
}
static GEN
lfunmisc_to_ldata_i(GEN ldata, long shallow)
{
  long lx;
  if (is_linit(ldata)) ldata = linit_get_ldata(ldata);
  lx = lg(ldata);
  if (typ(ldata)==t_VEC && (lx == 7 || lx == 8) && is_tagged(ldata))
  {
    if (!shallow) ldata = gcopy(ldata);
    checkldata(ldata); return ldata;
  }
  switch (lfundatatype(ldata))
  {
    case t_LFUNMISC_POL: return lfunzetak(ldata);
    case t_LFUNMISC_CHIQUAD: return lfunchiquad(ldata);
    case t_LFUNMISC_CHICONREY:
    {
      GEN G = znstar0(gel(ldata,1), 1);
      return lfunchiZ(G, gel(ldata,2));
    }
    case t_LFUNMISC_CHIGEN: return lfunchigen(gel(ldata,1), gel(ldata,2));
    case t_LFUNMISC_ELLINIT: return lfunell(ldata);
  }
  pari_err_TYPE("lfunmisc_to_ldata",ldata);
  return NULL; /* LCOV_EXCL_LINE */
}

GEN
lfunmisc_to_ldata(GEN ldata)
{ return lfunmisc_to_ldata_i(ldata, 0); }

GEN
lfunmisc_to_ldata_shallow(GEN ldata)
{ return lfunmisc_to_ldata_i(ldata, 1); }

/********************************************************************/
/**                    High-level an expansion                     **/
/********************************************************************/
/* van is the output of ldata_get_an: return a_1,...a_L at precision prec */
GEN
ldata_vecan(GEN van, long L, long prec)
{
  GEN an = gel(van, 2);
  long t = mael(van,1,1);
  pari_timer ti;
  if (DEBUGLEVEL >= 1)
    err_printf("Lfun: computing %ld coeffs, prec %ld, type %ld\n", L, prec, t);
  if (DEBUGLEVEL >= 2) timer_start(&ti);
  switch (t)
  {
    long n;
    case t_LFUN_GENERIC:
      an = vecan_closure(an, L, prec);
      n = lg(an)-1;
      if (n < L)
        pari_warn(warner, "#an = %ld < %ld, results may be imprecise", n, L);
      break;
    case t_LFUN_ZETA: an = const_vecsmall(L, 1); break;
    case t_LFUN_NF:  an = dirzetak(an, stoi(L)); break;
    case t_LFUN_ELL: an = ellan(an, L); break;
    case t_LFUN_KRONECKER: an = vecan_Kronecker(an, L); break;
    case t_LFUN_CHIZ: an = vecan_chiZ(an, L, prec); break;
    case t_LFUN_CHIGEN: an = vecan_chigen(an, L, prec); break;
    case t_LFUN_ARTIN: an = vecan_artin(an, L, prec); break;
    case t_LFUN_ETA: an = vecan_eta(an, L); break;
    case t_LFUN_QF: an = vecan_qf(an, L); break;
    case t_LFUN_DIV: an = vecan_div(an, L, prec); break;
    case t_LFUN_MUL: an = vecan_mul(an, L, prec); break;
    case t_LFUN_CONJ: an = vecan_conj(an, L, prec); break;
    case t_LFUN_SYMPOW_ELL: an = vecan_ellsympow(an, L); break;
    case t_LFUN_GENUS2: an = vecan_genus2(an, L); break;
    case t_LFUN_MFCLOS:
    {
      GEN F = gel(an,1), E = gel(an,2), c = gel(an,3);
      an = mfcoefs(F,L,1) + 1; /* skip a_0 */
      an[0] = evaltyp(t_VEC)|evallg(L+1);
      an = mfvecembed(E, an);
      if (!isint1(c)) an = RgV_Rg_mul(an,c);
      break;
    }
    case t_LFUN_TWIST: an = vecan_twist(an, L, prec); break;
    default: pari_err_TYPE("ldata_vecan", van);
  }
  if (DEBUGLEVEL >= 2) timer_printf(&ti, "ldata_vecan");
  return an;
}
