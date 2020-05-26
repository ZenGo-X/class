/* Copyright (C) 2000-2003  The PARI group.

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

/********************************************************************/
/**                                                                **/
/**                          MEMBER FUNCTIONS                      **/
/**                                                                **/
/********************************************************************/
INLINE int
is_ell5(GEN x) {
  long lx;
  if (typ(x) != t_VEC) return 0;
  lx = lg(x);
  return lx == 17 || (lx == 6 && !is_vec_t(typ(gel(x,2))));
}
INLINE int is_ell(GEN x) {
  long lx = lg(x);
  return (typ(x) == t_VEC && lx == 17);
}

static void
member_err(const char *s, GEN y) { pari_err_TYPE(s,y); }

GEN
member_e(GEN x)
{
  GEN y = get_prid(x);
  if (!y) member_err("e",x);
  return gel(y,3);
}

GEN
member_f(GEN x)
{
  GEN y = get_prid(x);
  if (!y)
  {
    if (typ(x) == t_FFELT) return utoipos(FF_f(x));
    member_err("f",x);
  }
  return gel(y,4);
}

GEN
member_p(GEN x)
{
  long t; (void)get_nf(x,&t);
  switch(t)
  {
    case typ_GAL: return gal_get_p(x);
    case typ_ELL: switch(ell_get_type(x))
    {
      case t_ELL_Fp:
      case t_ELL_Fq: return ellff_get_p(x);
      case t_ELL_Qp: return ellQp_get_p(x);
      default: member_err("p",x);
    }
    case typ_MODPR: x = get_prid(x);
    case typ_PRID: return pr_get_p(x);
  }
  switch(typ(x)) {
    case t_PADIC: return gel(x,2);
    case t_FFELT: return FF_p_i(x);
  }
  member_err("p",x);
  return NULL;
}

GEN
member_bid(GEN x)
{
  long t; (void)get_nf(x,&t);
  switch(t) {
    case typ_BNR: return bnr_get_bid(x);
    case typ_BIDZ:
    case typ_BID: return x;
  }
  member_err("bid",x);
  return NULL;
}

GEN
member_bnf(GEN x)
{
  long t; GEN y = get_bnf(x,&t);
  if (!y) {
    if (t == typ_ELL && ell_get_type(x) == t_ELL_NF)
    {
      y = ellnf_get_bnf(x);
      if (y) return y;
    }
    member_err("bnf",x);
  }
  return y;
}

GEN
member_nf(GEN x)
{
  long t; GEN y = get_nf(x,&t);
  if (!y) {
    if (t == typ_RNF) return gel(x,10);
    if (t == typ_ELL && ell_get_type(x) == t_ELL_NF) return ellnf_get_nf(x);
    member_err("nf",x);
  }
  return y;
}

/* integral basis */
GEN
member_zk(GEN x)
{
  long t; GEN y = get_nf(x,&t);
  if (!y)
  {
    switch(t)
    {
      case typ_Q:
        y = cgetg(3,t_VEC);
        gel(y,1) = gen_1;
        gel(y,2) = pol_x(varn(gel(x,1))); return y;
      case typ_RNF:
        return gel(x,7);
    }
    member_err("zk",x);
  }
  return nf_get_zk(y);
}

GEN
member_disc(GEN x) /* discriminant */
{
  long t; GEN y = get_nf(x,&t);
  if (!y)
  {
    switch(t)
    {
      case typ_Q  : return quad_disc(x);
      case typ_ELL: return ell_get_disc(x);
      case typ_RNF: return rnf_get_disc(x);
    }
    member_err("disc",x);
  }
  return nf_get_disc(y);
}

GEN
member_pol(GEN x) /* polynomial */
{
  long t; GEN y = get_nf(x,&t);
  if (!y)
  {
    switch(t)
    {
      case typ_POL: return x;
      case typ_Q  : return gel(x,1);
      case typ_GAL: return gal_get_pol(x);
      case typ_RNF: return rnf_get_pol(x);
    }
    if (typ(x)==t_POLMOD) return gel(x,2);
    if (typ(x)==t_FFELT) return FF_to_FpXQ(x);
    member_err("pol",x);
  }
  return nf_get_pol(y);
}

GEN
member_polabs(GEN x)
{
  long t; (void)get_nf(x,&t);
  if (t != typ_RNF) member_err("pol",x);
  return rnf_get_polabs(x);
}

GEN
member_mod(GEN x) /* modulus */
{
  long t; (void)get_nf(x,&t);
  switch(t) {
    case typ_GAL: return gal_get_mod(x);
    case typ_BNR: return bnr_get_mod(x);
    case typ_BIDZ: return bid_get_ideal(x);
    case typ_BID: return bid_get_mod(x);
  }
  switch(typ(x))
  {
    case t_INTMOD: case t_POLMOD: case t_QUAD: break;
    case t_PADIC: return gel(x,3);
    case t_FFELT: return FF_mod(x);
    case t_VEC:
      if (checkmf_i(x))
      {
        GEN T = mf_get_field(x), CHI = mf_get_CHI(x), P = mfcharpol(CHI);
        return (degpol(T) == 1)? P: (degpol(P) > 1? gmodulo(T, P): T);
      }
      else if (checkMF_i(x))
        return mfcharpol(MF_get_CHI(x));
    default: member_err("mod",x);
  }
  return gel(x,1);
}

GEN
member_sign(GEN x) /* signature */
{
  long t; GEN y = get_nf(x,&t);
  if (!y) member_err("sign",x);
  return gel(y,2);
}
GEN
member_r1(GEN x) { return gel(member_sign(x), 1); }
GEN
member_r2(GEN x) { return gel(member_sign(x), 2); }

GEN
member_index(GEN x)
{
  long t; GEN y = get_nf(x,&t);
  if (!y)
  {
    if (t == typ_RNF) return rnf_get_index(x);
    member_err("index",x);
  }
  return nf_get_index(y);
}

/* x assumed to be output by get_nf: ie a t_VEC with length 11 */
static GEN
nfmats(GEN x)
{
  GEN y;
  if (!x) return NULL;
  y = gel(x,5);
  if (typ(y) == t_VEC && lg(y) < 8) return NULL;
  return y;
}

GEN
member_t2(GEN x) /* T2 matrix */
{
  long t; GEN y = nfmats(get_nf(x,&t));
  if (!y) member_err("t2",x);
  return gram_matrix(gel(y,2));
}

GEN
member_diff(GEN x) /* different */
{
  long t; GEN y = nfmats(get_nf(x,&t));
  if (!y) member_err("diff",x);
  return gel(y,5);
}

GEN
member_codiff(GEN x) /* codifferent */
{
  long t;
  GEN T, d, Di, nf = get_nf(x,&t), y = nfmats(nf);
  if (!y) member_err("codiff",x);
  T = gel(y,4);
  Di = ZM_inv(T, &d); if (!d) return matid(lg(Di)-1);
  return RgM_Rg_div(ZM_hnfmodid(Di, d), d);
}

GEN
member_roots(GEN x) /* roots */
{
  long t; GEN y = get_nf(x,&t);
  if (!y)
  {
    if (t == typ_GAL) return gal_get_roots(x);
    if (t == typ_ELL)
      switch(ell_get_type(x))
      {
        case t_ELL_Qp: return mkcol( ellQp_root(x, ellQp_get_prec(x)) );
        case t_ELL_Q:
        case t_ELL_Rg: return ellR_roots(x, ellR_get_prec(x));
      }
    member_err("roots",x);
  }
  return nf_get_roots(y);
}

/* assume x output by get_bnf: ie a t_VEC with length 10 */
static GEN
check_RES(GEN x, const char *s)
{
  GEN y = gel(x,8);
  if (typ(y) != t_VEC || lg(y) < 4) member_err(s,x);
  return y;
}

/* y = get_bnf(x, &t) */
static GEN
_member_clgp(GEN x, GEN y, long t) /* class group (3-component row vector) */
{
  if (!y)
  {
    switch(t)
    {
      case typ_QUA: return mkvec3(gel(x,1), gel(x,2), gel(x,3));
      case typ_BIDZ:
      case typ_BID: return gel(x,2);
    }
    if (typ(x)==t_VEC)
      switch(lg(x))
      {
        case 3: /* no gen */
        case 4: return x;
      }
    member_err("clgp",x);
  }
  if (t==typ_BNR) return gel(x,5);
  y = check_RES(y, "clgp"); return gel(y,1);
}
static GEN
_check_clgp(GEN x, GEN y, long t)
{ GEN c = _member_clgp(x,y,t); checkabgrp(c); return c; }
GEN
member_clgp(GEN x)
{ long t; GEN y = get_bnf(x,&t); return _check_clgp(x,y,t); }

GEN
member_reg(GEN x) /* regulator */
{
  long t; GEN y = get_bnf(x,&t);
  if (!y)
  {
    if (t == typ_QUA) return gel(x,4);
    member_err("reg",x);
  }
  if (t == typ_BNR) pari_err_IMPL("ray regulator");
  y = check_RES(y, "reg");
  return gel(y,2);
}

GEN
member_fu(GEN x) /* fundamental units */
{
  long t; GEN y = get_bnf(x,&t);
  if (!y)
  {
    switch(t)
    {
      case typ_Q:
        x = quad_disc(x);
        return (signe(x)<0)? cgetg(1,t_VEC): quadunit(x);
    }
    member_err("fu",x);
  }
  if (t == typ_BNR) pari_err_IMPL("ray units");
  return matbasistoalg(y, bnf_get_fu(y));
}

/* torsion units. return [w,e] where w is the number of roots of 1, and e a
 * polmod (or integer) generator */
GEN
member_tu(GEN x)
{
  long t; GEN bnf = get_bnf(x,&t), res = cgetg(3,t_VEC);
  if (!bnf)
  {
    GEN y;
    if (t != typ_Q) member_err("tu",x);
    y = quad_disc(x);
    if (signe(y) > 0 || abscmpiu(y,4) > 0) return mkvec2(gen_m1, gen_2);

    gel(res,1) = utoipos((itos(y) == -4)? 4: 6);
    gel(res,2) = gcopy(x);
  }
  else
  {
    GEN z = bnf_get_tuU(bnf);
    if (t == typ_BNR) pari_err_IMPL("ray torsion units");
    gel(res,1) = utoipos( bnf_get_tuN(bnf) );
    gel(res,2) = typ(z)==t_INT? gen_m1: basistoalg(bnf,z);
  }
  return res;
}

GEN
member_futu(GEN x) /*  concatenation of fu and tu, w is lost */
{
  return shallowconcat(member_fu(x), gel(member_tu(x),2));
}

GEN
member_tufu(GEN x) /*  concatenation of tu and fu, w is lost */
{
  return shallowconcat(gel(member_tu(x),2), member_fu(x));
}

/* structure of (Z_K/m)^*, where x is an idealstarinit (with or without gen)
 * or a bnrinit (with or without gen) */
GEN
member_zkst(GEN x)
{
  long t; (void)get_nf(x,&t);
  switch(t)
  {
    case typ_BIDZ:
    case typ_BID: return bid_get_grp(x);
    case typ_BNR: {
      GEN bid = bnr_get_bid(x);
      if (typ(bid) == t_VEC && lg(bid) > 2) return bid_get_grp(bid);
    }
  }
  member_err("zkst",x);
  return NULL; /* LCOV_EXCL_LINE */
}

GEN
member_no(GEN x) /* number of elements of a group (of type clgp) */
{
  pari_sp av = avma;
  long t; GEN y = get_bnf(x,&t);
  if (t == typ_ELL) switch(ell_get_type(x))
  {
    case t_ELL_Fp:
    case t_ELL_Fq: return ellcard(x, NULL);
  }
  x = _check_clgp(x,y,t);
  avma = av; return gel(x,1);
}

GEN
member_cyc(GEN x) /* cyclic decomposition (SNF) of a group (of type clgp) */
{
  pari_sp av = avma;
  long t; GEN y = get_bnf(x,&t);
  if (t == typ_ELL) switch(ell_get_type(x))
  {
    case t_ELL_Fp:
    case t_ELL_Fq: return ellgroup(x, NULL);
  }
  x = _check_clgp(x,y,t);
  avma = av; return gel(x,2);
}

/* SNF generators of a group (of type clgp), or generators of a prime
 * ideal */
GEN
member_gen(GEN x)
{
  pari_sp av;
  long t; GEN y = get_bnf(x,&t);
  switch(t)
  {
    case typ_MODPR: x = get_prid(x);
    case typ_PRID: return mkvec2(gel(x,1), gel(x,2));
    case typ_GAL: return gal_get_gen(x);
    case typ_ELL: return ellgenerators(x);
  }
  av = avma;
  x = _check_clgp(x,y,t);
  if (lg(x)!=4) member_err("gen",x);
  avma = av; return gel(x,3);
}
GEN
member_group(GEN x)
{
  long t; (void)get_nf(x,&t);
  if (t == typ_GAL) return gal_get_group(x);
  if (t == typ_ELL) return ellgroup0(x, NULL, 1);
  member_err("group",x);
  return NULL; /* LCOV_EXCL_LINE */
}
GEN
member_orders(GEN x)
{
  long t; (void)get_nf(x,&t);
  if (t == typ_GAL) return gal_get_orders(x);
  member_err("orders",x);
  return NULL; /* LCOV_EXCL_LINE */
}

GEN
member_a1(GEN x)
{
  if (!is_ell5(x)) member_err("a1",x);
  return ell_get_a1(x);
}

GEN
member_a2(GEN x)
{
  if (!is_ell5(x)) member_err("a2",x);
  return ell_get_a2(x);
}

GEN
member_a3(GEN x)
{
  if (!is_ell5(x)) member_err("a3",x);
  return ell_get_a3(x);
}

GEN
member_a4(GEN x)
{
  if (!is_ell5(x)) member_err("a4",x);
  return ell_get_a4(x);
}

GEN
member_a6(GEN x)
{
  if (!is_ell5(x)) member_err("a6",x);
  return ell_get_a6(x);
}

GEN
member_b2(GEN x)
{
  if (!is_ell(x)) member_err("b2",x);
  return ell_get_b2(x);
}

GEN
member_b4(GEN x)
{
  if (!is_ell(x)) member_err("b4",x);
  return ell_get_b4(x);
}

GEN
member_b6(GEN x)
{
  if (!is_ell(x)) member_err("b6",x);
  return ell_get_b6(x);
}

GEN
member_b8(GEN x)
{
  if (!is_ell(x)) member_err("b8",x);
  return ell_get_b8(x);
}

GEN
member_c4(GEN x)
{
  if (!is_ell(x)) member_err("c4",x);
  return ell_get_c4(x);
}

GEN
member_c6(GEN x)
{
  if (!is_ell(x)) member_err("c6",x);
  return ell_get_c6(x);
}

GEN
member_j(GEN x)
{
  if (!is_ell(x)) member_err("j",x);
  return ell_get_j(x);
}

static int
ell_is_complex(GEN x)
{ long t = ell_get_type(x); return t == t_ELL_Q || t == t_ELL_Rg; }

static long
ellnf_get_prec(GEN x) { return nf_get_prec(ellnf_get_nf(x)); }

GEN
member_omega(GEN x)
{
  if (!is_ell(x)) member_err("omega",x);
  if (ell_get_type(x)==t_ELL_NF)
    return ellnf_vecomega(x, ellnf_get_prec(x));
  if (!ell_is_complex(x)) pari_err_TYPE("omega [not defined over C]",x);
  return ellR_omega(x, ellR_get_prec(x));
}

GEN
member_eta(GEN x)
{
  if (!is_ell(x)) member_err("eta",x);
  if (ell_get_type(x)==t_ELL_NF)
    return ellnf_veceta(x, ellnf_get_prec(x));
  if (!ell_is_complex(x)) pari_err_TYPE("eta [not defined over C]",x);
  return ellR_eta(x, ellR_get_prec(x));
}

GEN
member_area(GEN x)
{
  if (!is_ell(x)) member_err("area",x);
  if (ell_get_type(x)==t_ELL_NF)
    return ellnf_vecarea(x, ellnf_get_prec(x));
  if (!ell_is_complex(x)) pari_err_TYPE("area [not defined over C]",x);
  return ellR_area(x, ellR_get_prec(x));
}

GEN
member_tate(GEN x)
{
  long prec;
  if (!is_ell(x)) member_err("tate",x);
  if (ell_get_type(x) != t_ELL_Qp)
    pari_err_TYPE("tate [not defined over Qp]",x);
  prec = ellQp_get_prec(x);
  return ellQp_Tate_uniformization(x, prec);
}
