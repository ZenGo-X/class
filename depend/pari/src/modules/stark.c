/* Copyright (C) 2000  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/*******************************************************************/
/*                                                                 */
/*        COMPUTATION OF STARK UNITS OF TOTALLY REAL FIELDS        */
/*                                                                 */
/*******************************************************************/
#include "pari.h"
#include "paripriv.h"

static const long EXTRA_PREC = DEFAULTPREC-2;

/* ComputeCoeff */
typedef struct {
  GEN L0, L1, L11, L2; /* VECSMALL of p */
  GEN L1ray, L11ray; /* precomputed isprincipalray(pr), pr | p */
  GEN rayZ; /* precomputed isprincipalray(i), i < condZ */
  long condZ; /* generates cond(bnr) \cap Z, assumed small */
} LISTray;

/* Char evaluation */
typedef struct {
  long ord;
  GEN *val, chi;
} CHI_t;

/* RecCoeff */
typedef struct {
  GEN M, beta, B, U, nB;
  long v, G, N;
} RC_data;

/********************************************************************/
/*                    Miscellaneous functions                       */
/********************************************************************/
static GEN
chi_get_c(GEN chi) { return gmael(chi,1,2); }
static GEN
chi_get_gdeg(GEN chi) { return gmael(chi,1,1); }
static long
chi_get_deg(GEN chi) { return itou(chi_get_gdeg(chi)); }

/* Compute the image of logelt by character chi, as a complex number */
static ulong
CharEval_n(GEN chi, GEN logelt)
{
  GEN gn = ZV_dotproduct(chi_get_c(chi), logelt);
  return umodiu(gn, chi_get_deg(chi));
}
/* Compute the image of logelt by character chi, as a complex number */
static GEN
CharEval(GEN chi, GEN logelt)
{
  ulong n = CharEval_n(chi, logelt), d = chi_get_deg(chi);
  long nn = Fl_center(n,d,d>>1);
  GEN x = gel(chi,2);
  x = gpowgs(x, labs(nn));
  if (nn < 0) x = conj_i(x);
  return x;
}

/* return n such that C(elt) = z^n */
static ulong
CHI_eval_n(CHI_t *C, GEN logelt)
{
  GEN n = ZV_dotproduct(C->chi, logelt);
  return umodiu(n, C->ord);
}
/* return C(elt) */
static GEN
CHI_eval(CHI_t *C, GEN logelt)
{
  return C->val[CHI_eval_n(C, logelt)];
}

static void
init_CHI(CHI_t *c, GEN CHI, GEN z)
{
  long i, d = chi_get_deg(CHI);
  GEN *v = (GEN*)new_chunk(d);
  v[0] = gen_1;
  if (d != 1)
  {
    v[1] = z;
    for (i=2; i<d; i++) v[i] = gmul(v[i-1], z);
  }
  c->chi = chi_get_c(CHI);
  c->ord = d;
  c->val = v;
}
/* as t_POLMOD */
static void
init_CHI_alg(CHI_t *c, GEN CHI) {
  long d = chi_get_deg(CHI);
  GEN z;
  switch(d)
  {
    case 1: z = gen_1; break;
    case 2: z = gen_m1; break;
    default: z = mkpolmod(pol_x(0), polcyclo(d,0));
  }
  init_CHI(c,CHI, z);
}
/* as t_COMPLEX */
static void
init_CHI_C(CHI_t *c, GEN CHI) {
  init_CHI(c,CHI, gel(CHI,2));
}

typedef struct {
  long r; /* rank = lg(gen) */
  GEN j; /* current elt is gen[1]^j[1] ... gen[r]^j[r] */
  GEN cyc; /* t_VECSMALL of elementary divisors */
} GROUP_t;

static int
NextElt(GROUP_t *G)
{
  long i = 1;
  if (G->r == 0) return 0; /* no more elt */
  while (++G->j[i] == G->cyc[i]) /* from 0 to cyc[i]-1 */
  {
    G->j[i] = 0;
    if (++i > G->r) return 0; /* no more elt */
  }
  return i; /* we have multiplied by gen[i] */
}

/* Compute all the elements of a group given by its SNF */
static GEN
EltsOfGroup(long order, GEN cyc)
{
  long i;
  GEN rep;
  GROUP_t G;

  G.cyc = gtovecsmall(cyc);
  G.r = lg(cyc)-1;
  G.j = zero_zv(G.r);

  rep = cgetg(order + 1, t_VEC);
  gel(rep,order) = vecsmall_to_col(G.j);

  for  (i = 1; i < order; i++)
  {
    (void)NextElt(&G);
    gel(rep,i) = vecsmall_to_col(G.j);
  }
  return rep;
}

/* enumerate all group elements */
GEN
cyc2elts(GEN cyc)
{
  long i, n;
  GEN z;
  GROUP_t G;

  G.cyc = typ(cyc)==t_VECSMALL? cyc: gtovecsmall(cyc);
  n = zv_prod(G.cyc);
  G.r = lg(cyc)-1;
  G.j = zero_zv(G.r);

  z = cgetg(n+1, t_VEC);
  gel(z,n) = leafcopy(G.j); /* trivial elt comes last */
  for  (i = 1; i < n; i++)
  {
    (void)NextElt(&G);
    gel(z,i) = leafcopy(G.j);
  }
  return z;
}

/* Let Qt as given by InitQuotient, compute a system of
   representatives of the quotient */
static GEN
ComputeLift(GEN Qt)
{
  GEN e, U = gel(Qt,3);
  long i, h = itos(gel(Qt,1));

  e = EltsOfGroup(h, gel(Qt,2));
  if (!RgM_isidentity(U))
  {
    GEN Ui = ZM_inv(U,NULL);
    for (i = 1; i <= h; i++) gel(e,i) = ZM_ZC_mul(Ui, gel(e,i));
  }
  return e;
}

/* nchi: a character given by a vector [d, (c_i)], e.g. from char_normalize
 * such that chi(x) = e((c . log(x)) / d) where log(x) on bnr.gen */
static GEN
get_Char(GEN nchi, long prec)
{ return mkvec2(nchi, rootsof1_cx(gel(nchi,1), prec)); }

/* prime divisors of conductor */
static GEN
divcond(GEN bnr) {GEN bid = bnr_get_bid(bnr); return gel(bid_get_fact(bid),1);}

/* vector of prime ideals dividing bnr but not bnrc */
static GEN
get_prdiff(GEN bnr, GEN condc)
{
  GEN prdiff, M = gel(condc,1), D = divcond(bnr), nf = bnr_get_nf(bnr);
  long nd, i, l  = lg(D);
  prdiff = cgetg(l, t_COL);
  for (nd=1, i=1; i < l; i++)
    if (!idealval(nf, M, gel(D,i))) gel(prdiff,nd++) = gel(D,i);
  setlg(prdiff, nd); return prdiff;
}

#define ch_C(x)    gel(x,1)
#define ch_bnr(x)  gel(x,2)
#define ch_4(x)    gel(x,3)
#define ch_CHI(x)  gel(x,4)
#define ch_diff(x) gel(x,5)
#define ch_cond(x) gel(x,6)
#define ch_CHI0(x) gel(x,7)
#define ch_comp(x) gel(x,8)
static long
ch_deg(GEN dtcr) { return chi_get_deg(ch_CHI(dtcr)); }

static GEN
GetDeg(GEN dataCR)
{
  long i, l = lg(dataCR);
  GEN degs = cgetg(l, t_VECSMALL);
  for (i = 1; i < l; i++) degs[i] = eulerphiu(ch_deg(gel(dataCR,i)));
  return degs;
}

/********************************************************************/
/*                    1rst part: find the field K                   */
/********************************************************************/
static GEN AllStark(GEN data, GEN nf, long flag, long prec);

/* Columns of C [HNF] give the generators of a subgroup of the finite abelian
 * group A [ in terms of implicit generators ], compute data to work in A/C:
 * 1) order
 * 2) structure
 * 3) the matrix A ->> A/C
 * 4) the subgroup C */
static GEN
InitQuotient(GEN C)
{
  GEN U, D = ZM_snfall_i(C, &U, NULL, 1), h = ZV_prod(D);
  return mkvec5(h, D, U, C, cyc_normalize(D));
}

/* lift chi character on A/C [Qt from InitQuotient] to character on A [cyc]*/
static GEN
LiftChar(GEN Qt, GEN cyc, GEN chi)
{
  GEN ncyc = gel(Qt,5), U = gel(Qt,3);
  GEN nchi = char_normalize(chi, ncyc);
  GEN c = ZV_ZM_mul(gel(nchi,2), U), d = gel(nchi,1);
  return char_denormalize(cyc, d, c);
}

/* Let s: A -> B given by P, and let cycA, cycB be the cyclic structure of
 * A and B, compute the kernel of s. */
static GEN
ComputeKernel0(GEN P, GEN cycA, GEN cycB)
{
  pari_sp av = avma;
  long nbA = lg(cycA)-1, rk;
  GEN U, DB = diagonal_shallow(cycB);

  rk = nbA + lg(cycB) - lg(ZM_hnfall_i(shallowconcat(P, DB), &U, 1));
  U = matslice(U, 1,nbA, 1,rk);
  return gerepileupto(av, ZM_hnfmodid(U, cycA));
}

/* Let m and n be two moduli such that n|m and let C be a congruence
   group modulo n, compute the corresponding congruence group modulo m
   ie the kernel of the map Clk(m) ->> Clk(n)/C */
static GEN
ComputeKernel(GEN bnrm, GEN bnrn, GEN dtQ)
{
  pari_sp av = avma;
  GEN P = ZM_mul(gel(dtQ,3), bnrsurjection(bnrm, bnrn));
  return gerepileupto(av, ComputeKernel0(P, bnr_get_cyc(bnrm), gel(dtQ,2)));
}

static long
cyc_is_cyclic(GEN cyc) { return lg(cyc) <= 2 || equali1(gel(cyc,2)); }

/* Let H be a subgroup of cl(bnr)/sugbroup, return 1 if
   cl(bnr)/subgoup/H is cyclic and the signature of the
   corresponding field is equal to sig and no finite prime
   dividing cond(bnr) is totally split in this field. Return 0
   otherwise. */
static long
IsGoodSubgroup(GEN H, GEN bnr, GEN map)
{
  pari_sp av = avma;
  GEN mod, modH, p1, p2, U, P, PH, bnrH, iH, qH;
  long j;

  p1 = InitQuotient(H);
  /* quotient is non cyclic */
  if (!cyc_is_cyclic(gel(p1,2))) { avma = av; return 0; }

  p2 = ZM_hnfall_i(shallowconcat(map,H), &U, 0);
  setlg(U, lg(H));
  for (j = 1; j < lg(U); j++) setlg(gel(U,j), lg(H));
  p1 = ZM_hnfmodid(U, bnr_get_cyc(bnr)); /* H as a subgroup of bnr */
  modH = bnrconductor_i(bnr, p1, 0);
  mod  = bnr_get_mod(bnr);

  /* is the signature correct? */
  if (!gequal(gel(modH,2), gel(mod,2))) { avma = av; return 0; }

  /* finite part are the same: OK */
  if (gequal(gel(modH,1), gel(mod,1))) { avma = av; return 1; }

  /* need to check the splitting of primes dividing mod but not modH */
  bnrH = Buchray(bnr, modH, nf_INIT);
  P = divcond(bnr);
  PH = divcond(bnrH);
  p2 = ZM_mul(bnrsurjection(bnr, bnrH), p1);
  /* H as a subgroup of bnrH */
  iH = ZM_hnfmodid(p2,  bnr_get_cyc(bnrH));
  qH = InitQuotient(iH);
  for (j = 1; j < lg(P); j++)
  {
    GEN pr = gel(P, j), e;
    /* if pr divides modH, it is ramified, so it's good */
    if (tablesearch(PH, pr, cmp_prime_ideal)) continue;
    /* inertia degree of pr in bnr(modH)/H is charorder(e, cycH) */
    e = ZM_ZC_mul(gel(qH,3), isprincipalray(bnrH, pr));
    e = vecmodii(e, gel(qH,2));
    if (ZV_equal0(e)) { avma = av; return 0; } /* f = 1 */
  }
  avma = av; return 1;
}

/* compute the list of characters to consider for AllStark and
   initialize precision-independent data to compute with them */
static GEN
get_listCR(GEN bnr, GEN dtQ)
{
  GEN listCR, vecchi, Mr;
  long hD, h, nc, i, tnc;
  hashtable *S;

  Mr = bnr_get_cyc(bnr);
  hD = itos(gel(dtQ,1));
  h  = hD >> 1;

  listCR = cgetg(h+1, t_VEC); /* non-conjugate chars */
  nc = tnc = 1;
  vecchi = EltsOfGroup(hD, gel(dtQ,2));
  S = hash_create(h, (ulong(*)(void*))&hash_GEN,
                     (int(*)(void*,void*))&ZV_equal, 1);
  for (i = 1; tnc <= h; i++)
  { /* lift a character of D in Clk(m) */
    GEN cond, lchi = LiftChar(dtQ, Mr, gel(vecchi,i));
    if (hash_search(S, lchi)) continue;
    cond = bnrconductorofchar(bnr, lchi);
    if (gequal0(gel(cond,2))) continue;
    /* the infinite part of chi is non trivial */
    gel(listCR,nc++) = mkvec2(lchi, cond);

    /* if chi is not real, add its conjugate character to S */
    if (absequaliu(charorder(Mr,lchi), 2)) tnc++;
    else
    {
      hash_insert(S, charconj(Mr, lchi), (void*)1);
      tnc+=2;
    }
  }
  setlg(listCR, nc); return listCR;
}

static GEN InitChar(GEN bnr, GEN listCR, long prec);

/* Given a conductor and a subgroups, return the corresponding
   complexity and precision required using quickpol. Fill data[5] with
   listCR */
static long
CplxModulus(GEN data, long *newprec)
{
  long pr, ex, dprec = DEFAULTPREC;
  pari_sp av;
  GEN pol, listCR, cpl, bnr = gel(data,1), nf = checknf(bnr);

  listCR = get_listCR(bnr, gel(data,3));
  for (av = avma;; avma = av)
  {
    gel(data,5) = InitChar(bnr, listCR, dprec);
    pol = AllStark(data, nf, -1, dprec);
    pr = nbits2extraprec( gexpo(pol) );
    if (pr < 0) pr = 0;
    dprec = maxss(dprec, pr) + EXTRA_PREC;
    if (!gequal0(leading_coeff(pol)))
    {
      cpl = RgX_fpnorml2(pol, DEFAULTPREC);
      if (!gequal0(cpl)) break;
    }
    if (DEBUGLEVEL>1) pari_warn(warnprec, "CplxModulus", dprec);
  }
  ex = gexpo(cpl); avma = av;
  if (DEBUGLEVEL>1) err_printf("cpl = 2^%ld\n", ex);

  gel(data,5) = listCR;
  *newprec = dprec; return ex;
}

/* return A \cap B in abelian group defined by cyc. NULL = whole group */
static GEN
subgp_intersect(GEN cyc, GEN A, GEN B)
{
  GEN H, U;
  long k, lH;
  if (!A) return B;
  if (!B) return A;
  H = ZM_hnfall_i(shallowconcat(A,B), &U, 1);
  setlg(U, lg(A)); lH = lg(H);
  for (k = 1; k < lg(U); k++) setlg(gel(U,k), lH);
  return ZM_hnfmodid(ZM_mul(A,U), cyc);
}

 /* Let f be a conductor without infinite part and let C be a
   congruence group modulo f, compute (m,D) such that D is a
   congruence group of conductor m where m is a multiple of f
   divisible by all the infinite places but one, D is a subgroup of
   index 2 of Im(C) in Clk(m), and m is such that the intersection
   of the subgroups H of Clk(m)/D such that the quotient is
   cyclic and no prime divding m, but the one infinite prime, is
   totally split in the extension corresponding to H is trivial.
   Return bnr(m), D, the quotient Ck(m)/D and Clk(m)/Im(C) */
static GEN
FindModulus(GEN bnr, GEN dtQ, long *newprec)
{
  const long limnorm = 400;
  long n, i, narch, maxnorm, minnorm, N;
  long first = 1, pr, rb, oldcpl = -1, iscyc;
  pari_sp av = avma;
  GEN bnf, nf, f, arch, m, rep = NULL;

  bnf = bnr_get_bnf(bnr);
  nf  = bnf_get_nf(bnf);
  N   = nf_get_degree(nf);
  f   = gel(bnr_get_mod(bnr), 1);

  /* if cpl < rb, it is not necessary to try another modulus */
  rb = expi( powii(mulii(nf_get_disc(nf), ZM_det_triangular(f)), gmul2n(bnr_get_no(bnr), 3)) );

  /* Initialization of the possible infinite part */
  arch = const_vec(N, gen_1);

  /* narch = (N == 2)? 1: N; -- if N=2, only one case is necessary */
  narch = N;
  m = mkvec2(NULL, arch);

  /* go from minnorm up to maxnorm. If necessary, increase these values.
   * If we cannot find a suitable conductor of norm < limnorm, stop */
  maxnorm = 50;
  minnorm = 1;

  /* if the extension is cyclic then we _must_ find a suitable conductor */
  iscyc = cyc_is_cyclic(gel(dtQ,2));

  if (DEBUGLEVEL>1)
    err_printf("Looking for a modulus of norm: ");

  for(;;)
  {
    GEN listid = ideallist0(nf, maxnorm, 4+8); /* ideals of norm <= maxnorm */
    pari_sp av1 = avma;
    for (n = minnorm; n <= maxnorm; n++, avma = av1)
    {
      GEN idnormn = gel(listid,n);
      long nbidnn  = lg(idnormn) - 1;
      if (DEBUGLEVEL>1) err_printf(" %ld", n);
      for (i = 1; i <= nbidnn; i++)
      { /* finite part of the conductor */
        long s;

        gel(m,1) = idealmul(nf, f, gel(idnormn,i));
        for (s = 1; s <= narch; s++)
        { /* infinite part */
          GEN candD, ImC, bnrm;
          long nbcand, c;
          gel(arch,N+1-s) = gen_0;

          /* compute Clk(m), check if m is a conductor */
          bnrm = Buchray(bnf, m, nf_INIT);
          c = bnrisconductor(bnrm, NULL);
          gel(arch,N+1-s) = gen_1;
          if (!c) continue;

          /* compute Im(C) in Clk(m)... */
          ImC = ComputeKernel(bnrm, bnr, dtQ);

          /* ... and its subgroups of index 2 with conductor m */
          candD = subgrouplist_cond_sub(bnrm, ImC, mkvec(gen_2));
          nbcand = lg(candD) - 1;
          for (c = 1; c <= nbcand; c++)
          {
            GEN D  = gel(candD,c); /* check if the conductor is suitable */
            long cpl;
            GEN p1 = InitQuotient(D), p2;
            GEN ord = gel(p1,1), cyc = gel(p1,2), map = gel(p1,3);

            if (!cyc_is_cyclic(cyc)) /* cyclic => suitable, else test */
            {
              GEN lH = subgrouplist(cyc, NULL), IK = NULL;
              long j, ok = 0;
              for (j = 1; j < lg(lH); j++)
              {
                GEN H = gel(lH, j), IH = subgp_intersect(cyc, IK, H);
                /* if H > IK, no need to test H */
                if (IK && gidentical(IH, IK)) continue;
                if (IsGoodSubgroup(H, bnrm, map))
                {
                  IK = IH;
                  if (equalii(ord, ZM_det_triangular(IK))) { ok = 1; break; }
                }
              }
              if (!ok) continue;
            }

            p2 = cgetg(6, t_VEC); /* p2[5] filled in CplxModulus */
            gel(p2,1) = bnrm;
            gel(p2,2) = D;
            gel(p2,3) = InitQuotient(D);
            gel(p2,4) = InitQuotient(ImC);
            if (DEBUGLEVEL>1)
              err_printf("\nTrying modulus = %Ps and subgroup = %Ps\n",
                         bnr_get_mod(bnrm), D);
            cpl = CplxModulus(p2, &pr);
            if (oldcpl < 0 || cpl < oldcpl)
            {
              *newprec = pr;
              if (rep) gunclone(rep);
              rep    = gclone(p2);
              oldcpl = cpl;
            }
            if (oldcpl < rb) goto END; /* OK */

            if (DEBUGLEVEL>1) err_printf("Trying to find another modulus...");
            first = 0;
          }
        }
        if (!first) goto END; /* OK */
      }
    }
    /* if necessary compute more ideals */
    minnorm = maxnorm;
    maxnorm <<= 1;
    if (!iscyc && maxnorm > limnorm) return NULL;

  }
END:
  if (DEBUGLEVEL>1)
    err_printf("No, we're done!\nModulus = %Ps and subgroup = %Ps\n",
               bnr_get_mod(gel(rep,1)), gel(rep,2));
  gel(rep,5) = InitChar(gel(rep,1), gel(rep,5), *newprec);
  return gerepilecopy(av, rep);
}

/********************************************************************/
/*                      2nd part: compute W(X)                      */
/********************************************************************/

/* find ilambda s.t. Diff*f*ilambda integral and coprime to f
   and ilambda >> 0 at foo, fa = factorization of f */
static GEN
get_ilambda(GEN nf, GEN fa, GEN foo)
{
  GEN x, w, E2, P = gel(fa,1), E = gel(fa,2), D = nf_get_diff(nf);
  long i, l = lg(P);
  if (l == 1) return gen_1;
  w = cgetg(l, t_VEC);
  E2 = cgetg(l, t_COL);
  for (i = 1; i < l; i++)
  {
    GEN pr = gel(P,i), t = pr_get_tau(pr);
    long e = itou(gel(E,i)), v = idealval(nf, D, pr);
    if (v) { D = idealdivpowprime(nf, D, pr, utoipos(v)); e += v; }
    gel(E2,i) = stoi(e+1);
    if (typ(t) == t_MAT) t = gel(t,1);
    gel(w,i) = gdiv(nfpow(nf, t, stoi(e)), powiu(pr_get_p(pr),e));
  }
  x = mkmat2(P, E2);
  return idealchinese(nf, mkvec2(x, foo), w);
}
/* compute the list of W(chi) such that Ld(s,chi) = W(chi) Ld(1 - s, chi*),
 * for all chi in LCHI. All chi have the same conductor (= cond(bnr)).
 * if check == 0 do not check the result */
static GEN
ArtinNumber(GEN bnr, GEN LCHI, long check, long prec)
{
  long ic, i, j, nz, nChar = lg(LCHI)-1;
  pari_sp av = avma, av2;
  GEN sqrtnc, cond, condZ, cond0, cond1, nf, T;
  GEN cyc, vN, vB, diff, vt, idh, zid, gen, z, nchi;
  GEN indW, W, classe, s0, s, den, ilambda, sarch;
  CHI_t **lC;
  GROUP_t G;

  lC = (CHI_t**)new_chunk(nChar + 1);
  indW = cgetg(nChar + 1, t_VECSMALL);
  W = cgetg(nChar + 1, t_VEC);
  for (ic = 0, i = 1; i <= nChar; i++)
  {
    GEN CHI = gel(LCHI,i);
    if (chi_get_deg(CHI) <= 2) { gel(W,i) = gen_1; continue; }
    ic++; indW[ic] = i;
    lC[ic] = (CHI_t*)new_chunk(sizeof(CHI_t));
    init_CHI_C(lC[ic], CHI);
  }
  if (!ic) return W;
  nChar = ic;

  nf    = bnr_get_nf(bnr);
  diff  = nf_get_diff(nf);
  T     = nf_get_Tr(nf);
  cond  = bnr_get_mod(bnr);
  cond0 = gel(cond,1); condZ = gcoeff(cond0,1,1);
  cond1 = gel(cond,2);

  sqrtnc = gsqrt(idealnorm(nf, cond0), prec);
  ilambda = get_ilambda(nf, bid_get_fact(bnr_get_bid(bnr)), cond1);
  idh = idealmul(nf, ilambda, idealmul(nf, diff, cond0)); /* integral */
  ilambda = Q_remove_denom(ilambda, &den);
  z = den? rootsof1_cx(den, prec): NULL;

  /* compute a system of generators of (Ok/cond)^*, we'll make them
   * cond1-positive in the main loop */
  zid = Idealstar(nf, cond0, nf_GEN);
  cyc = abgrp_get_cyc(zid);
  gen = abgrp_get_gen(zid);
  nz = lg(gen) - 1;
  sarch = nfarchstar(nf, cond0, vec01_to_indices(cond1));

  nchi = cgetg(nChar+1, t_VEC);
  for (ic = 1; ic <= nChar; ic++) gel(nchi,ic) = cgetg(nz + 1, t_VECSMALL);
  for (i = 1; i <= nz; i++)
  {
    if (is_bigint(gel(cyc,i)))
      pari_err_OVERFLOW("ArtinNumber [conductor too large]");
    gel(gen,i) = set_sign_mod_divisor(nf, NULL, gel(gen,i), sarch);
    classe = isprincipalray(bnr, gel(gen,i));
    for (ic = 1; ic <= nChar; ic++) {
      GEN n = gel(nchi,ic);
      n[i] = CHI_eval_n(lC[ic], classe);
    }
  }

  /* Sum chi(beta) * exp(2i * Pi * Tr(beta * ilambda) where beta
     runs through the classes of (Ok/cond0)^* and beta cond1-positive */
  vt = gel(T,1); /* ( Tr(w_i) )_i */
  if (typ(ilambda) == t_COL)
    vt = ZV_ZM_mul(vt, zk_multable(nf, ilambda));
  else
    vt = ZC_Z_mul(vt, ilambda);
  /*vt = den . (Tr(w_i * ilambda))_i */
  G.cyc = gtovecsmall(cyc);
  G.r = nz;
  G.j = zero_zv(nz);
  vN = zero_Flm_copy(nz, nChar);

  av2 = avma;
  vB = const_vec(nz, gen_1);
  s0 = z? powgi(z, modii(gel(vt,1), den)): gen_1; /* for beta = 1 */
  s = const_vec(nChar, s0);

  while ( (i = NextElt(&G)) )
  {
    GEN b = gel(vB,i);
    b = nfmuli(nf, b, gel(gen,i));
    b = typ(b) == t_COL? FpC_red(b, condZ): modii(b, condZ);
    for (j=1; j<=i; j++) gel(vB,j) = b;

    for (ic = 1; ic <= nChar; ic++)
    {
      GEN v = gel(vN,ic), n = gel(nchi,ic);
      v[i] = Fl_add(v[i], n[i], lC[ic]->ord);
      for (j=1; j<i; j++) v[j] = v[i];
    }

    gel(vB,i) = b = set_sign_mod_divisor(nf, NULL, b, sarch);
    if (!z)
      s0 = gen_1;
    else
    {
      b = typ(b) == t_COL? ZV_dotproduct(vt, b): mulii(gel(vt,1),b);
      s0 = powgi(z, modii(b,den));
    }
    for (ic = 1; ic <= nChar; ic++)
    {
      GEN v = gel(vN,ic), val = lC[ic]->val[ v[i] ];
      gel(s,ic) = gadd(gel(s,ic), gmul(val, s0));
    }

    if (gc_needed(av2, 1))
    {
      if (DEBUGMEM > 1) pari_warn(warnmem,"ArtinNumber");
      gerepileall(av2, 2, &s, &vB);
    }
  }

  classe = isprincipalray(bnr, idh);
  z = powIs(- (lg(gel(sarch,1))-1));

  for (ic = 1; ic <= nChar; ic++)
  {
    s0 = gmul(gel(s,ic), CHI_eval(lC[ic], classe));
    s0 = gdiv(s0, sqrtnc);
    if (check && - expo(subrs(gnorm(s0), 1)) < prec2nbits(prec) >> 1)
      pari_err_BUG("ArtinNumber");
    gel(W, indW[ic]) = gmul(s0, z);
  }
  return gerepilecopy(av, W);
}

static GEN
ComputeAllArtinNumbers(GEN dataCR, GEN vChar, int check, long prec)
{
  long j, k, cl = lg(dataCR) - 1, J = lg(vChar)-1;
  GEN W = cgetg(cl+1,t_VEC), WbyCond, LCHI;

  for (j = 1; j <= J; j++)
  {
    GEN LChar = gel(vChar,j), ldata = vecpermute(dataCR, LChar);
    GEN dtcr = gel(ldata,1), bnr = ch_bnr(dtcr);
    long l = lg(LChar);

    if (DEBUGLEVEL>1)
      err_printf("* Root Number: cond. no %ld/%ld (%ld chars)\n", j, J, l-1);
    LCHI = cgetg(l, t_VEC);
    for (k = 1; k < l; k++) gel(LCHI,k) = ch_CHI0(gel(ldata,k));
    WbyCond = ArtinNumber(bnr, LCHI, check, prec);
    for (k = 1; k < l; k++) gel(W,LChar[k]) = gel(WbyCond,k);
  }
  return W;
}
static GEN
SingleArtinNumber(GEN bnr, GEN chi, long prec)
{ return gel(ArtinNumber(bnr, mkvec(chi), 1, prec), 1); }

/* compute the constant W of the functional equation of
   Lambda(chi). If flag = 1 then chi is assumed to be primitive */
GEN
bnrrootnumber(GEN bnr, GEN chi, long flag, long prec)
{
  pari_sp av = avma;
  GEN cyc;

  if (flag < 0 || flag > 1) pari_err_FLAG("bnrrootnumber");
  checkbnr(bnr);
  if (flag)
  {
    cyc = bnr_get_cyc(bnr);
    if (!char_check(cyc,chi)) pari_err_TYPE("bnrrootnumber [character]", chi);
  }
  else
  {
    GEN z = bnrconductor_i(bnr, chi, 2);
    bnr = gel(z,2);
    chi = gel(z,3);
    cyc = bnr_get_cyc(bnr);
  }
  chi = char_normalize(chi, cyc_normalize(cyc));
  chi = get_Char(chi, prec);
  return gerepilecopy(av, SingleArtinNumber(bnr, chi, prec));
}

/********************************************************************/
/*               3rd part: initialize the characters                */
/********************************************************************/

/* Let chi be a character, A(chi) corresponding to the primes dividing diff
   at s = flag. If s = 0, returns [r, A] where r is the order of vanishing
   at s = 0 corresponding to diff. No GC */
static GEN
ComputeAChi(GEN dtcr, long *r, long flag, long prec)
{
  GEN A, diff = ch_diff(dtcr), bnrc = ch_bnr(dtcr), chi  = ch_CHI0(dtcr);
  long i, l = lg(diff);

  A = gen_1; *r = 0;
  for (i = 1; i < l; i++)
  {
    GEN pr = gel(diff,i), B;
    GEN z = CharEval(chi, isprincipalray(bnrc, pr));

    if (flag)
      B = gsubsg(1, gdiv(z, pr_norm(pr)));
    else if (gequal1(z))
    {
      B = glog(pr_norm(pr), prec);
      (*r)++;
    }
    else
      B = gsubsg(1, z);
    A = gmul(A, B);
  }
  return A;
}
/* simplified version of ComputeAchi: return 1 if L(0,chi) = 0 */
static int
L_vanishes_at_0(GEN dtcr)
{
  GEN diff = ch_diff(dtcr), bnrc = ch_bnr(dtcr), chi  = ch_CHI0(dtcr);
  long i, l = lg(diff);

  for (i = 1; i < l; i++)
  {
    GEN pr = gel(diff,i);
    if (! CharEval_n(chi, isprincipalray(bnrc, pr))) return 1;
  }
  return 0;
}

static GEN
_data4(GEN arch, long r1, long r2)
{
  GEN z = cgetg(5, t_VECSMALL);
  long i, b, q = 0;

  for (i=1; i<=r1; i++) if (signe(gel(arch,i))) q++;
  z[1] = q; b = r1 - q;
  z[2] = b;
  z[3] = r2;
  z[4] = maxss(b+r2+1, r2+q);
  return z;
}

/* Given a list [chi, F = cond(chi)] of characters over Cl(bnr), compute a
   vector dataCR containing for each character:
   2: the constant C(F) [t_REAL]
   3: bnr(F)
   4: [q, r1 - q, r2, rc] where
        q = number of real places in F
        rc = max{r1 + r2 - q + 1, r2 + q}
   6: diff(chi) primes dividing m but not F
   7: finite part of F

   1: chi
   5: [(c_i), z, d] in bnr(m)
   8: [(c_i), z, d] in bnr(F)
   9: if NULL then does not compute (for AllStark) */
static GEN
InitChar(GEN bnr, GEN listCR, long prec)
{
  GEN bnf = checkbnf(bnr), nf = bnf_get_nf(bnf);
  GEN modul, dk, C, dataCR, chi, cond, ncyc;
  long N, r1, r2, prec2, i, j, l;
  pari_sp av = avma;

  modul = bnr_get_mod(bnr);
  dk    = nf_get_disc(nf);
  N     = nf_get_degree(nf);
  nf_get_sign(nf, &r1,&r2);
  prec2 = precdbl(prec) + EXTRA_PREC;
  C     = gmul2n(sqrtr_abs(divir(dk, powru(mppi(prec2),N))), -r2);
  ncyc = cyc_normalize( bnr_get_cyc(bnr) );

  dataCR = cgetg_copy(listCR, &l);
  for (i = 1; i < l; i++)
  {
    GEN bnrc, olddtcr, dtcr = cgetg(9, t_VEC);
    gel(dataCR,i) = dtcr;

    chi  = gmael(listCR, i, 1);
    cond = gmael(listCR, i, 2);

    /* do we already know the invariants of chi? */
    olddtcr = NULL;
    for (j = 1; j < i; j++)
      if (gequal(cond, gmael(listCR,j,2))) { olddtcr = gel(dataCR,j); break; }

    if (!olddtcr)
    {
      ch_C(dtcr) = gmul(C, gsqrt(ZM_det_triangular(gel(cond,1)), prec2));
      ch_4(dtcr) = _data4(gel(cond,2),r1,r2);
      ch_cond(dtcr) = cond;
      if (gequal(cond,modul))
      {
        ch_bnr(dtcr) = bnr;
        ch_diff(dtcr) = cgetg(1, t_VEC);
      }
      else
      {
        ch_bnr(dtcr) = Buchray(bnf, cond, nf_INIT);
        ch_diff(dtcr) = get_prdiff(bnr, cond);
      }
    }
    else
    {
      ch_C(dtcr) = ch_C(olddtcr);
      ch_bnr(dtcr) = ch_bnr(olddtcr);
      ch_4(dtcr) = ch_4(olddtcr);
      ch_diff(dtcr) = ch_diff(olddtcr);
      ch_cond(dtcr) = ch_cond(olddtcr);
    }

    chi = char_normalize(chi,ncyc);
    ch_CHI(dtcr) = get_Char(chi, prec2);
    ch_comp(dtcr) = gen_1; /* compute this character (by default) */

    bnrc = ch_bnr(dtcr);
    if (gequal(bnr_get_mod(bnr), bnr_get_mod(bnrc)))
      ch_CHI0(dtcr) = ch_CHI(dtcr);
    else
    {
      chi = bnrchar_primitive(bnr, chi, bnrc);
      ch_CHI0(dtcr) = get_Char(chi, prec2);
    }
  }

  return gerepilecopy(av, dataCR);
}

/* recompute dataCR with the new precision */
static GEN
CharNewPrec(GEN dataCR, GEN nf, long prec)
{
  GEN dk, C;
  long N, l, j, prec2;

  dk    =  nf_get_disc(nf);
  N     =  nf_get_degree(nf);
  prec2 = precdbl(prec) + EXTRA_PREC;

  C = sqrtr(divir(absi_shallow(dk), powru(mppi(prec2), N)));

  l = lg(dataCR);
  for (j = 1; j < l; j++)
  {
    GEN dtcr = gel(dataCR,j), f0 = gel(ch_cond(dtcr),1);
    ch_C(dtcr) = gmul(C, gsqrt(ZM_det_triangular(f0), prec2));

    gmael(ch_bnr(dtcr), 1, 7) = nf;

    ch_CHI( dtcr) = get_Char(gel(ch_CHI(dtcr), 1), prec2);
    ch_CHI0(dtcr) = get_Char(gel(ch_CHI0(dtcr),1), prec2);
  }

  return dataCR;
}

/********************************************************************/
/*             4th part: compute the coefficients an(chi)           */
/*                                                                  */
/* matan entries are arrays of ints containing the coefficients of  */
/* an(chi) as a polmod modulo polcyclo(order(chi))                     */
/********************************************************************/

static void
_0toCoeff(int *rep, long deg)
{
  long i;
  for (i=0; i<deg; i++) rep[i] = 0;
}

/* transform a polmod into Coeff */
static void
Polmod2Coeff(int *rep, GEN polmod, long deg)
{
  long i;
  if (typ(polmod) == t_POLMOD)
  {
    GEN pol = gel(polmod,2);
    long d = degpol(pol);

    pol += 2;
    for (i=0; i<=d; i++) rep[i] = itos(gel(pol,i));
    for (   ; i<deg; i++) rep[i] = 0;
  }
  else
  {
    rep[0] = itos(polmod);
    for (i=1; i<deg; i++) rep[i] = 0;
  }
}

/* initialize a deg * n matrix of ints */
static int**
InitMatAn(long n, long deg, long flag)
{
  long i, j;
  int *a, **A = (int**)pari_malloc((n+1)*sizeof(int*));
  A[0] = NULL;
  for (i = 1; i <= n; i++)
  {
    a = (int*)pari_malloc(deg*sizeof(int));
    A[i] = a; a[0] = (i == 1 || flag);
    for (j = 1; j < deg; j++) a[j] = 0;
  }
  return A;
}

static void
FreeMat(int **A, long n)
{
  long i;
  for (i = 0; i <= n; i++)
    if (A[i]) pari_free((void*)A[i]);
  pari_free((void*)A);
}

/* initialize Coeff reduction */
static int**
InitReduction(long d, long deg)
{
  long j;
  pari_sp av = avma;
  int **A;
  GEN polmod, pol;

  A   = (int**)pari_malloc(deg*sizeof(int*));
  pol = polcyclo(d, 0);
  for (j = 0; j < deg; j++)
  {
    A[j] = (int*)pari_malloc(deg*sizeof(int));
    polmod = gmodulo(pol_xn(deg+j, 0), pol);
    Polmod2Coeff(A[j], polmod, deg);
  }

  avma = av; return A;
}

#if 0
void
pan(int **an, long n, long deg)
{
  long i,j;
  for (i = 1; i <= n; i++)
  {
    err_printf("n = %ld: ",i);
    for (j = 0; j < deg; j++) err_printf("%d ",an[i][j]);
    err_printf("\n");
  }
}
#endif

/* returns 0 if c is zero, 1 otherwise. */
static int
IsZero(int* c, long deg)
{
  long i;
  for (i = 0; i < deg; i++)
    if (c[i]) return 0;
  return 1;
}

/* set c0 <-- c0 * c1 */
static void
MulCoeff(int *c0, int* c1, int** reduc, long deg)
{
  long i,j;
  int c, *T;

  if (IsZero(c0,deg)) return;

  T = (int*)new_chunk(2*deg);
  for (i = 0; i < 2*deg; i++)
  {
    c = 0;
    for (j = 0; j <= i; j++)
      if (j < deg && j > i - deg) c += c0[j] * c1[i-j];
    T[i] = c;
  }
  for (i = 0; i < deg; i++)
  {
    c = T[i];
    for (j = 0; j < deg; j++) c += reduc[j][i] * T[deg+j];
    c0[i] = c;
  }
}

/* c0 <- c0 + c1 * c2 */
static void
AddMulCoeff(int *c0, int *c1, int* c2, int** reduc, long deg)
{
  long i, j;
  pari_sp av;
  int c, *t;

  if (IsZero(c2,deg)) return;
  if (!c1) /* c1 == 1 */
  {
    for (i = 0; i < deg; i++) c0[i] += c2[i];
    return;
  }
  av = avma;
  t = (int*)new_chunk(2*deg); /* = c1 * c2, not reduced */
  for (i = 0; i < 2*deg; i++)
  {
    c = 0;
    for (j = 0; j <= i; j++)
      if (j < deg && j > i - deg) c += c1[j] * c2[i-j];
    t[i] = c;
  }
  for (i = 0; i < deg; i++)
  {
    c = t[i];
    for (j = 0; j < deg; j++) c += reduc[j][i] * t[deg+j];
    c0[i] += c;
  }
  avma = av;
}

/* evaluate the Coeff. No Garbage collector */
static GEN
EvalCoeff(GEN z, int* c, long deg)
{
  long i,j;
  GEN e, r;

  if (!c) return gen_0;
#if 0
  /* standard Horner */
  e = stoi(c[deg - 1]);
  for (i = deg - 2; i >= 0; i--)
    e = gadd(stoi(c[i]), gmul(z, e));
#else
  /* specific attention to sparse polynomials */
  e = NULL;
  for (i = deg-1; i >=0; i=j-1)
  {
    for (j=i; c[j] == 0; j--)
      if (j==0)
      {
        if (!e) return NULL;
        if (i!=j) z = gpowgs(z,i-j+1);
        return gmul(e,z);
      }
    if (e)
    {
      r = (i==j)? z: gpowgs(z,i-j+1);
      e = gadd(gmul(e,r), stoi(c[j]));
    }
    else
      e = stoi(c[j]);
  }
#endif
  return e;
}

/* copy the n * (m+1) array matan */
static void
CopyCoeff(int** a, int** a2, long n, long m)
{
  long i,j;

  for (i = 1; i <= n; i++)
  {
    int *b = a[i], *b2 = a2[i];
    for (j = 0; j < m; j++) b2[j] = b[j];
  }
}

static void
an_AddMul(int **an,int **an2, long np, long n, long deg, GEN chi, int **reduc)
{
  GEN chi2 = chi;
  long q, qk, k;
  int *c, *c2 = (int*)new_chunk(deg);

  CopyCoeff(an, an2, n/np, deg);
  for (q=np;;)
  {
    if (gequal1(chi2)) c = NULL; else { Polmod2Coeff(c2, chi2, deg); c = c2; }
    for(k = 1, qk = q; qk <= n; k++, qk += q)
      AddMulCoeff(an[qk], c, an2[k], reduc, deg);
    if (! (q = umuluu_le(q,np, n)) ) break;

    chi2 = gmul(chi2, chi);
  }
}

/* correct the coefficients an(chi) according with diff(chi) in place */
static void
CorrectCoeff(GEN dtcr, int** an, int** reduc, long n, long deg)
{
  pari_sp av = avma;
  long lg, j;
  pari_sp av1;
  int **an2;
  GEN bnrc, diff;
  CHI_t C;

  diff = ch_diff(dtcr); lg = lg(diff) - 1;
  if (!lg) return;

  if (DEBUGLEVEL>2) err_printf("diff(CHI) = %Ps", diff);
  bnrc = ch_bnr(dtcr);
  init_CHI_alg(&C, ch_CHI0(dtcr));

  an2 = InitMatAn(n, deg, 0);
  av1 = avma;
  for (j = 1; j <= lg; j++)
  {
    GEN pr = gel(diff,j);
    long Np = upr_norm(pr);
    GEN chi  = CHI_eval(&C, isprincipalray(bnrc, pr));
    an_AddMul(an,an2,Np,n,deg,chi,reduc);
    avma = av1;
  }
  FreeMat(an2, n); avma = av;
}

/* compute the coefficients an in the general case */
static int**
ComputeCoeff(GEN dtcr, LISTray *R, long n, long deg)
{
  pari_sp av = avma, av2;
  long i, l;
  int **an, **reduc, **an2;
  GEN L;
  CHI_t C;

  init_CHI_alg(&C, ch_CHI(dtcr));
  an  = InitMatAn(n, deg, 0);
  an2 = InitMatAn(n, deg, 0);
  reduc  = InitReduction(C.ord, deg);
  av2 = avma;

  L = R->L1; l = lg(L);
  for (i=1; i<l; i++, avma = av2)
  {
    long np = L[i];
    GEN chi  = CHI_eval(&C, gel(R->L1ray,i));
    an_AddMul(an,an2,np,n,deg,chi,reduc);
  }
  FreeMat(an2, n);

  CorrectCoeff(dtcr, an, reduc, n, deg);
  FreeMat(reduc, deg-1);
  avma = av; return an;
}

/********************************************************************/
/*              5th part: compute L-functions at s=1                */
/********************************************************************/
static void
deg11(LISTray *R, long p, GEN bnr, GEN pr) {
  GEN z = isprincipalray(bnr, pr);
  vecsmalltrunc_append(R->L1, p);
  vectrunc_append(R->L1ray, z);
}
static void
deg12(LISTray *R, long p, GEN bnr, GEN Lpr) {
  GEN z = isprincipalray(bnr, gel(Lpr,1));
  vecsmalltrunc_append(R->L11, p);
  vectrunc_append(R->L11ray, z);
}
static void
deg0(LISTray *R, long p) { vecsmalltrunc_append(R->L0, p); }
static void
deg2(LISTray *R, long p) { vecsmalltrunc_append(R->L2, p); }

static void
InitPrimesQuad(GEN bnr, ulong N0, LISTray *R)
{
  pari_sp av = avma;
  GEN bnf = bnr_get_bnf(bnr), cond = gel(bnr_get_mod(bnr), 1);
  long p,i,l, condZ = itos(gcoeff(cond,1,1)), contZ = itos(content(cond));
  GEN prime, Lpr, nf = bnf_get_nf(bnf), dk = nf_get_disc(nf);
  forprime_t T;

  l = 1 + primepi_upper_bound(N0);
  R->L0 = vecsmalltrunc_init(l);
  R->L2 = vecsmalltrunc_init(l); R->condZ = condZ;
  R->L1 = vecsmalltrunc_init(l); R->L1ray = vectrunc_init(l);
  R->L11= vecsmalltrunc_init(l); R->L11ray= vectrunc_init(l);
  prime = utoipos(2);
  u_forprime_init(&T, 2, N0);
  while ( (p = u_forprime_next(&T)) )
  {
    prime[2] = p;
    switch (kroiu(dk, p))
    {
    case -1: /* inert */
      if (condZ % p == 0) deg0(R,p); else deg2(R,p);
      break;
    case 1: /* split */
      Lpr = idealprimedec(nf, prime);
      if      (condZ % p != 0) deg12(R, p, bnr, Lpr);
      else if (contZ % p == 0) deg0(R,p);
      else
      {
        GEN pr = idealval(nf, cond, gel(Lpr,1))? gel(Lpr,2): gel(Lpr,1);
        deg11(R, p, bnr, pr);
      }
      break;
    default: /* ramified */
      if (condZ % p == 0)
        deg0(R,p);
      else
        deg11(R, p, bnr, idealprimedec_galois(nf,prime));
      break;
    }
  }
  /* precompute isprincipalray(x), x in Z */
  R->rayZ = cgetg(condZ, t_VEC);
  for (i=1; i<condZ; i++)
    gel(R->rayZ,i) = (ugcd(i,condZ) == 1)? isprincipalray(bnr, utoipos(i)): gen_0;
  gerepileall(av, 7, &(R->L0), &(R->L2), &(R->rayZ),
              &(R->L1), &(R->L1ray), &(R->L11), &(R->L11ray) );
}

static void
InitPrimes(GEN bnr, ulong N0, LISTray *R)
{
  GEN bnf = bnr_get_bnf(bnr), cond = gel(bnr_get_mod(bnr), 1);
  long p,j,k,l, condZ = itos(gcoeff(cond,1,1)), N = lg(cond)-1;
  GEN tmpray, tabpr, prime, BOUND, nf = bnf_get_nf(bnf);
  forprime_t T;

  R->condZ = condZ; l = primepi_upper_bound(N0) * N;
  tmpray = cgetg(N+1, t_VEC);
  R->L1 = vecsmalltrunc_init(l);
  R->L1ray = vectrunc_init(l);
  u_forprime_init(&T, 2, N0);
  prime = utoipos(2);
  BOUND = utoi(N0);
  while ( (p = u_forprime_next(&T)) )
  {
    pari_sp av = avma;
    prime[2] = p;
    if (DEBUGLEVEL>1 && (p & 2047) == 1) err_printf("%ld ", p);
    tabpr = idealprimedec_limit_norm(nf, prime, BOUND);
    for (j = 1; j < lg(tabpr); j++)
    {
      GEN pr  = gel(tabpr,j);
      if (condZ % p == 0 && idealval(nf, cond, pr))
      {
        gel(tmpray,j) = NULL; continue;
      }
      vecsmalltrunc_append(R->L1, upowuu(p, pr_get_f(pr)));
      gel(tmpray,j) = gclone( isprincipalray(bnr, pr) );
    }
    avma = av;
    for (k = 1; k < j; k++)
    {
      if (!tmpray[k]) continue;
      vectrunc_append(R->L1ray, ZC_copy(gel(tmpray,k)));
      gunclone(gel(tmpray,k));
    }
  }
}

static GEN /* cf polcoef */
_sercoeff(GEN x, long n)
{
  long i = n - valp(x);
  return (i < 0)? gen_0: gel(x,i+2);
}

static void
affect_coeff(GEN q, long n, GEN y)
{
  GEN x = _sercoeff(q,-n);
  if (x == gen_0) gel(y,n) = NULL; else affgr(x, gel(y,n));
}

typedef struct {
  GEN c1, aij, bij, cS, cT, powracpi;
  long i0, a,b,c, r, rc1, rc2;
} ST_t;

/* compute the principal part at the integers s = 0, -1, -2, ..., -i0
   of Gamma((s+1)/2)^a Gamma(s/2)^b Gamma(s)^c / (s - z) with z = 0 and 1 */
/* NOTE: surely not the best way to do this, but it's fast enough! */
static void
ppgamma(ST_t *T, long prec)
{
  GEN eul, gam,gamun,gamdm, an,bn,cn_evn,cn_odd, x,x2,X,Y, cf, sqpi;
  GEN p1, p2, aij, bij;
  long a = T->a;
  long b = T->b;
  long c = T->c, r = T->r, i0 = T->i0;
  long i,j, s,t;
  pari_sp av;

  aij = cgetg(i0+1, t_VEC);
  bij = cgetg(i0+1, t_VEC);
  for (i = 1; i <= i0; i++)
  {
    gel(aij,i) = p1 = cgetg(r+1, t_VEC);
    gel(bij,i) = p2 = cgetg(r+1, t_VEC);
    for (j=1; j<=r; j++) { gel(p1,j) = cgetr(prec); gel(p2,j) = cgetr(prec); }
  }
  av = avma;

  x   = pol_x(0);
  x2  = gmul2n(x, -1); /* x/2 */
  eul = mpeuler(prec);
  sqpi= sqrtr_abs(mppi(prec)); /* Gamma(1/2) */

  /* expansion of log(Gamma(u)) at u = 1 */
  gamun = cgetg(r+3, t_SER);
  gamun[1] = evalsigne(1) | _evalvalp(0) | evalvarn(0);
  gel(gamun,2) = gen_0;
  gel(gamun,3) = gneg(eul);
  for (i = 2; i <= r; i++)
    gel(gamun,i+2) = divrs(szeta(i,prec), odd(i)? -i: i);
  gamun = gexp(gamun, prec); /* Gamma(1 + x) */
  gam = gdiv(gamun,x); /* Gamma(x) */

  /* expansion of log(Gamma(u) / Gamma(1/2)) at u = 1/2 */
  gamdm = cgetg(r+3, t_SER);
  gamdm[1] = evalsigne(1) | _evalvalp(0) | evalvarn(0);
  gel(gamdm,2) = gen_0;
  gel(gamdm,3) = gneg(gadd(gmul2n(mplog2(prec), 1), eul));
  for (i = 2; i <= r; i++) gel(gamdm,i+2) = mulri(gel(gamun,i+2), int2um1(i));
  gamdm = gmul(sqpi, gexp(gamdm, prec)); /* Gamma(1/2 + x) */

 /* We simplify to get one of the following two expressions
  * if (b > a) : sqrt{Pi}^a 2^{a-au} Gamma(u)^{a+c} Gamma(  u/2  )^{|b-a|}
  * if (b <= a): sqrt{Pi}^b 2^{b-bu} Gamma(u)^{b+c} Gamma((u+1)/2)^{|b-a|} */
  if (b > a)
  {
    t = a; s = b; X = x2; Y = gsub(x2,ghalf);
    p1 = ser_unscale(gam, ghalf);
    p2 = gdiv(ser_unscale(gamdm,ghalf), Y); /* Gamma((x-1)/2) */
  }
  else
  {
    t = b; s = a; X = gadd(x2,ghalf); Y = x2;
    p1 = ser_unscale(gamdm,ghalf);
    p2 = ser_unscale(gam,ghalf);
  }
  cf = powru(sqpi, t);
  an = gpowgs(gpow(gen_2, gsubsg(1,x), prec), t); /* 2^{t-tx} */
  bn = gpowgs(gam, t+c); /* Gamma(x)^{t+c} */
  cn_evn = gpowgs(p1, s-t); /* Gamma(X)^{s-t} */
  cn_odd = gpowgs(p2, s-t); /* Gamma(Y)^{s-t} */
  for (i = 0; i < i0/2; i++)
  {
    GEN C1,q1, A1 = gel(aij,2*i+1), B1 = gel(bij,2*i+1);
    GEN C2,q2, A2 = gel(aij,2*i+2), B2 = gel(bij,2*i+2);

    C1 = gmul(cf, gmul(bn, gmul(an, cn_evn)));
    p1 = gdiv(C1, gsubgs(x, 2*i));
    q1 = gdiv(C1, gsubgs(x, 2*i+1));

    /* an(x-u-1) = 2^t an(x-u) */
    an = gmul2n(an, t);
    /* bn(x-u-1) = bn(x-u) / (x-u-1)^{t+c} */
    bn = gdiv(bn, gpowgs(gsubgs(x, 2*i+1), t+c));

    C2 = gmul(cf, gmul(bn, gmul(an, cn_odd)));
    p2 = gdiv(C2, gsubgs(x, 2*i+1));
    q2 = gdiv(C2, gsubgs(x, 2*i+2));
    for (j = 1; j <= r; j++)
    {
      affect_coeff(p1, j, A1); affect_coeff(q1, j, B1);
      affect_coeff(p2, j, A2); affect_coeff(q2, j, B2);
    }

    an = gmul2n(an, t);
    bn = gdiv(bn, gpowgs(gsubgs(x, 2*i+2), t+c));
    /* cn_evn(x-2i-2) = cn_evn(x-2i)  / (X - (i+1))^{s-t} */
    /* cn_odd(x-2i-3) = cn_odd(x-2i-1)/ (Y - (i+1))^{s-t} */
    cn_evn = gdiv(cn_evn, gpowgs(gsubgs(X,i+1), s-t));
    cn_odd = gdiv(cn_odd, gpowgs(gsubgs(Y,i+1), s-t));
  }
  T->aij = aij;
  T->bij = bij; avma = av;
}

static GEN
_cond(GEN dtcr) { return mkvec2(ch_cond(dtcr), ch_4(dtcr)); }

/* sort chars according to conductor */
static GEN
sortChars(GEN dataCR)
{
  const long cl = lg(dataCR) - 1;
  GEN vCond  = cgetg(cl+1, t_VEC);
  GEN CC     = cgetg(cl+1, t_VECSMALL);
  GEN nvCond = cgetg(cl+1, t_VECSMALL);
  long j,k, ncond;
  GEN vChar;

  for (j = 1; j <= cl; j++) nvCond[j] = 0;

  ncond = 0;
  for (j = 1; j <= cl; j++)
  {
    GEN cond = _cond(gel(dataCR,j));
    for (k = 1; k <= ncond; k++)
      if (gequal(cond, gel(vCond,k))) break;
    if (k > ncond) gel(vCond,++ncond) = cond;
    nvCond[k]++; CC[j] = k; /* char j has conductor number k */
  }
  vChar = cgetg(ncond+1, t_VEC);
  for (k = 1; k <= ncond; k++)
  {
    gel(vChar,k) = cgetg(nvCond[k]+1, t_VECSMALL);
    nvCond[k] = 0;
  }
  for (j = 1; j <= cl; j++)
  {
    k = CC[j]; nvCond[k]++;
    mael(vChar,k,nvCond[k]) = j;
  }
  return vChar;
}

/* Given W(chi), S(chi) and T(chi), return L(1, chi) if fl & 1, else
   [r(chi), c(chi)] where L(s, chi) ~ c(chi) s^r(chi) at s = 0.
   If fl & 2, adjust the value to get L_S(s, chi). */
static GEN
GetValue(GEN dtcr, GEN W, GEN S, GEN T, long fl, long prec)
{
  pari_sp av = avma;
  GEN cf, z, p1;
  long q, b, c, r;
  int isreal = (chi_get_deg(ch_CHI0(dtcr)) <= 2);

  p1 = ch_4(dtcr);
  q = p1[1];
  b = p1[2];
  c = p1[3];

  if (fl & 1)
  { /* S(chi) + W(chi).T(chi)) / (C(chi) sqrt(Pi)^{r1 - q}) */
    cf = gmul(ch_C(dtcr), powruhalf(mppi(prec), b));

    z = gadd(S, gmul(W, T));
    if (isreal) z = real_i(z);
    z = gdiv(z, cf);
    if (fl & 2) z = gmul(z, ComputeAChi(dtcr, &r, 1, prec));
  }
  else
  { /* (W(chi).S(conj(chi)) + T(chi)) / (sqrt(Pi)^q 2^{r1 - q}) */
    cf = gmul2n(powruhalf(mppi(prec), q), b);

    z = gadd(gmul(W, conj_i(S)), conj_i(T));
    if (isreal) z = real_i(z);
    z = gdiv(z, cf); r = 0;
    if (fl & 2) z = gmul(z, ComputeAChi(dtcr, &r, 0, prec));
    z = mkvec2(utoi(b + c + r), z);
  }
  return gerepilecopy(av, z);
}

/* return the order and the first non-zero term of L(s, chi0)
   at s = 0. If flag != 0, adjust the value to get L_S(s, chi0). */
static GEN
GetValue1(GEN bnr, long flag, long prec)
{
  GEN bnf = checkbnf(bnr), nf = bnf_get_nf(bnf);
  GEN h, R, c, diff;
  long i, l, r, r1, r2;
  pari_sp av = avma;

  nf_get_sign(nf, &r1,&r2);
  h = bnf_get_no(bnf);
  R = bnf_get_reg(bnf);

  c = gneg_i(gdivgs(mpmul(h, R), bnf_get_tuN(bnf)));
  r = r1 + r2 - 1;

  if (flag)
  {
    diff = divcond(bnr);
    l = lg(diff) - 1; r += l;
    for (i = 1; i <= l; i++)
      c = gmul(c, glog(pr_norm(gel(diff,i)), prec));
  }
  return gerepilecopy(av, mkvec2(stoi(r), c));
}

/********************************************************************/
/*                6th part: recover the coefficients                */
/********************************************************************/
static long
TestOne(GEN plg, RC_data *d)
{
  long j, v = d->v;
  GEN z = gsub(d->beta, gel(plg,v));
  if (expo(z) >= d->G) return 0;
  for (j = 1; j < lg(plg); j++)
    if (j != v && mpcmp(d->B, mpabs_shallow(gel(plg,j))) < 0) return 0;
  return 1;
}

static GEN
chk_reccoeff_init(FP_chk_fun *chk, GEN r, GEN mat)
{
  RC_data *d = (RC_data*)chk->data;
  (void)r; d->U = mat; return d->nB;
}

static GEN
chk_reccoeff(void *data, GEN x)
{
  RC_data *d = (RC_data*)data;
  GEN v = gmul(d->U, x), z = gel(v,1);

  if (!gequal1(z)) return NULL;
  *++v = evaltyp(t_COL) | evallg( lg(d->M) );
  if (TestOne(gmul(d->M, v), d)) return v;
  return NULL;
}

/* Using Cohen's method */
static GEN
RecCoeff3(GEN nf, RC_data *d, long prec)
{
  GEN A, M, nB, cand, p1, B2, C2, tB, beta2, nf2, Bd;
  GEN beta = d->beta, B = d->B;
  long N = d->N, v = d->v, e, BIG;
  long i, j, k, ct = 0, prec2;
  FP_chk_fun chk = { &chk_reccoeff, &chk_reccoeff_init, NULL, NULL, 0 };
  chk.data = (void*)d;

  d->G = minss(-10, -prec2nbits(prec) >> 4);
  BIG = maxss(32, -2*d->G);
  tB  = sqrtnr(real2n(BIG-N,DEFAULTPREC), N-1);
  Bd  = grndtoi(gmin_shallow(B, tB), &e);
  if (e > 0) return NULL; /* failure */
  Bd = addiu(Bd, 1);
  prec2 = nbits2prec( expi(Bd) + 192 );
  prec2 = maxss(precdbl(prec), prec2);
  B2 = sqri(Bd);
  C2 = shifti(B2, BIG<<1);

LABrcf: ct++;
  beta2 = gprec_w(beta, prec2);
  nf2 = nfnewprec_shallow(nf, prec2);
  d->M = M = nf_get_M(nf2);

  A = cgetg(N+2, t_MAT);
  for (i = 1; i <= N+1; i++) gel(A,i) = cgetg(N+2, t_COL);

  gcoeff(A, 1, 1) = gadd(gmul(C2, gsqr(beta2)), B2);
  for (j = 2; j <= N+1; j++)
  {
    p1 = gmul(C2, gmul(gneg_i(beta2), gcoeff(M, v, j-1)));
    gcoeff(A, 1, j) = gcoeff(A, j, 1) = p1;
  }
  for (i = 2; i <= N+1; i++)
    for (j = i; j <= N+1; j++)
    {
      p1 = gen_0;
      for (k = 1; k <= N; k++)
      {
        GEN p2 = gmul(gcoeff(M, k, j-1), gcoeff(M, k, i-1));
        if (k == v) p2 = gmul(C2, p2);
        p1 = gadd(p1,p2);
      }
      gcoeff(A, i, j) = gcoeff(A, j, i) = p1;
    }

  nB = mului(N+1, B2);
  d->nB = nB;
  cand = fincke_pohst(A, nB, -1, prec2, &chk);

  if (!cand)
  {
    if (ct > 3) return NULL;
    prec2 = precdbl(prec2);
    if (DEBUGLEVEL>1) pari_warn(warnprec,"RecCoeff", prec2);
    goto LABrcf;
  }

  cand = gel(cand,1);
  if (lg(cand) == 2) return gel(cand,1);

  if (DEBUGLEVEL>1) err_printf("RecCoeff3: no solution found!\n");
  return NULL;
}

/* Using linear dependance relations */
static GEN
RecCoeff2(GEN nf,  RC_data *d,  long prec)
{
  pari_sp av;
  GEN vec, M = nf_get_M(nf), beta = d->beta;
  long bit, min, max, lM = lg(M);

  d->G = minss(-20, -prec2nbits(prec) >> 4);

  vec  = shallowconcat(mkvec(gneg(beta)), row(M, d->v));
  min = (long)prec2nbits_mul(prec, 0.75);
  max = (long)prec2nbits_mul(prec, 0.98);
  av = avma;
  for (bit = max; bit >= min; bit-=32, avma = av)
  {
    long e;
    GEN v = lindep_bit(vec, bit), z = gel(v,1);
    if (!signe(z)) continue;
    *++v = evaltyp(t_COL) | evallg(lM);
    v = grndtoi(gdiv(v, z), &e);
    if (e > 0) break;
    if (TestOne(RgM_RgC_mul(M, v), d)) return v;
  }
  /* failure */
  return RecCoeff3(nf,d,prec);
}

/* Attempts to find a polynomial with coefficients in nf such that
   its coefficients are close to those of pol at the place v and
   less than B at all the other places */
static GEN
RecCoeff(GEN nf,  GEN pol,  long v, long prec)
{
  long j, md, cl = degpol(pol);
  pari_sp av = avma;
  RC_data d;

  /* if precision(pol) is too low, abort */
  for (j = 2; j <= cl+1; j++)
  {
    GEN t = gel(pol, j);
    if (prec2nbits(gprecision(t)) - gexpo(t) < 34) return NULL;
  }

  md = cl/2;
  pol = leafcopy(pol);

  d.N = nf_get_degree(nf);
  d.v = v;

  for (j = 1; j <= cl; j++)
  { /* start with the coefficients in the middle,
       since they are the harder to recognize! */
    long cf = md + (j%2? j/2: -j/2);
    GEN t, bound = shifti(binomial(utoipos(cl), cf), cl-cf);

    if (DEBUGLEVEL>1) err_printf("RecCoeff (cf = %ld, B = %Ps)\n", cf, bound);
    d.beta = real_i( gel(pol,cf+2) );
    d.B    = bound;
    if (! (t = RecCoeff2(nf, &d, prec)) ) return NULL;
    gel(pol, cf+2) = coltoalg(nf,t);
  }
  gel(pol,cl+2) = gen_1;
  return gerepilecopy(av, pol);
}

/* an[q * i] *= chi for all (i,p)=1 */
static void
an_mul(int **an, long p, long q, long n, long deg, GEN chi, int **reduc)
{
  pari_sp av;
  long c,i;
  int *T;

  if (gequal1(chi)) return;
  av = avma;
  T = (int*)new_chunk(deg); Polmod2Coeff(T,chi, deg);
  for (c = 1, i = q; i <= n; i += q, c++)
    if (c == p) c = 0; else MulCoeff(an[i], T, reduc, deg);
  avma = av;
}
/* an[q * i] = 0 for all (i,p)=1 */
static void
an_set0_coprime(int **an, long p, long q, long n, long deg)
{
  long c,i;
  for (c = 1, i = q; i <= n; i += q, c++)
    if (c == p) c = 0; else _0toCoeff(an[i], deg);
}
/* an[q * i] = 0 for all i */
static void
an_set0(int **an, long p, long n, long deg)
{
  long i;
  for (i = p; i <= n; i += p) _0toCoeff(an[i], deg);
}

/* compute the coefficients an for the quadratic case */
static int**
computean(GEN dtcr, LISTray *R, long n, long deg)
{
  pari_sp av = avma, av2;
  long i, p, q, condZ, l;
  int **an, **reduc;
  GEN L, chi, chi1;
  CHI_t C;

  init_CHI_alg(&C, ch_CHI(dtcr));
  condZ= R->condZ;

  an = InitMatAn(n, deg, 1);
  reduc = InitReduction(C.ord, deg);
  av2 = avma;

  /* all pr | p divide cond */
  L = R->L0; l = lg(L);
  for (i=1; i<l; i++) an_set0(an,L[i],n,deg);

  /* 1 prime of degree 2 */
  L = R->L2; l = lg(L);
  for (i=1; i<l; i++, avma = av2)
  {
    p = L[i];
    if (condZ == 1) chi = C.val[0]; /* 1 */
    else            chi = CHI_eval(&C, gel(R->rayZ, p%condZ));
    chi1 = chi;
    for (q=p;;)
    {
      an_set0_coprime(an, p,q,n,deg); /* v_p(q) odd */
      if (! (q = umuluu_le(q,p, n)) ) break;

      an_mul(an,p,q,n,deg,chi,reduc);
      if (! (q = umuluu_le(q,p, n)) ) break;
      chi = gmul(chi, chi1);
    }
  }

  /* 1 prime of degree 1 */
  L = R->L1; l = lg(L);
  for (i=1; i<l; i++, avma = av2)
  {
    p = L[i];
    chi = CHI_eval(&C, gel(R->L1ray,i));
    chi1 = chi;
    for(q=p;;)
    {
      an_mul(an,p,q,n,deg,chi,reduc);
      if (! (q = umuluu_le(q,p, n)) ) break;
      chi = gmul(chi, chi1);
    }
  }

  /* 2 primes of degree 1 */
  L = R->L11; l = lg(L);
  for (i=1; i<l; i++, avma = av2)
  {
    GEN ray1, ray2, chi11, chi12, chi2;

    p = L[i]; ray1 = gel(R->L11ray,i); /* use pr1 pr2 = (p) */
    if (condZ == 1)
      ray2 = ZC_neg(ray1);
    else
      ray2 = ZC_sub(gel(R->rayZ, p%condZ),  ray1);
    chi11 = CHI_eval(&C, ray1);
    chi12 = CHI_eval(&C, ray2);

    chi1 = gadd(chi11, chi12);
    chi2 = chi12;
    for(q=p;;)
    {
      an_mul(an,p,q,n,deg,chi1,reduc);
      if (! (q = umuluu_le(q,p, n)) ) break;
      chi2 = gmul(chi2, chi12);
      chi1 = gadd(chi2, gmul(chi1, chi11));
    }
  }

  CorrectCoeff(dtcr, an, reduc, n, deg);
  FreeMat(reduc, deg-1);
  avma = av; return an;
}

/* return the vector of A^i/i for i = 1...n */
static GEN
mpvecpowdiv(GEN A, long n)
{
  pari_sp av = avma;
  long i;
  GEN v = powersr(A, n);
  GEN w = cgetg(n+1, t_VEC);
  gel(w,1) = rcopy(gel(v,2));
  for (i=2; i<=n; i++) gel(w,i) = divru(gel(v,i+1), i);
  return gerepileupto(av, w);
}

static void GetST0(GEN bnr, GEN *pS, GEN *pT, GEN dataCR, GEN vChar, long prec);

/* compute S and T for the quadratic case. The following cases (cs) are:
   1) bnr complex;
   2) bnr real and no infinite place divide cond_chi (TBD);
   3) bnr real and one infinite place divide cond_chi;
   4) bnr real and both infinite places divide cond_chi (TBD) */
static void
QuadGetST(GEN bnr, GEN *pS, GEN *pT, GEN dataCR, GEN vChar, long prec)
{
  pari_sp av = avma, av1, av2;
  long ncond, n, j, k, n0;
  GEN N0, C, T = *pT, S = *pS, an, degs, cs;
  LISTray LIST;

  /* initializations */
  degs = GetDeg(dataCR);
  ncond = lg(vChar)-1;
  C    = cgetg(ncond+1, t_VEC);
  N0   = cgetg(ncond+1, t_VECSMALL);
  cs   = cgetg(ncond+1, t_VECSMALL);
  n0 = 0;
  for (j = 1; j <= ncond; j++)
  {
    /* FIXME: make sure that this value of c is correct for the general case */
    long r1, r2, q;
    GEN dtcr = gel(dataCR, mael(vChar,j,1)), p1 = ch_4(dtcr), c = ch_C(dtcr);

    gel(C,j) = c;
    q = p1[1];

    nf_get_sign(bnr_get_nf(ch_bnr(dtcr)), &r1, &r2);
    if (r1 == 2) /* real quadratic */
    {
      cs[j] = 2 + q;
      /* FIXME:
         make sure that this value of N0 is correct for the general case */
      N0[j] = (long)prec2nbits_mul(prec, 0.35 * gtodouble(c));
      if (cs[j] == 2 || cs[j] == 4) /* NOT IMPLEMENTED YET */
      {
        GetST0(bnr, pS, pT, dataCR, vChar, prec);
        return;
      }
    }
    else /* complex quadratic */
    {
      cs[j] = 1;
      N0[j] = (long)prec2nbits_mul(prec, 0.7 * gtodouble(c));
    }
    if (n0 < N0[j]) n0 = N0[j];
  }
  if (DEBUGLEVEL>1) err_printf("N0 = %ld\n", n0);
  InitPrimesQuad(bnr, n0, &LIST);

  av1 = avma;
  /* loop over conductors */
  for (j = 1; j <= ncond; j++)
  {
    GEN c0 = gel(C,j), c1 = divur(1, c0), c2 = divur(2, c0);
    GEN ec1 = mpexp(c1), ec2 = mpexp(c2), LChar = gel(vChar,j);
    GEN vf0, vf1, cf0, cf1;
    const long nChar = lg(LChar)-1, NN = N0[j];

    if (DEBUGLEVEL>1)
      err_printf("* conductor no %ld/%ld (N = %ld)\n\tInit: ", j,ncond,NN);
    if (realprec(ec1) > prec) ec1 = rtor(ec1, prec);
    if (realprec(ec2) > prec) ec2 = rtor(ec2, prec);
    switch(cs[j])
    {
    case 1:
      cf0 = gen_1;
      cf1 = c0;
      vf0 = mpveceint1(rtor(c1, prec), ec1, NN);
      vf1 = mpvecpowdiv(invr(ec1), NN); break;

    case 3:
      cf0 = sqrtr(mppi(prec));
      cf1 = gmul2n(cf0, 1);
      cf0 = gmul(cf0, c0);
      vf0 = mpvecpowdiv(invr(ec2), NN);
      vf1 = mpveceint1(rtor(c2, prec), ec2, NN); break;

    default:
      cf0 = cf1 = NULL; /* FIXME: not implemented */
      vf0 = vf1 = NULL;
    }
    for (k = 1; k <= nChar; k++)
    {
      const long t = LChar[k], d = degs[t];
      const GEN dtcr = gel(dataCR, t), z = gel(ch_CHI(dtcr), 2);
      GEN p1 = gen_0, p2 = gen_0;
      int **matan;
      long c = 0;

      if (DEBUGLEVEL>1)
        err_printf("\tcharacter no: %ld (%ld/%ld)\n", t,k,nChar);
      if (isintzero( ch_comp(gel(dataCR, t)) ))
      {
        if (DEBUGLEVEL>1) err_printf("\t  no need to compute this character\n");
        continue;
      }
      av2 = avma;
      matan = computean(gel(dataCR,t), &LIST, NN, d);
      for (n = 1; n <= NN; n++)
        if ((an = EvalCoeff(z, matan[n], d)))
        {
          p1 = gadd(p1, gmul(an, gel(vf0,n)));
          p2 = gadd(p2, gmul(an, gel(vf1,n)));
          if (++c == 256) { gerepileall(av2,2, &p1,&p2); c = 0; }
        }
      gaffect(gmul(cf0, p1), gel(S,t));
      gaffect(gmul(cf1,  conj_i(p2)), gel(T,t));
      FreeMat(matan,NN); avma = av2;
    }
    if (DEBUGLEVEL>1) err_printf("\n");
    avma = av1;
  }
  avma = av;
}

/* s += t*u. All 3 of them t_REAL, except we allow s or u = NULL (for 0) */
static GEN
_addmulrr(GEN s, GEN t, GEN u)
{
  if (u)
  {
    GEN v = mulrr(t, u);
    return s? addrr(s, v): v;
  }
  return s;
}
/* s += t. Both real, except we allow s or t = NULL (for exact 0) */
static GEN
_addrr(GEN s, GEN t)
{ return t? (s? addrr(s, t): t) : s; }

/* S & T for the general case. This is time-critical: optimize */
static void
get_cS_cT(ST_t *T, long n)
{
  pari_sp av;
  GEN csurn, nsurc, lncsurn, A, B, s, t, Z, aij, bij;
  long i, j, r, i0;

  if (T->cS[n]) return;

  av = avma;
  aij = T->aij; i0= T->i0;
  bij = T->bij; r = T->r;
  Z = cgetg(r+1, t_VEC);
  gel(Z,1) = NULL; /* unused */

  csurn = divru(T->c1, n);
  nsurc = invr(csurn);
  lncsurn = logr_abs(csurn);

  if (r > 1)
  {
    gel(Z,2) = lncsurn; /* r >= 2 */
    for (i = 3; i <= r; i++)
      gel(Z,i) = divru(mulrr(gel(Z,i-1), lncsurn), i-1);
    /* Z[i] = ln^(i-1)(c1/n) / (i-1)! */
  }

  /* i = i0 */
    A = gel(aij,i0); t = _addrr(NULL, gel(A,1));
    B = gel(bij,i0); s = _addrr(NULL, gel(B,1));
    for (j = 2; j <= r; j++)
    {
      s = _addmulrr(s, gel(Z,j),gel(B,j));
      t = _addmulrr(t, gel(Z,j),gel(A,j));
    }
  for (i = i0 - 1; i > 1; i--)
  {
    A = gel(aij,i); if (t) t = mulrr(t, nsurc);
    B = gel(bij,i); if (s) s = mulrr(s, nsurc);
    for (j = odd(i)? T->rc2: T->rc1; j > 1; j--)
    {
      s = _addmulrr(s, gel(Z,j),gel(B,j));
      t = _addmulrr(t, gel(Z,j),gel(A,j));
    }
    s = _addrr(s, gel(B,1));
    t = _addrr(t, gel(A,1));
  }
  /* i = 1 */
    A = gel(aij,1); if (t) t = mulrr(t, nsurc);
    B = gel(bij,1); if (s) s = mulrr(s, nsurc);
    s = _addrr(s, gel(B,1));
    t = _addrr(t, gel(A,1));
    for (j = 2; j <= r; j++)
    {
      s = _addmulrr(s, gel(Z,j),gel(B,j));
      t = _addmulrr(t, gel(Z,j),gel(A,j));
    }
  s = _addrr(s, T->b? mulrr(csurn, gel(T->powracpi,T->b+1)): csurn);
  if (!s) s = gen_0;
  if (!t) t = gen_0;
  gel(T->cS,n) = gclone(s);
  gel(T->cT,n) = gclone(t); avma = av;
}

static void
clear_cScT(ST_t *T, long N)
{
  GEN cS = T->cS, cT = T->cT;
  long i;
  for (i=1; i<=N; i++)
    if (cS[i]) {
      gunclone(gel(cS,i));
      gunclone(gel(cT,i)); gel(cS,i) = gel(cT,i) = NULL;
    }
}

static void
init_cScT(ST_t *T, GEN dtcr, long N, long prec)
{
  GEN p1 = ch_4(dtcr);
  T->a = p1[1];
  T->b = p1[2];
  T->c = p1[3];
  T->rc1 = T->a + T->c;
  T->rc2 = T->b + T->c;
  T->r   = maxss(T->rc2+1, T->rc1); /* >= 2 */
  ppgamma(T, prec);
  clear_cScT(T, N);
}

/* return a t_REAL */
static GEN
zeta_get_limx(long r1, long r2, long bit)
{
  pari_sp av = avma;
  GEN p1, p2, c0, c1, A0;
  long r = r1 + r2, N = r + r2;

  /* c1 = N 2^(-2r2 / N) */
  c1 = mulrs(powrfrac(real2n(1, DEFAULTPREC), -2*r2, N), N);

  p1 = powru(Pi2n(1, DEFAULTPREC), r - 1);
  p2 = mulir(powuu(N,r), p1); shiftr_inplace(p2, -r2);
  c0 = sqrtr( divrr(p2, powru(c1, r+1)) );

  A0 = logr_abs( gmul2n(c0, bit) ); p2 = divrr(A0, c1);
  p1 = divrr(mulur(N*(r+1), logr_abs(p2)), addsr(2*(r+1), gmul2n(A0,2)));
  return gerepileuptoleaf(av, divrr(addrs(p1, 1), powruhalf(p2, N)));
}
/* N_0 = floor( C_K / limx ). Large */
static long
zeta_get_N0(GEN C,  GEN limx)
{
  long e;
  pari_sp av = avma;
  GEN z = gcvtoi(gdiv(C, limx), &e); /* avoid truncation error */
  if (e >= 0 || is_bigint(z))
    pari_err_OVERFLOW("zeta_get_N0 [need too many primes]");
  if (DEBUGLEVEL>1) err_printf("\ninitzeta: N0 = %Ps\n", z);
  avma = av; return itos(z);
}

static GEN
eval_i(long r1, long r2, GEN limx, long i)
{
  GEN t = powru(limx, i);
  if (!r1)      t = mulrr(t, powru(mpfactr(i  , DEFAULTPREC), r2));
  else if (!r2) t = mulrr(t, powru(mpfactr(i/2, DEFAULTPREC), r1));
  else {
    GEN u1 = mpfactr(i/2, DEFAULTPREC);
    GEN u2 = mpfactr(i,   DEFAULTPREC);
    if (r1 == r2) t = mulrr(t, powru(mulrr(u1,u2), r1));
    else t = mulrr(t, mulrr(powru(u1,r1), powru(u2,r2)));
  }
  return t;
}

/* "small" even i such that limx^i ( (i\2)! )^r1 ( i! )^r2 > B. */
static long
get_i0(long r1, long r2, GEN B, GEN limx)
{
  long imin = 1, imax = 1400;
  while (mpcmp(eval_i(r1,r2,limx, imax), B) < 0) { imin = imax; imax *= 2; }
  while(imax - imin >= 4)
  {
    long m = (imax + imin) >> 1;
    if (mpcmp(eval_i(r1,r2,limx, m), B) >= 0) imax = m; else imin = m;
  }
  return imax & ~1; /* make it even */
}
/* assume limx = zeta_get_limx(r1, r2, bit), a t_REAL */
static long
zeta_get_i0(long r1, long r2, long bit, GEN limx)
{
  pari_sp av = avma;
  GEN B = gmul(sqrtr( divrr(powrs(mppi(DEFAULTPREC), r2-3), limx) ),
               gmul2n(powuu(5, r1), bit + r2));
  long i0 = get_i0(r1, r2, B, limx);
  if (DEBUGLEVEL>1) { err_printf("i0 = %ld\n",i0); err_flush(); }
  avma = av; return i0;
}

static void
GetST0(GEN bnr, GEN *pS, GEN *pT, GEN dataCR, GEN vChar, long prec)
{
  pari_sp av = avma, av1, av2;
  long ncond, n, j, k, jc, n0, prec2, i0, r1, r2;
  GEN nf = checknf(bnr), T = *pT, S = *pS;
  GEN N0, C, an, degs, limx;
  LISTray LIST;
  ST_t cScT;

  /* initializations */
  degs = GetDeg(dataCR);
  ncond = lg(vChar)-1;
  nf_get_sign(nf,&r1,&r2);

  C  = cgetg(ncond+1, t_VEC);
  N0 = cgetg(ncond+1, t_VECSMALL);
  n0 = 0;
  limx = zeta_get_limx(r1, r2, prec2nbits(prec));
  for (j = 1; j <= ncond; j++)
  {
    GEN dtcr = gel(dataCR, mael(vChar,j,1)), c = ch_C(dtcr);
    gel(C,j) = c;
    N0[j] = zeta_get_N0(c, limx);
    if (n0 < N0[j]) n0  = N0[j];
  }
  i0 = zeta_get_i0(r1, r2, prec2nbits(prec), limx);
  InitPrimes(bnr, n0, &LIST);

  prec2 = precdbl(prec) + EXTRA_PREC;
  cScT.powracpi = powersr(sqrtr(mppi(prec2)), r1);

  cScT.cS = cgetg(n0+1, t_VEC);
  cScT.cT = cgetg(n0+1, t_VEC);
  for (j=1; j<=n0; j++) gel(cScT.cS,j) = gel(cScT.cT,j) = NULL;

  cScT.i0 = i0;

  av1 = avma;
  for (jc = 1; jc <= ncond; jc++)
  {
    const GEN LChar = gel(vChar,jc);
    const long nChar = lg(LChar)-1, NN = N0[jc];

    if (DEBUGLEVEL>1)
      err_printf("* conductor no %ld/%ld (N = %ld)\n\tInit: ", jc,ncond,NN);

    cScT.c1 = gel(C,jc);
    init_cScT(&cScT, gel(dataCR, LChar[1]), NN, prec2);
    av2 = avma;
    for (k = 1; k <= nChar; k++)
    {
      const long t = LChar[k];
      if (DEBUGLEVEL>1)
        err_printf("\tcharacter no: %ld (%ld/%ld)\n", t,k,nChar);

      if (!isintzero( ch_comp(gel(dataCR, t)) ))
      {
        const long d = degs[t];
        const GEN dtcr = gel(dataCR, t), z = gel(ch_CHI(dtcr), 2);
        GEN p1 = gen_0, p2 = gen_0;
        long c = 0;
        int **matan = ComputeCoeff(gel(dataCR,t), &LIST, NN, d);
        for (n = 1; n <= NN; n++)
          if ((an = EvalCoeff(z, matan[n], d)))
          {
           get_cS_cT(&cScT, n);
           p1 = gadd(p1, gmul(an, gel(cScT.cS,n)));
           p2 = gadd(p2, gmul(an, gel(cScT.cT,n)));
           if (++c == 256) { gerepileall(av2,2, &p1,&p2); c = 0; }
          }
        gaffect(p1,        gel(S,t));
        gaffect(conj_i(p2), gel(T,t));
        FreeMat(matan, NN); avma = av2;
      }
      else if (DEBUGLEVEL>1)
        err_printf("\t  no need to compute this character\n");
    }
    if (DEBUGLEVEL>1) err_printf("\n");
    avma = av1;
  }
  clear_cScT(&cScT, n0);
  avma = av;
}

static void
GetST(GEN bnr, GEN *pS, GEN *pT, GEN dataCR, GEN vChar, long prec)
{
  const long cl = lg(dataCR) - 1;
  GEN S, T, nf  = checknf(bnr);
  long j;

  /* allocate memory for answer */
  *pS = S = cgetg(cl+1, t_VEC);
  *pT = T = cgetg(cl+1, t_VEC);
  for (j = 1; j <= cl; j++)
  {
    gel(S,j) = cgetc(prec);
    gel(T,j) = cgetc(prec);
  }
  if (nf_get_degree(nf) == 2)
    QuadGetST(bnr, pS, pT, dataCR, vChar, prec);
  else
    GetST0(bnr, pS, pT, dataCR, vChar, prec);
}

/*******************************************************************/
/*                                                                 */
/*     Class fields of real quadratic fields using Stark units     */
/*                                                                 */
/*******************************************************************/
/* compute the Hilbert class field using genus class field theory when
   the exponent of the class group is exactly 2 (trivial group not covered) */
/* Cf Herz, Construction of class fields, LNM 21, Theorem 1 (VII-6) */
static GEN
GenusFieldQuadReal(GEN disc)
{
  long i, i0 = 0, l;
  pari_sp av = avma;
  GEN T = NULL, p0 = NULL, P;

  P = gel(Z_factor(disc), 1);
  l = lg(P);
  for (i = 1; i < l; i++)
  {
    GEN p = gel(P,i);
    if (mod4(p) == 3) { p0 = p; i0 = i; break; }
  }
  l--; /* remove last prime */
  if (i0 == l) l--; /* ... remove p0 and last prime */
  for (i = 1; i < l; i++)
  {
    GEN p = gel(P,i), d, t;
    if (i == i0) continue;
    if (absequaliu(p, 2))
      switch (mod32(disc))
      {
        case  8: d = gen_2; break;
        case 24: d = shifti(p0, 1); break;
        default: d = p0; break;
      }
    else
      d = (mod4(p) == 1)? p: mulii(p0, p);
    t = mkpoln(3, gen_1, gen_0, negi(d)); /* x^2 - d */
    T = T? ZX_compositum_disjoint(T, t): t;
  }
  return gerepileupto(av, polredbest(T, 0));
}
static GEN
GenusFieldQuadImag(GEN disc)
{
  long i, l;
  pari_sp av = avma;
  GEN T = NULL, P;

  P = gel(absZ_factor(disc), 1);
  l = lg(P);
  l--; /* remove last prime */
  for (i = 1; i < l; i++)
  {
    GEN p = gel(P,i), d, t;
    if (absequaliu(p, 2))
      switch (mod32(disc))
      {
        case 24: d = gen_2; break;  /* disc = 8 mod 32 */
        case  8: d = gen_m2; break; /* disc =-8 mod 32 */
        default: d = gen_m1; break;
      }
    else
      d = (mod4(p) == 1)? p: negi(p);
    t = mkpoln(3, gen_1, gen_0, negi(d)); /* x^2 - d */
    T = T? ZX_compositum_disjoint(T, t): t;
  }
  return gerepileupto(av, polredbest(T, 0));
}

/* if flag != 0, computes a fast and crude approximation of the result */
static GEN
AllStark(GEN data,  GEN nf,  long flag,  long newprec)
{
  const long BND = 300;
  long cl, i, j, cpt = 0, N, h, v, n, r1, r2, den;
  pari_sp av, av2;
  int **matan;
  GEN bnr = gel(data,1), p1, p2, S, T, polrelnum, polrel, Lp, W, veczeta;
  GEN vChar, degs, C, dataCR, cond1, L1, an;
  LISTray LIST;
  pari_timer ti;

  nf_get_sign(nf, &r1,&r2);
  N     = nf_get_degree(nf);
  cond1 = gel(bnr_get_mod(bnr), 2);
  dataCR = gel(data,5);
  vChar = sortChars(dataCR);

  v = 1;
  while (gequal1(gel(cond1,v))) v++;

  cl = lg(dataCR)-1;
  degs = GetDeg(dataCR);
  h  = itos(ZM_det_triangular(gel(data,2))) >> 1;

LABDOUB:
  if (DEBUGLEVEL) timer_start(&ti);
  av = avma;

  /* characters with rank > 1 should not be computed */
  for (i = 1; i <= cl; i++)
  {
    GEN chi = gel(dataCR, i);
    if (L_vanishes_at_0(chi)) ch_comp(chi) = gen_0;
  }

  W = ComputeAllArtinNumbers(dataCR, vChar, (flag >= 0), newprec);
  if (DEBUGLEVEL) timer_printf(&ti,"Compute W");
  Lp = cgetg(cl + 1, t_VEC);
  if (!flag)
  {
    GetST(bnr, &S, &T, dataCR, vChar, newprec);
    if (DEBUGLEVEL) timer_printf(&ti, "S&T");
    for (i = 1; i <= cl; i++)
    {
      GEN chi = gel(dataCR, i), v = gen_0;
      if (!isintzero( ch_comp(chi) ))
        v = gel(GetValue(chi, gel(W,i), gel(S,i), gel(T,i), 2, newprec), 2);
      gel(Lp, i) = v;
    }
  }
  else
  { /* compute a crude approximation of the result */
    C = cgetg(cl + 1, t_VEC);
    for (i = 1; i <= cl; i++) gel(C,i) = ch_C(gel(dataCR, i));
    n = zeta_get_N0(vecmax(C), zeta_get_limx(r1, r2, prec2nbits(newprec)));
    if (n > BND) n = BND;
    if (DEBUGLEVEL) err_printf("N0 in QuickPol: %ld \n", n);
    InitPrimes(bnr, n, &LIST);

    L1 = cgetg(cl+1, t_VEC);
    /* use L(1) = sum (an / n) */
    for (i = 1; i <= cl; i++)
    {
      GEN dtcr = gel(dataCR,i);
      matan = ComputeCoeff(dtcr, &LIST, n, degs[i]);
      av2 = avma;
      p1 = real_0(newprec); p2 = gel(ch_CHI(dtcr), 2);
      for (j = 1; j <= n; j++)
        if ( (an = EvalCoeff(p2, matan[j], degs[i])) )
          p1 = gadd(p1, gdivgs(an, j));
      gel(L1,i) = gerepileupto(av2, p1);
      FreeMat(matan, n);
    }
    p1 = gmul2n(powruhalf(mppi(newprec), N-2), 1);

    for (i = 1; i <= cl; i++)
    {
      long r;
      GEN WW, A = ComputeAChi(gel(dataCR,i), &r, 0, newprec);
      WW = gmul(gel(C,i), gmul(A, gel(W,i)));
      gel(Lp,i) = gdiv(gmul(WW, conj_i(gel(L1,i))), p1);
    }
  }

  p1 = ComputeLift(gel(data,4));

  den = flag ? h: 2*h;
  veczeta = cgetg(h + 1, t_VEC);
  for (i = 1; i <= h; i++)
  {
    GEN z = gen_0, sig = gel(p1,i);
    for (j = 1; j <= cl; j++)
    {
      GEN dtcr = gel(dataCR,j), CHI = ch_CHI(dtcr);
      GEN t = mulreal(gel(Lp,j), CharEval(CHI, sig));
      if (chi_get_deg(CHI) != 2) t = gmul2n(t, 1); /* character not real */
      z = gadd(z, t);
    }
    gel(veczeta,i) = gdivgs(z, den);
  }
  for (j = 1; j <= h; j++)
    gel(veczeta,j) = gmul2n(gcosh(gel(veczeta,j), newprec), 1);
  polrelnum = roots_to_pol(veczeta, 0);
  if (DEBUGLEVEL)
  {
    if (DEBUGLEVEL>1) {
      err_printf("polrelnum = %Ps\n", polrelnum);
      err_printf("zetavalues = %Ps\n", veczeta);
      if (!flag)
        err_printf("Checking the square-root of the Stark unit...\n");
    }
    timer_printf(&ti, "Compute %s", flag? "quickpol": "polrelnum");
  }

  if (flag)
    return gerepilecopy(av, polrelnum);

  /* try to recognize this polynomial */
  polrel = RecCoeff(nf, polrelnum, v, newprec);
  if (!polrel)
  {
    for (j = 1; j <= h; j++)
      gel(veczeta,j) = gsubgs(gsqr(gel(veczeta,j)), 2);
    polrelnum = roots_to_pol(veczeta, 0);
    if (DEBUGLEVEL)
    {
      if (DEBUGLEVEL>1) {
        err_printf("It's not a square...\n");
        err_printf("polrelnum = %Ps\n", polrelnum);
      }
      timer_printf(&ti, "Compute polrelnum");
    }
    polrel = RecCoeff(nf, polrelnum, v, newprec);
  }
  if (!polrel) /* FAILED */
  {
    const long EXTRA_BITS = 64;
    long incr_pr;
    if (++cpt >= 3) pari_err_PREC( "stark (computation impossible)");
    /* estimate needed precision */
    incr_pr = prec2nbits(gprecision(polrelnum))- gexpo(polrelnum);
    if (incr_pr < 0) incr_pr = -incr_pr + EXTRA_BITS;
    newprec += nbits2extraprec(maxss(3*EXTRA_BITS, cpt*incr_pr));
    if (DEBUGLEVEL) pari_warn(warnprec, "AllStark", newprec);

    nf = nfnewprec_shallow(nf, newprec);
    dataCR = CharNewPrec(dataCR, nf, newprec);

    gerepileall(av, 2, &nf, &dataCR);
    goto LABDOUB;
  }

  if (DEBUGLEVEL) {
    if (DEBUGLEVEL>1) err_printf("polrel = %Ps\n", polrel);
    timer_printf(&ti, "Recpolnum");
  }
  return gerepilecopy(av, polrel);
}

/********************************************************************/
/*                        Main functions                            */
/********************************************************************/

static GEN
get_subgroup(GEN H, GEN cyc, const char *s)
{
  if (!H || gequal0(H)) return diagonal_shallow(cyc);
  if (typ(H) != t_MAT) pari_err_TYPE(stack_strcat(s," [subgroup]"), H);
  RgM_check_ZM(H, s);
  return ZM_hnfmodid(H, cyc);
}

GEN
bnrstark(GEN bnr, GEN subgrp, long prec)
{
  long N, newprec;
  pari_sp av = avma;
  GEN bnf, p1, cycbnr, nf, data, dtQ;

  /* check the bnr */
  checkbnr(bnr);
  bnf = checkbnf(bnr);
  nf  = bnf_get_nf(bnf);
  N   = nf_get_degree(nf);
  if (N == 1) return galoissubcyclo(bnr, subgrp, 0, 0);

  /* check the bnf */
  if (!nf_get_varn(nf))
    pari_err_PRIORITY("bnrstark", nf_get_pol(nf), "=", 0);
  if (nf_get_r2(nf)) pari_err_DOMAIN("bnrstark", "r2", "!=", gen_0, nf);
  subgrp = get_subgroup(subgrp,bnr_get_cyc(bnr),"bnrstark");

  /* compute bnr(conductor) */
  p1     = bnrconductor_i(bnr, subgrp, 2);
  bnr    = gel(p1,2); cycbnr = bnr_get_cyc(bnr);
  subgrp = gel(p1,3);
  if (gequal1( ZM_det_triangular(subgrp) )) { avma = av; return pol_x(0); }

  /* check the class field */
  if (!gequal0(gel(bnr_get_mod(bnr), 2)))
    pari_err_DOMAIN("bnrstark", "r2(class field)", "!=", gen_0, bnr);

  /* find a suitable extension N */
  dtQ = InitQuotient(subgrp);
  data  = FindModulus(bnr, dtQ, &newprec);
  if (!data)
  {
    GEN vec, H, cyc = gel(dtQ,2), U = gel(dtQ,3), M = RgM_inv(U);
    long i, j = 1, l = lg(M);

    /* M = indep. generators of Cl_f/subgp, restrict to cyclic components */
    vec = cgetg(l, t_VEC);
    for (i = 1; i < l; i++)
    {
      if (is_pm1(gel(cyc,i))) continue;
      H = ZM_hnfmodid(vecsplice(M,i), cycbnr);
      gel(vec,j++) = bnrstark(bnr, H, prec);
    }
    setlg(vec, j); return gerepilecopy(av, vec);
  }

  if (newprec > prec)
  {
    if (DEBUGLEVEL>1) err_printf("new precision: %ld\n", newprec);
    nf = nfnewprec_shallow(nf, newprec);
  }
  return gerepileupto(av, AllStark(data, nf, 0, newprec));
}

/* For each character of Cl(bnr)/subgp, compute L(1, chi) (or equivalently
 * the first non-zero term c(chi) of the expansion at s = 0).
 * If flag & 1: compute the value at s = 1 (for non-trivial characters),
 * else compute the term c(chi) and return [r(chi), c(chi)] where r(chi) is
 *   the order of L(s, chi) at s = 0.
 * If flag & 2: compute the value of the L-function L_S(s, chi) where S is the
 *   set of places dividing the modulus of bnr (and the infinite places),
 * else
 *   compute the value of the primitive L-function attached to chi,
 * If flag & 4: return also the character */
GEN
bnrL1(GEN bnr, GEN subgp, long flag, long prec)
{
  GEN cyc, L1, allCR, listCR;
  GEN indCR, invCR, Qt;
  long cl, i, nc;
  pari_sp av = avma;

  checkbnr(bnr);
  if (flag < 0 || flag > 8) pari_err_FLAG("bnrL1");

  cyc  = bnr_get_cyc(bnr);
  subgp = get_subgroup(subgp, cyc, "bnrL1");

  Qt = InitQuotient(subgp);
  cl = itou(gel(Qt,1));

  /* compute all characters */
  allCR = EltsOfGroup(cl, gel(Qt,2));

  /* make a list of all non-trivial characters modulo conjugation */
  listCR = cgetg(cl, t_VEC);
  indCR = cgetg(cl, t_VECSMALL);
  invCR = cgetg(cl, t_VECSMALL); nc = 0;
  for (i = 1; i < cl; i++)
  {
    /* lift to a character on Cl(bnr) */
    GEN lchi = LiftChar(Qt, cyc, gel(allCR,i));
    GEN clchi = charconj(cyc, lchi);
    long j, a = 0;
    for (j = 1; j <= nc; j++)
      if (ZV_equal(gmael(listCR, j, 1), clchi)) { a = j; break; }

    if (!a)
    {
      nc++;
      gel(listCR,nc) = mkvec2(lchi, bnrconductorofchar(bnr, lchi));
      indCR[i]  = nc;
      invCR[nc] = i;
    }
    else
      indCR[i] = -invCR[a];

    gel(allCR,i) = lchi;
  }
  settyp(allCR[cl], t_VEC); /* set correct type for trivial character */

  setlg(listCR, nc + 1);
  L1 = cgetg((flag&1)? cl: cl+1, t_VEC);
  if (nc)
  {
    GEN dataCR = InitChar(bnr, listCR, prec);
    GEN W, S, T, vChar = sortChars(dataCR);
    GetST(bnr, &S, &T, dataCR, vChar, prec);
    W = ComputeAllArtinNumbers(dataCR, vChar, 1, prec);
    for (i = 1; i < cl; i++)
    {
      long a = indCR[i];
      if (a > 0)
        gel(L1,i) = GetValue(gel(dataCR,a), gel(W,a), gel(S,a), gel(T,a),
                             flag, prec);
      else
        gel(L1,i) = conj_i(gel(L1,-a));
    }
  }
  if (!(flag & 1))
    gel(L1,cl) = GetValue1(bnr, flag & 2, prec);
  else
    cl--;

  if (flag & 4) {
    for (i = 1; i <= cl; i++) gel(L1,i) = mkvec2(gel(allCR,i), gel(L1,i));
  }
  return gerepilecopy(av, L1);
}

/*******************************************************************/
/*                                                                 */
/*       Hilbert and Ray Class field using Stark                   */
/*                                                                 */
/*******************************************************************/
/* P in A[x,y], deg_y P < 2, return P0 and P1 in A[x] such that P = P0 + P1 y */
static void
split_pol_quad(GEN P, GEN *gP0, GEN *gP1)
{
  long i, l = lg(P);
  GEN P0 = cgetg(l, t_POL), P1 = cgetg(l, t_POL);
  P0[1] = P1[1] = P[1];
  for (i = 2; i < l; i++)
  {
    GEN c = gel(P,i), c0 = c, c1 = gen_0;
    if (typ(c) == t_POL) /* write c = c1 y + c0 */
      switch(degpol(c))
      {
        case -1: c0 = gen_0; break;
        default: c1 = gel(c,3); /* fall through */
        case  0: c0 = gel(c,2); break;
      }
    gel(P0,i) = c0; gel(P1,i) = c1;
  }
  *gP0 = normalizepol_lg(P0, l);
  *gP1 = normalizepol_lg(P1, l);
}

/* k = nf quadratic field, P relative equation of H_k (Hilbert class field)
 * return T in Z[X], such that H_k / Q is the compositum of Q[X]/(T) and k */
static GEN
makescind(GEN nf, GEN P)
{
  GEN Pp, p, pol, G, L, a, roo, P0,P1, Ny,Try, nfpol = nf_get_pol(nf);
  long i, is_P;

  P = lift_shallow(P);
  split_pol_quad(P, &P0, &P1);
  /* P = P0 + y P1, Norm_{k/Q}(P) = P0^2 + Tr y P0P1 + Ny P1^2, irreducible/Q */
  Ny = gel(nfpol, 2);
  Try = negi(gel(nfpol, 3));
  pol = RgX_add(RgX_sqr(P0), RgX_Rg_mul(RgX_sqr(P1), Ny));
  if (signe(Try)) pol = RgX_add(pol, RgX_Rg_mul(RgX_mul(P0,P1), Try));
  /* pol = rnfequation(nf, P); */
  G = galoisinit(pol, NULL);
  L = gal_get_group(G);
  p = gal_get_p(G);
  a = FpX_oneroot(nfpol, p);
  /* P mod a prime \wp above p (which splits) */
  Pp = FpXY_evalx(P, a, p);
  roo = gal_get_roots(G);
  is_P = gequal0( FpX_eval(Pp, remii(gel(roo,1),p), p) );
  /* each roo[i] mod p is a root of P or (exclusive) tau(P) mod \wp */
  /* record whether roo[1] is a root of P or tau(P) */

  for (i = 1; i < lg(L); i++)
  {
    GEN perm = gel(L,i);
    long k = perm[1]; if (k == 1) continue;
    k = gequal0( FpX_eval(Pp, remii(gel(roo,k),p), p) );
    /* roo[k] is a root of the other polynomial */
    if (k != is_P)
    {
      long o = perm_order(perm);
      if (o != 2) perm = perm_pow(perm, o >> 1);
      /* perm has order two and doesn't belong to Gal(H_k/k) */
      return galoisfixedfield(G, perm, 1, varn(P));
    }
  }
  pari_err_BUG("makescind");
  return NULL; /*LCOV_EXCL_LINE*/
}

/* pbnf = NULL if no bnf is needed, f = NULL may be passed for a trivial
 * conductor */
static void
quadray_init(GEN *pD, GEN f, GEN *pbnf, long prec)
{
  GEN D = *pD, nf, bnf = NULL;
  if (typ(D) == t_INT)
  {
    int isfund;
    if (pbnf) {
      long v = f? gvar(f): NO_VARIABLE;
      if (v == NO_VARIABLE) v = 1;
      bnf = Buchall(quadpoly0(D, v), nf_FORCE, prec);
      nf = bnf_get_nf(bnf);
      isfund = equalii(D, nf_get_disc(nf));
    }
    else
      isfund = Z_isfundamental(D);
    if (!isfund) pari_err_DOMAIN("quadray", "isfundamental(D)", "=",gen_0, D);
  }
  else
  {
    bnf = checkbnf(D);
    nf = bnf_get_nf(bnf);
    if (nf_get_degree(nf) != 2)
      pari_err_DOMAIN("quadray", "degree", "!=", gen_2, nf_get_pol(nf));
    D = nf_get_disc(nf);
  }
  if (pbnf) *pbnf = bnf;
  *pD = D;
}

/* compute the polynomial over Q of the Hilbert class field of
   Q(sqrt(D)) where D is a positive fundamental discriminant */
static GEN
quadhilbertreal(GEN D, long prec)
{
  pari_sp av = avma;
  long newprec;
  GEN bnf;
  VOLATILE GEN bnr, dtQ, data, nf, cyc, M;
  pari_timer ti;
  if (DEBUGLEVEL) timer_start(&ti);

  (void)&prec; /* prevent longjmp clobbering it */
  (void)&bnf;  /* prevent longjmp clobbering it, avoid warning due to
                * quadray_init call : discards qualifiers from pointer type */
  quadray_init(&D, NULL, &bnf, prec);
  cyc = bnf_get_cyc(bnf);
  if (lg(cyc) == 1) { avma = av; return pol_x(0); }
  /* if the exponent of the class group is 2, use Genus Theory */
  if (absequaliu(gel(cyc,1), 2)) return gerepileupto(av, GenusFieldQuadReal(D));

  bnr  = Buchray(bnf, gen_1, nf_INIT);
  M = diagonal_shallow(bnr_get_cyc(bnr));
  dtQ = InitQuotient(M);
  nf  = bnf_get_nf(bnf);

  for(;;) {
    VOLATILE GEN pol = NULL;
    pari_CATCH(e_PREC) {
      prec += EXTRA_PREC;
      if (DEBUGLEVEL) pari_warn(warnprec, "quadhilbertreal", prec);
      bnr = bnrnewprec_shallow(bnr, prec);
      bnf = bnr_get_bnf(bnr);
      nf  = bnf_get_nf(bnf);
    } pari_TRY {
      /* find the modulus defining N */
      pari_timer T;
      if (DEBUGLEVEL) timer_start(&T);
      data = FindModulus(bnr, dtQ, &newprec);
      if (DEBUGLEVEL) timer_printf(&T,"FindModulus");
      if (!data)
      {
        long i, l = lg(M);
        GEN vec = cgetg(l, t_VEC);
        for (i = 1; i < l; i++)
        {
          GEN t = gcoeff(M,i,i);
          gcoeff(M,i,i) = gen_1;
          gel(vec,i) = bnrstark(bnr, M, prec);
          gcoeff(M,i,i) = t;
        }
        return gerepileupto(av, vec);
      }

      if (newprec > prec)
      {
        if (DEBUGLEVEL>1) err_printf("new precision: %ld\n", newprec);
        nf = nfnewprec_shallow(nf, newprec);
      }
      pol = AllStark(data, nf, 0, newprec);
    } pari_ENDCATCH;
    if (pol) {
      pol = makescind(nf, pol);
      return gerepileupto(av, polredbest(pol, 0));
    }
  }
}

/*******************************************************************/
/*                                                                 */
/*       Hilbert and Ray Class field using CM (Schertz)            */
/*                                                                 */
/*******************************************************************/
/* form^2 = 1 ? */
static int
hasexp2(GEN form)
{
  GEN a = gel(form,1), b = gel(form,2), c = gel(form,3);
  return !signe(b) || absequalii(a,b) || equalii(a,c);
}
static int
uhasexp2(GEN form)
{
  long a = form[1], b = form[2], c = form[3];
  return !b || a == labs(b) || a == c;
}

GEN
qfbforms(GEN D)
{
  ulong d = itou(D), dover3 = d/3, t, b2, a, b, c, h;
  GEN L = cgetg((long)(sqrt((double)d) * log2(d)), t_VEC);
  b2 = b = (d&1); h = 0;
  if (!b) /* b = 0 treated separately to avoid special cases */
  {
    t = d >> 2; /* (b^2 - D) / 4*/
    for (a=1; a*a<=t; a++)
      if (c = t/a, t == c*a) gel(L,++h) = mkvecsmall3(a,0,c);
    b = 2; b2 = 4;
  }
  /* now b > 0, b = D (mod 2) */
  for ( ; b2 <= dover3; b += 2, b2 = b*b)
  {
    t = (b2 + d) >> 2; /* (b^2 - D) / 4*/
    /* b = a */
    if (c = t/b, t == c*b) gel(L,++h) = mkvecsmall3(b,b,c);
    /* b < a < c */
    for (a = b+1; a*a < t; a++)
      if (c = t/a, t == c*a)
      {
        gel(L,++h) = mkvecsmall3(a, b,c);
        gel(L,++h) = mkvecsmall3(a,-b,c);
      }
    /* a = c */
    if (a * a == t) gel(L,++h) = mkvecsmall3(a,b,a);
  }
  setlg(L,h+1); return L;
}

/* gcd(n, 24) */
static long
GCD24(long n)
{
  switch(n % 24)
  {
    case 0: return 24;
    case 1: return 1;
    case 2: return 2;
    case 3: return 3;
    case 4: return 4;
    case 5: return 1;
    case 6: return 6;
    case 7: return 1;
    case 8: return 8;
    case 9: return 3;
    case 10: return 2;
    case 11: return 1;
    case 12: return 12;
    case 13: return 1;
    case 14: return 2;
    case 15: return 3;
    case 16: return 8;
    case 17: return 1;
    case 18: return 6;
    case 19: return 1;
    case 20: return 4;
    case 21: return 3;
    case 22: return 2;
    case 23: return 1;
    default: return 0;
  }
}

struct gpq_data {
  long p, q;
  GEN sqd; /* sqrt(D), t_REAL */
  GEN u, D;
  GEN pq, pq2; /* p*q, 2*p*q */
  GEN qfpq ; /* class of \P * \Q */
};

/* find P and Q two non principal prime ideals (above p <= q) such that
 *   cl(P) = cl(Q) if P,Q have order 2 in Cl(K).
 *   Ensure that e = 24 / gcd(24, (p-1)(q-1)) = 1 */
/* D t_INT, discriminant */
static void
init_pq(GEN D, struct gpq_data *T)
{
  const long Np = 6547; /* N.B. primepi(50000) = 5133 */
  const ulong maxq = 50000;
  GEN listp = cgetg(Np + 1, t_VECSMALL); /* primes p */
  GEN listP = cgetg(Np + 1, t_VEC); /* primeform(p) if of order 2, else NULL */
  GEN gcd24 = cgetg(Np + 1, t_VECSMALL); /* gcd(p-1, 24) */
  forprime_t S;
  long l = 1;
  double best = 0.;
  ulong q;

  u_forprime_init(&S, 2, ULONG_MAX);
  T->D = D;
  T->p = T->q = 0;
  for(;;)
  {
    GEN Q;
    long i, gcdq, mod;
    int order2, store;
    double t;

    q = u_forprime_next(&S);
    if (best > 0 && q >= maxq)
    {
      if (DEBUGLEVEL)
        pari_warn(warner,"possibly suboptimal (p,q) for D = %Ps", D);
      break;
    }
    if (kroiu(D, q) < 0) continue; /* inert */
    Q = redimag(primeform_u(D, q));
    if (is_pm1(gel(Q,1))) continue; /* Q | q is principal */

    store = 1;
    order2 = hasexp2(Q);
    gcd24[l] = gcdq = GCD24(q-1);
    mod = 24 / gcdq; /* mod must divide p-1 otherwise e > 1 */
    listp[l] = q;
    gel(listP,l) = order2 ? Q : NULL;
    t = (q+1)/(double)(q-1);
    for (i = 1; i < l; i++) /* try all (p, q), p < q in listp */
    {
      long p = listp[i], gcdp = gcd24[i];
      double b;
      /* P,Q order 2 => cl(Q) = cl(P) */
      if (order2 && gel(listP,i) && !gequal(gel(listP,i), Q)) continue;
      if (gcdp % gcdq == 0) store = 0; /* already a better one in the list */
      if ((p-1) % mod) continue;

      b = (t*(p+1)) / (p-1); /* (p+1)(q+1) / (p-1)(q-1) */
      if (b > best) {
        store = 0; /* (p,q) always better than (q,r) for r >= q */
        best = b; T->q = q; T->p = p;
        if (DEBUGLEVEL>2) err_printf("p,q = %ld,%ld\n", p, q);
      }
      /* won't improve with this q as largest member */
      if (best > 0) break;
    }
    /* if !store or (q,r) won't improve on current best pair, forget that q */
    if (store && t*t > best)
      if (++l >= Np) pari_err_BUG("quadhilbert (not enough primes)");
    if (!best) /* (p,q) with p < q always better than (q,q) */
    { /* try (q,q) */
      if (gcdq >= 12 && umodiu(D, q)) /* e = 1 and unramified */
      {
        double b = (t*q) / (q-1); /* q(q+1) / (q-1)^2 */
        if (b > best) {
          best = b; T->q = T->p = q;
          if (DEBUGLEVEL>2) err_printf("p,q = %ld,%ld\n", q, q);
        }
      }
    }
    /* If (p1+1)(q+1) / (p1-1)(q-1) <= best, we can no longer improve
     * even with best p : stop */
    if ((listp[1]+1)*t <= (listp[1]-1)*best) break;
  }
  if (DEBUGLEVEL>1)
    err_printf("(p, q) = %ld, %ld; gain = %f\n", T->p, T->q, 12*best);
}

static GEN
gpq(GEN form, struct gpq_data *T)
{
  pari_sp av = avma;
  long a = form[1], b = form[2], c = form[3];
  long p = T->p, q = T->q;
  GEN form2, w, z;
  int fl, real = 0;

  form2 = qficomp(T->qfpq, mkvec3s(a, -b, c));
  /* form2 and form yield complex conjugate roots : only compute for the
   * lexicographically smallest of the 2 */
  fl = cmpis(gel(form2,1), a);
  if (fl <= 0)
  {
    if (fl < 0) return NULL;
    fl = cmpis(gel(form2,2), b);
    if (fl <= 0)
    {
      if (fl < 0) return NULL;
      /* form == form2 : real root */
      real = 1;
    }
  }

  if (p == 2) { /* (a,b,c) = (1,1,0) mod 2 ? */
    if (a % q == 0 && (a & b & 1) && !(c & 1))
    { /* apply S : make sure that (a,b,c) represents odd values */
      lswap(a,c); b = -b;
    }
  }
  if (a % p == 0 || a % q == 0)
  { /* apply T^k, look for c' = a k^2 + b k + c coprime to N */
    while (c % p == 0 || c % q == 0)
    {
      c += a + b;
      b += a << 1;
    }
    lswap(a, c); b = -b; /* apply S */
  }
  /* now (a,b,c) ~ form and (a,pq) = 1 */

  /* gcd(2a, u) = 2,  w = u mod 2pq, -b mod 2a */
  w = Z_chinese(T->u, stoi(-b), T->pq2, utoipos(a << 1));
  z = double_eta_quotient(utoipos(a), w, T->D, T->p, T->q, T->pq, T->sqd);
  if (real && typ(z) == t_COMPLEX) z = gcopy(gel(z, 1));
  return gerepileupto(av, z);
}

/* returns an equation for the Hilbert class field of Q(sqrt(D)), D < 0
 * fundamental discriminant */
static GEN
quadhilbertimag(GEN D)
{
  GEN L, P, Pi, Pr, qfp, u;
  pari_sp av = avma;
  long h, i, prec;
  struct gpq_data T;
  pari_timer ti;

  if (DEBUGLEVEL>1) timer_start(&ti);
  if (lgefint(D) == 3)
    switch (D[2]) { /* = |D|; special cases where e > 1 */
      case 3:
      case 4:
      case 7:
      case 8:
      case 11:
      case 19:
      case 43:
      case 67:
      case 163: return pol_x(0);
    }
  L = qfbforms(D);
  h = lg(L)-1;
  if ((1L << vals(h)) == h) /* power of 2 */
  { /* check whether > |Cl|/2 elements have order <= 2 ==> 2-elementary */
    long lim = (h>>1) + 1;
    for (i=1; i <= lim; i++)
      if (!uhasexp2(gel(L,i))) break;
    if (i > lim) return GenusFieldQuadImag(D);
  }
  if (DEBUGLEVEL>1) timer_printf(&ti,"class number = %ld",h);
  init_pq(D, &T);
  qfp = primeform_u(D, T.p);
  T.pq =  muluu(T.p, T.q);
  T.pq2 = shifti(T.pq,1);
  if (T.p == T.q)
  {
    GEN qfbp2 = qficompraw(qfp, qfp);
    u = gel(qfbp2,2);
    T.u = modii(u, T.pq2);
    T.qfpq = redimag(qfbp2);
  }
  else
  {
    GEN qfq = primeform_u(D, T.q), bp = gel(qfp,2), bq = gel(qfq,2);
    T.u = Z_chinese(bp, bq, utoipos(T.p << 1), utoipos(T.q << 1));
    /* T.u = bp (mod 2p), T.u = bq (mod 2q) */
    T.qfpq = qficomp(qfp, qfq);
  }
  /* u modulo 2pq */
  prec = LOWDEFAULTPREC;
  Pr = cgetg(h+1,t_VEC);
  Pi = cgetg(h+1,t_VEC);
  for(;;)
  {
    long ex, exmax = 0, r1 = 0, r2 = 0;
    pari_sp av0 = avma;
    T.sqd = sqrtr_abs(itor(D, prec));
    for (i=1; i<=h; i++)
    {
      GEN s = gpq(gel(L,i), &T);
      if (DEBUGLEVEL>3) err_printf("%ld ", i);
      if (!s) continue;
      if (typ(s) != t_COMPLEX) gel(Pr, ++r1) = s; /* real root */
      else                     gel(Pi, ++r2) = s;
      ex = gexpo(s); if (ex > 0) exmax += ex;
    }
    if (DEBUGLEVEL>1) timer_printf(&ti,"roots");
    setlg(Pr, r1+1);
    setlg(Pi, r2+1);
    P = roots_to_pol_r1(shallowconcat(Pr,Pi), 0, r1);
    P = grndtoi(P,&exmax);
    if (DEBUGLEVEL>1) timer_printf(&ti,"product, error bits = %ld",exmax);
    if (exmax <= -10) break;
    avma = av0; prec += nbits2extraprec(prec2nbits(DEFAULTPREC)+exmax);
    if (DEBUGLEVEL) pari_warn(warnprec,"quadhilbertimag",prec);
  }
  return gerepileupto(av,P);
}

GEN
quadhilbert(GEN D, long prec)
{
  GEN d = D;
  quadray_init(&d, NULL, NULL, 0);
  return (signe(d)>0)? quadhilbertreal(D,prec)
                     : quadhilbertimag(d);
}

/* return a vector of all roots of 1 in bnf [not necessarily quadratic] */
static GEN
getallrootsof1(GEN bnf)
{
  GEN T, u, nf = bnf_get_nf(bnf), tu;
  long i, n = bnf_get_tuN(bnf);

  if (n == 2) {
    long N = nf_get_degree(nf);
    return mkvec2(scalarcol_shallow(gen_m1, N),
                  scalarcol_shallow(gen_1, N));
  }
  tu = poltobasis(nf, bnf_get_tuU(bnf));
  T = zk_multable(nf, tu);
  u = cgetg(n+1, t_VEC); gel(u,1) = tu;
  for (i=2; i <= n; i++) gel(u,i) = ZM_ZC_mul(T, gel(u,i-1));
  return u;
}
/* assume bnr has the right conductor */
static GEN
get_lambda(GEN bnr)
{
  GEN bnf = bnr_get_bnf(bnr), nf = bnf_get_nf(bnf), pol = nf_get_pol(nf);
  GEN f = gel(bnr_get_mod(bnr), 1), labas, lamodf, u;
  long a, b, f2, i, lu, v = varn(pol);

  f2 = 2 * itos(gcoeff(f,1,1));
  u = getallrootsof1(bnf); lu = lg(u);
  for (i=1; i<lu; i++)
    gel(u,i) = ZC_hnfrem(gel(u,i), f); /* roots of 1, mod f */
  if (DEBUGLEVEL>1)
    err_printf("quadray: looking for [a,b] != unit mod 2f\n[a,b] = ");
  for (a=0; a<f2; a++)
    for (b=0; b<f2; b++)
    {
      GEN la = deg1pol_shallow(stoi(a), stoi(b), v); /* ax + b */
      if (umodiu(gnorm(mkpolmod(la, pol)), f2) != 1) continue;
      if (DEBUGLEVEL>1) err_printf("[%ld,%ld] ",a,b);

      labas = poltobasis(nf, la);
      lamodf = ZC_hnfrem(labas, f);
      for (i=1; i<lu; i++)
        if (ZV_equal(lamodf, gel(u,i))) break;
      if (i < lu) continue; /* la = unit mod f */
      if (DEBUGLEVEL)
      {
        if (DEBUGLEVEL>1) err_printf("\n");
        err_printf("lambda = %Ps\n",la);
      }
      return labas;
    }
  pari_err_BUG("get_lambda");
  return NULL;
}

static GEN
to_approx(GEN nf, GEN a)
{
  GEN M = nf_get_M(nf);
  return gadd(gel(a,1), gmul(gcoeff(M,1,2),gel(a,2)));
}
/* Z-basis for a (over C) */
static GEN
get_om(GEN nf, GEN a) {
  return mkvec2(to_approx(nf,gel(a,2)),
                to_approx(nf,gel(a,1)));
}

/* Compute all elts in class group G = [|G|,c,g], c=cyclic factors, g=gens.
 * Set list[j + 1] = g1^e1...gk^ek where j is the integer
 *   ek + ck [ e(k-1) + c(k-1) [... + c2 [e1]]...] */
static GEN
getallelts(GEN bnr)
{
  GEN nf, C, c, g, list, pows, gk;
  long lc, i, j, no;

  nf = bnr_get_nf(bnr);
  no = itos( bnr_get_no(bnr) );
  c = bnr_get_cyc(bnr);
  g = bnr_get_gen_nocheck(bnr); lc = lg(c)-1;
  list = cgetg(no+1,t_VEC);
  gel(list,1) = matid(nf_get_degree(nf)); /* (1) */
  if (!no) return list;

  pows = cgetg(lc+1,t_VEC);
  c = leafcopy(c); settyp(c, t_VECSMALL);
  for (i=1; i<=lc; i++)
  {
    long k = itos(gel(c,i));
    c[i] = k;
    gk = cgetg(k, t_VEC); gel(gk,1) = gel(g,i);
    for (j=2; j<k; j++)
      gel(gk,j) = idealmoddivisor(bnr, idealmul(nf, gel(gk,j-1), gel(gk,1)));
    gel(pows,i) = gk; /* powers of g[i] */
  }

  C = cgetg(lc+1, t_VECSMALL); C[1] = c[lc];
  for (i=2; i<=lc; i++) C[i] = C[i-1] * c[lc-i+1];
  /* C[i] = c(k-i+1) * ... * ck */
  /* j < C[i+1] <==> j only involves g(k-i)...gk */
  i = 1;
  for (j=1; j < C[1]; j++)
    gel(list, j+1) = gmael(pows,lc,j);
  while(j<no)
  {
    long k;
    GEN a;
    if (j == C[i+1]) i++;
    a = gmael(pows,lc-i,j/C[i]);
    k = j%C[i] + 1;
    if (k > 1) a = idealmoddivisor(bnr, idealmul(nf, a, gel(list,k)));
    gel(list, ++j) = a;
  }
  return list;
}

/* x quadratic integer (approximate), recognize it. If error return NULL */
static GEN
findbezk(GEN nf, GEN x)
{
  GEN a,b, M = nf_get_M(nf), u = gcoeff(M,1,2);
  long ea, eb;

  /* u t_COMPLEX generator of nf.zk, write x ~ a + b u, a,b in Z */
  b = grndtoi(mpdiv(imag_i(x), gel(u,2)), &eb);
  if (eb > -20) return NULL;
  a = grndtoi(mpsub(real_i(x), mpmul(b,gel(u,1))), &ea);
  if (ea > -20) return NULL;
  return signe(b)? coltoalg(nf, mkcol2(a,b)): a;
}

static GEN
findbezk_pol(GEN nf, GEN x)
{
  long i, lx = lg(x);
  GEN y = cgetg(lx,t_POL);
  for (i=2; i<lx; i++)
    if (! (gel(y,i) = findbezk(nf,gel(x,i))) ) return NULL;
  y[1] = x[1]; return y;
}

/* P approximation computed at initial precision prec. Compute needed prec
 * to know P with 1 word worth of trailing decimals */
static long
get_prec(GEN P, long prec)
{
  long k = gprecision(P);
  if (k == 3) return precdbl(prec); /* approximation not trustworthy */
  k = prec - k; /* lost precision when computing P */
  if (k < 0) k = 0;
  k += nbits2prec(gexpo(P) + 128);
  if (k <= prec) k = precdbl(prec); /* dubious: old prec should have worked */
  return k;
}

/* Compute data for ellphist */
static GEN
ellphistinit(GEN om, long prec)
{
  GEN res,om1b,om2b, om1 = gel(om,1), om2 = gel(om,2);

  if (gsigne(imag_i(gdiv(om1,om2))) < 0) { swap(om1,om2); om = mkvec2(om1,om2); }
  om1b = conj_i(om1);
  om2b = conj_i(om2); res = cgetg(4,t_VEC);
  gel(res,1) = gdivgs(elleisnum(om,2,0,prec),12);
  gel(res,2) = gdiv(PiI2(prec), gmul(om2, imag_i(gmul(om1b,om2))));
  gel(res,3) = om2b; return res;
}

/* Computes log(phi^*(z,om)), using res computed by ellphistinit */
static GEN
ellphist(GEN om, GEN res, GEN z, long prec)
{
  GEN u = imag_i(gmul(z, gel(res,3)));
  GEN zst = gsub(gmul(u, gel(res,2)), gmul(z,gel(res,1)));
  return gsub(ellsigma(om,z,1,prec),gmul2n(gmul(z,zst),-1));
}

/* Computes phi^*(la,om)/phi^*(1,om) where (1,om) is an oriented basis of the
   ideal gf*gc^{-1} */
static GEN
computeth2(GEN om, GEN la, long prec)
{
  GEN p1,p2,res = ellphistinit(om,prec);

  p1 = gsub(ellphist(om,res,la,prec), ellphist(om,res,gen_1,prec));
  p2 = imag_i(p1);
  if (gexpo(real_i(p1))>20 || gexpo(p2)> prec2nbits(minss(prec,realprec(p2)))-10)
    return NULL;
  return gexp(p1,prec);
}

/* Computes P_2(X)=polynomial in Z_K[X] closest to prod_gc(X-th2(gc)) where
   the product is over the ray class group bnr.*/
static GEN
computeP2(GEN bnr, long prec)
{
  long clrayno, i, first = 1;
  pari_sp av=avma, av2;
  GEN listray, P0, P, lanum, la = get_lambda(bnr);
  GEN nf = bnr_get_nf(bnr), f = gel(bnr_get_mod(bnr), 1);
  listray = getallelts(bnr);
  clrayno = lg(listray)-1; av2 = avma;
PRECPB:
  if (!first)
  {
    if (DEBUGLEVEL) pari_warn(warnprec,"computeP2",prec);
    nf = gerepilecopy(av2, nfnewprec_shallow(checknf(bnr),prec));
  }
  first = 0; lanum = to_approx(nf,la);
  P = cgetg(clrayno+1,t_VEC);
  for (i=1; i<=clrayno; i++)
  {
    GEN om = get_om(nf, idealdiv(nf,f,gel(listray,i)));
    GEN s = computeth2(om,lanum,prec);
    if (!s) { prec = precdbl(prec); goto PRECPB; }
    gel(P,i) = s;
  }
  P0 = roots_to_pol(P, 0);
  P = findbezk_pol(nf, P0);
  if (!P) { prec = get_prec(P0, prec); goto PRECPB; }
  return gerepilecopy(av, P);
}

#define nexta(a) (a>0 ? -a : 1-a)
static GEN
do_compo(GEN A0, GEN B)
{
  long a, i, l = lg(B), v = fetch_var_higher();
  GEN A, z;
  /* now v > x = pol_x(0) > nf variable */
  B = leafcopy(B); setvarn(B, v);
  for (i = 2; i < l; i++) gel(B,i) = monomial(gel(B,i), l-i-1, 0);
  /* B := x^deg(B) B(v/x) */
  A = A0 = leafcopy(A0); setvarn(A0, v);
  for  (a = 0;; a = nexta(a))
  {
    if (a) A = RgX_translate(A0, stoi(a));
    z = resultant(A,B); /* in variable 0 */
    if (issquarefree(z)) break;
  }
  (void)delete_var(); return z;
}
#undef nexta

static GEN
galoisapplypol(GEN nf, GEN s, GEN x)
{
  long i, lx = lg(x);
  GEN y = cgetg(lx,t_POL);

  for (i=2; i<lx; i++) gel(y,i) = galoisapply(nf,s,gel(x,i));
  y[1] = x[1]; return y;
}
/* x quadratic, write it as ua + v, u,v rational */
static GEN
findquad(GEN a, GEN x, GEN p)
{
  long tu, tv;
  pari_sp av = avma;
  GEN u,v;
  if (typ(x) == t_POLMOD) x = gel(x,2);
  if (typ(a) == t_POLMOD) a = gel(a,2);
  u = poldivrem(x, a, &v);
  u = simplify_shallow(u); tu = typ(u);
  v = simplify_shallow(v); tv = typ(v);
  if (!is_scalar_t(tu)) pari_err_TYPE("findquad", u);
  if (!is_scalar_t(tv)) pari_err_TYPE("findquad", v);
  x = deg1pol(u, v, varn(a));
  if (typ(x) == t_POL) x = gmodulo(x,p);
  return gerepileupto(av, x);
}
static GEN
findquad_pol(GEN p, GEN a, GEN x)
{
  long i, lx = lg(x);
  GEN y = cgetg(lx,t_POL);
  for (i=2; i<lx; i++) gel(y,i) = findquad(a, gel(x,i), p);
  y[1] = x[1]; return y;
}
static GEN
compocyclo(GEN nf, long m, long d)
{
  GEN sb,a,b,s,p1,p2,p3,res,polL,polLK,nfL, D = nf_get_disc(nf);
  long ell,vx;

  p1 = quadhilbertimag(D);
  p2 = polcyclo(m,0);
  if (d==1) return do_compo(p1,p2);

  ell = m&1 ? m : (m>>2);
  if (absequalui(ell,D)) /* ell = |D| */
  {
    p2 = gcoeff(nffactor(nf,p2),1,1);
    return do_compo(p1,p2);
  }
  if (ell%4 == 3) ell = -ell;
  /* nf = K = Q(a), L = K(b) quadratic extension = Q(t) */
  polLK = quadpoly(stoi(ell)); /* relative polynomial */
  res = rnfequation2(nf, polLK);
  vx = nf_get_varn(nf);
  polL = gsubst(gel(res,1),0,pol_x(vx)); /* = charpoly(t) */
  a = gsubst(lift_shallow(gel(res,2)), 0,pol_x(vx));
  b = gsub(pol_x(vx), gmul(gel(res,3), a));
  nfL = nfinit(polL, DEFAULTPREC);
  p1 = gcoeff(nffactor(nfL,p1),1,1);
  p2 = gcoeff(nffactor(nfL,p2),1,1);
  p3 = do_compo(p1,p2); /* relative equation over L */
  /* compute non trivial s in Gal(L / K) */
  sb= gneg(gadd(b, RgX_coeff(polLK,1))); /* s(b) = Tr(b) - b */
  s = gadd(pol_x(vx), gsub(sb, b)); /* s(t) = t + s(b) - b */
  p3 = gmul(p3, galoisapplypol(nfL, s, p3));
  return findquad_pol(nf_get_pol(nf), a, p3);
}

/* I integral ideal in HNF. (x) = I, x small in Z ? */
static long
isZ(GEN I)
{
  GEN x = gcoeff(I,1,1);
  if (signe(gcoeff(I,1,2)) || !equalii(x, gcoeff(I,2,2))) return 0;
  return is_bigint(x)? -1: itos(x);
}

/* Treat special cases directly. return NULL if not special case */
static GEN
treatspecialsigma(GEN bnr)
{
  GEN bnf = bnr_get_bnf(bnr), nf = bnf_get_nf(bnf);
  GEN f = gel(bnr_get_mod(bnr), 1),  D = nf_get_disc(nf);
  GEN p1, p2;
  long Ds, fl, tryf, i = isZ(f);

  if (i == 1) return quadhilbertimag(D); /* f = 1 */

  if (absequaliu(D,3)) /* Q(j) */
  {
    if (i == 4 || i == 5 || i == 7) return polcyclo(i,0);
    if (!absequaliu(gcoeff(f,1,1),9) || !absequaliu(Z_content(f),3)) return NULL;
    /* f = P_3^3 */
    p1 = mkpolmod(bnf_get_tuU(bnf), nf_get_pol(nf));
    return gadd(pol_xn(3,0), p1); /* x^3+j */
  }
  if (absequaliu(D,4)) /* Q(i) */
  {
    if (i == 3 || i == 5) return polcyclo(i,0);
    if (i != 4) return NULL;
    p1 = mkpolmod(bnf_get_tuU(bnf), nf_get_pol(nf));
    return gadd(pol_xn(2,0), p1); /* x^2+i */
  }
  Ds = smodis(D,48);
  if (i)
  {
    if (i==2 && Ds%16== 8) return compocyclo(nf, 4,1);
    if (i==3 && Ds% 3== 1) return compocyclo(nf, 3,1);
    if (i==4 && Ds% 8== 1) return compocyclo(nf, 4,1);
    if (i==6 && Ds   ==40) return compocyclo(nf,12,1);
    return NULL;
  }

  p1 = gcoeff(f,1,1); /* integer > 0 */
  tryf = itou_or_0(p1); if (!tryf) return NULL;
  p2 = gcoeff(f,2,2); /* integer > 0 */
  if (is_pm1(p2)) fl = 0;
  else {
    if (Ds % 16 != 8 || !absequaliu(Z_content(f),2)) return NULL;
    fl = 1; tryf >>= 1;
  }
  if (tryf <= 3 || umodiu(D, tryf) || !uisprime(tryf)) return NULL;
  if (fl) tryf <<= 2;
  return compocyclo(nf,tryf,2);
}

GEN
quadray(GEN D, GEN f, long prec)
{
  GEN bnr, y, bnf;
  pari_sp av = avma;

  if (isint1(f)) return quadhilbert(D, prec);
  quadray_init(&D, f, &bnf, prec);
  bnr = Buchray(bnf, f, nf_INIT|nf_GEN);
  if (is_pm1(bnr_get_no(bnr))) { avma = av; return pol_x(0); }
  if (signe(D) > 0)
    y = bnrstark(bnr,NULL,prec);
  else
  {
    bnr = gel(bnrconductor_i(bnr,NULL,2), 2);
    y = treatspecialsigma(bnr);
    if (!y) y = computeP2(bnr, prec);
  }
  return gerepileupto(av, y);
}
