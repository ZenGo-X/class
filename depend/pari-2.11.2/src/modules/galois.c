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

/**************************************************************/
/*              Galois group for degree in [8, 11]            */
/**************************************************************/

#define NMAX 11 /* maximum degree */

typedef GEN PERM;
typedef PERM *GROUP;
typedef struct {
  PERM *a;
  long nm, nv;
} resolv; /* resolvent */

typedef struct {
  long pr, prmax, N;
  GEN p, r, coef;
} buildroot;

static long isin_G_H(buildroot *BR, long n1, long n2);

static long *par_vec;
/* k-1 entries filled so far
 * m = maximal allowed value, n = sum to reach with remaining elements */
static void
do_par(GEN T, long k, long n, long m)
{
  long i;
  if (n <= 0)
  {
    GEN t = cgetg(k, t_VECSMALL);
    for (i=1; i<k; i++) t[i] = par_vec[i];
    gel(T, ++T[0]) = t; return;
  }
  if (n < m) m = n;
  for (i=1; i<=m; i++) { par_vec[k] = i; do_par(T, k+1, n-i, i); }
}

/* compute the partitions of n, as decreasing t_VECSMALLs */
static GEN
partitions_galois(long n)
{
  pari_sp av;
  long i, p;
  GEN T;

  switch(n) /* optimized for galoismoduloX ... */
  {
    case 8: p = 22; break;
    case 9: p = 30; break;
    case 10:p = 42; break;
    default:
      if (n < 0) pari_err_TYPE("partitions_galois", stoi(n));
      av = avma; p = itos( numbpart(stoi(n)) ); avma = av; break;
  }
  T = new_chunk(p + 1); T[0] = 0;
  par_vec = cgetg(n+1, t_VECSMALL); /* not Garbage Collected later */
  do_par(T,1,n,n);
  if (DEBUGLEVEL > 7)
  {
    err_printf("Partitions of %ld (%ld)\n",n, p);
    for (i=1; i<=p; i++) err_printf("i = %ld: %Ps\n",i,gel(T,i));
  }
  T[0] = evallg(p + 1) | evaltyp(t_VEC); return T;
}

/* affect to the permutation x the N arguments that follow */
static void
_aff(long N, PERM x,...)
{
  va_list args; long i;
  va_start(args,x); for (i=1; i<=N; i++) x[i] = va_arg(args,int);
  va_end(args);
}

/* return an array of length |len| from the arguments (for galoismodulo) */
static GEN
_gr(long len,...)
{
  va_list args;
  long i, l = labs(len);
  GEN x = new_chunk(l+1);

  va_start(args,len); x[0] = len;
  for (i=1; i<=l; i++) x[i] = va_arg(args,int);
  va_end(args); return x;
}

/* return a VECSMALL of length l from the arguments (for galoismodulo11) */
static GEN
_typ(long l,...)
{
  va_list args;
  long i;
  GEN x = cgetg(l+1, t_VECSMALL);

  va_start(args,l);
  for (i=1; i<=l; i++) x[i] = va_arg(args,int);
  va_end(args); return x;
}

/* create a permutation with the N arguments of the function */
static PERM
_cr(long N, long a,...)
{
  static long x[NMAX+1];
  va_list args;
  long i;

  va_start(args, a); x[0] = N; x[1] = a;
  for (i=2; i<=N; i++) x[i] = va_arg(args,int);
  va_end(args); return x;
}

static PERM
permmul(PERM s1, PERM s2)
{
  long i, n1 = s1[0];
  PERM s3 = (PERM)stack_malloc((n1+1) * sizeof(long));
  for (i=1; i<=n1; i++) s3[i] = s1[s2[i]];
  s3[0] = n1; return s3;
}

static void
printperm(PERM perm)
{
  long i, n = perm[0];
  err_printf("(");
  for (i=1; i<=n; i++) err_printf(" %d",perm[i]);
  err_printf(" )\n");
}

static int
raye(long *g, long num)
{
  long i, nb = labs(g[0]);
  for (i=1; i<=nb; i++)
    if (g[i] == num) return 0;
  return 1;
}

/* we can never determine the group completely in there */
static long
rayergroup11(long EVEN, long num, long *gr)
{
  long r = 0;

  if (EVEN)
    switch(num)
    {
      case 2: case 5:
        if (gr[3]) { gr[3]=0; r++; }
      case 3: case 6: case 7:
        if (gr[2]) { gr[2]=0; r++; }
      case 4:
        if (gr[1]) { gr[1]=0; r++; }
    }
  else
    switch(num)
    {
      case 2: case 3:
        if (gr[1]) { gr[1]=0; r++; }
    }
  return r;
}

static long
rayergroup(long EVEN, long **GR, long num, long *gr)
{
  long i,nbgr,r;

  if (!GR) return rayergroup11(EVEN,num,gr);
  nbgr = lg(GR); r = 0 ;
  if (EVEN)
  {
    for (i=1; i<nbgr; i++)
      if (gr[i] && GR[i][0] < 0 && raye(GR[i],num)) { gr[i]=0; r++; }
  }
  else
  {
    for (i=1; i<nbgr; i++)
      if (gr[i] && GR[i][0] > 0 && raye(GR[i],num)) { gr[i]=0; r++; }
  }
  return r;
}

static long
galmodp(long EVEN, GEN pol, GEN dpol, GEN TYP, long *gr, long **GR)
{
  long i,k,l,n,nbremain;
  GEN p1, dtyp;
  forprime_t T;

  switch(degpol(pol))
  {
    case  8: nbremain = EVEN? 28: 22; break;
    case  9: nbremain = EVEN? 18: 16; break;
    case 10: nbremain = EVEN? 12: 33; break;
    default: nbremain = EVEN?  5:  3; break; /* case 11 */
  }

  u_forprime_init(&T, 2, ULONG_MAX);
  dtyp = new_chunk(NMAX+1);
  k = gr[0]; for (i=1; i<k; i++) gr[i]=1;
  for (k=1; k<15; k++)
  {
    ulong p = u_forprime_next(&T);
    if (!umodiu(dpol,p)) continue; /* p divides dpol */

    p1 = gel(Flx_degfact(ZX_to_Flx(pol,p),p),1);
    l = lg(p1);
    dtyp[0] = evaltyp(t_VECSMALL)|evallg(l);
    for (i=1; i<l; i++) dtyp[i] = p1[l-i]; /* decreasing order */
    n = RgV_isin(TYP, dtyp);
    if (!n) return 1; /* only for N=11 */
    nbremain -= rayergroup(EVEN,GR,n,gr);
    if (nbremain==1) return 1;
  }
  return 0;
}

static void
preci(GEN o, long p)
{
  long i, l = lg(o);
  for (i=1; i<l; i++)
  {
    GEN x = gel(o,i);
    if (typ(x)==t_COMPLEX) { setprec(gel(x,1),p); setprec(gel(x,2),p); } else setprec(x,p);
  }
}
static void
fixprec(buildroot *BR)
{
  GEN r = BR->r;
  long i, l = lg(r), p = BR->pr;

  if (p > BR->prmax) pari_err_BUG("fixprex [precision too large]");
  for (i = 1; i < l; i++) preci(gel(r,i), p);
}

static long
getpreci(buildroot *BR)
{
  GEN x = gmael(BR->r,1,1);
  return (typ(x)==t_COMPLEX)? realprec(gel(x,1)): realprec(x);
}

#define setcard_obj(x,n) ((x)[0] = (PERM)(n))
#define getcard_obj(x)   ((long)((x)[0]))

/* allocate a list of m arrays of length n (index 0 is codeword) */
static PERM *
alloc_pobj(long n, long m)
{
  long i;
  PERM *g = (PERM*) stack_malloc( (m+1)*sizeof(PERM) + (n+1)*m * sizeof(long) );
  PERM gpt = (PERM) (g + (m+1));

  for (i=1; i<=m; i++) { g[i] = gpt; gpt += (n+1); }
  setcard_obj(g, m); return g;
}

static GROUP
allocgroup(long n, long card)
{
  GROUP gr = alloc_pobj(n,card);
  long i;

  for (i=1; i<=card; i++) gr[i][0] = n;
  return gr;
}

static pariFILE *
galopen(const char *pre, long n, long n1, long n2)
{
  pari_sp av = avma;
  char *s = stack_malloc(strlen(pari_datadir) + 3 + 4 * 20 + 1 + 3);
  pariFILE *f;

  (void)sprintf(s, "%s/galdata/%s%ld_%ld_%ld", pari_datadir, pre, n, n1, n2);
  f = pari_fopengz(s);
  if (!f) pari_err_FILE("galois file",s);
  avma = av; return f;
}

static char
bin(char c)
{
  if (c>='0' && c<='9') c -= '0';
  else if (c>='A' && c<='Z') c -= 'A'-10;
  else if (c>='a' && c<='z') c -= 'a'-36;
  else pari_err_TYPE("bin [not alphanumeric]", stoi(c));
  return c;
}

#define BUFFS 512
/* fill in g[i][j] (i<=n, j<=m) with (buffered) data from f->file */
static void
read_obj(PERM *g, pariFILE *f, long n, long m)
{
  long i, j, k, N = m*n;
  char *ch = stack_malloc(N);
  pari_fread_chars(ch, N, f->file);
  for (k = 0, i = 1; i <= n; i++)
    for (j = 1; j <= m; j++,k++) g[i][j] = bin(ch[k]);
  pari_fclose(f);
}
#undef BUFFS

/* the first 8 bytes contain size data (possibly padded with \0) */
static GROUP
lirecoset(long n1, long n2, long n)
{
  GROUP gr;
  char c, ch[8];
  long m, cardgr;
  pariFILE *f = galopen("COS", n, n1, n2);
  pari_fread_chars(&c, 1, f->file); m=bin(c);
  pari_fread_chars(&c, 1, f->file);
  pari_fread_chars(ch, 6, f->file); cardgr=atol(ch);
  gr=allocgroup(m,cardgr);
  read_obj(gr, f,cardgr,m); return gr;
}

static void
lireresolv(long n1, long n2, long n, resolv *R)
{
  char ch[5];
  long nm, nv;
  pariFILE *f = galopen("RES", n, n1, n2);
  pari_fread_chars(ch,5,f->file); nm = atol(ch);
  pari_fread_chars(ch,3,f->file); nv = atol(ch);
  R->a = alloc_pobj(nv,nm);
  read_obj(R->a, f,nm,nv);
  R->nm = nm;
  R->nv = nv;
}

static int
cmp_re(GEN x, GEN y)
{
  if (typ(x) != t_COMPLEX) return -1;
  if (typ(y) != t_COMPLEX) return 1; /* t_REALS are smallest */
  return gcmp(gel(x,1), gel(y,1));
}

/* multiply the r o bb. Sort first to detect pairs of conjugate */
static GEN
Monomial(GEN r, PERM bb, long nbv)
{
  GEN t, R = cgetg(nbv + 1, t_VEC);
  long i, s = 1;

  for (i = 1; i <= nbv; i++)
  {
    t = gel(r,bb[i]);
    if (typ(t) == t_COMPLEX && signe(gel(t,1)) < 0) { s = -s; t = gneg(t); }
    gel(R,i) = t;
  }
  if (nbv > 2)
    gen_sort_inplace(R, (void*)&cmp_re, cmp_nodata, NULL);
  else if (nbv == 2 && typ(gel(R,2)) != t_COMPLEX)
    swap(gel(R,1), gel(R,2));
  t = NULL;
  for (i=1; i<=nbv; i++)
  {
    GEN c = gel(R,i);
    if (typ(c) == t_COMPLEX && i < nbv)
    { /* detect conjugates */
      GEN n = gel(R,++i);
      if (!abscmprr(gel(n,1), gel(c,1))
       && !abscmprr(gel(n,2), gel(c,2))
       && signe(gel(c,2)) != signe(gel(n,2)))
        c = addrr(sqrr(gel(c,1)), sqrr(gel(c,2)));
      else
        c = gmul(c,n);
    }
    t = t? gmul(t, c): c;
  }
  if (s < 0) t = gneg(t);
  return t;
}

/* sum(i = 1, R->nm, Monomial(r, R->a[i], R->nv)). Sort real / imaginary part
 * separately by increasing absolute values, to increase stability */
static GEN
gpolynomial(GEN r, resolv *R)
{
  GEN RE = cgetg(R->nm+1, t_VEC), IM = cgetg(R->nm+1, t_VEC), re, im;
  long i, k;
  for (i = k = 1; i <= R->nm; i++)
  {
    GEN m = Monomial(r,R->a[i], R->nv);
    if (typ(m) == t_REAL)
      gel(RE, i) = m;
    else {
      gel(RE, i)   = gel(m,1);
      gel(IM, k++) = gel(m,2);
    }
  }
  setlg(IM, k);
  gen_sort_inplace(RE, (void*)&abscmprr, cmp_nodata, NULL);
  gen_sort_inplace(IM, (void*)&abscmprr, cmp_nodata, NULL);
  re = gel(RE,1);
  for (i = 2; i <= R->nm; i++) re = addrr(re, gel(RE,i));
  if (k == 1) return re;
  im = gel(IM,1);
  for (i = 2; i < k; i++) im = addrr(im, gel(IM,i));
  return mkcomplex(re, im);
}

static void
zaux1(GEN *z, GEN *r)
{
  GEN p2,p1;
  p2=gsub(r[1], gadd(r[2],r[5]));
  p2=gmul(p2, gsub(r[2],r[5]));
  p1=gmul(p2,r[1]);
  p2=gsub(r[3],gadd(r[2],r[4]));
  p2=gmul(p2,gsub(r[4],r[2]));
  p1=gadd(p1,gmul(p2,r[3]));
  p2=gmul(r[5],gsub(r[4],r[5]));
  z[1]=gadd(p1,gmul(p2,r[4]));

  p2=gsub(r[1],gadd(r[3],r[4]));
  p2=gmul(p2,gsub(r[3],r[4]));
  p1=gmul(p2,r[1]);
  p2=gsub(r[5],gadd(r[3],r[2]));
  p2=gmul(p2,gsub(r[2],r[3]));
  p1=gadd(p1,gmul(p2,r[5]));
  p2=gmul(r[4],gsub(r[2],r[4]));
  z[2]=gadd(p1,gmul(p2,r[2]));
}

static void
zaux(GEN *z, GEN *r)
{
  zaux1(z, r); zaux1(z+2, r+5);
}

static GEN
gpoly(GEN rr, long n1, long n2)
{
  const long N = lg(rr)-1;
  GEN p1,p2,z[6], *r = (GEN*)rr; /* syntaxic kludge */
  long i,j;

  if (N==8)
  {
    if (n1==47 && n2==46)
    {
      p1=gsub(r[3],r[4]);
      for (i=1; i<3; i++) for (j=i+1; j<5; j++) p1 = gmul(p1,gsub(r[i],r[j]));
      for (i=5; i<8; i++) for (j=i+1; j<9; j++) p1 = gmul(p1,gsub(r[i],r[j]));
      p2=r[1];
      for (i=2; i<5; i++) p2=gadd(p2,r[i]);
      for (i=5; i<9; i++) p2=gsub(p2,r[i]);
    }
    else /* n1==44 && n2==40 */
    {
      for (i=1; i<5; i++) z[i] = gadd(r[2*i-1],r[2*i]);
      p1 = gsub(r[1],r[2]);
      for (i=2; i<5; i++) p1 = gmul(p1,gsub(r[2*i-1],r[2*i]));
      p2=gsub(z[3],z[4]);
      for (i=1; i<3; i++) for (j=i+1; j<5; j++) p2 = gmul(p2,gsub(z[i],z[j]));
    }
    return gmul(p1,p2);
  }

  if (N==9)
  {
    if (n1==31 && n2==29)
    {
      p1=gsub(r[2],r[3]);
      for (j=2; j<4; j++) p1 = gmul(p1,gsub(r[1],r[j]));
      for (i=4; i<6; i++) for (j=i+1; j<7; j++) p1 = gmul(p1,gsub(r[i],r[j]));
      p2 = gsub(r[8],r[9]);
      for (j=8; j<10; j++) p2 = gmul(p2,gsub(r[7],r[j]));
    }
    else /* ((n1==34 && n2==31) || (n1=33 && n2==30)) */
    {
      p1=r[1]; for (i=2; i<4; i++) p1=gadd(p1,r[i]);
      p2=r[4]; for (i=5; i<7; i++) p2=gadd(p2,r[i]);
      p1=gmul(p1,p2);
      p2=r[7]; for (i=8; i<10; i++) p2=gadd(p2,r[i]);
    }
    return gmul(p1,p2);
  }

  if (N==10)
  {
    if ((n1==45 && n2==43) || (n1==44 && n2==42))
    {
      p1=r[1]; for (i=2; i<6; i++) p1=gadd(p1,r[i]);
      p2=r[6]; for (i=7; i<11; i++) p2=gadd(p2,r[i]);
      return gmul(p1,p2);
    }
    else if ((n1==45 && n2==39) || (n1==44 && n2==37))
    {
      p1 = gadd(r[1],r[2]);
      for (i=2; i<6; i++) p1 = gmul(p1,gadd(r[2*i-1],r[2*i]));
      return p1;
    }
    else if ((n1==43 && n2==41) || (n1==33 && n2==27))
    {
      p1=gsub(r[4],r[5]);
      for (i=1; i<4; i++) for (j=i+1; j<6; j++) p1=gmul(p1,gsub(r[i],r[j]));
      p2=gsub(r[9],r[10]);
      for (i=6; i<9; i++) for (j=i+1; j<11; j++) p2=gmul(p2,gsub(r[i],r[j]));
      return gmul(p1,p2);
    }
    else if ((n1==43 && n2==33) || (n1==42 && n2==28) || (n1==41 && n2==27)
          || (n1==40 && n2==21))
    {
      p2=gadd(r[2],r[5]);
      p2=gsub(p2,gadd(r[3],r[4]));
      p1=gmul(p2,r[1]);
      p2=gsub(r[3],gadd(r[4],r[5]));
      p1=gadd(p1,gmul(p2,r[2]));
      p2=gsub(r[4],r[5]);
      p1=gadd(p1,gmul(p2,r[3]));
      z[1]=gadd(p1,gmul(r[4],r[5]));

      p2=gadd(r[7],r[10]);
      p2=gsub(p2,gadd(r[8],r[9]));
      p1=gmul(p2,r[6]);
      p2=gsub(r[8],gadd(r[9],r[10]));
      p1=gadd(p1,gmul(p2,r[7]));
      p2=gsub(r[9],r[10]);
      p1=gadd(p1,gmul(p2,r[8]));
      z[2]=gadd(p1,gmul(r[9],r[10]));
      return gadd(gsqr(z[1]), gsqr(z[2]));
    }
    else if (n1==41 && n2==40)
    {
      p1=gsub(r[4],r[5]);
      for (i=1; i<4; i++) for (j=i+1; j<6; j++) p1 = gmul(p1,gsub(r[i],r[j]));
      p2=gsub(r[9],r[10]);
      for (i=6; i<9; i++) for (j=i+1; j<11; j++) p2 = gmul(p2,gsub(r[i],r[j]));
      return gadd(p1,p2);
    }
    else if ((n1==41 && n2==22) || (n1==40 && n2==11) || (n1==17 && n2==5)
            || (n1==10 && n2==4) || (n1==9 && n2==3) || (n1==6 && n2==1))
    {
      p1=gadd(r[1],r[6]);
      for (i=2; i<6; i++) p1=gmul(p1,gadd(r[i],r[i+5]));
      return p1;
    }
    else if ((n1==39 && n2==38) || (n1==29 && n2==25))
    {
      for (i=1; i<6; i++) z[i]=gadd(r[2*i-1],r[2*i]);
      p1=gsub(r[1],r[2]);
      for (i=2; i<6; i++) p1=gmul(p1,gsub(r[2*i-1],r[2*i]));
      p2=gsub(z[4],z[5]);
      for (i=1; i<4; i++) for (j=i+1; j<6; j++) p2=gmul(p2,gsub(z[i],z[j]));
      return gmul(p1,p2);
    }
    else if ((n1==39 && n2==36) || (n1==37 && n2==34) || (n1==29 && n2==23)
          || (n1==24 && n2==15))
    {
      for (i=1; i<6; i++) z[i]=gadd(r[2*i-1],r[2*i]);
      p1=gsub(z[4],z[5]); p2=gmul(gsub(z[3],z[4]),gsub(z[3],z[5]));
      for (i=1; i<3; i++) for (j=i+1; j<6; j++) p2=gmul(p2,gsub(z[i],z[j]));
      return gmul(p1,p2);
    }
    else if ((n1==39 && n2==29) || (n1==38 && n2==25) || (n1==37 && n2==24)
          || (n1==36 && n2==23) || (n1==34 && n2==15))
    {
      for (i=1; i<6; i++) z[i]=gadd(r[2*i-1],r[2*i]);
      p2=gadd(z[2],z[5]);
      p2=gsub(p2,gadd(z[3],z[4]));
      p1=gmul(p2,z[1]);
      p2=gsub(z[3],gadd(z[4],z[5]));
      p1=gadd(p1,gmul(p2,z[2]));
      p2=gsub(z[4],z[5]);
      p1=gadd(p1,gmul(p2,z[3]));
      p1=gadd(p1,gmul(z[4],z[5]));
      return gsqr(p1);
    }
    else if ((n1==39 && n2==22) || (n1==38 && n2==12) || (n1==36 && n2==11)
          || (n1==29 && n2== 5) || (n1==25 && n2== 4) || (n1==23 && n2== 3)
          || (n1==16 && n2== 2) || (n1==14 && n2== 1))
    {
      p1=r[1]; for (i=2; i<6; i++) p1=gadd(p1,r[2*i-1]);
      p2=r[2]; for (i=2; i<6; i++) p2=gadd(p2,r[2*i]);
      return gmul(p1,p2);
    }
    else if (n1==28 && n2==18)
    {
      zaux(z, r);
      p1=gmul(z[1],gsub(z[3],z[4]));
      p2=gmul(z[2],gadd(z[3],z[4])); return gadd(p1,p2);
    }
    else if (n1==27 && n2==20)
    {
      zaux(z, r); p1=gmul(z[1],z[3]); p2=gmul(z[2],z[4]);
      p1 = gsub(p1,p2); p2=r[1];
      for (i=2; i<6 ; i++) p2=gadd(p2,r[i]);
      for (   ; i<11; i++) p2=gsub(p2,r[i]);
      return gmul(p1,p2);
    }
    else if (n1==27 && n2==19)
    {
      zaux(z, r); p1=gmul(z[1],z[3]); p2=gmul(z[2],z[4]);
      return gsub(p1,p2);
    }
    else if ((n1==27 && n2==17) || (n1==21 && n2==9))
    {
      zaux(z, r); p1=gmul(z[1],z[3]); p2=gmul(z[2],z[4]);
      return gadd(p1,p2);
    }
    else if (n1==23 && n2==16)
    {
      for (i=1; i<6; i++) z[i]=gadd(r[2*i-1],r[2*i]);
      p1=gsub(z[1],gadd(z[2],z[5])); p1=gmul(p1,gsub(z[2],z[5]));
      p2=gmul(p1,z[1]); p1=gsub(z[3],gadd(z[2],z[4]));
      p1=gmul(  p1,gsub(z[4],z[2])); p2=gadd(p2,gmul(p1,z[3]));
      p1=gmul(z[5],gsub(z[4],z[5])); p2=gadd(p2,gmul(p1,z[4]));
      p1=gsub(r[1],r[2]);
      for (i=2; i<6; i++) p1=gmul(p1,gsub(r[2*i-1],r[2*i]));
      return gmul(p1,p2);
    }
    else if (n1==22 && n2==12)
    {
      for (i=1; i<6; i++) z[i]=gadd(r[i],r[i+5]);
      p1=gsub(r[1],r[6]);
      for (i=2; i<6; i++) p1=gmul(p1,gsub(r[i],r[i+5]));
      p2=gsub(z[4],z[5]);
      for (i=1; i<4; i++) for (j=i+1; j<6; j++) p2=gmul(p2,gsub(z[i],z[j]));
      return gmul(p1,p2);
    }
    else if ((n1==22 && n2==11) || (n1==5 && n2==3))
    {
      for (i=1; i<6; i++) z[i]=gadd(r[i],r[i+5]);
      p1=gsub(z[4],z[5]); p2=gmul(gsub(z[3],z[4]),gsub(z[3],z[5]));
      for (i=1; i<3; i++) for (j=i+1; j<6; j++) p2=gmul(p2,gsub(z[i],z[j]));
      return gmul(p1,p2);
    }
    else if ((n1==22 && n2==5) || (n1==12 && n2==4) || (n1==11 && n2==3))
    {
      for (i=1; i<6; i++) z[i]=gadd(r[i],r[i+5]);
      p2=gadd(z[2],z[5]); p2=gsub(p2,gadd(z[3],z[4])); p1=gmul(p2,z[1]);
      p2=gsub(z[3],gadd(z[4],z[5])); p1=gadd(p1,gmul(p2,z[2]));
      p2=gsub(z[4],z[5]);
      p1=gadd(p1,gmul(p2,z[3])); p1=gadd(p1,gmul(z[4],z[5]));
      return gsqr(p1);
    }
    else if (n1==21 && n2==10)
    {
      zaux(z, r); p1=gmul(z[1],z[4]); p2=gmul(z[2],z[3]);
      return gsub(p1,p2);
    }
  }
  pari_err_TYPE("gpoly [undefined invariant polynomial]", mkvecsmall2(n1,n2));
  return NULL; /* LCOV_EXCL_LINE */
}

/* a is a t_VECSMALL representing a polynomial */
static GEN
new_pol(long N, GEN r, GEN a)
{
  long i, j, l = lg(a);
  GEN x, z, v = cgetg(N+1, t_VEC);
  for (i=1; i<=N; i++)
  {
    z = gel(r,i); x = gaddsg(a[2], z);
    for (j = 3; j < l; j++) x = gaddsg(a[j], gmul(z,x));
    gel(v,i) = x;
  }
  return gclone(v);
}

/* BR->r[l], BR->coef[l] hold data related to Tschirnausen transform of
 * degree l - 1 */
static void
tschirn(buildroot *BR)
{
  long i, k, v = varn(BR->p), l = lg(BR->r);
  GEN a, h, r;

  if (l >= BR->N) pari_err_BUG("tschirn");
  if (DEBUGLEVEL)
    err_printf("\n$$$$$ Tschirnhaus transformation of degree %ld: $$$$$\n",l-1);

  a = gel(BR->coef,l); /* fill with random polynomial of degree <= l-1 */
  do
  {
    a[1]=0;
    for (i=2; i < l+2; i++) a[i] = random_bits(3) + 1;
    h = Flx_to_ZX(Flx_renormalize(a,l+2));
  } while (degpol(h) <= 0 || !ZX_is_squarefree(h));
  setvarn(h, v); k = 0;
  (void)ZXQ_charpoly_sqf(BR->p, h, &k, v);
  a[2] += k;

  r = gel(BR->r,1);
  preci(r, BR->prmax); /* max accuracy original roots */
  vectrunc_append(BR->r, new_pol(BR->N, r, a));
  fixprec(BR); /* restore accuracy */
}

static GEN
sortroots(GEN newr, GEN oldr)
{
  long e, e0, i, j, k, l = lg(newr);
  GEN r = cgetg(l, t_VEC), z = cgetg(l, t_VEC), t = const_vecsmall(l-1, 1);
  k = 0; /* gcc -Wall */
  for (i=1; i<l; i++)
  {
    e0 = EXPOBITS;
    for (j=1; j<l; j++)
      if (t[j])
      {
        e = gexpo(gsub(gel(oldr,i), gel(newr,j)));
        if (e < e0) { e0 = e; k = j; }
      }
    gel(z,i) = gel(newr,k); t[k] = 0;
  }
  for (i=1; i<l; i++) gel(r,i) = gel(z,i);
  return r;
}

static void
delete_roots(buildroot *BR)
{
  GEN r = BR->r;
  long i, l = lg(r);
  for (i = 1; i < l; i++) gunclone(gel(r,i));
  setlg(r, 1);
}

/* increase the roots accuracy */
static void
moreprec(buildroot *BR)
{
  long d = BR->pr - BR->prmax;
  if (d > 0)
  { /* recompute roots */
    pari_sp av = avma;
    long l = lg(BR->r);
    GEN ro;

    if (d < BIGDEFAULTPREC-2) d = BIGDEFAULTPREC-2;
    BR->prmax = maxss(BR->prmax+d, (long)(BR->prmax * 1.2));
    if (DEBUGLEVEL)
      { err_printf("$$$$$ New prec = %ld\n",BR->prmax); err_flush(); }
    ro = sortroots(QX_complex_roots(BR->p,BR->prmax), gel(BR->r,1));
    delete_roots(BR);
    vectrunc_append(BR->r, gclone(ro));
    for (d = 2; d < l; d++)
      vectrunc_append(BR->r, new_pol(BR->N, ro, gel(BR->coef,d)));
    avma = av;
  }
  fixprec(BR);
}

/* determine "sufficient" extra bit-precision such that we may decide
 * (heuristic) whether z is an integer. */
static GEN
get_ro(long N, GEN rr, PERM S1, PERM S2, resolv *R)
{
  GEN r = cgetg(N+1, t_VEC);
  long i;
  for (i=1; i<=N; i++) r[i] = rr[ S1[S2[i] ] ];
  return R->a? gpolynomial(r, R): gpoly(r,R->nm,R->nv);
}
/* typ(z) = t_REAL, return zi = t_INT approximation */
static long
sufprec_r(GEN z)
{
  long p = bit_prec(z);
  /* bit accuracy of fractional part large enough ? */
  return ( p - expo(z) > maxss(3*32, (long)0.2*p) );
}
/* typ(z) = t_REAL or t_COMPLEX, return zi = t_INT approximation */
static long
sufprec(GEN z)
{
  if (typ(z) == t_REAL)
    return sufprec_r(z);
  else
    return sufprec_r(gel(z,2)) && sufprec_r(gel(z,1));
}

static GEN
get_ro_perm(PERM S1, PERM S2, long d, resolv *R, buildroot *BR)
{
  GEN ro, roi;
  long e;
  for (;;)
  {
    ro = get_ro(BR->N, gel(BR->r, d), S1,S2,R); roi = grndtoi(ro, &e);
    if (e < 0)
    {
      if (e < -64 || sufprec(ro)) break;
      e = 0;
    }
    BR->pr += nbits2extraprec(e + 10);
    moreprec(BR);
  }
  if (e > -10 || typ(roi) == t_COMPLEX) return NULL;
  /* compute with 128 more bits */
  BR->pr += MEDDEFAULTPREC-2;
  moreprec(BR);
  ro = get_ro(BR->N, gel(BR->r, d), S1,S2,R);
  BR->pr -= MEDDEFAULTPREC-2;
  fixprec(BR);
  /* ro closer to roi (32 more bits) ? */
  return (gexpo(gsub(ro, roi)) < e - 32) ? roi: NULL;
}

static void
dbg_rac(long nri,long nbracint,long numi[],GEN racint[],long multi[])
{
  long k;
  err_printf("\t# rational integer roots = %ld:",nbracint-nri);
  for (k = nri+1; k <= nbracint; k++) err_printf(" %ld^%ld", numi[k], multi[k]);
  err_printf("\n");
  for (k = nri+1; k <= nbracint; k++) err_printf("\t%2ld: %Ps\n", numi[k], racint[k]);
  err_flush();
}

#define M 2521
/* return NULL if not included, the permutation of the roots otherwise */
static PERM
check_isin(buildroot *BR, resolv *R, GROUP tau, GROUP ss)
{
  long nogr, nocos, init, i, j, k, l, d;
  pari_sp av1 = avma, av2;
  long nbgr,nbcos,nbracint,nbrac,lastnbri,lastnbrm;
  static long numi[M],numj[M],lastnum[M],multi[M],norac[M],lastnor[M];
  GEN  racint[M], roint;

  if (getpreci(BR) != BR->pr) fixprec(BR);
  nbcos = getcard_obj(ss);
  nbgr  = getcard_obj(tau);
  lastnbri = lastnbrm = -1; nbracint = nbrac = 0; /* gcc -Wall*/
  for (nogr=1; nogr<=nbgr; nogr++)
  {
    PERM T = tau[nogr];
    if (DEBUGLEVEL) err_printf("    ----> Group # %ld/%ld:\n",nogr,nbgr);
    init = 0; d = 1;
    for (;;)
    {
      if (!init)
      {
        av2 = avma; nbrac = nbracint = 0;
        for (nocos=1; nocos<=nbcos; nocos++, avma = av2)
        {
          roint = get_ro_perm(T, ss[nocos], d, R, BR);
          if (!roint) continue;

          nbrac++;
          if (nbrac >= M)
          {
            pari_warn(warner, "more than %ld rational integer roots\n", M);
            avma = av1; goto NEXT;
          }
          for (j=1; j<=nbracint; j++)
            if (equalii(roint,racint[j])) { multi[j]++; break; }
          if (j > nbracint)
          {
            nbracint = j; multi[j] = 1; numi[j] = nocos;
            racint[j] = gerepileuptoint(av2,roint); av2 = avma;
          }
          numj[nbrac] = nocos; norac[nbrac] = j;
        }
        if (DEBUGLEVEL) dbg_rac(0,nbracint,numi,racint,multi);
        for (i=1; i<=nbracint; i++)
          if (multi[i]==1) return permmul(T, ss[numi[i]]);
        init = 1;
      }
      else
      {
        nbrac = nbracint = 0;
        for (l=1; l<=lastnbri; l++, avma = av1)
        {
          long nri = nbracint;
          av2 = avma;
          for (k=1; k<=lastnbrm; k++)
            if (lastnor[k]==l)
            {
              nocos = lastnum[k];
              roint = get_ro_perm(T, ss[nocos], d, R, BR);
              if (!roint) { avma = av2; continue; }

              nbrac++;
              for (j=nri+1; j<=nbracint; j++)
                if (equalii(roint,racint[j])) { multi[j]++; break; }
              if (j > nbracint)
              {
                nbracint = j; multi[j] = 1; numi[j] = nocos;
                racint[j] = gerepileuptoint(av2,roint); av2=avma;
              }
              numj[nbrac] = nocos; norac[nbrac] = j;
            }
          if (DEBUGLEVEL) dbg_rac(nri,nbracint,numi,racint,multi);
          for (i=nri+1; i<=nbracint; i++)
            if (multi[i]==1) return permmul(T, ss[numi[i]]);
        }
      }
      avma = av1; if (!nbracint) break;

      lastnbri = nbracint; lastnbrm = nbrac;
      for (j=1; j<=nbrac; j++) { lastnum[j] = numj[j]; lastnor[j] = norac[j]; }

NEXT:
      if (DEBUGLEVEL) {
        err_printf("        all integer roots are double roots\n");
        err_printf("      Working with polynomial #%ld:\n", d+1);
      }
      if (++d >= lg(BR->r)) tschirn(BR);
    }
  }
  return NULL;
}
#undef M

/* DEGREE 8 */
static long
galoisprim8(long EVEN, buildroot *BR)
{
  long rep;

  rep=isin_G_H(BR,50,43);
  if (rep) return EVEN? 37: 43;
  if (!EVEN) return 50;
  rep=isin_G_H(BR,49,48);
  if (!rep) return 49;
  rep=isin_G_H(BR,48,36);
  if (!rep) return 48;
  rep=isin_G_H(BR,36,25);
  return rep? 25: 36;
}

static long
galoisimpodd8(buildroot *BR, long nh)
{
  long rep;
  if (nh!=47) goto IMPODD_8_6;
  rep=isin_G_H(BR,47,46);
  if (!rep) goto IMPODD_8_5;
  rep=isin_G_H(BR,46,28);
  if (rep) goto IMPODD_8_7; else return 46;

IMPODD_8_5:
  rep=isin_G_H(BR,47,35);
  if (rep) goto IMPODD_8_9; else return 47;

IMPODD_8_6:
  rep=isin_G_H(BR,44,40);
  if (rep) goto IMPODD_8_10; else goto IMPODD_8_11;

IMPODD_8_7:
  rep=isin_G_H(BR,28,21);
  if (rep) return 21; else goto IMPODD_8_33;

IMPODD_8_9:
  rep=isin_G_H(BR,35,31);
  if (rep) goto IMPODD_8_13; else goto IMPODD_8_14;

IMPODD_8_10:
  rep=isin_G_H(BR,40,26);
  if (rep) goto IMPODD_8_15; else goto IMPODD_8_16;

IMPODD_8_11:
  rep=isin_G_H(BR,44,38);
  if (rep) goto IMPODD_8_17; else goto IMPODD_8_18;

IMPODD_8_12:
  rep=isin_G_H(BR,16,7);
  if (rep) goto IMPODD_8_19; else return 16;

IMPODD_8_13:
  rep=isin_G_H(BR,31,21);
  return rep? 21: 31;

IMPODD_8_14:
  rep=isin_G_H(BR,35,30);
  if (rep) goto IMPODD_8_34; else goto IMPODD_8_20;

IMPODD_8_15:
  rep=isin_G_H(BR,26,16);
  if (rep) goto IMPODD_8_12; else goto IMPODD_8_21;

IMPODD_8_16:
  rep=isin_G_H(BR,40,23);
  if (rep) goto IMPODD_8_22; else return 40;

IMPODD_8_17:
  rep=isin_G_H(BR,38,31);
  if (rep) goto IMPODD_8_13; else return 38;

IMPODD_8_18:
  rep=isin_G_H(BR,44,35);
  if (rep) goto IMPODD_8_9; else return 44;

IMPODD_8_19:
  rep=isin_G_H(BR,7,1);
  return rep? 1: 7;

IMPODD_8_20:
  rep=isin_G_H(BR,35,28);
  if (rep) goto IMPODD_8_7; else goto IMPODD_8_23;

IMPODD_8_21:
  rep=isin_G_H(BR,26,17);
  if (rep) goto IMPODD_8_24; else goto IMPODD_8_25;

IMPODD_8_22:
  rep=isin_G_H(BR,23,8);
  if (rep) goto IMPODD_8_26; else return 23;

IMPODD_8_23:
  rep=isin_G_H(BR,35,27);
  if (rep) goto IMPODD_8_27; else goto IMPODD_8_28;

IMPODD_8_24:
  rep=isin_G_H(BR,17,7);
  if (rep) goto IMPODD_8_19; else return 17;

IMPODD_8_25:
  rep=isin_G_H(BR,26,15);
  if (rep) goto IMPODD_8_29; else return 26;

IMPODD_8_26:
  rep=isin_G_H(BR,8,1);
  return rep? 1: 8;

IMPODD_8_27:
  rep=isin_G_H(BR,27,16);
  if (rep) goto IMPODD_8_12; else return 27;

IMPODD_8_28:
  rep=isin_G_H(BR,35,26);
  if (rep) goto IMPODD_8_15; else return 35;

IMPODD_8_29:
  rep=isin_G_H(BR,15,7);
  if (rep) goto IMPODD_8_19;
  rep=isin_G_H(BR,15,6);
  if (!rep) goto IMPODD_8_32;
  rep=isin_G_H(BR,6,1);
  return rep? 1: 6;

IMPODD_8_32:
  rep=isin_G_H(BR,15,8);
  if (rep) goto IMPODD_8_26; else return 15;

IMPODD_8_33:
  rep=isin_G_H(BR,28,16);
  if (rep) goto IMPODD_8_12; else return 28;

IMPODD_8_34:
  rep=isin_G_H(BR,30,21);
  return rep? 21: 30;
}

static long
galoisimpeven8(buildroot *BR, long nh)
{
   long rep;
   if (nh!=45) goto IMPEVEN_8_6;
   rep=isin_G_H(BR,45,42);
   if (!rep) goto IMPEVEN_8_5;
  rep=isin_G_H(BR,42,34);
  if (rep) goto IMPEVEN_8_7; else goto IMPEVEN_8_8;

IMPEVEN_8_5:
  rep=isin_G_H(BR,45,41);
  if (rep) goto IMPEVEN_8_9; else return 45;

IMPEVEN_8_6:
  rep=isin_G_H(BR,39,32);
  if (rep) goto IMPEVEN_8_10; else goto IMPEVEN_8_11;

IMPEVEN_8_7:
  rep=isin_G_H(BR,34,18);
  if (rep) goto IMPEVEN_8_21; else goto IMPEVEN_8_45;

IMPEVEN_8_8:
  rep=isin_G_H(BR,42,33);
  if (rep) goto IMPEVEN_8_14; else return 42;

IMPEVEN_8_9:
  rep=isin_G_H(BR,41,34);
  if (rep) goto IMPEVEN_8_7; else goto IMPEVEN_8_15;

IMPEVEN_8_10:
  rep=isin_G_H(BR,32,22);
  if (rep) goto IMPEVEN_8_16; else goto IMPEVEN_8_17;

IMPEVEN_8_11:
  rep=isin_G_H(BR,39,29);
  if (rep) goto IMPEVEN_8_18; else goto IMPEVEN_8_19;

IMPEVEN_8_12:
  rep=isin_G_H(BR,14,4);
  return rep? 4: 14;

IMPEVEN_8_14:
  rep=isin_G_H(BR,33,18);
  if (rep) goto IMPEVEN_8_21; else goto IMPEVEN_8_22;

IMPEVEN_8_15:
  rep=isin_G_H(BR,41,33);
  if (rep) goto IMPEVEN_8_14; else goto IMPEVEN_8_23;

IMPEVEN_8_16:
  rep=isin_G_H(BR,22,11);
  if (rep) goto IMPEVEN_8_24; else goto IMPEVEN_8_25;

IMPEVEN_8_17:
  rep=isin_G_H(BR,32,13);
  if (rep) goto IMPEVEN_8_26; else goto IMPEVEN_8_27;

IMPEVEN_8_18:
  rep=isin_G_H(BR,29,22);
  if (rep) goto IMPEVEN_8_16; else goto IMPEVEN_8_28;

IMPEVEN_8_19:
  rep=isin_G_H(BR,39,24);
  if (rep) goto IMPEVEN_8_29; else return 39;

IMPEVEN_8_20:
  rep=isin_G_H(BR,9,4);
  if (rep) return 4; else goto IMPEVEN_8_30;

IMPEVEN_8_21:
  rep=isin_G_H(BR,18,10);
  if (rep) goto IMPEVEN_8_31; else goto IMPEVEN_8_32;

IMPEVEN_8_22:
  rep=isin_G_H(BR,33,13);
  if (rep) goto IMPEVEN_8_26; else return 33;

IMPEVEN_8_23:
  rep=isin_G_H(BR,41,29);
  if (rep) goto IMPEVEN_8_18; else goto IMPEVEN_8_33;

IMPEVEN_8_24:
  rep=isin_G_H(BR,11,5);
  if (rep) return 5; else goto IMPEVEN_8_34;

IMPEVEN_8_25:
  rep=isin_G_H(BR,22,9);
  if (rep) goto IMPEVEN_8_20; else return 22;

IMPEVEN_8_26:
  rep=isin_G_H(BR,13,3);
  return rep? 3: 13;

IMPEVEN_8_27:
  rep=isin_G_H(BR,32,12);
  if (rep) goto IMPEVEN_8_35; else return 32;

IMPEVEN_8_28:
  rep=isin_G_H(BR,29,20);
  if (rep) goto IMPEVEN_8_36; else goto IMPEVEN_8_37;

IMPEVEN_8_29:
  rep=isin_G_H(BR,24,14);
  if (rep) goto IMPEVEN_8_12; else goto IMPEVEN_8_38;

IMPEVEN_8_30:
  rep=isin_G_H(BR,9,3);
  if (rep) return 3; else goto IMPEVEN_8_39;

IMPEVEN_8_31:
  rep=isin_G_H(BR,10,2);
  return rep? 2: 10;

IMPEVEN_8_32:
  rep=isin_G_H(BR,18,9);
  if (rep) goto IMPEVEN_8_20; else return 18;

IMPEVEN_8_33:
  rep=isin_G_H(BR,41,24);
  if (rep) goto IMPEVEN_8_29; else return 41;

IMPEVEN_8_34:
  rep=isin_G_H(BR,11,4);
  if (rep) return 4; else goto IMPEVEN_8_44;

IMPEVEN_8_35:
  rep=isin_G_H(BR,12,5);
  return rep? 5: 12;

IMPEVEN_8_36:
  rep=isin_G_H(BR,20,10);
  if (rep) goto IMPEVEN_8_31; else return 20;

IMPEVEN_8_37:
  rep=isin_G_H(BR,29,19);
  if (rep) goto IMPEVEN_8_40; else goto IMPEVEN_8_41;

IMPEVEN_8_38:
  rep=isin_G_H(BR,24,13);
  if (rep) goto IMPEVEN_8_26; else goto IMPEVEN_8_42;

IMPEVEN_8_39:
  rep=isin_G_H(BR,9,2);
  return rep? 2: 9;

IMPEVEN_8_40:
  rep=isin_G_H(BR,19,10);
  if (rep) goto IMPEVEN_8_31; else goto IMPEVEN_8_43;

IMPEVEN_8_41:
  rep=isin_G_H(BR,29,18);
  if (rep) goto IMPEVEN_8_21; else return 29;

IMPEVEN_8_42:
  rep=isin_G_H(BR,24,9);
  if (rep) goto IMPEVEN_8_20; else return 24;

IMPEVEN_8_43:
  rep=isin_G_H(BR,19,9);
  if (rep) goto IMPEVEN_8_20; else return 19;

IMPEVEN_8_44:
  rep=isin_G_H(BR,11,2);
  return rep? 2: 11;

IMPEVEN_8_45:
  rep=isin_G_H(BR,34,14);
  if (rep) goto IMPEVEN_8_12; else return 34;
}

static long
closure8(long EVEN, buildroot *BR)
{
  long rep;

  if (!EVEN)
  {
    rep=isin_G_H(BR,50,47);
    if (rep) return galoisimpodd8(BR,47);
    rep=isin_G_H(BR,50,44);
    if (rep) return galoisimpodd8(BR,44);
  }
  else
  {
    rep=isin_G_H(BR,49,45);
    if (rep) return galoisimpeven8(BR,45);
    rep=isin_G_H(BR,49,39);
    if (rep) return galoisimpeven8(BR,39);
  }
  return galoisprim8(EVEN, BR);
}

static GROUP
initgroup(long n, long nbgr)
{
  GROUP t = allocgroup(n,nbgr);
  PERM ID =  t[1];
  long i;
  for (i = 1; i <= n; i++) ID[i] = i;
  return t;
}

static PERM
data8(long N, long n1, long n2, GROUP *t)
{
  switch(n1)
  {
    case 7: if (n2!=1) break;
      *t=initgroup(N,2);
      _aff(N, (*t)[2], 1, 2, 3, 4, 6, 5, 8, 7);
      return (*t)[1];
    case 9: if (n2!=4) break;
      *t=initgroup(N,2);
      _aff(N, (*t)[2], 1, 2, 4, 3, 5, 6, 8, 7);
      return (*t)[1];
    case 10: if (n2!=2) break;
      *t=initgroup(N,2);
      _aff(N, (*t)[2], 1, 2, 3, 4, 6, 5, 8, 7);
      return (*t)[1];
    case 11:
      switch(n2)
      {
        case 2:
          *t=initgroup(N,2);
          _aff(N, (*t)[2], 1, 2, 5, 6, 3, 4, 8, 7);
          return _cr(N, 1, 3, 5, 8, 2, 4, 6, 7);
        case 4:
          *t=initgroup(N,1);
          return _cr(N, 1, 3, 7, 5, 2, 4, 8, 6);
      }break;
    case 14: if (n2!=4) break;
      *t=initgroup(N,1);
      return _cr(N, 1, 2, 4, 3, 5, 6, 8, 7);
    case 15: if (n2!=6 && n2!=8) break;
      *t=initgroup(N,2);
      _aff(N, (*t)[2], 1, 2, 3, 4, 6, 5, 8, 7);
      return (*t)[1];
    case 16: if (n2!=7) break;
      *t=initgroup(N,2);
      _aff(N, (*t)[2], 1, 2, 3, 4, 5, 6, 8, 7);
      return (*t)[1];
    case 18:
      switch(n2)
      {
        case 9: *t=initgroup(N,3);
          _aff(N, (*t)[2], 1, 5, 3, 7, 2, 6, 4, 8);
          _aff(N, (*t)[3], 1, 2, 3, 4, 6, 5, 8, 7);
          return (*t)[1];
        case 10: *t=initgroup(N,3);
          _aff(N, (*t)[2], 1, 6, 3, 8, 2, 5, 4, 7);
          _aff(N, (*t)[3], 1, 5, 3, 7, 2, 6, 4, 8);
          return (*t)[1];
      }break;
    case 19: if (n2!=9) break;
      *t=initgroup(N,1);
      return _cr(N, 1, 5, 3, 8, 2, 6, 4, 7);
    case 20: if (n2!=10) break;
      *t=initgroup(N,2);
      _aff(N, (*t)[2], 1, 2, 3, 4, 5, 6, 8, 7);
      return (*t)[1];
    case 22:
      switch(n2)
      {
        case 9: *t=initgroup(N,6);
          _aff(N, (*t)[2], 1, 2, 7, 8, 3, 4, 6, 5);
          _aff(N, (*t)[3], 1, 2, 7, 8, 3, 4, 5, 6);
          _aff(N, (*t)[4], 1, 2, 5, 6, 3, 4, 8, 7);
          _aff(N, (*t)[5], 1, 2, 5, 6, 3, 4, 7, 8);
          _aff(N, (*t)[6], 1, 2, 3, 4, 5, 6, 8, 7);
          return _cr(N, 1, 3, 5, 7, 2, 4, 6, 8);
        case 11: *t=initgroup(N,6);
          _aff(N, (*t)[2], 1, 2, 5, 6, 7, 8, 4, 3);
          _aff(N, (*t)[3], 1, 2, 5, 6, 7, 8, 3, 4);
          _aff(N, (*t)[4], 1, 2, 3, 4, 7, 8, 6, 5);
          _aff(N, (*t)[5], 1, 2, 3, 4, 7, 8, 5, 6);
          _aff(N, (*t)[6], 1, 2, 3, 4, 5, 6, 8, 7);
          return (*t)[1];
      }break;
    case 23: if (n2!=8) break;
      *t=initgroup(N,1);
      return _cr(N, 1, 2, 3, 4, 6, 5, 8, 7);
    case 26: if (n2!=15 && n2!=17) break;
      *t=initgroup(N,2);
      _aff(N, (*t)[2], 1, 2, 3, 4, 5, 6, 8, 7);
      return (*t)[1];
    case 28: if (n2!=21) break;
      *t=initgroup(N,1);
      return _cr(N, 1, 2, 3, 4, 7, 8, 5, 6);
    case 29: if (n2!=18 && n2!=19) break;
      *t=initgroup(N,2);
      _aff(N, (*t)[2], 1, 2, 3, 4, 5, 6, 8, 7);
      return (*t)[1];
    case 30: if (n2!=21) break;
      *t=initgroup(N,1);
      return _cr(N, 1, 2, 3, 4, 7, 8, 5, 6);
    case 31: if (n2!=21) break;
      *t=initgroup(N,3);
      _aff(N, (*t)[2], 1, 2, 3, 4, 7, 8, 5, 6);
      _aff(N, (*t)[3], 1, 2, 5, 6, 7, 8, 3, 4);
      return (*t)[1];
    case 32: if (n2!=12 && n2!=13) break;
      *t=initgroup(N,2);
      _aff(N, (*t)[2], 1, 2, 3, 4, 5, 6, 8, 7);
      return (*t)[1];
    case 33:
      switch(n2)
      {
        case 13: *t=initgroup(N,1);
          return _cr(N, 1, 5, 2, 6, 3, 7, 4, 8);
        case 18: *t=initgroup(N,1);
          return _cr(N, 1, 2, 5, 6, 3, 4, 7, 8);
      }break;
    case 34:
      switch(n2)
      {
        case 14: *t=initgroup(N,3);
          _aff(N, (*t)[2], 1, 2, 3, 4, 5, 8, 6, 7);
          _aff(N, (*t)[3], 1, 2, 3, 4, 5, 7, 8, 6);
          return _cr(N, 1, 5, 2, 6, 3, 7, 4, 8);
        case 18: *t=initgroup(N,1);
          return _cr(N, 1, 2, 5, 6, 3, 4, 8, 7);
      }break;
    case 39: if (n2!=24) break;
      *t=initgroup(N,2);
      _aff(N, (*t)[2], 1, 2, 3, 4, 5, 6, 8, 7);
      return (*t)[1];
    case 40: if (n2!=23) break;
      *t=initgroup(N,2);
      _aff(N, (*t)[2], 1, 2, 3, 4, 5, 6, 8, 7);
      return (*t)[1];
    case 41:
      switch(n2)
      {
        case 24: *t=initgroup(N,1);
          return _cr(N, 1, 5, 2, 6, 3, 7, 4, 8);
        case 29: *t=initgroup(N,1);
          return _cr(N, 1, 2, 5, 6, 3, 4, 7, 8);
      }break;
    case 42: if (n2!=34) break;
      *t=initgroup(N,1);
      return _cr(N, 1, 2, 3, 4, 5, 6, 8, 7);
    case 45: if (n2!=41 && n2!=42) break;
      *t=initgroup(N,2);
      _aff(N, (*t)[2], 1, 2, 3, 4, 5, 6, 8, 7);
      return (*t)[1];
    case 46: if (n2!=28) break;
      *t=initgroup(N,1);
      return _cr(N, 1, 2, 5, 6, 3, 4, 7, 8);
    case 47: if (n2!=35) break;
      *t=initgroup(N,1);
      return _cr(N, 1, 2, 5, 6, 3, 4, 7, 8);
    case 49: if (n2!=48) break;
      *t=initgroup(N,2);
      _aff(N, (*t)[2], 1, 2, 3, 4, 5, 6, 8, 7);
      return (*t)[1];
  }
  *t=initgroup(N,1); return (*t)[1];
}

static long
galoismodulo8(long EVEN, GEN pol, GEN dpol)
{
  long res, gr[51];
  pari_sp av = avma;
  long **GR = (long**)cgeti(49);
  GEN TYP = partitions_galois(8);

/* List of possible types in group j: GR[j][0] = #GR[j] if
 * the group is odd, - #GR[j] if even */
  GR[ 1]= _gr(  4, 1,5,15,22);
  GR[ 2]= _gr( -3, 1,5,15);
  GR[ 3]= _gr( -2, 1,5);
  GR[ 4]= _gr( -3, 1,5,15);
  GR[ 5]= _gr( -3, 1,5,15);
  GR[ 6]= _gr(  5, 1,4,5,15,22);
  GR[ 7]= _gr(  5, 1,3,5,15,22);
  GR[ 8]= _gr(  5, 1,4,5,15,22);
  GR[ 9]= _gr( -4, 1,3,5,15);
  GR[10]= _gr( -4, 1,3,5,15);
  GR[11]= _gr( -4, 1,3,5,15);
  GR[12]= _gr( -5, 1,5,9,15,20);
  GR[13]= _gr( -4, 1,5,9,20);
  GR[14]= _gr( -4, 1,5,9,15);
  GR[15]= _gr(  6, 1,3,4,5,15,22);
  GR[16]= _gr(  5, 1,3,5,15,22);
  GR[17]= _gr(  7, 1,3,5,11,13,15,22);
  GR[18]= _gr( -4, 1,3,5,15);
  GR[19]= _gr( -5, 1,3,5,12,15);
  GR[20]= _gr( -4, 1,3,5,15);
  GR[21]= _gr(  5, 1,3,5,13,15);
  GR[22]= _gr( -4, 1,3,5,15);
  GR[23]= _gr(  7, 1,4,5,9,15,20,22);
  GR[24]= _gr( -6, 1,3,5,9,15,20);
  GR[25]= _gr( -3, 1,5,21);
  GR[26]= _gr(  8, 1,3,4,5,11,13,15,22);
  GR[27]= _gr(  8, 1,2,3,4,5,13,15,22);
  GR[28]= _gr(  7, 1,3,5,12,13,15,22);
  GR[29]= _gr( -5, 1,3,5,12,15);
  GR[30]= _gr(  7, 1,3,4,5,11,13,15);
  GR[31]= _gr(  7, 1,2,3,4,5,13,15);
  GR[32]= _gr( -6, 1,3,5,9,15,20);
  GR[33]= _gr( -6, 1,3,5,9,15,20);
  GR[34]= _gr( -5, 1,3,5,9,15);
  GR[35]= _gr( 10, 1,2,3,4,5,11,12,13,15,22);
  GR[36]= _gr( -5, 1,5,9,20,21);
  GR[37]= _gr( -5, 1,5,9,15,21);
  GR[38]= _gr( 11, 1,2,3,4,5,9,10,13,15,19,20);
  GR[39]= _gr( -7, 1,3,5,9,12,15,20);
  GR[40]= _gr( 10, 1,3,4,5,9,11,13,15,20,22);
  GR[41]= _gr( -7, 1,3,5,9,12,15,20);
  GR[42]= _gr( -8, 1,3,5,6,8,9,15,20);
  GR[43]= _gr(  8, 1,4,5,9,15,19,21,22);
  GR[44]= _gr( 14, 1,2,3,4,5,9,10,11,12,13,15,19,20,22);
  GR[45]= _gr( -9, 1,3,5,6,8,9,12,15,20);
  GR[46]= _gr( 10, 1,3,5,6,8,9,12,13,15,22);
  GR[47]= _gr( 16, 1,2,3,4,5,6,7,8,9,11,12,13,14,15,20,22);
  GR[48]= _gr( -8, 1,3,5,9,12,15,20,21);

  gr[0]=51; res = galmodp(EVEN,pol,dpol,TYP,gr,GR);
  avma=av; if (!res) return 0;
  return EVEN? 49: 50;
}

/* DEGREE 9 */
static long
galoisprim9(long EVEN, buildroot *BR)
{
  long rep;

  if (!EVEN)
  {
    rep=isin_G_H(BR,34,26);
    if (!rep) return 34;
    rep=isin_G_H(BR,26,19);
    if (!rep) return 26;
    rep=isin_G_H(BR,19,16);
    if (rep) return 16;
    rep=isin_G_H(BR,19,15);
    return rep? 15: 19;
  }
  rep=isin_G_H(BR,33,32);
  if (!rep) goto PRIM_9_7;
  rep=isin_G_H(BR,32,27);
  return rep? 27: 32;

PRIM_9_7:
  rep=isin_G_H(BR,33,23);
  if (!rep) return 33;
  rep=isin_G_H(BR,23,14);
  if (!rep) return 23;
  rep=isin_G_H(BR,14,9);
  return rep? 9: 14;
}

static long
galoisimpodd9(buildroot *BR)
{
  long rep;

  rep=isin_G_H(BR,31,29);
  if (!rep) goto IMPODD_9_5;
  rep=isin_G_H(BR,29,20);
  if (!rep) return 29;
IMPODD_9_3:
  rep=isin_G_H(BR,20,12);
  if (!rep) return 20;
IMPODD_9_4:
  rep=isin_G_H(BR,12,4);
  return rep? 4: 12;

IMPODD_9_5:
  rep=isin_G_H(BR,31,28);
  if (!rep) goto IMPODD_9_9;
  rep=isin_G_H(BR,28,22);
  if (!rep) return 28;
IMPODD_9_7:
  rep=isin_G_H(BR,22,13);
  if (!rep) return 22;
IMPODD_9_8:
  rep=isin_G_H(BR,13,4);
  return rep? 4: 13;

IMPODD_9_9:
  rep=isin_G_H(BR,31,24);
  if (!rep) return 31;
  rep=isin_G_H(BR,24,22);
  if (rep) goto IMPODD_9_7;
  rep=isin_G_H(BR,24,20);
  if (rep) goto IMPODD_9_3;
  rep=isin_G_H(BR,24,18);
  if (!rep) return 24;
  rep=isin_G_H(BR,18,13);
  if (rep) goto IMPODD_9_8;
  rep=isin_G_H(BR,18,12);
  if (rep) goto IMPODD_9_4;
  rep=isin_G_H(BR,18,8);
  if (!rep) return 18;
  rep=isin_G_H(BR,8,4);
  return rep? 4: 8;
}

static long
galoisimpeven9(buildroot *BR)
{
  long rep;

  rep=isin_G_H(BR,30,25);
  if (!rep) goto IMPEVEN_9_7;
  rep=isin_G_H(BR,25,17);
  if (!rep) return 25;
IMPEVEN_9_3:
  rep=isin_G_H(BR,17,7);
  if (!rep) goto IMPEVEN_9_5;
IMPEVEN_9_4:
  rep=isin_G_H(BR,7,2);
  return rep? 2: 7;

IMPEVEN_9_5:
  rep=isin_G_H(BR,17,6);
  if (!rep) return 17;
IMPEVEN_9_6:
  rep=isin_G_H(BR,6,1);
  return rep? 1: 6;

IMPEVEN_9_7:
  rep=isin_G_H(BR,30,21);
  if (!rep) return 30;
  rep=isin_G_H(BR,21,17);
  if (rep) goto IMPEVEN_9_3;
  rep=isin_G_H(BR,21,11);
  if (!rep) goto IMPEVEN_9_13;
  rep=isin_G_H(BR,11,7);
  if (rep) goto IMPEVEN_9_4;
  rep=isin_G_H(BR,11,5);
  if (!rep) return 11;
  rep=isin_G_H(BR,5,2);
  return rep? 2: 5;

IMPEVEN_9_13:
  rep=isin_G_H(BR,21,10);
  if (!rep) return 21;
  rep=isin_G_H(BR,10,6);
  if (rep) goto IMPEVEN_9_6;
  rep=isin_G_H(BR,10,3);
  if (!rep) return 10;
  rep=isin_G_H(BR,3,1);
  return rep? 1: 3;
}

static long
closure9(long EVEN, buildroot *BR)
{
  long rep;
  if (!EVEN)
  {
    rep=isin_G_H(BR,34,31);
    if (rep) return galoisimpodd9(BR);
  }
  else
  {
    rep=isin_G_H(BR,33,30);
    if (rep) return galoisimpeven9(BR);
  }
  return galoisprim9(EVEN, BR);
}

static PERM
data9(long N, long n1, long n2, GROUP *t)
{
  switch(n1)
  {
    case 6: if (n2!=1) break;
      *t=initgroup(N,3);
      _aff(N, (*t)[2], 1, 2, 3, 4, 5, 6, 8, 9, 7);
      _aff(N, (*t)[3], 1, 2, 3, 4, 5, 6, 9, 7, 8);
      return (*t)[1];
    case 7: if (n2!=2) break;
      *t=initgroup(N,3);
      _aff(N, (*t)[2], 1, 2, 3, 4, 5, 6, 8, 9, 7);
      _aff(N, (*t)[3], 1, 2, 3, 4, 5, 6, 9, 7, 8);
      return (*t)[1];
    case 8: if (n2!=4) break;
      *t=initgroup(N,2);
      _aff(N, (*t)[2], 1, 4, 7, 2, 5, 8, 3, 6, 9);
      return (*t)[1];
    case 12: if (n2!=4) break;
      *t=initgroup(N,3);
      _aff(N, (*t)[2], 1, 2, 3, 4, 5, 6, 8, 9, 7);
      _aff(N, (*t)[3], 1, 2, 3, 4, 5, 6, 9, 7, 8);
      return (*t)[1];
    case 13: if (n2!=4) break;
      *t=initgroup(N,1);
      return _cr(N, 1, 4, 7, 2, 5, 8, 3, 6, 9);
    case 14: if (n2!=9) break;
      *t=initgroup(N,3);
      _aff(N, (*t)[2], 1, 2, 3, 5, 6, 4, 9, 7, 8);
      _aff(N, (*t)[3], 1, 2, 3, 6, 4, 5, 8, 9, 7);
      return (*t)[1];
    case 17: if (n2!=6) break;
      *t=initgroup(N,2);
      _aff(N, (*t)[2], 1, 2, 3, 7, 8, 9, 4, 5, 6);
      return (*t)[1];
    case 21: if (n2!=10) break;
      *t=initgroup(N,2);
      _aff(N, (*t)[2], 1, 2, 3, 7, 8, 9, 4, 5, 6);
      return (*t)[1];
    case 33: if (n2!=32) break;
      *t=initgroup(N,2);
      _aff(N, (*t)[2], 1, 2, 3, 4, 5, 6, 7, 9, 8);
      return (*t)[1];
  }
  *t=initgroup(N,1); return (*t)[1];
}

static long
galoismodulo9(long EVEN, GEN pol, GEN dpol)
{
  long res, gr[35];
  pari_sp av = avma;
  long **GR = (long**) cgeti(33);
  GEN TYP = partitions_galois(9);

  /* 42 TYPES ORDONNES CROISSANT (T[1],...,T[30])*/

  GR[ 1]= _gr( -3, 1,12,30);
  GR[ 2]= _gr( -2, 1,12);
  GR[ 3]= _gr( -4, 1,5,12,30);
  GR[ 4]= _gr(  4, 1,4,12,26);
  GR[ 5]= _gr( -3, 1,5,12);
  GR[ 6]= _gr( -4, 1,10,12,30);
  GR[ 7]= _gr( -3, 1,10,12);
  GR[ 8]= _gr(  5, 1,4,5,12,26);
  GR[ 9]= _gr( -4, 1,5,12,18);
  GR[10]= _gr( -6, 1,5,10,12,25,30);
  GR[11]= _gr( -5, 1,5,10,12,25);
  GR[12]= _gr(  5, 1,4,10,12,26);
  GR[13]= _gr(  5, 1,4,10,12,26);
  GR[14]= _gr( -4, 1,5,12,18);
  GR[15]= _gr(  5, 1,5,12,18,29);
  GR[16]= _gr(  6, 1,4,5,12,18,26);
  GR[17]= _gr( -5, 1,6,10,12,30);
  GR[18]= _gr(  7, 1,4,5,10,12,25,26);
  GR[19]= _gr(  7, 1,4,5,12,18,26,29);
  GR[20]= _gr(  9, 1,4,6,9,10,12,24,26,30);
  GR[21]= _gr( -7, 1,5,6,10,12,25,30);
  GR[22]= _gr(  7, 1,4,6,10,12,26,30);
  GR[23]= _gr( -6, 1,5,10,12,18,25);
  GR[24]= _gr( 11, 1,4,5,6,9,10,12,24,25,26,30);
  GR[25]= _gr( -7, 1,3,6,8,10,12,30);
  GR[26]= _gr(  9, 1,4,5,10,12,18,25,26,29);
  GR[27]= _gr( -5, 1,5,12,27,30);
  GR[28]= _gr( 12, 1,2,3,4,6,7,8,10,11,12,26,30);
  GR[29]= _gr( 12, 1,3,4,6,8,9,10,12,15,24,26,30);
  GR[30]= _gr(-11, 1,3,5,6,8,10,12,14,17,25,30);
  GR[31]= _gr( 19, 1,2,3,4,5,6,7,8,9,10,11,12,14,15,17,24,25,26,30);
  GR[32]= _gr( -7, 1,5,10,12,25,27,30);

  gr[0]=35; res = galmodp(EVEN,pol,dpol,TYP,gr,GR);
  avma=av; if (!res) return 0;
  return EVEN? 33: 34;
}

/* DEGREE 10 */
static long
galoisprim10(long EVEN, buildroot *BR)
{
  long rep;
  if (EVEN)
  {
    rep=isin_G_H(BR,44,31);
    if (!rep) return 44;
    rep=isin_G_H(BR,31,26);
    if (!rep) return 31;
    rep=isin_G_H(BR,26,7);
    return rep? 7: 26;
  }
  else
  {
    rep=isin_G_H(BR,45,35);
    if (!rep) return 45;
    rep=isin_G_H(BR,35,32);
    if (!rep) goto PRIM_10_7;
    rep=isin_G_H(BR,32,13);
    return rep? 13: 32;

   PRIM_10_7:
    rep=isin_G_H(BR,35,30);
    return rep? 30: 35;
  }
}

static long
galoisimpeven10(buildroot *BR, long nogr)
{
  long rep;
  if (nogr==42)
  {
    rep=isin_G_H(BR,42,28);
    if (!rep) return 42;
    rep=isin_G_H(BR,28,18);
    return rep? 18: 28;
  }
  else
  {
    rep=isin_G_H(BR,37,34);
    if (!rep) goto IMPEVEN_10_5;
    rep=isin_G_H(BR,34,15);
    if (rep) goto IMPEVEN_10_7; else return 34;

  IMPEVEN_10_5:
    rep=isin_G_H(BR,37,24);
    if (!rep) return 37;
    rep=isin_G_H(BR,24,15);
    if (!rep) return 24;
  IMPEVEN_10_7:
    rep=isin_G_H(BR,15,8);
    return rep? 8: 15;
  }
}

static long
galoisimpodd10(buildroot *BR, long nogr)
{
  long rep;
  if (nogr==43)
  {
    rep=isin_G_H(BR,43,41);
    if (!rep) goto IMPODD_10_3;
    rep=isin_G_H(BR,41,40);
    if (rep) goto IMPODD_10_4; else goto IMPODD_10_5;

   IMPODD_10_3:
    rep=isin_G_H(BR,43,33);
    if (rep) goto IMPODD_10_6; else return 43;

   IMPODD_10_4:
    rep=isin_G_H(BR,40,21);
    if (rep) goto IMPODD_10_7; else goto IMPODD_10_8;

   IMPODD_10_5:
    rep=isin_G_H(BR,41,27);
    if (rep) goto IMPODD_10_9; else goto IMPODD_10_10;

   IMPODD_10_6:
    rep=isin_G_H(BR,33,27);
    if (rep) goto IMPODD_10_9; else return 33;

   IMPODD_10_7:
    rep=isin_G_H(BR,21,10);
    if (rep) goto IMPODD_10_12; else goto IMPODD_10_13;

   IMPODD_10_8:
    rep=isin_G_H(BR,40,12);
    if (rep) goto IMPODD_10_14; else goto IMPODD_10_15;

   IMPODD_10_9:
    rep=isin_G_H(BR,27,21);
    if (rep) goto IMPODD_10_7; else goto IMPODD_10_16;

   IMPODD_10_10:
    rep=isin_G_H(BR,41,22);
    if (!rep) return 41;
    rep=isin_G_H(BR,22,12);
    if (rep) goto IMPODD_10_14; else goto IMPODD_10_18;

   IMPODD_10_12:
    rep=isin_G_H(BR,10,4);
    return rep? 4: 10;

   IMPODD_10_13:
    rep=isin_G_H(BR,21,9);
    if (rep) goto IMPODD_10_19; else return 21;
   IMPODD_10_14:
    rep=isin_G_H(BR,12,4);
    return rep? 4: 12;

   IMPODD_10_15:
    rep=isin_G_H(BR,40,11);
    if (rep) goto IMPODD_10_20; else return 40;
   IMPODD_10_16:
    rep=isin_G_H(BR,27,20);
    if (!rep) goto IMPODD_10_21;
    rep=isin_G_H(BR,20,10);
    if (rep) goto IMPODD_10_12; return 20;

   IMPODD_10_18:
    rep=isin_G_H(BR,22,11);
    if (rep) goto IMPODD_10_20; else goto IMPODD_10_23;

   IMPODD_10_19:
    rep=isin_G_H(BR,9,6);
    if (rep) goto IMPODD_10_24; else goto IMPODD_10_25;

   IMPODD_10_20:
    rep=isin_G_H(BR,11,3);
    if (rep) goto IMPODD_10_26; else return 11;

   IMPODD_10_21:
    rep=isin_G_H(BR,27,19);
    if (rep) goto IMPODD_10_27;
    rep=isin_G_H(BR,27,17);
    if (rep) goto IMPODD_10_28; else return 27;

   IMPODD_10_23:
    rep=isin_G_H(BR,22,5);
    if (rep) goto IMPODD_10_29; else return 22;

   IMPODD_10_24:
    rep=isin_G_H(BR,6,2);
    if (rep) return 2; else goto IMPODD_10_30;

   IMPODD_10_25:
    rep=isin_G_H(BR,9,3);
    if (!rep) return 9;
   IMPODD_10_26:
    rep=isin_G_H(BR,3,2);
    if (rep) return 2; else goto IMPODD_10_31;

   IMPODD_10_27:
    rep=isin_G_H(BR,19,9);
    if (rep) goto IMPODD_10_19; else return 19;

   IMPODD_10_28:
    rep=isin_G_H(BR,17,10);
    if (rep) goto IMPODD_10_12; else goto IMPODD_10_32;

   IMPODD_10_29:
    rep=isin_G_H(BR,5,4);
    if (rep) return 4; else goto IMPODD_10_33;

   IMPODD_10_30:
    rep=isin_G_H(BR,6,1);
    return rep? 1: 6;

   IMPODD_10_31:
    rep=isin_G_H(BR,3,1);
    return rep? 1: 3;

   IMPODD_10_32:
    rep=isin_G_H(BR,17,9);
    if (rep) goto IMPODD_10_19; else goto IMPODD_10_60;

   IMPODD_10_33:
    rep=isin_G_H(BR,5,3);
    if (rep) goto IMPODD_10_26; else return 5;

   IMPODD_10_60:
    rep=isin_G_H(BR,17,5);
    if (rep) goto IMPODD_10_29; else return 17;
  }
  else
  {
    rep=isin_G_H(BR,39,38);
    if (!rep) goto IMPODD_10_36;
    rep=isin_G_H(BR,38,25);
    if (rep) goto IMPODD_10_37; else goto IMPODD_10_38;

   IMPODD_10_36:
    rep=isin_G_H(BR,39,36);
    if (rep) goto IMPODD_10_39; else goto IMPODD_10_40;

   IMPODD_10_37:
    rep=isin_G_H(BR,25,4);
    return rep? 4: 25;

   IMPODD_10_38:
    rep=isin_G_H(BR,38,12);
    if (rep) goto IMPODD_10_41; else return 38;

   IMPODD_10_39:
    rep=isin_G_H(BR,36,23);
    if (rep) goto IMPODD_10_42; else goto IMPODD_10_43;

   IMPODD_10_40:
    rep=isin_G_H(BR,39,29);
    if (rep) goto IMPODD_10_44; else goto IMPODD_10_45;

   IMPODD_10_41:
    rep=isin_G_H(BR,12,4);
    return rep? 4: 12;

   IMPODD_10_42:
    rep=isin_G_H(BR,23,16);
    if (rep) goto IMPODD_10_46; else goto IMPODD_10_47;

   IMPODD_10_43:
    rep=isin_G_H(BR,36,11);
    if (rep) goto IMPODD_10_48; else return 36;

   IMPODD_10_44:
    rep=isin_G_H(BR,29,25);
    if (rep) goto IMPODD_10_37; else goto IMPODD_10_49;

   IMPODD_10_45:
    rep=isin_G_H(BR,39,22);
    if (rep) goto IMPODD_10_50; else return 39;

   IMPODD_10_46:
    rep=isin_G_H(BR,16,2);
    return rep? 2: 16;

   IMPODD_10_47:
    rep=isin_G_H(BR,23,14);
    if (rep) goto IMPODD_10_51; else goto IMPODD_10_52;

   IMPODD_10_48:
    rep=isin_G_H(BR,11,3);
    if (rep) goto IMPODD_10_53; else return 11;

   IMPODD_10_49:
    rep=isin_G_H(BR,29,23);
    if (rep) goto IMPODD_10_42; else goto IMPODD_10_54;

   IMPODD_10_50:
    rep=isin_G_H(BR,22,12);
    if (rep) goto IMPODD_10_41; else goto IMPODD_10_55;

   IMPODD_10_51:
    rep=isin_G_H(BR,14,1);
    return rep? 1: 14;

   IMPODD_10_52:
    rep=isin_G_H(BR,23,3);
    if (!rep) return 23;
   IMPODD_10_53:
    rep=isin_G_H(BR,3,2);
    if (rep) return 2; else goto IMPODD_10_57;

   IMPODD_10_54:
    rep=isin_G_H(BR,29,5);
    if (rep) goto IMPODD_10_58; else return 29;

   IMPODD_10_55:
    rep=isin_G_H(BR,22,11);
    if (rep) goto IMPODD_10_48;
    rep=isin_G_H(BR,22,5);
    if (rep) goto IMPODD_10_58; else return 22;

   IMPODD_10_57:
    rep=isin_G_H(BR,3,1);
    return rep? 1: 3;

   IMPODD_10_58:
    rep=isin_G_H(BR,5,4);
    if (rep) return 4;
    rep=isin_G_H(BR,5,3);
    if (rep) goto IMPODD_10_53; else return 5;
  }
}

static long
closure10(long EVEN, buildroot *BR)
{
  long rep;
  if (EVEN)
  {
    rep=isin_G_H(BR,44,42);
    if (rep) return galoisimpeven10(BR,42);
    rep=isin_G_H(BR,44,37);
    if (rep) return galoisimpeven10(BR,37);
  }
  else
  {
    rep=isin_G_H(BR,45,43);
    if (rep) return galoisimpodd10(BR,43);
    rep=isin_G_H(BR,45,39);
    if (rep) return galoisimpodd10(BR,39);
  }
  return galoisprim10(EVEN, BR);
}

static PERM
data10(long N, long n1,long n2,GROUP *t)
{
  switch(n1)
  {
    case 6: if (n2!=2) break;
      *t=initgroup(N,1);
      return _cr(N, 1, 2, 3, 4, 5, 6, 10, 9, 8, 7);
    case 9: if (n2!=3 && n2!=6) break;
      *t=initgroup(N,2);
      _aff(N, (*t)[2], 1, 2, 3, 4, 5, 6, 10, 9, 8, 7);
      return (*t)[1];
    case 10: *t=initgroup(N,2);
      _aff(N, (*t)[2], 1, 2, 3, 4, 5, 6, 10, 9, 8, 7);
      return (*t)[1];
    case 14: case 16:*t=initgroup(N,1);
      return _cr(N, 1, 3, 5, 7, 9, 2, 4, 6, 8, 10);
    case 17: if (n2!=5) break;
      *t=initgroup(N,2);
      _aff(N, (*t)[2], 1, 2, 3, 4, 5, 6, 10, 9, 8, 7);
      return (*t)[1];
    case 19: case 20: *t=initgroup(N,2);
      _aff(N, (*t)[2], 1, 2, 3, 4, 5, 6, 8, 10, 7, 9);
      return (*t)[1];
    case 21: if (n2!=10) break;
      *t=initgroup(N,1);
      return _cr(N, 1, 2, 3, 4, 5, 6, 8, 10, 7, 9);
    case 23: if (n2!=3) break;
      *t=initgroup(N,1);
      return _cr(N, 1, 3, 5, 7, 9, 2, 4, 6, 8, 10);
    case 25: *t=initgroup(N,1);
      return _cr(N, 1, 3, 5, 7, 9, 2, 4, 6, 8, 10);
    case 26: *t=initgroup(N,2);
      _aff(N, (*t)[2], 1, 2, 4, 9, 6, 8, 10, 3, 7, 5);
      return _cr(N, 1, 2, 3, 10, 6, 5, 7, 4, 8, 9);
    case 27: if (n2!=17 && n2!=21) break;
      *t=initgroup(N,2);
      _aff(N, (*t)[2], 1, 2, 3, 4, 5, 6, 8, 10, 7, 9);
      return (*t)[1];
    case 28: *t=initgroup(N,2);
      _aff(N, (*t)[2], 1, 2, 3, 4, 5, 6, 8, 10, 7, 9);
      return (*t)[1];
    case 29: if (n2!=5) break;
      *t=initgroup(N,1);
      return _cr(N, 1, 3, 5, 7, 9, 2, 4, 6, 8, 10);
    case 32: *t=initgroup(N,2);
      _aff(N, (*t)[2], 1, 2, 4, 9, 6, 8, 10, 3, 7, 5);
      return _cr(N, 1, 2, 3, 10, 6, 5, 7, 4, 8, 9);
    case 36: if (n2!=11) break;
      *t=initgroup(N,1);
      return _cr(N, 1, 3, 5, 7, 9, 2, 4, 6, 8, 10);
    case 38: if (n2!=12) break;
      *t=initgroup(N,1);
      return _cr(N, 1, 3, 5, 7, 9, 2, 4, 6, 8, 10);
    case 39: if (n2!=22) break;
      *t=initgroup(N,1);
      return _cr(N, 1, 3, 5, 7, 9, 2, 4, 6, 8, 10);
    case 40: if (n2!=12) break;
      *t=initgroup(N,1);
      return _cr(N, 1, 2, 3, 4, 5, 6, 7, 8, 10, 9);
    case 41: if (n2!=22 && n2!=40) break;
      *t=initgroup(N,2);
      _aff(N, (*t)[2], 1, 2, 3, 4, 5, 6, 7, 8, 10, 9);
      return (*t)[1];
  }
  *t=initgroup(N,1); return (*t)[1];
}

static long
galoismodulo10(long EVEN, GEN pol, GEN dpol)
{
  long res, gr[46];
  pari_sp av = avma;
  long **GR = (long**) cgeti(45);
  GEN TYP = partitions_galois(10);

  GR[ 1]= _gr(  4, 1,6,30,42);
  GR[ 2]= _gr(  3, 1,6,30);
  GR[ 3]= _gr(  5, 1,5,6,30,42);
  GR[ 4]= _gr(  4, 1,5,23,30);
  GR[ 5]= _gr(  7, 1,5,6,22,23,30,42);
  GR[ 6]= _gr(  5, 1,6,24,30,42);
  GR[ 7]= _gr( -4, 1,5,14,30);
  GR[ 8]= _gr( -4, 1,3,5,30);
  GR[ 9]= _gr(  6, 1,5,6,24,30,42);
  GR[10]= _gr(  5, 1,5,23,24,30);
  GR[11]= _gr(  7, 1,5,6,11,30,33,42);
  GR[12]= _gr(  7, 1,5,6,11,23,30,33);
  GR[13]= _gr(  7, 1,4,5,14,23,30,34);
  GR[14]= _gr(  8, 1,2,3,4,5,6,30,42);
  GR[15]= _gr( -6, 1,3,5,18,22,30);
  GR[16]= _gr(  7, 1,3,5,6,17,23,30);
  GR[17]= _gr(  8, 1,5,6,22,23,24,30,42);
  GR[18]= _gr( -6, 1,5,22,24,30,40);
  GR[19]= _gr(  7, 1,5,6,22,24,30,42);
  GR[20]= _gr(  6, 1,5,22,23,24,30);
  GR[21]= _gr(  9, 1,3,5,6,23,24,26,30,42);
  GR[22]= _gr( 11, 1,3,5,6,11,13,22,23,30,33,42);
  GR[23]= _gr( 12, 1,2,3,4,5,6,17,18,22,23,30,42);
  GR[24]= _gr( -7, 1,3,5,18,22,30,40);
  GR[25]= _gr(  8, 1,3,5,18,22,23,30,39);
  GR[26]= _gr( -5, 1,5,14,22,30);
  GR[27]= _gr( 10, 1,3,5,6,22,23,24,26,30,42);
  GR[28]= _gr( -8, 1,3,5,22,24,26,30,40);
  GR[29]= _gr( 14, 1,2,3,4,5,6,17,18,22,23,30,39,40,42);
  GR[30]= _gr(  8, 1,5,6,14,22,30,39,42);
  GR[31]= _gr( -6, 1,5,14,22,30,40);
  GR[32]= _gr(  8, 1,4,5,14,22,23,30,34);
  GR[33]= _gr( 14, 1,3,5,6,15,17,22,23,24,26,29,30,40,42);
  GR[34]= _gr( -9, 1,3,5,11,13,18,22,30,32);
  GR[35]= _gr( 12, 1,4,5,6,14,22,23,30,34,39,40,42);
  GR[36]= _gr( 18, 1,2,3,4,5,6,11,12,13,17,18,22,23,30,31,32,33,42);
  GR[37]= _gr(-12, 1,3,5,11,13,16,18,22,30,32,35,40);
  GR[38]= _gr( 18, 1,3,4,5,6,11,13,15,17,18,21,22,23,30,32,33,35,39);
  GR[39]= _gr( 24, 1,2,3,4,5,6,11,12,13,15,16,17,18,21,22,23,30,31,32,33,35,39,40,42);
  GR[40]= _gr( 14, 1,3,5,6,7,9,11,23,24,26,27,30,33,42);
  GR[41]= _gr( 18, 1,3,5,6,7,9,11,13,16,20,22,23,24,26,27,30,33,42);
  GR[42]= _gr(-17, 1,3,5,7,9,11,13,16,18,20,22,24,26,27,30,35,40);
  GR[43]= _gr( 32, 1,2,3,4,5,6,7,8,9,10,11,12,13,15,16,17,18,19,20,22,23,24,25,26,27,28,29,30,33,35,40,42);
  GR[44]= _gr(-22, 1,3,5,7,9,11,13,14,16,18,20,22,24,26,27,30,32,35,36,38,40,41);

  gr[0]=46; res = galmodp(EVEN,pol,dpol,TYP,gr,GR);
  avma=av; if (!res) return 0;
  return EVEN? 44: 45;
}

/* DEGREE 11 */
static long
closure11(long EVEN, buildroot *BR)
{
  long rep;
  if (EVEN)
  {
    rep=isin_G_H(BR,7,6);
    if (!rep) return 7;
    rep=isin_G_H(BR,6,5);
    if (!rep) return 6;
    rep=isin_G_H(BR,5,3);
    if (!rep) return 5;
    rep=isin_G_H(BR,3,1);
    return rep? 1: 3;
  }
  else
  {
    GEN h = BR->p, r = compositum(h, h);
    r = gel(r,lg(r)-1);
    if (degpol(r) == 22) return 2; /* D11 */
    h = leafcopy(h); setvarn(h, fetch_var());
    setvarn(r, 0); r = nffactor(h, r);
    /* S11 (P10*P10*P90) or F_110[11] (11 factors of degree 10) */
    (void)delete_var();
    return (lgcols(r)-1 == 11)? 4: 8;
  }
}

static PERM
data11(long N, long n1, GROUP *t)
{
  switch(n1)
  {
    case 5: *t=initgroup(N,1);
      return _cr(N, 1, 2, 3, 7, 8, 6, 11, 5, 9, 4, 10);
    case 6: *t=initgroup(N,1);
      return _cr(N, 1, 2, 3, 4, 6, 10, 11, 9, 7, 5, 8);
    case 7: *t=initgroup(N,2);
      _aff(N, (*t)[2], 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 10);
      return (*t)[1];
  }
  *t=initgroup(N,1); return (*t)[1];
}

static long
galoismodulo11(long EVEN, GEN pol, GEN dpol)
{
  long res, gr[6] = {0, 1, 1, 1, 1, 1};
  pari_sp av = avma;
  GEN TYP = cgetg(EVEN? 9: 6, t_VEC);

  gel(TYP,1) = _typ(1, 11);
  if (EVEN)
  {
    gel(TYP,2) = _typ(3, 8,2,1);
    gel(TYP,3) = _typ(3, 6,3,2);
    gel(TYP,4) = _typ(3, 5,5,1);
    gel(TYP,5) = _typ(5, 4,4,1,1,1);
    gel(TYP,6) = _typ(5, 3,3,3,1,1);
    gel(TYP,7) = _typ(7, 2,2,2,2,1,1,1);
    gel(TYP,8) = _typ(11, 1,1,1,1,1,1,1,1,1,1,1);
  }
  else
  {
    gel(TYP,2) = _typ(2, 10,1);
    gel(TYP,3) = _typ(3, 5,5,1);
    gel(TYP,4) = _typ(6, 2,2,2,2,2,1);
    gel(TYP,5) = _typ(11, 1,1,1,1,1,1,1,1,1,1,1);
  }
  res = galmodp(EVEN,pol,dpol,TYP,gr,NULL);
  avma=av; if (!res) return 0;
  return EVEN? 7: 8;
}

static void
init_isin(long N, long n1, long n2, GROUP *tau, PERM *s0, resolv *R)
{
  int fl = 1;
  if (DEBUGLEVEL) {
    err_printf("\n*** Entering isin_%ld_G_H_(%ld,%ld)\n",N,n1,n2); err_flush();
  }
  switch(N)
  {
    case 8:
      if ((n1==47 && n2==46) || (n1==44 && n2==40)) fl=0;
      *s0=data8(N, n1,n2,tau); break;
    case 9:
      if ((n1==31 && n2==29) || (n1==34 && n2==31) || (n1==33 && n2==30)) fl=0;
      *s0=data9(N,n1,n2,tau); break;
    case 10:
      if ((n1==45 && (n2==43||n2==39))
       || (n1==44 && (n2==42||n2==37))
       || (n1==43 && (n2==41||n2==33))
       || (n1==42 && n2==28)
       || (n1==41 && (n2==40||n2==27||n2==22))
       || (n1==40 && (n2==21||n2==11))
       || (n1==39 && (n2==38||n2==36||n2==29||n2==22))
       || (n1==38 && (n2==25||n2==12))
       || (n1==37 && (n2==34||n2==24))
       || (n1==36 && (n2==23||n2==11))
       || (n1==34 && n2==15)
       || (n1==33 && n2==27)
       || (n1==29 && (n2==25||n2==23||n2==5))
       || (n1==28 && n2==18)
       || (n1==27 && (n2==20||n2==19||n2==17))
       || (n1==25 && n2==4)
       || (n1==24 && n2==15)
       || (n1==23 && (n2==16||n2==3))
       || (n1==22 && (n2==12||n2==11||n2==5))
       || (n1==21 && (n2==10||n2==9))
       || (n1==17 && n2==5)
       || (n1==16 && n2==2)
       || (n1==14 && n2==1)
       || (n1==12 && n2==4)
       || (n1==11 && n2==3)
       || (n1==10 && n2==4)
       || (n1== 9 && n2==3)
       || (n1== 6 && n2==1)
       || (n1== 5 && n2==3)) fl = 0;
      *s0=data10(N,n1,n2,tau); break;
    default: /* case 11: */
      *s0=data11(N,n1,tau); break;
  }
  if (fl) lireresolv(n1,n2,N,R); else { R->a = NULL; R->nm = n1; R->nv = n2; }
}

static long
isin_G_H(buildroot *BR, long n1, long n2)
{
  pari_sp av = avma;
  const long N = BR->N;
  PERM s0, ww;
  GROUP tau, ss = lirecoset(n1,n2,N);
  resolv R;

  init_isin(N,n1,n2, &tau, &s0, &R);
  ww = check_isin(BR, &R, tau, ss);
  if (ww)
  {
    GEN z = cgetg(N+1, t_VEC);
    long i, j, l = lg(BR->r);
    s0 = permmul(ww, s0);
    if (DEBUGLEVEL)
    {
      err_printf("\n    Output of isin_%ld_G_H(%ld,%ld): %ld",N,n1,n2,n2);
      err_printf("\n    Reordering of the roots: "); printperm(s0);
      err_flush();
    }
    for (i = 1; i < l; i++)
    {
      GEN p1 = gel(BR->r,i);
      for (j=1; j<=N; j++) gel(z,j) = gel(p1,s0[j]);
      for (j=1; j<=N; j++) gel(p1,j) = gel(z,j);
    }
    avma = av; return n2;
  }
  if (DEBUGLEVEL)
  {
    err_printf("    Output of isin_%ld_G_H(%ld,%ld): not included.\n",N,n1,n2);
    err_flush();
  }
  avma = av; return 0;
}

static GEN
polgaloisnamesbig(long n, long k)
{
  pari_sp av = avma;
  char *s = stack_malloc(strlen(pari_datadir) + 13 + 20 + 3);
  pariFILE *f;
  GEN V;

  (void)sprintf(s, "%s/galdata/NAM%ld", pari_datadir, n);
  f = pari_fopengz(s);
  V = f? gp_read_stream(f->file): NULL;
  if (!V || typ(V)!=t_VEC || k>=lg(V)) pari_err_FILE("galois file %s",s);
  pari_fclose(f);
  return gerepilecopy(av, gel(V,k));
}

/* pol a monic ZX */
static GEN
galoisbig(GEN pol, long prec)
{
  pari_sp av = avma;
  const long *tab;
  const long tab8[]={0,
    8,8,8,8,8,16,16,16,16,16, 16,24,24,24,32,32,32,32,32,32,
    32,32,48,48,56,64,64,64,64,64, 64,96,96,96,128,168,168,192,192,192,
    192,288,336,384,576,576,1152,1344,20160,40320};
  const long tab9[]={0,
    9,9,18,18,18,27,27,36,36,54, 54,54,54,72,72,72,81,108,144,162,
    162,162,216,324,324,432,504,648,648,648, 1296,1512,181440,362880};
  const long tab10[]={0,
    10,10,20,20,40,50,60,80,100,100, 120,120,120,160,160,160,200,200,200,200,
    200,240,320,320,320,360,400,400,640,720, 720,720,800,960,1440,
    1920,1920,1920,3840,7200,14400,14400,28800,1814400,3628800};
  const long tab11[]={0, 11,22,55,110,660,7920,19958400,39916800};
  GEN res, dpol = ZX_disc(pol);
  long t = 0, N = degpol(pol), EVEN = Z_issquare(dpol);

  if (DEBUGLEVEL)
  {
    err_printf("Galoisbig: polynomial #1 = %Ps\n", pol);
    err_printf("%s group\n", EVEN? "EVEN": "ODD"); err_flush();
  }
  switch(N)
  {
    case 8: t = galoismodulo8(EVEN,pol,dpol);  tab=tab8; break;
    case 9: t = galoismodulo9(EVEN,pol,dpol);  tab=tab9; break;
    case 10:t = galoismodulo10(EVEN,pol,dpol); tab=tab10; break;
    case 11:t = galoismodulo11(EVEN,pol,dpol); tab=tab11; break;
    default: pari_err_IMPL("galois in degree > 11");
      return NULL; /* LCOV_EXCL_LINE */
  }
  if (!t)
  {
    buildroot BR;
    long i;
    GEN r, z = cgetg(N + 1, t_VEC);
    for (i = 1; i <= N; i++)
    {
      GEN v = cgetg(i+2,t_VECSMALL);
      gel(z,i) = v; v[1] = 0;
    }
    BR.coef = z;
    BR.p = pol;
    BR.pr = prec + nbits2extraprec((long)fujiwara_bound(pol));
    BR.prmax = BR.pr + BIGDEFAULTPREC-2;
    BR.N = N;
    BR.r = vectrunc_init(N+1);
    r = gclone ( QX_complex_roots(BR.p, BR.prmax) );
    vectrunc_append(BR.r, r); preci(r, BR.pr);
    switch(N)
    {
      case  8: t = closure8(EVEN, &BR); break;
      case  9: t = closure9(EVEN, &BR); break;
      case 10: t = closure10(EVEN, &BR); break;
      case 11: t = closure11(EVEN, &BR); break;
    }
    for (i = 1; i < lg(BR.r); i++) gunclone(gel(BR.r,i));
  }
  avma = av;
  res    = cgetg(5,t_VEC);
  gel(res,1) = stoi(tab[t]);
  gel(res,2) = stoi(EVEN? 1: -1);
  gel(res,3) = stoi(t);
  gel(res,4) = polgaloisnamesbig(N,t);
  return res;
}

/**************************************************************/
/*               Galois group for degree <= 7                 */
/**************************************************************/

/* exchange elements i and j in vector x */
static GEN
transroot(GEN x, int i, int j)
{ x = leafcopy(x); swap(gel(x,i), gel(x,j)); return x; }

/* x1*x2^2 + x2*x3^2 + x3*x4^2 + x4*x1^2 */
static GEN
F4(GEN x)
{
  return gadd(
    gmul(gel(x,1), gadd(gsqr(gel(x,2)), gmul(gel(x,4),gel(x,1)))),
    gmul(gel(x,3), gadd(gsqr(gel(x,4)), gmul(gel(x,2),gel(x,3)))));
}

static GEN
roots_to_ZX(GEN z, long *e)
{
  GEN a = roots_to_pol(z,0);
  GEN b = grndtoi(real_i(a),e);
  long e1 = gexpo(imag_i(a));
  if (e1 > *e) *e = e1;
  return b;
}

static GEN
polgaloisnames(long a, long b)
{
  const char * const t[]={"S1", "S2", "A3", "S3",
       "C(4) = 4", "E(4) = 2[x]2", "D(4)", "A4", "S4",
       "C(5) = 5", "D(5) = 5:2", "F(5) = 5:4", "A5", "S5",
       "C(6) = 6 = 3[x]2", "D_6(6) = [3]2", "D(6) = S(3)[x]2",
             "A_4(6) = [2^2]3", "F_18(6) = [3^2]2 = 3 wr 2",
             "2A_4(6) = [2^3]3 = 2 wr 3", "S_4(6d) = [2^2]S(3)",
             "S_4(6c) = 1/2[2^3]S(3)", "F_18(6):2 = [1/2.S(3)^2]2",
             "F_36(6) = 1/2[S(3)^2]2", "2S_4(6) = [2^3]S(3) = 2 wr S(3)",
             "L(6) = PSL(2,5) = A_5(6)", "F_36(6):2 = [S(3)^2]2 = S(3) wr 2",
             "L(6):2 = PGL(2,5) = S_5(6)", "A6", "S6",
       "C(7) = 7", "D(7) = 7:2", "F_21(7) = 7:3", "F_42(7) = 7:6",
             "L(7) = L(3,2)", "A7", "S7"};

   const long idx[]={0,1,2,4,9,14,30};
   return strtoGENstr(t[idx[a-1]+b-1]);
}

static GEN
galois_res(long d, long n, long s, long k)
{
  GEN z = cgetg(5,t_VEC);
  long kk;
  if (new_galois_format)
    kk = k;
  else
    kk = (d == 6 && (k==6 || k==2))? 2: 1;
  gel(z,1) = stoi(n);
  gel(z,2) = stoi(s);
  gel(z,3) = stoi(kk);
  gel(z,4) = polgaloisnames(d,k);
  return z;
}

GEN
polgalois(GEN x, long prec)
{
  pari_sp av = avma, av1;
  long i,j,k,n,f,l,l2,e,e1,pr,ind;
  GEN x1,p1,p2,p3,p4,p5,w,z,ee;
  const int ind5[20]={2,5,3,4, 1,3,4,5, 1,5,2,4, 1,2,3,5, 1,4,2,3};
  const int ind6[60]={3,5,4,6, 2,6,4,5, 2,3,5,6, 2,4,3,6, 2,5,3,4,
                      1,4,5,6, 1,5,3,6, 1,6,3,4, 1,3,4,5, 1,6,2,5,
                      1,2,4,6, 1,5,2,4, 1,3,2,6, 1,2,3,5, 1,4,2,3};
  if (typ(x)!=t_POL) pari_err_TYPE("galois",x);
  n=degpol(x);
  if (n>11) pari_err_IMPL("galois of degree higher than 11");
  x = Q_primpart(x);
  RgX_check_ZX(x, "galois");
  if (!ZX_is_irred(x)) pari_err_IRREDPOL("galois",x);

  if (n<4)
  {
    if (n == 1) { avma = av; return galois_res(n,1, 1,1); }
    if (n == 2) { avma = av; return galois_res(n,2,-1,1); }
    /* n = 3 */
    f = Z_issquare(ZX_disc(x));
    avma = av;
    return f? galois_res(n,3,1,1):
              galois_res(n,6,-1,2);
  }
  x1 = x = ZX_Q_normalize(x,NULL); av1=avma;
  if (n > 7) return galoisbig(x, prec);
  for(;;)
  {
    double fb = fujiwara_bound(x);
    switch(n)
    {
      case 4: z = cgetg(7,t_VEC);
        prec = nbits2prec((long)(fb*18.) + 64);
        for(;;)
        {
          p1=QX_complex_roots(x,prec);
          gel(z,1) = F4(p1);
          gel(z,2) = F4(transroot(p1,1,2));
          gel(z,3) = F4(transroot(p1,1,3));
          gel(z,4) = F4(transroot(p1,1,4));
          gel(z,5) = F4(transroot(p1,2,3));
          gel(z,6) = F4(transroot(p1,3,4));
          p5 = roots_to_ZX(z, &e); if (e <= -10) break;
          prec = precdbl(prec);
        }
        if (!ZX_is_squarefree(p5)) goto tchi;
        p2 = gel(ZX_factor(p5),1);
        switch(lg(p2)-1)
        {
          case 1: f = Z_issquare(ZX_disc(x)); avma = av;
            return f? galois_res(n,12,1,4): galois_res(n,24,-1,5);

          case 2: avma = av; return galois_res(n,8,-1,3);

          case 3: avma = av;
            return (degpol(gel(p2,1))==2)? galois_res(n,4,1,2)
                                         : galois_res(n,4,-1,1);

          default: pari_err_BUG("galois (bug1)");
        }

      case 5: z = cgetg(7,t_VEC);
        ee= cgetg(7,t_VECSMALL);
        w = cgetg(7,t_VECSMALL);
        prec = nbits2prec((long)(fb*21.) + 64);
        for(;;)
        {
          for(;;)
          {
            p1=QX_complex_roots(x,prec);
            for (l=1; l<=6; l++)
            {
              p2=(l==1)?p1: ((l<6)?transroot(p1,1,l): transroot(p1,2,5));
              p3=gen_0;
              for (k=0,i=1; i<=5; i++,k+=4)
              {
                p5 = gadd(gmul(gel(p2,ind5[k]),gel(p2,ind5[k+1])),
                          gmul(gel(p2,ind5[k+2]),gel(p2,ind5[k+3])));
                p3 = gadd(p3, gmul(gsqr(gel(p2,i)),p5));
              }
              gel(w,l) = grndtoi(real_i(p3),&e);
              e1 = gexpo(imag_i(p3)); if (e1>e) e=e1;
              ee[l]=e; gel(z,l) = p3;
            }
            p5 = roots_to_ZX(z, &e); if (e <= -10) break;
            prec = precdbl(prec);
          }
          if (!ZX_is_squarefree(p5)) goto tchi;
          p3=gel(ZX_factor(p5),1);
          f=Z_issquare(ZX_disc(x));
          if (lg(p3)-1==1)
          {
            avma = av;
            return f? galois_res(n,60,1,4): galois_res(n,120,-1,5);
          }
          if (!f) { avma = av; return galois_res(n,20,-1,3); }

          pr = - (prec2nbits(prec) >> 1);
          for (l=1; l<=6; l++)
            if (ee[l] <= pr && gequal0(poleval(p5,gel(w,l)))) break;
          if (l>6) pari_err_BUG("galois (bug4)");
          p2=(l==6)? transroot(p1,2,5):transroot(p1,1,l);
          p3=gen_0;
          for (i=1; i<=5; i++)
          {
            j = (i == 5)? 1: i+1;
            p3 = gadd(p3,gmul(gmul(gel(p2,i),gel(p2,j)),
                              gsub(gel(p2,j),gel(p2,i))));
          }
          p5=gsqr(p3); p4=grndtoi(real_i(p5),&e);
          e1 = gexpo(imag_i(p5)); if (e1>e) e=e1;
          if (e <= -10)
          {
            if (gequal0(p4)) goto tchi;
            f = Z_issquare(p4); avma = av;
            return f? galois_res(n,5,1,1): galois_res(n,10,1,2);
          }
          prec = precdbl(prec);
        }

      case 6: z = cgetg(7, t_VEC);
        prec = nbits2prec((long) (fb * 42) + 64);
        for(;;)
        {
          for(;;)
          {
            p1=QX_complex_roots(x,prec);
            for (l=1; l<=6; l++)
            {
              p2=(l==1)?p1:transroot(p1,1,l);
              p3=gen_0; k=0;
              for (i=1; i<=5; i++) for (j=i+1; j<=6; j++)
              {
                p5=gadd(gmul(gel(p2,ind6[k]),gel(p2,ind6[k+1])),
                        gmul(gel(p2,ind6[k+2]),gel(p2,ind6[k+3])));
                p3=gadd(p3,gmul(gsqr(gmul(gel(p2,i),gel(p2,j))),p5));
                k += 4;
              }
              gel(z,l) = p3;
            }
            p5 = roots_to_ZX(z, &e); if (e <= -10) break;
            prec = precdbl(prec);
          }
          if (!ZX_is_squarefree(p5)) goto tchi;
          p2=gel(ZX_factor(p5),1);
          switch(lg(p2)-1)
          {
            case 1:
              z = cgetg(11,t_VEC); ind=0;
              p3=gadd(gmul(gmul(gel(p1,1),gel(p1,2)),gel(p1,3)),
                      gmul(gmul(gel(p1,4),gel(p1,5)),gel(p1,6)));
              gel(z,++ind) = p3;
              for (i=1; i<=3; i++)
                for (j=4; j<=6; j++)
                {
                  p2=transroot(p1,i,j);
                  p3=gadd(gmul(gmul(gel(p2,1),gel(p2,2)),gel(p2,3)),
                          gmul(gmul(gel(p2,4),gel(p2,5)),gel(p2,6)));
                  gel(z,++ind) = p3;
                }
              p5 = roots_to_ZX(z, &e);
              if (e <= -10)
              {
                if (!ZX_is_squarefree(p5)) goto tchi;
                p2 = gel(ZX_factor(p5),1);
                f = Z_issquare(ZX_disc(x));
                avma = av;
                if (lg(p2)-1==1)
                  return f? galois_res(n,360,1,15): galois_res(n,720,-1,16);
                else
                  return f? galois_res(n,36,1,10): galois_res(n,72,-1,13);
              }
              prec = precdbl(prec); break;

            case 2: l2=degpol(gel(p2,1)); if (l2>3) l2=6-l2;
              switch(l2)
              {
                case 1: f = Z_issquare(ZX_disc(x));
                  avma = av;
                  return f? galois_res(n,60,1,12): galois_res(n,120,-1,14);
                case 2: f = Z_issquare(ZX_disc(x));
                  if (f) { avma = av; return galois_res(n,24,1,7); }
                  p3 = (degpol(gel(p2,1))==2)? gel(p2,2): gel(p2,1);
                  f = Z_issquare(ZX_disc(p3));
                  avma = av;
                  return f? galois_res(n,24,-1,6): galois_res(n,48,-1,11);
                case 3: f = Z_issquare(ZX_disc(gel(p2,1)))
                         || Z_issquare(ZX_disc(gel(p2,2)));
                  avma = av;
                  return f? galois_res(n,18,-1,5): galois_res(n,36,-1,9);
              }
            case 3:
              for (l2=1; l2<=3; l2++)
                if (degpol(gel(p2,l2)) >= 3) p3 = gel(p2,l2);
              if (degpol(p3) == 3)
              {
                f = Z_issquare(ZX_disc(p3)); avma = av;
                return f? galois_res(n,6,-1,1): galois_res(n,12,-1,3);
              }
              else
              {
                f = Z_issquare(ZX_disc(x)); avma = av;
                return f? galois_res(n,12,1,4): galois_res(n,24,-1,8);
              }
            case 4: avma = av; return galois_res(n,6,-1,2);
            default: pari_err_BUG("galois (bug3)");
          }
        }

      case 7: z = cgetg(36,t_VEC);
        prec = nbits2prec((long)(fb*7.) + 64);
        for(;;)
        {
          ind = 0; p1=QX_complex_roots(x,prec);
          for (i=1; i<=5; i++)
            for (j=i+1; j<=6; j++)
            {
              GEN t = gadd(gel(p1,i),gel(p1,j));
              for (k=j+1; k<=7; k++) gel(z,++ind) = gadd(t, gel(p1,k));
            }
          p5 = roots_to_ZX(z, &e); if (e <= -10) break;
          prec = precdbl(prec);
        }
        if (!ZX_is_squarefree(p5)) goto tchi;
        p2=gel(ZX_factor(p5),1);
        switch(lg(p2)-1)
        {
          case 1: f = Z_issquare(ZX_disc(x)); avma = av;
            return f? galois_res(n,2520,1,6): galois_res(n,5040,-1,7);
          case 2: f = degpol(gel(p2,1)); avma = av;
            return (f==7 || f==28)? galois_res(n,168,1,5): galois_res(n,42,-1,4);
          case 3: avma = av; return galois_res(n,21,1,3);
          case 4: avma = av; return galois_res(n,14,-1,2);
          case 5: avma = av; return galois_res(n,7,1,1);
          default: pari_err_BUG("galois (bug2)");
        }
    }
    tchi: avma = av1; x = tschirnhaus(x1);
  }
}
