/* Copyright (C) 2005  The PARI group.

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
/**  INTERFACE TO JOHN CREMONA ELLIPTIC CURVES DATABASE            **/
/**                                                                **/
/********************************************************************/
#include "pari.h"
#include "paripriv.h"

static long
strtoclass(const char *s)
{
  long c=0;
  while (*s && *s<='9') s++;
  if (!*s) return -1;
  while ('a'<=*s && *s<='z') c = 26*c + *(s++)-'a';
  return c;
}

/*Take a curve name like "100a2" and set
 * f to the conductor, (100)
 * c to the isogeny class (in base 26), ("a" or 0)
 * i to the curve index (2).
 * return 0 if parse error. */
static int
ellparsename(const char *s, long *f, long *c, long *i)
{
  long j;
  *f=-1; *c=-1; *i=-1;
  if (*s<'0' || *s>'9') return 0;
  *f=0;
  for (j=0;j<10 && '0'<=*s && *s<='9';j++)
    *f=10**f+*(s++)-'0';
  if (j==10) {*f=-1; return 0;}
  if (*s<'a' || *s>'z') return !*s;
  *c=0;
  for (j=0; j<7 && 'a'<=*s && *s<='z';j++)
    *c=26**c+*(s++)-'a';
  if (j==7) {*c=-1; return 0;}
  if (*s<'0' || *s>'9') return !*s;
  *i=0;
  for (j=0; j<10 && '0'<=*s && *s<='9';j++)
    *i=10**i+*(s++)-'0';
  if (j==10) {*i=-1; return 0;}
  return !*s;
}

/* Take an integer and convert it to base 26 */
static GEN
ellrecode(long x)
{
  GEN str;
  char *s;
  long d = 0, n = x;
  do { d++; n /= 26; } while (n);
  str = cgetg(nchar2nlong(d+1)+1, t_STR);
  s = GSTR(str); s[d] = 0;
  n = x;
  do { s[--d] = n%26 + 'a'; n /= 26; } while (n);
  return str;
}

GEN
ellconvertname(GEN n)
{
  switch(typ(n))
  {
  case t_STR:
    {
      long f,i,c;
      if (!ellparsename(GSTR(n),&f,&c,&i)) pari_err_TYPE("ellconvertname", n);
      if (f<0 || c<0 || i<0)
        pari_err_TYPE("ellconvertname [incomplete name]", n);
      return mkvec3s(f,c,i);
    }
  case t_VEC:
    if (lg(n)==4)
    {
      pari_sp av = avma;
      GEN f=gel(n,1), c=gel(n,2), s=gel(n,3);
      if (typ(f)!=t_INT || typ(c)!=t_INT || typ(s)!=t_INT)
        pari_err_TYPE("ellconvertname",n);
      return gerepilecopy(av, shallowconcat1(mkvec3(f, ellrecode(itos(c)), s)));
    }
    /*fall through*/
  }
  pari_err_TYPE("ellconvertname",n);
  return NULL; /*LCOV_EXCL_LINE*/
}

static GEN
ellcondfile(long f)
{
  pari_sp av = avma;
  long n = f / 1000;
  char *s = stack_malloc(strlen(pari_datadir) + 12 + 20 + 1);
  pariFILE *F;
  GEN V;
  sprintf(s, "%s/elldata/ell%ld", pari_datadir, n);
  F = pari_fopengz(s);
  if (!F) pari_err_FILE("elldata file",s);
  avma = av;
  V = gp_read_stream(F->file);
  if (!V || typ(V)!=t_VEC ) pari_err_FILE("elldata file [read]",s);
  pari_fclose(F); return V;
}

/* return the vector of all curves of conductor f */
static int cmpi1(GEN x, GEN v) { return cmpii(x, gel(v,1)); }
static GEN
ellcondlist(long f)
{
  pari_sp av = avma;
  GEN V = ellcondfile(f);
  long i = tablesearch(V, utoipos(f), &cmpi1);
  if (i)
  {
    GEN v = gel(V,i);
    return vecslice(v,2, lg(v)-1);
  }
  avma = av; return cgetg(1,t_VEC);
}

static GEN
ellsearchbyname(GEN V, char *name)
{
  GEN x;
  long j;
  for (j=1; j<lg(V); j++)
  {
    GEN v = gel(V,j);
    if (!strcmp(GSTR(gel(v,1)), name)) return v;
  }
  x = strtoGENstr(name);
  pari_err_DOMAIN("ellsearchbyname", "name", "=", x,x);
  return NULL;
}

static GEN
ellsearchbyclass(GEN V, long c)
{
  long i,j,n;
  GEN res;
  for (n=0,j=1; j<lg(V); j++)
    if (strtoclass(GSTR(gmael(V,j,1)))==c) n++;
  res = cgetg(n+1,t_VEC);
  for (i=1,j=1; j<lg(V); j++)
    if (strtoclass(GSTR(gmael(V,j,1)))==c) res[i++] = V[j];
  return res;
}

GEN
ellsearch(GEN A)
{
  pari_sp av = avma;
  long f, c, i;
  GEN V;
  if      (typ(A)==t_INT) { f = itos(A); c = i = -1; }
  else if  (typ(A)==t_VEC)
  {
    long l = lg(A)-1;
    if (l<1 || l>3)
      pari_err_TYPE("ellsearch",A);
    f = gtos(gel(A,1));
    c = l>=2 ? gtos(gel(A,2)): -1;
    i = l>=3 ? gtos(gel(A,3)): -1;
    if (l>=3) A = ellconvertname(A);
  }
  else if (typ(A)==t_STR) {
    if (!ellparsename(GSTR(A),&f,&c,&i))
      pari_err_TYPE("ellsearch",A);
  } else {
    pari_err_TYPE("ellsearch",A);
    return NULL;
  }
  if (f <= 0) pari_err_DOMAIN("ellsearch", "conductor", "<=", gen_0,stoi(f));
  V = ellcondlist(f);
  if (c >= 0)
    V = (i < 0)? ellsearchbyclass(V,c): ellsearchbyname(V, GSTR(A));
  return gerepilecopy(av, V);
}

GEN
ellsearchcurve(GEN name)
{
  pari_sp ltop=avma;
  long f, c, i;
  if (!ellparsename(GSTR(name),&f,&c,&i)) pari_err_TYPE("ellsearch",name);
  if (f<0 || c<0 || i<0) pari_err_TYPE("ellsearch [incomplete name]", name);
  return gerepilecopy(ltop, ellsearchbyname(ellcondlist(f), GSTR(name)));
}

GEN
ellidentify(GEN E)
{
  pari_sp ltop=avma;
  long j;
  GEN V, M, G, N;
  checkell_Q(E);
  G = ellglobalred(E); N = gel(G,1);
  V = ellcondlist(itos(N));
  M = ellchangecurve(vecslice(E,1,5),gel(G,2));
  for (j=1; j<lg(V); j++)
    if (ZV_equal(gmael(V,j,2), M))
      return gerepilecopy(ltop, mkvec2(gel(V,j),gel(G,2)));
  pari_err_BUG("ellidentify [missing curve]");
  return NULL;
}

GEN
elldatagenerators(GEN E)
{
  pari_sp ltop=avma;
  GEN V=ellidentify(E);
  GEN gens=gmael(V,1,3);
  GEN W=ellchangepointinv(gens,gel(V,2));
  return gerepileupto(ltop,W);
}

void
forell(void *E, long call(void*, GEN), long a, long b, long flag)
{
  long ca=a/1000, cb=b/1000;
  long i, j, k;

  if (ca < 0) ca = 0;
  for(i=ca; i<=cb; i++)
  {
    pari_sp ltop=avma;
    GEN V = ellcondfile(i*1000);
    for (j=1; j<lg(V); j++)
    {
      GEN ells = gel(V,j);
      long cond= itos(gel(ells,1));

      if (i==ca && cond<a) continue;
      if (i==cb && cond>b) break;
      for(k=2; k<lg(ells); k++)
      {
        GEN e = gel(ells,k);
        if (flag) {
          GEN n = gel(e,1); /* Cremona label */
          long f, c, x;
          if (!ellparsename(GSTR(n),&f,&c,&x))
            pari_err_TYPE("ellconvertname", n);
          if (x != 1) continue;
        }
        if (call(E, e)) return;
      }
    }
    avma = ltop;
  }
}

void
forell0(long a, long b, GEN code, long flag)
{
  push_lex(gen_0, code);
  forell((void*)code, &gp_evalvoid, a, b, flag);
  pop_lex(1);
}
