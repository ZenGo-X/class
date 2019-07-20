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
#include "anal.h"
#include "parse.h"

/***************************************************************************
 **                                                                       **
 **                           Mnemonic codes parser                       **
 **                                                                       **
 ***************************************************************************/

/* TEMPLATE is assumed to be ";"-separated list of items.  Each item
 * may have one of the following forms: id=value id==value id|value id&~value.
 * Each id consists of alphanum characters, dashes and underscores.
 * IDs are case-sensitive.

 * ARG consists of several IDs separated by punctuation (and optional
 * whitespace).  Each modifies the return value in a "natural" way: an
 * ID from id=value should be the first in the sequence and sets RETVAL to
 * VALUE (and cannot be negated), ID from id|value bit-ORs RETVAL with
 * VALUE (and bit-ANDs RETVAL with ~VALUE if negated), ID from
 * id&~value behaves as if it were noid|value, ID from
 * id==value behaves the same as id=value, but should come alone.

 * For items of the form id|value and id&~value negated forms are
 * allowed: either when arg looks like no[-_]id, or when id looks like
 * this, and arg is not-negated. */

static int
IS_ID(char c) { return isalnum((int)c) || c == '_'; }
long
eval_mnemonic(GEN str, const char *tmplate)
{
  const char *arg, *etmplate;
  ulong retval = 0;

  if (typ(str)==t_INT) return itos(str);
  if (typ(str)!=t_STR) pari_err_TYPE("eval_mnemonic",str);

  arg = GSTR(str);
  etmplate = strchr(tmplate, '\n');
  if (!etmplate) etmplate = tmplate + strlen(tmplate);

  while (1)
  {
    long numarg;
    const char *e, *id, *negated = NULL;
    int negate = 0; /* Arg has 'no' prefix removed */
    ulong l;
    char *buf;
    static char b[80];

    while (isspace((int)*arg)) arg++;
    if (!*arg) break;
    e = arg; while (IS_ID(*e)) e++;
    /* Now the ID is whatever is between arg and e. */
    l = e - arg;
    if (l >= sizeof(b)) pari_err(e_MISC,"id too long in a mnemonic");
    if (!l) pari_err(e_MISC,"mnemonic does not start with an id");
    strncpy(b, arg, l); b[l] = 0;
    arg = e; e = buf = b;
    while ('0' <= *e && *e <= '9') e++;
    if (*e == 0) pari_err(e_MISC,"numeric id in a mnemonic");
FIND:
    id = tmplate;
    while ((id = strstr(id, buf)) && id < etmplate)
    {
      const char *s = id;
      id += l; if (s[l] != '|') continue; /* False positive */
      if (s == tmplate || !IS_ID(s[-1])) break; /* Found as is */
      /* If we found "no_ID", negate */
      if (!negate && s >= tmplate+3 && (s == tmplate+3 || !IS_ID(s[-4]))
          && s[-3] == 'n' && s[-2] == 'o' && s[-1] == '_')
         { negated = id; break; }
    }
    if (!id && !negated && !negate && l > 3
            && buf[0] == 'n' && buf[1] == 'o' && buf[2] == '_')
    { /* Try to find the flag without the prefix "no_". */
      buf += 3; l -= 3; negate = 1;
      if (buf[0]) goto FIND;
    }
    /* Negated and AS_IS forms, prefer AS_IS otherwise use negated form */
    if (!id)
    {
      if (!negated) pari_err(e_MISC,"Unrecognized id '%s' in mnemonic", b);
      id = negated; negate = 1;
    }
    if (*id++ != '|') pari_err(e_MISC,"Missing | in mnemonic template");
    e = id;
    while (*e >= '0' && *e <= '9') e++;
    while (isspace((int)*e)) e++;
    if (*e && *e != ';' && *e != ',')
      pari_err(e_MISC, "Non-numeric argument in mnemonic template");
    numarg = atol(id);
    if (negate) retval &= ~numarg; else retval |= numarg;
    while (isspace((int)*arg)) arg++;
    if (*arg && !ispunct((int)*arg++)) /* skip punctuation */
      pari_err(e_MISC,"Junk after id in mnemonic");
  }
  return retval;
}

/********************************************************************/
/**                                                                **/
/**                   HASH TABLE MANIPULATIONS                     **/
/**                                                                **/
/********************************************************************/
/* return hashing value for identifier s */
static ulong
hashvalue(const char *s)
{
  ulong n = 0, c;
  while ( (c = (ulong)*s++) ) n = (n<<1) ^ c;
  return n;
}

static ulong
hashvalue_raw(const char *s, long len)
{
  long n = 0, i;
  for(i=0; i<len; i++) { n = (n<<1) ^ *s; s++; }
  return n;
}

static void
insertep(entree *ep, entree **table, ulong hash)
{
  ep->hash = hash;
  hash %= functions_tblsz;
  ep->next = table[hash];
  table[hash] = ep;
}

static entree *
initep(const char *name, long len)
{
  const long add = 4*sizeof(long);
  entree *ep = (entree *) pari_calloc(sizeof(entree) + add + len+1);
  entree *ep1 = initial_value(ep);
  char *u = (char *) ep1 + add;
  ep->name    = u; memcpy(u, name,len); u[len]=0;
  ep->valence = EpNEW;
  ep->value   = NULL;
  ep->menu    = 0;
  ep->code    = NULL;
  ep->help    = NULL;
  ep->pvalue  = NULL;
  ep->arity   = 0;
  return ep;
}

/* Look for s of length len in T; if 'insert', insert if missing */
static entree *
findentry(const char *s, long len, entree **T, int insert)
{
  ulong hash = hashvalue_raw(s, len);
  entree *ep;
  for (ep = T[hash % functions_tblsz]; ep; ep = ep->next)
    if (ep->hash == hash)
    {
      const char *t = ep->name;
      if (!strncmp(t, s, len) && !t[len]) return ep;
    }
  /* not found */
  if (insert) { ep = initep(s,len); insertep(ep, T, hash); }
  return ep;
}
entree *
pari_is_default(const char *s)
{ return findentry(s, strlen(s), defaults_hash, 0); }
entree *
is_entry(const char *s)
{ return findentry(s, strlen(s), functions_hash, 0); }
entree *
fetch_entry_raw(const char *s, long len)
{ return findentry(s, len, functions_hash, 1); }
entree *
fetch_entry(const char *s) { return fetch_entry_raw(s, strlen(s)); }

/*******************************************************************/
/*                                                                 */
/*                  SYNTACTICAL ANALYZER FOR GP                    */
/*                                                                 */
/*******************************************************************/
GEN
readseq(char *t)
{
  pari_sp av = avma;
  GEN x;
  if (gp_meta(t,0)) return gnil;
  x = pari_compile_str(t);
  return gerepileupto(av, closure_evalres(x));
}

/* filtered readseq = remove blanks and comments */
GEN
gp_read_str(const char *s)
{
  char *t = gp_filter(s);
  GEN x = readseq(t);
  pari_free(t); return x;
}

GEN
compile_str(const char *s)
{
  char *t = gp_filter(s);
  GEN x = pari_compile_str(t);
  pari_free(t); return x;
}

static long
check_proto(const char *code)
{
  long arity = 0;
  const char *s = code, *old;
  if (*s == 'l' || *s == 'v' || *s == 'i' || *s == 'm' || *s == 'u') s++;
  while (*s && *s != '\n') switch (*s++)
  {
    case '&':
    case 'C':
    case 'G':
    case 'I':
    case 'J':
    case 'U':
    case 'L':
    case 'M':
    case 'P':
    case 'W':
    case 'f':
    case 'n':
    case 'p':
    case 'b':
    case 'r':
      arity++;
      break;
    case 'E':
    case 's':
      if (*s == '*') s++;
      arity++;
      break;
    case 'D':
      if (*s == 'G' || *s == '&' || *s == 'n' || *s == 'I' || *s == 'E'
                    || *s == 'V' || *s == 'P' || *s == 's' || *s == 'r')
      {
        if (*s != 'V') arity++;
        s++; break;
      }
      old = s; while (*s && *s != ',') s++;
      if (*s != ',') pari_err(e_SYNTAX, "missing comma", old, code);
      break;
    case 'V':
    case '=':
    case ',': break;
    case '\n': break; /* Before the mnemonic */

    case 'm':
    case 'l':
    case 'i':
    case 'v': pari_err(e_SYNTAX, "this code has to come first", s-1, code);
    default: pari_err(e_SYNTAX, "unknown parser code", s-1, code);
  }
  if (arity > 20) pari_err_IMPL("functions with more than 20 parameters");
  return arity;
}
static void
check_name(const char *name)
{
  const char *s = name;
  if (isalpha((int)*s))
    while (is_keyword_char(*++s)) /* empty */;
  if (*s) pari_err(e_SYNTAX,"not a valid identifier", s, name);
}

entree *
install(void *f, const char *name, const char *code)
{
  long arity = check_proto(code);
  entree *ep;

  check_name(name);
  ep = fetch_entry(name);
  if (ep->valence != EpNEW)
  {
    if (ep->valence != EpINSTALL)
      pari_err(e_MISC,"[install] identifier '%s' already in use", name);
    pari_warn(warner, "[install] updating '%s' prototype; module not reloaded", name);
    if (ep->code) pari_free((void*)ep->code);
  }
  else
  {
    ep->value = f;
    ep->valence = EpINSTALL;
  }
  ep->code = pari_strdup(code);
  ep->arity = arity; return ep;
}

static void
killep(entree *ep)
{
  GEN p = (GEN)initial_value(ep);
  freeep(ep);
  *p = 0; /* otherwise pari_var_create won't regenerate it */
  ep->valence = EpNEW;
  ep->value   = NULL;
  ep->pvalue  = NULL;
}
/* Kill ep, i.e free all memory it references, and reset to initial value */
void
kill0(const char *e)
{
  entree *ep = is_entry(e);
  if (!ep || EpSTATIC(ep)) pari_err(e_MISC,"can't kill that");
  killep(ep);
}

void
addhelp(const char *e, char *s)
{
  entree *ep = fetch_entry(e);
  void *f = (void *) ep->help;
  ep->help = pari_strdup(s);
  if (f && !EpSTATIC(ep)) pari_free(f);
}

GEN
type0(GEN x)
{
  const char *s = type_name(typ(x));
  return strtoGENstr(s);
}

/*******************************************************************/
/*                                                                 */
/*                              PARSER                             */
/*                                                                 */
/*******************************************************************/

#ifdef LONG_IS_64BIT
static const long MAX_DIGITS  = 19;
#else
static const long MAX_DIGITS  = 9;
#endif

static const long MAX_XDIGITS = BITS_IN_LONG>>2;
static const long MAX_BDIGITS = BITS_IN_LONG;

static int
ishex(const char **s)
{
  if (**s == '0' && ((*s)[1] == 'x' || (*s)[1] == 'X' ))
  {
    *s += 2;
    return 1;
  }
  else
    return 0;
}

static int
isbin(const char **s)
{
  if (**s == '0' && ((*s)[1] == 'b' || (*s)[1] == 'B' ))
  {
    *s += 2;
    return 1;
  }
  else
    return 0;
}

static ulong
bin_number_len(const char *s, long n)
{
  ulong m = 0;
  long i;
  for (i = 0; i < n; i++,s++)
    m = 2*m + (*s - '0');
  return m;
}

static int
pari_isbdigit(int c)
{
  return c=='0' || c=='1';
}

static ulong
hex_number_len(const char *s, long n)
{
  ulong m = 0;
  long i;
  for(i = 0; i < n; i++, s++)
  {
    ulong c;
    if( *s >= '0' && *s <= '9')
      c = *s - '0';
    else if( *s >= 'A' && *s <= 'F')
      c = *s - 'A' + 10;
    else
      c = *s - 'a' + 10;
    m = 16*m + c;
  }
  return m;
}

static GEN
strtobin_len(const char *s, long n, long B, ulong num(const char *s, long n))
{
  long i, l = (n+B-1)/B;
  GEN N, Np;
  N = cgetipos(l+2);
  Np = int_LSW(N);
  for (i=1; i<l; i++, Np = int_nextW(Np))
    uel(Np, 0) = num(s+n-i*B, B);
  uel(Np, 0) = num(s, n-(i-1)*B);
  return int_normalize(N, 0);
}

static GEN
binary_read(const char **ps, long B, int is(int), ulong num(const char *s, long n))
{
  const char *s = *ps;
  while (is((int)**ps)) (*ps)++;
  return strtobin_len(s, *ps-s, B, num);
}

static GEN
bin_read(const char **ps)
{
  return binary_read(ps, MAX_BDIGITS, pari_isbdigit, bin_number_len);
}

static GEN
hex_read(const char **ps)
{
  return binary_read(ps, MAX_XDIGITS, isxdigit, hex_number_len);
}

static ulong
dec_number_len(const char *s, long B)
{
  ulong m = 0;
  long n;
  for (n = 0; n < B; n++,s++)
    m = 10*m + (*s - '0');
  return m;
}

static GEN
dec_strtoi_len(const char *s, long n)
{
  const long B = MAX_DIGITS;
  long i, l = (n+B-1)/B;
  GEN V = cgetg(l+1, t_VECSMALL);
  for (i=1; i<l; i++)
    uel(V,i) = dec_number_len(s+n-i*B, B);
  uel(V, i) = dec_number_len(s, n-(i-1)*B);
  return fromdigitsu(V, powuu(10, B));
}

static GEN
dec_read_more(const char **ps)
{
  pari_sp av = avma;
  const char *s = *ps;
  while (isdigit((int)**ps)) (*ps)++;
  return gerepileuptoint(av, dec_strtoi_len(s, *ps-s));
}

static ulong
number(int *n, const char **s)
{
  ulong m = 0;
  for (*n = 0; *n < MAX_DIGITS && isdigit((int)**s); (*n)++,(*s)++)
    m = 10*m + (**s - '0');
  return m;
}

static GEN
dec_read(const char **s)
{
  int nb;
  ulong y  = number(&nb, s);
  if (nb < MAX_DIGITS)
    return utoi(y);
  *s -= MAX_DIGITS;
  return dec_read_more(s);
}

static GEN
real_read_more(GEN y, const char **ps)
{
  pari_sp av = avma;
  const char *s = *ps;
  GEN z = dec_read(ps);
  long e = *ps-s;
  return gerepileuptoint(av, addmulii(z, powuu(10, e), y));
}

static long
exponent(const char **pts)
{
  const char *s = *pts;
  long n;
  int nb;
  switch(*++s)
  {
    case '-': s++; n = -(long)number(&nb, &s); break;
    case '+': s++; /* Fall through */
    default: n = (long)number(&nb, &s);
  }
  *pts = s; return n;
}

static GEN
real_0_digits(long n) {
  long b = (n > 0)? (long)(n/LOG10_2): (long)-((-n)/LOG10_2 + 1);
  return real_0_bit(b);
}

static GEN
real_read(pari_sp av, const char **s, GEN y, long prec)
{
  long l, n = 0;
  switch(**s)
  {
    default: return y; /* integer */
    case '.':
    {
      const char *old = ++*s;
      if (isalpha((int)**s) || **s=='.')
      {
        if (**s == 'E' || **s == 'e') {
          n = exponent(s);
          if (!signe(y)) { avma = av; return real_0_digits(n); }
          break;
        }
        --*s; return y; /* member */
      }
      if (isdigit((int)**s)) y = real_read_more(y, s);
      n = old - *s;
      if (**s != 'E' && **s != 'e')
      {
        if (!signe(y)) { avma = av; return real_0(prec); }
        break;
      }
    }
    /* Fall through */
    case 'E': case 'e':
      n += exponent(s);
      if (!signe(y)) { avma = av; return real_0_digits(n); }
  }
  l = nbits2prec(bit_accuracy(lgefint(y)));
  if (l < prec) l = prec; else prec = l;
  if (!n) return itor(y, prec);
  incrprec(l);
  y = itor(y, l);
  if (n > 0)
    y = mulrr(y, rpowuu(10UL, (ulong)n, l));
  else
    y = divrr(y, rpowuu(10UL, (ulong)-n, l));
  return gerepileuptoleaf(av, rtor(y, prec));
}

static GEN
int_read(const char **s)
{
  GEN y;
  if (isbin(s))
    y = bin_read(s);
  else if (ishex(s))
    y = hex_read(s);
  else
    y = dec_read(s);
  return y;
}

GEN
strtoi(const char *s) { return int_read(&s); }

GEN
strtor(const char *s, long prec)
{
  pari_sp av = avma;
  GEN y = dec_read(&s);
  y = real_read(av, &s, y, prec);
  if (typ(y) == t_REAL) return y;
  return gerepileuptoleaf(av, itor(y, prec));
}

static void
skipdigits(char **lex) {
  while (isdigit((int)**lex)) ++*lex;
}

static int
skipexponent(char **lex)
{
  char *old=*lex;
  if ((**lex=='e' || **lex=='E'))
  {
    ++*lex;
    if ( **lex=='+' || **lex=='-' ) ++*lex;
    if (!isdigit((int)**lex))
    {
      *lex=old;
      return KINTEGER;
    }
    skipdigits(lex);
    return KREAL;
  }
  return KINTEGER;
}

static int
skipconstante(char **lex)
{
  skipdigits(lex);
  if (**lex=='.')
  {
    char *old = ++*lex;
    if (**lex == '.') { --*lex; return KINTEGER; }
    if (isalpha((int)**lex))
    {
      skipexponent(lex);
      if (*lex == old)
      {
        --*lex; /* member */
        return KINTEGER;
      }
      return KREAL;
    }
    skipdigits(lex);
    skipexponent(lex);
    return KREAL;
  }
  return skipexponent(lex);
}

static void
skipstring(char **lex)
{
  while (**lex)
  {
    while (**lex == '\\') *lex+=2;
    if (**lex == '"')
    {
      if ((*lex)[1] != '"') break;
      *lex += 2; continue;
    }
    (*lex)++;
  }
}

int
pari_lex(union token_value *yylval, struct node_loc *yylloc, char **lex)
{
  (void) yylval;
  yylloc->start=*lex;
  if (!**lex)
  {
    yylloc->end=*lex;
    return 0;
  }
  if (isalpha((int)**lex))
  {
    while (is_keyword_char(**lex)) ++*lex;
    yylloc->end=*lex;
    return KENTRY;
  }
  if (**lex=='"')
  {
    ++*lex;
    skipstring(lex);
    if (!**lex)
      compile_err("run-away string",*lex-1);
    ++*lex;
    yylloc->end=*lex;
    return KSTRING;
  }
  if (**lex == '.')
  {
    int token;
    if ((*lex)[1]== '.')
    {
      *lex+=2; yylloc->end = *lex; return KDOTDOT;
    }
    token=skipconstante(lex);
    if (token==KREAL)
    {
      yylloc->end = *lex;
      return token;
    }
    ++*lex;
    yylloc->end=*lex;
    return '.';
  }
  if (isbin((const char**)lex))
  {
    while (**lex=='0' || **lex=='1') ++*lex;
    return KINTEGER;
  }
  if (ishex((const char**)lex))
  {
    while (isxdigit((int)**lex)) ++*lex;
    return KINTEGER;
  }
  if (isdigit((int)**lex))
  {
    int token=skipconstante(lex);
    yylloc->end = *lex;
    return token;
  }
  if ((*lex)[1]=='=')
    switch (**lex)
    {
    case '=':
      if ((*lex)[2]=='=')
      { *lex+=3; yylloc->end = *lex; return KID; }
      else
      { *lex+=2; yylloc->end = *lex; return KEQ; }
    case '>':
      *lex+=2; yylloc->end = *lex; return KGE;
    case '<':
      *lex+=2; yylloc->end = *lex; return KLE;
    case '*':
      *lex+=2; yylloc->end = *lex; return KME;
    case '/':
      *lex+=2; yylloc->end = *lex; return KDE;
    case '%':
      if ((*lex)[2]=='=') break;
      *lex+=2; yylloc->end = *lex; return KMODE;
    case '!':
      if ((*lex)[2]=='=') break;
      *lex+=2; yylloc->end = *lex; return KNE;
    case '\\':
      *lex+=2; yylloc->end = *lex; return KEUCE;
    case '+':
      *lex+=2; yylloc->end = *lex; return KPE;
    case '-':
      *lex+=2; yylloc->end = *lex; return KSE;
    }
  if (**lex==')' && (*lex)[1]=='-' && (*lex)[2]=='>')
  {
    *lex+=3; yylloc->end = *lex; return KPARROW;
  }
  if (**lex=='-' && (*lex)[1]=='>')
  {
    *lex+=2; yylloc->end = *lex; return KARROW;
  }
  if (**lex=='<' && (*lex)[1]=='>')
  {
    *lex+=2; yylloc->end = *lex; return KNE;
  }
  if (**lex=='\\' && (*lex)[1]=='/')
    switch((*lex)[2])
    {
    case '=':
      *lex+=3; yylloc->end = *lex; return KDRE;
    default:
      *lex+=2; yylloc->end = *lex; return KDR;
    }
  if ((*lex)[1]==**lex)
    switch (**lex)
    {
    case '&':
      *lex+=2; yylloc->end = *lex; return KAND;
    case '|':
      *lex+=2; yylloc->end = *lex; return KOR;
    case '+':
      *lex+=2; yylloc->end = *lex; return KPP;
    case '-':
      *lex+=2; yylloc->end = *lex; return KSS;
    case '>':
      if ((*lex)[2]=='=') { *lex+=3; yylloc->end = *lex; return KSRE;}
      *lex+=2; yylloc->end = *lex; return KSR;
    case '<':
      if ((*lex)[2]=='=')
      { *lex+=3; yylloc->end = *lex; return KSLE; }
      *lex+=2; yylloc->end = *lex; return KSL;
    }
  yylloc->end = *lex+1;
  return (unsigned char) *(*lex)++;
}

/********************************************************************/
/**                                                                **/
/**                            STRINGS                             **/
/**                                                                **/
/********************************************************************/

/* return the first n0 chars of s as a GEN [s may not be 0-terminated] */
GEN
strntoGENstr(const char *s, long n0)
{
  long n = nchar2nlong(n0+1);
  GEN x = cgetg(n+1, t_STR);
  char *t = GSTR(x);
  x[n] = 0;
  strncpy(t, s, n0); t[n0] = 0; return x;
}

GEN
strtoGENstr(const char *s) { return strntoGENstr(s, strlen(s)); }

GEN
chartoGENstr(char c)
{
  GEN x = cgetg(2, t_STR);
  char *t = GSTR(x);
  t[0] = c; t[1] = 0; return x;
}

/********************************************************************/
/*                                                                  */
/*                Formal variables management                       */
/*                                                                  */
/********************************************************************/
static THREAD long max_priority, min_priority;
static THREAD long max_avail; /* max variable not yet used */
static THREAD long nvar; /* first GP free variable */
static hashtable *h_polvar;
static struct pari_varstate global_varstate;
static long *global_varpriority;

void
varstate_save(struct pari_varstate *s)
{
  s->nvar = nvar;
  s->max_avail = max_avail;
  s->max_priority = max_priority;
  s->min_priority = min_priority;
}

static void
varentries_set(long v, entree *ep)
{
  hash_insert(h_polvar, (void*)ep->name, (void*)v);
  varentries[v] = ep;
}
static int
_given_value(void *E, hashentry *e) { return e->val == E; }

static void
varentries_unset(long v)
{
  entree *ep = varentries[v];
  if (ep)
  {
    hashentry *e = hash_remove_select(h_polvar, (void*)ep->name, (void*)v,
        _given_value);
    if (!e) pari_err_BUG("varentries_unset [unknown var]");
    varentries[v] = NULL;
    pari_free(e);
    if (v <= nvar && ep == is_entry(ep->name))
    { /* known to the GP interpreter; entree in functions_hash is permanent */
      GEN p = (GEN)initial_value(ep);
      if (ep->value == p) { ep->value = NULL; ep->valence = EpNEW; }
      *p = 0;
    }
    else /* from name_var() or a direct pari_var_create() */
      pari_free(ep);
 }
}
static void
varentries_reset(long v, entree *ep)
{
  varentries_unset(v);
  varentries_set(v, ep);
}

static void
var_restore(struct pari_varstate *s)
{
  nvar = s->nvar;
  max_avail = s->max_avail;
  max_priority = s->max_priority;
  min_priority = s->min_priority;
}

void
varstate_restore(struct pari_varstate *s)
{
  long i;
  for (i = nvar; i >= s->nvar; i--)
  {
    varentries_unset(i);
    varpriority[i] = -i;
  }
  for (i = max_avail+1; i <= s->max_avail; i++)
  {
    varentries_unset(i);
    varpriority[i] = -i;
  }
  var_restore(s);
}

void
pari_thread_init_varstate(void)
{
  long i;
  var_restore(&global_varstate);
  varpriority = (long*)newblock((MAXVARN+2)) + 1;
  varpriority[-1] = 1-LONG_MAX;
  for (i = 0; i < max_avail; i++) varpriority[i] = global_varpriority[i];
}

void
pari_pthread_init_varstate(void)
{
  varstate_save(&global_varstate);
  global_varpriority = varpriority;
}

void
pari_var_close(void)
{
  free((void*)varentries);
  free((void*)(varpriority-1));
  hash_destroy(h_polvar);
}

void
pari_var_init(void)
{
  long i;
  varentries = (entree**) pari_calloc((MAXVARN+1)*sizeof(entree*));
  varpriority = (long*)pari_malloc((MAXVARN+2)*sizeof(long)) + 1;
  varpriority[-1] = 1-LONG_MAX;
  h_polvar = hash_create_str(100, 0);
  nvar = 0; max_avail = MAXVARN;
  max_priority = min_priority = 0;
  (void)fetch_user_var("x");
  (void)fetch_user_var("y");
  /* initialize so that people can use pol_x(i) directly */
  for (i = 2; i <= (long)MAXVARN; i++) varpriority[i] = -i;
  /* reserve varnum 1..9 for static temps with predictable priority wrt x */
  nvar = 10;
  min_priority = -MAXVARN;
}
long pari_var_next(void) { return nvar; }
long pari_var_next_temp(void) { return max_avail; }
long
pari_var_create(entree *ep)
{
  GEN p = (GEN)initial_value(ep);
  long v;
  if (*p) return varn(p);
  if (nvar == max_avail) pari_err(e_MISC,"no more variables available");
  v = nvar++;
  /* set p = pol_x(v) */
  p[0] = evaltyp(t_POL) | _evallg(4);
  p[1] = evalsigne(1) | evalvarn(v);
  gel(p,2) = gen_0;
  gel(p,3) = gen_1;
  varentries_set(v, ep);
  varpriority[v]= min_priority--;
  return v;
}

long
delete_var(void)
{ /* user wants to delete one of his/her/its variables */
  if (max_avail == MAXVARN) return 0; /* nothing to delete */
  max_avail++;
  if      (varpriority[max_avail] == min_priority) min_priority++;
  else if (varpriority[max_avail] == max_priority) max_priority--;
  return max_avail+1;
}
long
fetch_var(void)
{
  if (nvar == max_avail) pari_err(e_MISC,"no more variables available");
  varpriority[max_avail] = min_priority--;
  return max_avail--;
}
long
fetch_var_higher(void)
{
  if (nvar == max_avail) pari_err(e_MISC,"no more variables available");
  varpriority[max_avail] = ++max_priority;
  return max_avail--;
}

static int
_higher(void *E, hashentry *e)
{ long v = (long)e->val; return (varncmp(v, (long)E) < 0); }
static int
_lower(void *E, hashentry *e)
{ long v = (long)e->val; return (varncmp(v, (long)E) > 0); }

static GEN
var_register(long v, const char *s)
{
  varentries_reset(v, initep(s, strlen(s)));
  return pol_x(v);
}
GEN
varhigher(const char *s, long w)
{
  long v;
  if (w >= 0)
  {
    hashentry *e = hash_select(h_polvar, (void*)s, (void*)w, _higher);
    if (e) return pol_x((long)e->val);
  }
  /* no luck: need to create */
  if (nvar == max_avail) pari_err(e_MISC,"no more variables available");
  v = nvar++;
  varpriority[v]= ++max_priority;
  return var_register(v, s);
}
GEN
varlower(const char *s, long w)
{
  long v;
  if (w >= 0)
  {
    hashentry *e = hash_select(h_polvar, (void*)s, (void*)w, _lower);
    if (e) return pol_x((long)e->val);
  }
  /* no luck: need to create */
  v = fetch_var();
  return var_register(v, s);
}

long
fetch_user_var(const char *s)
{
  entree *ep = fetch_entry(s);
  long v;
  switch (EpVALENCE(ep))
  {
    case EpVAR: return varn((GEN)initial_value(ep));
    case EpNEW: break;
    default: pari_err(e_MISC, "%s already exists with incompatible valence", s);
  }
  v = pari_var_create(ep);
  ep->valence = EpVAR;
  ep->value = initial_value(ep);
  return v;
}

GEN
fetch_var_value(long v, GEN t)
{
  entree *ep = varentries[v];
  if (!ep) return NULL;
  if (t)
  {
    long vn = localvars_find(t,ep);
    if (vn) return get_lex(vn);
  }
  return (GEN)ep->value;
}

void
name_var(long n, const char *s)
{
  entree *ep;
  char *u;

  if (n < pari_var_next())
    pari_err(e_MISC, "renaming a GP variable is forbidden");
  if (n > (long)MAXVARN)
    pari_err_OVERFLOW("variable number");

  ep = (entree*)pari_malloc(sizeof(entree) + strlen(s) + 1);
  u = (char *)initial_value(ep);
  ep->valence = EpVAR;
  ep->name = u; strcpy(u,s);
  ep->value = gen_0; /* in case geval is called */
  varentries_reset(n, ep);
}

static int
cmp_by_var(void *E,GEN x, GEN y)
{ (void)E; return varncmp((long)x,(long)y); }
GEN
vars_sort_inplace(GEN z)
{ gen_sort_inplace(z,NULL,cmp_by_var,NULL); return z; }
GEN
vars_to_RgXV(GEN h)
{
  long i, l = lg(h);
  GEN z = cgetg(l, t_VEC);
  for (i = 1; i < l; i++) gel(z,i) = pol_x(h[i]);
  return z;
}
GEN
gpolvar(GEN x)
{
  long v;
  if (!x) {
    GEN h = hash_values(h_polvar);
    return vars_to_RgXV(vars_sort_inplace(h));
  }
  if (typ(x)==t_PADIC) return gcopy( gel(x,2) );
  v = gvar(x);
  if (v==NO_VARIABLE) return gen_0;
  return pol_x(v);
}

static void
fill_hashtable_single(entree **table, entree *ep)
{
  EpSETSTATIC(ep);
  insertep(ep, table,  hashvalue(ep->name));
  if (ep->code) ep->arity = check_proto(ep->code);
  ep->pvalue = NULL;
}

void
pari_fill_hashtable(entree **table, entree *ep)
{
  for ( ; ep->name; ep++) fill_hashtable_single(table, ep);
}

void
pari_add_function(entree *ep)
{
  fill_hashtable_single(functions_hash, ep);
}

/********************************************************************/
/**                                                                **/
/**                        SIMPLE GP FUNCTIONS                     **/
/**                                                                **/
/********************************************************************/

#define ALIAS(ep) (entree *) ((GEN)ep->value)[1]

entree *
do_alias(entree *ep)
{
  while (ep->valence == EpALIAS) ep = ALIAS(ep);
  return ep;
}

void
alias0(const char *s, const char *old)
{
  entree *ep, *e;
  GEN x;

  ep = fetch_entry(old);
  e  = fetch_entry(s);
  if (EpVALENCE(e) != EpALIAS && EpVALENCE(e) != EpNEW)
    pari_err(e_MISC,"can't replace an existing symbol by an alias");
  freeep(e);
  x = cgetg_block(2, t_VECSMALL); gel(x,1) = (GEN)ep;
  e->value=x; e->valence=EpALIAS;
}

GEN
ifpari(GEN g, GEN a/*closure*/, GEN b/*closure*/)
{
  if (gequal0(g)) /* false */
    return b? closure_evalgen(b): gnil;
  else /* true */
    return a? closure_evalgen(a): gnil;
}

void
ifpari_void(GEN g, GEN a/*closure*/, GEN b/*closure*/)
{
  if (gequal0(g)) /* false */
  { if (b) closure_evalvoid(b); }
  else /* true */
  { if (a) closure_evalvoid(a); }
}

GEN
ifpari_multi(GEN g, GEN a/*closure*/)
{
  long i, nb = lg(a)-1;
  if (!gequal0(g)) /* false */
    return closure_evalgen(gel(a,1));
  for(i=2;i<nb;i+=2)
  {
    GEN g = closure_evalgen(gel(a,i));
    if (!g) return g;
    if (!gequal0(g))
      return closure_evalgen(gel(a,i+1));
  }
  return i<=nb? closure_evalgen(gel(a,i)): gnil;
}

GEN
andpari(GEN a, GEN b/*closure*/)
{
  GEN g;
  if (gequal0(a))
    return gen_0;
  g=closure_evalgen(b);
  if (!g) return g;
  return gequal0(g)?gen_0:gen_1;
}

GEN
orpari(GEN a, GEN b/*closure*/)
{
  GEN g;
  if (!gequal0(a))
    return gen_1;
  g=closure_evalgen(b);
  if (!g) return g;
  return gequal0(g)?gen_0:gen_1;
}

GEN gmule(GEN *x, GEN y) { *x = gmul(*x,y); return *x; }
GEN gdive(GEN *x, GEN y) { *x = gdiv(*x,y); return *x; }
GEN gdivente(GEN *x, GEN y) { *x = gdivent(*x,y); return *x; }
GEN gdivrounde(GEN *x, GEN y) { *x = gdivround(*x,y); return *x; }
GEN gmode(GEN *x, GEN y) { *x = gmod(*x,y); return *x; }
GEN gshiftle(GEN *x, long n) { *x = gshift(*x,n); return *x; }
GEN gshiftre(GEN *x, long n) { *x = gshift(*x,-n); return *x; }
GEN gadde(GEN *x, GEN y) { *x = gadd(*x,y); return *x; }
GEN gadd1e(GEN *x) { *x = typ(*x)==t_INT?addiu(*x,1):gaddgs(*x,1); return *x; }
GEN gsube(GEN *x, GEN y) { *x = gsub(*x,y); return *x; }
GEN gsub1e(GEN *x) { *x = typ(*x)==t_INT?subiu(*x,1):gsubgs(*x,1); return *x; }

GEN gshift_right(GEN x, long n) { return gshift(x,-n); }
