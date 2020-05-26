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

#ifdef _WIN32
#  include "../systems/mingw/mingw.h"
#endif


/* Return all chars, up to next separator
 * [as strtok but must handle verbatim character string] */
char*
get_sep(const char *t)
{
  char *buf = stack_malloc(strlen(t)+1);
  char *s = buf;
  int outer = 1;

  for(;;)
  {
    switch(*s++ = *t++)
    {
      case '"':
        outer = !outer; break;
      case '\0':
        return buf;
      case ';':
        if (outer) { s[-1] = 0; return buf; }
        break;
      case '\\': /* gobble next char */
        if (! (*s++ = *t++) ) return buf;
    }
  }
}

/* "atoul" + optional [kmg] suffix */
static ulong
my_int(char *s)
{
  ulong n = 0;
  char *p = s;

  while (isdigit((int)*p)) {
    ulong m;
    if (n > (~0UL / 10)) pari_err(e_SYNTAX,"integer too large",s,s);
    n *= 10; m = n;
    n += *p++ - '0';
    if (n < m) pari_err(e_SYNTAX,"integer too large",s,s);
  }
  if (n)
  {
    switch(*p)
    {
      case 'k': case 'K': n = umuluu_or_0(n,1000UL);       p++; break;
      case 'm': case 'M': n = umuluu_or_0(n,1000000UL);    p++; break;
      case 'g': case 'G': n = umuluu_or_0(n,1000000000UL); p++; break;
#ifdef LONG_IS_64BIT
      case 't': case 'T': n = umuluu_or_0(n,1000000000000UL); p++; break;
#endif
    }
    if (!n) pari_err(e_SYNTAX,"integer too large",s,s);
  }
  if (*p) pari_err(e_SYNTAX,"I was expecting an integer here", s, s);
  return n;
}

long
get_int(const char *s, long dflt)
{
  pari_sp av = avma;
  char *p = get_sep(s);
  long n;
  int minus = 0;

  if (*p == '-') { minus = 1; p++; }
  if (!isdigit((int)*p)) { avma = av; return dflt; }

  n = (long)my_int(p);
  if (n < 0) pari_err(e_SYNTAX,"integer too large",s,s);
  avma = av; return minus? -n: n;
}

ulong
get_uint(const char *s)
{
  pari_sp av = avma;
  char *p = get_sep(s);
  ulong u;
  if (*p == '-') pari_err(e_SYNTAX,"arguments must be positive integers",s,s);
  u = my_int(p); avma = av; return u;
}

#if defined(__EMX__) || defined(_WIN32) || defined(__CYGWIN32__)
#  define PATH_SEPARATOR ';' /* beware DOSish 'C:' disk drives */
#else
#  define PATH_SEPARATOR ':'
#endif

static const char *
pari_default_path(void) {
#if PATH_SEPARATOR == ';'
  return ".;C:;C:/gp";
#elif defined(UNIX)
  return ".:~:~/gp";
#else
  return ".";
#endif
}

static void
delete_dirs(gp_path *p)
{
  char **v = p->dirs, **dirs;
  if (v)
  {
    p->dirs = NULL; /* in case of error */
    for (dirs = v; *dirs; dirs++) pari_free(*dirs);
    pari_free(v);
  }
}

static void
expand_path(gp_path *p)
{
  char **dirs, *s, *v = p->PATH;
  int i, n = 0;

  delete_dirs(p);
  if (*v)
  {
    v = pari_strdup(v);
    for (s=v; *s; s++)
      if (*s == PATH_SEPARATOR) {
        *s = 0;
        if (s == v || s[-1] != 0) n++; /* ignore empty path components */
      }
    dirs = (char**) pari_malloc((n + 2)*sizeof(char *));

    for (s=v, i=0; i<=n; i++)
    {
      char *end, *f;
      while (!*s) s++; /* skip empty path components */
      f = end = s + strlen(s);
      while (f > s && *--f == '/') *f = 0; /* skip trailing '/' */
      dirs[i] = path_expand(s);
      s = end + 1; /* next path component */
    }
    pari_free((void*)v);
  }
  else
  {
    dirs = (char**) pari_malloc(sizeof(char *));
    i = 0;
  }
  dirs[i] = NULL; p->dirs = dirs;
}
void
pari_init_paths(void)
{
  expand_path(GP_DATA->path);
  expand_path(GP_DATA->sopath);
}

static void
delete_path(gp_path *p) { delete_dirs(p); free(p->PATH); }
void
pari_close_paths(void)
{
  delete_path(GP_DATA->path);
  delete_path(GP_DATA->sopath);
}

/********************************************************************/
/*                                                                  */
/*                            DEFAULTS                              */
/*                                                                  */
/********************************************************************/

long
getrealprecision(void)
{
  return GP_DATA->fmt->sigd;
}

long
setrealprecision(long n, long *prec)
{
  GP_DATA->fmt->sigd = n;
  *prec = ndec2prec(n);
  precreal = prec2nbits(*prec);
  return n;
}

GEN
sd_toggle(const char *v, long flag, const char *s, int *ptn)
{
  int state = *ptn;
  if (v)
  {
    int n = (int)get_int(v,0);
    if (n == state) return gnil;
    if (n != !state)
    {
      char *t = stack_malloc(64 + strlen(s));
      (void)sprintf(t, "default: incorrect value for %s [0:off / 1:on]", s);
      pari_err(e_SYNTAX, t, v,v);
    }
    state = *ptn = n;
  }
  switch(flag)
  {
    case d_RETURN: return utoi(state);
    case d_ACKNOWLEDGE:
      if (state) pari_printf("   %s = 1 (on)\n", s);
      else       pari_printf("   %s = 0 (off)\n", s);
      break;
  }
  return gnil;
}

static void
sd_ulong_init(const char *v, const char *s, ulong *ptn, ulong Min, ulong Max)
{
  if (v)
  {
    ulong n = get_uint(v);
    if (n > Max || n < Min)
    {
      char *buf = stack_malloc(strlen(s) + 2 * 20 + 40);
      (void)sprintf(buf, "default: incorrect value for %s [%lu-%lu]",
                    s, Min, Max);
      pari_err(e_SYNTAX, buf, v,v);
    }
    *ptn = n;
  }
}

/* msg is NULL or NULL-terminated array with msg[0] != NULL. */
GEN
sd_ulong(const char *v, long flag, const char *s, ulong *ptn, ulong Min, ulong Max,
         const char **msg)
{
  ulong n = *ptn;
  sd_ulong_init(v, s, ptn, Min, Max);
  switch(flag)
  {
    case d_RETURN:
      return utoi(*ptn);
    case d_ACKNOWLEDGE:
      if (!v || *ptn != n) {
        if (!msg)         /* no specific message */
          pari_printf("   %s = %lu\n", s, *ptn);
        else if (!msg[1]) /* single message, always printed */
          pari_printf("   %s = %lu %s\n", s, *ptn, msg[0]);
        else              /* print (new)-n-th message */
          pari_printf("   %s = %lu %s\n", s, *ptn, msg[*ptn]);
      }
      break;
  }
  return gnil;
}

static void
err_intarray(char *t, char *p, const char *s)
{
  char *b = stack_malloc(64 + strlen(s));
  sprintf(b, "incorrect value for %s", s);
  pari_err(e_SYNTAX, b, p, t);
}
static GEN
parse_intarray(const char *v, const char *s)
{
  char *p, *t = gp_filter(v);
  long i, l;
  GEN w;
  if (*t != '[') err_intarray(t, t, s);
  if (t[1] == ']') { pari_free(t); return cgetalloc(t_VECSMALL, 1); }
  for (p = t+1, l=2; *p; p++)
    if (*p == ',') l++;
    else if (*p < '0' || *p > '9') break;
  if (*p != ']') err_intarray(t, p, s);
  w = cgetalloc(t_VECSMALL, l);
  for (p = t+1, i=0; *p; p++)
  {
    long n = 0;
    while (*p >= '0' && *p <= '9') n = 10*n + (*p++ -'0');
    w[++i] = n;
  }
  pari_free(t); return w;
}
GEN
sd_intarray(const char *v, long flag, GEN *pz, const char *s)
{
  if (v) { GEN z = *pz; *pz = parse_intarray(v, s); pari_free(z); }
  switch(flag)
  {
    case d_RETURN: return zv_to_ZV(*pz);
    case d_ACKNOWLEDGE: pari_printf("   %s = %Ps\n", s, zv_to_ZV(*pz));
  }
  return gnil;
}

GEN
sd_realprecision(const char *v, long flag)
{
  pariout_t *fmt = GP_DATA->fmt;
  if (v)
  {
    ulong newnb = fmt->sigd;
    long prec;
    sd_ulong_init(v, "realprecision", &newnb, 1, prec2ndec(LGBITS));
    if (fmt->sigd == (long)newnb) return gnil;
    if (fmt->sigd >= 0) fmt->sigd = newnb;
    prec = ndec2nbits(newnb);
    if (prec == precreal) return gnil;
    precreal = prec;
  }
  if (flag == d_RETURN) return stoi(nbits2ndec(precreal));
  if (flag == d_ACKNOWLEDGE)
  {
    long n = nbits2ndec(precreal);
    pari_printf("   realprecision = %ld significant digits", n);
    if (fmt->sigd < 0)
      pari_puts(" (all digits displayed)");
    else if (n != fmt->sigd)
      pari_printf(" (%ld digits displayed)", fmt->sigd);
    pari_putc('\n');
  }
  return gnil;
}

GEN
sd_realbitprecision(const char *v, long flag)
{
  pariout_t *fmt = GP_DATA->fmt;
  if (v)
  {
    ulong newnb = precreal;
    long n;
    sd_ulong_init(v, "realbitprecision", &newnb, 1, prec2nbits(LGBITS));
    if ((long)newnb == precreal) return gnil;
    n = nbits2ndec(newnb);
    if (!n) n = 1;
    if (fmt->sigd >= 0) fmt->sigd = n;
    precreal = (long) newnb;
  }
  if (flag == d_RETURN) return stoi(precreal);
  if (flag == d_ACKNOWLEDGE)
  {
    pari_printf("   realbitprecision = %ld significant bits", precreal);
    if (fmt->sigd < 0)
      pari_puts(" (all digits displayed)");
    else
      pari_printf(" (%ld decimal digits displayed)", fmt->sigd);
    pari_putc('\n');
  }
  return gnil;
}

GEN
sd_seriesprecision(const char *v, long flag)
{
  const char *msg[] = {"significant terms", NULL};
  return sd_ulong(v,flag,"seriesprecision",&precdl, 1,LGBITS,msg);
}

static long
gp_get_color(char **st)
{
  char *s, *v = *st;
  int trans;
  long c;
  if (isdigit((int)*v))
    { c = atol(v); trans = 1; } /* color on transparent background */
  else
  {
    if (*v == '[')
    {
      const char *a[3];
      long i = 0;
      for (a[0] = s = ++v; *s && *s != ']'; s++)
        if (*s == ',') { *s = 0; a[++i] = s+1; }
      if (*s != ']') pari_err(e_SYNTAX,"expected character: ']'",s, *st);
      *s = 0; for (i++; i<3; i++) a[i] = "";
      /*    properties    |   color    | background */
      c = (atoi(a[2])<<8) | atoi(a[0]) | (atoi(a[1])<<4);
      trans = (*(a[1]) == 0);
      v = s + 1;
    }
    else { c = c_NONE; trans = 0; }
  }
  if (trans) c = c | (1L<<12);
  while (*v && *v++ != ',') /* empty */;
  if (c != c_NONE) disable_color = 0;
  *st = v; return c;
}

/* 1: error, 2: history, 3: prompt, 4: input, 5: output, 6: help, 7: timer */
GEN
sd_colors(const char *v, long flag)
{
  long c,l;
  if (v && !(GP_DATA->flags & (gpd_EMACS|gpd_TEXMACS)))
  {
    char *v0, *s;
    disable_color=1;
    l = strlen(v);
    if (l <= 2 && strncmp(v, "no", l) == 0)
      v = "";
    if (l <= 6 && strncmp(v, "darkbg", l) == 0)
      v = "1, 5, 3, 7, 6, 2, 3"; /* Assume recent ReadLine. */
    if (l <= 7 && strncmp(v, "lightbg", l) == 0)
      v = "1, 6, 3, 4, 5, 2, 3"; /* Assume recent ReadLine. */
    if (l <= 8 && strncmp(v, "brightfg", l) == 0)      /* Good for windows consoles */
      v = "9, 13, 11, 15, 14, 10, 11";
    if (l <= 6 && strncmp(v, "boldfg", l) == 0)        /* Good for darkbg consoles */
      v = "[1,,1], [5,,1], [3,,1], [7,,1], [6,,1], , [2,,1]";
    v0 = s = gp_filter(v);
    for (c=c_ERR; c < c_LAST; c++)
      gp_colors[c] = gp_get_color(&s);
    pari_free(v0);
  }
  if (flag == d_ACKNOWLEDGE || flag == d_RETURN)
  {
    char s[128], *t = s;
    long col[3], n;
    for (*t=0,c=c_ERR; c < c_LAST; c++)
    {
      n = gp_colors[c];
      if (n == c_NONE)
        sprintf(t,"no");
      else
      {
        decode_color(n,col);
        if (n & (1L<<12))
        {
          if (col[0])
            sprintf(t,"[%ld,,%ld]",col[1],col[0]);
          else
            sprintf(t,"%ld",col[1]);
        }
        else
          sprintf(t,"[%ld,%ld,%ld]",col[1],col[2],col[0]);
      }
      t += strlen(t);
      if (c < c_LAST - 1) { *t++=','; *t++=' '; }
    }
    if (flag==d_RETURN) return strtoGENstr(s);
    pari_printf("   colors = \"%s\"\n",s);
  }
  return gnil;
}

GEN
sd_format(const char *v, long flag)
{
  pariout_t *fmt = GP_DATA->fmt;
  if (v)
  {
    char c = *v;
    if (c!='e' && c!='f' && c!='g')
      pari_err(e_SYNTAX,"default: inexistent format",v,v);
    fmt->format = c; v++;

    if (isdigit((int)*v))
      { while (isdigit((int)*v)) v++; } /* FIXME: skip obsolete field width */
    if (*v++ == '.')
    {
      if (*v == '-') fmt->sigd = -1;
      else
        if (isdigit((int)*v)) fmt->sigd=atol(v);
    }
  }
  if (flag == d_RETURN)
  {
    char *s = stack_malloc(64);
    (void)sprintf(s, "%c.%ld", fmt->format, fmt->sigd);
    return strtoGENstr(s);
  }
  if (flag == d_ACKNOWLEDGE)
    pari_printf("   format = %c.%ld\n", fmt->format, fmt->sigd);
  return gnil;
}

GEN
sd_compatible(const char *v, long flag)
{
  const char *msg[] = {
    "(no backward compatibility)",
    "(no backward compatibility)",
    "(no backward compatibility)",
    "(no backward compatibility)", NULL
  };
  ulong junk = 0;
  return sd_ulong(v,flag,"compatible",&junk, 0,3,msg);
}

GEN
sd_secure(const char *v, long flag)
{
  if (v && GP_DATA->secure)
    pari_ask_confirm("[secure mode]: About to modify the 'secure' flag");
  return sd_toggle(v,flag,"secure", &(GP_DATA->secure));
}

GEN
sd_debug(const char *v, long flag)
{ return sd_ulong(v,flag,"debug",&DEBUGLEVEL, 0,20,NULL); }

GEN
sd_debugfiles(const char *v, long flag)
{ return sd_ulong(v,flag,"debugfiles",&DEBUGFILES, 0,20,NULL); }

GEN
sd_debugmem(const char *v, long flag)
{ return sd_ulong(v,flag,"debugmem",&DEBUGMEM, 0,20,NULL); }

/* set D->hist to size = s / total = t */
static void
init_hist(gp_data *D, size_t s, ulong t)
{
  gp_hist *H = D->hist;
  H->total = t;
  H->size = s;
  H->v = (gp_hist_cell*)pari_calloc(s * sizeof(gp_hist_cell));
}
GEN
sd_histsize(const char *s, long flag)
{
  gp_hist *H = GP_DATA->hist;
  ulong n = H->size;
  GEN r = sd_ulong(s,flag,"histsize",&n, 1,
                     (LONG_MAX / sizeof(long)) - 1,NULL);
  if (n != H->size)
  {
    const ulong total = H->total;
    long g, h, k, kmin;
    gp_hist_cell *v = H->v, *w; /* v = old data, w = new one */
    size_t sv = H->size, sw;

    init_hist(GP_DATA, n, total);
    if (!total) return r;

    w = H->v;
    sw= H->size;
    /* copy relevant history entries */
    g     = (total-1) % sv;
    h = k = (total-1) % sw;
    kmin = k - minss(sw, sv);
    for ( ; k > kmin; k--, g--, h--)
    {
      w[h]   = v[g];
      v[g].z = NULL;
      if (!g) g = sv;
      if (!h) h = sw;
    }
    /* clean up */
    for ( ; v[g].z; g--)
    {
      gunclone(v[g].z);
      if (!g) g = sv;
    }
    pari_free((void*)v);
  }
  return r;
}

static void
TeX_define(const char *s, const char *def) {
  fprintf(pari_logfile, "\\ifx\\%s\\undefined\n  \\def\\%s{%s}\\fi\n", s,s,def);
}
static void
TeX_define2(const char *s, const char *def) {
  fprintf(pari_logfile, "\\ifx\\%s\\undefined\n  \\def\\%s#1#2{%s}\\fi\n", s,s,def);
}

static FILE *
open_logfile(const char *s) {
  FILE *log = fopen(s, "a");
  if (!log) pari_err_FILE("logfile",s);
  setbuf(log,(char *)NULL);
  return log;
}

GEN
sd_log(const char *v, long flag)
{
  const char *msg[] = {
      "(off)",
      "(on)",
      "(on with colors)",
      "(TeX output)", NULL
  };
  ulong s = logstyle;
  GEN res = sd_ulong(v,flag,"log", &s, 0, 3, msg);

  if (!s != !logstyle) /* Compare converts to boolean */
  { /* toggled LOG */
    if (logstyle)
    { /* close log */
      if (flag == d_ACKNOWLEDGE)
        pari_printf("   [logfile was \"%s\"]\n", current_logfile);
      if (pari_logfile) /* paranoia */
      {
        fclose(pari_logfile);
        pari_logfile = NULL;
      }
    }
    else
      pari_logfile = open_logfile(current_logfile);
  }
  if (pari_logfile && s != logstyle && s == logstyle_TeX)
  {
    TeX_define("PARIbreak",
               "\\hskip 0pt plus \\hsize\\relax\\discretionary{}{}{}");
    TeX_define("PARIpromptSTART", "\\vskip\\medskipamount\\bgroup\\bf");
    TeX_define("PARIpromptEND", "\\egroup\\bgroup\\tt");
    TeX_define("PARIinputEND", "\\egroup");
    TeX_define2("PARIout",
                "\\vskip\\smallskipamount$\\displaystyle{\\tt\\%#1} = #2$");
  }
  /* don't record new value until we are sure everything is fine */
  logstyle = s; return res;
}

GEN
sd_TeXstyle(const char *v, long flag)
{
  const char *msg[] = { "(bits 0x2/0x4 control output of \\left/\\PARIbreak)",
                        NULL };
  ulong n = GP_DATA->fmt->TeXstyle;
  GEN z = sd_ulong(v,flag,"TeXstyle", &n, 0, 7, msg);
  GP_DATA->fmt->TeXstyle = n; return z;
}

GEN
sd_nbthreads(const char *v, long flag)
{ return sd_ulong(v,flag,"nbthreads",&pari_mt_nbthreads, 1,LONG_MAX,NULL); }

GEN
sd_output(const char *v, long flag)
{
  const char *msg[] = {"(raw)", "(prettymatrix)", "(prettyprint)",
                 "(external prettyprint)", NULL};
  ulong n = GP_DATA->fmt->prettyp;
  GEN z = sd_ulong(v,flag,"output", &n, 0,3,msg);
  GP_DATA->fmt->prettyp = n;
  GP_DATA->fmt->sp = (n != f_RAW);
  return z;
}

GEN
sd_parisizemax(const char *v, long flag)
{
  ulong size = pari_mainstack->vsize, n = size;
  GEN r = sd_ulong(v,flag,"parisizemax",&n, 0,LONG_MAX,NULL);
  if (n != size) {
    if (flag == d_INITRC)
      paristack_setsize(pari_mainstack->rsize, n);
    else
      parivstack_resize(n);
  }
  return r;
}

GEN
sd_parisize(const char *v, long flag)
{
  ulong rsize = pari_mainstack->rsize, n = rsize;
  GEN r = sd_ulong(v,flag,"parisize",&n, 10000,LONG_MAX,NULL);
  if (n != rsize) {
    if (flag == d_INITRC)
      paristack_setsize(n, pari_mainstack->vsize);
    else
      paristack_newrsize(n);
  }
  return r;
}

GEN
sd_threadsizemax(const char *v, long flag)
{
  ulong size = GP_DATA->threadsizemax, n = size;
  GEN r = sd_ulong(v,flag,"threadsizemax",&n, 0,LONG_MAX,NULL);
  if (n != size)
    GP_DATA->threadsizemax = n;
  return r;
}

GEN
sd_threadsize(const char *v, long flag)
{
  ulong size = GP_DATA->threadsize, n = size;
  GEN r = sd_ulong(v,flag,"threadsize",&n, 0,LONG_MAX,NULL);
  if (n != size)
    GP_DATA->threadsize = n;
  return r;
}

GEN
sd_primelimit(const char *v, long flag)
{ return sd_ulong(v,flag,"primelimit",&(GP_DATA->primelimit),
                  0,2*(ulong)(LONG_MAX-1024) + 1,NULL); }

GEN
sd_simplify(const char *v, long flag)
{ return sd_toggle(v,flag,"simplify", &(GP_DATA->simplify)); }

GEN
sd_strictmatch(const char *v, long flag)
{ return sd_toggle(v,flag,"strictmatch", &(GP_DATA->strictmatch)); }

GEN
sd_strictargs(const char *v, long flag)
{ return sd_toggle(v,flag,"strictargs", &(GP_DATA->strictargs)); }

GEN
sd_string(const char *v, long flag, const char *s, char **pstr)
{
  char *old = *pstr;
  if (v)
  {
    char *str, *ev = path_expand(v);
    long l = strlen(ev) + 256;
    str = (char *) pari_malloc(l);
    strftime_expand(ev,str, l-1); pari_free(ev);
    if (GP_DATA->secure)
    {
      char *msg=pari_sprintf("[secure mode]: About to change %s to '%s'",s,str);
      pari_ask_confirm(msg);
      pari_free(msg);
    }
    if (old) pari_free(old);
    *pstr = old = pari_strdup(str);
    pari_free(str);
  }
  else if (!old) old = (char*)"<undefined>";
  if (flag == d_RETURN) return strtoGENstr(old);
  if (flag == d_ACKNOWLEDGE) pari_printf("   %s = \"%s\"\n",s,old);
  return gnil;
}

GEN
sd_logfile(const char *v, long flag)
{
  GEN r = sd_string(v, flag, "logfile", &current_logfile);
  if (v && pari_logfile)
  {
    FILE *log = open_logfile(current_logfile);
    fclose(pari_logfile); pari_logfile = log;
  }
  return r;
}

GEN
sd_factor_add_primes(const char *v, long flag)
{ return sd_toggle(v,flag,"factor_add_primes", &factor_add_primes); }

GEN
sd_factor_proven(const char *v, long flag)
{ return sd_toggle(v,flag,"factor_proven", &factor_proven); }

GEN
sd_new_galois_format(const char *v, long flag)
{ return sd_toggle(v,flag,"new_galois_format", &new_galois_format); }

GEN
sd_datadir(const char *v, long flag)
{
  const char *str;
  if (v)
  {
    if (pari_datadir) pari_free(pari_datadir);
    pari_datadir = path_expand(v);
  }
  str = pari_datadir? pari_datadir: "none";
  if (flag == d_RETURN) return strtoGENstr(str);
  if (flag == d_ACKNOWLEDGE)
    pari_printf("   datadir = \"%s\"\n", str);
  return gnil;
}

static GEN
sd_PATH(const char *v, long flag, const char* s, gp_path *p)
{
  if (v)
  {
    pari_free((void*)p->PATH);
    p->PATH = pari_strdup(v);
    if (flag == d_INITRC) return gnil;
    expand_path(p);
  }
  if (flag == d_RETURN) return strtoGENstr(p->PATH);
  if (flag == d_ACKNOWLEDGE)
    pari_printf("   %s = \"%s\"\n", s, p->PATH);
  return gnil;
}
GEN
sd_path(const char *v, long flag)
{ return sd_PATH(v, flag, "path", GP_DATA->path); }
GEN
sd_sopath(char *v, int flag)
{ return sd_PATH(v, flag, "sopath", GP_DATA->sopath); }

static const char *DFT_PRETTYPRINTER = "tex2mail -TeX -noindent -ragged -by_par";
GEN
sd_prettyprinter(const char *v, long flag)
{
  gp_pp *pp = GP_DATA->pp;
  if (v && !(GP_DATA->flags & gpd_TEXMACS))
  {
    char *old = pp->cmd;
    int cancel = (!strcmp(v,"no"));

    if (GP_DATA->secure)
      pari_err(e_MISC,"[secure mode]: can't modify 'prettyprinter' default (to %s)",v);
    if (!strcmp(v,"yes")) v = DFT_PRETTYPRINTER;
    if (old && strcmp(old,v) && pp->file)
    {
      pariFILE *f;
      if (cancel) f = NULL;
      else
      {
        f = try_pipe(v, mf_OUT);
        if (!f)
        {
          pari_warn(warner,"broken prettyprinter: '%s'",v);
          return gnil;
        }
      }
      pari_fclose(pp->file);
      pp->file = f;
    }
    pp->cmd = cancel? NULL: pari_strdup(v);
    if (old) pari_free(old);
    if (flag == d_INITRC) return gnil;
  }
  if (flag == d_RETURN)
    return strtoGENstr(pp->cmd? pp->cmd: "");
  if (flag == d_ACKNOWLEDGE)
    pari_printf("   prettyprinter = \"%s\"\n",pp->cmd? pp->cmd: "");
  return gnil;
}

/* compare entrees s1 s2 according to the attached function name */
static int
compare_name(const void *s1, const void *s2) {
  entree *e1 = *(entree**)s1, *e2 = *(entree**)s2;
  return strcmp(e1->name, e2->name);
}
static void
defaults_list(pari_stack *s)
{
  entree *ep;
  long i;
  for (i = 0; i < functions_tblsz; i++)
    for (ep = defaults_hash[i]; ep; ep = ep->next) pari_stack_pushp(s, ep);
}
/* ep attached to function f of arity 2. Call f(v,flag) */
static GEN
call_f2(entree *ep, const char *v, long flag)
{ return ((GEN (*)(const char*,long))ep->value)(v, flag); }
GEN
setdefault(const char *s, const char *v, long flag)
{
  entree *ep;
  if (!s)
  { /* list all defaults */
    pari_stack st;
    entree **L;
    long i;
    pari_stack_init(&st, sizeof(*L), (void**)&L);
    defaults_list(&st);
    qsort (L, st.n, sizeof(*L), compare_name);
    for (i = 0; i < st.n; i++) (void)call_f2(L[i], NULL, d_ACKNOWLEDGE);
    pari_stack_delete(&st);
    return gnil;
  }
  ep = pari_is_default(s);
  if (!ep)
  {
    pari_err(e_MISC,"unknown default: %s",s);
    return NULL; /* LCOV_EXCL_LINE */
  }
  return call_f2(ep, v, flag);
}

GEN
default0(const char *a, const char *b) { return setdefault(a,b, b? d_SILENT: d_RETURN); }

/********************************************************************/
/*                                                                  */
/*                     INITIALIZE GP_DATA                           */
/*                                                                  */
/********************************************************************/
/* initialize path */
static void
init_path(gp_path *path, const char *v)
{
  path->PATH = pari_strdup(v);
  path->dirs = NULL;
}

/* initialize D->fmt */
static void
init_fmt(gp_data *D)
{
#ifdef LONG_IS_64BIT
  static pariout_t DFLT_OUTPUT = { 'g', 38, 1, f_PRETTYMAT, 0 };
#else
  static pariout_t DFLT_OUTPUT = { 'g', 28, 1, f_PRETTYMAT, 0 };
#endif
  D->fmt = &DFLT_OUTPUT;
}

/* initialize D->pp */
static void
init_pp(gp_data *D)
{
  gp_pp *p = D->pp;
  p->cmd = pari_strdup(DFT_PRETTYPRINTER);
  p->file = NULL;
}

static char *
init_help(void)
{
  char *h = os_getenv("GPHELP");
  if (!h) h = (char*)paricfg_gphelp;
#ifdef _WIN32
  win32_set_pdf_viewer();
#endif
  if (h) h = pari_strdup(h);
  return h;
}

static void
init_graphs(gp_data *D)
{
  const char *cols[] = { "",
    "white","black","blue","violetred","red","green","grey","gainsboro"
  };
  const long N = 8;
  GEN c = cgetalloc(t_VECSMALL, 3), s;
  long i;
  c[1] = 4;
  c[2] = 5;
  D->graphcolors = c;
  c = (GEN)pari_malloc((N+1 + 4*N)*sizeof(long));
  c[0] = evaltyp(t_VEC)|evallg(N+1);
  for (i = 1, s = c+N+1; i <= N; i++, s += 4)
  {
    GEN lp = s;
    lp[0] = evaltyp(t_STR)|evallg(4);
    strcpy(GSTR(lp), cols[i]);
    gel(c,i) = lp;
  }
  D->colormap = c;
}

gp_data *
default_gp_data(void)
{
  static gp_data __GPDATA, *D = &__GPDATA;
  static gp_hist __HIST;
  static gp_pp   __PP;
  static gp_path __PATH, __SOPATH;
  static pari_timer __T;

  D->flags       = 0;
  D->primelimit  = 500000;

  /* GP-specific */
  D->breakloop   = 1;
  D->echo        = 0;
  D->lim_lines   = 0;
  D->linewrap    = 0;
  D->recover     = 1;
  D->chrono      = 0;

  D->strictargs  = 0;
  D->strictmatch = 1;
  D->simplify    = 1;
  D->secure      = 0;
  D->use_readline= 0;
  D->T    = &__T;
  D->hist = &__HIST;
  D->pp   = &__PP;
  D->path = &__PATH;
  D->sopath=&__SOPATH;
  init_fmt(D);
  init_hist(D, 5000, 0);
  init_path(D->path, pari_default_path());
  init_path(D->sopath, "");
  init_pp(D);
  init_graphs(D);
  D->plothsizes = cgetalloc(t_VECSMALL, 1);
  D->prompt_comment = (char*)"comment> ";
  D->prompt = pari_strdup("? ");
  D->prompt_cont = pari_strdup("");
  D->help = init_help();
  D->readline_state = DO_ARGS_COMPLETE;
  D->histfile = NULL;
  return D;
}
