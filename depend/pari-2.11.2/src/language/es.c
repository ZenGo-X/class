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
/**                                                               **/
/**                 INPUT/OUTPUT SUBROUTINES                      **/
/**                                                               **/
/*******************************************************************/
#ifdef _WIN32
#include "../systems/mingw/pwinver.h"
#include <windows.h>
#include <process.h> /* for getpid */
#include <fcntl.h>
#include <io.h>      /* for setmode */
#include "../systems/mingw/mingw.h"
#endif
#include "paricfg.h"
#ifdef HAS_STAT
#include <sys/stat.h>
#endif
#ifdef HAS_OPENDIR
#include <dirent.h>
#endif

#include "pari.h"
#include "paripriv.h"
#include "anal.h"
#ifdef __EMSCRIPTEN__
#include "../systems/emscripten/emscripten.h"
#endif

typedef void (*OUT_FUN)(GEN, pariout_t *, pari_str *);

static void bruti_sign(GEN g, pariout_t *T, pari_str *S, int addsign);
static void matbruti(GEN g, pariout_t *T, pari_str *S);
static void texi_sign(GEN g, pariout_t *T, pari_str *S, int addsign);

static void bruti(GEN g, pariout_t *T, pari_str *S)
{ bruti_sign(g,T,S,1); }
static void texi(GEN g, pariout_t *T, pari_str *S)
{ texi_sign(g,T,S,1); }

void
pari_ask_confirm(const char *s)
{
  if (!cb_pari_ask_confirm)
    pari_err(e_MISC,"Can't ask for confirmation. Please define cb_pari_ask_confirm()");
  cb_pari_ask_confirm(s);
}

static char *
strip_last_nl(char *s)
{
  ulong l = strlen(s);
  char *t;
  if (l && s[l-1] != '\n') return s;
  if (l>1 && s[l-2] == '\r') l--;
  t = stack_malloc(l); memcpy(t, s, l-1); t[l-1] = 0;
  return t;
}

/********************************************************************/
/**                                                                **/
/**                        INPUT FILTER                            **/
/**                                                                **/
/********************************************************************/
#define ONE_LINE_COMMENT   2
#define MULTI_LINE_COMMENT 1
#define LBRACE '{'
#define RBRACE '}'

static int
in_help(filtre_t *F)
{
  char c;
  if (!F->buf) return (*F->s == '?');
  c = *F->buf->buf;
  return c? (c == '?'): (*F->s == '?');
}
/* Filter F->s into F->t */
static char *
filtre0(filtre_t *F)
{
  const char *s = F->s;
  char *t;
  char c;

  if (!F->t) F->t = (char*)pari_malloc(strlen(s)+1);
  t = F->t;

  if (F->more_input == 1) F->more_input = 0;
  while ((c = *s++))
  {
    if (F->in_string)
    {
      *t++ = c; /* copy verbatim */
      switch(c)
      {
        case '\\': /* in strings, \ is the escape character */
          if (*s) *t++ = *s++;
          break;

        case '"': F->in_string = 0;
      }
      continue;
    }

    if (F->in_comment)
    { /* look for comment's end */
      if (F->in_comment == MULTI_LINE_COMMENT)
      {
        while (c != '*' || *s != '/')
        {
          if (!*s)
          {
            if (!F->more_input) F->more_input = 1;
            goto END;
          }
          c = *s++;
        }
        s++;
      }
      else
        while (c != '\n' && *s) c = *s++;
      F->in_comment = 0;
      continue;
    }

    /* weed out comments and spaces */
    if (c=='\\' && *s=='\\') { F->in_comment = ONE_LINE_COMMENT; continue; }
    if (isspace((int)c)) continue;
    *t++ = c;
    switch(c)
    {
      case '/':
        if (*s == '*') { t--; F->in_comment = MULTI_LINE_COMMENT; }
        break;

      case '\\':
        if (!*s) {
          if (in_help(F)) break; /* '?...\' */
          t--;
          if (!F->more_input) F->more_input = 1;
          goto END;
        }
        if (*s == '\r') s++; /* DOS */
        if (*s == '\n') {
          if (in_help(F)) break; /* '?...\' */
          t--; s++;
          if (!*s)
          {
            if (!F->more_input) F->more_input = 1;
            goto END;
          }
        } /* skip \<CR> */
        break;

      case '"': F->in_string = 1;
        break;

      case LBRACE:
        t--;
        if (F->wait_for_brace) pari_err_IMPL("embedded braces (in parser)");
        F->more_input = 2;
        F->wait_for_brace = 1;
        break;

      case RBRACE:
        if (!F->wait_for_brace) pari_err(e_MISC,"unexpected closing brace");
        F->more_input = 0; t--;
        F->wait_for_brace = 0;
        break;
    }
  }

  if (t != F->t) /* non empty input */
  {
    c = t[-1]; /* last char */
    if (c == '=') { if (!in_help(F)) F->more_input = 2; }
    else if (! F->wait_for_brace) F->more_input = 0;
    else if (c == RBRACE)       { F->more_input = 0; t--; F->wait_for_brace--;}
  }

END:
  F->end = t; *t = 0; return F->t;
}
#undef ONE_LINE_COMMENT
#undef MULTI_LINE_COMMENT

char *
gp_filter(const char *s)
{
  filtre_t T;
  T.buf = NULL;
  T.s = s;    T.in_string = 0; T.more_input = 0;
  T.t = NULL; T.in_comment= 0; T.wait_for_brace = 0;
  return filtre0(&T);
}

void
init_filtre(filtre_t *F, Buffer *buf)
{
  F->buf = buf;
  F->in_string  = 0;
  F->in_comment = 0;
}

/********************************************************************/
/**                                                                **/
/**                        INPUT METHODS                           **/
/**                                                                **/
/********************************************************************/
/* create */
Buffer *
new_buffer(void)
{
  Buffer *b = (Buffer*) pari_malloc(sizeof(Buffer));
  b->len = 1024;
  b->buf = (char*)pari_malloc(b->len);
  return b;
}
/* delete */
void
delete_buffer(Buffer *b)
{
  if (!b) return;
  pari_free((void*)b->buf); pari_free((void*)b);
}
/* resize */
void
fix_buffer(Buffer *b, long newlbuf)
{
  b->len = newlbuf;
  b->buf = (char*)pari_realloc((void*)b->buf, b->len);
}

static int
gp_read_stream_buf(FILE *fi, Buffer *b)
{
  input_method IM;
  filtre_t F;

  init_filtre(&F, b);

  IM.file = (void*)fi;
  IM.fgets = (fgets_t)&fgets;
  IM.getline = &file_input;
  IM.free = 0;
  return input_loop(&F,&IM);
}

GEN
gp_read_stream(FILE *fi)
{
  Buffer *b = new_buffer();
  GEN x = gp_read_stream_buf(fi, b)? readseq(b->buf): gnil;
  delete_buffer(b); return x;
}

static GEN
gp_read_from_input(input_method* IM, int loop, char *last)
{
  Buffer *b = new_buffer();
  GEN x = gnil;
  filtre_t F;
  if (last) *last = 0;
  do {
    char *s;
    init_filtre(&F, b);
    if (!input_loop(&F, IM)) break;
    s = b->buf;
    if (s[0])
    {
      x = readseq(s);
      if (last) *last = s[strlen(s) - 1];
    }
  } while (loop);
  delete_buffer(b);
  return x;
}

GEN
gp_read_file(const char *s)
{
  GEN x = gnil;
  FILE *f = switchin(s);
  if (file_is_binary(f))
  {
    x = readbin(s,f, NULL);
    if (!x) pari_err_FILE("input file",s);
  }
  else {
    pari_sp av = avma;
    Buffer *b = new_buffer();
    x = gnil;
    for (;;) {
      if (!gp_read_stream_buf(f, b)) break;
      if (*(b->buf)) { avma = av; x = readseq(b->buf); }
    }
    delete_buffer(b);
  }
  popinfile(); return x;
}

static char*
string_gets(char *s, int size, const char **ptr)
{
  /* f is actually a const char** */
  const char *in = *ptr;
  int i;
  char c;

  /* Copy from in to s */
  for (i = 0; i+1 < size && in[i] != 0;)
  {
    s[i] = c = in[i]; i++;
    if (c == '\n') break;
  }
  s[i] = 0;  /* Terminating 0 byte */
  if (i == 0) return NULL;

  *ptr += i;
  return s;
}

GEN
gp_read_str_multiline(const char *s, char *last)
{
  input_method IM;
  const char *ptr = s;

  IM.file = (void*)(&ptr);
  IM.fgets = (fgets_t)&string_gets;
  IM.getline = &file_input;
  IM.free = 0;

  return gp_read_from_input(&IM, 1, last);
}

void
gp_embedded_init(long rsize, long vsize)
{
  pari_init(rsize, 500000);
  paristack_setsize(rsize, vsize);
}

char *
gp_embedded(const char *s)
{
  char last, *res;
  struct gp_context state;
  VOLATILE long t = 0;
  gp_context_save(&state);
  timer_start(GP_DATA->T);
  pari_set_last_newline(1);
  pari_CATCH(CATCH_ALL)
  {
    GENbin* err = copy_bin(pari_err_last());
    gp_context_restore(&state);
    res = pari_err2str(bin_copy(err));
  } pari_TRY {
    GEN z = gp_read_str_multiline(s, &last);
    ulong n;
    t = timer_delay(GP_DATA->T);
    if (GP_DATA->simplify) z = simplify_shallow(z);
    pari_add_hist(z, t);
    n = pari_nb_hist();
    parivstack_reset();
    res = (z==gnil || last==';') ? stack_strdup("\n"):
          stack_sprintf("%%%lu = %Ps\n", n, pari_get_hist(n));
    if (t && GP_DATA->chrono)
      res = stack_sprintf("%stime = %s", res, gp_format_time(t));
  } pari_ENDCATCH;
  if (!pari_last_was_newline()) pari_putc('\n');
  avma = pari_mainstack->top;
  return res;
}

GEN
gp_readvec_stream(FILE *fi)
{
  pari_sp ltop = avma;
  Buffer *b = new_buffer();
  long i = 1, n = 16;
  GEN z = cgetg(n+1,t_VEC);
  for(;;)
  {
    if (!gp_read_stream_buf(fi, b)) break;
    if (!*(b->buf)) continue;
    if (i>n)
    {
      if (DEBUGLEVEL) err_printf("gp_readvec_stream: reaching %ld entries\n",n);
      n <<= 1;
      z = vec_lengthen(z,n);
    }
    gel(z,i++) = readseq(b->buf);
  }
  if (DEBUGLEVEL) err_printf("gp_readvec_stream: found %ld entries\n",i-1);
  setlg(z,i); delete_buffer(b);
  return gerepilecopy(ltop,z);
}

GEN
gp_readvec_file(char *s)
{
  GEN x = NULL;
  FILE *f = switchin(s);
  if (file_is_binary(f)) {
    int junk;
    x = readbin(s,f,&junk);
    if (!x) pari_err_FILE("input file",s);
  } else
    x = gp_readvec_stream(f);
  popinfile(); return x;
}

char *
file_getline(Buffer *b, char **s0, input_method *IM)
{
  const ulong MAX = (1UL << 31) - 1;
  ulong used0, used;

  **s0 = 0; /* paranoia */
  used0 = used = *s0 - b->buf;
  for(;;)
  {
    ulong left = b->len - used, l, read;
    char *s;

    /* If little space left, double the buffer size before next read. */
    if (left < 512)
    {
      fix_buffer(b, b->len << 1);
      left = b->len - used;
      *s0 = b->buf + used0;
    }
    /* # of chars read by fgets is an int; be careful */
    read = minuu(left, MAX);
    s = b->buf + used;
    if (! IM->fgets(s, (int)read, IM->file)) return **s0? *s0: NULL; /* EOF */

    l = strlen(s);
    if (l+1 < read || s[l-1] == '\n') return *s0; /* \n */
    used += l;
  }
}

/* Read from file (up to '\n' or EOF) and copy at s0 (points in b->buf) */
char *
file_input(char **s0, int junk, input_method *IM, filtre_t *F)
{
  (void)junk;
  return file_getline(F->buf, s0, IM);
}

/* Read a "complete line" and filter it. Return: 0 if EOF, 1 otherwise */
int
input_loop(filtre_t *F, input_method *IM)
{
  Buffer *b = (Buffer*)F->buf;
  char *to_read, *s = b->buf;

  /* read first line */
  if (! (to_read = IM->getline(&s,1, IM, F)) )
  {
    if (F->in_string)
    {
      pari_warn(warner,"run-away string. Closing it");
      F->in_string = 0;
    }
    if (F->in_comment)
    {
      pari_warn(warner,"run-away comment. Closing it");
      F->in_comment = 0;
    }
    return 0;
  }

  /* buffer is not empty, init filter */
  F->in_string = 0;
  F->more_input= 0;
  F->wait_for_brace = 0;
  for(;;)
  {
    if (GP_DATA->echo == 2) gp_echo_and_log("", strip_last_nl(to_read));
    F->s = to_read;
    F->t = s;
    (void)filtre0(F); /* pre-processing of line, read by previous call to IM->getline */
    if (IM->free) pari_free(to_read);
    if (! F->more_input) break;

    /* read continuation line */
    s = F->end;
    to_read = IM->getline(&s,0, IM, F);
    if (!to_read) break;
  }
  return 1;
}

/********************************************************************/
/**                                                                **/
/**                  GENERAL PURPOSE PRINTING                      **/
/**                                                                **/
/********************************************************************/
PariOUT *pariOut, *pariErr;
static void
_fputs(const char *s, FILE *f ) {
#ifdef _WIN32
   win32_ansi_fputs(s, f);
#else
  fputs(s, f);
#endif
}
static void
_putc_log(char c) { if (pari_logfile) (void)putc(c, pari_logfile); }
static void
_puts_log(const char *s)
{
  FILE *f = pari_logfile;
  const char *p;
  if (!f) return;
  if (logstyle != logstyle_color)
    while ( (p = strchr(s, '\x1b')) )
    { /* skip ANSI color escape sequence */
      if ( p!=s ) fwrite(s, 1, p-s, f);
      s = strchr(p, 'm');
      if (!s) return;
      s++;
    }
  fputs(s, f);
}
static void
_flush_log(void)
{ if (pari_logfile != NULL) (void)fflush(pari_logfile); }

static void
normalOutC(char c) { putc(c, pari_outfile); _putc_log(c); }
static void
normalOutS(const char *s) { _fputs(s, pari_outfile); _puts_log(s); }
static void
normalOutF(void) { fflush(pari_outfile); _flush_log(); }
static PariOUT defaultOut = {normalOutC, normalOutS, normalOutF};

static void
normalErrC(char c) { putc(c, pari_errfile); _putc_log(c); }
static void
normalErrS(const char *s) { _fputs(s, pari_errfile); _puts_log(s); }
static void
normalErrF(void) { fflush(pari_errfile); _flush_log(); }
static PariOUT defaultErr = {normalErrC, normalErrS, normalErrF};

/**                         GENERIC PRINTING                       **/
void
resetout(int initerr)
{
  pariOut = &defaultOut;
  if (initerr) pariErr = &defaultErr;
}
void
initout(int initerr)
{
  pari_infile = stdin;
  pari_outfile = stdout;
  pari_errfile = stderr;
  resetout(initerr);
}

static int last_was_newline = 1;

static void
set_last_newline(char c) { last_was_newline = (c == '\n'); }

void
out_putc(PariOUT *out, char c) { set_last_newline(c); out->putch(c); }
void
pari_putc(char c) { out_putc(pariOut, c); }

void
out_puts(PariOUT *out, const char *s) {
  if (*s) { set_last_newline(s[strlen(s)-1]); out->puts(s); }
}
void
pari_puts(const char *s) { out_puts(pariOut, s); }

int
pari_last_was_newline(void) { return last_was_newline; }
void
pari_set_last_newline(int last) { last_was_newline = last; }

void
pari_flush(void) { pariOut->flush(); }

void
err_flush(void) { pariErr->flush(); }

static GEN
log10_2(void)
{ return divrr(mplog2(LOWDEFAULTPREC), mplog(utor(10,LOWDEFAULTPREC))); }

/* e binary exponent, return exponent in base ten */
static long
ex10(long e) {
  pari_sp av;
  GEN z;
  if (e >= 0) {
    if (e < 1e15) return (long)(e*LOG10_2);
    av = avma; z = mulur(e, log10_2());
    z = floorr(z); e = itos(z);
  }
  else /* e < 0 */
  {
    if (e > -1e15) return (long)(-(-e*LOG10_2)-1);
    av = avma; z = mulsr(e, log10_2());
    z = floorr(z); e = itos(z) - 1;
  }
  avma = av; return e;
}

static char *
zeros(char *b, long nb) { while (nb-- > 0) *b++ = '0'; *b = 0; return b; }

/* # of decimal digits, assume l > 0 */
static long
numdig(ulong l)
{
  if (l < 100000)
  {
    if (l < 100)    return (l < 10)? 1: 2;
    if (l < 10000)  return (l < 1000)? 3: 4;
    return 5;
  }
  if (l < 10000000)   return (l < 1000000)? 6: 7;
  if (l < 1000000000) return (l < 100000000)? 8: 9;
  return 10;
}

/* let ndig <= 9, x < 10^ndig, write in p[-ndig..-1] the decimal digits of x */
static void
utodec(char *p, ulong x, long ndig)
{
  switch(ndig)
  {
    case  9: *--p = x % 10 + '0'; x = x/10;
    case  8: *--p = x % 10 + '0'; x = x/10;
    case  7: *--p = x % 10 + '0'; x = x/10;
    case  6: *--p = x % 10 + '0'; x = x/10;
    case  5: *--p = x % 10 + '0'; x = x/10;
    case  4: *--p = x % 10 + '0'; x = x/10;
    case  3: *--p = x % 10 + '0'; x = x/10;
    case  2: *--p = x % 10 + '0'; x = x/10;
    case  1: *--p = x % 10 + '0'; x = x/10;
  }
}

/* convert abs(x) != 0 to str. Prepend '-' if (sx < 0) */
static char *
itostr_sign(GEN x, int sx, long *len)
{
  long l, d;
  ulong *res = convi(x, &l);
  /* l 9-digits words (< 10^9) + (optional) sign + \0 */
  char *s = (char*)new_chunk(nchar2nlong(l*9 + 1 + 1)), *t = s;

  if (sx < 0) *t++ = '-';
  d = numdig(*--res); t += d; utodec(t, *res, d);
  while (--l > 0) { t += 9; utodec(t, *--res, 9); }
  *t = 0; *len = t - s; return s;
}

/********************************************************************/
/**                                                                **/
/**                        WRITE A REAL NUMBER                     **/
/**                                                                **/
/********************************************************************/
/* 19 digits (if 64 bits, at most 2^60-1) + 1 sign */
static const long MAX_EXPO_LEN = 20;

/* write z to buf, inserting '.' at 'point', 0 < point < strlen(z) */
static void
wr_dec(char *buf, char *z, long point)
{
  char *s = buf + point;
  strncpy(buf, z, point); /* integer part */
  *s++ = '.'; z += point;
  while ( (*s++ = *z++) ) /* empty */;
}

static char *
zerotostr(void)
{
  char *s = (char*)new_chunk(1);
  s[0] = '0';
  s[1] = 0; return s;
}

/* write a real 0 of exponent ex in format f */
static char *
real0tostr_width_frac(long width_frac)
{
  char *buf, *s;
  if (width_frac == 0) return zerotostr();
  buf = s = stack_malloc(width_frac + 3);
  *s++ = '0';
  *s++ = '.';
  (void)zeros(s, width_frac);
  return buf;
}

/* write a real 0 of exponent ex */
static char *
real0tostr(long ex, char format, char exp_char, long wanted_dec)
{
  char *buf, *buf0;

  if (format == 'f') {
    long width_frac = wanted_dec;
    if (width_frac < 0) width_frac = (ex >= 0)? 0: (long)(-ex * LOG10_2);
    return real0tostr_width_frac(width_frac);
  } else {
    buf0 = buf = stack_malloc(3 + MAX_EXPO_LEN + 1);
    *buf++ = '0';
    *buf++ = '.';
    *buf++ = exp_char;
    sprintf(buf, "%ld", ex10(ex) + 1);
  }
  return buf0;
}

/* format f, width_frac >= 0: number of digits in fractional part, */
static char *
absrtostr_width_frac(GEN x, int width_frac)
{
  long beta, ls, point, lx, sx = signe(x);
  char *s, *buf;
  GEN z;

  if (!sx) return real0tostr_width_frac(width_frac);

  /* x != 0 */
  lx = realprec(x);
  beta = width_frac;
  if (beta) /* >= 0 */
  { /* z = |x| 10^beta, 10^b = 5^b * 2^b, 2^b goes into exponent */
    if (beta > 4e9) lx++;
    z = mulrr(x, rpowuu(5UL, (ulong)beta, lx+1));
    setsigne(z, 1);
    shiftr_inplace(z, beta);
  }
  else
    z = mpabs(x);
  z = roundr_safe(z);
  if (!signe(z)) return real0tostr_width_frac(width_frac);

  s = itostr_sign(z, 1, &ls); /* ls > 0, number of digits in s */
  point = ls - beta; /* position of . in s; <= ls, may be < 0 */
  if (point > 0) /* write integer_part.fractional_part */
  {
    /* '.', trailing \0 */
    buf = stack_malloc( ls + 1+1 );
    if (ls == point)
      strcpy(buf, s); /* no '.' */
    else
      wr_dec(buf, s, point);
  } else { /* point <= 0, fractional part must be written */
    char *t;
    /* '0', '.', zeroes, trailing \0 */
    buf = t = stack_malloc( 1 + 1 - point + ls + 1 );
    *t++ = '0';
    *t++ = '.';
    t = zeros(t, -point);
    strcpy(t, s);
  }
  return buf;
}

/* Return t_REAL |x| in floating point format.
 * Allocate freely, the caller must clean the stack.
 *   FORMAT: E/e (exponential), F/f (floating point), G/g
 *   wanted_dec: number of significant digits to print (all if < 0).
 */
static char *
absrtostr(GEN x, int sp, char FORMAT, long wanted_dec)
{
  const char format = (char)tolower((int)FORMAT), exp_char = (format == FORMAT)? 'e': 'E';
  long beta, ls, point, lx, sx = signe(x), ex = expo(x);
  char *s, *buf, *buf0;
  GEN z;

  if (!sx) return real0tostr(ex, format, exp_char, wanted_dec);

  /* x != 0 */
  lx = realprec(x);
  if (wanted_dec >= 0)
  { /* reduce precision if possible */
    long w = ndec2prec(wanted_dec); /* digits -> pari precision in words */
    if (lx > w) lx = w; /* truncature with guard, no rounding */
  }
  beta = ex10(prec2nbits(lx) - ex);
  if (beta)
  { /* z = |x| 10^beta, 10^b = 5^b * 2^b, 2^b goes into exponent */
    if (beta > 0)
    {
      if (beta > 18) { lx++; x = rtor(x, lx); }
      z = mulrr(x, rpowuu(5UL, (ulong)beta, lx+1));
    }
    else
    {
      if (beta < -18) { lx++; x = rtor(x, lx); }
      z = divrr(x, rpowuu(5UL, (ulong)-beta, lx+1));
    }
    setsigne(z, 1);
    shiftr_inplace(z, beta);
  }
  else
    z = x;
  z = roundr_safe(z);
  if (!signe(z)) return real0tostr(ex, format, exp_char, wanted_dec);

  s = itostr_sign(z, 1, &ls); /* ls > 0, number of digits in s */
  if (wanted_dec < 0)
    wanted_dec = ls;
  else if (ls > wanted_dec)
  {
    beta -= ls - wanted_dec;
    ls = wanted_dec;
    if (s[ls] >= '5') /* round up */
    {
      long i;
      for (i = ls-1; i >= 0; s[i--] = '0')
        if (++s[i] <= '9') break;
      if (i < 0) { s[0] = '1'; beta--; }
    }
    s[ls] = 0;
  }

  /* '.', " E", exponent, trailing \0 */
  point = ls - beta; /* position of . in s; < 0 or > 0 */
  if (beta <= 0 || format == 'e' || (format == 'g' && point-1 < -4))
  { /* e format */
    buf0 = buf = stack_malloc(ls+1+2+MAX_EXPO_LEN + 1);
    wr_dec(buf, s, 1); buf += ls + 1;
    if (sp) *buf++ = ' ';
    *buf++ = exp_char;
    sprintf(buf, "%ld", point-1);
  }
  else if (point > 0) /* f format, write integer_part.fractional_part */
  {
    buf0 = buf = stack_malloc(ls+1 + 1);
    wr_dec(buf, s, point); /* point < ls since beta > 0 */
  }
  else /* f format, point <= 0, write fractional part */
  {
    buf0 = buf = stack_malloc(2-point+ls + 1);
    *buf++ = '0';
    *buf++ = '.';
    buf = zeros(buf, -point);
    strcpy(buf, s);
  }
  return buf0;
}

/* vsnprintf implementation rewritten from snprintf.c to be found at
 *
 * http://www.nersc.gov/~scottc/misc/docs/snort-2.1.1-RC1/snprintf_8c-source.html
 * The original code was
 *   Copyright (C) 1998-2002 Martin Roesch <roesch@sourcefire.com>
 * available under the terms of the GNU GPL version 2 or later. It
 * was itself adapted from an original version by Patrick Powell. */

/* Modifications for format %Ps: R.Butel IMB/CNRS 2007/12/03 */

/* l = old len, L = new len */
static void
str_alloc0(pari_str *S, long l, long L)
{
  char *s;
  if (S->use_stack)
  {
    s = stack_malloc(L);
    memcpy(s, S->string, l);
  }
  else
    s = (char*)pari_realloc((void*)S->string, L);
  S->string = s;
  S->cur = s + l;
  S->end = s + L;
  S->size = L;
}
/* make sure S is large enough to write l further words (<= l * 20 chars).
 * To avoid automatic extension in between av = avma / avma = av pairs
 * [ would destroy S->string if (S->use_stack) ] */
static void
str_alloc(pari_str *S, long l)
{
  l *= 20;
  if (S->end - S->cur <= l)
    str_alloc0(S, S->cur - S->string, S->size + maxss(S->size, l));
}
void
str_putc(pari_str *S, char c)
{
  *S->cur++ = c;
  if (S->cur == S->end) str_alloc0(S, S->size, S->size << 1);
}

void
str_init(pari_str *S, int use_stack)
{
  char *s;
  S->size = 1024;
  S->use_stack = use_stack;
  if (S->use_stack)
    s = (char*)stack_malloc(S->size);
  else
    s = (char*)pari_malloc(S->size);
  *s = 0;
  S->string = S->cur = s;
  S->end = S->string + S->size;
}
void
str_puts(pari_str *S, const char *s) { while (*s) str_putc(S, *s++); }

static void
str_putscut(pari_str *S, const char *s, int cut)
{
  if (cut < 0) str_puts(S, s);
  else {
    while (*s && cut-- > 0) str_putc(S, *s++);
  }
}

/* lbuf = strlen(buf), len < 0: unset */
static void
outpad(pari_str *S, const char *buf, long lbuf, int sign, long ljust, long len, long zpad)
{
  long padlen = len - lbuf;
  if (padlen < 0) padlen = 0;
  if (ljust) padlen = -padlen;
  if (padlen > 0)
  {
    if (zpad) {
      if (sign) { str_putc(S, sign); --padlen; }
      while (padlen > 0) { str_putc(S, '0'); --padlen; }
    }
    else
    {
      if (sign) --padlen;
      while (padlen > 0) { str_putc(S, ' '); --padlen; }
      if (sign) str_putc(S, sign);
    }
  } else
    if (sign) str_putc(S, sign);
  str_puts(S, buf);
  while (padlen < 0) { str_putc(S, ' '); ++padlen; }
}

/* len < 0 or maxwidth < 0: unset */
static void
fmtstr(pari_str *S, const char *buf, int ljust, int len, int maxwidth)
{
  int padlen, lbuf = strlen(buf);

  if (maxwidth >= 0 && lbuf > maxwidth) lbuf = maxwidth;

  padlen = len - lbuf;
  if (padlen < 0) padlen = 0;
  if (ljust) padlen = -padlen;
  while (padlen > 0) { str_putc(S, ' '); --padlen; }
  str_putscut(S, buf, maxwidth);
  while (padlen < 0) { str_putc(S, ' '); ++padlen; }
}

/* abs(base) is 8, 10, 16. If base < 0, some "alternate" form
 * -- print hex in uppercase
 * -- prefix octal with 0
 * signvalue = -1: unsigned, otherwise ' ' or '+'. Leaves a messy stack if
 * S->use_stack */
static void
fmtnum(pari_str *S, long lvalue, GEN gvalue, int base, int signvalue,
       int ljust, int len, int zpad)
{
  int caps;
  char *buf0, *buf;
  long lbuf, mxl;
  GEN uvalue = NULL;
  ulong ulvalue = 0;
  pari_sp av = avma;

  if (gvalue)
  {
    long s, l;
    if (typ(gvalue) != t_INT) {
      long i, j, h;
      l = lg(gvalue);
      switch(typ(gvalue))
      {
        case t_VEC:
          str_putc(S, '[');
          for (i = 1; i < l; i++)
          {
            fmtnum(S, 0, gel(gvalue,i), base, signvalue, ljust,len,zpad);
            if (i < l-1) str_putc(S, ',');
          }
          str_putc(S, ']');
          return;
        case t_COL:
          str_putc(S, '[');
          for (i = 1; i < l; i++)
          {
            fmtnum(S, 0, gel(gvalue,i), base, signvalue, ljust,len,zpad);
            if (i < l-1) str_putc(S, ',');
          }
          str_putc(S, ']');
          str_putc(S, '~');
          return;
        case t_MAT:
          if (l == 1)
            str_puts(S, "[;]");
          else
          {
            h = lgcols(gvalue);
            for (i=1; i<h; i++)
            {
              str_putc(S, '[');
              for (j=1; j<l; j++)
              {
                fmtnum(S, 0, gcoeff(gvalue,i,j), base, signvalue, ljust,len,zpad);
                if (j<l-1) str_putc(S, ' ');
              }
              str_putc(S, ']');
              str_putc(S, '\n');
              if (i<h-1) str_putc(S, '\n');
            }
          }
          return;
      }
      gvalue = gfloor( simplify_shallow(gvalue) );
      if (typ(gvalue) != t_INT)
        pari_err(e_MISC,"not a t_INT in integer format conversion: %Ps", gvalue);
    }
    s = signe(gvalue);
    if (!s) { lbuf = 1; buf = zerotostr(); signvalue = 0; goto END; }

    l = lgefint(gvalue);
    uvalue = gvalue;
    if (signvalue < 0)
    {
      if (s < 0) uvalue = addii(int2n(bit_accuracy(l)), gvalue);
      signvalue = 0;
    }
    else
    {
      if (s < 0) { signvalue = '-'; uvalue = absi(uvalue); }
    }
    mxl = (l-2)* 22 + 1; /* octal at worst; 22 octal chars per 64bit word */
  } else {
    ulvalue = lvalue;
    if (signvalue < 0)
      signvalue = 0;
    else
      if (lvalue < 0) { signvalue = '-'; ulvalue = - lvalue; }
    mxl = 22 + 1; /* octal at worst; 22 octal chars to write down 2^64 - 1 */
  }
  if (base > 0) caps = 0; else { caps = 1; base = -base; }

  buf0 = buf = stack_malloc(mxl) + mxl; /* fill from the right */
  *--buf = 0; /* trailing \0 */
  if (gvalue) {
    if (base == 10) {
      long i, l, cnt;
      ulong *larray = convi(uvalue, &l);
      larray -= l;
      for (i = 0; i < l; i++) {
        cnt = 0;
        ulvalue = larray[i];
        do {
          *--buf = '0' + ulvalue%10;
          ulvalue = ulvalue / 10;
          cnt++;
        } while (ulvalue);
        if (i + 1 < l)
          for (;cnt<9;cnt++) *--buf = '0';
      }
    } else if (base == 16) {
      long i, l = lgefint(uvalue);
      GEN up = int_LSW(uvalue);
      for (i = 2; i < l; i++, up = int_nextW(up)) {
        ulong ucp = (ulong)*up;
        long j;
        for (j=0; j < BITS_IN_LONG/4; j++) {
          unsigned char cv = ucp & 0xF;
          *--buf = (caps? "0123456789ABCDEF":"0123456789abcdef")[cv];
          ucp >>= 4;
          if (ucp == 0 && i+1 == l) break;
        }
      } /* loop on hex digits in word */
    } else if (base == 8) {
      long i, l = lgefint(uvalue);
      GEN up = int_LSW(uvalue);
      ulong rem = 0;
      int shift = 0;
      int mask[3] = {0, 1, 3};
      for (i = 2; i < l; i++, up = int_nextW(up)) {
        ulong ucp = (ulong)*up;
        long j, ldispo = BITS_IN_LONG;
        if (shift) { /* 0, 1 or 2 */
          unsigned char cv = ((ucp & mask[shift]) <<(3-shift)) + rem;
          *--buf = "01234567"[cv];
          ucp >>= shift;
          ldispo -= shift;
        };
        shift = (shift + 3 - BITS_IN_LONG % 3) % 3;
        for (j=0; j < BITS_IN_LONG/3; j++) {
          unsigned char cv = ucp & 0x7;
          if (ucp == 0 && i+1 == l) { rem = 0; break; };
          *--buf = "01234567"[cv];
          ucp >>= 3;
          ldispo -= 3;
          rem = ucp;
          if (ldispo < 3) break;
        }
      } /* loop on hex digits in word */
      if (rem) *--buf = "01234567"[rem];
    }
  } else { /* not a gvalue, thus a standard integer */
    do {
      *--buf = (caps? "0123456789ABCDEF":"0123456789abcdef")[ulvalue % (unsigned)base ];
      ulvalue /= (unsigned)base;
    } while (ulvalue);
  }
  /* leading 0 if octal and alternate # form */
  if (caps && base == 8) *--buf = '0';
  lbuf = (buf0 - buf) - 1;
END:
  outpad(S, buf, lbuf, signvalue, ljust, len, zpad);
  if (!S->use_stack) avma = av;
}

static GEN
v_get_arg(GEN arg_vector, int *index, const char *save_fmt)
{
  if (*index >= lg(arg_vector))
    pari_err(e_MISC, "missing arg %d for printf format '%s'", *index, save_fmt);
  return gel(arg_vector, (*index)++);
}

static int
dosign(int blank, int plus)
{
  if (plus) return('+');
  if (blank) return(' ');
  return 0;
}

/* x * 10 + 'digit whose char value is ch'. Do not check for overflow */
static int
shift_add(int x, int ch)
{
  if (x < 0) /* was unset */
    x = ch - '0';
  else
    x = x*10 + ch - '0';
  return x;
}

static long
get_sigd(GEN gvalue, char ch, int maxwidth)
{
  long sigd, e;
  if (maxwidth < 0) return nbits2ndec(precreal);
  switch(ch)
  {
    case 'E':
    case 'e': sigd = maxwidth+1; break;
    case 'F':
    case 'f':
      e = gexpo(gvalue);
      if (e == -(long)HIGHEXPOBIT) /* exact 0 */
        sigd = 0;
      else
        sigd = ex10(e) + 1 + maxwidth;
      break;
    /* 'g', 'G' */
    default : sigd = maxwidth? maxwidth: 1; break;
  }
  return sigd;
}

static void
fmtreal(pari_str *S, GEN gvalue, int space, int signvalue, int FORMAT,
        int maxwidth, int ljust, int len, int zpad)
{
  pari_sp av = avma;
  long sigd;
  char *buf;

  if (typ(gvalue) == t_REAL)
    sigd = get_sigd(gvalue, FORMAT, maxwidth);
  else
  {
    long i, j, h, l = lg(gvalue);
    switch(typ(gvalue))
    {
      case t_VEC:
        str_putc(S, '[');
        for (i = 1; i < l; i++)
        {
          fmtreal(S, gel(gvalue,i), space, signvalue, FORMAT, maxwidth,
                  ljust,len,zpad);
          if (i < l-1) str_putc(S, ',');
        }
        str_putc(S, ']');
        return;
      case t_COL:
        str_putc(S, '[');
        for (i = 1; i < l; i++)
        {
          fmtreal(S, gel(gvalue,i), space, signvalue, FORMAT, maxwidth,
                  ljust,len,zpad);
          if (i < l-1) str_putc(S, ',');
        }
        str_putc(S, ']');
        str_putc(S, '~');
        return;
      case t_MAT:
        if (l == 1)
          str_puts(S, "[;]");
        else
        {
          h = lgcols(gvalue);
          for (i=1; i<l; i++)
          {
            str_putc(S, '[');
            for (j=1; j<h; j++)
            {
              fmtreal(S, gcoeff(gvalue,j,i), space, signvalue, FORMAT, maxwidth,
                      ljust,len,zpad);
              if (j<h-1) str_putc(S, ' ');
            }
            str_putc(S, ']');
            str_putc(S, '\n');
            if (i<l-1) str_putc(S, '\n');
          }
        }
        return;
    }
    sigd = get_sigd(gvalue, FORMAT, maxwidth);
    gvalue = gtofp(gvalue, ndec2prec(sigd));
    if (typ(gvalue) != t_REAL)
      pari_err(e_MISC,"impossible conversion to t_REAL: %Ps",gvalue);
  }
  if ((FORMAT == 'f' || FORMAT == 'F') && maxwidth >= 0)
    buf = absrtostr_width_frac(gvalue, maxwidth);
  else
    buf = absrtostr(gvalue, space, FORMAT, sigd);
  if (signe(gvalue) < 0) signvalue = '-';
  outpad(S, buf, strlen(buf), signvalue, ljust, len, zpad);
  if (!S->use_stack) avma = av;
}
/* Format handling "inspired" by the standard draft at
-- http://www.open-std.org/jtc1/sc22/wg14/www/docs/n1124.pdf pages 274ff
 * fmt is a standard printf format, except 'P' is a "length modifier"
 * allowing GEN arguments. Use either the arg_vector or (if NULL) the va_list.
 * Appent output to the pari_str S, which must be initialized; clean if
 * !S->use_stack, else leaves objects of stack. */
static void
str_arg_vprintf(pari_str *S, const char *fmt, GEN arg_vector, va_list args)
{
  int GENflag = 0, longflag = 0, pointflag = 0;
  int print_plus, print_blank, with_sharp, ch, ljust, len, maxwidth, zpad;
  long lvalue;
  int index = 1;
  GEN gvalue;
  const char *save_fmt = fmt;

  while ((ch = *fmt++) != '\0') {
    switch(ch) {
      case '%':
        ljust = zpad = 0;
        len = maxwidth = -1;
        GENflag = longflag = pointflag = 0;
        print_plus = print_blank = with_sharp = 0;
nextch:
        ch = *fmt++;
        switch(ch) {
          case 0:
            pari_err(e_MISC, "printf: end of format");
/*------------------------------------------------------------------------
                             -- flags
------------------------------------------------------------------------*/
          case '-':
            ljust = 1;
            goto nextch;
          case '+':
            print_plus = 1;
            goto nextch;
          case '#':
            with_sharp = 1;
            goto nextch;
          case ' ':
            print_blank = 1;
            goto nextch;
          case '0':
            /* appears as a flag: set zero padding */
            if (len < 0 && !pointflag) { zpad = '0'; goto nextch; }

            /* else part of a field width or precision */
            /* fall through */
/*------------------------------------------------------------------------
                       -- maxwidth or precision
------------------------------------------------------------------------*/
          case '1':
          case '2':
          case '3':
          case '4':
          case '5':
          case '6':
          case '7':
          case '8':
          case '9':
            if (pointflag)
              maxwidth = shift_add(maxwidth, ch);
            else
              len = shift_add(len, ch);
            goto nextch;

          case '*':
          {
            int *t = pointflag? &maxwidth: &len;
            if (arg_vector)
              *t = (int)gtolong( v_get_arg(arg_vector, &index, save_fmt) );
            else
              *t = va_arg(args, int);
            goto nextch;
          }
          case '.':
            if (pointflag)
              pari_err(e_MISC, "two '.' in conversion specification");
            pointflag = 1;
            goto nextch;
/*------------------------------------------------------------------------
                       -- length modifiers
------------------------------------------------------------------------*/
          case 'l':
            if (GENflag)
              pari_err(e_MISC, "P/l length modifiers in the same conversion");
#if !defined(_WIN64)
            if (longflag)
              pari_err_IMPL( "ll length modifier in printf");
#endif
            longflag = 1;
            goto nextch;
          case 'P':
            if (longflag)
              pari_err(e_MISC, "P/l length modifiers in the same conversion");
            if (GENflag)
              pari_err(e_MISC, "'P' length modifier appears twice");
            GENflag = 1;
            goto nextch;
          case 'h': /* dummy: va_arg promotes short into int */
            goto nextch;
/*------------------------------------------------------------------------
                       -- conversions
------------------------------------------------------------------------*/
          case 'u': /* not a signed conversion: print_(blank|plus) ignored */
#define get_num_arg() \
  if (arg_vector) { \
    lvalue = 0; \
    gvalue = v_get_arg(arg_vector, &index, save_fmt); \
  } else { \
    if (GENflag) { \
      lvalue = 0; \
      gvalue = va_arg(args, GEN); \
    } else { \
      lvalue = longflag? va_arg(args, long): va_arg(args, int); \
      gvalue = NULL; \
    } \
  }
            get_num_arg();
            fmtnum(S, lvalue, gvalue, 10, -1, ljust, len, zpad);
            break;
          case 'o': /* not a signed conversion: print_(blank|plus) ignored */
            get_num_arg();
            fmtnum(S, lvalue, gvalue, with_sharp? -8: 8, -1, ljust, len, zpad);
            break;
          case 'd':
          case 'i':
            get_num_arg();
            fmtnum(S, lvalue, gvalue, 10,
                   dosign(print_blank, print_plus), ljust, len, zpad);
            break;
          case 'p':
            str_putc(S, '0'); str_putc(S, 'x');
            if (arg_vector)
              lvalue = (long)v_get_arg(arg_vector, &index, save_fmt);
            else
              lvalue = (long)va_arg(args, void*);
            fmtnum(S, lvalue, NULL, 16, -1, ljust, len, zpad);
            break;
          case 'x': /* not a signed conversion: print_(blank|plus) ignored */
            if (with_sharp) { str_putc(S, '0'); str_putc(S, 'x'); }
            get_num_arg();
            fmtnum(S, lvalue, gvalue, 16, -1, ljust, len, zpad);
            break;
          case 'X': /* not a signed conversion: print_(blank|plus) ignored */
            if (with_sharp) { str_putc(S, '0'); str_putc(S, 'X'); }
            get_num_arg();
            fmtnum(S, lvalue, gvalue,-16, -1, ljust, len, zpad);
            break;
          case 's':
          {
            char *strvalue;
            pari_sp av = avma;

            if (arg_vector) {
              gvalue = v_get_arg(arg_vector, &index, save_fmt);
              strvalue = NULL;
            } else {
              if (GENflag) {
                gvalue = va_arg(args, GEN);
                strvalue = NULL;
              } else {
                gvalue = NULL;
                strvalue = va_arg(args, char *);
              }
            }
            if (gvalue) strvalue = GENtostr_unquoted(gvalue);
            fmtstr(S, strvalue, ljust, len, maxwidth);
            if (!S->use_stack) avma = av;
            break;
          }
          case 'c':
            if (arg_vector) {
              gvalue = v_get_arg(arg_vector, &index, save_fmt);
              ch = (int)gtolong(gvalue);
            } else {
              if (GENflag)
                ch = (int)gtolong( va_arg(args,GEN) );
              else
                ch = va_arg(args, int);
            }
            str_putc(S, ch);
            break;

          case '%':
            str_putc(S, ch);
            continue;
          case 'g':
          case 'G':
          case 'e':
          case 'E':
          case 'f':
          case 'F':
          {
            pari_sp av = avma;
            if (arg_vector)
              gvalue = simplify_shallow( v_get_arg(arg_vector, &index, save_fmt) );
            else {
              if (GENflag)
                gvalue = simplify_shallow( va_arg(args, GEN) );
              else
                gvalue = dbltor( va_arg(args, double) );
            }
            fmtreal(S, gvalue, GP_DATA->fmt->sp, dosign(print_blank,print_plus),
                    ch, maxwidth, ljust, len, zpad);
            if (!S->use_stack) avma = av;
            break;
          }
          default:
            pari_err(e_MISC, "invalid conversion or specification %c in format `%s'", ch, save_fmt);
        } /* second switch on ch */
        break;
      default:
        str_putc(S, ch);
        break;
    } /* first switch on ch */
  } /* while loop on ch */
  *S->cur = 0;
}

void
decode_color(long n, long *c)
{
  c[1] = n & 0xf; n >>= 4; /* foreground */
  c[2] = n & 0xf; n >>= 4; /* background */
  c[0] = n & 0xf; /* attribute */
}

#define COLOR_LEN 16
/* start printing in "color" c */
/* terminal has to support ANSI color escape sequences */
void
out_term_color(PariOUT *out, long c)
{
  static char s[COLOR_LEN];
  out->puts(term_get_color(s, c));
}
void
term_color(long c) { out_term_color(pariOut, c); }

/* s must be able to store 12 chars (including final \0) */
char *
term_get_color(char *s, long n)
{
  long c[3], a;
  if (!s) s = stack_malloc(COLOR_LEN);

  if (disable_color) { *s = 0; return s; }
  if (n == c_NONE || (a = gp_colors[n]) == c_NONE)
    strcpy(s, "\x1b[0m"); /* reset */
  else
  {
    decode_color(a,c);
    if (c[1]<8) c[1] += 30; else c[1] += 82;
    if (a & (1L<<12)) /* transparent background */
      sprintf(s, "\x1b[%ld;%ldm", c[0], c[1]);
    else
    {
      if (c[2]<8) c[2] += 40; else c[2] += 92;
      sprintf(s, "\x1b[%ld;%ld;%ldm", c[0], c[1], c[2]);
    }
  }
  return s;
}

static long
strlen_real(const char *s)
{
  const char *t = s;
  long len = 0;
  while (*t)
  {
    if (t[0] == '\x1b' && t[1] == '[')
    { /* skip ANSI escape sequence */
      t += 2;
      while (*t && *t++ != 'm') /* empty */;
      continue;
    }
    t++; len++;
  }
  return len;
}

#undef COLOR_LEN

/********************************************************************/
/**                                                                **/
/**                  PRINTING BASED ON SCREEN WIDTH                **/
/**                                                                **/
/********************************************************************/
#undef larg /* problems with SCO Unix headers (ioctl_arg) */
#ifdef HAS_TIOCGWINSZ
#  ifdef __sun
#    include <sys/termios.h>
#  endif
#  include <sys/ioctl.h>
#endif

static int
term_width_intern(void)
{
#ifdef _WIN32
  return win32_terminal_width();
#endif
#ifdef HAS_TIOCGWINSZ
  {
    struct winsize s;
    if (!(GP_DATA->flags & (gpd_EMACS|gpd_TEXMACS))
     && !ioctl(0, TIOCGWINSZ, &s)) return s.ws_col;
  }
#endif
  {
    char *str;
    if ((str = os_getenv("COLUMNS"))) return atoi(str);
  }
#ifdef __EMX__
  {
    int scrsize[2];
    _scrsize(scrsize); return scrsize[0];
  }
#endif
  return 0;
}

static int
term_height_intern(void)
{
#ifdef _WIN32
  return win32_terminal_height();
#endif
#ifdef HAS_TIOCGWINSZ
  {
    struct winsize s;
    if (!(GP_DATA->flags & (gpd_EMACS|gpd_TEXMACS))
     && !ioctl(0, TIOCGWINSZ, &s)) return s.ws_row;
  }
#endif
  {
    char *str;
    if ((str = os_getenv("LINES"))) return atoi(str);
  }
#ifdef __EMX__
  {
    int scrsize[2];
    _scrsize(scrsize); return scrsize[1];
  }
#endif
  return 0;
}

#define DFT_TERM_WIDTH  80
#define DFT_TERM_HEIGHT 20

int
term_width(void)
{
  int n = term_width_intern();
  return (n>1)? n: DFT_TERM_WIDTH;
}

int
term_height(void)
{
  int n = term_height_intern();
  return (n>1)? n: DFT_TERM_HEIGHT;
}

static ulong col_index;

/* output string wrapped after MAX_WIDTH characters (for gp -test) */
static void
putc_lw(char c)
{
  if (c == '\n') col_index = 0;
  else if (col_index >= GP_DATA->linewrap) { normalOutC('\n'); col_index = 1; }
  else col_index++;
  normalOutC(c);
}
static void
puts_lw(const char *s) { while (*s) putc_lw(*s++); }

static PariOUT pariOut_lw= {putc_lw, puts_lw, normalOutF};

void
init_linewrap(long w) { col_index=0; GP_DATA->linewrap=w; pariOut=&pariOut_lw; }

/* output stopped after max_line have been printed, for default(lines,).
 * n = length of prefix already printed (print up to max_lin lines) */
void
lim_lines_output(char *s, long n, long max_lin)
{
  long lin, col, width;
  char c;
  if (!*s) return;
  width = term_width();
  lin = 1;
  col = n;

  if (lin > max_lin) return;
  while ( (c = *s++) )
  {
    if (lin >= max_lin)
      if (c == '\n' || col >= width-5)
      {
        pari_sp av = avma;
        pari_puts(term_get_color(NULL, c_ERR)); avma = av;
        pari_puts("[+++]"); return;
      }
    if (c == '\n')         { col = -1; lin++; }
    else if (col == width) { col =  0; lin++; }
    set_last_newline(c);
    col++; pari_putc(c);
  }
}

static void
new_line(PariOUT *out, const char *prefix)
{
  out_putc(out, '\n'); if (prefix) out_puts(out, prefix);
}

#define is_blank(c) ((c) == ' ' || (c) == '\n' || (c) == '\t')
/* output: <prefix>< s wrapped at EOL >
 *         <prefix>< ... > <str>
 *                         ^---  (no \n at the end)
 * If str is NULL, omit the arrow, end the text with '\n'.
 * If prefix is NULL, use "" */
void
print_prefixed_text(PariOUT *out, const char *s, const char *prefix,
                    const char *str)
{
  const long prelen = prefix? strlen_real(prefix): 0;
  const long W = term_width(), ls = strlen(s);
  long linelen = prelen;
  char *word = (char*)pari_malloc(ls + 3);

  if (prefix) out_puts(out, prefix);
  for(;;)
  {
    long len;
    int blank = 0;
    char *u = word;
    while (*s && !is_blank(*s)) *u++ = *s++;
    *u = 0; /* finish "word" */
    len = strlen_real(word);
    linelen += len;
    if (linelen >= W) { new_line(out, prefix); linelen = prelen + len; }
    out_puts(out, word);
    while (is_blank(*s)) {
      switch (*s) {
        case ' ': break;
        case '\t':
          linelen = (linelen & ~7UL) + 8; out_putc(out, '\t');
          blank = 1; break;
        case '\n':
          linelen = W;
          blank = 1; break;
      }
      if (linelen >= W) { new_line(out, prefix); linelen = prelen; }
      s++;
    }
    if (!*s) break;
    if (!blank) { out_putc(out, ' '); linelen++; }
  }
  if (!str)
    out_putc(out, '\n');
  else
  {
    long i,len = strlen_real(str);
    int space = (*str == ' ' && str[1]);
    if (linelen + len >= W)
    {
      new_line(out, prefix); linelen = prelen;
      if (space) { str++; len--; space = 0; }
    }
    out_term_color(out, c_OUTPUT);
    out_puts(out, str);
    if (!len || str[len-1] != '\n') out_putc(out, '\n');
    if (space) { linelen++; len--; }
    out_term_color(out, c_ERR);
    if (prefix) { out_puts(out, prefix); linelen -= prelen; }
    for (i=0; i<linelen; i++) out_putc(out, ' ');
    out_putc(out, '^');
    for (i=0; i<len; i++) out_putc(out, '-');
  }
  pari_free(word);
}

#define CONTEXT_LEN 46
#define MAX_TERM_COLOR 16
/* Outputs a beautiful error message (not \n terminated)
 *   msg is errmessage to print.
 *   s points to the offending chars.
 *   entry tells how much we can go back from s[0] */
void
print_errcontext(PariOUT *out,
                 const char *msg, const char *s, const char *entry)
{
  const long MAX_PAST = 25;
  long past = s - entry, future, lmsg;
  char str[CONTEXT_LEN + 1 + 1], pre[MAX_TERM_COLOR + 8 + 1];
  char *buf, *t;

  if (!s || !entry) { print_prefixed_text(out, msg,"  ***   ",NULL); return; }

  /* message + context */
  lmsg = strlen(msg);
  /* msg + past + ': ' + '...' + term_get_color + \0 */
  t = buf = (char*)pari_malloc(lmsg + MAX_PAST + 2 + 3 + MAX_TERM_COLOR + 1);
  memcpy(t, msg, lmsg); t += lmsg;
  strcpy(t, ": "); t += 2;
  if (past <= 0) past = 0;
  else
  {
    if (past > MAX_PAST) { past = MAX_PAST; strcpy(t, "..."); t += 3; }
    term_get_color(t, c_OUTPUT);
    t += strlen(t);
    memcpy(t, s - past, past); t[past] = 0;
  }

  /* suffix (past arrow) */
  t = str; if (!past) *t++ = ' ';
  future = CONTEXT_LEN - past;
  strncpy(t, s, future); t[future] = 0;
  /* prefix '***' */
  term_get_color(pre, c_ERR);
  strcat(pre, "  ***   ");
  /* now print */
  print_prefixed_text(out, buf, pre, str);
  pari_free(buf);
}

/********************************************************************/
/**                                                                **/
/**                    GEN <---> CHARACTER STRINGS                 **/
/**                                                                **/
/********************************************************************/
static OUT_FUN
get_fun(long flag)
{
  switch(flag) {
    case f_RAW : return bruti;
    case f_TEX : return texi;
    default: return matbruti;
  }
}

char *
stack_strdup(const char *s)
{
  long n = strlen(s)+1;
  char *t = stack_malloc(n);
  memcpy(t,s,n); return t;
}
char *
stack_strcat(const char *s, const char *t)
{
  long ls = strlen(s), lt = strlen(t);
  long n = ls + lt + 1;
  char *u = stack_malloc(n);
  memcpy(u,     s, ls);
  memcpy(u + ls,t, lt+1); return u;
}

char *
pari_strdup(const char *s)
{
  long n = strlen(s)+1;
  char *t = (char*)pari_malloc(n);
  memcpy(t,s,n); return t;
}

char *
pari_strndup(const char *s, long n)
{
  char *t = (char*)pari_malloc(n+1);
  memcpy(t,s,n); t[n] = 0; return t;
}

/* not stack clean */
static char *
stack_GENtostr_fun(GEN x, pariout_t *T, OUT_FUN out)
{
  pari_str S; str_init(&S, 1);
  out(x, T, &S); *S.cur = 0;
  return S.string;
}
/* same but remove quotes "" around t_STR */
static char *
stack_GENtostr_fun_unquoted(GEN x, pariout_t *T, OUT_FUN out)
{ return (typ(x)==t_STR)? GSTR(x): stack_GENtostr_fun(x, T, out); }

/* stack-clean: pari-malloc'ed */
static char *
GENtostr_fun(GEN x, pariout_t *T, OUT_FUN out)
{
  pari_sp av = avma;
  pari_str S; str_init(&S, 0);
  out(x, T, &S); *S.cur = 0;
  avma = av; return S.string;
}
/* returns a malloc-ed string, which should be freed after usage */
/* Returns pari_malloc()ed string */
char *
GENtostr(GEN x)
{ return GENtostr_fun(x, GP_DATA->fmt, get_fun(GP_DATA->fmt->prettyp)); }
char *
GENtoTeXstr(GEN x) { return GENtostr_fun(x, GP_DATA->fmt, &texi); }
char *
GENtostr_unquoted(GEN x)
{ return stack_GENtostr_fun_unquoted(x, GP_DATA->fmt, &bruti); }
/* alloc-ed on PARI stack */
char *
GENtostr_raw(GEN x) { return stack_GENtostr_fun(x,GP_DATA->fmt,&bruti); }

GEN
GENtoGENstr(GEN x)
{
  char *s = GENtostr_fun(x, GP_DATA->fmt, &bruti);
  GEN z = strtoGENstr(s); pari_free(s); return z;
}
GEN
GENtoGENstr_nospace(GEN x)
{
  pariout_t T = *(GP_DATA->fmt);
  char *s;
  GEN z;
  T.sp = 0;
  s = GENtostr_fun(x, &T, &bruti);
  z = strtoGENstr(s); pari_free(s); return z;
}

static char
ltoc(long n) {
  if (n <= 0 || n > 255)
    pari_err(e_MISC, "out of range in integer -> character conversion (%ld)", n);
  return (char)n;
}
static char
itoc(GEN x) { return ltoc(gtos(x)); }

GEN
Strchr(GEN g)
{
  long i, l, len, t = typ(g);
  char *s;
  GEN x;
  if (is_vec_t(t)) {
    l = lg(g); len = nchar2nlong(l);
    x = cgetg(len+1, t_STR); s = GSTR(x);
    for (i=1; i<l; i++) *s++ = itoc(gel(g,i));
  }
  else if (t == t_VECSMALL)
  {
    l = lg(g); len = nchar2nlong(l);
    x = cgetg(len+1, t_STR); s = GSTR(x);
    for (i=1; i<l; i++) *s++ = ltoc(g[i]);
  }
  else
    return chartoGENstr(itoc(g));
  *s = 0; return x;
}

/********************************************************************/
/**                                                                **/
/**                         WRITE AN INTEGER                       **/
/**                                                                **/
/********************************************************************/
char *
itostr(GEN x) {
  long sx = signe(x), l;
  return sx? itostr_sign(x, sx, &l): zerotostr();
}

/* x != 0 t_INT, write abs(x) to S */
static void
str_absint(pari_str *S, GEN x)
{
  pari_sp av;
  long l;
  str_alloc(S, lgefint(x)); /* careful ! */
  av = avma;
  str_puts(S, itostr_sign(x, 1, &l)); avma = av;
}

#define putsigne_nosp(S, x) str_putc(S, (x>0)? '+' : '-')
#define putsigne(S, x) str_puts(S, (x>0)? " + " : " - ")
#define sp_sign_sp(T,S, x) ((T)->sp? putsigne(S,x): putsigne_nosp(S,x))
#define semicolon_sp(T,S)  ((T)->sp? str_puts(S, "; "): str_putc(S, ';'))
#define comma_sp(T,S)      ((T)->sp? str_puts(S, ", "): str_putc(S, ','))

/* print e to S (more efficient than sprintf) */
static void
str_ulong(pari_str *S, ulong e)
{
  if (e == 0) str_putc(S, '0');
  else
  {
    char buf[21], *p = buf + numberof(buf);
    *--p = 0;
    if (e > 9) {
      do
        *--p = "0123456789"[e % 10];
      while ((e /= 10) > 9);
    }
    *--p = "0123456789"[e];
    str_puts(S, p);
  }
}
static void
str_long(pari_str *S, long e)
{
  if (e >= 0) str_ulong(S, (ulong)e);
  else { str_putc(S, '-'); str_ulong(S, -(ulong)e); }
}

static void
wr_vecsmall(pariout_t *T, pari_str *S, GEN g)
{
  long i, l;
  str_puts(S, "Vecsmall(["); l = lg(g);
  for (i=1; i<l; i++)
  {
    str_long(S, g[i]);
    if (i<l-1) comma_sp(T,S);
  }
  str_puts(S, "])");
}

/********************************************************************/
/**                                                                **/
/**                       HEXADECIMAL OUTPUT                       **/
/**                                                                **/
/********************************************************************/
/* English ordinal numbers */
char *
uordinal(ulong i)
{
  const char *suff[] = {"st","nd","rd","th"};
  char *s = stack_malloc(23);
  long k = 3;
  switch (i%10)
  {
    case 1: if (i%100!=11) k = 0;
            break;
    case 2: if (i%100!=12) k = 1;
            break;
    case 3: if (i%100!=13) k = 2;
            break;
  }
  sprintf(s, "%lu%s", i, suff[k]); return s;
}

const char *
type_name(long t)
{
  const char *s;
  switch(t)
  {
    case t_INT    : s="t_INT";     break;
    case t_REAL   : s="t_REAL";    break;
    case t_INTMOD : s="t_INTMOD";  break;
    case t_FRAC   : s="t_FRAC";    break;
    case t_FFELT  : s="t_FFELT";   break;
    case t_COMPLEX: s="t_COMPLEX"; break;
    case t_PADIC  : s="t_PADIC";   break;
    case t_QUAD   : s="t_QUAD";    break;
    case t_POLMOD : s="t_POLMOD";  break;
    case t_POL    : s="t_POL";     break;
    case t_SER    : s="t_SER";     break;
    case t_RFRAC  : s="t_RFRAC";   break;
    case t_QFR    : s="t_QFR";     break;
    case t_QFI    : s="t_QFI";     break;
    case t_VEC    : s="t_VEC";     break;
    case t_COL    : s="t_COL";     break;
    case t_MAT    : s="t_MAT";     break;
    case t_LIST   : s="t_LIST";    break;
    case t_STR    : s="t_STR";     break;
    case t_VECSMALL:s="t_VECSMALL";break;
    case t_CLOSURE: s="t_CLOSURE"; break;
    case t_ERROR:   s="t_ERROR";   break;
    case t_INFINITY:s="t_INFINITY";break;
    default: pari_err(e_MISC,"unknown type %ld",t);
      s = NULL; /* LCOV_EXCL_LINE */
  }
  return s;
}

static char
vsigne(GEN x)
{
  long s = signe(x);
  if (!s) return '0';
  return (s > 0) ? '+' : '-';
}

static void
blancs(long nb) { while (nb-- > 0) pari_putc(' '); }

/* write an "address" */
static void
str_addr(pari_str *S, ulong x)
{ char s[128]; sprintf(s,"%0*lx", BITS_IN_LONG/4, x); str_puts(S, s); }
static void
dbg_addr(ulong x) { pari_printf("[&=%0*lx] ", BITS_IN_LONG/4, x); }
/* write a "word" */
static void
dbg_word(ulong x) { pari_printf("%0*lx ", BITS_IN_LONG/4, x); }

/* bl: indent level */
static void
dbg(GEN x, long nb, long bl)
{
  long tx,i,j,e,dx,lx;

  if (!x) { pari_puts("NULL\n"); return; }
  tx = typ(x);
  if (tx == t_INT && x == gen_0) { pari_puts("gen_0\n"); return; }
  dbg_addr((ulong)x);

  lx = lg(x);
  pari_printf("%s(lg=%ld%s):",type_name(tx)+2,lx,isclone(x)? ",CLONE" : "");
  dbg_word(x[0]);
  if (! is_recursive_t(tx)) /* t_INT, t_REAL, t_STR, t_VECSMALL */
  {
    if (tx == t_STR)
      pari_puts("chars:");
    else if (tx == t_INT)
    {
      lx = lgefint(x);
      pari_printf("(%c,lgefint=%ld):", vsigne(x), lx);
    }
    else if (tx == t_REAL)
      pari_printf("(%c,expo=%ld):", vsigne(x), expo(x));
    if (nb < 0) nb = lx;
    for (i=1; i < nb; i++) dbg_word(x[i]);
    pari_putc('\n'); return;
  }

  if (tx == t_PADIC)
    pari_printf("(precp=%ld,valp=%ld):", precp(x), valp(x));
  else if (tx == t_POL)
    pari_printf("(%c,varn=%ld):", vsigne(x), varn(x));
  else if (tx == t_SER)
    pari_printf("(%c,varn=%ld,prec=%ld,valp=%ld):",
               vsigne(x), varn(x), lg(x)-2, valp(x));
  else if (tx == t_LIST)
  {
    pari_printf("(subtyp=%ld,lmax=%ld):", list_typ(x), list_nmax(x));
    x = list_data(x); lx = x? lg(x): 1;
    tx = t_VEC; /* print list_data as vec */
  } else if (tx == t_CLOSURE)
    pari_printf("(arity=%ld%s):", closure_arity(x),
                                  closure_is_variadic(x)?"+":"");
  for (i=1; i<lx; i++) dbg_word(x[i]);
  bl+=2; pari_putc('\n');
  switch(tx)
  {
    case t_INTMOD: case t_POLMOD:
    {
      const char *s = (tx==t_INTMOD)? "int = ": "pol = ";
      blancs(bl); pari_puts("mod = "); dbg(gel(x,1),nb,bl);
      blancs(bl); pari_puts(s);        dbg(gel(x,2),nb,bl);
      break;
    }
    case t_FRAC: case t_RFRAC:
      blancs(bl); pari_puts("num = "); dbg(gel(x,1),nb,bl);
      blancs(bl); pari_puts("den = "); dbg(gel(x,2),nb,bl);
      break;

    case t_FFELT:
      blancs(bl); pari_puts("pol = "); dbg(gel(x,2),nb,bl);
      blancs(bl); pari_puts("mod = "); dbg(gel(x,3),nb,bl);
      blancs(bl); pari_puts("p   = "); dbg(gel(x,4),nb,bl);
      break;

    case t_COMPLEX:
      blancs(bl); pari_puts("real = "); dbg(gel(x,1),nb,bl);
      blancs(bl); pari_puts("imag = "); dbg(gel(x,2),nb,bl);
      break;

    case t_PADIC:
      blancs(bl); pari_puts("  p : "); dbg(gel(x,2),nb,bl);
      blancs(bl); pari_puts("p^l : "); dbg(gel(x,3),nb,bl);
      blancs(bl); pari_puts("  I : "); dbg(gel(x,4),nb,bl);
      break;

    case t_QUAD:
      blancs(bl); pari_puts("pol = ");  dbg(gel(x,1),nb,bl);
      blancs(bl); pari_puts("real = "); dbg(gel(x,2),nb,bl);
      blancs(bl); pari_puts("imag = "); dbg(gel(x,3),nb,bl);
      break;

    case t_POL: case t_SER:
      e = (tx==t_SER)? valp(x): 0;
      for (i=2; i<lx; i++)
      {
        blancs(bl); pari_printf("coef of degree %ld = ",e);
        e++; dbg(gel(x,i),nb,bl);
      }
      break;

    case t_QFR: case t_QFI: case t_VEC: case t_COL:
      for (i=1; i<lx; i++)
      {
        blancs(bl); pari_printf("%s component = ",uordinal(i));
        dbg(gel(x,i),nb,bl);
      }
      break;

    case t_CLOSURE:
      blancs(bl); pari_puts("code = "); dbg(closure_get_code(x),nb,bl);
      blancs(bl); pari_puts("operand = "); dbg(closure_get_oper(x),nb,bl);
      blancs(bl); pari_puts("data = "); dbg(closure_get_data(x),nb,bl);
      blancs(bl); pari_puts("dbg/frpc/fram = "); dbg(closure_get_dbg(x),nb,bl);
      if (lg(x)>=7)
      {
        blancs(bl); pari_puts("text = "); dbg(closure_get_text(x),nb,bl);
        if (lg(x)>=8)
        {
          blancs(bl); pari_puts("frame = "); dbg(closure_get_frame(x),nb,bl);
        }
      }
      break;

    case t_ERROR:
      blancs(bl);
      pari_printf("error type = %s\n", numerr_name(err_get_num(x)));
      for (i=2; i<lx; i++)
      {
        blancs(bl); pari_printf("%s component = ",uordinal(i-1));
        dbg(gel(x,i),nb,bl);
      }
      break;

    case t_INFINITY:
      blancs(bl); pari_printf("1st component = ");
      dbg(gel(x,1),nb,bl);
      break;

    case t_MAT:
    {
      GEN c = gel(x,1);
      if (lx == 1) return;
      if (typ(c) == t_VECSMALL)
      {
        for (i = 1; i < lx; i++)
        {
          blancs(bl); pari_printf("%s column = ",uordinal(i));
          dbg(gel(x,i),nb,bl);
        }
      }
      else
      {
        dx = lg(c);
        for (i=1; i<dx; i++)
          for (j=1; j<lx; j++)
          {
            blancs(bl); pari_printf("mat(%ld,%ld) = ",i,j);
            dbg(gcoeff(x,i,j),nb,bl);
          }
      }
    }
  }
}

void
dbgGEN(GEN x, long nb) { dbg(x,nb,0); }

static void
print_entree(entree *ep)
{
  pari_printf(" %s ",ep->name); dbg_addr((ulong)ep);
  pari_printf(": hash = %ld [%ld]\n", ep->hash % functions_tblsz, ep->hash);
  pari_printf("   menu = %2ld, code = %-10s",
              ep->menu, ep->code? ep->code: "NULL");
  if (ep->next)
  {
    pari_printf("next = %s ",(ep->next)->name);
    dbg_addr((ulong)ep->next);
  }
  pari_puts("\n");
}

/* s = digit n : list of entrees in functions_hash[n] (s = $: last entry)
 *   = range m-n: functions_hash[m..n]
 *   = identifier: entree for that identifier */
void
print_functions_hash(const char *s)
{
  long m, n, Max, Total;
  entree *ep;

  if (isdigit((int)*s) || *s == '$')
  {
    m = functions_tblsz-1; n = atol(s);
    if (*s=='$') n = m;
    if (m<n) pari_err(e_MISC,"invalid range in print_functions_hash");
    while (isdigit((int)*s)) s++;

    if (*s++ != '-') m = n;
    else
    {
      if (*s !='$') m = minss(atol(s),m);
      if (m<n) pari_err(e_MISC,"invalid range in print_functions_hash");
    }

    for(; n<=m; n++)
    {
      pari_printf("*** hashcode = %lu\n",n);
      for (ep=functions_hash[n]; ep; ep=ep->next) print_entree(ep);
    }
    return;
  }
  if (is_keyword_char((int)*s))
  {
    ep = is_entry(s);
    if (!ep) pari_err(e_MISC,"no such function");
    print_entree(ep); return;
  }
  if (*s=='-')
  {
    for (n=0; n<functions_tblsz; n++)
    {
      m=0;
      for (ep=functions_hash[n]; ep; ep=ep->next) m++;
      pari_printf("%3ld:%3ld ",n,m);
      if (n%9 == 8) pari_putc('\n');
    }
    pari_putc('\n'); return;
  }
  Max = Total = 0;
  for (n=0; n<functions_tblsz; n++)
  {
    long cnt = 0;
    for (ep=functions_hash[n]; ep; ep=ep->next) { print_entree(ep); cnt++; }
    Total += cnt;
    if (cnt > Max) Max = cnt;
  }
  pari_printf("Total: %ld, Max: %ld\n", Total, Max);
}

/********************************************************************/
/**                                                                **/
/**                        FORMATTED OUTPUT                        **/
/**                                                                **/
/********************************************************************/
static const char *
get_var(long v, char *buf)
{
  entree *ep = varentries[v];
  if (ep) return (char*)ep->name;
  sprintf(buf,"t%d",(int)v); return buf;
}

static void
do_append(char **sp, char c, char *last, int count)
{
  if (*sp + count > last)
    pari_err(e_MISC, "TeX variable name too long");
  while (count--)
    *(*sp)++ = c;
}

static char *
get_texvar(long v, char *buf, unsigned int len)
{
  entree *ep = varentries[v];
  char *t = buf, *e = buf + len - 1;
  const char *s;

  if (!ep) pari_err(e_MISC, "this object uses debugging variables");
  s = ep->name;
  if (strlen(s) >= len) pari_err(e_MISC, "TeX variable name too long");
  while (isalpha((int)*s)) *t++ = *s++;
  *t = 0;
  if (isdigit((int)*s) || *s == '_') {
    int seen1 = 0, seen = 0;

    /* Skip until the first non-underscore */
    while (*s == '_') s++, seen++;

    /* Special-case integers and empty subscript */
    if (*s == 0 || isdigit((unsigned char)*s))
      seen++;

    do_append(&t, '_', e, 1);
    do_append(&t, '{', e, 1);
    do_append(&t, '[', e, seen - 1);
    while (1) {
      if (*s == '_')
        seen1++, s++;
      else {
        if (seen1) {
          do_append(&t, ']', e, (seen >= seen1 ? seen1 : seen) - 1);
          do_append(&t, ',', e, 1);
          do_append(&t, '[', e, seen1 - 1);
          if (seen1 > seen)
            seen = seen1;
          seen1 = 0;
        }
        if (*s == 0)
          break;
        do_append(&t, *s++, e, 1);
      }
    }
    do_append(&t, ']', e, seen - 1);
    do_append(&t, '}', e, 1);
    *t = 0;
  }
  return buf;
}

void
dbg_pari_heap(void)
{
  long nu, l, u, s;
  pari_sp av = avma;
  GEN adr = getheap();
  pari_sp top = pari_mainstack->top, bot = pari_mainstack->bot;

  nu = (top-avma)/sizeof(long);
  l = pari_mainstack->size/sizeof(long);
  pari_printf("\n Top : %lx   Bottom : %lx   Current stack : %lx\n",
              top, bot, avma);
  pari_printf(" Used :                         %ld  long words  (%ld K)\n",
              nu, nu/1024*sizeof(long));
  pari_printf(" Available :                    %ld  long words  (%ld K)\n",
              (l-nu), (l-nu)/1024*sizeof(long));
  pari_printf(" Occupation of the PARI stack : %6.2f percent\n", 100.0*nu/l);
  pari_printf(" %ld objects on heap occupy %ld long words\n\n",
              itos(gel(adr,1)), itos(gel(adr,2)));
  u = pari_var_next();
  s = MAXVARN - pari_var_next_temp();
  pari_printf(" %ld variable names used (%ld user + %ld private) out of %d\n\n",
              u+s, u, s, MAXVARN);
  avma = av;
}

/* is to be printed as '0' */
static long
isnull(GEN g)
{
  long i;
  switch (typ(g))
  {
    case t_INT:
      return !signe(g);
    case t_COMPLEX:
      return isnull(gel(g,1)) && isnull(gel(g,2));
    case t_FFELT:
      return FF_equal0(g);
    case t_QUAD:
      return isnull(gel(g,2)) && isnull(gel(g,3));
    case t_FRAC: case t_RFRAC:
      return isnull(gel(g,1));
    case t_POL:
      for (i=lg(g)-1; i>1; i--)
        if (!isnull(gel(g,i))) return 0;
      return 1;
  }
  return 0;
}
/* 0 coeff to be omitted in t_POL ? */
static int
isnull_for_pol(GEN g)
{
  switch(typ(g))
  {
    case t_INTMOD: return !signe(gel(g,2));
    case t_POLMOD: return isnull(gel(g,2));
    default:       return isnull(g);
  }
}

/* return 1 or -1 if g is 1 or -1, 0 otherwise*/
static long
isone(GEN g)
{
  long i;
  switch (typ(g))
  {
    case t_INT:
      return (signe(g) && is_pm1(g))? signe(g): 0;
    case t_FFELT:
      return FF_equal1(g);
    case t_COMPLEX:
      return isnull(gel(g,2))? isone(gel(g,1)): 0;
    case t_QUAD:
      return isnull(gel(g,3))? isone(gel(g,2)): 0;
    case t_FRAC: case t_RFRAC:
      return isone(gel(g,1)) * isone(gel(g,2));
    case t_POL:
      if (!signe(g)) return 0;
      for (i=lg(g)-1; i>2; i--)
        if (!isnull(gel(g,i))) return 0;
      return isone(gel(g,2));
  }
  return 0;
}

/* if g is a "monomial", return its sign, 0 otherwise */
static long
isfactor(GEN g)
{
  long i,deja,sig;
  switch(typ(g))
  {
    case t_INT: case t_REAL:
      return (signe(g)<0)? -1: 1;
    case t_FRAC: case t_RFRAC:
      return isfactor(gel(g,1));
    case t_FFELT:
      return isfactor(FF_to_FpXQ_i(g));
    case t_COMPLEX:
      if (isnull(gel(g,1))) return isfactor(gel(g,2));
      if (isnull(gel(g,2))) return isfactor(gel(g,1));
      return 0;
    case t_PADIC:
      return !signe(gel(g,4));
    case t_QUAD:
      if (isnull(gel(g,2))) return isfactor(gel(g,3));
      if (isnull(gel(g,3))) return isfactor(gel(g,2));
      return 0;
    case t_POL: deja = 0; sig = 1;
      for (i=lg(g)-1; i>1; i--)
        if (!isnull_for_pol(gel(g,i)))
        {
          if (deja) return 0;
          sig=isfactor(gel(g,i)); deja=1;
        }
      return sig? sig: 1;
    case t_SER:
      for (i=lg(g)-1; i>1; i--)
        if (!isnull(gel(g,i))) return 0;
  }
  return 1;
}

/* return 1 if g is a "truc" (see anal.c) */
static long
isdenom(GEN g)
{
  long i,deja;
  switch(typ(g))
  {
    case t_FRAC: case t_RFRAC:
      return 0;
    case t_COMPLEX: return isnull(gel(g,2));
    case t_PADIC: return !signe(gel(g,4));
    case t_QUAD: return isnull(gel(g,3));

    case t_POL: deja = 0;
      for (i=lg(g)-1; i>1; i--)
        if (!isnull(gel(g,i)))
        {
          if (deja) return 0;
          if (i==2) return isdenom(gel(g,2));
          if (!isone(gel(g,i))) return 0;
          deja=1;
        }
      return 1;
    case t_SER:
      for (i=lg(g)-1; i>1; i--)
        if (!isnull(gel(g,i))) return 0;
  }
  return 1;
}

/********************************************************************/
/**                                                                **/
/**                           RAW OUTPUT                           **/
/**                                                                **/
/********************************************************************/
/* ^e */
static void
texexpo(pari_str *S, long e)
{
  if (e != 1) {
    str_putc(S, '^');
    if (e >= 0 && e < 10)
    { str_putc(S, '0' + e); }
    else
    {
      str_putc(S, '{'); str_long(S, e); str_putc(S, '}');
    }
  }
}
static void
wrexpo(pari_str *S, long e)
{ if (e != 1) { str_putc(S, '^'); str_long(S, e); } }

/* v^e */
static void
VpowE(pari_str *S, const char *v, long e) { str_puts(S, v); wrexpo(S,e); }
static void
texVpowE(pari_str *S, const char *v, long e) { str_puts(S, v); texexpo(S,e); }
static void
monome(pari_str *S, const char *v, long e)
{ if (e) VpowE(S, v, e); else str_putc(S, '1'); }
static void
texnome(pari_str *S, const char *v, long e)
{ if (e) texVpowE(S, v, e); else str_putc(S, '1'); }

/* ( a ) */
static void
paren(pariout_t *T, pari_str *S, GEN a)
{ str_putc(S, '('); bruti(a,T,S); str_putc(S, ')'); }
static void
texparen(pariout_t *T, pari_str *S, GEN a)
{
  if (T->TeXstyle & TEXSTYLE_PAREN)
    str_puts(S, " (");
  else
    str_puts(S, " \\left(");
  texi(a,T,S);
  if (T->TeXstyle & TEXSTYLE_PAREN)
    str_puts(S, ") ");
  else
    str_puts(S, "\\right) ");
}

/* * v^d */
static void
times_texnome(pari_str *S, const char *v, long d)
{ if (d) { str_puts(S, "\\*"); texnome(S,v,d); } }
static void
times_monome(pari_str *S, const char *v, long d)
{ if (d) { str_putc(S, '*'); monome(S,v,d); } }

/* write a * v^d */
static void
wr_monome(pariout_t *T, pari_str *S, GEN a, const char *v, long d)
{
  long sig = isone(a);

  if (sig) {
    sp_sign_sp(T,S,sig); monome(S,v,d);
  } else {
    sig = isfactor(a);
    if (sig) { sp_sign_sp(T,S,sig); bruti_sign(a,T,S,0); }
    else { sp_sign_sp(T,S,1); paren(T,S, a); }
    times_monome(S, v, d);
  }
}
static void
wr_texnome(pariout_t *T, pari_str *S, GEN a, const char *v, long d)
{
  long sig = isone(a);

  str_putc(S, '\n'); /* Avoid TeX buffer overflow */
  if (T->TeXstyle & TEXSTYLE_BREAK) str_puts(S, "\\PARIbreak ");

  if (sig) {
    putsigne(S,sig); texnome(S,v,d);
  } else {
    sig = isfactor(a);
    if (sig) { putsigne(S,sig); texi_sign(a,T,S,0); }
    else { str_puts(S, " +"); texparen(T,S, a); }
    times_texnome(S, v, d);
  }
}

static void
wr_lead_monome(pariout_t *T, pari_str *S, GEN a,const char *v, long d, int addsign)
{
  long sig = isone(a);
  if (sig) {
    if (addsign && sig<0) str_putc(S, '-');
    monome(S,v,d);
  } else {
    if (isfactor(a)) bruti_sign(a,T,S,addsign);
    else paren(T,S, a);
    times_monome(S, v, d);
  }
}
static void
wr_lead_texnome(pariout_t *T, pari_str *S, GEN a,const char *v, long d, int addsign)
{
  long sig = isone(a);
  if (sig) {
    if (addsign && sig<0) str_putc(S, '-');
    texnome(S,v,d);
  } else {
    if (isfactor(a)) texi_sign(a,T,S,addsign);
    else texparen(T,S, a);
    times_texnome(S, v, d);
  }
}

static void
prints(GEN g, pariout_t *T, pari_str *S)
{ (void)T; str_long(S, (long)g); }

static void
quote_string(pari_str *S, char *s)
{
  str_putc(S, '"');
  while (*s)
  {
    char c=*s++;
    if (c=='\\' || c=='"' || c=='\033' || c=='\n' || c=='\t')
    {
      str_putc(S, '\\');
      switch(c)
      {
      case '\\': case '"': break;
      case '\n':   c='n'; break;
      case '\033': c='e'; break;
      case '\t':   c='t'; break;
      }
    }
    str_putc(S, c);
  }
  str_putc(S, '"');
}

static int
print_0_or_pm1(GEN g, pari_str *S, int addsign)
{
  long r;
  if (!g) { str_puts(S, "NULL"); return 1; }
  if (isnull(g)) { str_putc(S, '0'); return 1; }
  r = isone(g);
  if (r)
  {
    if (addsign && r<0) str_putc(S, '-');
    str_putc(S, '1'); return 1;
  }
  return 0;
}

static void
print_precontext(GEN g, pari_str *S, long tex)
{
  if (lg(g)<8 || lg(gel(g,7))==1) return;
  else
  {
    long i, n  = closure_arity(g);
    str_puts(S,"(");
    for(i=1; i<=n; i++)
    {
      str_puts(S,"v");
      if (tex) str_puts(S,"_{");
      str_ulong(S,i);
      if (tex) str_puts(S,"}");
      if (i < n) str_puts(S,",");
    }
    str_puts(S,")->");
  }
}

static void
print_context(GEN g, pariout_t *T, pari_str *S, long tex)
{
  GEN str = closure_get_text(g);
  if (lg(g)<8 || lg(gel(g,7))==1) return;
  if (typ(str)==t_VEC && lg(gel(closure_get_dbg(g),3)) >= 2)
  {
    GEN v = closure_get_frame(g), d = gmael(closure_get_dbg(g),3,1);
    long i, l = lg(v), n=0;
    for(i=1; i<l; i++)
      if (gel(d,i))
        n++;
    if (n==0) return;
    str_puts(S,"my(");
    for(i=1; i<l; i++)
      if (gel(d,i))
      {
        entree *ep = (entree*) gel(d,i);
        str_puts(S,ep->name);
        str_putc(S,'=');
        if (tex) texi(gel(v,l-i),T,S); else bruti(gel(v,l-i),T,S);
        if (--n)
          str_putc(S,',');
      }
    str_puts(S,");");
  }
  else
  {
    GEN v = closure_get_frame(g);
    long i, l = lg(v), n  = closure_arity(g);
    str_puts(S,"(");
    for(i=1; i<=n; i++)
    {
      str_puts(S,"v");
      if (tex) str_puts(S,"_{");
      str_ulong(S,i);
      if (tex) str_puts(S,"}");
      str_puts(S,",");
    }
    for(i=1; i<l; i++)
    {
      if (tex) texi(gel(v,i),T,S); else bruti(gel(v,i),T,S);
      if (i<l-1)
        str_putc(S,',');
    }
    str_puts(S,")");
  }
}
static void
mat0n(pari_str *S, long n)
{ str_puts(S, "matrix(0,"); str_long(S, n); str_putc(S, ')'); }

static const char *
cxq_init(GEN g, long tg, GEN *a, GEN *b, char *buf)
{
  int r = (tg==t_QUAD);
  *a = gel(g,r+1);
  *b = gel(g,r+2); return r? get_var(varn(gel(g,1)), buf): "I";
}

static void
bruti_intern(GEN g, pariout_t *T, pari_str *S, int addsign)
{
  long l,i,j,r, tg = typ(g);
  GEN a,b;
  const char *v;
  char buf[32];

  switch(tg)
  {
    case t_INT:
      if (addsign && signe(g) < 0) str_putc(S, '-');
      str_absint(S, g); break;
    case t_REAL:
    {
      pari_sp av;
      str_alloc(S, lg(g)); /* careful! */
      av = avma;
      if (addsign && signe(g) < 0) str_putc(S, '-');
      str_puts(S, absrtostr(g, T->sp, (char)toupper((int)T->format), T->sigd) );
      avma = av; break;
    }

    case t_INTMOD: case t_POLMOD:
      str_puts(S, "Mod(");
      bruti(gel(g,2),T,S); comma_sp(T,S);
      bruti(gel(g,1),T,S); str_putc(S, ')'); break;

    case t_FFELT:
      bruti_sign(FF_to_FpXQ_i(g),T,S,addsign);
      break;

    case t_FRAC: case t_RFRAC:
      r = isfactor(gel(g,1)); if (!r) str_putc(S, '(');
      bruti_sign(gel(g,1),T,S,addsign);
      if (!r) str_putc(S, ')');
      str_putc(S, '/');
      r = isdenom(gel(g,2)); if (!r) str_putc(S, '(');
      bruti(gel(g,2),T,S);
      if (!r) str_putc(S, ')');
      break;

    case t_COMPLEX: case t_QUAD: r = (tg==t_QUAD);
      v = cxq_init(g, tg, &a, &b, buf);
      if (isnull(a))
      {
        wr_lead_monome(T,S,b,v,1,addsign);
        return;
      }
      bruti_sign(a,T,S,addsign);
      if (!isnull(b)) wr_monome(T,S,b,v,1);
      break;

    case t_POL: v = get_var(varn(g), buf);
      /* hack: we want g[i] = coeff of degree i. */
      i = degpol(g); g += 2; while (isnull(gel(g,i))) i--;
      wr_lead_monome(T,S,gel(g,i),v,i,addsign);
      while (i--)
      {
        a = gel(g,i);
        if (!isnull_for_pol(a)) wr_monome(T,S,a,v,i);
      }
      break;

    case t_SER: v = get_var(varn(g), buf);
      i = valp(g);
      l = lg(g)-2;
      if (l)
      {
        /* See normalize(): Mod(0,2)*x^i*(1+O(x)), has valp = i+1 */
        if (l == 1 && !signe(g) && isexactzero(gel(g,2))) i--;
        /* hack: we want g[i] = coeff of degree i */
        l += i; g -= i-2;
        wr_lead_monome(T,S,gel(g,i),v,i,addsign);
        while (++i < l)
        {
          a = gel(g,i);
          if (!isnull_for_pol(a)) wr_monome(T,S,a,v,i);
        }
        sp_sign_sp(T,S,1);
      }
      str_puts(S, "O("); VpowE(S, v, i); str_putc(S, ')'); break;

    case t_PADIC:
    {
      GEN p = gel(g,2);
      pari_sp av, av0;
      char *ev;
      str_alloc(S, (precp(g)+1) * lgefint(p)); /* careful! */
      av0 = avma;
      ev = itostr(p);
      av = avma;
      i = valp(g); l = precp(g)+i;
      g = gel(g,4);
      for (; i<l; i++)
      {
        g = dvmdii(g,p,&a);
        if (signe(a))
        {
          if (!i || !is_pm1(a))
          {
            str_absint(S, a); if (i) str_putc(S, '*');
          }
          if (i) VpowE(S, ev,i);
          sp_sign_sp(T,S,1);
        }
        if ((i & 0xff) == 0) g = gerepileuptoint(av,g);
      }
      str_puts(S, "O("); VpowE(S, ev,i); str_putc(S, ')');
      avma = av0; break;
    }

    case t_QFR: case t_QFI: r = (tg == t_QFR);
      str_puts(S, "Qfb(");
      bruti(gel(g,1),T,S); comma_sp(T,S);
      bruti(gel(g,2),T,S); comma_sp(T,S);
      bruti(gel(g,3),T,S);
      if (r) { comma_sp(T,S); bruti(gel(g,4),T,S); }
      str_putc(S, ')'); break;

    case t_VEC: case t_COL:
      str_putc(S, '['); l = lg(g);
      for (i=1; i<l; i++)
      {
        bruti(gel(g,i),T,S);
        if (i<l-1) comma_sp(T,S);
      }
      str_putc(S, ']'); if (tg==t_COL) str_putc(S, '~');
      break;
    case t_VECSMALL: wr_vecsmall(T,S,g); break;

    case t_LIST:
      switch (list_typ(g))
      {
      case t_LIST_RAW:
        str_puts(S, "List([");
        g = list_data(g);
        l = g? lg(g): 1;
        for (i=1; i<l; i++)
        {
          bruti(gel(g,i),T,S);
          if (i<l-1) comma_sp(T,S);
        }
        str_puts(S, "])"); break;
      case t_LIST_MAP:
        {
          pari_sp av;
          str_puts(S, "Map(");
          av = avma;
          bruti(maptomat_shallow(g),T,S);
          avma = av;
          str_puts(S, ")"); break;
        }
      }
      break;
    case t_STR:
      quote_string(S, GSTR(g)); break;
    case t_ERROR:
      {
        char *s = pari_err2str(g);
        str_puts(S, "error(");
        quote_string(S, s); pari_free(s);
        str_puts(S, ")"); break;
      }
    case t_CLOSURE:
      if (lg(g)>=7)
      {
        GEN str = closure_get_text(g);
        if (typ(str)==t_STR)
        {
          print_precontext(g, S, 0);
          str_puts(S, GSTR(str));
          print_context(g, T, S, 0);
        }
        else
        {
          str_putc(S,'(');   str_puts(S,GSTR(gel(str,1)));
          str_puts(S,")->");
          print_context(g, T, S, 0);
          str_puts(S,GSTR(gel(str,2)));
        }
      }
      else
      {
        str_puts(S,"{\""); str_puts(S,GSTR(closure_get_code(g)));
        str_puts(S,"\","); wr_vecsmall(T,S,closure_get_oper(g));
        str_putc(S,',');   bruti(gel(g,4),T,S);
        str_putc(S,',');   bruti(gel(g,5),T,S);
        str_putc(S,'}');
      }
      break;
    case t_INFINITY: str_puts(S, inf_get_sign(g) == 1? "+oo": "-oo");
      break;

    case t_MAT:
    {
      OUT_FUN print;

      r = lg(g); if (r==1) { str_puts(S, "[;]"); return; }
      l = lgcols(g); if (l==1) { mat0n(S, r-1); return; }
      print = (typ(gel(g,1)) == t_VECSMALL)? prints: bruti;
      if (l==2)
      {
        str_puts(S, "Mat(");
        if (r == 2) { print(gcoeff(g,1,1),T,S); str_putc(S, ')'); return; }
      }
      str_putc(S, '[');
      for (i=1; i<l; i++)
      {
        for (j=1; j<r; j++)
        {
          print(gcoeff(g,i,j),T,S);
          if (j<r-1) comma_sp(T,S);
        }
        if (i<l-1) semicolon_sp(T,S);
      }
      str_putc(S, ']'); if (l==2) str_putc(S, ')');
      break;
    }

    default: str_addr(S, *g);
  }
}

static void
bruti_sign(GEN g, pariout_t *T, pari_str *S, int addsign)
{
  if (!print_0_or_pm1(g, S, addsign))
    bruti_intern(g, T, S, addsign);
}

static void
matbruti(GEN g, pariout_t *T, pari_str *S)
{
  long i, j, r, w, l, *pad = NULL;
  pari_sp av;
  OUT_FUN print;

  if (typ(g) != t_MAT) { bruti(g,T,S); return; }

  r=lg(g); if (r==1) { str_puts(S, "[;]"); return; }
  l = lgcols(g); if (l==1) { mat0n(S, r-1); return; }
  str_putc(S, '\n');
  print = (typ(gel(g,1)) == t_VECSMALL)? prints: bruti;
  av = avma;
  w = term_width();
  if (2*r < w)
  {
    long lgall = 2; /* opening [ and closing ] */
    pari_sp av2;
    pari_str str;
    pad = cgetg(l*r+1, t_VECSMALL); /* left on stack if (S->use_stack)*/
    av2 = avma;
    str_init(&str, 1);
    for (j=1; j<r; j++)
    {
      GEN col = gel(g,j);
      long maxc = 0;
      for (i=1; i<l; i++)
      {
        long lgs;
        str.cur = str.string;
        print(gel(col,i),T,&str);
        lgs = str.cur - str.string;
        pad[j*l+i] = -lgs;
        if (maxc < lgs) maxc = lgs;
      }
      for (i=1; i<l; i++) pad[j*l+i] += maxc;
      lgall += maxc + 1; /* column width, including separating space */
      if (lgall > w) { pad = NULL; break; } /* doesn't fit, abort padding */
    }
    avma = av2;
  }
  for (i=1; i<l; i++)
  {
    str_putc(S, '[');
    for (j=1; j<r; j++)
    {
      if (pad) {
        long white = pad[j*l+i];
        while (white-- > 0) str_putc(S, ' ');
      }
      print(gcoeff(g,i,j),T,S); if (j<r-1) str_putc(S, ' ');
    }
    if (i<l-1) str_puts(S, "]\n\n"); else str_puts(S, "]\n");
  }
  if (!S->use_stack) avma = av;
}

/********************************************************************/
/**                                                                **/
/**                           TeX OUTPUT                           **/
/**                                                                **/
/********************************************************************/
/* this follows bruti_sign */
static void
texi_sign(GEN g, pariout_t *T, pari_str *S, int addsign)
{
  long tg,i,j,l,r;
  GEN a,b;
  const char *v;
  char buf[67];

  if (print_0_or_pm1(g, S, addsign)) return;

  tg = typ(g);
  switch(tg)
  {
    case t_INT: case t_REAL: case t_QFR: case t_QFI:
      bruti_intern(g, T, S, addsign); break;

    case t_INTMOD: case t_POLMOD:
      texi(gel(g,2),T,S); str_puts(S, " mod ");
      texi(gel(g,1),T,S); break;

    case t_FRAC:
      if (addsign && isfactor(gel(g,1)) < 0) str_putc(S, '-');
      str_puts(S, "\\frac{");
      texi_sign(gel(g,1),T,S,0);
      str_puts(S, "}{");
      texi_sign(gel(g,2),T,S,0);
      str_puts(S, "}"); break;

    case t_RFRAC:
      str_puts(S, "\\frac{");
      texi(gel(g,1),T,S); /* too complicated otherwise */
      str_puts(S, "}{");
      texi(gel(g,2),T,S);
      str_puts(S, "}"); break;

    case t_FFELT:
      bruti_sign(FF_to_FpXQ_i(g),T,S,addsign);
      break;

    case t_COMPLEX: case t_QUAD: r = (tg==t_QUAD);
      v = cxq_init(g, tg, &a, &b, buf);
      if (isnull(a))
      {
        wr_lead_texnome(T,S,b,v,1,addsign);
        break;
      }
      texi_sign(a,T,S,addsign);
      if (!isnull(b)) wr_texnome(T,S,b,v,1);
      break;

    case t_POL: v = get_texvar(varn(g), buf, sizeof(buf));
      /* hack: we want g[i] = coeff of degree i. */
      i = degpol(g); g += 2; while (isnull(gel(g,i))) i--;
      wr_lead_texnome(T,S,gel(g,i),v,i,addsign);
      while (i--)
      {
        a = gel(g,i);
        if (!isnull_for_pol(a)) wr_texnome(T,S,a,v,i);
      }
      break;

    case t_SER: v = get_texvar(varn(g), buf, sizeof(buf));
      i = valp(g);
      if (lg(g)-2)
      { /* hack: we want g[i] = coeff of degree i. */
        l = i + lg(g)-2; g -= i-2;
        wr_lead_texnome(T,S,gel(g,i),v,i,addsign);
        while (++i < l)
        {
          a = gel(g,i);
          if (!isnull_for_pol(a)) wr_texnome(T,S,a,v,i);
        }
        str_puts(S, "+ ");
      }
      str_puts(S, "O("); texnome(S,v,i); str_putc(S, ')'); break;

    case t_PADIC:
    {
      GEN p = gel(g,2);
      pari_sp av;
      char *ev;
      str_alloc(S, (precp(g)+1) * lgefint(p)); /* careful! */
      av = avma;
      i = valp(g); l = precp(g)+i;
      g = gel(g,4); ev = itostr(p);
      for (; i<l; i++)
      {
        g = dvmdii(g,p,&a);
        if (signe(a))
        {
          if (!i || !is_pm1(a))
          {
            str_absint(S, a); if (i) str_puts(S, "\\cdot");
          }
          if (i) texVpowE(S, ev,i);
          str_putc(S, '+');
        }
      }
      str_puts(S, "O("); texVpowE(S, ev,i); str_putc(S, ')');
      avma = av; break;
    }

    case t_VEC:
      str_puts(S, "\\pmatrix{ "); l = lg(g);
      for (i=1; i<l; i++)
      {
        texi(gel(g,i),T,S); if (i < l-1) str_putc(S, '&');
      }
      str_puts(S, "\\cr}\n"); break;

    case t_LIST:
      switch(list_typ(g))
      {
      case t_LIST_RAW:
        str_puts(S, "\\pmatrix{ ");
        g = list_data(g);
        l = g? lg(g): 1;
        for (i=1; i<l; i++)
        {
          texi(gel(g,i),T,S); if (i < l-1) str_putc(S, '&');
        }
        str_puts(S, "\\cr}\n"); break;
      case t_LIST_MAP:
        {
          pari_sp av = avma;
          texi(maptomat_shallow(g),T,S);
          avma = av;
          break;
        }
      }
      break;
    case t_COL:
      str_puts(S, "\\pmatrix{ "); l = lg(g);
      for (i=1; i<l; i++)
      {
        texi(gel(g,i),T,S); str_puts(S, "\\cr\n");
      }
      str_putc(S, '}'); break;

    case t_VECSMALL:
      str_puts(S, "\\pmatrix{ "); l = lg(g);
      for (i=1; i<l; i++)
      {
        str_long(S, g[i]);
        if (i < l-1) str_putc(S, '&');
      }
      str_puts(S, "\\cr}\n"); break;

    case t_STR:
      str_puts(S, GSTR(g)); break;

    case t_CLOSURE:
      if (lg(g)>=6)
      {
        GEN str = closure_get_text(g);
        if (typ(str)==t_STR)
        {
          print_precontext(g, S, 1);
          str_puts(S, GSTR(str));
          print_context(g, T, S ,1);
        }
        else
        {
          str_putc(S,'(');          str_puts(S,GSTR(gel(str,1)));
          str_puts(S,")\\mapsto ");
          print_context(g, T, S ,1); str_puts(S,GSTR(gel(str,2)));
        }
      }
      else
      {
        str_puts(S,"\\{\""); str_puts(S,GSTR(closure_get_code(g)));
        str_puts(S,"\","); texi(gel(g,3),T,S);
        str_putc(S,',');   texi(gel(g,4),T,S);
        str_putc(S,',');   texi(gel(g,5),T,S); str_puts(S,"\\}");
      }
      break;
    case t_INFINITY: str_puts(S, inf_get_sign(g) == 1? "+\\infty": "-\\infty");
      break;

    case t_MAT:
    {
      str_puts(S, "\\pmatrix{\n "); r = lg(g);
      if (r>1)
      {
        OUT_FUN print = (typ(gel(g,1)) == t_VECSMALL)? prints: texi;

        l = lgcols(g);
        for (i=1; i<l; i++)
        {
          for (j=1; j<r; j++)
          {
            print(gcoeff(g,i,j),T,S); if (j<r-1) str_putc(S, '&');
          }
          str_puts(S, "\\cr\n ");
        }
      }
      str_putc(S, '}'); break;
    }
  }
}

/*******************************************************************/
/**                                                               **/
/**                        USER OUTPUT FUNCTIONS                  **/
/**                                                               **/
/*******************************************************************/
static void
_initout(pariout_t *T, char f, long sigd, long sp)
{
  T->format = f;
  T->sigd = sigd;
  T->sp = sp;
}

static void
gen_output_fun(GEN x, pariout_t *T, OUT_FUN out)
{ pari_sp av = avma; pari_puts( stack_GENtostr_fun(x,T,out) ); avma = av; }

void
fputGEN_pariout(GEN x, pariout_t *T, FILE *out)
{
  pari_sp av = avma;
  char *s = stack_GENtostr_fun(x, T, get_fun(T->prettyp));
  if (*s) { set_last_newline(s[strlen(s)-1]); fputs(s, out); }
  avma = av;
}

void
brute(GEN g, char f, long d)
{
  pariout_t T; _initout(&T,f,d,0);
  gen_output_fun(g, &T, &bruti);
}
void
matbrute(GEN g, char f, long d)
{
  pariout_t T; _initout(&T,f,d,1);
  gen_output_fun(g, &T, &matbruti);
}
void
texe(GEN g, char f, long d)
{
  pariout_t T; _initout(&T,f,d,0);
  gen_output_fun(g, &T, &texi);
}

void
gen_output(GEN x)
{
  gen_output_fun(x, GP_DATA->fmt, get_fun(GP_DATA->fmt->prettyp));
  pari_putc('\n'); pari_flush();
}
void
output(GEN x)
{ brute(x,'g',-1); pari_putc('\n'); pari_flush(); }
void
outmat(GEN x)
{ matbrute(x,'g',-1); pari_putc('\n'); pari_flush(); }

/*******************************************************************/
/**                            FILES                              **/
/*******************************************************************/
/* to cache '~' expansion */
static char *homedir;
/* last file read successfully from try_name() */
static THREAD char *last_filename;
/* stack of temporary files (includes all infiles + some output) */
static THREAD pariFILE *last_tmp_file;
/* stack of "permanent" (output) files */
static THREAD pariFILE *last_file;

typedef struct gpfile
{
  const char *name;
  FILE *fp;
  int type;
  long serial;
} gpfile;

static THREAD gpfile *gp_file;
static THREAD pari_stack s_gp_file;
static THREAD long gp_file_serial;

#if defined(UNIX) || defined(__EMX__)
#  include <fcntl.h>
#  include <sys/stat.h> /* for open */
#  ifdef __EMX__
#    include <process.h>
#  endif
#  define HAVE_PIPES
#endif
#if defined(_WIN32)
#  define HAVE_PIPES
#endif
#ifndef O_RDONLY
#  define O_RDONLY 0
#endif

pariFILE *
newfile(FILE *f, const char *name, int type)
{
  pariFILE *file = (pariFILE*) pari_malloc(strlen(name) + 1 + sizeof(pariFILE));
  file->type = type;
  file->name = strcpy((char*)(file+1), name);
  file->file = f;
  file->next = NULL;
  if (type & mf_PERM)
  {
    file->prev = last_file;
    last_file = file;
  }
  else
  {
    file->prev = last_tmp_file;
    last_tmp_file = file;
  }
  if (file->prev) (file->prev)->next = file;
  if (DEBUGFILES)
    err_printf("I/O: new pariFILE %s (code %d) \n",name,type);
  return file;
}

static void
pari_kill_file(pariFILE *f)
{
  if ((f->type & mf_PIPE) == 0)
  {
    if (f->file != stdin && fclose(f->file))
      pari_warn(warnfile, "close", f->name);
  }
#ifdef HAVE_PIPES
  else
  {
    if (f->type & mf_FALSE)
    {
      if (f->file != stdin && fclose(f->file))
        pari_warn(warnfile, "close", f->name);
      if (unlink(f->name)) pari_warn(warnfile, "delete", f->name);
    }
    else
      if (pclose(f->file) < 0) pari_warn(warnfile, "close pipe", f->name);
  }
#endif
  if (DEBUGFILES)
    err_printf("I/O: closing file %s (code %d) \n",f->name,f->type);
  pari_free(f);
}

void
pari_fclose(pariFILE *f)
{
  if (f->next) (f->next)->prev = f->prev;
  else if (f == last_tmp_file) last_tmp_file = f->prev;
  else if (f == last_file) last_file = f->prev;
  if (f->prev) (f->prev)->next = f->next;
  pari_kill_file(f);
}

static pariFILE *
pari_open_file(FILE *f, const char *s, const char *mode)
{
  if (!f) pari_err_FILE("requested file", s);
  if (DEBUGFILES)
    err_printf("I/O: opening file %s (mode %s)\n", s, mode);
  return newfile(f,s,0);
}

pariFILE *
pari_fopen_or_fail(const char *s, const char *mode)
{
  return pari_open_file(fopen(s, mode), s, mode);
}
pariFILE *
pari_fopen(const char *s, const char *mode)
{
  FILE *f = fopen(s, mode);
  return f? pari_open_file(f, s, mode): NULL;
}

void
pari_fread_chars(void *b, size_t n, FILE *f)
{
  if (fread(b, sizeof(char), n, f) < n)
    pari_err_FILE("input file [fread]", "FILE*");
}

/* FIXME: HAS_FDOPEN & allow standard open() flags */
#ifdef UNIX
/* open tmpfile s (a priori for writing) avoiding symlink attacks */
pariFILE *
pari_safefopen(const char *s, const char *mode)
{
  long fd = open(s, O_CREAT|O_EXCL|O_RDWR, S_IRUSR|S_IWUSR);

  if (fd == -1) pari_err(e_MISC,"tempfile %s already exists",s);
  return pari_open_file(fdopen(fd, mode), s, mode);
}
#else
pariFILE *
pari_safefopen(const char *s, const char *mode)
{
  return pari_fopen_or_fail(s, mode);
}
#endif

void
pari_unlink(const char *s)
{
  if (unlink(s)) pari_warn(warner, "I/O: can\'t remove file %s", s);
  else if (DEBUGFILES)
    err_printf("I/O: removed file %s\n", s);
}

/* Remove one INFILE from the stack. Reset pari_infile (to the most recent
 * infile)
 * Return -1, if we're trying to pop out stdin itself; 0 otherwise
 * Check for leaked file handlers (temporary files) */
int
popinfile(void)
{
  pariFILE *f = last_tmp_file, *g;
  while (f)
  {
    if (f->type & mf_IN) break;
    pari_warn(warner, "I/O: leaked file descriptor (%d): %s", f->type, f->name);
    g = f; f = f->prev; pari_fclose(g);
  }
  last_tmp_file = f; if (!f) return -1;
  pari_fclose(last_tmp_file);
  for (f = last_tmp_file; f; f = f->prev)
    if (f->type & mf_IN) { pari_infile = f->file; return 0; }
  pari_infile = stdin; return 0;
}

/* delete all "temp" files open since last reference point F */
void
tmp_restore(pariFILE *F)
{
  pariFILE *f = last_tmp_file;
  if (DEBUGFILES>1) err_printf("gp_context_restore: deleting open files...\n");
  while (f)
  {
    pariFILE *g = f->prev;
    if (f == F) break;
    pari_fclose(f); f = g;
  }
  for (; f; f = f->prev) {
    if (f->type & mf_IN) {
      pari_infile = f->file;
      if (DEBUGFILES>1)
        err_printf("restoring pari_infile to %s\n", f->name);
      break;
    }
  }
  if (!f) {
    pari_infile = stdin;
    if (DEBUGFILES>1)
      err_printf("gp_context_restore: restoring pari_infile to stdin\n");
  }
  if (DEBUGFILES>1) err_printf("done\n");
}

void
filestate_save(struct pari_filestate *file)
{
  file->file = last_tmp_file;
  file->serial = gp_file_serial;
}

static void
filestate_close(long serial)
{
  long i;
  for (i = 0; i < s_gp_file.n; i++)
    if (gp_file[i].fp && gp_file[i].serial >= serial)
      gp_fileclose(i);
  gp_file_serial = serial;
}

void
filestate_restore(struct pari_filestate *file)
{
  tmp_restore(file->file);
  filestate_close(file->serial);
}

static void
kill_file_stack(pariFILE **s)
{
  pariFILE *f = *s;
  while (f)
  {
    pariFILE *t = f->prev;
    pari_kill_file(f);
    *s = f = t; /* have to update *s in case of ^C */
  }
}

void
killallfiles(void)
{
  kill_file_stack(&last_tmp_file);
  pari_infile = stdin;
}

void
pari_init_homedir(void)
{
  homedir = NULL;
}

void
pari_close_homedir(void)
{
  if (homedir) pari_free(homedir);
}

void
pari_init_files(void)
{
  last_filename = NULL;
  last_tmp_file = NULL;
  last_file=NULL;
  pari_stack_init(&s_gp_file, sizeof(*gp_file), (void**)&gp_file);
  gp_file_serial = 0;
}

void
pari_thread_close_files(void)
{
  popinfile(); /* look for leaks */
  kill_file_stack(&last_file);
  if (last_filename) pari_free(last_filename);
  kill_file_stack(&last_tmp_file);
  filestate_close(-1);
  pari_stack_delete(&s_gp_file);
}

void
pari_close_files(void)
{
  if (pari_logfile) { fclose(pari_logfile); pari_logfile = NULL; }
  pari_infile = stdin;
}

static int
ok_pipe(FILE *f)
{
  if (DEBUGFILES) err_printf("I/O: checking output pipe...\n");
  pari_CATCH(CATCH_ALL) {
    return 0;
  }
  pari_TRY {
    int i;
    fprintf(f,"\n\n"); fflush(f);
    for (i=1; i<1000; i++) fprintf(f,"                  \n");
    fprintf(f,"\n"); fflush(f);
  } pari_ENDCATCH;
  return 1;
}

pariFILE *
try_pipe(const char *cmd, int fl)
{
#ifndef HAVE_PIPES
  pari_err(e_ARCH,"pipes"); return NULL;
#else
  FILE *file;
  const char *f;
  VOLATILE int flag = fl;

#  ifdef __EMX__
  if (_osmode == DOS_MODE) /* no pipes under DOS */
  {
    pari_sp av = avma;
    char *s;
    if (flag & mf_OUT) pari_err(e_ARCH,"pipes");
    f = pari_unique_filename("pipe");
    s = stack_malloc(strlen(cmd)+strlen(f)+4);
    sprintf(s,"%s > %s",cmd,f);
    file = system(s)? NULL: fopen(f,"r");
    flag |= mf_FALSE; pari_free(f); avma = av;
  }
  else
#  endif
  {
    file = (FILE *) popen(cmd, (flag & mf_OUT)? "w": "r");
    if (flag & mf_OUT) {
      if (!ok_pipe(file)) return NULL;
      flag |= mf_PERM;
    }
    f = cmd;
  }
  if (!file) pari_err(e_MISC,"[pipe:] '%s' failed",cmd);
  return newfile(file, f, mf_PIPE|flag);
#endif
}

char *
os_getenv(const char *s)
{
#ifdef HAS_GETENV
  return getenv(s);
#else
  (void) s; return NULL;
#endif
}

GEN
gp_getenv(const char *s)
{
  char *t = os_getenv(s);
  return t?strtoGENstr(t):gen_0;
}

/* FIXME: HAS_GETPWUID */
#if defined(UNIX) || defined(__EMX__)
#include <pwd.h>
#include <sys/types.h>
/* user = "": use current uid */
char *
pari_get_homedir(const char *user)
{
  struct passwd *p;
  char *dir = NULL;

  if (!*user)
  {
    if (homedir) dir = homedir;
    else
    {
      p = getpwuid(geteuid());
      if (p)
      {
        dir = p->pw_dir;
        homedir = pari_strdup(dir); /* cache result */
      }
    }
  }
  else
  {
    p = getpwnam(user);
    if (p) dir = p->pw_dir;
    /* warn, but don't kill session on startup (when expanding path) */
    if (!dir) pari_warn(warner,"can't expand ~%s", user? user: "");
  }
  return dir;
}
#else
char *
pari_get_homedir(const char *user) { (void) user; return NULL; }
#endif

/*******************************************************************/
/**                                                               **/
/**                   GP STANDARD INPUT AND OUTPUT                **/
/**                                                               **/
/*******************************************************************/
#ifdef HAS_OPENDIR
/* slow, but more portable than stat + S_ISDIR */
static int
is_dir_opendir(const char *name)
{
  DIR *d = opendir(name);
  if (d) { (void)closedir(d); return 1; }
  return 0;
}
#endif

#ifdef HAS_STAT
static int
is_dir_stat(const char *name)
{
  struct stat buf;
  if (stat(name, &buf)) return 0;
  return S_ISDIR(buf.st_mode);
}
#endif

/* Does name point to a directory? */
int
pari_is_dir(const char *name)
{
#ifdef HAS_STAT
  return is_dir_stat(name);
#else
#  ifdef HAS_OPENDIR
  return is_dir_opendir(name);
#  else
  (void) name; return 0;
#  endif
#endif
}

/* Does name point to a regular file? */
/* If unknown, assume that it is indeed regular. */
int
pari_is_file(const char *name)
{
#ifdef HAS_STAT
  struct stat buf;
  if (stat(name, &buf)) return 1;
  return S_ISREG(buf.st_mode);
#else
  (void) name; return 1;
#endif
}

int
pari_stdin_isatty(void)
{
#ifdef HAS_ISATTY
  return isatty( fileno(stdin) );
#else
  return 1;
#endif
}

/* expand tildes in filenames, return a malloc'ed buffer */
static char *
_path_expand(const char *s)
{
  const char *t;
  char *ret, *dir = NULL;

  if (*s != '~') return pari_strdup(s);
  s++; /* skip ~ */
  t = s; while (*t && *t != '/') t++;
  if (t == s)
    dir = pari_get_homedir("");
  else
  {
    size_t len = t - s;
    char *user = (char*)pari_malloc(len+1);
    (void)memcpy(user,s,len); user[len] = 0;
    dir = pari_get_homedir(user);
    pari_free(user);
  }
  if (!dir) return pari_strdup(s);
  ret = (char*)pari_malloc(strlen(dir) + strlen(t) + 1);
  sprintf(ret,"%s%s",dir,t); return ret;
}

/* expand environment variables in str, return a malloc'ed buffer
 * assume no \ remain and str can be freed */
static char *
_expand_env(char *str)
{
  long i, l, len = 0, xlen = 16, xnum = 0;
  char *s = str, *s0 = s, *env;
  char **x = (char **)pari_malloc(xlen * sizeof(char*));

  while (*s)
  {
    if (*s != '$') { s++; continue; }
    l = s - s0;
    if (l)
    {
      s0 = (char*)memcpy(pari_malloc(l+1), s0, l); s0[l] = 0;
      x[xnum++] = s0; len += l;
    }
    if (xnum > xlen - 3) /* need room for possibly two more elts */
    {
      xlen <<= 1;
      x = (char **)pari_realloc((void*)x, xlen * sizeof(char*));
    }

    s0 = ++s; /* skip $ */
    while (is_keyword_char(*s)) s++;
    l = s - s0;
    env = (char*)memcpy(pari_malloc(l+1), s0, l); env[l] = 0;
    s0 = os_getenv(env);
    if (!s0)
    {
      pari_warn(warner,"undefined environment variable: %s",env);
      s0 = (char*)"";
    }
    l = strlen(s0);
    if (l)
    {
      s0 = (char*)memcpy(pari_malloc(l+1), s0, l); s0[l] = 0;
      x[xnum++] = s0; len += l;
    }
    pari_free(env); s0 = s;
  }
  l = s - s0;
  if (l)
  {
    s0 = (char*)memcpy(pari_malloc(l+1), s0, l); s0[l] = 0;
    x[xnum++] = s0; len += l;
  }

  s = (char*)pari_malloc(len+1); *s = 0;
  for (i = 0; i < xnum; i++) { (void)strcat(s, x[i]); pari_free(x[i]); }
  pari_free(str); pari_free(x); return s;
}

char *
path_expand(const char *s)
{
#ifdef _WIN32
  char *ss, *p;
  ss = pari_strdup(s);
  for (p = ss; *p != 0; ++p)
    if (*p == '\\') *p = '/';
  p = _expand_env(_path_expand(ss));
  pari_free(ss);
  return p;
#else
  return _expand_env(_path_expand(s));
#endif
}

#ifdef HAS_STRFTIME
#  include <time.h>
void
strftime_expand(const char *s, char *buf, long max)
{
  time_t t;
  BLOCK_SIGINT_START
  t = time(NULL);
  (void)strftime(buf,max,s,localtime(&t));
  BLOCK_SIGINT_END
}
#else
void
strftime_expand(const char *s, char *buf, long max)
{ strcpy(buf,s); }
#endif

/* name is a malloc'ed (existing) filename. Accept it as new pari_infile
 * (unzip if needed). */
static pariFILE *
pari_get_infile(const char *name, FILE *file)
{
#ifdef ZCAT
  long l = strlen(name);
  const char *end = name + l-1;

  if (l > 2 && (!strncmp(end-1,".Z",2)
#ifdef GNUZCAT
             || !strncmp(end-2,".gz",3)
#endif
  ))
  { /* compressed file (compress or gzip) */
    char *cmd = stack_malloc(strlen(ZCAT) + l + 4);
    sprintf(cmd,"%s \"%s\"",ZCAT,name);
    fclose(file);
    return try_pipe(cmd, mf_IN);
  }
#endif
  return newfile(file, name, mf_IN);
}

pariFILE *
pari_fopengz(const char *s)
{
  pari_sp av = avma;
  char *name;
  long l;
  FILE *f = fopen(s, "r");
  pariFILE *pf;

  if (f) return pari_get_infile(s, f);

#ifdef __EMSCRIPTEN__
  if (pari_is_dir(pari_datadir)) pari_emscripten_wget(s);
#endif
  l = strlen(s);
  name = stack_malloc(l + 3 + 1);
  strcpy(name, s); (void)sprintf(name + l, ".gz");
  f = fopen(name, "r");
  pf = f ? pari_get_infile(name, f): NULL;
  avma = av; return pf;
}

static FILE*
try_open(char *s)
{
  if (!pari_is_dir(s)) return fopen(s, "r");
  pari_warn(warner,"skipping directory %s",s);
  return NULL;
}

void
forpath_init(forpath_t *T, gp_path *path, const char *s)
{
  T->s = s;
  T->ls = strlen(s);
  T->dir = path->dirs;
}
char *
forpath_next(forpath_t *T)
{
  char *t, *dir = T->dir[0];

  if (!dir) return NULL; /* done */
  /* room for dir + '/' + s + '\0' */
  t = (char*)pari_malloc(strlen(dir) + T->ls + 2);
  sprintf(t,"%s/%s", dir, T->s);
  T->dir++; return t;
}

/* If a file called "name" exists (possibly after appending ".gp")
 * record it in the file_stack (as a pipe if compressed).
 * name is malloc'ed, we free it before returning
 */
static FILE *
try_name(char *name)
{
  pari_sp av = avma;
  char *s = name;
  FILE *file = try_open(name);

  if (!file)
  { /* try appending ".gp" to name */
    s = stack_malloc(strlen(name)+4);
    sprintf(s, "%s.gp", name);
    file = try_open(s);
  }
  if (file)
  {
    if (! last_tmp_file)
    {  /* empty file stack, record this name */
      if (last_filename) pari_free(last_filename);
      last_filename = pari_strdup(s);
    }
    file = pari_infile = pari_get_infile(s,file)->file;
  }
  pari_free(name); avma = av;
  return file;
}
static FILE *
switchin_last(void)
{
  char *s = last_filename;
  FILE *file;
  if (!s) pari_err(e_MISC,"You never gave me anything to read!");
  file = try_open(s);
  if (!file) pari_err_FILE("input file",s);
  return pari_infile = pari_get_infile(s,file)->file;
}

/* return 1 if s starts by '/' or './' or '../' */
static int
path_is_absolute(char *s)
{
#ifdef _WIN32
  if( (*s >= 'A' && *s <= 'Z') ||
      (*s >= 'a' && *s <= 'z') )
  {
      return *(s+1) == ':';
  }
#endif
  if (*s == '/') return 1;
  if (*s++ != '.') return 0;
  if (*s == '/') return 1;
  if (*s++ != '.') return 0;
  return *s == '/';
}

/* If name = "", re-read last file */
FILE *
switchin(const char *name)
{
  FILE *f;
  char *s;

  if (!*name) return switchin_last();
  s = path_expand(name);
  /* if s is an absolute path, don't use dir_list */
  if (path_is_absolute(s)) { if ((f = try_name(s))) return f; }
  else
  {
    char *t;
    forpath_t T;
    forpath_init(&T, GP_DATA->path, s);
    while ( (t = forpath_next(&T)) )
      if ((f = try_name(t))) { pari_free(s); return f; }
    pari_free(s);
  }
  pari_err_FILE("input file",name);
  return NULL; /*LCOV_EXCL_LINE*/
}

static int is_magic_ok(FILE *f);

static FILE *
switchout_get_FILE(const char *name)
{
  FILE* f;
  /* only for ordinary files (to avoid blocking on pipes). */
  if (pari_is_file(name))
  {
    f = fopen(name, "r");
    if (f)
    {
      int magic = is_magic_ok(f);
      fclose(f);
      if (magic) pari_err_FILE("binary output file [ use writebin ! ]", name);
    }
  }
  f = fopen(name, "a");
  if (!f) pari_err_FILE("output file",name);
  return f;
}

void
switchout(const char *name)
{
  if (name)
    pari_outfile = switchout_get_FILE(name);
  else if (pari_outfile != stdout)
  {
    fclose(pari_outfile);
    pari_outfile = stdout;
  }
}

/*******************************************************************/
/**                                                               **/
/**                SYSTEM, READSTR/EXTERNSTR/EXTERN               **/
/**                                                               **/
/*******************************************************************/
static void
check_secure(const char *s)
{
  if (GP_DATA->secure)
    pari_err(e_MISC, "[secure mode]: system commands not allowed\nTried to run '%s'",s);
}

void
gpsystem(const char *s)
{
#ifdef HAS_SYSTEM
  check_secure(s);
  if (system(s) < 0)
    pari_err(e_MISC, "system(\"%s\") failed", s);
#else
  pari_err(e_ARCH,"system");
#endif
}

static GEN
get_lines(FILE *F)
{
  pari_sp av = avma;
  long i, nz = 16;
  GEN z = cgetg(nz + 1, t_VEC);
  Buffer *b = new_buffer();
  input_method IM;
  IM.fgets = (fgets_t)&fgets;
  IM.file = (void*)F;
  for(i = 1;;)
  {
    char *s = b->buf, *e;
    if (!file_getline(b, &s, &IM)) break;
    if (i > nz) { nz <<= 1; z = vec_lengthen(z, nz); }
    e = s + strlen(s)-1;
    if (*e == '\n') *e = 0;
    gel(z,i++) = strtoGENstr(s);
  }
  delete_buffer(b); setlg(z, i);
  return gerepilecopy(av, z);
}

GEN
externstr(const char *s)
{
  pariFILE *F;
  GEN z;
  check_secure(s);
  F = try_pipe(s, mf_IN);
  z = get_lines(F->file);
  pari_fclose(F); return z;
}
GEN
gpextern(const char *s)
{
  pariFILE *F;
  GEN z;
  check_secure(s);
  F = try_pipe(s, mf_IN);
  z = gp_read_stream(F->file);
  pari_fclose(F); return z;
}

GEN
readstr(const char *s)
{
  GEN z = get_lines(switchin(s));
  popinfile(); return z;
}

/*******************************************************************/
/**                                                               **/
/**                    I/O IN BINARY FORM                         **/
/**                                                               **/
/*******************************************************************/
static void
pari_fread_longs(void *a, size_t c, FILE *d)
{ if (fread(a,sizeof(long),c,d) < c)
    pari_err_FILE("input file [fread]", "FILE*"); }

static void
_fwrite(const void *a, size_t b, size_t c, FILE *d)
{ if (fwrite(a,b,c,d) < c) pari_err_FILE("output file [fwrite]", "FILE*"); }
static void
_lfwrite(const void *a, size_t b, FILE *c) { _fwrite(a,sizeof(long),b,c); }
static void
_cfwrite(const void *a, size_t b, FILE *c) { _fwrite(a,sizeof(char),b,c); }

enum { BIN_GEN, NAM_GEN, VAR_GEN, RELINK_TABLE };

static long
rd_long(FILE *f) { long L; pari_fread_longs(&L, 1UL, f); return L; }
static void
wr_long(long L, FILE *f) { _lfwrite(&L, 1UL, f); }

/* append x to file f */
static void
wrGEN(GEN x, FILE *f)
{
  GENbin *p = copy_bin_canon(x);
  size_t L = p->len;

  wr_long(L,f);
  if (L)
  {
    wr_long((long)p->x,f);
    wr_long((long)p->base,f);
    _lfwrite(GENbinbase(p), L,f);
  }
  pari_free((void*)p);
}

static void
wrstr(const char *s, FILE *f)
{
  size_t L = strlen(s)+1;
  wr_long(L,f);
  _cfwrite(s, L, f);
}

static char *
rdstr(FILE *f)
{
  size_t L = (size_t)rd_long(f);
  char *s;
  if (!L) return NULL;
  s = (char*)pari_malloc(L);
  pari_fread_chars(s, L, f); return s;
}

static void
writeGEN(GEN x, FILE *f)
{
  fputc(BIN_GEN,f);
  wrGEN(x, f);
}

static void
writenamedGEN(GEN x, const char *s, FILE *f)
{
  fputc(x ? NAM_GEN : VAR_GEN,f);
  wrstr(s, f);
  if (x) wrGEN(x, f);
}

/* read a GEN from file f */
static GEN
rdGEN(FILE *f)
{
  size_t L = (size_t)rd_long(f);
  GENbin *p;

  if (!L) return gen_0;
  p = (GENbin*)pari_malloc(sizeof(GENbin) + L*sizeof(long));
  p->len  = L;
  p->x    = (GEN)rd_long(f);
  p->base = (GEN)rd_long(f);
  p->rebase = &shiftaddress_canon;
  pari_fread_longs(GENbinbase(p), L,f);
  return bin_copy(p);
}

/* read a binary object in file f. Set *ptc to the object "type":
 * BIN_GEN: an anonymous GEN x; return x.
 * NAM_GEN: a named GEN x, with name v; set 'v to x (changevalue) and return x
 * VAR_GEN: a name v; create the (unassigned) variable v and return gnil
 * RELINK_TABLE: a relinking table for gen_relink(), to replace old adresses
 * in * the original session by new incarnations in the current session.
 * H is the current relinking table
 * */
static GEN
readobj(FILE *f, int *ptc, hashtable *H)
{
  int c = fgetc(f);
  GEN x = NULL;
  switch(c)
  {
    case BIN_GEN:
      x = rdGEN(f);
      if (H) gen_relink(x, H);
      break;
    case NAM_GEN:
    case VAR_GEN:
    {
      char *s = rdstr(f);
      if (!s) pari_err(e_MISC,"malformed binary file (no name)");
      if (c == NAM_GEN)
      {
        x = rdGEN(f);
        if (H) gen_relink(x, H);
        err_printf("setting %s\n",s);
        changevalue(varentries[fetch_user_var(s)], x);
      }
      else
      {
        pari_var_create(fetch_entry(s));
        x = gnil;
      }
      break;
    }
    case RELINK_TABLE:
      x = rdGEN(f); break;
    case EOF: break;
    default: pari_err(e_MISC,"unknown code in readobj");
  }
  *ptc = c; return x;
}

#define MAGIC "\020\001\022\011-\007\020" /* ^P^A^R^I-^G^P */
#ifdef LONG_IS_64BIT
#  define ENDIAN_CHECK 0x0102030405060708L
#else
#  define ENDIAN_CHECK 0x01020304L
#endif
static const long BINARY_VERSION = 1; /* since 2.2.9 */

static int
is_magic_ok(FILE *f)
{
  pari_sp av = avma;
  size_t L = strlen(MAGIC);
  char *s = stack_malloc(L);
  int r = (fread(s,1,L, f) == L && strncmp(s,MAGIC,L) == 0);
  avma = av; return r;
}

static int
is_sizeoflong_ok(FILE *f)
{
  char c;
  return (fread(&c,1,1, f) == 1 && c == (char)sizeof(long));
}

static int
is_long_ok(FILE *f, long L)
{
  long c;
  return (fread(&c,sizeof(long),1, f) == 1 && c == L);
}

/* return 1 if valid binary file */
static int
check_magic(const char *name, FILE *f)
{
  if (!is_magic_ok(f))
    pari_warn(warner, "%s is not a GP binary file",name);
  else if (!is_sizeoflong_ok(f))
    pari_warn(warner, "%s not written for a %ld bit architecture",
               name, sizeof(long)*8);
  else if (!is_long_ok(f, ENDIAN_CHECK))
    pari_warn(warner, "unexpected endianness in %s",name);
  else if (!is_long_ok(f, BINARY_VERSION))
    pari_warn(warner, "%s written by an incompatible version of GP",name);
  else return 1;
  return 0;
}

static void
write_magic(FILE *f)
{
  fprintf(f, MAGIC);
  fprintf(f, "%c", (char)sizeof(long));
  wr_long(ENDIAN_CHECK, f);
  wr_long(BINARY_VERSION, f);
}

int
file_is_binary(FILE *f)
{
  int r, c = fgetc(f);
  ungetc(c,f);
  r = (c != EOF && isprint(c) == 0 && isspace(c) == 0);
#ifdef _WIN32
  if (r) { setmode(fileno(f), _O_BINARY); rewind(f); }
#endif
  return r;
}

void
writebin(const char *name, GEN x)
{
  FILE *f = fopen(name,"rb");
  pari_sp av = avma;
  GEN V;
  int already = f? 1: 0;

  if (f) {
    int ok = check_magic(name,f);
    fclose(f);
    if (!ok) pari_err_FILE("binary output file",name);
  }
  f = fopen(name,"ab");
  if (!f) pari_err_FILE("binary output file",name);
  if (!already) write_magic(f);

  V = copybin_unlink(x);
  if (lg(gel(V,1)) > 1)
  {
    fputc(RELINK_TABLE,f);
    wrGEN(V, f);
  }
  if (x) writeGEN(x,f);
  else
  {
    long v, maxv = pari_var_next();
    for (v=0; v<maxv; v++)
    {
      entree *ep = varentries[v];
      if (!ep) continue;
      writenamedGEN((GEN)ep->value,ep->name,f);
    }
  }
  avma = av; fclose(f);
}

/* read all objects in f. If f contains BIN_GEN that would be silently ignored
 * [i.e f contains more than one objet, not all of them 'named GENs'], return
 * them all in a vector and set 'vector'. */
GEN
readbin(const char *name, FILE *f, int *vector)
{
  pari_sp av = avma;
  hashtable *H = NULL;
  pari_stack s_obj;
  GEN obj, x, y;
  int cy;
  if (vector) *vector = 0;
  if (!check_magic(name,f)) return NULL;
  pari_stack_init(&s_obj, sizeof(GEN), (void**)&obj);
  /* HACK: push codeword so as to be able to treat s_obj.data as a t_VEC */
  pari_stack_pushp(&s_obj, (void*) (evaltyp(t_VEC)|evallg(1)));
  x = gnil;
  while ((y = readobj(f, &cy, H)))
  {
    x = y;
    switch(cy)
    {
      case BIN_GEN:
        pari_stack_pushp(&s_obj, (void*)y); break;
      case RELINK_TABLE:
        if (H) hash_destroy(H);
        H = hash_from_link(gel(y,1),gel(y,2), 0);
    }
  }
  if (H) hash_destroy(H);
  switch(s_obj.n) /* >= 1 */
  {
    case 1: break; /* nothing but the codeword */
    case 2: x = gel(obj,1); break; /* read a single BIN_GEN */
    default: /* more than one BIN_GEN */
      setlg(obj, s_obj.n);
      if (DEBUGLEVEL)
        pari_warn(warner,"%ld unnamed objects read. Returning then in a vector",
                  s_obj.n - 1);
      x = gerepilecopy(av, obj);
      if (vector) *vector = 1;
  }
  pari_stack_delete(&s_obj);
  return x;
}

/*******************************************************************/
/**                                                               **/
/**                             GP I/O                            **/
/**                                                               **/
/*******************************************************************/
/* print a vector of GENs, in output context 'out', using 'sep' as a
 * separator between sucessive entries [ NULL = no separator ]*/
void
out_print0(PariOUT *out, const char *sep, GEN g, long flag)
{
  pari_sp av = avma;
  OUT_FUN f = get_fun(flag);
  long i, l = lg(g);
  for (i = 1; i < l; i++, avma = av)
  {
    out_puts(out, stack_GENtostr_fun_unquoted(gel(g,i), GP_DATA->fmt, f));
    if (sep && i+1 < l) out_puts(out, sep);
  }
}
static void
str_print0(pari_str *S, GEN g, long flag)
{
  pari_sp av = avma;
  OUT_FUN f = get_fun(flag);
  long i, l = lg(g);
  for (i = 1; i < l; i++)
  {
    GEN x = gel(g,i);
    if (typ(x) == t_STR) str_puts(S, GSTR(x)); else f(x, GP_DATA->fmt, S);
    if (!S->use_stack) avma = av;
  }
  *(S->cur) = 0;
}

/* see print0(). Returns pari_malloc()ed string */
char *
RgV_to_str(GEN g, long flag)
{
  pari_str S; str_init(&S,0);
  str_print0(&S, g, flag);
  return S.string;
}

static GEN
Str_fun(GEN g, long flag) {
  char *t = RgV_to_str(g, flag);
  GEN z = strtoGENstr(t);
  pari_free(t); return z;
}
GEN Str(GEN g)    { return Str_fun(g, f_RAW); }
GEN Strtex(GEN g) { return Str_fun(g, f_TEX); }
GEN
Strexpand(GEN g) {
  char *s = RgV_to_str(g, f_RAW), *t = path_expand(s);
  GEN z = strtoGENstr(t);
  pari_free(t); pari_free(s); return z;
}

/* display s, followed by the element of g */
char *
pari_sprint0(const char *s, GEN g, long flag)
{
  pari_str S; str_init(&S, 0);
  str_puts(&S, s);
  str_print0(&S, g, flag);
  return S.string;
}

static void
print0_file(FILE *out, GEN g, long flag)
{
  pari_sp av = avma;
  pari_str S; str_init(&S, 1);
  str_print0(&S, g, flag);
  fputs(S.string, out);
  avma = av;
}

void
print0(GEN g, long flag) { out_print0(pariOut, NULL, g, flag); }
void
printsep(const char *s, GEN g)
{ out_print0(pariOut, s, g, f_RAW); pari_putc('\n'); pari_flush(); }
void
printsep1(const char *s, GEN g)
{ out_print0(pariOut, s, g, f_RAW); pari_flush(); }

static char *
sm_dopr(const char *fmt, GEN arg_vector, va_list args)
{
  pari_str s; str_init(&s, 0);
  str_arg_vprintf(&s, fmt, arg_vector, args);
  return s.string;
}
char *
pari_vsprintf(const char *fmt, va_list ap)
{ return sm_dopr(fmt, NULL, ap); }

/* dummy needed to pass an empty va_list to sm_dopr */
static char *
dopr_arg_vector(GEN arg_vector, const char* fmt, ...)
{
  va_list ap;
  char *s;
  va_start(ap, fmt);
  s = sm_dopr(fmt, arg_vector, ap);
  va_end(ap); return s;
}
/* GP only */
void
printf0(const char *fmt, GEN args)
{ char *s = dopr_arg_vector(args, fmt);
  pari_puts(s); pari_free(s); pari_flush(); }
/* GP only */
GEN
Strprintf(const char *fmt, GEN args)
{ char *s = dopr_arg_vector(args, fmt);
  GEN z = strtoGENstr(s); pari_free(s); return z; }

void
out_vprintf(PariOUT *out, const char *fmt, va_list ap)
{
  char *s = pari_vsprintf(fmt, ap);
  out_puts(out, s); pari_free(s);
}
void
pari_vprintf(const char *fmt, va_list ap) { out_vprintf(pariOut, fmt, ap); }

void
err_printf(const char* fmt, ...)
{
  va_list args; va_start(args, fmt);
  out_vprintf(pariErr,fmt,args); va_end(args);
}

/* variadic version of printf0 */
void
out_printf(PariOUT *out, const char *fmt, ...)
{
  va_list args; va_start(args,fmt);
  out_vprintf(out,fmt,args); va_end(args);
}
void
pari_printf(const char *fmt, ...) /* variadic version of printf0 */
{
  va_list args; va_start(args,fmt);
  pari_vprintf(fmt,args); va_end(args);
}

GEN
gvsprintf(const char *fmt, va_list ap)
{
  char *s = pari_vsprintf(fmt, ap);
  GEN z = strtoGENstr(s);
  pari_free(s); return z;
}

char *
pari_sprintf(const char *fmt, ...) /* variadic version of Strprintf */
{
  char *s;
  va_list ap;
  va_start(ap, fmt);
  s = pari_vsprintf(fmt, ap);
  va_end(ap); return s;
}

void
str_printf(pari_str *S, const char *fmt, ...)
{
  va_list ap; va_start(ap, fmt);
  str_arg_vprintf(S, fmt, NULL, ap);
  va_end(ap);
}

char *
stack_sprintf(const char *fmt, ...)
{
  char *s, *t;
  va_list ap;
  va_start(ap, fmt);
  s = pari_vsprintf(fmt, ap);
  va_end(ap);
  t = stack_strdup(s);
  pari_free(s); return t;
}

GEN
gsprintf(const char *fmt, ...) /* variadic version of gvsprintf */
{
  GEN s;
  va_list ap;
  va_start(ap, fmt);
  s = gvsprintf(fmt, ap);
  va_end(ap); return s;
}

/* variadic version of fprintf0. FIXME: fprintf0 not yet available */
void
pari_vfprintf(FILE *file, const char *fmt, va_list ap)
{
  char *s = pari_vsprintf(fmt, ap);
  fputs(s, file); pari_free(s);
}
void
pari_fprintf(FILE *file, const char *fmt, ...)
{
  va_list ap; va_start(ap, fmt);
  pari_vfprintf(file, fmt, ap); va_end(ap);
}

void print   (GEN g) { print0(g, f_RAW);       pari_putc('\n'); pari_flush(); }
void printp  (GEN g) { print0(g, f_PRETTYMAT); pari_putc('\n'); pari_flush(); }
void printtex(GEN g) { print0(g, f_TEX);       pari_putc('\n'); pari_flush(); }
void print1  (GEN g) { print0(g, f_RAW);       pari_flush(); }

void
error0(GEN g)
{
  if (lg(g)==2 && typ(gel(g,1))==t_ERROR) pari_err(0, gel(g,1));
  else pari_err(e_USER, g);
}

void warning0(GEN g) { pari_warn(warnuser, g); }

static char *
wr_check(const char *s) {
  char *t = path_expand(s);
  if (GP_DATA->secure)
  {
    char *msg = pari_sprintf("[secure mode]: about to write to '%s'",t);
    pari_ask_confirm(msg);
    pari_free(msg);
  }
  return t;
}

/* write to file s */
static void
wr(const char *s, GEN g, long flag, int addnl)
{
  char *t = wr_check(s);
  FILE *out = switchout_get_FILE(t);
  pari_free(t);
  print0_file(out, g, flag);
  if (addnl) fputc('\n', out);
  fflush(out);
  if (fclose(out)) pari_warn(warnfile, "close", t);
}
void write0  (const char *s, GEN g) { wr(s, g, f_RAW, 1); }
void writetex(const char *s, GEN g) { wr(s, g, f_TEX, 1); }
void write1  (const char *s, GEN g) { wr(s, g, f_RAW, 0); }
void gpwritebin(const char *s, GEN x) { char *t=wr_check(s); writebin(t, x); pari_free(t);}

/*******************************************************************/
/**                                                               **/
/**                       HISTORY HANDLING                        **/
/**                                                               **/
/*******************************************************************/
/* history management function:
 *   p > 0, called from %p or %#p
 *   p <= 0, called from %` or %#` (|p| backquotes, possibly 0) */
static gp_hist_cell *
history(long p)
{
  gp_hist *H = GP_DATA->hist;
  ulong t = H->total, s = H->size;
  gp_hist_cell *c;

  if (!t) pari_err(e_MISC,"The result history is empty");

  if (p <= 0) p += t; /* count |p| entries starting from last */
  if (p <= 0 || p <= (long)(t - s) || (ulong)p > t)
  {
    long pmin = (long)(t - s) + 1;
    if (pmin <= 0) pmin = 1;
    pari_err(e_MISC,"History result %%%ld not available [%%%ld-%%%lu]",
             p,pmin,t);
  }
  c = H->v + ((p-1) % s);
  if (!c->z)
    pari_err(e_MISC,"History result %%%ld has been deleted (histsize changed)", p);
  return c;
}
GEN
pari_get_hist(long p) { return history(p)->z; }
long
pari_get_histtime(long p) { return history(p)->t; }

void
pari_add_hist(GEN x, long time)
{
  gp_hist *H = GP_DATA->hist;
  ulong i = H->total % H->size;
  H->total++;
  if (H->v[i].z) gunclone(H->v[i].z);
  H->v[i].t = time;
  H->v[i].z = gclone(x);
}

ulong
pari_nb_hist(void)
{
  return GP_DATA->hist->total;
}

/*******************************************************************/
/**                                                               **/
/**                       TEMPORARY FILES                         **/
/**                                                               **/
/*******************************************************************/

#ifndef R_OK
#  define R_OK 4
#  define W_OK 2
#  define X_OK 1
#  define F_OK 0
#endif

#ifdef __EMX__
#include <io.h>
static int
unix_shell(void)
{
  char *base, *sh = getenv("EMXSHELL");
  if (!sh) {
    sh = getenv("COMSPEC");
    if (!sh) return 0;
  }
  base = _getname(sh);
  return (stricmp (base, "cmd.exe") && stricmp (base, "4os2.exe")
       && stricmp (base, "command.com") && stricmp (base, "4dos.com"));
}
#endif

/* check if s has rwx permissions for us */
static int
pari_is_rwx(const char *s)
{
/* FIXME: HAS_ACCESS */
#if defined(UNIX) || defined (__EMX__)
  return access(s, R_OK | W_OK | X_OK) == 0;
#else
  (void) s; return 1;
#endif
}

#if defined(UNIX) || defined (__EMX__)
#include <sys/types.h>
#include <sys/stat.h>
static int
pari_file_exists(const char *s)
{
  int id = open(s, O_CREAT|O_EXCL|O_RDWR, S_IRUSR|S_IWUSR);
  return id < 0 || close(id);
}
static int
pari_dir_exists(const char *s) { return mkdir(s, 0777); }
#elif defined(_WIN32)
static int
pari_file_exists(const char *s) { return GetFileAttributesA(s) != ~0UL; }
static int
pari_dir_exists(const char *s) { return mkdir(s); }
#else
static int
pari_file_exists(const char *s) { return 0; }
static int
pari_dir_exists(const char *s) { return 0; }
#endif

static char *
env_ok(const char *s)
{
  char *t = os_getenv(s);
  if (t && !pari_is_rwx(t))
  {
    pari_warn(warner,"%s is set (%s), but is not writable", s,t);
    t = NULL;
  }
  if (t && !pari_is_dir(t))
  {
    pari_warn(warner,"%s is set (%s), but is not a directory", s,t);
    t = NULL;
  }
  return t;
}

static const char*
pari_tmp_dir(void)
{
  char *s;
  s = env_ok("GPTMPDIR"); if (s) return s;
  s = env_ok("TMPDIR"); if (s) return s;
#if defined(_WIN32) || defined(__EMX__)
  s = env_ok("TMP"); if (s) return s;
  s = env_ok("TEMP"); if (s) return s;
#endif
#if defined(UNIX) || defined(__EMX__)
  if (pari_is_rwx("/tmp")) return "/tmp";
  if (pari_is_rwx("/var/tmp")) return "/var/tmp";
#endif
  return ".";
}

/* loop through 26^2 variants [suffix 'aa' to 'zz'] */
static int
get_file(char *buf, int test(const char *), const char *suf)
{
  char c, d, *end = buf + strlen(buf) - 1;
  if (suf) end -= strlen(suf);
  for (d = 'a'; d <= 'z'; d++)
  {
    end[-1] = d;
    for (c = 'a'; c <= 'z'; c++)
    {
      *end = c;
      if (! test(buf)) return 1;
      if (DEBUGFILES) err_printf("I/O: file %s exists!\n", buf);
    }
  }
  return 0;
}

#if defined(__EMX__) || defined(_WIN32)
static void
swap_slash(char *s)
{
#ifdef __EMX__
  if (!unix_shell())
#endif
  {
    char *t;
    for (t=s; *t; t++)
      if (*t == '/') *t = '\\';
  }
}
#endif

/* s truncated to 8 chars, suf possibly NULL */
static char *
init_unique(const char *s, const char *suf)
{
  const char *pre = pari_tmp_dir();
  char *buf, salt[64];
  size_t lpre, lsalt, lsuf;
#ifdef UNIX
  sprintf(salt,"-%ld-%ld", (long)getuid(), (long)getpid());
#else
  sprintf(salt,"-%ld", (long)time(NULL));
#endif
  lsuf = suf? strlen(suf): 0;
  lsalt = strlen(salt);
  lpre = strlen(pre);
  /* room for prefix + '/' + s + salt + suf + '\0' */
  buf = (char*) pari_malloc(lpre + 1 + 8 + lsalt + lsuf + 1);
  strcpy(buf, pre);
  if (buf[lpre-1] != '/') { (void)strcat(buf, "/"); lpre++; }
#if defined(__EMX__) || defined(_WIN32)
  swap_slash(buf);
#endif
  sprintf(buf + lpre, "%.8s%s", s, salt);
  if (lsuf) strcat(buf, suf);
  if (DEBUGFILES) err_printf("I/O: prefix for unique file/dir = %s\n", buf);
  return buf;
}

/* Return a "unique filename" built from the string s, possibly the user id
 * and the process pid (on Unix systems). A "temporary" directory name is
 * prepended. The name returned is pari_malloc'ed. It is DOS-safe
 * (s truncated to 8 chars) */
char*
pari_unique_filename_suffix(const char *s, const char *suf)
{
  char *buf = init_unique(s, suf);
  if (pari_file_exists(buf) && !get_file(buf, pari_file_exists, suf))
    pari_err(e_MISC,"couldn't find a suitable name for a tempfile (%s)",s);
  return buf;
}
char*
pari_unique_filename(const char *s)
{ return pari_unique_filename_suffix(s, NULL); }

/* Create a "unique directory" and return its name built from the string
 * s, the user id and process pid (on Unix systems). A "temporary"
 * directory name is prepended. The name returned is pari_malloc'ed.
 * It is DOS-safe (truncated to 8 chars) */
char*
pari_unique_dir(const char *s)
{
  char *buf = init_unique(s, NULL);
  if (pari_dir_exists(buf) && !get_file(buf, pari_dir_exists, NULL))
    pari_err(e_MISC,"couldn't find a suitable name for a tempdir (%s)",s);
  return buf;
}

static long
get_free_gp_file(void)
{
  long i, l = s_gp_file.n;
  for (i=0; i<l; i++)
    if (!gp_file[i].fp)
      return i;
  return pari_stack_new(&s_gp_file);
}

static void
check_gp_file(const char *s, long n)
{
  if (n < 0 || n >= s_gp_file.n || !gp_file[n].fp)
    pari_err_FILEDESC(s, n);
}

static long
new_gp_file(const char *s, FILE *f, int t)
{
  long n;
  n = get_free_gp_file();
  gp_file[n].name = pari_strdup(s);
  gp_file[n].fp = f;
  gp_file[n].type = t;
  gp_file[n].serial = gp_file_serial++;
  if (DEBUGFILES) err_printf("fileopen:%ld (%ld)\n", n, gp_file[n].serial);
  return n;
}

#if defined(ZCAT) && defined(HAVE_PIPES)
static long
check_compress(const char *name)
{
  long l = strlen(name);
  const char *end = name + l-1;
  if (l > 2 && (!strncmp(end-1,".Z",2)
#ifdef GNUZCAT
             || !strncmp(end-2,".gz",3)
#endif
  ))
  { /* compressed file (compress or gzip) */
    char *cmd = stack_malloc(strlen(ZCAT) + l + 4);
    sprintf(cmd,"%s \"%s\"",ZCAT,name);
    return gp_fileextern(cmd);
  }
  return -1;
}
#endif

long
gp_fileopen(char *s, char *mode)
{
  FILE *f;
  if (mode[0]==0 || mode[1]!=0)
    pari_err_TYPE("fileopen",strtoGENstr(mode));
  switch (mode[0])
  {
  case 'r':
#if defined(ZCAT) && defined(HAVE_PIPES)
    {
      long n = check_compress(s);
      if (n >= 0) return n;
    }
#endif
    f = fopen(s, "r");
    if (!f) pari_err_FILE("requested file", s);
    return new_gp_file(s, f, mf_IN);
  case 'w':
  case 'a':
    f = fopen(s, mode[0]=='w' ? "w": "a");
    if (!f) pari_err_FILE("requested file", s);
    return new_gp_file(s, f, mf_OUT);
  default:
    pari_err_TYPE("fileopen",strtoGENstr(mode));
    return -1; /* LCOV_EXCL_LINE */
  }
}

long
gp_fileextern(char *s)
{
#ifndef HAVE_PIPES
  pari_err(e_ARCH,"pipes"); return NULL;
#else
  FILE *f;
  check_secure(s);
  f = popen(s, "r");
  if (!f) pari_err(e_MISC,"[pipe:] '%s' failed",s);
  return new_gp_file(s,f, mf_PIPE);
#endif
}

void
gp_fileclose(long n)
{
  check_gp_file("fileclose", n);
  if (DEBUGFILES) err_printf("fileclose(%ld)\n",n);
  if (gp_file[n].type == mf_PIPE)
    pclose(gp_file[n].fp);
  else
    fclose(gp_file[n].fp);
  pari_free((void*)gp_file[n].name);
  gp_file[n].name = NULL;
  gp_file[n].fp = NULL;
  gp_file[n].type = mf_FALSE;
  gp_file[n].serial = -1;
  while (s_gp_file.n > 0 && !gp_file[s_gp_file.n-1].fp)
    s_gp_file.n--;
}

void
gp_fileflush(long n)
{
  check_gp_file("fileflush", n);
  if (DEBUGFILES) err_printf("fileflush(%ld)\n",n);
  if (gp_file[n].type == mf_OUT) (void)fflush(gp_file[n].fp);
}
void
gp_fileflush0(GEN gn)
{
  long i;
  if (gn)
  {
    if (typ(gn) != t_INT) pari_err_TYPE("fileflush",gn);
    gp_fileflush(itos(gn));
  }
  else for (i = 0; i < s_gp_file.n; i++)
    if (gp_file[i].fp && gp_file[i].type == mf_OUT) gp_fileflush(i);
}

GEN
gp_fileread(long n)
{
  Buffer *b;
  FILE *fp;
  GEN z;
  int t;
  check_gp_file("fileread", n);
  t = gp_file[n].type;
  if (t!=mf_IN && t!=mf_PIPE)
    pari_err_FILEDESC("fileread",n);
  fp = gp_file[n].fp;
  b = new_buffer();
  while(1)
  {
    if (!gp_read_stream_buf(fp, b)) { delete_buffer(b); return gen_0; }
    if (*(b->buf)) break;
  }
  z = strtoGENstr(b->buf);
  delete_buffer(b);
  return z;
}

void
gp_filewrite(long n, const char *s)
{
  FILE *fp;
  check_gp_file("filewrite", n);
  if (gp_file[n].type!=mf_OUT)
    pari_err_FILEDESC("filewrite",n);
  fp = gp_file[n].fp;
  fputs(s, fp);
  fputc('\n',fp);
}

void
gp_filewrite1(long n, const char *s)
{
  FILE *fp;
  check_gp_file("filewrite1", n);
  if (gp_file[n].type!=mf_OUT)
    pari_err_FILEDESC("filewrite1",n);
  fp = gp_file[n].fp;
  fputs(s, fp);
}

GEN
gp_filereadstr(long n)
{
  Buffer *b;
  char *s, *e;
  GEN z;
  int t;
  input_method IM;
  check_gp_file("filereadstr", n);
  t = gp_file[n].type;
  if (t!=mf_IN && t!=mf_PIPE)
    pari_err_FILEDESC("fileread",n);
  b = new_buffer();
  IM.fgets = (fgets_t)&fgets;
  IM.file = (void*) gp_file[n].fp;
  s = b->buf;
  if (!file_getline(b, &s, &IM)) { delete_buffer(b); return gen_0; }
  e = s + strlen(s)-1;
  if (*e == '\n') *e = 0;
  z = strtoGENstr(s);
  delete_buffer(b);
  return z;
}

/*******************************************************************/
/**                                                               **/
/**                             INSTALL                           **/
/**                                                               **/
/*******************************************************************/

#ifdef HAS_DLOPEN
#include <dlfcn.h>

/* see try_name() */
static void *
try_dlopen(const char *s, int flag)
{ void *h = dlopen(s, flag); pari_free((void*)s); return h; }

/* like dlopen, but using default(sopath) */
static void *
gp_dlopen(const char *name, int flag)
{
  void *handle;
  char *s;

  if (!name) return dlopen(NULL, flag);
  s = path_expand(name);

  /* if sopath empty or path is absolute, use dlopen */
  if (!GP_DATA || *(GP_DATA->sopath->PATH)==0 || path_is_absolute(s))
    return try_dlopen(s, flag);
  else
  {
    forpath_t T;
    char *t;
    forpath_init(&T, GP_DATA->sopath, s);
    while ( (t = forpath_next(&T)) )
    {
      if ( (handle = try_dlopen(t,flag)) ) { pari_free(s); return handle; }
      (void)dlerror(); /* clear error message */
    }
    pari_free(s);
  }
  return NULL;
}

static void *
install0(const char *name, const char *lib)
{
  void *handle;

#ifndef RTLD_GLOBAL /* OSF1 has dlopen but not RTLD_GLOBAL*/
#  define RTLD_GLOBAL 0
#endif
  handle = gp_dlopen(lib, RTLD_LAZY|RTLD_GLOBAL);

  if (!handle)
  {
    const char *s = dlerror(); if (s) err_printf("%s\n\n",s);
    if (lib) pari_err(e_MISC,"couldn't open dynamic library '%s'",lib);
    pari_err(e_MISC,"couldn't open dynamic symbol table of process");
  }
  return dlsym(handle, name);
}
#else
#  ifdef _WIN32
static HMODULE
try_LoadLibrary(const char *s)
{ void *h = LoadLibrary(s); pari_free((void*)s); return h; }

/* like LoadLibrary, but using default(sopath) */
static HMODULE
gp_LoadLibrary(const char *name)
{
  HMODULE handle;
  char *s = path_expand(name);

  /* if sopath empty or path is absolute, use LoadLibrary */
  if (!GP_DATA || *(GP_DATA->sopath->PATH)==0 || path_is_absolute(s))
    return try_LoadLibrary(s);
  else
  {
    forpath_t T;
    char *t;
    forpath_init(&T, GP_DATA->sopath, s);
    while ( (t = forpath_next(&T)) )
      if ( (handle = try_LoadLibrary(t)) ) { pari_free(s); return handle; }
    pari_free(s);
  }
  return NULL;
}
static void *
install0(const char *name, const char *lib)
{
  HMODULE handle;

  handle = gp_LoadLibrary(lib);
  if (!handle)
  {
    if (lib) pari_err(e_MISC,"couldn't open dynamic library '%s'",lib);
    pari_err(e_MISC,"couldn't open dynamic symbol table of process");
  }
  return (void *) GetProcAddress(handle,name);
}
#  else
static void *
install0(const char *name, const char *lib)
{ pari_err(e_ARCH,"install"); return NULL; }
#endif
#endif

static char *
dft_help(const char *gp, const char *s, const char *code)
{ return stack_sprintf("%s: installed function\nlibrary name: %s\nprototype: %s" , gp, s, code); }

void
gpinstall(const char *s, const char *code, const char *gpname, const char *lib)
{
  pari_sp av = avma;
  const char *gp = *gpname? gpname: s;
  int update_help;
  void *f;
  entree *ep;
  if (GP_DATA->secure)
  {
    char *msg = pari_sprintf("[secure mode]: about to install '%s'", s);
    pari_ask_confirm(msg);
    pari_free(msg);
  }
  f = install0(s, *lib ?lib :pari_library_path);
  if (!f)
  {
    if (*lib) pari_err(e_MISC,"can't find symbol '%s' in library '%s'",s,lib);
    pari_err(e_MISC,"can't find symbol '%s' in dynamic symbol table of process",s);
  }
  ep = is_entry(gp);
  /* Delete help if 1) help is the default (don't delete user addhelp)
   * and 2) default help changes */
  update_help = (ep && ep->valence == EpINSTALL && ep->help
      && strcmp(ep->code, code)
      && !strcmp(ep->help, dft_help(gp,s,ep->code)));
  ep = install(f,gp,code);
  if (update_help || !ep->help) addhelp(gp, dft_help(gp,s,code));
  mt_broadcast(strtoclosure("install",4,strtoGENstr(s),strtoGENstr(code),
                                       strtoGENstr(gp),strtoGENstr(lib)));
  avma = av;
}
