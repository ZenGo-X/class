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
/**                        PARI CALCULATOR                        **/
/**                                                               **/
/*******************************************************************/
#ifdef _WIN32
#  include "../systems/mingw/pwinver.h"
#  include <windows.h>
#  include "../systems/mingw/mingw.h"
#endif
#include "pari.h"
#include "paripriv.h"
#include "gp.h"

static jmp_buf *env;
static pari_stack s_env;
void (*cb_gp_output)(GEN z) = NULL;
void (*cb_pari_end_output)(void) = NULL;

static void
gp_ask_confirm(const char *s)
{
  err_printf(s);
  err_printf(". OK ? (^C if not)\n");
  pari_hit_return();
}

/* numerr < 0: from SIGINT */
static void
gp_err_recover(long numerr)
{
  longjmp(env[s_env.n-1], numerr);
}
/* numerr < 0: from SIGINT */
static void
gp_pre_recover(long numerr)
{
  if (numerr>=0)
  {
    out_puts(pariErr, "\n"); pariErr->flush();
  }
  longjmp(env[s_env.n-1], numerr);
}

static void
reset_ctrlc(void)
{
#if defined(_WIN32) || defined(__CYGWIN32__)
  win32ctrlc = 0;
#endif
}

static int
is_silent(char *s) { return s[strlen(s) - 1] == ';'; }

static int stdin_isatty = 0;
static int
is_interactive(void)
{ return pari_infile == stdin && stdin_isatty; }

/*******************************************************************/
/**                                                               **/
/**                        INITIALIZATION                         **/
/**                                                               **/
/*******************************************************************/
static void
print_shortversion(void)
{
  const ulong mask = (1UL<<PARI_VERSION_SHIFT) - 1;
  ulong n = paricfg_version_code, major, minor, patch;

  patch = n & mask; n >>= PARI_VERSION_SHIFT;
  minor = n & mask; n >>= PARI_VERSION_SHIFT;
  major = n;
  printf("%lu.%lu.%lu\n", major,minor,patch); exit(0);
}

static void
usage(char *s)
{
  printf("### Usage: %s [options] [GP files]\n", s);
  printf("Available options:\n");
  printf("  [-f,--fast]\t\tFast start: do not read .gprc\n");
  printf("  [-q,--quiet]\t\tQuiet mode: do not print banner and history numbers\n");
  printf("  [-s stacksize]\tStart with the PARI stack of given size (in bytes)\n");
  printf("  [--default key=val]\tExecute default(key,val) on startup\n");
  printf("  [--emacs]\t\tRun as if in Emacs shell\n");
  printf("  [--help]\t\tPrint this message\n");
  printf("  [--test]\t\tTest mode. No history, wrap long lines (bench only)\n");
  printf("  [--texmacs]\t\tRun as if using TeXmacs frontend\n");
  printf("  [--version]\t\tOutput version info and exit\n");
  printf("  [--version-short]\tOutput version number and exit\n\n");
  exit(0);
}

static void
gp_head(void)
{
  pari_print_version();
  pari_putc('\n');
  pari_center("Copyright (C) 2000-2018 The PARI Group");
  pari_putc('\n');
  print_text("PARI/GP is free software, covered by the GNU General Public \
License, and comes WITHOUT ANY WARRANTY WHATSOEVER.");
  pari_puts("\nType ? for help, \\q to quit.\n");
  pari_printf("Type ?%d for how to get moral"
              " (and possibly technical) support.\n", pari_community());
  if (pari_mainstack->vsize)
    pari_printf("\nparisizemax = %lu, primelimit = %lu",
                pari_mainstack->vsize,GP_DATA->primelimit);
  else
    pari_printf("\nparisize = %lu, primelimit = %lu",
                pari_mainstack->rsize,GP_DATA->primelimit);
  if (pari_mt_nbthreads > 1)
    pari_printf(", nbthreads = %lu", pari_mt_nbthreads);
  pari_putc('\n');
}

static char *
read_arg(long *nread, char *t, long argc, char **argv)
{
  long i = *nread;
  if (isdigit((int)*t)) return t;
  if (*t || i==argc) usage(argv[0]);
  *nread = i+1; return argv[i];
}

static char *
read_arg_equal(long *nread, char *t, long argc, char **argv)
{
  long i = *nread;
  if (*t=='=' && isdigit((int)t[1])) return t+1;
  if (*t || i==argc) usage(argv[0]);
  *nread = i+1; return argv[i];
}

static void
init_trivial_stack(void)
{
  const size_t s = 2048;
  pari_mainstack->size = s;
  pari_mainstack->bot = (pari_sp)pari_malloc(s);
  avma = pari_mainstack->top = pari_mainstack->bot + s;
}

static void
free_trivial_stack(void)
{
  free((void*)pari_mainstack->bot);
}

typedef struct { char *key, *val; } pair_t;
/* If ab of the form key=val, record pair in new stack entry
 * P[n].key must be freed by caller to avoid memory leak */
static void
record_default(pari_stack *s_P, char *ab)
{
  pair_t *P = (pair_t*)*pari_stack_base(s_P);
  char *k, *v;
  long n;
  ab = pari_strdup(ab);
  parse_key_val(ab, &k, &v);
  n = pari_stack_new(s_P);
  P[n].key = k;
  P[n].val = v;
}
static void
read_opt(pari_stack *p_A, long argc, char **argv)
{
  pair_t *P;
  pari_stack s_P; /* key / value to record default() settings */
  char *b = NULL, *p = NULL, *s = NULL;
  ulong f = GP_DATA->flags;
  long i = 1, initrc = 1;

  (void)&p; (void)&b; (void)&s; /* -Wall gcc-2.95 */

  pari_stack_init(&s_P,sizeof(*P),(void**)&P);
  pari_stack_alloc(&s_P, 64);
  pari_outfile = stderr;
  while (i < argc)
  {
    char *t = argv[i];

    if (*t++ != '-') break;
    i++;
START:
    switch(*t++)
    {
      case 'p': p = read_arg(&i,t,argc,argv); break;
      case 's': s = read_arg(&i,t,argc,argv); break;
      case 'e':
        f |= gpd_EMACS; if (*t) goto START;
        break;
      case 'q':
        f |= gpd_QUIET; if (*t) goto START;
        break;
      case 't':
        f |= gpd_TEST; if (*t) goto START;
        break;
      case 'f':
        initrc = 0; if (*t) goto START;
        break;
      case 'D':
        if (*t || i == argc) usage(argv[0]);
        record_default(&s_P, argv[i++]);
        break;
      case '-':
        if (strcmp(t, "version-short") == 0) { print_shortversion(); exit(0); }
        if (strcmp(t, "version") == 0) {
          init_trivial_stack(); pari_print_version();
          free_trivial_stack(); exit(0);
        }
        if (strcmp(t, "default") == 0) {
          if (i == argc) usage(argv[0]);
          record_default(&s_P, argv[i++]);
          break;
        }
        if (strcmp(t, "texmacs") == 0) { f |= gpd_TEXMACS; break; }
        if (strcmp(t, "emacs") == 0) { f |= gpd_EMACS; break; }
        if (strcmp(t, "test") == 0) { f |= gpd_TEST; initrc = 0; break; }
        if (strcmp(t, "quiet") == 0) { f |= gpd_QUIET; break; }
        if (strcmp(t, "fast") == 0) { initrc = 0; break; }
        if (strncmp(t, "primelimit",10) == 0) {p = read_arg_equal(&i,t+10,argc,argv); break; }
        if (strncmp(t, "stacksize",9) == 0) {s = read_arg_equal(&i,t+9,argc,argv); break; }
       /* fall through */
      default:
        usage(argv[0]);
    }
  }
  if (f & gpd_TEST) stdin_isatty = 0;
  GP_DATA->flags = f;
#ifdef READLINE
  GP_DATA->use_readline = stdin_isatty;
#endif
  if (!is_interactive()) GP_DATA->breakloop = 0;
  if (initrc) gp_initrc(p_A);
  for ( ; i < argc; i++) pari_stack_pushp(p_A, pari_strdup(argv[i]));

  /* override the values from gprc */
  if (p) (void)sd_primelimit(p, d_INITRC);
  if (s) (void)sd_parisize(s, d_INITRC);
  for (i = 0; i < s_P.n; i++) {
    setdefault(P[i].key, P[i].val, d_INITRC);
    free((void*)P[i].key);
  }
  pari_stack_delete(&s_P);
  pari_outfile = stdout;
}

/*******************************************************************/
/**                                                               **/
/**                            TEST MODE                          **/
/**                                                               **/
/*******************************************************************/
static int
test_is_interactive(void) { return 0; }

static void
test_output(GEN z) { init_linewrap(76); gen_output(z); }
void
init_test(void)
{
  disable_color = 1;
  init_linewrap(76);
  pari_errfile = stdout;
  cb_gp_output = test_output;
  cb_pari_is_interactive = test_is_interactive;
}

/*******************************************************************/
/**                                                               **/
/**                   FORMAT GP OUTPUT                            **/
/**                                                               **/
/*******************************************************************/
    /* REGULAR */
static void
normal_output(GEN z, long n)
{
  long l = 0;
  char *s;
  /* history number */
  if (n)
  {
    char buf[64];
    if (!(GP_DATA->flags & gpd_QUIET))
    {
      term_color(c_HIST);
      sprintf(buf, "%%%ld = ", n);
      pari_puts(buf);
      l = strlen(buf);
    }
  }
  /* output */
  term_color(c_OUTPUT);
  s = GENtostr(z);
  if (GP_DATA->lim_lines)
    lim_lines_output(s, l, GP_DATA->lim_lines);
  else
    pari_puts(s);
  pari_free(s);
  term_color(c_NONE); pari_putc('\n');
}

static void
gp_output(GEN z)
{
  if (cb_gp_output) { cb_gp_output(z); return; }
  if (GP_DATA->fmt->prettyp == f_PRETTY)
  { if (tex2mail_output(z, GP_DATA->hist->total)) return; }
  normal_output(z, GP_DATA->hist->total);
  pari_flush();
}

static GEN
gp_main_loop(long ismain)
{
  VOLATILE GEN z = gnil;
  VOLATILE long t = 0;
  VOLATILE pari_sp av = avma;
  filtre_t F;
  Buffer *b = filtered_buffer(&F);
  struct gp_context rec;
  long er;
  if ((er = setjmp(env[s_env.n-1])))
  { /* recover: jump from error [ > 0 ] or allocatemem [ -1 ] */
    if (er > 0) { /* true error */
      if (!(GP_DATA->recover)) exit(1);
      gp_context_restore(&rec);
      /* true error not from main instance, let caller sort it out */
      if (!ismain) { kill_buffers_upto_including(b); return NULL; }
    } else { /* allocatemem */
      tmp_restore(rec.file.file);
      gp_context_save(&rec);
    }
    avma = av = pari_mainstack->top;
    parivstack_reset();
    kill_buffers_upto(b);
    pari_alarm(0);
  }
  for(;;)
  {
    gp_context_save(&rec);
    if (! gp_read_line(&F, NULL))
    {
      if (popinfile()) gp_quit(0);
      if (ismain) continue;
      pop_buffer(); return z;
    }
    if (ismain)
    {
      reset_ctrlc();
      timer_start(GP_DATA->T);
      pari_set_last_newline(1);
    }
    if (gp_meta(b->buf,ismain)) continue;
    z = pari_compile_str(b->buf);
    z = closure_evalres(z);
    if (!ismain) continue;

    t = timer_delay(GP_DATA->T);
    if (!pari_last_was_newline()) pari_putc('\n');
    pari_alarm(0);
    if (t && GP_DATA->chrono)
    {
      pari_puts("time = ");
      pari_puts(gp_format_time(t));
    }
    if (GP_DATA->simplify) z = simplify_shallow(z);
    pari_add_hist(z, t);
    if (z != gnil && ! is_silent(b->buf) ) gp_output(z);
    avma = av;
    parivstack_reset();
  }
}

/* as gp_read_file, before running the main gp instance */
static void
read_main(const char *s)
{
  GEN z;
  if (setjmp(env[s_env.n-1]))
    z = NULL;
  else {
    FILE *f = switchin(s);
    if (file_is_binary(f)) {
      z = readbin(s,f, NULL);
      popinfile();
    }
    else z = gp_main_loop(0);
  }
  if (!z) err_printf("... skipping file '%s'\n", s);
  avma = pari_mainstack->top;
}

static const char *
break_loop_prompt(long n)
{
  const char *s = (n==1)? "break> ": stack_sprintf("break[%ld]> ", n);
  return gp_format_prompt(s);
}

static long frame_level=0, dbg_level = 0;

static int
break_loop(int numerr)
{
  filtre_t F;
  Buffer *b;
  int sigint = numerr<0, go_on = sigint;
  struct gp_context rec1, rec2;
  const char *prompt, *msg;
  long nenv, oldframe_level = frame_level;
  pari_sp av;

  if (numerr == e_SYNTAX) return 0;
  if (numerr == e_STACK) { evalstate_clone(); avma = pari_mainstack->top; }
  gp_context_save(&rec1);

  b = filtered_buffer(&F);
  nenv=pari_stack_new(&s_env);
  prompt = break_loop_prompt(s_env.n-1);
  iferr_env = NULL;
  dbg_level = 0;
  frame_level = closure_context(oldframe_level, dbg_level);
  pari_infile = newfile(stdin, "stdin", mf_IN)->file;
  term_color(c_ERR); pari_putc('\n');
  if (sigint)
    msg = "Break loop: <Return> to continue; 'break' to go back to GP prompt";
  else
    msg = "Break loop: type 'break' to go back to GP prompt";
  print_errcontext(pariOut, msg, NULL, NULL);
  term_color(c_NONE);
  av = avma;
  for(;;)
  {
    GEN x;
    long er, br_status;
    avma = av;
    gp_context_save(&rec2);
    if ((er=setjmp(env[nenv])))
    {
      if (er < 0)
      {
        s_env.n = 1;
        frame_level = oldframe_level;
        longjmp(env[s_env.n-1], er);
      }
      gp_context_restore(&rec2);
      iferr_env = NULL;
      closure_err(dbg_level);
      compilestate_restore(&rec1.eval.comp);
      (void) closure_context(oldframe_level, dbg_level);
      pari_infile = newfile(stdin, "stdin", mf_IN)->file;
    }
    term_color(c_NONE);
    if (!gp_read_line(&F, prompt))
      br_status = br_BREAK; /* EOF */
    else
    {
      /* Empty input ? Continue if entry on sigint (exit debugger frame) */
      if (! *(b->buf) && sigint) break;
      reset_ctrlc();
      if (gp_meta(b->buf,0)) continue;
      x = pari_compile_str(b->buf);
      x = closure_evalbrk(x, &br_status);
    }
    switch (br_status)
    {
      case br_NEXT: case br_MULTINEXT:
        popinfile(); /* exit frame. Don't exit debugger if s_env.n > 2 */
        go_on = 0; goto BR_EXIT;
      case br_BREAK: case br_RETURN:
        killallfiles(); /* completely exit the debugger */
        go_on = 0; goto BR_EXIT;
    }
    if (x!=gnil && !is_silent(b->buf)) { term_color(c_OUTPUT); gen_output(x); }
  }
BR_EXIT:
  s_env.n=nenv;
  frame_level = oldframe_level;
  gp_context_restore(&rec1);
  pop_buffer(); return go_on;
}

#ifdef __CYGWIN32__
void
cyg_environment(int argc, char ** argv)
{
  char *ti_dirs = getenv("TERMINFO_DIRS");
  char *argv0, *p;
  char *newdir;
  long n;

  if (!argc || !argv) return;
  argv0 = *argv;
  if (!argv0 || !*argv0) return;
  p = strrchr(argv0, '/');
  if (!p)
    p = argv0 = "";
  else
    p++;
  n = p - argv0;
  if (ti_dirs)
  {
    n += 14 + strlen(ti_dirs) + 1 + 8 + 1;
    newdir = malloc(n);
    if (!newdir) return;
    snprintf(newdir, n-8, "TERMINFO_DIRS=%s:%s", ti_dirs, argv0);
  }
  else
  {
    n += 14 + 8 + 1;
    newdir = malloc(n);
    if (!newdir) return;
    snprintf(newdir, n-8, "TERMINFO_DIRS=%s", argv0);
  }
  strcpy(newdir+n-9,"terminfo");
  putenv(newdir);
}
#endif

int
main(int argc, char **argv)
{
  char **A;
  pari_stack s_A;

  GP_DATA = default_gp_data();
  pari_stack_init(&s_env, sizeof(*env), (void**)&env);
  (void)pari_stack_new(&s_env);

  if (setjmp(env[s_env.n-1]))
  {
    puts("### Errors on startup, exiting...\n\n");
    exit(1);
  }
#ifdef __CYGWIN32__
  cyg_environment(argc, argv);
#endif
  stdin_isatty = pari_stdin_isatty();
  pari_init_defaults();
  pari_library_path = DL_DFLT_NAME;
  pari_stack_init(&s_A,sizeof(*A),(void**)&A);
  pari_init_opts(1000000 * sizeof(long), 0, INIT_SIGm | INIT_noPRIMEm | INIT_noIMTm);
  cb_pari_err_recover = gp_err_recover;
  cb_pari_pre_recover = gp_pre_recover;
  cb_pari_break_loop = break_loop;
  cb_pari_is_interactive = is_interactive;

  read_opt(&s_A, argc,argv);
  pari_init_primes(GP_DATA->primelimit);
#ifdef SIGALRM
  (void)os_signal(SIGALRM,gp_alarm_handler);
#endif
  pari_add_module(functions_gp);

  pari_set_plot_engine(gp_get_plot);
  cb_pari_quit = gp_quit;
  cb_pari_whatnow = whatnow;
  cb_pari_sigint = gp_sigint_fun;
  cb_pari_handle_exception = gp_handle_exception;
  cb_pari_ask_confirm = gp_ask_confirm;
  pari_init_paths();
  pari_mt_init(); /* MPI: will not return on slaves (pari_MPI_rank = 0) */
#ifdef _WIN32
  if (stdin_isatty) win32_set_codepage();
#endif
#ifdef READLINE
  init_readline();
#endif
  if (GP_DATA->flags & gpd_EMACS) init_emacs();
  if (GP_DATA->flags & gpd_TEXMACS) init_texmacs();

  timer_start(GP_DATA->T);
  if (!(GP_DATA->flags & gpd_QUIET)) gp_head();
  if (GP_DATA->flags & gpd_TEST) init_test();
  if (s_A.n)
  {
    FILE *l = pari_logfile;
    long i;
    pari_logfile = NULL;
    for (i = 0; i < s_A.n; pari_free(A[i]),i++) read_main(A[i]);
    /* Reading one of the input files above can set pari_logfile.
     * Don't restore in that case. */
    if (!pari_logfile) pari_logfile = l;
  }
  pari_stack_delete(&s_A);
  (void)gp_main_loop(1);
  gp_quit(0);
  return 0; /* LCOV_EXCL_LINE */
}

void
pari_breakpoint(void)
{
  if (!pari_last_was_newline()) pari_putc('\n');
  closure_err(0);
  if (cb_pari_break_loop && cb_pari_break_loop(-1)) return;
  cb_pari_err_recover(e_MISC);
}

void
dbg_down(long k)
{
  if (k<0) k=0;
  dbg_level -= k;
  if (dbg_level<0) dbg_level=0;
  gp_err_recover(e_NONE);
}

GEN
dbg_err(void) { GEN E = pari_err_last(); return E? gcopy(E):gnil; }

void
dbg_up(long k)
{
  if (k<0) k=0;
  dbg_level += k;
  if (dbg_level>frame_level) dbg_level=frame_level;
  gp_err_recover(e_NONE);
}

void
gp_quit(long code)
{
  pari_kill_plot_engine();
  pari_close();
  kill_buffers_upto(NULL);
  if (!(GP_DATA->flags & gpd_QUIET)) pari_puts("Goodbye!\n");
  if (cb_pari_end_output) cb_pari_end_output();
  exit(code);
}

void
whatnow0(char *s) { whatnow(pariOut, s,0); }

#include "gp_init.h"
