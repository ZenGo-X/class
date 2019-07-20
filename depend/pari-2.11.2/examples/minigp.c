#include <stdio.h>
#include <pari/pari.h>
#include <readline/readline.h>
#include <readline/history.h>
#include <setjmp.h>

jmp_buf env;

int gp_is_interactive(void) { return pari_infile == stdin; }
void gp_err_recover(long numerr) { longjmp(env, numerr); }
void gp_quit(long exitcode) { exit(exitcode); }

entree functions_gp[]={
  {"quit",0,(void*)gp_quit,11,"vD0,L,","quit({status = 0}): quit, return to the system with exit status 'status'."},
  {NULL,0,NULL,0,NULL,NULL}};

#define col(a) term_get_color(NULL, a)

int main(int argc, char **argv)
{
  pari_init(8000000,500000);
  pari_add_module(functions_gp);
  cb_pari_err_recover = gp_err_recover;
  cb_pari_is_interactive = gp_is_interactive;
  cb_pari_quit = gp_quit;
  sd_colors("lightbg",d_INITRC);
  pari_printf("Welcome to minigp!\n");
  gp_load_gprc();
  (void)setjmp(env);
  while(1)
  {
    GEN z;
    const char *prompt = gp_format_prompt(GP_DATA->prompt);
    char *in = readline(prompt);
    pari_timer T;
    long time;

    if (!in) break;
    if (!*in) continue;

    add_history(in);
    gp_echo_and_log(prompt,in);
    timer_start(&T); z = gp_read_str(in); time = timer_delay(&T);
    pari_add_hist(z, time);
    if (z != gnil && in[strlen(in)-1] != ';')
    {
      pari_printf("%s%%%lu = %s",col(c_HIST),pari_nb_hist(),col(c_OUTPUT));
      output(z);
      pari_puts(col(c_NONE));
    }
    if (GP_DATA->chrono && time)
      pari_printf("time = %s\n", gp_format_time(time) );
    free(in); avma = pari_mainstack->top;
  }
  return 0;
}
