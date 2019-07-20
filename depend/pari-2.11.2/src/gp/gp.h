/* Copyright (C) 2000  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/*************************************************************************/
/*                                                                       */
/*                      GP-SPECIFIC DECLARATIONS                         */
/*                                                                       */
/*************************************************************************/
BEGINEXTERN
void init_emacs(void);
void init_readline(void);
void init_texmacs(void);

/* gp specific routines */
void dbg_down(long k);
void dbg_up(long k);
GEN dbg_err(void);
void gp_quit(long exitcode);
void pari_breakpoint(void);
int  whatnow(PariOUT *out, const char *s, int silent);

extern void (*cb_gp_output)(GEN z);
extern void (*cb_pari_end_output)(void);
extern entree functions_gp[];

/* architecture-dependent plot files (src/graph/plot*.c) */
void gp_get_plot(PARI_plot *T);
ENDEXTERN
