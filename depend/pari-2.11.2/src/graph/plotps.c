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
/*           HIGH RESOLUTION PLOT VIA POSTSCRIPT FILE              */
/*******************************************************************/
#include "pari.h"
#include "rect.h"

static void
draw(PARI_plot *T, GEN w, GEN x, GEN y)
{
  if (pari_daemon()) return;  /* parent process returns */
  pari_plot_by_file("GP_POSTSCRIPT_VIEWER", ".ps", rect2ps_i(w,x,y,T,1));
  exit(0);
}

void
gp_get_plot(PARI_plot *T)
{
  T->width  = 400;
  T->height = 300;
  T->fheight= 9;
  T->fwidth = 5;
  T->hunit  = 3;
  T->vunit  = 3;
  gp_get_ploth_default_sizes(T);
  T->dwidth = 0;
  T->dheight= 0;
  T->draw = &draw;
}
