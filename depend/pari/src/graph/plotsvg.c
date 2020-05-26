/* Copyright (C) 2017  The PARI group.

This file is part of the PARI/GP package.

This program is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License along
with this program; if not, write to the Free Software Foundation, Inc.,
51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
*/
#include "pari.h"
#include "rect.h"

static void
draw(PARI_plot *T, GEN w, GEN x, GEN y)
{
  if (pari_daemon()) return;  /* parent process returns */
  pari_plot_by_file("GP_SVG_VIEWER", ".svg", rect2svg(w,x,y,T));
  exit(0);
}
void
gp_get_plot(PARI_plot *T)
{
  T->width   = 480;
  T->height  = 320;
  T->fheight = 12;
  T->fwidth  = 6;
  T->hunit   = 3;
  T->vunit   = 3;
  gp_get_ploth_default_sizes(T);
  T->dwidth  = 0;
  T->dheight = 0;
  T->draw = &draw;
}
