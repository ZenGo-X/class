/* Copyright (C) 2016  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

#include "pari.h"
#include "../src/graph/rect.h"
#include <emscripten/emscripten.h>

void
pari_emscripten_wget(const char *s)
{
  const char *name = stack_sprintf("/gpjs/root/%s",s);
  emscripten_async_wget(name,s,NULL,NULL);
  pari_err(e_MISC,"retry");
}

void
pari_emscripten_help(const char *s)
{
  const char *url = "https://pari.math.u-bordeaux.fr/dochtml";
#if ((PARI_VERSION_CODE>>PARI_VERSION_SHIFT)&1)
  pari_err(e_MISC,"Help: %s/help-stable/%s",url,s);
#else
  pari_err(e_MISC,"Help: %s/help/%s",url,s);
#endif
}

static GEN
emscripten_base64(const char *s)
{
  static const char *base64 =
    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
  long i, j, ls = strlen(s), lt = ((ls+2)/3)*4;
  long n = nchar2nlong(lt+1);
  GEN g = cgetg(1+n, t_STR);
  char *t = GSTR(g);
  g[n] = 0L;
  for(i=j=0; i < ls; i+=3, j+=4)
  {
    char s0 = s[i], s1 = i+1<ls ? s[i+1]: 0, s2 = i+2<ls ? s[i+2]: 0;
    t[j] = base64[(s0 & 0xfc) >> 2];
    t[j+1] = base64[((s0 & 0x3) << 4) + ((s1 & 0xf0) >> 4)];
    t[j+2] = i+1<ls ? base64[((s1 & 0xf) << 2) + ((s2 & 0xc0) >> 6)]: '=';
    t[j+3] = i+2<ls ? base64[s2 & 0x3f]: '=';
  }
  return g;
}

static void
emscripten_draw(PARI_plot *T, GEN w, GEN x, GEN y)
{
  pari_sp av = avma;
  GEN svg = emscripten_base64(rect2svg(w,x,y,NULL));
  EM_ASM(rawPrint=true);(void)T;
  pari_printf("<img src=\"data:image/svg+xml;charset=utf-8;base64,%Ps\">\n", svg);
  EM_ASM(rawPrint=false);
  avma = av;
}

static long plot_width, plot_height;

static void
pari_emscripten_get_plot(PARI_plot *T)
{
  T->width   = plot_width;
  T->height  = plot_height;
  T->hunit   = 3;   //
  T->vunit   = 3;   //
  T->fwidth  = 9;   // font width
  T->fheight = 12;  //   and height
  gp_get_ploth_default_sizes(T);
  T->dwidth  = 0;   // display width
  T->dheight = 0;   //   and height
  T->draw = &emscripten_draw;
}

void
pari_emscripten_plot_init(long width, long height)
{
  plot_width  = width;
  plot_height = height;
  pari_set_plot_engine(pari_emscripten_get_plot);
}
