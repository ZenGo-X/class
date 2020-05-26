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
#include "paripriv.h"

/********************************************************************/
/**                                                                **/
/**                         LOW-RES PLOT                           **/
/**                                                                **/
/********************************************************************/
#define ISCR 64
#define JSCR 22

INLINE long
DTOL(double t) { return (long)(t + 0.5); }

static char
PICT(long j) {
  switch(j%3) {
    case 0:  return '_';
    case 1:  return 'x';
    default: return '"';
  }
}
static char
PICTZERO(long j) {
  switch(j%3) {
    case 0:  return ',';
    case 1:  return '-';
    default: return '`';
  }
}

static char *
dsprintf9(double d, char *buf)
{
  int i = 10;

  while (--i >= 0) {
    sprintf(buf, "%9.*g", i, d);
    if (strlen(buf) <= 9) break;
  }
  return buf;
}

typedef unsigned char screen[ISCR+1][JSCR+1];

static void
fill_gap(screen scr, long i, int jnew, int jpre)
{
  int mid, i_up, i_lo, up, lo;

  if (jpre < jnew - 2) {
    up = jnew - 1; i_up = i;
    lo = jpre + 1; i_lo = i - 1;
  } else if (jnew < jpre - 2) {
    up = jpre - 1; i_up = i - 1;
    lo = jnew + 1; i_lo = i;
  } else return; /* if gap < 2, leave it as it is. */

  mid = (jpre+jnew)/2;
  if (mid>JSCR) mid=JSCR; else if (mid<0) mid=0;
  if (lo<0) lo=0;
  if (lo<=JSCR) while (lo <= mid) scr[i_lo][lo++] = ':';
  if (up>JSCR) up=JSCR;
  if (up>=0) while (up > mid) scr[i_up][up--] = ':';
}

static double
todbl(GEN x) { return rtodbl(gtofp(x, LOWDEFAULTPREC)); }

/* code is either a t_CLOSURE (from GP: ploth, etc.) or a t_POL/t_VEC of
 * two t_POLs from rectsplines */
static GEN
READ_EXPR(GEN code, GEN x) {
  if (typ(code)!=t_CLOSURE) return gsubst(code,0,x);
  set_lex(-1, x); return closure_evalgen(code);
}

void
pariplot(GEN a, GEN b, GEN code, GEN ysmlu,GEN ybigu, long prec)
{
  const char BLANK = ' ', YY = '|', XX_UPPER = '\'', XX_LOWER = '.';
  long jz, j, i, sig;
  pari_sp av = avma;
  int jnew, jpre = 0; /* for lint */
  GEN x, dx;
  double diff, dyj, ysml, ybig, y[ISCR+1];
  screen scr;
  char buf[80], z;

  sig=gcmp(b,a); if (!sig) return;
  if (sig<0) { x=a; a=b; b=x; }
  x = gtofp(a, prec); push_lex(x, code);
  dx = divru(gtofp(gsub(b,a),prec), ISCR-1);
  for (j=1; j<=JSCR; j++) scr[1][j]=scr[ISCR][j]=YY;
  for (i=2; i<ISCR; i++)
  {
    scr[i][1]   = XX_LOWER;
    scr[i][JSCR]= XX_UPPER;
    for (j=2; j<JSCR; j++) scr[i][j] = BLANK;
  }
  ysml = ybig = 0.; /* -Wall */
  for (i=1; i<=ISCR; i++)
  {
    pari_sp av2 = avma;
    y[i] = gtodouble( READ_EXPR(code,x) );
    avma = av2;
    if (i == 1)
      ysml = ybig = y[1];
    else
    {
      if (y[i] < ysml) ysml = y[i];
      if (y[i] > ybig) ybig = y[i];
    }
    x = addrr(x,dx);
  }
  avma = av;
  if (ysmlu) ysml = gtodouble(ysmlu);
  if (ybigu) ybig = gtodouble(ybigu);
  diff = ybig - ysml;
  if (!diff) { ybig += 1; diff= 1.; }
  dyj = ((JSCR-1)*3+2) / diff;
  /* work around bug in gcc-4.8 (32bit): plot(x=-5,5,sin(x)))) */
  jz = 3 - (long)(ysml*dyj + 0.5); /* 3 - DTOL(ysml*dyj) */
  z = PICTZERO(jz); jz /= 3;
  for (i=1; i<=ISCR; i++)
  {
    if (0<=jz && jz<=JSCR) scr[i][jz]=z;
    j = 3 + DTOL((y[i]-ysml)*dyj);
    jnew = j/3;
    if (i > 1) fill_gap(scr, i, jnew, jpre);
    if (0<=jnew && jnew<=JSCR) scr[i][jnew] = PICT(j);
    jpre = jnew;
  }
  pari_putc('\n');
  pari_printf("%s ", dsprintf9(ybig, buf));
  for (i=1; i<=ISCR; i++) pari_putc(scr[i][JSCR]);
  pari_putc('\n');
  for (j=(JSCR-1); j>=2; j--)
  {
    pari_puts("          ");
    for (i=1; i<=ISCR; i++) pari_putc(scr[i][j]);
    pari_putc('\n');
  }
  pari_printf("%s ", dsprintf9(ysml, buf));
  for (i=1; i<=ISCR; i++)  pari_putc(scr[i][1]);
  pari_putc('\n');
  {
    char line[10 + 32 + 32 + ISCR - 9];
    sprintf(line, "%10s%-9.7g%*.7g\n"," ",todbl(a),ISCR-9,todbl(b));
    pari_printf(line);
  }
  pop_lex(1);
}
