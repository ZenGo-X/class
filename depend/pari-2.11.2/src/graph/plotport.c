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
/*                                                                 */
/*                         PLOT ROUTINES                           */
/*                                                                 */
/*******************************************************************/
#include "pari.h"
#include "paripriv.h"
#include "rect.h"

static void (*pari_get_plot)(PARI_plot *);

/* no need for THREAD: OK to share this */
static hashtable *rgb_colors = NULL;

THREAD PariRect rectgraph[18]; /*NUMRECT*/
static THREAD long current_color[18]; /*NUMRECT*/

static long plotpoint_itype = 0, rectline_itype  = 0;

const long NUMRECT = 18;
const long RECUR_MAXDEPTH = 10;
const double RECUR_PREC = 0.001;
const long DEFAULT_COLOR = 1, AXIS_COLOR = 2;

enum {
  ROt_MV = 1, /* Move */
  ROt_PT,  /* Point */
  ROt_LN,  /* Line */
  ROt_BX,  /* Box */
  ROt_FBX, /* Filled Box */
  ROt_MP,  /* Multiple point */
  ROt_ML,  /* Multiple lines */
  ROt_ST,  /* String */
  ROt_PTT,  /* Point type change */
  ROt_LNT,  /* Line type change */
  ROt_PTS,  /* Point size change */
  ROt_NULL, /* To be the start of the chain */
};

/* string justification */
#define RoSTdirLEFT       0x00
#define RoSTdirRIGHT      0x02
#define RoSTdirHPOS_mask  0x03
#define RoSTdirBOTTOM     0x00
#define RoSTdirTOP        0x08
#define RoSTdirVPOS_mask  0x0c
#define RoSTdirHGAP       0x10
#define RoSTdirVGAP       0x20

/* ploth flags */
#define PLOT_PARAMETRIC   0x00001
#define PLOT_RECURSIVE    0x00002
#define PLOT_NO_RESCALE   0x00004
#define PLOT_NO_AXE_X     0x00008
#define PLOT_NO_AXE_Y     0x00010
#define PLOT_NO_FRAME     0x00020
#define PLOT_POINTS       0x00040
#define PLOT_POINTS_LINES 0x00080
#define PLOT_SPLINES      0x00100
#define PLOT_NO_TICK_X    0x00200
#define PLOT_NO_TICK_Y    0x00400
#define PLOT_NODOUBLETICK 0x00800
#define PLOT_COMPLEX      0x01000
#define PLOT_PARA         0x02000

INLINE long
DTOL(double t) { return (long)(t + 0.5); }

static const long PS_WIDTH = 1120 - 60; /* 1400 - 60 for hi-res */
static const long PS_HEIGH = 800 - 40; /* 1120 - 60 for hi-res */

static void
_psdraw_scale(PARI_plot *T, GEN w, GEN x, GEN y)
{
  pari_sp av = avma;
  FILE *F = fopen(current_psfile, "a");
  if (!F) pari_err_FILE("postscript file",current_psfile);
  fputs(rect2ps(w,x,y,T), F);
  fclose(F); avma = av;
}
static void
_psdraw(PARI_plot *T, GEN w, GEN x, GEN y)
{ (void)T; _psdraw_scale(NULL,w,x,y); }
static void
pari_get_psplot(PARI_plot *T)
{
  T->width  = PS_WIDTH;
  T->height = PS_HEIGH;
  T->fheight= 15;
  T->fwidth = 6;
  T->hunit  = 5;
  T->vunit  = 5;
  T->dwidth = 0;
  T->dheight= 0;
  T->draw = NULL;
}
static void
pari_get_svgplot(PARI_plot *T)
{
  T->width   = 480;
  T->height  = 320;
  T->fheight = 12;
  T->fwidth  = 6;
  T->hunit   = 3;
  T->vunit   = 3;
  T->dwidth  = 0;
  T->dheight = 0;
  T->draw = NULL;
}

/********************************************************************/
/**                                                                **/
/**                      RECTPLOT FUNCTIONS                        **/
/**                                                                **/
/********************************************************************/
static void
get_plot_null(PARI_plot *T)
{ (void)T; pari_err(e_MISC,"high resolution graphics disabled"); }

void
pari_init_graphics(void) { pari_get_plot = &get_plot_null; }

void
pari_set_plot_engine(void (*plot)(PARI_plot *))
{
  long n;
  pari_get_plot = plot;
  for (n = 0; n < NUMRECT; n++)
  {
    PariRect *e = &rectgraph[n];
    RHead(e) = RTail(e) = NULL;
    RXsize(e) = RYsize(e) = 0;
  }
}

void
pari_kill_plot_engine(void)
{
  int i;
  for (i=0; i<NUMRECT; i++)
  {
    PariRect *e = &rectgraph[i];
    if (RHead(e)) plotkill(i);
  }
  if (rgb_colors)
  {
    pari_free((void*)rgb_colors->table);
    pari_free((void*)rgb_colors);
  }
}

static PariRect *
check_rect(long ne)
{
  const char *f = "graphic function";
  const long m = NUMRECT-1;
  if (ne < 0) pari_err_DOMAIN(f, "rectwindow", "<", gen_0, stoi(ne));
  if (ne > m) pari_err_DOMAIN(f, "rectwindow", ">", stoi(m), stoi(ne));
  return &rectgraph[ne];
}

static PariRect *
check_rect_init(long ne)
{
  PariRect *e = check_rect(ne);
  if (!RHead(e)) pari_err_TYPE("graphic function [use plotinit()]", stoi(ne));
  return e;
}
static void
Rchain(PariRect *e, RectObj *z)
{
  if (!RHead(e)) RHead(e) = z; else RoNext(RTail(e)) = z;
  RTail(e) = z;
  RoNext(z) = NULL;
}

static long
rgb_to_long(long r, long g, long b)
{ return (r << 16) | (g << 8) | b; }
/* c from graphcolormap */
static long
colormap_to_color(long i)
{
  GEN c = GP_DATA->colormap;
  long k = i+1, l = lg(c)-1;
  int r, g, b;
  if (k > l)
    pari_err_COMPONENT("graphcolormap",">", stoi(l), stoi(k));
  color_to_rgb(gel(c, k), &r,&g,&b);
  return rgb_to_long(r, g, b);
}

static void
initrect_i(long ne, long x, long y)
{
  PariRect *e;
  RectObj *z;

  if (x <= 1) pari_err_DOMAIN("plotinit", "x", "<=", gen_1, stoi(x));
  if (y <= 1) pari_err_DOMAIN("plotinit", "y", "<=", gen_1, stoi(y));
  e = check_rect(ne); if (RHead(e)) plotkill(ne);

  current_color[ne] = colormap_to_color(DEFAULT_COLOR);
  z = (RectObj*) pari_malloc(sizeof(RectObj));
  RoType(z) = ROt_NULL;
  Rchain(e, z);
  RXsize(e) = x; RXcursor(e) = 0; RXscale(e) = 1; RXshift(e) = 0;
  RYsize(e) = y; RYcursor(e) = 0; RYscale(e) = 1; RYshift(e) = 0;
}
static long
initrect_get_arg(GEN x, long dft)
{
  if (!x) return dft;
  if (typ(x) != t_INT) pari_err_TYPE("plotinit",x);
  return itos(x);
}
void
plotinit(long ne, GEN x, GEN y, long flag)
{
  const long m = NUMRECT-3;
  long xi, yi;
  PARI_plot T;

  if (flag)
  {
    pari_get_plot(&T);
    xi = T.width -1; if (x) xi = DTOL(xi * gtodouble(x));
    yi = T.height-1; if (y) yi = DTOL(yi * gtodouble(y));
  }
  else
  {
    if (!x || !y) pari_get_plot(&T);
    xi = initrect_get_arg(x, T.width -1);
    yi = initrect_get_arg(y, T.height-1);
  }
  if (ne > m) pari_err_DOMAIN("plotinit", "rectwindow", ">", stoi(m), stoi(ne));
  initrect_i(ne, xi, yi);
}

GEN
plotcursor(long ne)
{
  PariRect *e = check_rect_init(ne);
  return mkvec2s((long)RXcursor(e), (long)RYcursor(e));
}

static void
plotscale0(long ne, double x1, double x2, double y1, double y2)
{
  PariRect *e = check_rect_init(ne);
  double x, y;

  x = RXshift(e) + RXscale(e) * RXcursor(e);
  y = RYshift(e) + RYscale(e) * RYcursor(e);
  RXscale(e) = RXsize(e)/(x2-x1); RXshift(e) = -x1*RXscale(e);
  RYscale(e) = RYsize(e)/(y1-y2); RYshift(e) = -y2*RYscale(e);
  RXcursor(e) = (x - RXshift(e)) / RXscale(e);
  RYcursor(e) = (y - RYshift(e)) / RYscale(e);
}
void
plotscale(long ne, GEN x1, GEN x2, GEN y1, GEN y2)
{ plotscale0(ne, gtodouble(x1), gtodouble(x2), gtodouble(y1), gtodouble(y2)); }

static void
plotmove0(long ne, double x, double y, long relative)
{
  PariRect *e = check_rect_init(ne);
  RectObj *z = (RectObj*) pari_malloc(sizeof(RectObj1P));

  if (relative) { RXcursor(e) += x; RYcursor(e) += y; }
  else          { RXcursor(e) = x; RYcursor(e) = y; }
  RoType(z) = ROt_MV;
  RoMVx(z) = RXcursor(e) * RXscale(e) + RXshift(e);
  RoMVy(z) = RYcursor(e) * RYscale(e) + RYshift(e);
  Rchain(e, z);
}
static void
_move(long ne, double x, double y)
{ plotmove0(ne,x,y,0); }
void
plotmove(long ne, GEN x, GEN y)
{ plotmove0(ne,gtodouble(x),gtodouble(y),0); }
void
plotrmove(long ne, GEN x, GEN y)
{ plotmove0(ne,gtodouble(x),gtodouble(y),1); }

/* ROt_MV/ROt_PT */
static void
plotpoint0(long ne, double x, double y,long relative)
{
  PariRect *e = check_rect_init(ne);
  RectObj *z = (RectObj*) pari_malloc(sizeof(RectObj1P));

  if (relative) { RXcursor(e) += x; RYcursor(e) += y; }
  else          { RXcursor(e) = x; RYcursor(e) = y; }
  RoPTx(z) = RXcursor(e)*RXscale(e) + RXshift(e);
  RoPTy(z) = RYcursor(e)*RYscale(e) + RYshift(e);
  RoType(z) = ( DTOL(RoPTx(z)) < 0
                || DTOL(RoPTy(z)) < 0 || DTOL(RoPTx(z)) > RXsize(e)
                || DTOL(RoPTy(z)) > RYsize(e) ) ? ROt_MV : ROt_PT;
  Rchain(e, z);
  RoCol(z) = current_color[ne];
}
static void
plotpoint(long ne, GEN x, GEN y)
{ plotpoint0(ne,gtodouble(x),gtodouble(y),0); }
void
plotrpoint(long ne, GEN x, GEN y)
{ plotpoint0(ne,gtodouble(x),gtodouble(y),1); }

GEN
plotcolor(long ne, GEN c)
{
  long t = typ(c), n = lg(GP_DATA->colormap)-2;
  int r, g, b;
  check_rect(ne);
  if (t == t_INT)
  {
    long i = itos(c);
    if (i < 0) pari_err_DOMAIN("plotcolor", "color", "<", gen_0, c);
    if (i > n) pari_err_DOMAIN("plotcolor", "color", ">", stoi(n), c);
    c = gel(GP_DATA->colormap,i+1);
  }
  else
  {
    if (t == t_VEC) { c = ZV_to_zv(c); t = typ(c); }
    if (t != t_VECSMALL && t != t_STR) pari_err_TYPE("plotcolor",c);
  }
  color_to_rgb(c, &r,&g,&b);
  current_color[ne] = rgb_to_long(r,g,b);
  return mkvec3s(r, g, b);
}

/* ROt_MV/ROt_LN */
static void
rectline0(long ne, double gx2, double gy2, long relative)
{
  double dx, dy, dxy, xmin, xmax, ymin, ymax, x1, y1, x2, y2;
  PariRect *e = check_rect_init(ne);
  RectObj *z = (RectObj*) pari_malloc(sizeof(RectObj2P));
  const double c = 1 + 1e-10;

  x1 = RXcursor(e)*RXscale(e) + RXshift(e);
  y1 = RYcursor(e)*RYscale(e) + RYshift(e);
  if (relative)
    { RXcursor(e)+=gx2; RYcursor(e)+=gy2; }
  else
    { RXcursor(e)=gx2; RYcursor(e)=gy2; }
  x2 = RXcursor(e)*RXscale(e) + RXshift(e);
  y2 = RYcursor(e)*RYscale(e) + RYshift(e);
  xmin = maxdd(mindd(x1,x2),0); xmax = mindd(maxdd(x1,x2),RXsize(e));
  ymin = maxdd(mindd(y1,y2),0); ymax = mindd(maxdd(y1,y2),RYsize(e));
  dxy = x1*y2 - y1*x2; dx = x2-x1; dy = y2-y1;
  if (dy)
  {
    double a = (dxy + RYsize(e)*dx) / dy, b = dxy / dy;
    if (dx*dy < 0)
    { xmin=maxdd(xmin,a); xmax=mindd(xmax,b); }
    else
    { xmin=maxdd(xmin,b); xmax=mindd(xmax,a); }
  }
  if (dx)
  {
    double a = (RXsize(e)*dy - dxy) / dx, b = -dxy / dx;
    if (dx*dy < 0)
    { ymin=maxdd(ymin,a); ymax=mindd(ymax,b); }
    else
    { ymin=maxdd(ymin,b); ymax=mindd(ymax,a); }
  }
  RoLNx1(z) = xmin;
  RoLNx2(z) = xmax;
  if (dx*dy < 0) { RoLNy1(z) = ymax; RoLNy2(z) = ymin; }
  else         { RoLNy1(z) = ymin; RoLNy2(z) = ymax; }
  RoType(z) = (xmin>xmax*c || ymin>ymax*c) ? ROt_MV : ROt_LN;
  Rchain(e, z);
  RoCol(z) = current_color[ne];
}
static void
_line(long ne, double x, double y)
{ rectline0(ne, x, y, 0); }
void
plotline(long ne, GEN gx2, GEN gy2)
{ rectline0(ne, gtodouble(gx2), gtodouble(gy2),0); }
void
plotrline(long ne, GEN gx2, GEN gy2)
{ rectline0(ne, gtodouble(gx2), gtodouble(gy2),1); }

enum {
  TICKS_CLOCKW   = 1, /* Draw in clockwise direction */
  TICKS_ACLOCKW  = 2, /* Draw in anticlockwise direction */
  TICKS_ENDSTOO  = 4, /* Draw at endspoints if needed */
  TICKS_NODOUBLE = 8  /* Do not draw double-length ticks */
};

/* Given coordinates of ends of a line, and labels l1 l2 attached to the
 * ends, plot ticks where the label coordinate takes "round" values */
static void
rectticks(PARI_plot *WW, long ne, double dx1, double dy1, double dx2,
          double dy2, double l1, double l2, long flags)
{
  long dx, dy, dxy, dxy1, x1, y1, x2, y2, nticks, n, n1, dn;
  double minstep, maxstep, step, l_min, l_max, minl, maxl, dl, dtx, dty, x, y;
  double ddx, ddy;
  const double mult[3] = { 2./1., 5./2., 10./5. };
  PariRect *e = check_rect_init(ne);
  int do_double = !(flags & TICKS_NODOUBLE);

  x1 = DTOL(dx1*RXscale(e) + RXshift(e));
  y1 = DTOL(dy1*RYscale(e) + RYshift(e));
  x2 = DTOL(dx2*RXscale(e) + RXshift(e));
  y2 = DTOL(dy2*RYscale(e) + RYshift(e));
  dx = x2 - x1; if (dx < 0) dx = -dx;
  dy = y2 - y1; if (dy < 0) dy = -dy;
  dxy1 = maxss(dx, dy);
  dx /= WW->hunit;
  dy /= WW->vunit;
  if (dx > 1000 || dy > 1000)
    dxy = 1000; /* avoid overflow */
  else
    dxy = usqrt(dx*dx + dy*dy);
  nticks = (long) ((dxy + 2.5)/4);
  if (!nticks) return;

  /* Find nticks (or less) "round" numbers between l1 and l2. For our purpose
   * round numbers have "last significant" decimal digit either
   *    - any;
   *    - even;
   *    - divisible by 5.
   * We need to choose which alternative is better. */
  if (l1 < l2)
    l_min = l1, l_max = l2;
  else
    l_min = l2, l_max = l1;
  minstep = (l_max - l_min)/(nticks + 1);
  maxstep = 2.5*(l_max - l_min);
  step = exp(log(10.) * floor(log10(minstep)));
  if (!(flags & TICKS_ENDSTOO)) {
    double d = 2*(l_max - l_min)/dxy1; /* Two pixels off */
    l_min += d;
    l_max -= d;
  }
  for (n = 0; ; n++)
  {
    if (step >= maxstep) return;

    if (step >= minstep) {
      minl = ceil(l_min/step);
      maxl = floor(l_max/step);
      if (minl <= maxl && maxl - minl + 1 <= nticks) {
        nticks = (long) (maxl - minl + 1);
        l_min = minl * step;
        l_max = maxl * step; break;
      }
    }
    step *= mult[ n % 3 ];
  }
  /* Where to position doubleticks. Variants:
   * small: each 5, double: each 10  ; n=2 mod 3
   * small: each 2, double: each 10  ; n=1 mod 3
   * small: each 1, double: each  5 */
  dn = (n % 3 == 2)? 2: 5;
  n1 = ((long)minl) % dn; /* unused if do_double = FALSE */

  /* now l_min and l_max keep min/max values of l with ticks, and nticks is
     the number of ticks to draw. */
  if (nticks == 1) ddx = ddy = 0; /* -Wall */
  else {
    dl = (l_max - l_min)/(nticks - 1);
    ddx = (dx2 - dx1) * dl / (l2 - l1);
    ddy = (dy2 - dy1) * dl / (l2 - l1);
  }
  x = dx1 + (dx2 - dx1) * (l_min - l1) / (l2 - l1);
  y = dy1 + (dy2 - dy1) * (l_min - l1) / (l2 - l1);
  /* assume hunit and vunit form a square. For clockwise ticks: */
  dtx = WW->hunit * dy/dxy * (y2 > y1 ? 1 : -1); /* y-coord runs down */
  dty = WW->vunit * dx/dxy * (x2 > x1 ? 1 : -1);
  for (n = 0; n < nticks; n++, x += ddx, y += ddy) {
    RectObj *z = (RectObj*) pari_malloc(sizeof(RectObj2P));
    double lunit = WW->hunit > 1 ? 1.5 : 2;
    double l = (do_double && (n + n1) % dn == 0) ? lunit: 1;
    double x1, x2, y1, y2;
    x1 = x2 = x*RXscale(e) + RXshift(e);
    y1 = y2 = y*RYscale(e) + RYshift(e);
    if (flags & TICKS_CLOCKW)  { x1 += dtx*l; y1 -= dty*l; }
    if (flags & TICKS_ACLOCKW) { x2 -= dtx*l; y2 += dty*l; }
    RoLNx1(z) = x1; RoLNy1(z) = y1;
    RoLNx2(z) = x2; RoLNy2(z) = y2;
    RoType(z) = ROt_LN;
    Rchain(e, z);
    RoCol(z) = current_color[ne];
  }
}

static void
rectbox0(long ne, double gx2, double gy2, long relative, long filled)
{
  double xx, yy, x1, y1, x2, y2, xmin, ymin, xmax, ymax;
  PariRect *e = check_rect_init(ne);
  RectObj *z = (RectObj*) pari_malloc(sizeof(RectObj2P));

  x1 = RXcursor(e)*RXscale(e) + RXshift(e);
  y1 = RYcursor(e)*RYscale(e) + RYshift(e);
  if (relative)
  { xx = RXcursor(e)+gx2; yy = RYcursor(e)+gy2; }
  else
  {  xx = gx2; yy = gy2; }
  x2 = xx*RXscale(e) + RXshift(e);
  y2 = yy*RYscale(e) + RYshift(e);
  xmin = maxdd(mindd(x1,x2),0); xmax = mindd(maxdd(x1,x2),RXsize(e));
  ymin = maxdd(mindd(y1,y2),0); ymax = mindd(maxdd(y1,y2),RYsize(e));

  RoType(z) = filled ? ROt_FBX: ROt_BX;
  RoBXx1(z) = xmin; RoBXy1(z) = ymin;
  RoBXx2(z) = xmax; RoBXy2(z) = ymax;
  Rchain(e, z);
  RoCol(z) = current_color[ne];
}
static void
_box(long ne, double x, double y)
{ rectbox0(ne, x, y, 0, 0); }
void
plotbox(long ne, GEN gx2, GEN gy2, long f)
{ rectbox0(ne, gtodouble(gx2), gtodouble(gy2), 0, f); }
void
plotrbox(long ne, GEN gx2, GEN gy2, long f)
{ rectbox0(ne, gtodouble(gx2), gtodouble(gy2), 1, f); }

static void
freeobj(RectObj *z) {
  switch(RoType(z)) {
    case ROt_MP: case ROt_ML:
      pari_free(RoMPxs(z));
      pari_free(RoMPys(z)); break;
    case ROt_ST:
      pari_free(RoSTs(z)); break;
  }
  pari_free(z);
}

void
plotkill(long ne)
{
  RectObj *z, *t;
  PariRect *e = check_rect_init(ne);

  z = RHead(e);
  RHead(e) = RTail(e) = NULL;
  RXsize(e) = RYsize(e) = 0;
  RXcursor(e) = RYcursor(e) = 0;
  RXscale(e) = RYscale(e) = 1;
  RXshift(e) = RYshift(e) = 0;
  while (z) { t = RoNext(z); freeobj(z); z = t; }
}

/* ROt_MP */
static void
plotpoints0(long ne, double *X, double *Y, long lx)
{
  double *px, *py;
  long i, cp=0;
  PariRect *e = check_rect_init(ne);
  RectObj *z = (RectObj*) pari_malloc(sizeof(RectObjMP));

  RoMPxs(z) = px = (double*) pari_malloc(lx*sizeof(double));
  RoMPys(z) = py = (double*) pari_malloc(lx*sizeof(double));
  for (i=0; i<lx; i++)
  {
    double x = RXscale(e)*X[i] + RXshift(e);
    double y = RYscale(e)*Y[i] + RYshift(e);
    if (x >= 0 && y >= 0 && x <= RXsize(e) && y <= RYsize(e))
    {
      px[cp] = x; py[cp] = y; cp++;
    }
  }
  RoType(z) = ROt_MP;
  RoMPcnt(z) = cp;
  Rchain(e, z);
  RoCol(z) = current_color[ne];
}
void
plotpoints(long ne, GEN X, GEN Y)
{
  pari_sp av = avma;
  double *px, *py;
  long i, lx;

  if (!is_vec_t(typ(X)) || !is_vec_t(typ(Y))) { plotpoint(ne, X, Y); return; }
  lx = lg(X); if (lg(Y) != lx) pari_err_DIM("plotpoints");
  lx--; if (!lx) return;

  px = (double*)stack_malloc_align(lx*sizeof(double), sizeof(double)); X++;
  py = (double*)stack_malloc_align(lx*sizeof(double), sizeof(double)); Y++;
  for (i=0; i<lx; i++)
  {
    px[i] = gtodouble(gel(X,i));
    py[i] = gtodouble(gel(Y,i));
  }
  plotpoints0(ne,px,py,lx); avma = av;
}

/* ROt_ML */
static void
rectlines0(long ne, double *x, double *y, long lx, long flag)
{
  long i,I;
  double *ptx,*pty;
  PariRect *e = check_rect_init(ne);
  RectObj *z = (RectObj*) pari_malloc(sizeof(RectObj2P));

  I = flag ? lx+1 : lx;
  ptx = (double*) pari_malloc(I*sizeof(double));
  pty = (double*) pari_malloc(I*sizeof(double));
  for (i=0; i<lx; i++)
  {
    ptx[i] = RXscale(e)*x[i] + RXshift(e);
    pty[i] = RYscale(e)*y[i] + RYshift(e);
  }
  if (flag)
  {
    ptx[i] = RXscale(e)*x[0] + RXshift(e);
    pty[i] = RYscale(e)*y[0] + RYshift(e);
  }
  Rchain(e, z);
  RoType(z) = ROt_ML;
  RoMLcnt(z) = lx;
  RoMLxs(z) = ptx;
  RoMLys(z) = pty;
  RoCol(z) = current_color[ne];
}
void
plotlines(long ne, GEN X, GEN Y, long flag)
{
  pari_sp av = avma;
  double *x, *y;
  long i, lx;

  if (!is_vec_t(typ(X)) || !is_vec_t(typ(Y))) { plotline(ne, X, Y); return; }
  lx = lg(X); if (lg(Y) != lx) pari_err_DIM("plotlines");
  lx--; if (!lx) return;

  x = (double*)stack_malloc_align(lx*sizeof(double), sizeof(double)); X++;
  y = (double*)stack_malloc_align(lx*sizeof(double), sizeof(double)); Y++;
  for (i=0; i<lx; i++)
  {
    x[i] = gtodouble(gel(X,i));
    y[i] = gtodouble(gel(Y,i));
  }
  rectlines0(ne,x,y,lx,flag); avma = av;
}

/* ROt_ST */
void
plotstring(long ne, char *str, long dir)
{
  PariRect *e = check_rect_init(ne);
  RectObj *z = (RectObj*) pari_malloc(sizeof(RectObjST));
  long l = strlen(str);
  char *s = (char *) pari_malloc(l+1);

  memcpy(s,str,l+1);
  RoType(z) = ROt_ST;
  RoSTl(z) = l;
  RoSTs(z) = s;
  RoSTx(z) = RXscale(e)*RXcursor(e)+RXshift(e);
  RoSTy(z) = RYscale(e)*RYcursor(e)+RYshift(e);
  RoSTdir(z) = dir;
  Rchain(e, z);
  RoCol(z) = current_color[ne];
}

/* ROt_PTT */
void
plotpointtype(long ne, long type)
{
 if (ne == -1) plotpoint_itype = type;
 else {
   PariRect *e = check_rect_init(ne);
   RectObj *z = (RectObj*) pari_malloc(sizeof(RectObjPN));
   RoType(z) = ROt_PTT;
   RoPTTpen(z) = type;
   Rchain(e, z);
 }
}

/* ROt_PTS. FIXME: this function is a noop, since no graphic driver implement
 * this code. ne == -1 (change globally). */
void
plotpointsize(long ne, GEN size)
{
 if (ne == -1) { /*do nothing*/ }
 else {
   PariRect *e = check_rect_init(ne);
   RectObj *z = (RectObj*) pari_malloc(sizeof(RectObjPS));
   RoType(z) = ROt_PTS;
   RoPTSsize(z) = gtodouble(size);
   Rchain(e, z);
 }
}

void
plotlinetype(long ne, long type)
{
 if (ne == -1) rectline_itype = type;
 else {
   PariRect *e = check_rect_init(ne);
   RectObj *z = (RectObj*) pari_malloc(sizeof(RectObjPN));
   RoType(z) = ROt_LNT;
   RoLNTpen(z) = type;
   Rchain(e, z);
 }
}

#define RECT_CP_RELATIVE  0x1
#define RECT_CP_NW        0x0
#define RECT_CP_SW        0x2
#define RECT_CP_SE        0x4
#define RECT_CP_NE        0x6

static double*
cpd(double* R, size_t t)
{ void *o = pari_malloc(t * sizeof(double)); memcpy(o,R,t); return (double*)o; }
static void*
cp(void* R, size_t t)
{ void *o = pari_malloc(t); memcpy(o,R,t); return o; }
void
plotcopy(long source, long dest, GEN xoff, GEN yoff, long flag)
{
  PariRect *s = check_rect_init(source), *d = check_rect_init(dest);
  RectObj *R, *tail = RTail(d);
  long i, x, y;
  if (flag & RECT_CP_RELATIVE) {
    double xd = gtodouble(xoff), yd = gtodouble(yoff);
    PARI_plot T;
    if (xd > 1) pari_err_DOMAIN("plotcopy","dx",">",gen_1,xoff);
    if (xd < 0) pari_err_DOMAIN("plotcopy","dx","<",gen_0,xoff);
    if (yd > 1) pari_err_DOMAIN("plotcopy","dy",">",gen_1,yoff);
    if (yd < 0) pari_err_DOMAIN("plotcopy","dy","<",gen_0,yoff);
    pari_get_plot(&T);
    x = DTOL(xd * (T.width-1));
    y = DTOL(yd * (T.height-1));
  } else {
    if (typ(xoff) != t_INT) pari_err_TYPE("plotcopy",xoff);
    if (typ(yoff) != t_INT) pari_err_TYPE("plotcopy",yoff);
    x = itos(xoff);
    y = itos(yoff);
  }
  switch (flag & ~RECT_CP_RELATIVE)
  {
    case RECT_CP_NW: break;
    case RECT_CP_SW: y = RYsize(d) - RYsize(s) - y; break;
    case RECT_CP_SE: y = RYsize(d) - RYsize(s) - y; /* fall through */
    case RECT_CP_NE: x = RXsize(d) - RXsize(s) - x; break;
  }
  for (R = RHead(s); R; R = RoNext(R))
  {
    RectObj *o;
    switch(RoType(R))
    {
      case ROt_PT:
        o = (RectObj*)cp(R, sizeof(RectObj1P));
        RoPTx(o) += x; RoPTy(o) += y;
        break;
      case ROt_LN: case ROt_BX: case ROt_FBX:
        o = (RectObj*)cp(R, sizeof(RectObj2P));
        RoLNx1(o) += x; RoLNy1(o) += y;
        RoLNx2(o) += x; RoLNy2(o) += y;
        break;
      case ROt_MP: case ROt_ML:
        o = (RectObj*)cp(R, sizeof(RectObjMP));
        RoMPxs(o) = (double*)cp(RoMPxs(R), sizeof(double)*RoMPcnt(o));
        RoMPys(o) = (double*)cp(RoMPys(R), sizeof(double)*RoMPcnt(o));
        for (i=0; i<RoMPcnt(o); i++) { RoMPxs(o)[i] += x; RoMPys(o)[i] += y; }
        break;
      case ROt_ST:
        o = (RectObj*)cp(R, sizeof(RectObjST));
        RoSTs(o) = (char*)cp(RoSTs(R),RoSTl(R)+1);
        RoSTx(o) += x; RoSTy(o) += y;
        break;
      default: /* ROt_PTT, ROt_LNT, ROt_PTS */
        o = (RectObj*)cp(R, sizeof(RectObjPN));
        break;
    }
    RoNext(tail) = o; tail = o;
  }
  RoNext(tail) = NULL; RTail(d) = tail;
}

enum {CLIPLINE_NONEMPTY = 1, CLIPLINE_CLIP_1 = 2, CLIPLINE_CLIP_2 = 4};
/* A simpler way is to clip by 4 half-planes */
static int
clipline(double xmin, double xmax, double ymin, double ymax,
         double *x1p, double *y1p, double *x2p, double *y2p)
{
  int xy_exch = 0, rc = CLIPLINE_NONEMPTY;
  double t, sl;
  double xi, xmn, xmx;
  double yi, ymn, ymx;
  int x1_is_ymn, x1_is_xmn;
  double x1 = *x1p, x2 = *x2p, y1 = *y1p, y2 = *y2p;

  if ((x1 < xmin &&  x2 < xmin) || (x1 > xmax && x2 > xmax))
    return 0;
  if (fabs(x1 - x2) < fabs(y1 - y2)) { /* Exchange x and y */
    xy_exch = 1;
    dswap(xmin, ymin); dswap(x1, y1);
    dswap(xmax, ymax); dswap(x2, y2);
  }

  /* Build y as a function of x */
  xi = x1;
  yi = y1;
  sl = x1==x2? 0: (y2 - yi)/(x2 - xi);

  if (x1 > x2) {
    x1_is_xmn = 0;
    xmn = x2;
    xmx = x1;
  } else {
    x1_is_xmn = 1;
    xmn = x1;
    xmx = x2;
  }

  if (xmn < xmin) {
    xmn = xmin;
    rc |= x1_is_xmn? CLIPLINE_CLIP_1: CLIPLINE_CLIP_2;
  }
  if (xmx > xmax) {
    xmx = xmax;
    rc |= x1_is_xmn? CLIPLINE_CLIP_2: CLIPLINE_CLIP_1;
  }
  if (xmn > xmx) return 0;

  ymn = yi + (xmn - xi)*sl;
  ymx = yi + (xmx - xi)*sl;

  if (sl < 0) t = ymn, ymn = ymx, ymx = t;
  if (ymn > ymax || ymx < ymin) return 0;

  if (rc & CLIPLINE_CLIP_1) x1 = x1_is_xmn? xmn: xmx;
  if (rc & CLIPLINE_CLIP_2) x2 = x1_is_xmn? xmx: xmn;

  /* Now we know there is an intersection, need to move x1 and x2 */
  x1_is_ymn = ((sl >= 0) == (x1 < x2));
  if (ymn < ymin) {
    double x = (ymin - yi)/sl + xi; /* slope != 0  ! */
    if (x1_is_ymn) x1 = x, rc |= CLIPLINE_CLIP_1;
    else           x2 = x, rc |= CLIPLINE_CLIP_2;
  }
  if (ymx > ymax) {
    double x = (ymax - yi)/sl + xi; /* slope != 0  ! */
    if (x1_is_ymn) x2 = x, rc |= CLIPLINE_CLIP_2;
    else           x1 = x, rc |= CLIPLINE_CLIP_1;
  }
  if (rc & CLIPLINE_CLIP_1) y1 = yi + (x1 - xi)*sl;
  if (rc & CLIPLINE_CLIP_2) y2 = yi + (x2 - xi)*sl;
  if (xy_exch) /* Exchange x and y */
    *x1p = y1, *x2p = y2, *y1p = x1, *y2p = x2;
  else
    *x1p = x1, *x2p = x2, *y1p = y1, *y2p = y2;
  return rc;
}

void
plotclip(long rect)
{
  PariRect *s = check_rect_init(rect);
  RectObj *next, *R = RHead(s), **prevp = &RHead(s);
  double xmin = 0, xmax = RXsize(s);
  double ymin = 0, ymax = RYsize(s);

  for (; R; R = next) {
    int did_clip = 0;
#define REMOVE() { *prevp = next; freeobj(R); break; }
#define NEXT() { prevp = &RoNext(R); break; }

    next = RoNext(R);
    switch(RoType(R)) {
      case ROt_PT:
        if ( DTOL(RoPTx(R)) < xmin || DTOL(RoPTx(R)) > xmax
          || DTOL(RoPTy(R)) < ymin || DTOL(RoPTy(R)) > ymax) REMOVE();
        NEXT();
      case ROt_BX: case ROt_FBX:
        if (RoLNx1(R) < xmin) RoLNx1(R) = xmin, did_clip = 1;
        if (RoLNx2(R) < xmin) RoLNx2(R) = xmin, did_clip = 1;
        if (RoLNy1(R) < ymin) RoLNy1(R) = ymin, did_clip = 1;
        if (RoLNy2(R) < ymin) RoLNy2(R) = ymin, did_clip = 1;
        if (RoLNx1(R) > xmax) RoLNx1(R) = xmax, did_clip = 1;
        if (RoLNx2(R) > xmax) RoLNx2(R) = xmax, did_clip = 1;
        if (RoLNy1(R) > ymax) RoLNy1(R) = ymax, did_clip = 1;
        if (RoLNy2(R) > ymax) RoLNy2(R) = ymax, did_clip = 1;
        /* Remove zero-size clipped boxes */
        if (did_clip && RoLNx1(R) == RoLNx2(R)
                     && RoLNy1(R) == RoLNy2(R)) REMOVE();
        NEXT();
      case ROt_LN:
        if (!clipline(xmin, xmax, ymin, ymax,
                      &RoLNx1(R), &RoLNy1(R),
                      &RoLNx2(R), &RoLNy2(R))) REMOVE();
        NEXT();
      case ROt_MP: {
        int c = RoMPcnt(R), f = 0, t = 0;

        while (f < c) {
          if ( DTOL(RoMPxs(R)[f]) >= xmin && DTOL(RoMPxs(R)[f]) <= xmax
            && DTOL(RoMPys(R)[f]) >= ymin && DTOL(RoMPys(R)[f]) <= ymax) {
            if (t != f) {
              RoMPxs(R)[t] = RoMPxs(R)[f];
              RoMPys(R)[t] = RoMPys(R)[f];
            }
            t++;
          }
          f++;
        }
        if (t == 0) REMOVE();
        RoMPcnt(R) = t;
        NEXT();
      }
      case ROt_ML: {
        /* Hard case. Break a multiline into several pieces
         * if some part is clipped. */
        int c = RoMPcnt(R) - 1;
        int f = 0, t = 0, had_lines = 0, had_hole = 0, rc;
        double ox = RoMLxs(R)[0], oy = RoMLys(R)[0], oxn, oyn;

        while (f < c) {
        /* Endpoint of this segment is startpoint of next one: need to
         * preserve it if it is clipped. */
          oxn = RoMLxs(R)[f+1];
          oyn = RoMLys(R)[f+1];
          rc = clipline(xmin, xmax, ymin, ymax,
                  &ox, &oy, /* &RoMLxs(R)[f], &RoMLys(R)[f], */
                  &RoMLxs(R)[f+1], &RoMLys(R)[f+1]);
          RoMLxs(R)[f] = ox; ox = oxn;
          RoMLys(R)[f] = oy; oy = oyn;
          if (!rc) {
            if (had_lines) had_hole = 1;
            f++; continue;
          }

          if (!had_lines || (!(rc & CLIPLINE_CLIP_1) && !had_hole) ) {
            /* Continuous */
            had_lines = 1;
            if (t != f) {
              if (t == 0) {
                RoMPxs(R)[t] = RoMPxs(R)[f];
                RoMPys(R)[t] = RoMPys(R)[f];
              }
              RoMPxs(R)[t+1] = RoMPxs(R)[f+1];
              RoMPys(R)[t+1] = RoMPys(R)[f+1];
            }
            t++;
            f++;
            if (rc & CLIPLINE_CLIP_2) had_hole = 1, RoMLcnt(R) = t+1;
            continue;
          }
          /* Is not continuous, automatically R is not pari_free()ed.  */
          t++;
          RoMLcnt(R) = t;
          if (rc & CLIPLINE_CLIP_2) { /* Needs separate entry */
            RectObj *n = (RectObj*) pari_malloc(sizeof(RectObj2P));
            RoType(n) = ROt_LN;
            RoCol(n) = RoCol(R);
            RoLNx1(n) = RoMLxs(R)[f];   RoLNy1(n) = RoMLys(R)[f];
            RoLNx2(n) = RoMLxs(R)[f+1]; RoLNy2(n) = RoMLys(R)[f+1];
            RoNext(n) = next;
            RoNext(R) = n;
            /* Restore the unclipped value: */
            RoMLxs(R)[f+1] = oxn; RoMLys(R)[f+1] = oyn;
            f++;
            prevp = &RoNext(n);
          }
          if (f + 1 < c) { /* Are other lines */
            RectObj *n = (RectObj*) pari_malloc(sizeof(RectObjMP));
            RoType(n) = ROt_ML;
            RoCol(n) = RoCol(R);
            RoMLcnt(n) = c - f;
            RoMLxs(n) = cpd(RoMPxs(R) + f, c-f);
            RoMLys(n) = cpd(RoMPys(R) + f, c-f);
            RoMPxs(n)[0] = oxn;
            RoMPys(n)[0] = oyn;
            RoNext(n) = next;
            RoNext(R) = n;
            next = n;
          }
          break;
        }
        if (t == 0) REMOVE();
        NEXT();
      }
    }
#undef REMOVE
#undef NEXT
  }
}

/********************************************************************/
/**                                                                **/
/**                        HI-RES PLOT                             **/
/**                                                                **/
/********************************************************************/
static void
set_xrange(dblPointList *f, double x)
{ if (x < f->xsml) f->xsml = x;
  if (x > f->xbig) f->xbig = x; }
static void
Appendxat(dblPointList *f, dblPointList *l,long n,double x)
{ (l->d)[n] = x; l->nb = n+1; set_xrange(f,x); }
static void
set_yrange(dblPointList *f, double y)
{ if (y < f->ysml) f->ysml = y;
  if (y > f->ybig) f->ybig = y; }
static void
Appendyat(dblPointList *f, dblPointList *l,long n,double y)
{ (l->d)[n] = y; l->nb = n+1; set_yrange(f,y); }
static void
Appendx(dblPointList *f, dblPointList *l,double x) { Appendxat(f,l,l->nb,x); }
static void
Appendy(dblPointList *f, dblPointList *l,double y) { Appendyat(f,l,l->nb,y); }

static void
get_xy(long cplx, GEN t, double *x, double *y)
{
  GEN a, b;
  if (cplx)
  {
    if (typ(t) == t_VEC)
    {
      if (lg(t) != 2) pari_err_DIM("get_xy");
      t = gel(t,1);
    }
    a = real_i(t); b = imag_i(t);
  }
  else
  {
    if (typ(t) != t_VEC || lg(t) != 3) pari_err_DIM("get_xy");
    a = gel(t,1); b = gel(t,2);
  }
  *x = gtodouble(a);
  *y = gtodouble(b);
}
/* t a t_VEC (possibly a scalar if cplx), get next (x,y) coordinate starting
 * at index *i [update i] */
static void
get_xy_from_vec(long cplx, GEN t, long *i, double *x, double *y)
{
  GEN a, b;
  if (cplx)
  {
    if (typ(t) == t_VEC) t = gel(t,*i);
    a = real_i(t); b = imag_i(t); (*i)++;
  }
  else
  {
    a = gel(t, (*i)++);
    b = gel(t, (*i)++);
  }
  *x = gtodouble(a);
  *y = gtodouble(b);
}
/* X,Y t_VEC; next (x,y) coordinate starting at index i; Y ignored if (cplx) */
static void
get_xy_from_vec2(long cplx, GEN X, GEN Y, long i, double *x, double *y)
{
  GEN a, b;
  if (cplx)
  {
    GEN z = gel(X,i);
    a = real_i(z); b = imag_i(z);
  }
  else
  {
    a = gel(X,i); b = gel(Y,i);
  }
  *x = gtodouble(a);
  *y = gtodouble(b);
}

/* Convert data from GEN to double before we call plotrecthrawin. */
static dblPointList*
gtodblList(GEN data, long flags)
{
  dblPointList *l, *L;
  double *X, *Y;
  long nl=lg(data)-1, lx1, i, j;
  const long param = (flags & (PLOT_PARAMETRIC|PLOT_COMPLEX));
  const long cplx = (flags & PLOT_COMPLEX);

  if (! is_vec_t(typ(data))) pari_err_TYPE("gtodblList",data);
  if (!nl) return NULL;
  lx1 = lg(gel(data,1));
  if (!param && lx1 == 1) return NULL;

  if (nl == 1 && !cplx) pari_err_DIM("gtodblList");
  /* Allocate memory, then convert coord. to double */
  l = (dblPointList*)pari_malloc((cplx? 2*nl: nl)*sizeof(dblPointList));
  L = &l[0];
  for (i = 0; i < nl; i += cplx? 1: 2)
  {
    GEN x = gel(data,i+1), y;
    long lx = lg(x);
    if (!is_vec_t(typ(x))) pari_err_TYPE("gtodblList",x);
    if (cplx) y = NULL;
    else
    {
      y = gel(data,i+2);
      if (!is_vec_t(typ(y))) pari_err_TYPE("gtodblList",y);
      if (lg(y) != lx || (!param && lx != lx1)) pari_err_DIM("gtodblList");
    }
    lx--;
    l[i].d   = X = (double*)pari_malloc(lx*sizeof(double));
    l[i+1].d = Y = (double*)pari_malloc(lx*sizeof(double));
    for (j=1; j<=lx; j++) get_xy_from_vec2(cplx, x, y, j, X+(j-1), Y+(j-1));
    l[i].nb = l[i+1].nb = lx;
  }

  /* Compute extremas */
  if (param)
  {
    L->nb = cplx? nl: nl/2;
    for (i=0; i < L->nb; i+=2)
      if (l[i+1].nb) break;
    if (i >= L->nb) { pari_free(l); return NULL; }
    L->xsml = L->xbig = l[i  ].d[0];
    L->ysml = L->ybig = l[i+1].d[0];
    for (; i < L->nb; i+=2)
    {
      long nbi = l[i+1].nb; X = l[i].d; Y = l[i+1].d;
      for (j = 0; j < nbi; j++) { set_xrange(L, X[j]); set_yrange(L, Y[j]); }
    }
  }
  else
  {
    L->nb = nl-1;
    X = L->d;   L->xsml = L->xbig = X[0];
    Y = l[1].d; L->ysml = L->ybig = Y[0];
    for (j=0; j < l[1].nb; j++) set_xrange(L, X[j]);
    for (i=1; i <= L->nb; i++)
    {
      long nbi = l[i].nb; Y = l[i].d;
      for (j = 0; j < nbi; j++) set_yrange(L, Y[j]);
    }
  }
  return l;
}

/* (x+y)/2 */
static GEN
rmiddle(GEN x, GEN y) { GEN z = addrr(x,y); shiftr_inplace(z,-1); return z; }

static void
single_recursion(void *E, GEN(*eval)(void*,GEN), dblPointList *pl,
                 GEN xleft,double yleft, GEN xright,double yright,long depth)
{
  GEN xx;
  pari_sp av = avma;
  double yy, dy=pl[0].ybig - pl[0].ysml;

  if (depth==RECUR_MAXDEPTH) return;

  xx = rmiddle(xleft,xright);
  yy = gtodouble(eval(E,xx));

  if (dy && fabs(yleft+yright-2*yy) < dy*RECUR_PREC) return;
  single_recursion(E,eval, pl,xleft,yleft, xx,yy, depth+1);
  Appendx(&pl[0],&pl[0],rtodbl(xx));
  Appendy(&pl[0],&pl[1],yy);
  single_recursion(E,eval, pl,xx,yy, xright,yright, depth+1);
  avma = av;
}

static void
param_recursion(void *E,GEN(*eval)(void*,GEN), long cplx, dblPointList *pl,
  GEN tleft,double xleft, double yleft,
  GEN tright,double xright,double yright, long depth)
{
  GEN tt;
  pari_sp av = avma;
  double xx, dy=pl[0].ybig - pl[0].ysml;
  double yy, dx=pl[0].xbig - pl[0].xsml;

  if (depth==RECUR_MAXDEPTH) return;

  tt = rmiddle(tleft,tright);
  get_xy(cplx, eval(E,tt), &xx,&yy);

  if (dx && dy && fabs(xleft+xright-2*xx) < dx*RECUR_PREC
               && fabs(yleft+yright-2*yy) < dy*RECUR_PREC) return;
  param_recursion(E,eval, cplx, pl, tleft,xleft,yleft, tt,xx,yy, depth+1);
  Appendx(&pl[0],&pl[0],xx);
  Appendy(&pl[0],&pl[1],yy);
  param_recursion(E,eval,cplx, pl, tt,xx,yy, tright,xright,yright, depth+1);
  avma = av;
}

/* Graph 'code' for parameter values in [a,b], using 'N' sample points
 * (0 = use a default value); code is either a t_CLOSURE or a t_POL or a
 * t_VEC of two t_POLs from rectsplines. Returns a dblPointList of
 * (absolute) coordinates. */
static dblPointList *
plotrecthin(void *E, GEN(*eval)(void*, GEN), GEN a, GEN b, ulong flags,
            long N, long prec)
{
  const double INF = 1.0/0.0;
  const long param = flags & (PLOT_PARAMETRIC|PLOT_COMPLEX);
  const long recur = flags & PLOT_RECURSIVE;
  const long cplx = flags & PLOT_COMPLEX;
  GEN t,dx,x;
  dblPointList *pl;
  long tx, i, j, sig, nc, nl, ncoords, nbpoints, non_vec = 0;
  pari_sp av = avma;

  sig = gcmp(b,a); if (!sig) return NULL;
  if (sig < 0) swap(a, b);
  if (N == 1) pari_err_DOMAIN("ploth", "#points", "<", gen_2, stoi(N));
  if (!N) N = recur? 8: (param? 1500: 1000);
  /* compute F(a) to determine nc = #curves; nl = #coord. lists */
  x = gtofp(a, prec);
  t = eval(E, x); tx = typ(t);
  if (cplx) nc = nl = (tx == t_VEC)? lg(t)-1: 1;
  else if (param)
  {
    if (tx != t_VEC) pari_err_TYPE("ploth [not a t_VEC in parametric plot]", t);
    nl = lg(t)-1; nc = nl >> 1;
    if (odd(nl)) pari_err_TYPE("ploth [odd #components in parametric plot]",t);
  }
  else if (!is_matvec_t(tx)) { nl = 2; non_vec = 1; nc = 1; }
  else
  {
    if (tx != t_VEC) pari_err_TYPE("ploth [not a t_VEC]",t);
    nl = lg(t);
    nc = nl-1;
  }
  if (!nc) { avma = av; return NULL; }
  if (recur && nc > 1) pari_err_TYPE("ploth [multi-curves + recursive]",t);

  ncoords = cplx? 2*nl: nl;
  nbpoints = recur? N << RECUR_MAXDEPTH: N;
  pl=(dblPointList*) pari_malloc(ncoords*sizeof(dblPointList));
  /* set [xy]sml,[xy]big to default values */
  if (param)
  {
    pl[0].xsml = INF;
    pl[0].xbig =-INF;
  } else {
    pl[0].xsml = gtodouble(a);
    pl[0].xbig = gtodouble(b);
  }
  pl[0].ysml = INF;
  pl[0].ybig =-INF;
  for (i = 0; i < ncoords; i++)
  {
    pl[i].d = (double*)pari_malloc((nbpoints+1)*sizeof(double));
    pl[i].nb=0;
  }
  dx = divru(gtofp(gsub(b,a),prec), N-1);
  if (recur)
  { /* recursive plot */
    double yleft, yright = 0;
    if (param)
    {
      GEN tleft = cgetr(prec), tright = cgetr(prec);
      double xleft, xright = 0;
      pari_sp av2 = avma;
      affgr(a,tleft);
      t = eval(E, tleft);
      get_xy(cplx,t, &xleft,&yleft);
      for (i=0; i<N-1; i++, avma = av2)
      {
        if (i) { affrr(tright,tleft); xleft = xright; yleft = yright; }
        addrrz(tleft,dx,tright);
        t = eval(E, tright);
        get_xy(cplx,t, &xright,&yright);
        Appendx(&pl[0],&pl[0],xleft);
        Appendy(&pl[0],&pl[1],yleft);
        param_recursion(E,eval, cplx, pl, tleft,xleft,yleft, tright,xright,yright, 0);
      }
      Appendx(&pl[0],&pl[0],xright);
      Appendy(&pl[0],&pl[1],yright);
    }
    else /* single curve */
    {
      GEN xleft = cgetr(prec), xright = cgetr(prec);
      pari_sp av2 = avma;
      affgr(a,xleft);
      yleft = gtodouble(eval(E,xleft));
      for (i=0; i<N-1; i++, avma = av2)
      {
        addrrz(xleft,dx,xright);
        yright = gtodouble(eval(E,xright));

        Appendx(&pl[0],&pl[0],rtodbl(xleft));
        Appendy(&pl[0],&pl[1],yleft);

        single_recursion(E,eval, pl,xleft,yleft,xright,yright,0);
        affrr(xright,xleft); yleft = yright;
      }
      Appendx(&pl[0],&pl[0],rtodbl(xright));
      Appendy(&pl[0],&pl[1],yright);
    }
  }
  else /* non-recursive plot */
  {
    pari_sp av2;
    GEN worker = NULL, vx = NULL;
    long pending = 0, workid;
    struct pari_mt pt;
    if (flags & PLOT_PARA && eval == gp_call)
    {
      worker = snm_closure(is_entry("_parvector_worker"), mkvec((GEN)E));
      mt_queue_start_lim(&pt, worker, N-1);
      vx = mkvec(x);
    }
    av2 = avma;
    if (param)
    {
      for (i=0; i<N || pending; i++, avma = av2)
      {
        long k, nt;
        if (worker)
        {
          mt_queue_submit(&pt, i, i<N ? vx : NULL);
          t = mt_queue_get(&pt, &workid, &pending);
          if (!t) continue;
        }
        else
        {
          t = eval(E,x);
          workid = i;
        }
        if (typ(t) != t_VEC)
        {
          if (cplx) nt = 1;
          else nt = 0; /* trigger error */
        }
        else
          nt = lg(t)-1;
        if (nt != nl) pari_err_DIM("plotrecth");
        k = 0; j = 1;
        while (j <= nl)
        {
          double xx, yy;
          get_xy_from_vec(cplx, t, &j, &xx, &yy);
          Appendxat(&pl[0], &pl[k++], workid, xx);
          Appendyat(&pl[0], &pl[k++], workid, yy);
        }
        if (i<N) affrr(addrr(x,dx), x);
      }
    }
    else if (non_vec)
      for (i=0; i<N || pending; i++, avma = av2)
      {
        if (worker)
        {
          mt_queue_submit(&pt, i, i<N ? vx : NULL);
          t = mt_queue_get(&pt, &workid, &pending);
        }
        else
        {
          t = eval(E,x);
          workid = i;
        }
        if (t) Appendyat(&pl[0], &pl[1], workid, gtodouble(t));
        if (i<N)
        {
          pl[0].d[i] = gtodouble(x);
          affrr(addrr(x,dx), x);
        }
      }
    else /* vector of non-parametric curves */
      for (i=0; i<N || pending; i++, avma = av2)
      {
        if (worker)
        {
          mt_queue_submit(&pt, i, i<N ? vx : NULL);
          t = mt_queue_get(&pt, &workid, &pending);
        }
        else
        {
          t = eval(E,x);
          workid = i;
        }
        if (t)
        {
          if (typ(t) != t_VEC || lg(t) != nl) pari_err_DIM("plotrecth");
          for (j=1; j<nl; j++)
            Appendyat(&pl[0], &pl[j], workid, gtodouble(gel(t,j)));
        }
        if (i<N)
        {
          pl[0].d[i] = gtodouble(x);
          affrr(addrr(x,dx), x);
        }
      }
    if (worker) mt_queue_end(&pt);
  }
  pl[0].nb = nc; avma = av; return pl;
}

static GEN
spline_eval(void* E, GEN x) { return gsubst((GEN)E,0,x); }

/* Uses highlevel plotting functions to implement splines as
   a low-level plotting function. */
static void
rectsplines(long ne, double *x, double *y, long lx, long flag)
{
  long i, j;
  pari_sp av0 = avma;
  GEN X = pol_x(0), xa = cgetg(lx+1, t_VEC), ya = cgetg(lx+1, t_VEC);
  GEN tas, pol3;
  long param = flag & PLOT_PARAMETRIC;
  const long fl = param | PLOT_RECURSIVE | PLOT_NO_RESCALE | PLOT_NO_FRAME
                        | PLOT_NO_AXE_Y | PLOT_NO_AXE_X;

  if (lx < 4) pari_err(e_MISC, "Too few points (%ld) for spline plot", lx);
  for (i = 1; i <= lx; i++) {
    gel(xa,i) = dbltor(x[i-1]);
    gel(ya,i) = dbltor(y[i-1]);
  }
  if (param) {
    tas = new_chunk(4);
    for (j = 1; j <= 4; j++) gel(tas,j-1) = utoipos(j);
    pol3 = cgetg(3, t_VEC);
  }
  else
    tas = pol3 = NULL; /* gcc -Wall */
  for (i = 0; i <= lx - 4; i++) {
    pari_sp av = avma;

    xa++; ya++;
    if (param) {
      gel(pol3,1) = polint_i(tas, xa, X, 4, NULL);
      gel(pol3,2) = polint_i(tas, ya, X, 4, NULL);
    } else {
      pol3 = polint_i(xa, ya, X, 4, NULL);
      tas = xa;
    }
    /* Start with 3 points */
    plotrecth((void*)pol3, &spline_eval, ne,
               i== 0 ? gel(tas,0) : gel(tas,1),
               i==lx-4 ? gel(tas,3) : gel(tas,2),
               fl, 2, DEFAULTPREC);
    avma = av;
  }
  avma = av0;
}

static void
pari_get_fmtplot(GEN fmt, PARI_plot *T)
{
  char *f = GSTR(fmt);
  if (!strcmp(f, "svg")) pari_get_svgplot(T);
  else if (!strcmp(f, "ps")) pari_get_psplot(T);
  else pari_err_TYPE("plotexport [unknown format]", fmt);
}
static GEN
fmt_convert(GEN fmt, GEN w, GEN x, GEN y, PARI_plot *T)
{
  char *f, *s = NULL;
  if (typ(fmt) != t_STR) pari_err_TYPE("plotexport",fmt);
  f = GSTR(fmt);
  if (!strcmp(f, "svg"))
    s = rect2svg(w,x,y,T);
  else if (!strcmp(f, "ps"))
    s = rect2ps(w,x,y,T);
  else
    pari_err_TYPE("plotexport [unknown format]", fmt);
  return strtoGENstr(s);
}

static void
Draw(PARI_plot *T, GEN w, GEN x, GEN y)
{ if (T->draw) T->draw(T, w,x,y); else get_plot_null(NULL); }
static void
set_range(double m, double M, double *sml, double *big)
{
  if (M - m < 1.e-9)
  {
    double d = fabs(m)/10; if (!d) d = 0.1;
    M += d; m -= d;
  }
  *sml = m; *big = M;
}
/* Plot a dblPointList. Complete with axes, bounding box, etc.
 *
 * data is an array of structs. Its meaning depends on flags :
 *
 * + data[0] contains global extremas, the number of curves to plot
 *   (data[0].nb) and a list of doubles (first set of x-coordinates).
 *
 * + data[i].nb (i>0) contains the number of points in the list
 *   data[i].d (hopefully, data[2i].nb=data[2i+1].nb when i>0...)
 *
 * + If flags contain PLOT_PARAMETRIC, the array length should be
 *   even, and successive pairs (data[2i].d, data[2i+1].d) represent
 *   curves to plot.
 *
 * + If there is no such flag, the first element is an array with
 *   x-coordinates and the following ones contain y-coordinates.
 * If W != NULL, output wrt this PARI_plot using two drawing rectangles:
 * one for labels, another for graphs. Else draw to rectwindow ne without
 * labels.
 * If fmt != NULL (requires W != NULL), output is a t_STR containing the
 * converted picture, else a bounding box */
static GEN
plotrecthrawin(GEN fmt, PARI_plot *W, long ne, dblPointList *data, long flags)
{
  const long param = flags & (PLOT_PARAMETRIC|PLOT_COMPLEX);
  const long max_graphcolors = lg(GP_DATA->graphcolors)-1;
  const pari_sp av = avma;
  dblPointList x, y;
  double xsml, xbig, ysml, ybig;
  long ltype, i, nc, w[3], wx[3], wy[3];

  if (!data) return cgetg(1,t_VEC);
  x = data[0]; nc = x.nb;
  set_range(x.xsml, x.xbig, &xsml, &xbig);
  set_range(x.ysml, x.ybig, &ysml, &ybig);
  if (W)
  { /* actual output; else output to rectwindow: no labels */
    const long se = NUMRECT-2;
    long lm, rm, tm, bm;
    char YBIG[16], YSML[16], XSML[16], XBIG[16];
    /* left/right/top/bottom margin */
    sprintf(YSML,"%.5g", ysml); sprintf(YBIG,"%.5g", ybig);
    sprintf(XSML,"%.5g", xsml); sprintf(XBIG,"%.5g", xbig);
    /* left margin has y labels with hgap on both sides of text */
    lm = maxss(strlen(YSML),strlen(YBIG))*W->fwidth + 2*W->hunit-1;
    rm = W->hunit-1;
    tm = W->vunit-1;
    bm = W->vunit+W->fheight-1;
    w[0] = wx[0] = wy[0] = evaltyp(t_VECSMALL) | evallg(3);
    w[1] = se; wx[1] = 0;  wy[1] = 0;
    w[2] = ne; wx[2] = lm; wy[2] = tm;
   /* Window (width x height) is given in pixels, correct pixels are 0..n-1,
    * whereas rect functions work with windows whose pixel range is [0,n] */
    initrect_i(se, W->width - 1, W->height - 1);
    initrect_i(ne, W->width - (lm+rm) - 1, W->height - (tm+bm) - 1);
    /* draw labels on se */
    _move(se,lm,0); plotstring(se, YBIG, RoSTdirRIGHT|RoSTdirHGAP|RoSTdirTOP);
    _move(se,lm,W->height-bm); plotstring(se,YSML, RoSTdirRIGHT|RoSTdirHGAP|RoSTdirVGAP);
    _move(se,lm,W->height-bm); plotstring(se, XSML, RoSTdirLEFT|RoSTdirTOP);
    _move(se,W->width-rm-1, W->height-bm); plotstring(se, XBIG, RoSTdirRIGHT|RoSTdirTOP);
  }
  if (!(flags & PLOT_NO_RESCALE)) plotscale0(ne, xsml, xbig, ysml, ybig);
  if (!(flags & PLOT_NO_FRAME))
  {
    long fl = (flags & PLOT_NODOUBLETICK)? TICKS_CLOCKW|TICKS_NODOUBLE
                                         : TICKS_CLOCKW;
    PARI_plot T, *pl;
    if (W) pl = W; else { pl = &T; pari_get_plot(pl); }
    plotlinetype(ne, -2); /* frame */
    current_color[ne] = colormap_to_color(DEFAULT_COLOR);
    _move(ne,xsml,ysml);
    _box(ne,xbig,ybig);
    if (!(flags & PLOT_NO_TICK_X)) {
      rectticks(pl, ne, xsml, ysml, xbig, ysml, xsml, xbig, fl);
      rectticks(pl, ne, xbig, ybig, xsml, ybig, xbig, xsml, fl);
    }
    if (!(flags & PLOT_NO_TICK_Y)) {
      rectticks(pl, ne, xbig, ysml, xbig, ybig, ysml, ybig, fl);
      rectticks(pl, ne, xsml, ybig, xsml, ysml, ybig, ysml, fl);
    }
  }
  if (!(flags & PLOT_NO_AXE_Y) && (xsml<=0 && xbig >=0))
  {
    plotlinetype(ne, -1); /* axes */
    current_color[ne] = colormap_to_color(AXIS_COLOR);
    _move(ne,0.0,ysml);
    _line(ne,0.0,ybig);
  }
  if (!(flags & PLOT_NO_AXE_X) && (ysml<=0 && ybig >=0))
  {
    plotlinetype(ne, -1); /* axes */
    current_color[ne] = colormap_to_color(AXIS_COLOR);
    _move(ne,xsml,0.0);
    _line(ne,xbig,0.0);
  }

  if (param) {
    i = 0;
    flags |= PLOT_PARAMETRIC;
    flags &= (~PLOT_COMPLEX); /* turn COMPLEX to PARAMETRIC*/
  } else i = 1;
  for (ltype = 0; ltype < nc; ltype++)
  {
    long c = GP_DATA->graphcolors[1+(ltype%max_graphcolors)];
    current_color[ne] = colormap_to_color(c);
    if (param) x = data[i++];

    y = data[i++];
    if (flags & (PLOT_POINTS_LINES|PLOT_POINTS)) {
      plotlinetype(ne, plotpoint_itype + ltype); /* Graphs */
      plotpointtype(ne,plotpoint_itype + ltype); /* Graphs */
      plotpoints0(ne, x.d, y.d, y.nb);
      if (!(flags & PLOT_POINTS_LINES)) continue;
    }

    if (flags & PLOT_SPLINES) {
      /* rectsplines will call us back with ltype == 0 */
      int old = rectline_itype;
      rectline_itype = rectline_itype + ltype;
      rectsplines(ne, x.d, y.d, y.nb, flags);
      rectline_itype = old;
    } else {
      plotlinetype(ne, rectline_itype + ltype); /* Graphs */
      rectlines0(ne, x.d, y.d, y.nb, 0);
    }
  }
  for (i--; i>=0; i--) pari_free(data[i].d);
  pari_free(data);

  if (W)
  {
    GEN s = NULL;
    if (fmt) s = fmt_convert(fmt, w, wx, wy, W); else Draw(W, w,wx,wy);
    plotkill(w[1]);
    plotkill(w[2]);
    if (fmt) return s;
  }
  avma = av;
  retmkvec4(dbltor(xsml), dbltor(xbig), dbltor(ysml), dbltor(ybig));
}

/*************************************************************************/
/*                                                                       */
/*                          HI-RES FUNCTIONS                             */
/*                                                                       */
/*************************************************************************/
/* If T != NULL, draw using the attached graphic (using rectwindow ne as a temp)
 * Else write to rectwindow 'ne'.
 * Graph y=f(x), x=a..b, use n points */
static GEN
plotrecth_i(GEN fmt, void *E, GEN(*f)(void*,GEN), PARI_plot *T, long ne,
            GEN a,GEN b, ulong flags,long n, long prec)
{
  dblPointList *pl = plotrecthin(E,f, a,b, flags, n, prec);
  return plotrecthrawin(fmt, T, ne, pl, flags);
}
GEN
plotrecth(void *E, GEN(*f)(void*,GEN), long ne, GEN a,GEN b,
          ulong flags, long n, long prec)
{ return plotrecth_i(NULL, E,f, NULL, ne, a,b, flags&~PLOT_PARA, n, prec); }
GEN
plotrecth0(long ne, GEN a,GEN b,GEN code,ulong flags,long n, long prec)
{ EXPR_WRAP(code, plotrecth(EXPR_ARG, ne, a,b, flags, n, prec)); }
GEN
ploth(void *E, GEN(*f)(void*,GEN), GEN a, GEN b,long flags, long n, long prec)
{
  PARI_plot T; pari_get_plot(&T);
  return plotrecth_i(NULL, E,f, &T, NUMRECT-1, a,b, flags&~PLOT_PARA,n, prec);
}
GEN
parploth(GEN a, GEN b, GEN code, long flags, long n, long prec)
{
  PARI_plot T; pari_get_plot(&T);
  return plotrecth_i(NULL, code,gp_call,&T, NUMRECT-1, a,b, flags|PLOT_PARA,n, prec);
}
GEN
ploth0(GEN a, GEN b, GEN code, long flags,long n, long prec)
{ EXPR_WRAP(code, ploth(EXPR_ARG, a,b,flags,n, prec)); }
GEN
psploth(void *E, GEN(*f)(void*,GEN), GEN a,GEN b, long flags, long n, long prec)
{
  PARI_plot T; pari_get_psplot(&T); T.draw = &_psdraw;
  return plotrecth_i(NULL, E,f, &T, NUMRECT-1, a,b, flags&~PLOT_PARA,n, prec);
}
GEN
psploth0(GEN a, GEN b, GEN code, long flags, long n, long prec)
{ EXPR_WRAP(code, psploth(EXPR_ARG, a, b, flags, n, prec)); }
GEN
plothexport(GEN fmt, void *E, GEN(*f)(void*,GEN), GEN a,GEN b, long flags,
            long n, long prec)
{
  pari_sp av = avma;
  GEN s;
  PARI_plot T; pari_get_fmtplot(fmt, &T);
  s = plotrecth_i(fmt, E,f, &T, NUMRECT-1, a,b, flags&~PLOT_PARA,n, prec);
  return gerepileuptoleaf(av, s);
}
GEN
plothexport0(GEN fmt, GEN a, GEN b, GEN code, long flags, long n, long prec)
{ EXPR_WRAP(code, plothexport(fmt, EXPR_ARG, a, b, flags, n, prec)); }

/* Draw list of points */
static GEN
plotrecthraw_i(GEN fmt, PARI_plot *T, long ne, GEN data, long flags)
{
  dblPointList *pl = gtodblList(data,flags);
  return plotrecthrawin(fmt, T, ne, pl, flags);
}
static GEN
plothraw_i(GEN fmt, PARI_plot *T, GEN X, GEN Y, long flag)
{
  pari_sp av = avma;
  switch (flag) {
    case 0: flag = PLOT_PARAMETRIC|PLOT_POINTS; break;
    case 1: flag = PLOT_PARAMETRIC; break;
    default: flag |= PLOT_PARAMETRIC; break;
  }
  return gerepileupto(av, plotrecthraw_i(fmt, T, NUMRECT-1, mkvec2(X,Y), flag));
}
GEN
plothraw(GEN X, GEN Y, long flags)
{ PARI_plot T; pari_get_plot(&T); return plothraw_i(NULL,&T,X,Y,flags); }
GEN
psplothraw(GEN X, GEN Y, long flags)
{ PARI_plot T; pari_get_psplot(&T); T.draw = &_psdraw;
  return plothraw_i(NULL,&T,X,Y,flags); }
GEN
plotrecthraw(long ne, GEN data, long flags)
{ return plotrecthraw_i(NULL, NULL, ne, data, flags); }
GEN
plothrawexport(GEN fmt, GEN X, GEN Y, long flags)
{ PARI_plot T; pari_get_fmtplot(fmt,&T); return plothraw_i(fmt,&T,X,Y,flags); }

GEN
plothsizes(long flag)
{
  GEN vect = cgetg(1+8,t_VEC);
  PARI_plot T;

  pari_get_plot(&T);
  gel(vect,1) = stoi(T.width);
  gel(vect,2) = stoi(T.height);
  if (flag) {
    gel(vect,3) = dbltor(T.hunit*1.0/T.width);
    gel(vect,4) = dbltor(T.vunit*1.0/T.height);
    gel(vect,5) = dbltor(T.fwidth*1.0/T.width);
    gel(vect,6) = dbltor(T.fheight*1.0/T.height);
  } else {
    gel(vect,3) = stoi(T.hunit);
    gel(vect,4) = stoi(T.vunit);
    gel(vect,5) = stoi(T.fwidth);
    gel(vect,6) = stoi(T.fheight);
  }
  gel(vect,7) = stoi(T.dwidth);
  gel(vect,8) = stoi(T.dheight);
  return vect;
}

/*************************************************************************/
/*                                                                       */
/*                         POSTSCRIPT OUTPUT                             */
/*                                                                       */
/*************************************************************************/
static long
wxy_n(GEN wxy)
{
  long n;
  switch(typ(wxy))
  {
    case t_INT: return 1;
    case t_VEC:
      n = lg(wxy)-1;
      if (n%3) pari_err_DIM("plotdraw");
      return n/3;
  }
  pari_err_TYPE("plotdraw",wxy);
  return 0;/*LCOV_EXCL_LINE*/
}
static void
wxy_init(GEN wxy, GEN W, GEN X, GEN Y, PARI_plot *T)
{
  long i, l = lg(X);
  if (typ(wxy) == t_INT)
  {
    W[1] = itos(wxy); check_rect_init(W[1]);
    X[1] = 0;
    Y[1] = 0; return;
  }
  for (i = 1; i < l; i++)
  {
    GEN w = gel(wxy,3*i-2), x = gel(wxy,3*i-1), y = gel(wxy,3*i);
    if (typ(w) != t_INT) pari_err_TYPE("plotdraw",w);
    if (T) {
      X[i] = DTOL(gtodouble(x)*(T->width - 1));
      Y[i] = DTOL(gtodouble(y)*(T->height - 1));
    } else {
      X[i] = gtos(x);
      Y[i] = gtos(y);
    }
    W[i] = itos(w); check_rect_init(W[i]);
  }
}
/* if flag is set, rescale wrt T */
static void
gendraw(PARI_plot *T, GEN wxy, long flag)
{
  long n = wxy_n(wxy);
  /* malloc mandatory in case draw() forks then pari_close() */
  GEN W = cgetalloc(t_VECSMALL, n+1); /* win number */
  GEN X = cgetalloc(t_VECSMALL, n+1);
  GEN Y = cgetalloc(t_VECSMALL, n+1); /* (x,y)-offset */
  wxy_init(wxy, W,X,Y, flag? T: NULL);
  Draw(T,W,X,Y);
  pari_free(W);
  pari_free(X);
  pari_free(Y);
}
void
psdraw(GEN wxy, long flag)
{ PARI_plot T; pari_get_psplot(&T); T.draw = flag? &_psdraw: &_psdraw_scale;
  gendraw(&T, wxy, flag); }
void
plotdraw(GEN wxy, long flag)
{ PARI_plot T; pari_get_plot(&T); gendraw(&T, wxy, flag); }
GEN
plotexport(GEN fmt, GEN wxy, long flag)
{
  pari_sp av = avma;
  long n = wxy_n(wxy);
  GEN w = cgetg(n+1, t_VECSMALL);
  GEN x = cgetg(n+1, t_VECSMALL);
  GEN y = cgetg(n+1, t_VECSMALL);
  PARI_plot _T, *T = flag? &_T: NULL;
  if (T) pari_get_plot(T);
  wxy_init(wxy, w, x, y, T);
  return gerepileuptoleaf(av, fmt_convert(fmt, w, x, y, T));
}

/* may be called after pari_close(): don't use the PARI stack */
void
gen_draw(struct plot_eng *eng, GEN w, GEN x, GEN y, double xs, double ys)
{
  void *data = eng->data;
  long i, j, lw = lg(w);
  long hgapsize = eng->pl->hunit, fheight = eng->pl->fheight;
  long vgapsize = eng->pl->vunit,  fwidth = eng->pl->fwidth;
  for(i = 1; i < lw; i++)
  {
    PariRect *e = &rectgraph[w[i]];
    RectObj *R;
    long x0 = x[i], y0 = y[i];
    for (R = RHead(e); R; R = RoNext(R))
    {
      long col = RoCol(R);
      switch(RoType(R))
      {
      case ROt_PT:
        eng->sc(data,col);
        eng->pt(data, DTOL((RoPTx(R)+x0)*xs), DTOL((RoPTy(R)+y0)*ys));
        break;
      case ROt_LN:
        eng->sc(data,col);
        eng->ln(data, DTOL((RoLNx1(R)+x0)*xs), DTOL((RoLNy1(R)+y0)*ys),
                      DTOL((RoLNx2(R)+x0)*xs), DTOL((RoLNy2(R)+y0)*ys));
        break;
      case ROt_BX:
        eng->sc(data,col);
        eng->bx(data,
                DTOL((RoBXx1(R)+x0)*xs),
                DTOL((RoBXy1(R)+y0)*ys),
                DTOL((RoBXx2(R)-RoBXx1(R))*xs),
                DTOL((RoBXy2(R)-RoBXy1(R))*ys));
        break;
      case ROt_FBX:
        eng->sc(data,col);
        eng->fb(data,
                DTOL((RoBXx1(R)+x0)*xs),
                DTOL((RoBXy1(R)+y0)*ys),
                DTOL((RoBXx2(R)-RoBXx1(R))*xs),
                DTOL((RoBXy2(R)-RoBXy1(R))*ys));
        break;
      case ROt_MP:
        {
          double *ptx = RoMPxs(R);
          double *pty = RoMPys(R);
          long     nb = RoMPcnt(R);
          struct plot_points *points =
            (struct plot_points *) pari_malloc(sizeof(*points)*nb);
          for(j=0;j<nb;j++)
          {
            points[j].x = DTOL((ptx[j]+x0)*xs);
            points[j].y = DTOL((pty[j]+y0)*ys);
          }
          eng->sc(data,col);
          eng->mp(data, nb, points);
          pari_free(points);
          break;
        }
      case ROt_ML:
        {
          double *ptx = RoMLxs(R);
          double *pty = RoMLys(R);
          long     nb = RoMLcnt(R);
          struct plot_points *points =
            (struct plot_points *) pari_malloc(sizeof(*points)*nb);
          for(j=0;j<nb;j++)
          {
            points[j].x = DTOL((ptx[j]+x0)*xs);
            points[j].y = DTOL((pty[j]+y0)*ys);
          }
          eng->sc(data,col);
          eng->ml(data, nb, points);
          pari_free(points);
          break;
        }
      case ROt_ST:
        {
          long dir = RoSTdir(R);
          long h = dir & RoSTdirHPOS_mask, hgap  = 0;
          long v = dir & RoSTdirVPOS_mask, vgap  = 0;
          long x, y, l = RoSTl(R);
          long shift = (h == RoSTdirLEFT ? 0 : (h == RoSTdirRIGHT? 2: 1));
          long vshift= (v == RoSTdirBOTTOM? 0: (v == RoSTdirTOP? 2: 1));
          if (dir & RoSTdirHGAP)
            hgap = (h == RoSTdirLEFT) ? hgapsize : -hgapsize;
          if (dir & RoSTdirVGAP)
            vgap = (v == RoSTdirBOTTOM) ? 2*vgapsize : -2*vgapsize;
          x = DTOL(xs * (RoSTx(R) + x0 + hgap - (l * fwidth * shift)/2));
          y = DTOL(ys * (RoSTy(R) + y0 - (vgap - vshift*(fheight-1))/2));
          eng->sc(data,col);
          eng->st(data, x, y, RoSTs(R), l);
          break;
        }
      default:
        break;
      }
    }
  }
}
/*************************************************************************/
/*                               SVG                                     */
/*************************************************************************/

struct svg_data {
  pari_str str;
  char hexcolor[8];  /* "#rrggbb\0" */
};
#define data_str(d) (&((struct svg_data*)(d))->str)
#define data_hexcolor(d) (((struct svg_data*)(d))->hexcolor)

/* Work with precision 1/scale */
static const float SVG_SCALE = 1024.0;

static float
svg_rescale(float x) { return x / SVG_SCALE; }

static void
svg_point(void *data, long x, long y)
{
  pari_str *S = data_str(data);

  str_printf(S, "<circle cx='%.2f' cy='%.2f' r='0.5' ",
    svg_rescale(x), svg_rescale(y));
  str_printf(S, "style='fill:%s;stroke:none;'/>", data_hexcolor(data));
}

static void
svg_line(void *data, long x1, long y1, long x2, long y2)
{
  pari_str *S = data_str(data);

  str_printf(S, "<line x1='%.2f' y1='%.2f' x2='%.2f' y2='%.2f' ",
    svg_rescale(x1), svg_rescale(y1), svg_rescale(x2), svg_rescale(y2));
  str_printf(S, "style='fill:none;stroke:%s;'/>", data_hexcolor(data));
}

static void
svg_rect(void *data, long x, long y, long w, long h)
{
  pari_str *S = data_str(data);

  str_printf(S, "<rect x='%.2f' y='%.2f' width='%.2f' height='%.2f' ",
    svg_rescale(x), svg_rescale(y), svg_rescale(w), svg_rescale(h));
  str_printf(S, "style='fill:none;stroke:%s;'/>", data_hexcolor(data));
}

static void
svg_fillrect(void *data, long x, long y, long w, long h)
{
  pari_str *S = data_str(data);
  const char * color = data_hexcolor(data);
  str_printf(S, "<rect x='%.2f' y='%.2f' width='%.2f' height='%.2f' ",
    svg_rescale(x), svg_rescale(y), svg_rescale(w), svg_rescale(h));
  str_printf(S, "style='fill:%s;stroke:%s;'/>", color, color);
}

static void
svg_points(void *data, long nb, struct plot_points *p)
{
  long i;
  for (i = 0; i < nb; i++)
    svg_point(data, p[i].x, p[i].y);
}

static void
svg_color(void *data, long col)
{
  static const char hex[] = "0123456789abcdef";
  char *c = data_hexcolor(data);
  int r, g, b;
  long_to_rgb(col, &r, &g, &b);
  c[0] = '#';
  c[1] = hex[r / 16];
  c[2] = hex[r & 15];
  c[3] = hex[g / 16];
  c[4] = hex[g & 15];
  c[5] = hex[b / 16];
  c[6] = hex[b & 15];
  c[7] = '\0';
}

static void
svg_lines(void *data, long nb, struct plot_points *p)
{
  long i;
  pari_str *S = data_str(data);

  str_printf(S, "<polyline points='");
  for (i = 0; i < nb; i++)
  {
    if (i > 0) str_printf(S, " ");
    str_printf(S, "%.2f,%.2f", svg_rescale(p[i].x), svg_rescale(p[i].y));
  }
  str_printf(S, "' style='fill:none;stroke:%s;'/>", data_hexcolor(data));
}

static void
svg_text(void *data, long x, long y, char *text, long numtext)
{
  pari_str *S = data_str(data);
  (void)numtext;
  str_printf(S, "<text x='%.5f' y='%.5f' font-size='%ld' style='fill:%s;'>%s</text>",
    svg_rescale(x),svg_rescale(y), 12, data_hexcolor(data), text);
}

static void
svg_head(PARI_plot *T, pari_str *S)
{
  str_printf(S, "<svg width='%ld' height='%ld' version='1.1' xmlns='http://www.w3.org/2000/svg'>", T->width, T->height);
}

static void
svg_tail(pari_str *S)
{
  str_printf(S, "</svg>");
}

char *
rect2svg(GEN w, GEN x, GEN y, PARI_plot *T)
{
  struct plot_eng pl;
  struct svg_data data;
  PARI_plot U;

  str_init(&data.str, 1);
  svg_color(&data, 0);
  if (!T)
  {
    long i, l = lg(w), xmax = 0, ymax = 0;
    T = &U; pari_get_svgplot(T);
    for (i = 1; i < l; i++)
    {
      PariRect *e = check_rect_init(w[i]);
      xmax = maxss(xmax, RXsize(e) + x[i]);
      ymax = maxss(ymax, RYsize(e) + y[i]);
    }
    T->width = xmax;
    T->height = ymax;
  }
  pl.data = &data;
  pl.sc = &svg_color;
  pl.pt = &svg_point;
  pl.ln = &svg_line;
  pl.bx = &svg_rect;
  pl.fb = &svg_fillrect;
  pl.mp = &svg_points;
  pl.ml = &svg_lines;
  pl.st = &svg_text;
  pl.pl = T;

  svg_head(T, &data.str);
  gen_draw(&pl, w, x, y, SVG_SCALE, SVG_SCALE);
  svg_tail(&data.str);

  return data.str.string;
}

/*************************************************************************/
/*                            POSTSCRIPT                                 */
/*************************************************************************/
static void
ps_sc(void *data, long col)
{
  pari_str *S = (pari_str*)data;
  int r, g, b; long_to_rgb(col, &r, &g, &b);
  if (!r && !g && !b)
    str_puts(S,"c0\n");
  else
    str_printf(S,"%.6f %.6f %.6f c\n", r/255., g/255., b/255.);
}

static void
ps_point(void *data, long x, long y)
{
  pari_str *S = (pari_str*)data;
  str_printf(S,"%ld %ld p\n",y,x);
}

static void
ps_line(void *data, long x1, long y1, long x2, long y2)
{
  pari_str *S = (pari_str*)data;
  str_printf(S,"%ld %ld m %ld %ld l\n",y1,x1,y2,x2);
  str_printf(S,"stroke\n");
}

static void
ps_rect(void *data, long x, long y, long w, long h)
{
  pari_str *S = (pari_str*)data;
  str_printf(S,"%ld %ld m %ld %ld l %ld %ld l %ld %ld l closepath stroke\n",
             y,x, y,x+w, y+h,x+w, y+h,x);
}

static void
ps_fillrect(void *data, long x, long y, long w, long h)
{
  pari_str *S = (pari_str*)data;
  str_printf(S,"%ld %ld m %ld %ld l %ld %ld l %ld %ld l closepath fill\n",
             y,x, y,x+w, y+h,x+w, y+h,x);
}

static void
ps_points(void *data, long nb, struct plot_points *p)
{
  long i;
  for (i=0; i<nb; i++) ps_point(data, p[i].x, p[i].y);
}

static void
ps_lines(void *data, long nb, struct plot_points *p)
{
  pari_str *S = (pari_str*)data;
  long i;
  str_printf(S,"%ld %ld m\n",p[0].y,p[0].x);
  for (i=1; i<nb; i++) str_printf(S, "%ld %ld l\n", p[i].y, p[i].x);
  str_printf(S,"stroke\n");
}

static void
ps_string(void *data, long x, long y, char *s, long length)
{
  pari_str *S = (pari_str*)data;
  (void)length;
  if (strpbrk(s, "(\\)")) {
    str_printf(S,"(");
    while (*s) {
      if ( *s=='(' || *s==')' || *s=='\\' ) str_putc(S,'\\');
      str_putc(S, *s);
      s++;
    }
  } else
    str_printf(S,"(%s", s);
  str_printf(S,") %ld %ld m 90 rotate show -90 rotate\n", y, x);
}

char *
rect2ps_i(GEN w, GEN x, GEN y, PARI_plot *T, int plotps)
{
  struct plot_eng pl;
  PARI_plot U;
  pari_str S;
  double xs = 0.65, ys = 0.65;
  if (T) /* res wrt T dimens */
  {
    if (plotps)
      xs = ys = 1;
    else
    {
      xs *= ((double)PS_WIDTH) / T->width;
      ys *= ((double)PS_HEIGH) / T->height;
    }
  }
  else
  {
    T = &U; pari_get_psplot(T);
  }
  str_init(&S, 1);
  /* Definitions taken from post terminal of Gnuplot. */
  str_printf(&S, "%%!\n\
50 50 translate\n\
/p {moveto 0 2 rlineto 2 0 rlineto 0 -2 rlineto closepath fill} def\n\
/c0 {0 0 0 setrgbcolor} def\n\
/c {setrgbcolor} def\n\
/l {lineto} def\n\
/m {moveto} def\n"
"/Times-Roman findfont %ld scalefont setfont\n", DTOL(T->fheight * xs));

  pl.sc = &ps_sc;
  pl.pt = &ps_point;
  pl.ln = &ps_line;
  pl.bx = &ps_rect;
  pl.fb = &ps_fillrect;
  pl.mp = &ps_points;
  pl.ml = &ps_lines;
  pl.st = &ps_string;
  pl.pl = T;
  pl.data = (void*)&S;

  if (plotps) str_printf(&S,"0 %ld translate -90 rotate\n", T->height - 50);
  gen_draw(&pl, w, x, y, xs, ys);
  str_puts(&S,"stroke showpage\n");
  *S.cur = 0; return S.string;
}
char *
rect2ps(GEN w, GEN x, GEN y, PARI_plot *T)
{ return rect2ps_i(w,x,y,T,0); }

void
pari_plot_by_file(const char *env, const char *suf, const char *img)
{
  const char *cmd, *s = pari_unique_filename_suffix("plotfile", suf);
  FILE *f = fopen(s, "w");
  if (!f) pari_err_FILE("image file", s);
  fputs(img, f); (void)fclose(f);
  cmd = os_getenv(env);
#ifdef GP_MIME_OPEN
  if (!cmd) cmd = GP_MIME_OPEN;
#else
  if (!cmd) cmd = "open -W";
#endif
  cmd = pari_sprintf("%s \"%s\" 2>/dev/null", cmd, s);
  gpsystem(cmd);
  pari_unlink(s);
  pari_free((char*)s);
}

/*************************************************************************/
/*                                                                       */
/*                           RGB COLORS                                  */
/*                                                                       */
/*************************************************************************/
/* generated from /etc/X11/rgb.txt by the following perl script
#!/usr/bin/perl
while(<>)
{
  ($hex, $name) = split(/\t\t/, $_);
  $hex =~ s/^ +//; chomp($name); $name =~ s, *,,g;
  $hex = sprintf("0x%02x%02x%02x", split(/\s+/, $hex));
  $name = lc($name); next if ($done{$name});
  $done{$name} = 1;
  print "COL(\"$name\", $hex),\n";
}
*/

#define COL(x,y) {(void*)x,(void*)y,0,NULL}
static hashentry col_list[] = {
COL("", 0x000000),
COL("snow", 0xfffafa),
COL("ghostwhite", 0xf8f8ff),
COL("whitesmoke", 0xf5f5f5),
COL("gainsboro", 0xdcdcdc),
COL("floralwhite", 0xfffaf0),
COL("oldlace", 0xfdf5e6),
COL("linen", 0xfaf0e6),
COL("antiquewhite", 0xfaebd7),
COL("papayawhip", 0xffefd5),
COL("blanchedalmond", 0xffebcd),
COL("bisque", 0xffe4c4),
COL("peachpuff", 0xffdab9),
COL("navajowhite", 0xffdead),
COL("moccasin", 0xffe4b5),
COL("cornsilk", 0xfff8dc),
COL("ivory", 0xfffff0),
COL("lemonchiffon", 0xfffacd),
COL("seashell", 0xfff5ee),
COL("honeydew", 0xf0fff0),
COL("mintcream", 0xf5fffa),
COL("azure", 0xf0ffff),
COL("aliceblue", 0xf0f8ff),
COL("lavender", 0xe6e6fa),
COL("lavenderblush", 0xfff0f5),
COL("mistyrose", 0xffe4e1),
COL("white", 0xffffff),
COL("black", 0x000000),
COL("darkslategray", 0x2f4f4f),
COL("darkslategrey", 0x2f4f4f),
COL("dimgray", 0x696969),
COL("dimgrey", 0x696969),
COL("slategray", 0x708090),
COL("slategrey", 0x708090),
COL("lightslategray", 0x778899),
COL("lightslategrey", 0x778899),
COL("gray", 0xbebebe),
COL("grey", 0xbebebe),
COL("lightgrey", 0xd3d3d3),
COL("lightgray", 0xd3d3d3),
COL("midnightblue", 0x191970),
COL("navy", 0x000080),
COL("navyblue", 0x000080),
COL("cornflowerblue", 0x6495ed),
COL("darkslateblue", 0x483d8b),
COL("slateblue", 0x6a5acd),
COL("mediumslateblue", 0x7b68ee),
COL("lightslateblue", 0x8470ff),
COL("mediumblue", 0x0000cd),
COL("royalblue", 0x4169e1),
COL("blue", 0x0000ff),
COL("dodgerblue", 0x1e90ff),
COL("deepskyblue", 0x00bfff),
COL("skyblue", 0x87ceeb),
COL("lightskyblue", 0x87cefa),
COL("steelblue", 0x4682b4),
COL("lightsteelblue", 0xb0c4de),
COL("lightblue", 0xadd8e6),
COL("powderblue", 0xb0e0e6),
COL("paleturquoise", 0xafeeee),
COL("darkturquoise", 0x00ced1),
COL("mediumturquoise", 0x48d1cc),
COL("turquoise", 0x40e0d0),
COL("cyan", 0x00ffff),
COL("lightcyan", 0xe0ffff),
COL("cadetblue", 0x5f9ea0),
COL("mediumaquamarine", 0x66cdaa),
COL("aquamarine", 0x7fffd4),
COL("darkgreen", 0x006400),
COL("darkolivegreen", 0x556b2f),
COL("darkseagreen", 0x8fbc8f),
COL("seagreen", 0x2e8b57),
COL("mediumseagreen", 0x3cb371),
COL("lightseagreen", 0x20b2aa),
COL("palegreen", 0x98fb98),
COL("springgreen", 0x00ff7f),
COL("lawngreen", 0x7cfc00),
COL("green", 0x00ff00),
COL("chartreuse", 0x7fff00),
COL("mediumspringgreen", 0x00fa9a),
COL("greenyellow", 0xadff2f),
COL("limegreen", 0x32cd32),
COL("yellowgreen", 0x9acd32),
COL("forestgreen", 0x228b22),
COL("olivedrab", 0x6b8e23),
COL("darkkhaki", 0xbdb76b),
COL("khaki", 0xf0e68c),
COL("palegoldenrod", 0xeee8aa),
COL("lightgoldenrodyellow", 0xfafad2),
COL("lightyellow", 0xffffe0),
COL("yellow", 0xffff00),
COL("gold", 0xffd700),
COL("lightgoldenrod", 0xeedd82),
COL("goldenrod", 0xdaa520),
COL("darkgoldenrod", 0xb8860b),
COL("rosybrown", 0xbc8f8f),
COL("indianred", 0xcd5c5c),
COL("saddlebrown", 0x8b4513),
COL("sienna", 0xa0522d),
COL("peru", 0xcd853f),
COL("burlywood", 0xdeb887),
COL("beige", 0xf5f5dc),
COL("wheat", 0xf5deb3),
COL("sandybrown", 0xf4a460),
COL("tan", 0xd2b48c),
COL("chocolate", 0xd2691e),
COL("firebrick", 0xb22222),
COL("brown", 0xa52a2a),
COL("darksalmon", 0xe9967a),
COL("salmon", 0xfa8072),
COL("lightsalmon", 0xffa07a),
COL("orange", 0xffa500),
COL("darkorange", 0xff8c00),
COL("coral", 0xff7f50),
COL("lightcoral", 0xf08080),
COL("tomato", 0xff6347),
COL("orangered", 0xff4500),
COL("red", 0xff0000),
COL("hotpink", 0xff69b4),
COL("deeppink", 0xff1493),
COL("pink", 0xffc0cb),
COL("lightpink", 0xffb6c1),
COL("palevioletred", 0xdb7093),
COL("maroon", 0xb03060),
COL("mediumvioletred", 0xc71585),
COL("violetred", 0xd02090),
COL("magenta", 0xff00ff),
COL("violet", 0xee82ee),
COL("plum", 0xdda0dd),
COL("orchid", 0xda70d6),
COL("mediumorchid", 0xba55d3),
COL("darkorchid", 0x9932cc),
COL("darkviolet", 0x9400d3),
COL("blueviolet", 0x8a2be2),
COL("purple", 0xa020f0),
COL("mediumpurple", 0x9370db),
COL("thistle", 0xd8bfd8),
COL("snow1", 0xfffafa),
COL("snow2", 0xeee9e9),
COL("snow3", 0xcdc9c9),
COL("snow4", 0x8b8989),
COL("seashell1", 0xfff5ee),
COL("seashell2", 0xeee5de),
COL("seashell3", 0xcdc5bf),
COL("seashell4", 0x8b8682),
COL("antiquewhite1", 0xffefdb),
COL("antiquewhite2", 0xeedfcc),
COL("antiquewhite3", 0xcdc0b0),
COL("antiquewhite4", 0x8b8378),
COL("bisque1", 0xffe4c4),
COL("bisque2", 0xeed5b7),
COL("bisque3", 0xcdb79e),
COL("bisque4", 0x8b7d6b),
COL("peachpuff1", 0xffdab9),
COL("peachpuff2", 0xeecbad),
COL("peachpuff3", 0xcdaf95),
COL("peachpuff4", 0x8b7765),
COL("navajowhite1", 0xffdead),
COL("navajowhite2", 0xeecfa1),
COL("navajowhite3", 0xcdb38b),
COL("navajowhite4", 0x8b795e),
COL("lemonchiffon1", 0xfffacd),
COL("lemonchiffon2", 0xeee9bf),
COL("lemonchiffon3", 0xcdc9a5),
COL("lemonchiffon4", 0x8b8970),
COL("cornsilk1", 0xfff8dc),
COL("cornsilk2", 0xeee8cd),
COL("cornsilk3", 0xcdc8b1),
COL("cornsilk4", 0x8b8878),
COL("ivory1", 0xfffff0),
COL("ivory2", 0xeeeee0),
COL("ivory3", 0xcdcdc1),
COL("ivory4", 0x8b8b83),
COL("honeydew1", 0xf0fff0),
COL("honeydew2", 0xe0eee0),
COL("honeydew3", 0xc1cdc1),
COL("honeydew4", 0x838b83),
COL("lavenderblush1", 0xfff0f5),
COL("lavenderblush2", 0xeee0e5),
COL("lavenderblush3", 0xcdc1c5),
COL("lavenderblush4", 0x8b8386),
COL("mistyrose1", 0xffe4e1),
COL("mistyrose2", 0xeed5d2),
COL("mistyrose3", 0xcdb7b5),
COL("mistyrose4", 0x8b7d7b),
COL("azure1", 0xf0ffff),
COL("azure2", 0xe0eeee),
COL("azure3", 0xc1cdcd),
COL("azure4", 0x838b8b),
COL("slateblue1", 0x836fff),
COL("slateblue2", 0x7a67ee),
COL("slateblue3", 0x6959cd),
COL("slateblue4", 0x473c8b),
COL("royalblue1", 0x4876ff),
COL("royalblue2", 0x436eee),
COL("royalblue3", 0x3a5fcd),
COL("royalblue4", 0x27408b),
COL("blue1", 0x0000ff),
COL("blue2", 0x0000ee),
COL("blue3", 0x0000cd),
COL("blue4", 0x00008b),
COL("dodgerblue1", 0x1e90ff),
COL("dodgerblue2", 0x1c86ee),
COL("dodgerblue3", 0x1874cd),
COL("dodgerblue4", 0x104e8b),
COL("steelblue1", 0x63b8ff),
COL("steelblue2", 0x5cacee),
COL("steelblue3", 0x4f94cd),
COL("steelblue4", 0x36648b),
COL("deepskyblue1", 0x00bfff),
COL("deepskyblue2", 0x00b2ee),
COL("deepskyblue3", 0x009acd),
COL("deepskyblue4", 0x00688b),
COL("skyblue1", 0x87ceff),
COL("skyblue2", 0x7ec0ee),
COL("skyblue3", 0x6ca6cd),
COL("skyblue4", 0x4a708b),
COL("lightskyblue1", 0xb0e2ff),
COL("lightskyblue2", 0xa4d3ee),
COL("lightskyblue3", 0x8db6cd),
COL("lightskyblue4", 0x607b8b),
COL("slategray1", 0xc6e2ff),
COL("slategray2", 0xb9d3ee),
COL("slategray3", 0x9fb6cd),
COL("slategray4", 0x6c7b8b),
COL("lightsteelblue1", 0xcae1ff),
COL("lightsteelblue2", 0xbcd2ee),
COL("lightsteelblue3", 0xa2b5cd),
COL("lightsteelblue4", 0x6e7b8b),
COL("lightblue1", 0xbfefff),
COL("lightblue2", 0xb2dfee),
COL("lightblue3", 0x9ac0cd),
COL("lightblue4", 0x68838b),
COL("lightcyan1", 0xe0ffff),
COL("lightcyan2", 0xd1eeee),
COL("lightcyan3", 0xb4cdcd),
COL("lightcyan4", 0x7a8b8b),
COL("paleturquoise1", 0xbbffff),
COL("paleturquoise2", 0xaeeeee),
COL("paleturquoise3", 0x96cdcd),
COL("paleturquoise4", 0x668b8b),
COL("cadetblue1", 0x98f5ff),
COL("cadetblue2", 0x8ee5ee),
COL("cadetblue3", 0x7ac5cd),
COL("cadetblue4", 0x53868b),
COL("turquoise1", 0x00f5ff),
COL("turquoise2", 0x00e5ee),
COL("turquoise3", 0x00c5cd),
COL("turquoise4", 0x00868b),
COL("cyan1", 0x00ffff),
COL("cyan2", 0x00eeee),
COL("cyan3", 0x00cdcd),
COL("cyan4", 0x008b8b),
COL("darkslategray1", 0x97ffff),
COL("darkslategray2", 0x8deeee),
COL("darkslategray3", 0x79cdcd),
COL("darkslategray4", 0x528b8b),
COL("aquamarine1", 0x7fffd4),
COL("aquamarine2", 0x76eec6),
COL("aquamarine3", 0x66cdaa),
COL("aquamarine4", 0x458b74),
COL("darkseagreen1", 0xc1ffc1),
COL("darkseagreen2", 0xb4eeb4),
COL("darkseagreen3", 0x9bcd9b),
COL("darkseagreen4", 0x698b69),
COL("seagreen1", 0x54ff9f),
COL("seagreen2", 0x4eee94),
COL("seagreen3", 0x43cd80),
COL("seagreen4", 0x2e8b57),
COL("palegreen1", 0x9aff9a),
COL("palegreen2", 0x90ee90),
COL("palegreen3", 0x7ccd7c),
COL("palegreen4", 0x548b54),
COL("springgreen1", 0x00ff7f),
COL("springgreen2", 0x00ee76),
COL("springgreen3", 0x00cd66),
COL("springgreen4", 0x008b45),
COL("green1", 0x00ff00),
COL("green2", 0x00ee00),
COL("green3", 0x00cd00),
COL("green4", 0x008b00),
COL("chartreuse1", 0x7fff00),
COL("chartreuse2", 0x76ee00),
COL("chartreuse3", 0x66cd00),
COL("chartreuse4", 0x458b00),
COL("olivedrab1", 0xc0ff3e),
COL("olivedrab2", 0xb3ee3a),
COL("olivedrab3", 0x9acd32),
COL("olivedrab4", 0x698b22),
COL("darkolivegreen1", 0xcaff70),
COL("darkolivegreen2", 0xbcee68),
COL("darkolivegreen3", 0xa2cd5a),
COL("darkolivegreen4", 0x6e8b3d),
COL("khaki1", 0xfff68f),
COL("khaki2", 0xeee685),
COL("khaki3", 0xcdc673),
COL("khaki4", 0x8b864e),
COL("lightgoldenrod1", 0xffec8b),
COL("lightgoldenrod2", 0xeedc82),
COL("lightgoldenrod3", 0xcdbe70),
COL("lightgoldenrod4", 0x8b814c),
COL("lightyellow1", 0xffffe0),
COL("lightyellow2", 0xeeeed1),
COL("lightyellow3", 0xcdcdb4),
COL("lightyellow4", 0x8b8b7a),
COL("yellow1", 0xffff00),
COL("yellow2", 0xeeee00),
COL("yellow3", 0xcdcd00),
COL("yellow4", 0x8b8b00),
COL("gold1", 0xffd700),
COL("gold2", 0xeec900),
COL("gold3", 0xcdad00),
COL("gold4", 0x8b7500),
COL("goldenrod1", 0xffc125),
COL("goldenrod2", 0xeeb422),
COL("goldenrod3", 0xcd9b1d),
COL("goldenrod4", 0x8b6914),
COL("darkgoldenrod1", 0xffb90f),
COL("darkgoldenrod2", 0xeead0e),
COL("darkgoldenrod3", 0xcd950c),
COL("darkgoldenrod4", 0x8b6508),
COL("rosybrown1", 0xffc1c1),
COL("rosybrown2", 0xeeb4b4),
COL("rosybrown3", 0xcd9b9b),
COL("rosybrown4", 0x8b6969),
COL("indianred1", 0xff6a6a),
COL("indianred2", 0xee6363),
COL("indianred3", 0xcd5555),
COL("indianred4", 0x8b3a3a),
COL("sienna1", 0xff8247),
COL("sienna2", 0xee7942),
COL("sienna3", 0xcd6839),
COL("sienna4", 0x8b4726),
COL("burlywood1", 0xffd39b),
COL("burlywood2", 0xeec591),
COL("burlywood3", 0xcdaa7d),
COL("burlywood4", 0x8b7355),
COL("wheat1", 0xffe7ba),
COL("wheat2", 0xeed8ae),
COL("wheat3", 0xcdba96),
COL("wheat4", 0x8b7e66),
COL("tan1", 0xffa54f),
COL("tan2", 0xee9a49),
COL("tan3", 0xcd853f),
COL("tan4", 0x8b5a2b),
COL("chocolate1", 0xff7f24),
COL("chocolate2", 0xee7621),
COL("chocolate3", 0xcd661d),
COL("chocolate4", 0x8b4513),
COL("firebrick1", 0xff3030),
COL("firebrick2", 0xee2c2c),
COL("firebrick3", 0xcd2626),
COL("firebrick4", 0x8b1a1a),
COL("brown1", 0xff4040),
COL("brown2", 0xee3b3b),
COL("brown3", 0xcd3333),
COL("brown4", 0x8b2323),
COL("salmon1", 0xff8c69),
COL("salmon2", 0xee8262),
COL("salmon3", 0xcd7054),
COL("salmon4", 0x8b4c39),
COL("lightsalmon1", 0xffa07a),
COL("lightsalmon2", 0xee9572),
COL("lightsalmon3", 0xcd8162),
COL("lightsalmon4", 0x8b5742),
COL("orange1", 0xffa500),
COL("orange2", 0xee9a00),
COL("orange3", 0xcd8500),
COL("orange4", 0x8b5a00),
COL("darkorange1", 0xff7f00),
COL("darkorange2", 0xee7600),
COL("darkorange3", 0xcd6600),
COL("darkorange4", 0x8b4500),
COL("coral1", 0xff7256),
COL("coral2", 0xee6a50),
COL("coral3", 0xcd5b45),
COL("coral4", 0x8b3e2f),
COL("tomato1", 0xff6347),
COL("tomato2", 0xee5c42),
COL("tomato3", 0xcd4f39),
COL("tomato4", 0x8b3626),
COL("orangered1", 0xff4500),
COL("orangered2", 0xee4000),
COL("orangered3", 0xcd3700),
COL("orangered4", 0x8b2500),
COL("red1", 0xff0000),
COL("red2", 0xee0000),
COL("red3", 0xcd0000),
COL("red4", 0x8b0000),
COL("debianred", 0xd70751),
COL("deeppink1", 0xff1493),
COL("deeppink2", 0xee1289),
COL("deeppink3", 0xcd1076),
COL("deeppink4", 0x8b0a50),
COL("hotpink1", 0xff6eb4),
COL("hotpink2", 0xee6aa7),
COL("hotpink3", 0xcd6090),
COL("hotpink4", 0x8b3a62),
COL("pink1", 0xffb5c5),
COL("pink2", 0xeea9b8),
COL("pink3", 0xcd919e),
COL("pink4", 0x8b636c),
COL("lightpink1", 0xffaeb9),
COL("lightpink2", 0xeea2ad),
COL("lightpink3", 0xcd8c95),
COL("lightpink4", 0x8b5f65),
COL("palevioletred1", 0xff82ab),
COL("palevioletred2", 0xee799f),
COL("palevioletred3", 0xcd6889),
COL("palevioletred4", 0x8b475d),
COL("maroon1", 0xff34b3),
COL("maroon2", 0xee30a7),
COL("maroon3", 0xcd2990),
COL("maroon4", 0x8b1c62),
COL("violetred1", 0xff3e96),
COL("violetred2", 0xee3a8c),
COL("violetred3", 0xcd3278),
COL("violetred4", 0x8b2252),
COL("magenta1", 0xff00ff),
COL("magenta2", 0xee00ee),
COL("magenta3", 0xcd00cd),
COL("magenta4", 0x8b008b),
COL("orchid1", 0xff83fa),
COL("orchid2", 0xee7ae9),
COL("orchid3", 0xcd69c9),
COL("orchid4", 0x8b4789),
COL("plum1", 0xffbbff),
COL("plum2", 0xeeaeee),
COL("plum3", 0xcd96cd),
COL("plum4", 0x8b668b),
COL("mediumorchid1", 0xe066ff),
COL("mediumorchid2", 0xd15fee),
COL("mediumorchid3", 0xb452cd),
COL("mediumorchid4", 0x7a378b),
COL("darkorchid1", 0xbf3eff),
COL("darkorchid2", 0xb23aee),
COL("darkorchid3", 0x9a32cd),
COL("darkorchid4", 0x68228b),
COL("purple1", 0x9b30ff),
COL("purple2", 0x912cee),
COL("purple3", 0x7d26cd),
COL("purple4", 0x551a8b),
COL("mediumpurple1", 0xab82ff),
COL("mediumpurple2", 0x9f79ee),
COL("mediumpurple3", 0x8968cd),
COL("mediumpurple4", 0x5d478b),
COL("thistle1", 0xffe1ff),
COL("thistle2", 0xeed2ee),
COL("thistle3", 0xcdb5cd),
COL("thistle4", 0x8b7b8b),
COL("gray0", 0x000000),
COL("grey0", 0x000000),
COL("gray1", 0x030303),
COL("grey1", 0x030303),
COL("gray2", 0x050505),
COL("grey2", 0x050505),
COL("gray3", 0x080808),
COL("grey3", 0x080808),
COL("gray4", 0x0a0a0a),
COL("grey4", 0x0a0a0a),
COL("gray5", 0x0d0d0d),
COL("grey5", 0x0d0d0d),
COL("gray6", 0x0f0f0f),
COL("grey6", 0x0f0f0f),
COL("gray7", 0x121212),
COL("grey7", 0x121212),
COL("gray8", 0x141414),
COL("grey8", 0x141414),
COL("gray9", 0x171717),
COL("grey9", 0x171717),
COL("gray10", 0x1a1a1a),
COL("grey10", 0x1a1a1a),
COL("gray11", 0x1c1c1c),
COL("grey11", 0x1c1c1c),
COL("gray12", 0x1f1f1f),
COL("grey12", 0x1f1f1f),
COL("gray13", 0x212121),
COL("grey13", 0x212121),
COL("gray14", 0x242424),
COL("grey14", 0x242424),
COL("gray15", 0x262626),
COL("grey15", 0x262626),
COL("gray16", 0x292929),
COL("grey16", 0x292929),
COL("gray17", 0x2b2b2b),
COL("grey17", 0x2b2b2b),
COL("gray18", 0x2e2e2e),
COL("grey18", 0x2e2e2e),
COL("gray19", 0x303030),
COL("grey19", 0x303030),
COL("gray20", 0x333333),
COL("grey20", 0x333333),
COL("gray21", 0x363636),
COL("grey21", 0x363636),
COL("gray22", 0x383838),
COL("grey22", 0x383838),
COL("gray23", 0x3b3b3b),
COL("grey23", 0x3b3b3b),
COL("gray24", 0x3d3d3d),
COL("grey24", 0x3d3d3d),
COL("gray25", 0x404040),
COL("grey25", 0x404040),
COL("gray26", 0x424242),
COL("grey26", 0x424242),
COL("gray27", 0x454545),
COL("grey27", 0x454545),
COL("gray28", 0x474747),
COL("grey28", 0x474747),
COL("gray29", 0x4a4a4a),
COL("grey29", 0x4a4a4a),
COL("gray30", 0x4d4d4d),
COL("grey30", 0x4d4d4d),
COL("gray31", 0x4f4f4f),
COL("grey31", 0x4f4f4f),
COL("gray32", 0x525252),
COL("grey32", 0x525252),
COL("gray33", 0x545454),
COL("grey33", 0x545454),
COL("gray34", 0x575757),
COL("grey34", 0x575757),
COL("gray35", 0x595959),
COL("grey35", 0x595959),
COL("gray36", 0x5c5c5c),
COL("grey36", 0x5c5c5c),
COL("gray37", 0x5e5e5e),
COL("grey37", 0x5e5e5e),
COL("gray38", 0x616161),
COL("grey38", 0x616161),
COL("gray39", 0x636363),
COL("grey39", 0x636363),
COL("gray40", 0x666666),
COL("grey40", 0x666666),
COL("gray41", 0x696969),
COL("grey41", 0x696969),
COL("gray42", 0x6b6b6b),
COL("grey42", 0x6b6b6b),
COL("gray43", 0x6e6e6e),
COL("grey43", 0x6e6e6e),
COL("gray44", 0x707070),
COL("grey44", 0x707070),
COL("gray45", 0x737373),
COL("grey45", 0x737373),
COL("gray46", 0x757575),
COL("grey46", 0x757575),
COL("gray47", 0x787878),
COL("grey47", 0x787878),
COL("gray48", 0x7a7a7a),
COL("grey48", 0x7a7a7a),
COL("gray49", 0x7d7d7d),
COL("grey49", 0x7d7d7d),
COL("gray50", 0x7f7f7f),
COL("grey50", 0x7f7f7f),
COL("gray51", 0x828282),
COL("grey51", 0x828282),
COL("gray52", 0x858585),
COL("grey52", 0x858585),
COL("gray53", 0x878787),
COL("grey53", 0x878787),
COL("gray54", 0x8a8a8a),
COL("grey54", 0x8a8a8a),
COL("gray55", 0x8c8c8c),
COL("grey55", 0x8c8c8c),
COL("gray56", 0x8f8f8f),
COL("grey56", 0x8f8f8f),
COL("gray57", 0x919191),
COL("grey57", 0x919191),
COL("gray58", 0x949494),
COL("grey58", 0x949494),
COL("gray59", 0x969696),
COL("grey59", 0x969696),
COL("gray60", 0x999999),
COL("grey60", 0x999999),
COL("gray61", 0x9c9c9c),
COL("grey61", 0x9c9c9c),
COL("gray62", 0x9e9e9e),
COL("grey62", 0x9e9e9e),
COL("gray63", 0xa1a1a1),
COL("grey63", 0xa1a1a1),
COL("gray64", 0xa3a3a3),
COL("grey64", 0xa3a3a3),
COL("gray65", 0xa6a6a6),
COL("grey65", 0xa6a6a6),
COL("gray66", 0xa8a8a8),
COL("grey66", 0xa8a8a8),
COL("gray67", 0xababab),
COL("grey67", 0xababab),
COL("gray68", 0xadadad),
COL("grey68", 0xadadad),
COL("gray69", 0xb0b0b0),
COL("grey69", 0xb0b0b0),
COL("gray70", 0xb3b3b3),
COL("grey70", 0xb3b3b3),
COL("gray71", 0xb5b5b5),
COL("grey71", 0xb5b5b5),
COL("gray72", 0xb8b8b8),
COL("grey72", 0xb8b8b8),
COL("gray73", 0xbababa),
COL("grey73", 0xbababa),
COL("gray74", 0xbdbdbd),
COL("grey74", 0xbdbdbd),
COL("gray75", 0xbfbfbf),
COL("grey75", 0xbfbfbf),
COL("gray76", 0xc2c2c2),
COL("grey76", 0xc2c2c2),
COL("gray77", 0xc4c4c4),
COL("grey77", 0xc4c4c4),
COL("gray78", 0xc7c7c7),
COL("grey78", 0xc7c7c7),
COL("gray79", 0xc9c9c9),
COL("grey79", 0xc9c9c9),
COL("gray80", 0xcccccc),
COL("grey80", 0xcccccc),
COL("gray81", 0xcfcfcf),
COL("grey81", 0xcfcfcf),
COL("gray82", 0xd1d1d1),
COL("grey82", 0xd1d1d1),
COL("gray83", 0xd4d4d4),
COL("grey83", 0xd4d4d4),
COL("gray84", 0xd6d6d6),
COL("grey84", 0xd6d6d6),
COL("gray85", 0xd9d9d9),
COL("grey85", 0xd9d9d9),
COL("gray86", 0xdbdbdb),
COL("grey86", 0xdbdbdb),
COL("gray87", 0xdedede),
COL("grey87", 0xdedede),
COL("gray88", 0xe0e0e0),
COL("grey88", 0xe0e0e0),
COL("gray89", 0xe3e3e3),
COL("grey89", 0xe3e3e3),
COL("gray90", 0xe5e5e5),
COL("grey90", 0xe5e5e5),
COL("gray91", 0xe8e8e8),
COL("grey91", 0xe8e8e8),
COL("gray92", 0xebebeb),
COL("grey92", 0xebebeb),
COL("gray93", 0xededed),
COL("grey93", 0xededed),
COL("gray94", 0xf0f0f0),
COL("grey94", 0xf0f0f0),
COL("gray95", 0xf2f2f2),
COL("grey95", 0xf2f2f2),
COL("gray96", 0xf5f5f5),
COL("grey96", 0xf5f5f5),
COL("gray97", 0xf7f7f7),
COL("grey97", 0xf7f7f7),
COL("gray98", 0xfafafa),
COL("grey98", 0xfafafa),
COL("gray99", 0xfcfcfc),
COL("grey99", 0xfcfcfc),
COL("gray100", 0xffffff),
COL("grey100", 0xffffff),
COL("darkgrey", 0xa9a9a9),
COL("darkgray", 0xa9a9a9),
COL("darkblue", 0x00008b),
COL("darkcyan", 0x008b8b),
COL("darkmagenta", 0x8b008b),
COL("darkred", 0x8b0000),
COL("lightgreen", 0x90ee90),
COL(NULL,0) /* sentinel */
};
#undef COL

void
long_to_rgb(long c, int *r, int *g, int *b)
{
  *b = c & 0xff; c >>= 8;
  *g = c & 0xff; c >>= 8;
  *r = c;
}
static int
hex2(const char *s)
{
  int m = 0, c = 0, i;
  for (i = 0; i < 2; i++, s++)
  {
    if (*s >= '0' && *s <= '9')
      c = *s - '0';
    else if (*s >= 'A' && *s <= 'F')
      c = *s - 'A' + 10;
    else if (*s >= 'a' && *s <= 'f')
      c = *s - 'a' + 10;
    else pari_err(e_MISC,"incorrect hexadecimal number: %s", s);
    m = 16*m + c;
  }
  return m;
}
void
colorname_to_rgb(const char *s, int *r, int *g, int *b)
{
  if (!rgb_colors) rgb_colors = hashstr_import_static(col_list, 1000);
  if (*s == '#' && strlen(s) == 7)
  {
    *r = hex2(s+1);
    *g = hex2(s+3);
    *b = hex2(s+5);
  }
  else
  {
    hashentry *ep = hash_search(rgb_colors, (void*)s);
    if (!ep) pari_err(e_MISC, "unknown color %s", s);
    long_to_rgb((long)ep->val, r,g,b);
  }
}

static void
chk_8bit(int v, GEN c)
{ if (v & ~0xff) pari_err(e_MISC, "invalid RGB code: %Ps", c); }
void
color_to_rgb(GEN c, int *r, int *g, int *b)
{
  switch(typ(c))
  {
    case t_STR:
      colorname_to_rgb(GSTR(c), r,g,b);
      break;
    default: /* t_VECSMALL: */
      *r = c[1]; chk_8bit(*r, c);
      *g = c[2]; chk_8bit(*g, c);
      *b = c[3]; chk_8bit(*b, c);
      break;
  }
}
