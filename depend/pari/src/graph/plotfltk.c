/* Copyright (C) 2000  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */
/////////////////////////////////////////////////////////////////////////////
//
//  High resolution plot using FLTK library
//  Bill Allombert 2003
//
//  Based on plotQt by Nils-Peter Skoruppa (www.countnumber.de)
/////////////////////////////////////////////////////////////////////////////
extern "C" {
#include "pari.h"
#include "rect.h"
}

#include <FL/Fl.H>
#include <FL/Fl_Window.H>
#include <FL/fl_draw.H>

class Plotter: public Fl_Window {

public:
  Plotter(PARI_plot *T, GEN w, GEN x, GEN y);

private:
  void draw();
  int handle(int event);

private:
  PARI_plot *T;
  GEN my_w, my_x, my_y;
};

static Fl_Color
rgb_color(long c)
{
  int r, g, b; long_to_rgb(c, &r, &g, &b);
  return fl_color_cube(r*FL_NUM_RED/256, g*FL_NUM_GREEN/256, b*FL_NUM_BLUE/256);
}
Plotter::Plotter(PARI_plot *T, GEN w, GEN x, GEN y)
        : Fl_Window(T->width, T->height, "PARI/GP")
{
  this->T = T;
  this->my_w = w;
  this->my_x = x;
  this->my_y = y;
}

static void
DrawPoint(void *data, long x, long y)
{ (void)data; fl_point(x,y); }

static void
DrawLine(void *data, long x1, long y1, long x2, long y2)
{ (void)data; fl_line(x1,y1, x2,y2); }

static void
DrawRectangle(void *data, long x, long y, long w, long h)
{ (void)data; fl_rect(x,y,w,h); }
static void
FillRectangle(void *data, long x, long y, long w, long h)
{ (void)data; fl_rectf(x,y,w,h); }
static void
DrawPoints(void *data, long nb, struct plot_points *p)
{
  long i; (void)data;
  for (i=0; i<nb; i++) fl_point(p[i].x, p[i].y);
}
static void
SetForeground(void *data, long col)
{
  (void)data; fl_color(rgb_color(col));
}
static void
DrawLines(void *data, long nb, struct plot_points *p)
{
  long i;
  (void)data;
  for (i=1; i<nb; i++) fl_line(p[i-1].x, p[i-1].y, p[i].x, p[i].y);
}
static void
DrawString(void *data, long x, long y, char *text, long numtext)
{ (void)data; fl_draw(text,numtext,x,y); }

void
Plotter::draw()
{
  struct plot_eng pl;
  double xs = double(this->w()) / T->width;
  double ys = double(this->h()) / T->height;

  fl_font(FL_COURIER, int(T->fheight * xs));
  fl_color(rgb_color(0xffffff)); // transparent window on Windows otherwise
  fl_rectf(0, 0, this->w(), this->h());
  pl.sc = &SetForeground;
  pl.pt = &DrawPoint;
  pl.ln = &DrawLine;
  pl.bx = &DrawRectangle;
  pl.fb = &FillRectangle;
  pl.mp = &DrawPoints;
  pl.ml = &DrawLines;
  pl.st = &DrawString;
  pl.pl = T;
  pl.data = NULL;
  gen_draw(&pl, my_w, my_x, my_y, xs, ys);
}

int Plotter::handle(int event)
{
  switch(event)
  {
  case FL_PUSH:
    switch(Fl::event_button())
    {
    case 1:
     exit(0);
    case 2:
     {
       static int flag = 0, my_x, my_y, my_w, my_h;
       flag = 1-flag;
       if (flag)
       {
         my_x = this->x();
         my_y = this->y();
         my_w = this->w();
         my_h = this->h();
         this->fullscreen();
       }
       else
       {
         this->fullscreen_off(my_x, my_y, my_w, my_h);
         this->size_range(1,1);
       }
       return 1;
     }
    }
  case FL_KEYUP:
    switch(Fl::event_key())
    {
    case 'q':
      switch(Fl::event_shift())
      {
        case 0:
        case FL_CTRL: exit(0);
      }
      break;
    case 'c':
      if (Fl::event_state() == FL_CTRL) exit(0);
      break;
    }
  default:
    return 0;
  }
}

static void
draw(PARI_plot *T, GEN w, GEN x, GEN y)
{
  Plotter *win;

  if (pari_daemon()) return;  // parent process returns
  pari_close();

  Fl::visual(FL_DOUBLE|FL_INDEX);
  win = new Plotter(T, w, x, y);
  win->size_range(1,1);
  win->box(FL_FLAT_BOX);
  win->end();
  win->show();
  Fl::run();
  exit(0);
}

INLINE void
gp_get_display_sizes(long *dwidth, long *dheight, long *fwidth, long *fheight)
{
  *dwidth  = 800;
  *dheight = 600;
  *fwidth  = 6;
  *fheight = 9;
}

void
gp_get_plot(PARI_plot *T)
{
  gp_get_plot_generic(T,gp_get_display_sizes);
  T->draw = &draw;
}
