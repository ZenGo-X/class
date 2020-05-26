/* Copyright (C) 2009  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

/* Written by Vasili Burdo */

#include "../systems/mingw/pwinver.h"
#include <windows.h>
#include <time.h>
#include "pari.h"
#include "rect.h"

static void SetForeground(void *data, long col)
{
  HPEN hOldPen;
  int r, g, b; long_to_rgb(col, &r, &g, &b);
  SetDCPenColor((HDC)data,RGB(r,g,b));
  hOldPen = SelectObject((HDC)data, CreatePen(PS_SOLID, 1, RGB(r,g,b)));
  if( hOldPen ) DeleteObject(hOldPen);
}

static void DrawPoint(void *data, long x, long y)
{
  Ellipse((HDC)data,x-1,y-1,x+1,y+1);
}

static void DrawLine(void *data, long x1, long y1, long x2, long y2)
{
  MoveToEx((HDC)data, x1, y1, NULL);
  LineTo((HDC)data,x2,y2);
}

static void DrawRectangle(void *data, long x, long y, long w, long h)
{
  DrawLine(data, x,y,x+w,y);
  DrawLine(data, x,y,x,y+h);
  DrawLine(data, x+w,y,x+w,y+h);
  DrawLine(data, x,y+h,x+w,y+h);
}

static void FillRectangle(void *data, long x, long y, long w, long h)
{
  RECT rc;
  COLORREF color;
  HBRUSH brush;
  rc.left = x; rc.right  = x+w;
  rc.top  = y; rc.bottom = y+h;
  color = GetDCPenColor((HDC) data);
  brush = CreateSolidBrush(color);
  FillRect((HDC)data, &rc, brush);
  DeleteObject(brush);
}

static void DrawPoints(void *data, long nb, struct plot_points *p)
{
  long i;
  for (i=0; i<nb; ++i)
    DrawPoint(data,p[i].x,p[i].y);
}

static void DrawLines(void *data, long nb, struct plot_points *p)
{
  long i;
  MoveToEx((HDC)data, p[0].x, p[0].y, NULL);
  for(i=1; i<nb; ++i)
    LineTo((HDC)data,p[i].x,p[i].y);
}

static void DrawString(void *data, long x, long y, char *text, long numtext)
{
  TextOut((HDC)data, x, y, text, numtext);
}

static void
draw(PARI_plot *T, GEN w, GEN x, GEN y)
{
  char tmppath[MAX_PATH], fname[MAX_PATH];
  struct plot_eng plotWin32;
  HDC hEmf;
  int r, g, b;

  GetTempPath(sizeof(tmppath), tmppath);
  sprintf(fname, "%s\\gp-ploth-%lx.emf", tmppath, time(NULL)/(24*60*60)*1000+GetTickCount());

  hEmf = CreateEnhMetaFile(GetDC(NULL), fname, NULL, NULL);
  SetMapMode(hEmf, MM_TEXT);
  SelectObject(hEmf, GetStockObject(DEFAULT_GUI_FONT));
  color_to_rgb(gel(GP_DATA->colormap,1), &r,&g,&b);
  SetBkColor(hEmf, RGB(r,g,b));
  SetBkMode(hEmf, OPAQUE);

  plotWin32.sc=&SetForeground;
  plotWin32.pt=&DrawPoint;
  plotWin32.ln=&DrawLine;
  plotWin32.bx=&DrawRectangle;
  plotWin32.fb=&FillRectangle;
  plotWin32.mp=&DrawPoints;
  plotWin32.ml=&DrawLines;
  plotWin32.st=&DrawString;
  plotWin32.pl=T;
  plotWin32.data=(void*)hEmf;

  gen_draw(&plotWin32, w, x, y, 1, 1);
  DeleteEnhMetaFile(CloseEnhMetaFile(hEmf));

  ShellExecute(NULL,NULL,fname,NULL,NULL,SW_SHOWDEFAULT);
}

INLINE void
gp_get_display_sizes(long *dwidth, long *dheight, long *fwidth, long *fheight)
{
  HDC hdc;
  TEXTMETRIC tm;

  *dwidth  = GetSystemMetrics(SM_CXSCREEN);
  *dheight = GetSystemMetrics(SM_CYSCREEN);

  hdc = GetDC(0);
  SelectObject(hdc, GetStockObject(DEFAULT_GUI_FONT));
  GetTextMetrics(hdc, &tm);
  ReleaseDC(0,hdc);

  *fwidth  = tm.tmAveCharWidth;
  *fheight = tm.tmHeight;
}

void
gp_get_plot(PARI_plot *T)
{
  gp_get_plot_generic(T,gp_get_display_sizes);
  T->draw = &draw;
}
