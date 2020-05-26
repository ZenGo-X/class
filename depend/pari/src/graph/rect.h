/* Copyright (C) 2000  The PARI group.

This file is part of the PARI/GP package.

PARI/GP is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation. It is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY WHATSOEVER.

Check the License for details. You should have received a copy of it, along
with the package; see the file 'COPYING'. If not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA. */

BEGINEXTERN
typedef struct dblPointList{
  double *d;                   /* data */
  long nb;                     /* number of elements */
  double xsml,xbig,ysml,ybig;  /* extrema */
} dblPointList;

typedef struct RectObj {
  struct RectObj *next;
  long code,color;
} RectObj;

typedef struct PariRect {
  RectObj *head,*tail;
  long sizex,sizey;
  double cursorx,cursory;
  double xscale,yscale;
  double xshift,yshift;
} PariRect;

/* The structures below are "subclasses" of RectObj. */

typedef struct RectObj1P {
  struct RectObj *next;
  long code,color;
  double x,y;
} RectObj1P;

typedef struct RectObj2P {
  struct RectObj *next;
  long code,color;
  double x1,y1;
  double x2,y2;
} RectObj2P;

typedef struct RectObjMP {
  struct RectObj *next;
  long code,color;
  long count;
  double *xs,*ys;
} RectObjMP;

typedef struct RectObjST {
  struct RectObj *next;
  long code,color;
  long length;
  char *s;
  double x,y;
  long dir;
} RectObjST;

typedef struct RectObjPN {
  struct RectObj *next;
  long code,color;
  long pen;
} RectObjPN;

typedef struct RectObjPS {
  struct RectObj *next;
  long code,color;
  double size;
} RectObjPS;

struct plot_points { long x, y; };
struct plot_eng {
  PARI_plot *pl;
  void *data;
  void (*sc)(void *data, long col);
  void (*pt)(void *data, long x, long y);
  void (*ln)(void *data, long x1, long y1, long x2, long y2);
  void (*bx)(void *data, long x, long y, long w, long h);
  void (*fb)(void *data, long x, long y, long w, long h);
  void (*mp)(void *data, long n, struct plot_points *points);
  void (*ml)(void *data, long n, struct plot_points *points);
  void (*st)(void *data, long x, long y, char *s, long l);
};

/* Pointer conversion. */
#define RoMV(rop) ((RectObj1P*)rop)
#define RoPT(rop) ((RectObj1P*)rop)
#define RoLN(rop) ((RectObj2P*)rop)
#define RoBX(rop) ((RectObj2P*)rop)
#define RoMP(rop) ((RectObjMP*)rop)
#define RoML(rop) ((RectObjMP*)rop)
#define RoST(rop) ((RectObjST*)rop)
#define RoPTT(rop) ((RectObjPN*)rop)
#define RoPTS(rop) ((RectObjPS*)rop)
#define RoLNT(rop) ((RectObjPN*)rop)

/* All the access to the rectangle data go via these macros! */
#define RHead(rp) ((rp)->head)
#define RTail(rp) ((rp)->tail)
#define RXsize(rp) ((rp)->sizex)
#define RYsize(rp) ((rp)->sizey)
#define RXcursor(rp) ((rp)->cursorx)
#define RYcursor(rp) ((rp)->cursory)
#define RXshift(rp) ((rp)->xshift)
#define RYshift(rp) ((rp)->yshift)
#define RXscale(rp) ((rp)->xscale)
#define RYscale(rp) ((rp)->yscale)

#define RoNext(rop) ((rop)->next)
#define RoType(rop) ((rop)->code)
#define RoCol(rop) ((rop)->color)
#define RoMVx(rop) (RoMV(rop)->x)
#define RoMVy(rop) (RoMV(rop)->y)
#define RoPTx(rop) (RoPT(rop)->x)
#define RoPTy(rop) (RoPT(rop)->y)
#define RoLNx1(rop) (RoLN(rop)->x1)
#define RoLNy1(rop) (RoLN(rop)->y1)
#define RoLNx2(rop) (RoLN(rop)->x2)
#define RoLNy2(rop) (RoLN(rop)->y2)
#define RoBXx1(rop) (RoBX(rop)->x1)
#define RoBXy1(rop) (RoBX(rop)->y1)
#define RoBXx2(rop) (RoBX(rop)->x2)
#define RoBXy2(rop) (RoBX(rop)->y2)

#define RoMPcnt(rop) (RoMP(rop)->count)
#define RoMPxs(rop) (RoMP(rop)->xs)
#define RoMPys(rop) (RoMP(rop)->ys)

#define RoMLcnt(rop) (RoML(rop)->count)
#define RoMLxs(rop) (RoML(rop)->xs)
#define RoMLys(rop) (RoML(rop)->ys)

#define RoSTs(rop) (RoST(rop)->s)
#define RoSTl(rop) (RoST(rop)->length)
#define RoSTx(rop) (RoST(rop)->x)
#define RoSTy(rop) (RoST(rop)->y)
#define RoSTdir(rop) (RoST(rop)->dir)

#define RoPTTpen(rop) (RoPTT(rop)->pen)
#define RoLNTpen(rop) (RoLNT(rop)->pen)
#define RoPTSsize(rop) (RoPTS(rop)->size)

void gen_draw(struct plot_eng *eng, GEN w, GEN x, GEN y, double xs, double ys);
void gp_get_plot(PARI_plot *T);

#define gp_get_ploth_default_sizes(S)                                  \
{ PARI_plot *_T = (PARI_plot *)S;                                      \
  GEN D = GP_DATA->plothsizes;                                         \
  if (D) switch(lg(D)) {                                               \
    case 5: if (D[4]) _T->vunit  = D[4];                               \
    case 4: if (D[3]) _T->hunit  = D[3];                               \
    case 3: if (D[2]) _T->height = D[2];                               \
    case 2: if (D[1]) _T->width  = D[1];                               \
  }                                                                    \
}

#define gp_get_plot_generic(S,gp_get_display_sizes)                          \
{ PARI_plot *_T = (PARI_plot *)S;                                            \
  gp_get_display_sizes(&_T->dwidth, &_T->dheight, &_T->fwidth, &_T->fheight);\
  _T->width = _T->dwidth? _T->dwidth*4/5: 640;                               \
  _T->height= _T->dheight?_T->dheight*4/5: 480;                              \
  _T->hunit = maxss(_T->height/100,3);                                       \
  _T->vunit = maxss(_T->height/100,3);                                       \
  gp_get_ploth_default_sizes(S);                                             \
}
ENDEXTERN
