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
//  High resolution plot using Trolltech's Qt library
//
//  You may possibly want to use this file with a "Qt Free Edition"
//  which is distributed under the terms of the Q PUBLIC LICENSE (QPL),
//  or with a "Qt/Embedded Free Edition" which is
//  distributed under the terms of the GNU General Public License (GPL).
//  Please check http://www.trolltech.com for details.
//
//                            ---Nils-Peter Skoruppa (www.countnumber.de)
/////////////////////////////////////////////////////////////////////////////
#include <Qt/qapplication.h>
#include <Qt/qwidget.h>
#include <Qt/qpainter.h>
#include <Qt/qcolor.h>
#include <Qt/qdesktopwidget.h>
#include <Qt/qevent.h>
#include <Qt/qpixmap.h>
#include <Qt/qsignalmapper.h>
#include <Qt/qimage.h>
#include <Qt/qimagewriter.h>
#include <Qt/qmainwindow.h>
#include <Qt/qmenubar.h>
#include <Qt/qtoolbar.h>
#include <Qt/qaction.h>
#include <Qt/qfiledialog.h>
#include <Qt/qmessagebox.h>
#include <Qt/qfile.h>
#include <Qt/qstatusbar.h>
#include <Qt/qimage.h>
#include <Qt/qlabel.h>
#include <Qt/qspinbox.h>
#include <Qt/qlayout.h>

extern "C" {
#include "pari.h"
#include "rect.h"
#undef grem
}

using namespace Qt;

class Plotter: public QWidget {

  Q_OBJECT

signals:
  void clicked();

protected:
  void mouseReleaseEvent(QMouseEvent*);

public:
  Plotter(PARI_plot *T, GEN w, GEN x, GEN y, QWidget* parent = 0);
  void save(const QString& s = *plotFile + ".xpm",
            const QString& f = QString("XPM"));

protected:
  void paintEvent(QPaintEvent *);

private:
  PARI_plot *T;
  GEN w, x, y;
  QColor color0;
  QFont font;
  static QString *plotFile;
  void draw(QPainter *p);
};

QString *Plotter::plotFile = new QString("pariplot");

static QColor
rgb_color(long c)
{
  int r, g, b; long_to_rgb(c, &r, &g, &b);
  return QColor(r, g, b);
}
Plotter::Plotter(PARI_plot *T, GEN w, GEN x, GEN y, QWidget* parent)
    : QWidget(parent), font("lucida", 9) {
  this->w = w;
  this->x = x;
  this->y = y;
  this->T = T;
  this->setFont(font);
  {
    int r, g, b;
    color_to_rgb(gel(GP_DATA->colormap,1), &r, &g, &b);
    color0 = QColor(r, g, b);
  }
  QPalette palette;
  palette.setColor(backgroundRole(), color0);
  setPalette(palette);
}

static void
SetForeground(void *data, long col)
{
  QPainter *p = (QPainter *)data;
  p->setPen(rgb_color(col));
}

static void
DrawPoint(void *data, long x, long y)
{
  QPainter *p = (QPainter *)data;
  p->drawPoint(x, y);
}

static void
DrawLine(void *data, long x1, long y1, long x2, long y2)
{
  QPainter *p = (QPainter *)data;
  p->drawLine(x1, y1, x2, y2);
}

static void
DrawRectangle(void *data, long x, long y, long w, long h)
{
  QPainter *p = (QPainter *)data;
  p->drawRect(x, y, w, h);
}

static void
FillRectangle(void *data, long x, long y, long w, long h)
{
  QPainter *p = (QPainter *)data;
  p->fillRect(x, y, w, h, p->pen().color());
}

static void
DrawPoints(void *data, long nb, struct plot_points *pt)
{
  QPainter *p = (QPainter *)data;
  QPolygon xp = QPolygon(nb);
  long i;
  for (i = 0;i < nb; i++) xp.setPoint(i,pt[i].x, pt[i].y);
  p->drawPoints(xp);
}

static void
DrawLines(void *data, long nb, struct plot_points *pt)
{
  QPainter *p = (QPainter *)data;
  QPolygon xp = QPolygon(nb);
  long i;
  for (i = 0;i < nb; i++) xp.setPoint(i, pt[i].x, pt[i].y);
  p->drawPolyline(xp);
}

static void
DrawString(void *data, long x, long y, char *text, long numtext)
{
  QPainter *p = (QPainter *)data;
  p->drawText(x, y, QString(text).left(numtext));
}

void
Plotter::draw(QPainter *p)
{
  struct plot_eng plotQt;
  plotQt.sc=&SetForeground;
  plotQt.pt=&DrawPoint;
  plotQt.ln=&DrawLine;
  plotQt.bx=&DrawRectangle;
  plotQt.fb=&FillRectangle;
  plotQt.mp=&DrawPoints;
  plotQt.mp=&DrawPoints;
  plotQt.ml=&DrawLines;
  plotQt.st=&DrawString;
  plotQt.pl=T;
  plotQt.data=(void *)p;
  double xs = double(this->width()) / T->width;
  double ys = double(this->height()) / T->height;
  gen_draw(&plotQt, this->w, this->x, this->y, xs, ys);
}

void
Plotter::save(const QString& s, const QString& f)
{
  QPixmap pm(this->width(), this->height());
  QPainter p;
  p.begin(&pm);
  p.initFrom(this);
  p.fillRect(0, 0, pm.width(), pm.height(), color0);
  draw(&p);
  p.end();
  pm.save(s, f.toAscii().data());
}

void
Plotter::paintEvent(QPaintEvent *)
{
  QPainter p;
  p.begin(this);
  this->draw(&p);
  p.end();
}

void Plotter::mouseReleaseEvent(QMouseEvent*) { emit clicked(); }

/* XPM */
static const char * const fullscreen_xpm[] = {
"14 14 2 1",
"         c None",
".        c #000000",
"..............",
".     ..     .",
".     ..     .",
".    ....    .",
".     ..     .",
".  .  ..  .  .",
"..............",
"..............",
".  .  ..  .  .",
".     ..     .",
".    ....    .",
".     ..     .",
".     ..     .",
".............."};

class PlotWindow: public QMainWindow
{
  Q_OBJECT

public:
  PlotWindow(PARI_plot *T, GEN w, GEN x, GEN y, QWidget* parent = 0);
  ~PlotWindow();

protected:
  void resizeEvent(QResizeEvent *);

private slots:
  void fullScreen();
  void normalView();
  void save();
  void save(int);

private:
  static const QList<QByteArray> file_formats;
  Plotter *plr;
  QString saveFileName;
  int saveFileFormat;
  QLabel *res;
  QMenu* menuFile;
  QMenu* menuView;
  QMenu* menuFormat;
  QAction* quitAction;
  QAction* saveAction;
  QAction* fullScreenAction;
  QSignalMapper* signalMapper;
  QIcon* icon;
};

const QList<QByteArray> PlotWindow::file_formats = QImageWriter::supportedImageFormats();

PlotWindow::PlotWindow(PARI_plot *T, GEN w, GEN x, GEN y, QWidget* parent)
    : QMainWindow(parent), saveFileName("pariplot"), saveFileFormat(0)
{
  setWindowTitle("Pari QtPlot");

  QPalette palette;
  palette.setColor(this->backgroundRole(), white);
  this->setPalette(palette);

  menuFile = menuBar()->addMenu("&File");

  saveAction = new QAction("&Save",this);
  saveAction->setShortcut(QKeySequence(CTRL+Key_S));
  connect (saveAction, SIGNAL(triggered()), this, SLOT(save()));
  menuFile->addAction(saveAction);
  menuFormat = menuFile->addMenu("Save &as");

  signalMapper = new QSignalMapper(this);

  for(int i = 0; i < file_formats.count(); i++)
  {
    QAction* tmpAction;
    tmpAction = new QAction(QString(file_formats.at(i)),this);
    connect (tmpAction, SIGNAL(triggered()), signalMapper, SLOT(map()));
    signalMapper->setMapping(tmpAction,i);
    menuFormat->addAction(tmpAction);
  }

  connect (signalMapper, SIGNAL(mapped(int)), this,SLOT(save(int)));

  quitAction = new QAction("&Quit",this);
  quitAction->setShortcut(QKeySequence(CTRL+Key_Q));
  connect (quitAction, SIGNAL(triggered()), this, SLOT(close()));
  menuFile->addAction(quitAction);

  menuView = menuBar()->addMenu("&View");

  fullScreenAction = new QAction("Use &full screen", this);
  fullScreenAction->setShortcut(QKeySequence(CTRL+Key_F));
  icon = new QIcon();
  icon->addPixmap(QPixmap((const char ** )fullscreen_xpm));
  fullScreenAction->setIcon(*icon);
  connect(fullScreenAction, SIGNAL(triggered()), this, SLOT(fullScreen()));
  menuView->addAction(fullScreenAction);

  // Setting up an instance of plotter
  plr = new Plotter(T, w, x, y, this);
  connect(plr, SIGNAL(clicked()), this, SLOT(normalView()));
  this->setCentralWidget(plr);

  this->resize(T->width, T->height + 24);
  res = new QLabel();
  statusBar()->addWidget(res);
}

PlotWindow::~PlotWindow() {}

void
PlotWindow::resizeEvent(QResizeEvent *e)
{
  QMainWindow::resizeEvent(e);
  res->setText(QString("Resolution: ") +
                QString::number(plr->width()) + "x" +
                QString::number(plr->height()));
  res->setFixedSize(res->sizeHint());
}


void
PlotWindow::fullScreen()
{
  plr->setParent(0);
  plr->showMaximized();
  plr->show();
}

void
PlotWindow::normalView()
{
  if (!plr->parentWidget())
  {
    plr->setParent(this);
    this->setCentralWidget(plr);
    plr->show();
  }
}

void
PlotWindow::save()
{
  QString ff = QString(file_formats.at(saveFileFormat));
  QString fn = saveFileName + "." + ff.toLower();
  plr->save(fn, ff);
  setWindowTitle(QString("Pari QtPlot:") + fn);
}

void
PlotWindow::save(int id)
{
  QString ff(file_formats.at(id));
  QString s(ff + " (*." + ff.toLower() +");;All (*)");
  QString fn = QFileDialog::getSaveFileName(this, saveFileName + "." + ff,
    saveFileName + "." + ff, s);
  if (!fn.isEmpty())
  {
    saveFileName = fn;
    int p;
    if ((p = saveFileName.lastIndexOf("." + ff, -1)) >= 0)
      saveFileName.truncate(p);
    saveFileFormat = id;
    save();
  }
}

#include "plotQt4.moc.cpp"

static void
draw(PARI_plot *T, GEN w, GEN x, GEN y)
{
  if (pari_daemon()) return;  // parent process returns

  // launch Qt window
  int argc = 1;                         // set argc = 2 for cross
  const char * argv[] = { "gp", "-qws"}; // development using qvfb
  QApplication a(argc, (char**) argv);
  PlotWindow *win = new PlotWindow(T, w, x, y);
  win->show();
  a.exec();
  pari_close(); exit(0);
}

INLINE void
gp_get_display_sizes(long *dwidth, long *dheight, long *fwidth, long *fheight)
{
  /* There must be an easier way to get desktop size... */
  int argc = 1;
  const char * argv[] = { "gp", "-qws"};
  QApplication a(argc, (char**) argv);
  QDesktopWidget *qw = new QDesktopWidget();
  if (qw)
  {
    QRect rec = qw->screenGeometry();
    *dwidth  = rec.width();   // screen width
    *dheight = rec.height();  //   and height
  }
  else
  {
    *dwidth  = 0;
    *dheight = 0;
  }
  *fwidth  = 6; // font width
  *fheight = 9; //   and height
}

void
gp_get_plot(PARI_plot *T)
{
  gp_get_plot_generic(T,gp_get_display_sizes);
  T->draw = &draw;
}
