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

using namespace Qt;

int
main(void)
{
  int argc = 1;                         // set argc = 2 for cross
  const char * argv[] = { "gp", "-qws"}; // development using qvfb
  QApplication a(argc, (char**) argv);
  a.exec(); exit(0);
}
