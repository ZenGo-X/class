#include <unistd.h>
#include <sys/types.h>
#ifdef __sun
#  include <sys/termios.h>
#endif
#include <sys/ioctl.h>
#ifdef __EMSCRIPTEN__
#error TIOCGWINSZ broken with emscripten
#endif
int main()
{
  struct winsize s;
  int status = ioctl(0, TIOCGWINSZ, &s);
  (void)status; return s.ws_col;
}
