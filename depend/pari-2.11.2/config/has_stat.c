#include <sys/stat.h>
#if (!defined(_MSC_VER) && !defined(_WIN32))
#  include <sys/types.h>
#  include <unistd.h>
#endif
int main(void) { struct stat buf;
  if (stat (".", &buf) || !S_ISDIR(buf.st_mode)) return 1;
  return 0;
}
