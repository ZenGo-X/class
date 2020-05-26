#include <unistd.h>
#include <sys/mman.h>
#ifndef MAP_ANONYMOUS
#define MAP_ANONYMOUS MAP_ANON
#endif
int main(void)
{
  size_t size = sysconf(_SC_PAGE_SIZE)*1000;
  void *b = mmap(NULL, size, PROT_READ|PROT_WRITE,
                             MAP_PRIVATE|MAP_ANONYMOUS,-1,0);
  mmap(b, size, PROT_NONE, MAP_FIXED|MAP_PRIVATE|MAP_ANONYMOUS,-1,0);
  munmap(b, size);
  return 0;
}
