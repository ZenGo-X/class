#include <stdio.h>
#include <time.h>
int
main()
{
  struct timespec t;
  printf("%d",clock_gettime(CLOCK_PROCESS_CPUTIME_ID,&t));
  return 0;
}
