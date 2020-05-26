#include <stdio.h>

#ifdef _WIN64
#define long long long
#endif

int main()
{
  if (sizeof(long) == 4)
  {
    union {double d; unsigned long l[2];} x;
    x.d = 2.;
    if      (x.l[0]==0 && x.l[1]==(1UL<<30)) printf("1\n");
    else if (x.l[1]==0 && x.l[0]==(1UL<<30)) printf("0\n");
    else
      printf("NOT IEEE (32 bit)\n");
  }
  else
  {
    union {double d; unsigned long l;} x;
    x.d = 2.;
    if (x.l==((unsigned long)1)<<62) printf("-\n");
    else
      printf("NOT IEEE (64 bit)\n");
  }
  return 0;
}
