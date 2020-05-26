#define ulong unsigned long
#define ASMINLINE
#include "asm0.h"

#define __asm__ __asm__ volatile

void fun(ulong a, ulong b)
{
  LOCAL_HIREMAINDER;
  LOCAL_OVERFLOW;
  addll(a,b);
  addllx(a,b);
  mulll(a,b);
  addmul(a,b);
#if 0
  bfffo(a);
#endif
}

int main(void)
{
  fun(0xb9f3dcdcUL,0xfbdc740b);
  return 0;
}
