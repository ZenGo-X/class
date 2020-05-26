#include <stdio.h>
#include <gmp.h>
void f(void) { mpn_gcdext(NULL,NULL, NULL, NULL, 0, NULL, 0); }
int main()
{
  if (sizeof(mp_limb_t) == sizeof(long *))
    printf("%s\n", gmp_version);
  else
    printf("unsupported\n");
  return 0;
}
