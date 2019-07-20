#include <stdio.h>
#include <gmp.h>
int main()
{
  mp_limb_t *x = NULL, *y = NULL;
  long nx = 0;
#ifdef mpn_sqr
  mpn_sqr(y, x, nx);
#else
  mpn_mul_n(y, x, x, nx);
#endif
  return 0;
}
