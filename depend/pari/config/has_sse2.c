#include <emmintrin.h>
typedef __v2di bit_array;
#define AND(a,b) ((bit_array)__builtin_ia32_andps((__v4sf)(a), (__v4sf)(b)))
#define EXT0(a) ((ulong)__builtin_ia32_vec_ext_v2di((__v2di)(a), 0))
#define EXT1(a) ((ulong)__builtin_ia32_vec_ext_v2di((__v2di)(a), 1))
#define TEST(a) (EXT0(a) || EXT1(a))
#define RBA(a) ((__v2di){((long) a), ((long) a)})

int main(void)
{
  bit_array x = RBA(1L), y = RBA(3L);
  ulong t = TEST(AND(x,y));
  (void) t;
  return 0;
}
