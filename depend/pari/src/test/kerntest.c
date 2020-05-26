#include "pari.h"

GEN   gen_0, gen_1, gen_m1, gen_2, gen_m2;
THREAD pari_sp avma;
THREAD size_t memused = 0;
ulong  DEBUGLEVEL,DEBUGMEM = 0;
const double LOG10_2 = 0.;
const long lontyp[] = {0};
THREAD VOLATILE int PARI_SIGINT_block, PARI_SIGINT_pending;
struct pari_mainstack * pari_mainstack;
long    *varpriority;

void mt_sigint_block(void) { }
void mt_sigint_unblock(void) { }
void new_chunk_resize(size_t x) {(void)x;}

void specinit()
{
  long size = 100000L;
  pari_mainstack = malloc(sizeof(*pari_mainstack));
  pari_mainstack->size = size;
  pari_mainstack->bot = (pari_sp)malloc(size);
  pari_mainstack->top = avma = pari_mainstack->bot + size;
  gen_0 = cgeti(2); affui(0, gen_0);
  gen_1 = utoipos(1);
  gen_m1= utoineg(1);
  gen_2 = utoipos(2);
  gen_m2= utoineg(2);
}

void sorstring(ulong x)
{
#ifdef LONG_IS_64BIT
  if (x>>32) printf("%08lx  ", x>>32);
  printf("%08lx  ", x & 0xFFFFFFFF);
#else
  printf("%08lx  ", x);
#endif
}

void _voiri(GEN x)
{
  long i, lx = lgefint(x);
  GEN y = int_MSW(x);
  printf("signe: %ld, ",signe(x));
  for (i=2; i < lx; i++, y = int_precW(y)) sorstring(*y);
  printf("\n");
}
void _voirr(GEN x)
{
  long i, lx = lg(x);
  printf("signe: %ld, expo: %ld, ",signe(x),expo(x));
  for (i=2; i < lx; i++) sorstring(x[i]);
  printf("\n");
}

int main()
{
  GEN x,y,r,z, xr,yr;
  specinit();
  x = utoipos(187654321UL);
  y = utoineg(12345678UL);
  printf("INT: %ld\n", itos(x));
  printf("conv:"); _voiri(x);
  printf("+:"); _voiri(addii(x,y));
  printf("-:"); _voiri(subii(x,y));
  printf("*:"); _voiri(mulii(x,y));
  printf("/:"); _voiri(dvmdii(x,y, &z));
  printf("rem:"); _voiri(z);
  printf("pow:\n");
  z = mulii(x,x); _voiri(z);
  z = mulii(z,z); _voiri(z);
  z = mulii(z,z); _voiri(z);
  z = mulii(z,z); _voiri(z);
  z = mulii(z,z); _voiri(z);
  printf("invmod:"); invmod(y,z,&r); _voiri(r);
  xr = itor(x, DEFAULTPREC);
  yr = itor(y, DEFAULTPREC);
  printf("\nREAL: %f\n", rtodbl(xr));
  printf("conv1:"); _voirr(xr);
  printf("conv2:"); _voirr(dbltor(rtodbl(xr)));
  printf("+:"); _voirr(addrr(xr,yr));
  printf("-:"); _voirr(subrr(xr,yr));
  printf("*:"); _voirr(mulrr(xr,yr));
  printf("/:"); _voirr(divrr(xr,yr));
  printf("gcc bug?:"); _voirr(divru(dbltor(3.),2));
  return 0;
}
