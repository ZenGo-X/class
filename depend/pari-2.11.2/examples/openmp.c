#include <pari/pari.h> /* Include PARI headers */

#include <omp.h>       /* Include OpenMP headers */

#define MAXTHREADS 3  /* Max number of parallel threads */

int
main(void)
{
  GEN M,N1,N2, F1,F2,D;
  struct pari_thread pth[MAXTHREADS];
  int numth = omp_get_max_threads(), i;
  /* Initialise the main PARI stack and global objects (gen_0, etc.) */
  pari_init(4000000,500000);
  if (numth > MAXTHREADS)
  {
    numth = MAXTHREADS;
    omp_set_num_threads(numth);
  }
  /* Compute in the main PARI stack */
  N1 = addis(int2n(256), 1); /* 2^256 + 1 */
  N2 = subis(int2n(193), 1); /* 2^193 - 1 */
  M = mathilbert(80);
  /*Allocate pari thread structures */
  for (i = 1; i < numth; i++) pari_thread_alloc(&pth[i],4000000,NULL);
#pragma omp parallel
  {
    int this_th = omp_get_thread_num();
    if (this_th) (void)pari_thread_start(&pth[this_th]);
#pragma omp sections
    {
#pragma omp section
      {
        F1 = factor(N1);
      }
#pragma omp section
      {
        F2 = factor(N2);
      }
#pragma omp section
      {
        D = det(M);
      }
    } /* omp sections */
    if (this_th) pari_thread_close();
  } /* omp parallel */
  pari_printf("F1=%Ps\nF2=%Ps\nlog(D)=%Ps\n", F1, F2, glog(D,3));
  for (i = 1; i < numth; i++) pari_thread_free(&pth[i]);
  return 0;
}
