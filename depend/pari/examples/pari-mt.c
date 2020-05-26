#include <pari/pari.h> /* Include PARI headers */

GEN
my_worker(GEN d, long l)
{
  return l==1 ? Z_factor(d) : det(d);
}

int
main(void)
{
  long i;
  GEN M,N1,N2, F1,F2,D;
  GEN input, output;
  struct pari_mt pt;
  GEN done, worker;
  long workid, pending;
  entree ep_worker={"_worker",0,(void*)my_worker,14,"GL",""};
  /* Initialize the main PARI stack and global objects (gen_0, etc.)
     Postpone initialization of parallelism */
  pari_init_opts(8000000,500000,INIT_JMPm | INIT_SIGm | INIT_DFTm | INIT_noIMTm);
  /* Add my_worker function to gp */
  pari_add_function(&ep_worker);
  /* Initialize parallelism, now that my_worker is registered */
  pari_mt_init();
  /* Compute in the main PARI stack */
  N1 = addis(int2n(256), 1); /* 2^256 + 1 */
  N2 = subis(int2n(193), 1); /* 2^193 - 1 */
  M = mathilbert(80);
  /* Create input and output vectors */
  input  = mkvec3(N1,N2,M);
  output = cgetg(4,t_VEC);
  /* Initialize parallel evaluation of my_worker */
  worker = strtofunction("_worker");
  mt_queue_start(&pt, worker);
  for (i=1; i<=3 || pending; i++)
  {
    /* submit job (input) */
    mt_queue_submit(&pt, i,
      i<=3? mkvec2(gel(input,i),i<=2 ? gen_1: gen_2): NULL);
    /* get result (output) */
    done = mt_queue_get(&pt, &workid, &pending);
    if (done) gel(output,workid) = done;
  }
  /* end parallelism */
  mt_queue_end(&pt);
  F1 = gel(output,1); F2 = gel(output,2); D = gel(output,3);
  pari_printf("F1=%Ps\nF2=%Ps\nlog(D)=%Ps\n", F1, F2, glog(D,3));
  pari_close();
  return 0;
}
