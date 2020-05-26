#include <stdlib.h>
#include <pthread.h>

static __thread long counter;

void *start_routine(void *pt_val)
{
  long val = *(long *)pt_val;
  counter = val+1;
  return NULL;
}

int main(void)
{
  pthread_t thread;
  counter = 0;
  if (pthread_create(&thread, NULL, start_routine, &counter))
    exit(1);
  if (pthread_join(thread, NULL))
    exit(1);
  return 0;
}
