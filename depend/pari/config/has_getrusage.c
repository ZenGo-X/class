#define _INCLUDE_POSIX_SOURCE
#include <stdio.h>
#include <sys/types.h>
#include <sys/time.h>
#include <sys/resource.h>
#include <unistd.h>
int main(){ struct rusage a; printf("%d",getrusage(RUSAGE_SELF,&a)); return 0; }
