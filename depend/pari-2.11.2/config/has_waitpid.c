#include <stdio.h>
#include <sys/types.h>
#include <sys/wait.h>
int main(){ waitpid(-1,NULL,0); return 0; }
