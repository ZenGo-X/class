#include <sys/types.h>
#include <unistd.h>
pid_t (*f)() = setsid;
int main(){ return f != setsid; }
