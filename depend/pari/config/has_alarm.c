#include <unistd.h>
unsigned int (*f)(unsigned int) = alarm;
int main(){ return f != alarm; }
