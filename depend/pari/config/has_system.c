#include <stdlib.h>
int (*f)(const char*) = system;
int main(){ return f != system; }
