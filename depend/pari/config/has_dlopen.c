#include <stdio.h>
#include <dlfcn.h>
int main() {dlopen("a",RTLD_LAZY); return 0;}
