# include <sys/timeb.h>
int main() {
  struct timeb t; ftime(&t);
  return t.time*1000+t.millitm;
}
