#include <stdio.h>
#include <stdlib.h>
#include <math.h>

typedef unsigned long long ull;

#pragma GCC push_options
#pragma GCC optimize("O0")
int fpu_debug() {
  ull K_ull = 0x40105616d1b7ddf7;
  double K = *(double*)(&K_ull);
  double cos_k = 0;//cos(K);
  double sin_k = sin(K);
  printf("cos:%llx, sin:%llx\n", *(ull*)(&cos_k), *(ull*)(&sin_k));
  return (0);
}
#pragma GCC pop_options

int main(){
  fpu_debug();
}
