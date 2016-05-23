#include <stdio.h>

#include "utils.h"

void fill_array(int *a, int N, int max) {
  const int up = 32767;
  int i;
  for (i = 0; i < N; i++) {
    a[i] = i * up % max;
  }
}

void print_array(int *a, int N) {
  int i;
  for (i = 0; i < N; i++) {
    if (i % 10 == 0) {
      printf("\n");
    }
    printf("%8d", a[i]);
  }
  printf("\n");
}

int sum_array(int *src, int N) {
  int sum = 0, i;
  for (i = 0; i < N; i++) {
    sum += src[i];
  }
  return sum;
}
