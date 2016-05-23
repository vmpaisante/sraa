#include <time.h>
#include <stdio.h>
#include <stdlib.h>

#include "utils.h"
#include "prefix_sum.h"

void prefix_sum_init(int* v, int N) {
  int i;
  for (i = 0; i < N; i++) {
    v[i] = 0;
  }
  for (i = N; i < 2 * N; i++) {
    v[i] = 1;
  }
}

int main(int argc, char** argv) {
  if (argc < 2) {
    fprintf(stderr, "Syntax: %s <array_size> <kernel>\n", argv[0]);
    return 1;
  } else {
    clock_t begin, end;
    double time_spent;
    const int N = atoi(argv[1]);
    const int K = atoi(argv[2]);
    int *v = (int*) malloc(2 * N * sizeof(int));
    prefix_sum_init(v, N);
    begin = clock();
    printf("Kernel %d\n", K);
    switch(K) {
      case 1: prefix_sum_chal(v, v + N, N); break;
      case 2: prefix_sum_goal(v, v + N, N);
    }
    end = clock();
    time_spent = (double)(end - begin) / CLOCKS_PER_SEC;
    printf("Time spent = %lf\n", time_spent);
    printf("Sum = %d\n", sum_array(v, N));
    return 0;
  }
}
