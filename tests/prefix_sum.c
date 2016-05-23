void prefix_sum_chal(int* v, int N) {
 if(N > 0) {
  int i, j;
  for (i = 0; i < N; i++) {
    v[i] = 0;
    for (j = i + N; j < 2 * N; j++) {
      v[i] += v[j]; // Can we disambiguate pointers here?
    }
  }
 }
}
