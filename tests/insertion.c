void ins_sort_chal(int* v, int N) {
  int i, j;
  for (i = 0; i < N - 1; i++) {
    for (j = i + 1; j < N; j++) {
      if (v[i] > v[j]) {
        int tmp = v[i];
        v[i] = v[j];
        v[j] = tmp;
      }
    }
  }
}
