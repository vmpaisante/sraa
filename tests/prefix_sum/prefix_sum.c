//void prefix_sum_chal(int v[restrict], int  w[restrict], int N) {
void prefix_sum_chal(int v[], int  w[], int N) {
  int i, j;
  for (i = 0; i < N; ++i) {
    v[i] = 0;
    for (j = 0; j < N; ++j) {
      v[i] += w[j]; // Can we disambiguate pointers here?
    }
  }
}

void prefix_sum_goal(int * v, int* w, int N) {
  int i, j;
  for (i = 0; i < N; ++i) {
    int tmp = 0;
    for (j = 0; j < N; ++j) {
      tmp += w[j];
    }
    v[i] = tmp;
  }
}
