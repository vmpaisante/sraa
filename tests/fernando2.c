//fernando2.c
int bench (int* v, int N){
  int* p = v + N - 1;    
  int i = 0;
  int j = N - 1;
  while (v < p){
    *v = 0;
    *v = *p;
    v++;
  }
  return 0;
}
