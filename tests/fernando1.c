//fernando1.c
int* bench (int* v, int N){
  int p;    
  int i = 0;
  int j = N - 1;
  int var2 = 0;
  //assert (N>1);
  p = N - 1;
  while(i < p){
    v[i] = 0;
    v[i] = v[p];
    i++;
  }
  return v;
}

