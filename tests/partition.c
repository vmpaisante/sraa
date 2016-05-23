int partition( int a[], int l, int r) {
  int pivot, i, j, t;

  pivot = a[l];
  i = l;
  j = r+1;
  while(1) {
    do {
      ++i;
    } while (a[i] <= pivot && i <= r);
    do {
      --j;
    } while (a[j] > pivot);
    if (i >= j) {
      break;
    } else {
      t = a[i];
      a[i] = a[j];
      a[j] = t;
    }
  }
  t = a[l];
  a[l] = a[j];
  a[j] = t;
  return j;
}
