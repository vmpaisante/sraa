#ifndef PREFIX_SUM_H
#define PREFIX_SUM_H

/*
 * These functions receive an array v or size 2 * N, and performs the sum of
 * prefixes of the last N positions of v into the first N positions. E.g.:
 * v[0] = V[N]
 * v[1] = V[N] + V[N+1]
 * ...
 * v[N-1] = V[N] + V[N+1] + ... + V[2 * N - 1]
 */
void prefix_sum_chal(int* v, int* w, int N);
void prefix_sum_goal(int* v, int* w, int N);

#endif
