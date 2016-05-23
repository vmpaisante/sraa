#ifndef _UTILS_H
#define _UTILS_H

/*
 * Fillup all the integer memory positions from a till a + N with integers in
 * the interval [0, max]
 */
void fill_array(int* a, int N, int max);

/*
 * Print all the integer elements in memory positions a .. a + N:
 */
void print_array(int* a, int N);

/*
 * Sums up all the integer elements in memory positions a .. a + N:
 */
int sum_array(int* a, int N);

#endif
