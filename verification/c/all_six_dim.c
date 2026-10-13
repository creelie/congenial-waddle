// all_six_dim.c : exhaustive search for a 6-dimensional subspace W of M_3(F_3) with no nonzero nilpotent.
// W = U^perp (standard dot product on F_3^9), U = row space of a 3x9 RREF matrix. W is nilpotent-free
// iff every nonzero nilpotent X has u.X != 0 for some u in U. Prints every U found and the count.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef struct { uint16_t p, m; } V;   // entries 1 -> bit in p, entries 2 (= -1) -> bit in m
static int dot(V a, V b) {
  int s = __builtin_popcount(a.p & b.p) + __builtin_popcount(a.m & b.m)
        - __builtin_popcount(a.p & b.m) - __builtin_popcount(a.m & b.p);
  return ((s % 3) + 3) % 3;
}
static int M[9];
static void mul(const int *a, const int *b, int *c) {
  for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) {
    int s = 0; for (int k = 0; k < 3; k++) s += a[3*i+k] * b[3*k+j]; c[3*i+j] = s % 3; }
}
static V nil[800]; static int nn = 0;
static V mk(const int *e) { V v = {0,0}; for (int k = 0; k < 9; k++) { if (e[k]==1) v.p |= 1<<k; if (e[k]==2) v.m |= 1<<k; } return v; }
static long long leaves = 0, found = 0;
static V rows[3];
static V L1[800], L2[800]; static int n1, n2;
// enumerate row r with pivot > prevpiv; entries before pivot 0, pivot 1, later pivots fixed to 0 afterwards
// we enumerate pivot sets first, then fill.
static int piv[3];
static void fill_rows(int r);
static int ent[3][9];
static void leaf(void) {
  leaves++;
  V u = mk(ent[2]);
  for (int i = 0; i < n2; i++) if (dot(u, L2[i]) == 0) return;
  found++;
  if (found <= 20) {
    for (int r = 0; r < 3; r++) { for (int k = 0; k < 9; k++) printf("%d", ent[r][k]); printf(r<2?"/":"\n"); }
    fflush(stdout);
  }
}
static int freecols[3][9], nfree[3];
static void rec(int r, int idx) {
  if (idx == nfree[r]) {
    if (r == 0) { V u = mk(ent[0]); n1 = 0; for (int i = 0; i < nn; i++) if (dot(u, nil[i]) == 0) L1[n1++] = nil[i]; rec(1, 0); }
    else if (r == 1) { V u = mk(ent[1]); n2 = 0; for (int i = 0; i < n1; i++) if (dot(u, L1[i]) == 0) L2[n2++] = L1[i]; rec(2, 0); }
    else leaf();
    return;
  }
  for (int x = 0; x < 3; x++) { ent[r][freecols[r][idx]] = x; rec(r, idx+1); }
  ent[r][freecols[r][idx]] = 0;
}
int main(void) {
  // nilpotents: X^3 = 0; keep one representative per projective point (first nonzero entry 1)
  int e[9];
  for (int a = 1; a < 19683; a++) {
    int t = a; for (int k = 0; k < 9; k++) { e[k] = t % 3; t /= 3; }
    int f = 0; while (e[f] == 0) f++; if (e[f] != 1) continue;
    int s[9], c[9]; mul(e, e, s); mul(s, e, c);
    int z = 1; for (int k = 0; k < 9; k++) if (c[k]) z = 0;
    if (z) nil[nn++] = mk(e);
  }
  fprintf(stderr, "projective nilpotents %d\n", nn);
  for (piv[0] = 0; piv[0] < 9; piv[0]++) for (piv[1] = piv[0]+1; piv[1] < 9; piv[1]++) for (piv[2] = piv[1]+1; piv[2] < 9; piv[2]++) {
    for (int r = 0; r < 3; r++) {
      nfree[r] = 0;
      for (int k = 0; k < 9; k++) ent[r][k] = 0;
      ent[r][piv[r]] = 1;
      for (int k = piv[r]+1; k < 9; k++) if (k != piv[0] && k != piv[1] && k != piv[2]) freecols[r][nfree[r]++] = k;
    }
    rec(0, 0);
  }
  fprintf(stderr, "subspaces %lld found %lld\n", leaves, found);
  printf("subspaces %lld found %lld\n", leaves, found);
  return 0;
}
