// trace_zero.c Q D : over F_Q (Q prime), counts the D-dimensional subspaces of sl_3(F_Q) (as kernels of
// (8-D) x 8 RREF matrices) and how many contain no nonzero nilpotent (direct test X^3 = 0).
#include <stdio.h>
#include <stdlib.h>
static int Q, D, R, B[8][9];
static void basis(void) {
  int idx[6][2] = {{0,1},{0,2},{1,0},{1,2},{2,0},{2,1}};
  for (int b = 0; b < 8; b++) for (int k = 0; k < 9; k++) B[b][k] = 0;
  for (int b = 0; b < 6; b++) B[b][3*idx[b][0]+idx[b][1]] = 1;
  B[6][0] = 1; B[6][4] = Q-1; B[7][4] = 1; B[7][8] = Q-1;
}
static int isnil(const int *x) {
  int s[9];
  for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) { int t = 0; for (int k = 0; k < 3; k++) t += x[3*i+k]*x[3*k+j]; s[3*i+j] = t % Q; }
  for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) { int t = 0; for (int k = 0; k < 3; k++) t += s[3*i+k]*x[3*k+j]; if (t % Q) return 0; }
  return 1;
}
static int phi[8][8], piv[8];
static long long subs = 0, bad = 0;
static void check(void) {
  subs++;
  int fr[8], nf = 0, ispiv[8] = {0};
  for (int r = 0; r < R; r++) ispiv[piv[r]] = 1;
  for (int c = 0; c < 8; c++) if (!ispiv[c]) fr[nf++] = c;
  int kb[8][8];
  for (int a = 0; a < D; a++) {
    for (int c = 0; c < 8; c++) kb[a][c] = 0;
    kb[a][fr[a]] = 1;
    for (int r = 0; r < R; r++) kb[a][piv[r]] = (Q - phi[r][fr[a]]) % Q;
  }
  long long tot = 1; for (int a = 0; a < D; a++) tot *= Q;
  for (long long m = 1; m < tot; m++) {
    int co[8]; long long t = m; for (int a = 0; a < D; a++) { co[a] = t % Q; t /= Q; }
    int f = 0; while (co[f] == 0) f++; if (co[f] != 1) continue;
    int v[8], x[9];
    for (int c = 0; c < 8; c++) { int s = 0; for (int a = 0; a < D; a++) s += co[a]*kb[a][c]; v[c] = s % Q; }
    for (int k = 0; k < 9; k++) { int s = 0; for (int c = 0; c < 8; c++) s += v[c]*B[c][k]; x[k] = s % Q; }
    if (isnil(x)) return;
  }
  bad++;
}
static void rec(int r, int c) {
  if (r == R) { check(); return; }
  if (c == 8) { rec(r+1, 0); return; }
  int isp = 0; for (int s = 0; s < R; s++) if (c == piv[s]) isp = 1;
  if (c <= piv[r] || isp) { rec(r, c+1); return; }
  for (int x = 0; x < Q; x++) { phi[r][c] = x; rec(r, c+1); }
  phi[r][c] = 0;
}
static void pivs(int r, int lo) {
  if (r == R) { for (int s = 0; s < R; s++) for (int c = 0; c < 8; c++) phi[s][c] = (c == piv[s]); rec(0, 0); return; }
  for (int p = lo; p < 8; p++) { piv[r] = p; pivs(r+1, p+1); }
}
int main(int argc, char **argv) {
  Q = atoi(argv[1]); D = atoi(argv[2]); R = 8 - D; basis();
  pivs(0, 0);
  printf("q=%d: %d-dim subspaces of sl3: %lld, without a nonzero nilpotent: %lld\n", Q, D, subs, bad);
  return 0;
}
