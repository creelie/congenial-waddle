// histogram.c : for every 5-dim subspace W0 of sl_3(F_3), the number of projective nilpotent points,
// histogram, split by whether I lies in W0.
#include <stdio.h>
static int B[8][9];
static void basis(void) {
  int idx[6][2] = {{0,1},{0,2},{1,0},{1,2},{2,0},{2,1}};
  for (int b = 0; b < 8; b++) for (int k = 0; k < 9; k++) B[b][k] = 0;
  for (int b = 0; b < 6; b++) B[b][3*idx[b][0]+idx[b][1]] = 1;
  B[6][0] = 1; B[6][4] = 2; B[7][4] = 1; B[7][8] = 2;
}
static int isnil(const int *x) {
  int s[9];
  for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) { int t = 0; for (int k = 0; k < 3; k++) t += x[3*i+k]*x[3*k+j]; s[3*i+j] = t % 3; }
  for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) { int t = 0; for (int k = 0; k < 3; k++) t += s[3*i+k]*x[3*k+j]; if (t % 3) return 0; }
  return 1;
}
static int phi[3][8], piv[3];
static long long hist[2][200];
static void check(void) {
  int fr[5], nf = 0, ispiv[8] = {0};
  for (int r = 0; r < 3; r++) ispiv[piv[r]] = 1;
  for (int c = 0; c < 8; c++) if (!ispiv[c]) fr[nf++] = c;
  int kb[5][8];
  for (int a = 0; a < 5; a++) { for (int c = 0; c < 8; c++) kb[a][c] = 0; kb[a][fr[a]] = 1;
    for (int r = 0; r < 3; r++) kb[a][piv[r]] = (3 - phi[r][fr[a]]) % 3; }
  // I = B6 + 2*B7 ... check: I has coords (0,..,0,1,2) since E11-E22 + 2(E22-E33) = E11+E22-2E33 = E11+E22+E33 mod 3
  int hasI = 1; int Iv[8] = {0,0,0,0,0,0,1,2};
  for (int r = 0; r < 3; r++) { int t = 0; for (int c = 0; c < 8; c++) t += phi[r][c]*Iv[c]; if (t % 3) hasI = 0; }
  int cnt = 0;
  for (int m = 1; m < 243; m++) {
    int co[5], t = m; for (int a = 0; a < 5; a++) { co[a] = t % 3; t /= 3; }
    int f = 0; while (co[f] == 0) f++; if (co[f] != 1) continue;
    int v[8], x[9];
    for (int c = 0; c < 8; c++) { int s = 0; for (int a = 0; a < 5; a++) s += co[a]*kb[a][c]; v[c] = s % 3; }
    for (int k = 0; k < 9; k++) { int s = 0; for (int c = 0; c < 8; c++) s += v[c]*B[c][k]; x[k] = s % 3; }
    cnt += isnil(x);
  }
  hist[hasI][cnt]++;
}
static void rec(int r, int c) {
  if (r == 3) { check(); return; }
  if (c == 8) { rec(r+1, 0); return; }
  if (c <= piv[r] || c == piv[0] || c == piv[1] || c == piv[2]) { rec(r, c+1); return; }
  for (int x = 0; x < 3; x++) { phi[r][c] = x; rec(r, c+1); }
  phi[r][c] = 0;
}
int main(void) {
  basis();
  for (piv[0] = 0; piv[0] < 8; piv[0]++) for (piv[1] = piv[0]+1; piv[1] < 8; piv[1]++) for (piv[2] = piv[1]+1; piv[2] < 8; piv[2]++) {
    for (int r = 0; r < 3; r++) for (int c = 0; c < 8; c++) phi[r][c] = (c == piv[r]);
    rec(0, 0);
  }
  for (int h = 0; h < 2; h++) { printf("I in W0: %d\n", h); for (int k = 0; k < 200; k++) if (hist[h][k]) printf("  %d projective nilpotents: %lld subspaces\n", k, hist[h][k]); }
  return 0;
}
