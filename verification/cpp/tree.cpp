// tree.cpp : the search tree of the Lean proof (lean/NilCore/Search.lean), written again in C++.
// A space W of dimension 6 that meets the strictly upper triangular matrices only in 0 is the set of
// matrices X(y) with entries y at the free positions (1,1),(2,2),(3,3),(2,1),(3,1),(3,2) and -(C y)
// at (1,2),(1,3),(2,3), for a 3x6 matrix C over F_3. The columns of C are fixed in the order
// (2,1),(3,1),(3,2),(1,1),(2,2),(3,3); a node is closed when some y with a 1 at the newest column,
// supported on the fixed columns, gives X(y)^3 = 0. Prints the node counts by depth; "open 0" proves that
// every such W contains a nonzero nilpotent.
#include <array>
#include <cstdio>
#include <vector>

namespace {
constexpr int kUpper[3] = {1, 2, 5};
constexpr int kFree[6] = {0, 4, 8, 3, 6, 7};
constexpr int kOrder[6] = {3, 4, 5, 0, 1, 2};
using Mat = std::array<int, 9>;
int C[3][6];
long long nodes = 0, closed = 0, open_nodes = 0;
long long nodes_at[7], closed_at[7];
std::vector<std::array<int, 6>> cand[7];

Mat mul(const Mat& a, const Mat& b) {
  Mat c{};
  for (int i = 0; i < 3; ++i)
    for (int j = 0; j < 3; ++j) {
      int s = 0;
      for (int k = 0; k < 3; ++k) s += a[3 * i + k] * b[3 * k + j];
      c[3 * i + j] = s % 3;
    }
  return c;
}

bool nilpotent(const std::array<int, 6>& y) {
  Mat x{};
  for (int j = 0; j < 6; ++j) x[kFree[j]] = y[j];
  for (int r = 0; r < 3; ++r) {
    int s = 0;
    for (int j = 0; j < 6; ++j) s += C[r][j] * y[j];
    x[kUpper[r]] = (3 - s % 3) % 3;
  }
  Mat cube = mul(mul(x, x), x);
  for (int v : cube) if (v) return false;
  return true;
}

void dfs(int d) {
  ++nodes;
  ++nodes_at[d];
  if (d > 0)
    for (const auto& y : cand[d])
      if (nilpotent(y)) { ++closed; ++closed_at[d]; return; }
  if (d == 6) { ++open_nodes; return; }
  const int col = kOrder[d];
  for (int v = 0; v < 27; ++v) {
    C[0][col] = v % 3; C[1][col] = v / 3 % 3; C[2][col] = v / 9;
    dfs(d + 1);
  }
  C[0][col] = C[1][col] = C[2][col] = 0;
}
}  // namespace

int main() {
  for (int d = 1; d <= 6; ++d) {
    int tot = 1;
    for (int a = 0; a < d - 1; ++a) tot *= 3;
    for (int m = 0; m < tot; ++m) {
      std::array<int, 6> y{};
      int t = m;
      for (int a = 0; a < d - 1; ++a) { y[kOrder[a]] = t % 3; t /= 3; }
      y[kOrder[d - 1]] = 1;
      cand[d].push_back(y);
    }
  }
  dfs(0);
  for (int d = 0; d <= 6; ++d)
    std::printf("depth %d: nodes %lld closed %lld\n", d, nodes_at[d], closed_at[d]);
  std::printf("nodes %lld closed %lld open %lld\n", nodes, closed, open_nodes);
  return open_nodes == 0 ? 0 : 1;
}
