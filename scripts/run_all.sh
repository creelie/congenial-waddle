#!/usr/bin/env bash
# run_all.sh -- build and run every check outside Lean; outputs go to build/.
#   C:      all six-dimensional subspaces of M_3(F_3) (all_six_dim.c), all trace-zero subspaces of
#           dimensions 4 and 5 over F_3 and 5 and 6 over F_2 (trace_zero.c), nilpotent counts (histogram.c)
#   C++:    the search tree of the Lean proof (tree.cpp)
#   Python: examples, counts, random spot checks and the shift identities (checks.py)
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
B="$ROOT/build"
mkdir -p "$B"
cc -O2 -o "$B/all_six_dim" "$ROOT/verification/c/all_six_dim.c"
cc -O2 -o "$B/trace_zero" "$ROOT/verification/c/trace_zero.c"
cc -O2 -o "$B/histogram" "$ROOT/verification/c/histogram.c"
c++ -O2 -std=c++17 -o "$B/tree" "$ROOT/verification/cpp/tree.cpp"

"$B/all_six_dim" | tee "$B/all_six_dim.txt"
grep -q "subspaces 678468820 found 0" "$B/all_six_dim.txt"
for args in "3 5" "3 4" "2 5" "2 6"; do "$B/trace_zero" $args; done | tee "$B/trace_zero.txt"
grep -q "q=3: 5-dim subspaces of sl3: 25095280, without a nonzero nilpotent: 0" "$B/trace_zero.txt"
"$B/histogram" | tee "$B/histogram.txt"
"$B/tree" | tee "$B/tree.txt"
grep -q "open 0" "$B/tree.txt"
python3 -I "$ROOT/verification/python/checks.py" | tee "$B/checks.txt"
echo "all checks passed"
