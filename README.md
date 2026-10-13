# Nilpotent-free spaces of 3 × 3 matrices over 𝔽₃

**Result.** Every linear subspace of the 3 × 3 matrices over the field with three elements of
dimension at least six contains a nonzero nilpotent matrix. The largest dimension of a subspace
without nonzero nilpotent elements is five, attained by

```
      [ a      0       b ]
W5 =  [ 0  c - d - e   c ] ,   a, b, c, d, e ∈ 𝔽₃.
      [ b      d       e ]
```

This disproves Conjecture 8 of Y. Wigderson, *Duality for matrix space questions*
([arXiv:2609.29177](https://arxiv.org/abs/2609.29177), to appear in Amer. Math. Monthly), which asks
for a nilpotent-free space of dimension n² − C(n,2) over every finite field and every n; for n = 3
over 𝔽₃ that is dimension six. The Gerstenhaber–Serezhkin theorem itself is unaffected.

The conjecture does hold for n ≤ 2 over every finite field, and for n = 3 over 𝔽₂ and 𝔽₅
(explicit six-dimensional examples). For n = 3 over 𝔽₄, 𝔽₇, 𝔽₈ and 𝔽₉ it is open.

## What is proved, and how

| Statement | Lean theorem | Trust base |
|---|---|---|
| Every subspace of M₃(𝔽₃) of dimension ≥ 6 has a nonzero nilpotent | `NilFree.exists_nilpotent` | standard axioms + compiled search |
| Conjecture 8 is false | `NilFree.not_conjecture8`, `NilFree.not_holdsAt_zmod3` | standard axioms + compiled search |
| The largest dimension is 5 | `NilFree.isGreatest_nilFree_finrank` | standard axioms + compiled search |
| W5 is nilpotent-free | `NilFree.exists_nilFree_five` | standard axioms |
| Conjecture 8 holds for n ≤ 2 over every finite field | `NilFree.holdsAt_le_two` | standard axioms |
| Conjecture 8 holds for n = 3 over 𝔽₂ and 𝔽₅ | `NilFree.holdsAt_zmod2`, `NilFree.holdsAt_zmod5` | standard axioms |
| Characteristic three: unique nilpotent translate, Prop. 4.4, its corollary | `NilFree.existsUnique_nilpotent_translate`, `NilFree.exists_nilpotent_of_one_mem`, `NilFree.one_not_mem_of_nilFree` | standard axioms |

The standard axioms are `propext`, `Classical.choice` and `Quot.sound`. The "compiled search" is
the two Boolean equations `NilCore.root () = true` and `NilCore.checkCands () = true`, evaluated by
`native_decide` (about five minutes); Lean records each as an axiom stating exactly that equation.
`lean/Check.lean` prints the axioms of all sixteen main theorems and `scripts/audit_axioms.py`
checks them.

The proof of the main theorem has two parts.

1. **Reduction** (`lean/NilFree/Bridge.lean`). A six-dimensional subspace that meets the strictly
   upper triangular matrices only in 0 is the set of matrices `X_C(y)` with `y ∈ 𝔽₃⁶` at the
   positions (1,1), (2,2), (3,3), (2,1), (3,1), (3,2) and `−Cy` at (1,2), (1,3), (2,3), for a unique
   3 × 6 matrix `C`.
2. **Finite statement** (`lean/NilCore/`). For every `C` there is `y ≠ 0` with `X_C(y)³ = 0`. A
   search tree fixes the columns of `C` one at a time and closes a node as soon as a vector supported
   on the fixed columns gives a nilpotent matrix: 3,109,888 nodes, none left open. Its soundness is
   proved in Lean by induction.

Independent checks outside Lean (`scripts/run_all.sh`, about fifteen minutes):

- `verification/c/all_six_dim.c`: all 678,468,820 six-dimensional subspaces of M₃(𝔽₃), none
  nilpotent-free;
- `verification/c/trace_zero.c`: all 25,095,280 five-dimensional subspaces of the trace-zero
  matrices over 𝔽₃ contain a nonzero nilpotent (a second proof, without the reduction);
- `verification/c/histogram.c`: how many nilpotent lines those subspaces contain (as few as one);
- `verification/cpp/tree.cpp`: the search tree again, with node counts by depth;
- `verification/python/checks.py`: the example W5, the small fields, random spot checks and the
  characteristic-three identities.

## Layout

```
lean/                 Lean 4 + Mathlib (v4.34.1)
  NilCore/            the search and its soundness proof (plain Lean, compiled)
  NilFree/Bridge.lean the reduction to the finite statement
  NilFree/Main.lean   Theorems A and B, Conjecture 8 as a formal statement
  NilFree/Holds.lean  n ≤ 2 over every finite field; n = 3 over 𝔽₂ and 𝔽₅
  NilFree/Char3.lean  Section 4: characteristic three, with Chevalley–Warning
  Check.lean          axiom audit
verification/         C, C++ and Python checks
preprint/             the paper (amsart) and its TikZ figures
dist/                 PDF, LaTeX source with PNG figures, arXiv tarball
scripts/              run_all.sh, build_paper.sh, audit_axioms.py
PRIORITY-CHECK.md     dated check that the conjecture had not been settled
```

## Reproduce

```
cd lean && lake exe cache get && lake build && lake env lean Check.lean | python3 ../scripts/audit_axioms.py /dev/stdin
scripts/run_all.sh
scripts/build_paper.sh
```

## Author

Deep Bhattacharjee, formerly Electro-Gravitational Space Propulsion Laboratory (EGSPL),
Bhubaneswar, Odisha 751030, India. d.bhattacharjee@erl-forschung.de (corresponding),
itsdeep@live.com. ORCID [0000-0003-0466-750X](https://orcid.org/0000-0003-0466-750X).

The conjecture is Y. Wigderson's; the counterexample, proofs and computations are in this
repository. Released under the MIT licence.
