import Lake
open Lake DSL

package NilpotentFree where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.34.1"

/-- the search tree over the coefficient matrices and its soundness proof; plain Lean, compiled to
native code so that the `native_decide` checks in `NilCore.Cert` run in a few minutes -/
@[default_target]
lean_lib NilCore where
  precompileModules := true

/-- the theorems about subspaces of `M₃(𝔽₃)` -/
@[default_target]
lean_lib NilFree
