import NilCore.Sound

/-!
# The certificate

The two Boolean checks are evaluated by compiled code (`native_decide`); the search takes a few
minutes. Together with `NilCore.core` they give the statement for every coefficient matrix.
-/

namespace NilCore

theorem checkCands_eq : checkCands () = true := by native_decide

theorem root_eq : root () = true := by native_decide

/-- every coefficient matrix admits a nonzero `y` for which `mk C y` is nilpotent -/
theorem every_coef (C : Coef) : ∃ y : Vec, (∃ j, y j ≠ 0) ∧ nilB C y = true :=
  core root_eq checkCands_eq C

end NilCore
