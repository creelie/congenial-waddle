import Mathlib
import NilCore.Sound

/-!
# From the search to subspaces of `M₃(𝔽₃)`

`exists_nilpotent_of_core`: if every coefficient matrix `C` admits a nonzero `y` with
`nilB C y = true` (the statement `NilCore.core` derives from the search), then every subspace of
`M₃(𝔽₃)` of dimension at least 6 contains a nonzero nilpotent matrix.
-/

open Matrix Module

namespace NilFree

/-- `3 × 3` matrices over `𝔽₃` -/
abbrev M3 := Matrix (Fin 3) (Fin 3) (ZMod 3)

/-- the nine entries of `X³` vanish when `cubeZero` says so -/
theorem cube_of_cubeZero (a b c d e f g h i : ZMod 3)
    (hz : NilCore.cubeZero a b c d e f g h i = true) :
    (!![a, b, c; d, e, f; g, h, i] : M3) ^ 3 = 0 := by
  simp only [NilCore.cubeZero, Bool.and_eq_true, beq_iff_eq] at hz
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h00, h01⟩, h02⟩, h10⟩, h11⟩, h12⟩, h20⟩, h21⟩, h22⟩ := hz
  have e00 : (a*a + b*d + c*g)*a + (a*b + b*e + c*h)*d + (a*c + b*f + c*i)*g = (0 : ZMod 3) := h00
  have e01 : (a*a + b*d + c*g)*b + (a*b + b*e + c*h)*e + (a*c + b*f + c*i)*h = (0 : ZMod 3) := h01
  have e02 : (a*a + b*d + c*g)*c + (a*b + b*e + c*h)*f + (a*c + b*f + c*i)*i = (0 : ZMod 3) := h02
  have e10 : (d*a + e*d + f*g)*a + (d*b + e*e + f*h)*d + (d*c + e*f + f*i)*g = (0 : ZMod 3) := h10
  have e11 : (d*a + e*d + f*g)*b + (d*b + e*e + f*h)*e + (d*c + e*f + f*i)*h = (0 : ZMod 3) := h11
  have e12 : (d*a + e*d + f*g)*c + (d*b + e*e + f*h)*f + (d*c + e*f + f*i)*i = (0 : ZMod 3) := h12
  have e20 : (g*a + h*d + i*g)*a + (g*b + h*e + i*h)*d + (g*c + h*f + i*i)*g = (0 : ZMod 3) := h20
  have e21 : (g*a + h*d + i*g)*b + (g*b + h*e + i*h)*e + (g*c + h*f + i*i)*h = (0 : ZMod 3) := h21
  have e22 : (g*a + h*d + i*g)*c + (g*b + h*e + i*h)*f + (g*c + h*f + i*i)*i = (0 : ZMod 3) := h22
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first
    | linear_combination e00 | linear_combination e01 | linear_combination e02
    | linear_combination e10 | linear_combination e11 | linear_combination e12
    | linear_combination e20 | linear_combination e21 | linear_combination e22

/-- the free coordinates `(1,1), (2,2), (3,3), (2,1), (3,1), (3,2)` of a matrix -/
def fr : M3 →ₗ[ZMod 3] (Fin 6 → ZMod 3) where
  toFun X := ![X 0 0, X 1 1, X 2 2, X 1 0, X 2 0, X 2 1]
  map_add' X Y := by ext k; fin_cases k <;> simp
  map_smul' c X := by ext k; fin_cases k <;> simp

/-- a matrix whose free coordinates vanish is strictly upper triangular, so its cube is `0` -/
theorem cube_of_fr_eq_zero (X : M3) (h : fr X = 0) : X ^ 3 = 0 := by
  have h0 := congrFun h 0; have h1 := congrFun h 1; have h2 := congrFun h 2
  have h3 := congrFun h 3; have h4 := congrFun h 4; have h5 := congrFun h 5
  simp [fr] at h0 h1 h2 h3 h4 h5
  ext r s
  fin_cases r <;> fin_cases s <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three, h0, h1, h2, h3, h4, h5]

/-- an element of `Fin 3` read as an element of `ZMod 3` (the same type) -/
def z (a : Fin 3) : ZMod 3 := a

/-- the upper positions `(1,2), (1,3), (2,3)` -/
def up : Fin 3 → Fin 3 × Fin 3 := ![(0, 1), (0, 2), (1, 2)]

theorem u_eq (C : NilCore.Coef) (y : NilCore.Vec) (r : Fin 3) :
    z (NilCore.u C y r) = ∑ j : Fin 6, z (C r j) * z (y j) := by
  rw [Fin.sum_univ_six]; rfl

/-- the core statement gives a nilpotent in every subspace of dimension at least 6 -/
theorem exists_nilpotent_of_core
    (hcore : ∀ C : NilCore.Coef, ∃ y : NilCore.Vec, (∃ j, y j ≠ 0) ∧ NilCore.nilB C y = true)
    (W : Submodule (ZMod 3) M3) (hW : 6 ≤ finrank (ZMod 3) W) :
    ∃ X ∈ W, X ≠ 0 ∧ IsNilpotent X := by
  by_cases hex : ∃ X ∈ W, X ≠ 0 ∧ fr X = 0
  · obtain ⟨X, hX, hne, h0⟩ := hex
    exact ⟨X, hX, hne, 3, cube_of_fr_eq_zero X h0⟩
  push Not at hex
  let f : W →ₗ[ZMod 3] (Fin 6 → ZMod 3) := fr.comp W.subtype
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    by_contra hne
    exact hex w w.2 (fun h => hne (Subtype.ext h)) hw
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  have hfin : finrank (ZMod 3) W = finrank (ZMod 3) (Fin 6 → ZMod 3) := by
    simp only [Module.finrank_fin_fun] at hle ⊢; omega
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).1 hinj
  let e := LinearEquiv.ofBijective f ⟨hinj, hsurj⟩
  let g : (Fin 6 → ZMod 3) →ₗ[ZMod 3] M3 := W.subtype.comp e.symm.toLinearMap
  have hg_mem : ∀ y, g y ∈ W := fun y => (e.symm y).2
  have hg_fr : ∀ y, fr (g y) = y := fun y => e.apply_symm_apply y
  let E : Fin 6 → (Fin 6 → ZMod 3) := fun i => fun j => if i = j then 1 else 0
  let C : NilCore.Coef := fun r j => (-(g (E j)) (up r).1 (up r).2 : ZMod 3)
  obtain ⟨y, ⟨j0, hj0⟩, hn⟩ := hcore C
  let yz : Fin 6 → ZMod 3 := fun j => z (y j)
  have hsum : g yz = ∑ i : Fin 6, yz i • g (E i) := by
    conv_lhs => rw [pi_eq_sum_univ yz]
    simp [map_sum, map_smul, E]
  have hX : g yz = !![z (y 0), -z (NilCore.u C y 0), -z (NilCore.u C y 1);
      z (y 3), z (y 1), -z (NilCore.u C y 2);
      z (y 4), z (y 5), z (y 2)] := by
    have hfr := hg_fr yz
    have hup : ∀ r, g yz (up r).1 (up r).2 = -z (NilCore.u C y r) := by
      intro r
      rw [u_eq, hsum, ← Finset.sum_neg_distrib]
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro j _
      show z (y j) * g (E j) (up r).1 (up r).2 = -(z ((-(g (E j))) (up r).1 (up r).2) * z (y j))
      have hneg : z ((-(g (E j))) (up r).1 (up r).2) = -(g (E j) (up r).1 (up r).2) := rfl
      rw [hneg]
      ring
    ext r s
    fin_cases r <;> fin_cases s
    exacts [congrFun hfr 0, hup 0, hup 1, congrFun hfr 3, congrFun hfr 1, hup 2,
      congrFun hfr 4, congrFun hfr 5, congrFun hfr 2]
  refine ⟨g yz, hg_mem yz, ?_, 3, ?_⟩
  · intro h0
    apply hj0
    have := congrFun (hg_fr yz) j0
    rw [h0, map_zero] at this
    exact this.symm
  · rw [hX]
    exact cube_of_cubeZero _ _ _ _ _ _ _ _ _ hn

end NilFree
