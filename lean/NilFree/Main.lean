import NilFree.Bridge
import NilFree.Holds
import NilCore.Cert

/-!
# Wigderson's Conjecture 8 fails over `𝔽₃`

Y. Wigderson (*Duality for matrix space questions*, arXiv:2609.29177, Conjecture 8) conjectured
that for every finite field `F` and every `n ≥ 1` there is a space of `n × n` matrices over `F` of
dimension `n² - C(n,2)` with no nonzero nilpotent element. For `F = 𝔽₃` and `n = 3` this would be
a 6-dimensional space. Every subspace of `M₃(𝔽₃)` of dimension at least 6 contains a nonzero
nilpotent matrix (`exists_nilpotent`), so the conjecture is false (`not_conjecture8`); the largest
dimension of a nilpotent-free subspace of `M₃(𝔽₃)` is 5 (`isGreatest_nilFree_finrank`).
-/

open Matrix Module

namespace NilFree

/-- every subspace of `M₃(𝔽₃)` of dimension at least 6 contains a nonzero nilpotent matrix -/
theorem exists_nilpotent (W : Submodule (ZMod 3) M3) (hW : 6 ≤ finrank (ZMod 3) W) :
    ∃ X ∈ W, X ≠ 0 ∧ IsNilpotent X :=
  exists_nilpotent_of_core NilCore.every_coef W hW

/-- Conjecture 8 of arXiv:2609.29177 -/
def Conjecture8 : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (n : ℕ), ∃ W : Submodule F (Matrix (Fin n) (Fin n) F),
    finrank F W = n ^ 2 - n.choose 2 ∧ ∀ X ∈ W, IsNilpotent X → X = 0

/-- Conjecture 8 fails for `𝔽₃` and `n = 3` -/
theorem not_holdsAt_zmod3 : ¬ HoldsAt (ZMod 3) 3 := by
  rintro ⟨W, hdim, hW⟩
  have h6 : 6 ≤ finrank (ZMod 3) W := by rw [hdim]; decide
  obtain ⟨X, hX, hne, hnil⟩ := exists_nilpotent W h6
  exact hne (hW X hX hnil)

theorem conjecture8_iff : Conjecture8 ↔ ∀ (F : Type) [Field F] [Fintype F] (n : ℕ), HoldsAt F n :=
  Iff.rfl

theorem not_conjecture8 : ¬ Conjecture8 := by
  intro h
  obtain ⟨W, hdim, hW⟩ := h (ZMod 3) 3
  have h6 : 6 ≤ finrank (ZMod 3) W := by rw [hdim]; decide
  obtain ⟨X, hX, hne, hnil⟩ := exists_nilpotent W h6
  exact hne (hW X hX hnil)

/-- a nilpotent `3 × 3` matrix over `𝔽₃` has vanishing cube (Cayley–Hamilton) -/
theorem pow_three_of_isNilpotent {X : M3} (h : IsNilpotent X) : X ^ 3 = 0 := by
  have h1 := Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent h
  have h2 : X.charpoly = Polynomial.X ^ 3 := by
    have := h1.eq_zero
    simpa [Fintype.card_fin, sub_eq_zero] using this
  have := Matrix.aeval_self_charpoly X
  rw [h2] at this
  simpa using this

/-- the matrices `[[a, 0, b], [0, c - d - e, c], [b, d, e]]` -/
def mat5 (a b c d e : ZMod 3) : M3 := !![a, 0, b; 0, c - d - e, c; b, d, e]

set_option maxRecDepth 100000 in
/-- checked by the kernel over all `3⁵` choices -/
theorem mat5_nilFree : ∀ a b c d e : ZMod 3, mat5 a b c d e ^ 3 = 0 → mat5 a b c d e = 0 := by
  decide +kernel

/-- the five-dimensional space spanned by the matrices `mat5` -/
def L5 : (Fin 5 → ZMod 3) →ₗ[ZMod 3] M3 where
  toFun v := mat5 (v 0) (v 1) (v 2) (v 3) (v 4)
  map_add' v w := by
    ext i j; fin_cases i <;> fin_cases j <;> (simp [mat5]; try ring)
  map_smul' c v := by
    ext i j; fin_cases i <;> fin_cases j <;> (simp [mat5]; try ring)

theorem L5_injective : Function.Injective L5 := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  have h00 := congrFun (congrFun hv 0) 0
  have h02 := congrFun (congrFun hv 0) 2
  have h12 := congrFun (congrFun hv 1) 2
  have h21 := congrFun (congrFun hv 2) 1
  have h22 := congrFun (congrFun hv 2) 2
  simp [L5, mat5] at h00 h02 h12 h21 h22
  ext k; fin_cases k <;> simp [h00, h02, h12, h21, h22]

/-- a five-dimensional subspace of `M₃(𝔽₃)` with no nonzero nilpotent element -/
theorem exists_nilFree_five : ∃ W : Submodule (ZMod 3) M3,
    finrank (ZMod 3) W = 5 ∧ ∀ X ∈ W, IsNilpotent X → X = 0 := by
  refine ⟨LinearMap.range L5, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj L5_injective]; simp
  · rintro X ⟨v, rfl⟩ hX
    exact mat5_nilFree _ _ _ _ _ (pow_three_of_isNilpotent hX)

/-- the largest dimension of a subspace of `M₃(𝔽₃)` without nonzero nilpotent elements is 5,
whereas Conjecture 8 asks for 6 -/
theorem isGreatest_nilFree_finrank :
    IsGreatest {d : ℕ | ∃ W : Submodule (ZMod 3) M3,
      finrank (ZMod 3) W = d ∧ ∀ X ∈ W, IsNilpotent X → X = 0} 5 := by
  refine ⟨exists_nilFree_five, ?_⟩
  rintro d ⟨W, rfl, hW⟩
  by_contra hlt
  obtain ⟨X, hX, hne, hnil⟩ := exists_nilpotent W (by omega)
  exact hne (hW X hX hnil)

end NilFree
