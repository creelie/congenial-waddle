import Mathlib

/-!
# Where Conjecture 8 holds

`HoldsAt F n` is the statement of Conjecture 8 of arXiv:2609.29177 for one field and one size: there
is a subspace of `n × n` matrices over `F` of dimension `n² - C(n,2)` without nonzero nilpotent
elements. It holds for `n ≤ 2` over every finite field (`holdsAt_le_two`) and for `n = 3` over `𝔽₂`
and `𝔽₅` (`holdsAt_zmod2`, `holdsAt_zmod5`); over `𝔽₃` it fails for `n = 3` (`NilFree.Main`).
-/

open Matrix Module

namespace NilFree

/-- Conjecture 8 of arXiv:2609.29177 for the field `F` and the size `n` -/
def HoldsAt (F : Type) [Field F] (n : ℕ) : Prop :=
  ∃ W : Submodule F (Matrix (Fin n) (Fin n) F),
    finrank F W = n ^ 2 - n.choose 2 ∧ ∀ X ∈ W, IsNilpotent X → X = 0

variable {K : Type*} [Field K]

/-- a nilpotent `n × n` matrix over a field has `X ^ n = 0` (Cayley–Hamilton) -/
theorem pow_eq_zero_of_isNilpotent {n : ℕ} {X : Matrix (Fin n) (Fin n) K} (h : IsNilpotent X) :
    X ^ n = 0 := by
  have h1 := Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent h
  have h2 : X.charpoly = Polynomial.X ^ n := by
    have := h1.eq_zero
    simpa [Fintype.card_fin, sub_eq_zero] using this
  have := Matrix.aeval_self_charpoly X
  rw [h2] at this
  simpa using this

/-! ### `n ≤ 2` -/

/-- over a finite field some `t² + t + c` has no root: `t ↦ t² + t` identifies `0` and `-1`, so it
is not injective, hence not surjective -/
theorem exists_no_root [Finite K] : ∃ c : K, ∀ t : K, t ^ 2 + t + c ≠ 0 := by
  have hni : ¬ Function.Injective (fun t : K => t ^ 2 + t) := by
    intro hinj
    have h := @hinj 0 (-1) (by ring)
    have h1 : (1 : K) = 0 := by linear_combination h
    exact one_ne_zero h1
  have hns : ¬ Function.Surjective (fun t : K => t ^ 2 + t) := fun hs =>
    hni (Finite.injective_iff_surjective.mpr hs)
  simp only [Function.Surjective, not_forall, not_exists] at hns
  obtain ⟨e, he⟩ := hns
  refine ⟨-e, fun t ht => he t ?_⟩
  show t ^ 2 + t = e
  linear_combination ht

/-- the linear form `X ↦ tr(J M X)` with `J = [[0, -1], [1, 0]]` and `M = [[1, 1], [0, c]]` -/
def phi (c : K) : Matrix (Fin 2) (Fin 2) K →ₗ[K] K where
  toFun X := X 0 1 + X 1 1 - c * X 1 0
  map_add' X Y := by simp; ring
  map_smul' a X := by simp; ring

theorem eq_zero_of_sq (c : K) (hc : ∀ t : K, t ^ 2 + t + c ≠ 0) (a b x d : K)
    (h00 : a * a + b * x = 0) (h10 : x * a + d * x = 0) (h11 : x * b + d * d = 0)
    (hφ : b + d - c * x = 0) : a = 0 ∧ b = 0 ∧ x = 0 ∧ d = 0 := by
  by_cases hx : x = 0
  · subst hx
    have ha : a = 0 := by simpa using h00
    have hd : d = 0 := by simpa using h11
    subst ha; subst hd
    exact ⟨rfl, by simpa using hφ, rfl, rfl⟩
  · exfalso
    have hd : d = -a := by
      have : x * (a + d) = 0 := by linear_combination h10
      have := (mul_eq_zero.mp this).resolve_left hx
      linear_combination this
    have hb : b = c * x + a := by linear_combination hφ - hd
    apply hc (a / x)
    field_simp
    rw [hb] at h00
    linear_combination h00

/-- Proposition 5.1 for `n = 2`: the kernel of `phi c` is a nilpotent-free space of dimension 3 -/
theorem exists_nilFree_two [Finite K] : ∃ W : Submodule K (Matrix (Fin 2) (Fin 2) K),
    finrank K W = 3 ∧ ∀ X ∈ W, IsNilpotent X → X = 0 := by
  obtain ⟨c, hc⟩ := exists_no_root (K := K)
  refine ⟨LinearMap.ker (phi c), ?_, ?_⟩
  · have hsurj : Function.Surjective (phi c) := fun r =>
      ⟨Matrix.of ![![0, r], ![0, 0]], by simp [phi]⟩
    have h := LinearMap.finrank_range_add_finrank_ker (phi c)
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self,
      Module.finrank_matrix] at h
    simp at h
    omega
  · intro X hX hnil
    have h2 : X ^ 2 = 0 := pow_eq_zero_of_isNilpotent hnil
    have h00 := congrFun (congrFun h2 0) 0
    have h10 := congrFun (congrFun h2 1) 0
    have h11 := congrFun (congrFun h2 1) 1
    simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two] at h00 h10 h11
    have hφ : X 0 1 + X 1 1 - c * X 1 0 = 0 := hX
    obtain ⟨ha, hb, hx, hd⟩ := eq_zero_of_sq c hc (X 0 0) (X 0 1) (X 1 0) (X 1 1) h00 h10 h11 hφ
    ext i j; fin_cases i <;> fin_cases j <;> simp [ha, hb, hx, hd]

/-- Proposition 5.1: Conjecture 8 holds for `n ≤ 2` over every finite field -/
theorem holdsAt_le_two (F : Type) [Field F] [Finite F] {n : ℕ} (hn : n ≤ 2) : HoldsAt F n := by
  interval_cases n
  · refine ⟨⊥, by simp, fun X _ _ => Subsingleton.elim _ _⟩
  · refine ⟨⊤, by simp [Module.finrank_matrix], fun X _ hX => ?_⟩
    simpa using pow_eq_zero_of_isNilpotent hX
  · obtain ⟨W, hW, hnil⟩ := exists_nilFree_two (K := F)
    exact ⟨W, by rw [hW]; decide, hnil⟩

/-! ### `n = 3` over `𝔽₂` and `𝔽₅` -/

/-- `(C y)_r` -/
def cy (C : Fin 3 → Fin 6 → K) (y : Fin 6 → K) (r : Fin 3) : K :=
  C r 0 * y 0 + C r 1 * y 1 + C r 2 * y 2 + C r 3 * y 3 + C r 4 * y 4 + C r 5 * y 5

/-- the matrix `X_C(y)`: entries `y` at `(1,1), (2,2), (3,3), (2,1), (3,1), (3,2)` and `-(C y)` at
`(1,2), (1,3), (2,3)` -/
def graphMap (C : Fin 3 → Fin 6 → K) : (Fin 6 → K) →ₗ[K] Matrix (Fin 3) (Fin 3) K where
  toFun y := !![y 0, -cy C y 0, -cy C y 1; y 3, y 1, -cy C y 2; y 4, y 5, y 2]
  map_add' y y' := by
    ext i k; fin_cases i <;> fin_cases k <;> (simp [cy]; try ring)
  map_smul' c y := by
    ext i k; fin_cases i <;> fin_cases k <;> (simp [cy]; try ring)

theorem graphMap_injective (C : Fin 3 → Fin 6 → K) : Function.Injective (graphMap C) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  have h00 := congrFun (congrFun hy 0) 0
  have h11 := congrFun (congrFun hy 1) 1
  have h22 := congrFun (congrFun hy 2) 2
  have h10 := congrFun (congrFun hy 1) 0
  have h20 := congrFun (congrFun hy 2) 0
  have h21 := congrFun (congrFun hy 2) 1
  simp [graphMap] at h00 h11 h22 h10 h20 h21
  ext k; fin_cases k <;> simp [h00, h11, h22, h10, h20, h21]

/-- if no nonzero `X_C(y)` has vanishing cube, the space of all `X_C(y)` witnesses `HoldsAt F 3` -/
theorem holdsAt_three_of_graph (F : Type) [Field F] (C : Fin 3 → Fin 6 → F)
    (h : ∀ y, graphMap C y ^ 3 = 0 → y = 0) : HoldsAt F 3 := by
  refine ⟨LinearMap.range (graphMap C), ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj (graphMap_injective C)]; simp
  · rintro X ⟨y, rfl⟩ hX
    rw [h y (pow_eq_zero_of_isNilpotent hX), map_zero]

/-- `X³ = 0` for the matrix with rows `(a, b, c)`, `(d, e, f)`, `(g, h, i)`, written out -/
def cubeZeroK [DecidableEq K] (a b c d e f g h i : K) : Bool :=
  let p₀₀ := a*a + b*d + c*g; let p₀₁ := a*b + b*e + c*h; let p₀₂ := a*c + b*f + c*i
  let p₁₀ := d*a + e*d + f*g; let p₁₁ := d*b + e*e + f*h; let p₁₂ := d*c + e*f + f*i
  let p₂₀ := g*a + h*d + i*g; let p₂₁ := g*b + h*e + i*h; let p₂₂ := g*c + h*f + i*i
  p₀₀*a + p₀₁*d + p₀₂*g == 0 && p₀₀*b + p₀₁*e + p₀₂*h == 0 && p₀₀*c + p₀₁*f + p₀₂*i == 0 &&
  p₁₀*a + p₁₁*d + p₁₂*g == 0 && p₁₀*b + p₁₁*e + p₁₂*h == 0 && p₁₀*c + p₁₁*f + p₁₂*i == 0 &&
  p₂₀*a + p₂₁*d + p₂₂*g == 0 && p₂₀*b + p₂₁*e + p₂₂*h == 0 && p₂₀*c + p₂₁*f + p₂₂*i == 0

theorem cubeZeroK_of_cube [DecidableEq K] (a b c d e f g h i : K)
    (hX : (!![a, b, c; d, e, f; g, h, i] : Matrix (Fin 3) (Fin 3) K) ^ 3 = 0) :
    cubeZeroK a b c d e f g h i = true := by
  have e : ∀ r s, ((!![a, b, c; d, e, f; g, h, i] : Matrix (Fin 3) (Fin 3) K) ^ 3) r s = 0 :=
    fun r s => by rw [hX]; rfl
  have e00 := e 0 0; have e01 := e 0 1; have e02 := e 0 2
  have e10 := e 1 0; have e11 := e 1 1; have e12 := e 1 2
  have e20 := e 2 0; have e21 := e 2 1; have e22 := e 2 2
  simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three] at e00 e01 e02 e10 e11 e12 e20 e21 e22
  simp only [cubeZeroK, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · linear_combination e00
  · linear_combination e01
  · linear_combination e02
  · linear_combination e10
  · linear_combination e11
  · linear_combination e12
  · linear_combination e20
  · linear_combination e21
  · linear_combination e22

/-- Example 5.2: upper entries `b + d + e`, `a + e + f`, `b + f` -/
def C2 : Fin 3 → Fin 6 → ZMod 2 := ![![0, 1, 0, 1, 1, 0], ![1, 0, 0, 0, 1, 1], ![0, 1, 0, 0, 0, 1]]

/-- the test for one vector `(a, b, c, d, e, f)` over `𝔽₂`: zero, or `X_C(y)³ ≠ 0` -/
def ok2 (a b c d e f : ZMod 2) : Bool :=
  (a == 0 && b == 0 && c == 0 && d == 0 && e == 0 && f == 0) ||
  !cubeZeroK a (-(b + d + e)) (-(a + e + f)) d b (-(b + f)) e f c

/-- the test for all `2⁶` vectors -/
def check2 : Bool :=
  (List.finRange 2).all fun a => (List.finRange 2).all fun b => (List.finRange 2).all fun c =>
  (List.finRange 2).all fun d => (List.finRange 2).all fun e => (List.finRange 2).all fun f =>
  ok2 a b c d e f

/-- checked by the kernel -/
theorem check2_eq : check2 = true := by decide +kernel

theorem nilFree_C2 : ∀ y, graphMap C2 y ^ 3 = 0 → y = 0 := by
  intro y hy
  have h := check2_eq
  simp only [check2, List.all_eq_true, List.mem_finRange, forall_const] at h
  have hok := h (y 0) (y 1) (y 2) (y 3) (y 4) (y 5)
  have hc0 : cy C2 y 0 = y 1 + y 3 + y 4 := by simp [cy, C2]
  have hc1 : cy C2 y 1 = y 0 + y 4 + y 5 := by simp [cy, C2]
  have hc2 : cy C2 y 2 = y 1 + y 5 := by simp [cy, C2]
  have hX : (!![y 0, -cy C2 y 0, -cy C2 y 1; y 3, y 1, -cy C2 y 2; y 4, y 5, y 2] :
      Matrix (Fin 3) (Fin 3) (ZMod 2)) ^ 3 = 0 := hy
  have hz := cubeZeroK_of_cube _ _ _ _ _ _ _ _ _ hX
  rw [hc0, hc1, hc2] at hz
  simp only [ok2, hz, Bool.not_true, Bool.or_false, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := hok
  ext k; fin_cases k <;> simp [h0, h1, h2, h3, h4, h5]

theorem holdsAt_zmod2 : HoldsAt (ZMod 2) 3 := holdsAt_three_of_graph _ C2 nilFree_C2

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- Example 5.3: upper entries `3a + 4b + d + 2e + 2f`, `3a + 3b + 3e + 3f`, `a + 4b + c + 3d + 3f` -/
def C5 : Fin 3 → Fin 6 → ZMod 5 := ![![2, 1, 0, 4, 3, 3], ![2, 2, 0, 0, 2, 2], ![4, 1, 4, 2, 0, 2]]

/-- the test for one vector `(a, b, c, d, e, f)` over `𝔽₅`: zero, or `X_C(y)³ ≠ 0` -/
def ok5 (a b c d e f : ZMod 5) : Bool :=
  (a == 0 && b == 0 && c == 0 && d == 0 && e == 0 && f == 0) ||
  !cubeZeroK a (-(2*a + b + 4*d + 3*e + 3*f)) (-(2*a + 2*b + 2*e + 2*f))
    d b (-(4*a + b + 4*c + 2*d + 2*f)) e f c

/-- the test for all `5⁶` vectors -/
def check5 : Bool :=
  (List.finRange 5).all fun a => (List.finRange 5).all fun b => (List.finRange 5).all fun c =>
  (List.finRange 5).all fun d => (List.finRange 5).all fun e => (List.finRange 5).all fun f =>
  ok5 a b c d e f

/-- checked by the kernel -/
theorem check5_eq : check5 = true := by decide +kernel

theorem nilFree_C5 : ∀ y, graphMap C5 y ^ 3 = 0 → y = 0 := by
  intro y hy
  have h := check5_eq
  simp only [check5, List.all_eq_true, List.mem_finRange, forall_const] at h
  have hok := h (y 0) (y 1) (y 2) (y 3) (y 4) (y 5)
  have hc0 : cy C5 y 0 = 2 * y 0 + y 1 + 4 * y 3 + 3 * y 4 + 3 * y 5 := by
    simp [cy, C5]
  have hc1 : cy C5 y 1 = 2 * y 0 + 2 * y 1 + 2 * y 4 + 2 * y 5 := by
    simp [cy, C5]
  have hc2 : cy C5 y 2 = 4 * y 0 + y 1 + 4 * y 2 + 2 * y 3 + 2 * y 5 := by
    simp [cy, C5]
  have hX : (!![y 0, -cy C5 y 0, -cy C5 y 1; y 3, y 1, -cy C5 y 2; y 4, y 5, y 2] :
      Matrix (Fin 3) (Fin 3) (ZMod 5)) ^ 3 = 0 := hy
  have hz := cubeZeroK_of_cube _ _ _ _ _ _ _ _ _ hX
  rw [hc0, hc1, hc2] at hz
  simp only [ok5, hz, Bool.not_true, Bool.or_false, Bool.and_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := hok
  ext k; fin_cases k <;> simp [h0, h1, h2, h3, h4, h5]

theorem holdsAt_zmod5 : HoldsAt (ZMod 5) 3 := holdsAt_three_of_graph _ C5 nilFree_C5

end NilFree
