import Mathlib

/-!
# Nilpotent `3 × 3` matrices in characteristic three (Section 4 of the paper)

Over a field of characteristic three the identity has trace zero. For trace-zero `X`,
`c₂(X + aI) = c₂(X)` and `det(X + aI) = det X + a³ + a c₂(X)` (`c2_add_smul_one`,
`det_add_smul_one'`), so over a finite field every trace-zero `X` with `c₂(X) = 0` has exactly one
nilpotent translate `X + aI` (`existsUnique_nilpotent_translate`). With the Chevalley–Warning
theorem this gives `exists_nilpotent_of_one_mem` (Proposition 4.4) and `one_not_mem_of_nilFree`.
-/

open Matrix Module

namespace NilFree

variable {K : Type*} [Field K]

/-- the sum of the principal `2 × 2` minors -/
def c2 (X : Matrix (Fin 3) (Fin 3) K) : K :=
  X 0 0 * X 1 1 - X 0 1 * X 1 0 + (X 0 0 * X 2 2 - X 0 2 * X 2 0) + (X 1 1 * X 2 2 - X 1 2 * X 2 1)

/-- Cayley–Hamilton for `3 × 3` matrices, written out -/
theorem cayley_hamilton (X : Matrix (Fin 3) (Fin 3) K) :
    X ^ 3 - trace X • X ^ 2 + c2 X • X - det X • (1 : Matrix (Fin 3) (Fin 3) K) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [c2, pow_succ, Matrix.mul_apply, Fin.sum_univ_three, Matrix.det_fin_three,
      Matrix.trace_fin_three] <;> ring

theorem pow_three_of_invariants {X : Matrix (Fin 3) (Fin 3) K} (ht : trace X = 0) (hc : c2 X = 0)
    (hd : det X = 0) : X ^ 3 = 0 := by
  have h := cayley_hamilton X
  rw [ht, hc, hd] at h
  simpa using h

theorem two_mul_c2 (X : Matrix (Fin 3) (Fin 3) K) : 2 * c2 X = trace X ^ 2 - trace (X ^ 2) := by
  simp [c2, pow_two, Matrix.trace_fin_three, Matrix.mul_apply, Fin.sum_univ_three]; ring

theorem det_add_smul_one (X : Matrix (Fin 3) (Fin 3) K) (a : K) :
    det (X + a • (1 : Matrix (Fin 3) (Fin 3) K)) = det X + a * c2 X + a ^ 2 * trace X + a ^ 3 := by
  simp [c2, Matrix.det_fin_three, Matrix.trace_fin_three]; ring

section char3

variable [CharP K 3]

theorem three_eq_zero : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3

theorem trace_one_three : trace (1 : Matrix (Fin 3) (Fin 3) K) = 0 := by
  simp [Matrix.trace_one]; exact three_eq_zero

/-- Lemma 4.2: on trace-zero matrices `c₂(X) = tr(X²)` -/
theorem c2_eq_trace_sq {X : Matrix (Fin 3) (Fin 3) K} (ht : trace X = 0) : c2 X = trace (X ^ 2) := by
  have h := two_mul_c2 X
  rw [ht] at h
  linear_combination (-1 : K) * h + c2 X * three_eq_zero (K := K)

omit [CharP K 3] in
/-- Lemma 4.2: a matrix orthogonal to all trace-zero matrices under the trace form is scalar -/
theorem eq_smul_one_of_trace_mul (X : Matrix (Fin 3) (Fin 3) K)
    (hX : ∀ Y : Matrix (Fin 3) (Fin 3) K, trace Y = 0 → trace (X * Y) = 0) :
    X = X 0 0 • (1 : Matrix (Fin 3) (Fin 3) K) := by
  have e : ∀ i j : Fin 3, i ≠ j → X j i = 0 := by
    intro i j hij
    have := hX (Matrix.single i j 1) (by simp [Matrix.trace, hij])
    fin_cases i <;> fin_cases j <;>
      simp_all [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_three]
  have d1 := hX (Matrix.diagonal ![1, -1, 0]) (by simp [Fin.sum_univ_three])
  have d2 := hX (Matrix.diagonal ![0, 1, -1]) (by simp [Fin.sum_univ_three])
  simp [Matrix.trace, Fin.sum_univ_three] at d1 d2
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;>
    first
    | exact e _ _ (by decide)
    | linear_combination -d1
    | linear_combination -d1 - d2

/-- Lemma 4.1 -/
theorem c2_add_smul_one {X : Matrix (Fin 3) (Fin 3) K} (ht : trace X = 0) (a : K) :
    c2 (X + a • (1 : Matrix (Fin 3) (Fin 3) K)) = c2 X := by
  have h3 := three_eq_zero (K := K)
  have ht' : X 0 0 + X 1 1 + X 2 2 = 0 := by simpa [Matrix.trace_fin_three] using ht
  simp [c2]
  linear_combination (2 * a) * ht' + a ^ 2 * h3

omit [CharP K 3] in
theorem det_add_smul_one' {X : Matrix (Fin 3) (Fin 3) K} (ht : trace X = 0) (a : K) :
    det (X + a • (1 : Matrix (Fin 3) (Fin 3) K)) = det X + a ^ 3 + a * c2 X := by
  rw [det_add_smul_one, ht]; ring

/-- in characteristic three a nilpotent `3 × 3` matrix has trace and `c₂` zero -/
theorem trace_c2_of_isNilpotent {X : Matrix (Fin 3) (Fin 3) K} (h : IsNilpotent X) :
    trace X = 0 ∧ c2 X = 0 := by
  have ht : trace X = 0 := (Matrix.isNilpotent_trace_of_isNilpotent h).eq_zero
  have h2 : IsNilpotent (X ^ 2) := h.pow_succ 1
  have ht2 : trace (X ^ 2) = 0 := (Matrix.isNilpotent_trace_of_isNilpotent h2).eq_zero
  refine ⟨ht, ?_⟩
  have h := two_mul_c2 X
  rw [ht, ht2] at h
  have h2ne : (2 : K) ≠ 0 := by
    intro h2
    have : (1 : K) = 0 := by linear_combination three_eq_zero (K := K) - h2
    exact one_ne_zero this
  have : 2 * c2 X = 0 := by simpa using h
  exact (mul_eq_zero.mp this).resolve_left h2ne

theorem cube_injective : Function.Injective (fun a : K => a ^ 3) := by
  intro a b hab
  have : (a - b) ^ 3 = 0 := by
    rw [sub_pow_char (p := 3) a b]; simpa [sub_eq_zero] using hab
  exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp this)

/-- Proposition 4.3: a trace-zero matrix with `c₂ = 0` has exactly one nilpotent translate by a
scalar matrix -/
theorem existsUnique_nilpotent_translate [Finite K] {X : Matrix (Fin 3) (Fin 3) K}
    (ht : trace X = 0) (hc : c2 X = 0) :
    ∃! a : K, IsNilpotent (X + a • (1 : Matrix (Fin 3) (Fin 3) K)) := by
  have hsurj : Function.Surjective (fun a : K => a ^ 3) :=
    Finite.injective_iff_surjective.mp cube_injective
  have key : ∀ a : K, IsNilpotent (X + a • (1 : Matrix (Fin 3) (Fin 3) K)) ↔ a ^ 3 = -det X := by
    intro a
    have htA : trace (X + a • (1 : Matrix (Fin 3) (Fin 3) K)) = 0 := by
      rw [trace_add, trace_smul, trace_one_three, ht]; simp
    have hcA : c2 (X + a • (1 : Matrix (Fin 3) (Fin 3) K)) = 0 := by
      rw [c2_add_smul_one ht, hc]
    have hdA := det_add_smul_one' ht a
    rw [hc, mul_zero, add_zero] at hdA
    constructor
    · intro hn
      have h3 : (X + a • (1 : Matrix (Fin 3) (Fin 3) K)) ^ 3 = 0 := by
        obtain ⟨k, hk⟩ := hn
        have := pow_three_of_invariants htA hcA ?_
        · exact this
        · have hdet : det ((X + a • (1 : Matrix (Fin 3) (Fin 3) K)) ^ k) = 0 := by rw [hk]; simp
          rw [det_pow] at hdet
          exact IsNilpotent.eq_zero ⟨k, hdet⟩
      have hdet : det (X + a • (1 : Matrix (Fin 3) (Fin 3) K)) = 0 := by
        have := congrArg det h3; rw [det_pow] at this; simpa using this
      rw [hdA] at hdet; linear_combination hdet
    · intro ha
      refine ⟨3, pow_three_of_invariants htA hcA ?_⟩
      rw [hdA, ha]; ring
  obtain ⟨a, ha⟩ := hsurj (-det X)
  have ha' : a ^ 3 = -det X := ha
  refine ⟨a, (key a).mpr ha', fun b hb => cube_injective ?_⟩
  show b ^ 3 = a ^ 3
  rw [(key b).mp hb, ha']


/-- the bilinear form with `c2 X = m X X` -/
def m (A B : Matrix (Fin 3) (Fin 3) K) : K :=
  A 0 0 * B 1 1 - A 0 1 * B 1 0 + (A 0 0 * B 2 2 - A 0 2 * B 2 0) + (A 1 1 * B 2 2 - A 1 2 * B 2 1)

omit [CharP K 3] in
theorem c2_sum (Y : Fin 3 → Matrix (Fin 3) (Fin 3) K) (t : Fin 3 → K) :
    c2 (∑ i, t i • Y i) = ∑ i, ∑ j, t i * t j * m (Y i) (Y j) := by
  simp [c2, m, Fin.sum_univ_three]; ring

omit [CharP K 3] in
/-- Chevalley–Warning: `c₂` restricted to the span of three matrices has a nonzero zero -/
theorem exists_ne_zero_c2 [Fintype K] (p : ℕ) [CharP K p] (Y : Fin 3 → Matrix (Fin 3) (Fin 3) K) :
    ∃ t : Fin 3 → K, t ≠ 0 ∧ c2 (∑ i, t i • Y i) = 0 := by
  classical
  let f : MvPolynomial (Fin 3) K :=
    ∑ i, ∑ j, MvPolynomial.C (m (Y i) (Y j)) * MvPolynomial.X i * MvPolynomial.X j
  have hterm : ∀ i j, (MvPolynomial.C (m (Y i) (Y j)) * MvPolynomial.X i * MvPolynomial.X j :
      MvPolynomial (Fin 3) K).totalDegree ≤ 2 := by
    intro i j
    calc _ ≤ (MvPolynomial.C (m (Y i) (Y j)) * MvPolynomial.X i : MvPolynomial (Fin 3) K).totalDegree
            + (MvPolynomial.X j : MvPolynomial (Fin 3) K).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
      _ ≤ ((MvPolynomial.C (m (Y i) (Y j)) : MvPolynomial (Fin 3) K).totalDegree
            + (MvPolynomial.X i : MvPolynomial (Fin 3) K).totalDegree)
            + (MvPolynomial.X j : MvPolynomial (Fin 3) K).totalDegree := by
          gcongr; exact MvPolynomial.totalDegree_mul _ _
      _ = 2 := by simp [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
  have hdeg : f.totalDegree < Fintype.card (Fin 3) := by
    have : f.totalDegree ≤ 2 := by
      refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ => ?_)
      exact (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => hterm i j)
    simp only [Fintype.card_fin]; omega
  have heval : ∀ x : Fin 3 → K, MvPolynomial.eval x f = c2 (∑ i, x i • Y i) := by
    intro x; rw [c2_sum]
    simp only [f, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hdvd := char_dvd_card_solutions p hdeg
  by_contra hne
  have hall : ∀ t : Fin 3 → K, c2 (∑ i, t i • Y i) = 0 → t = 0 := by
    intro t ht
    by_contra h0
    exact hne ⟨t, h0, ht⟩
  have hcard : Fintype.card {x : Fin 3 → K // MvPolynomial.eval x f = 0} = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨0, by rw [heval]; simp [c2]⟩, ?_⟩
    rintro ⟨x, hx⟩
    apply Subtype.ext
    exact hall x (by rw [← heval]; exact hx)
  rw [hcard] at hdvd
  exact CharP.char_ne_one K p (Nat.dvd_one.mp hdvd)

/-- Proposition 4.4: a space of trace-zero matrices of dimension at least four that contains the
identity contains a nonzero nilpotent matrix -/
theorem exists_nilpotent_of_one_mem [Fintype K] (U : Submodule K (Matrix (Fin 3) (Fin 3) K))
    (hI : (1 : Matrix (Fin 3) (Fin 3) K) ∈ U) (htr : ∀ X ∈ U, trace X = 0)
    (hdim : 4 ≤ finrank K U) : ∃ X ∈ U, X ≠ 0 ∧ IsNilpotent X := by
  classical
  set P : Submodule K U := K ∙ (⟨1, hI⟩ : U) with hPdef
  have hP : finrank K P ≤ 1 := by
    have := finrank_span_le_card (R := K) ({(⟨1, hI⟩ : U)} : Set U)
    simpa using this
  have hq : 3 ≤ finrank K (U ⧸ P) := by
    have := Submodule.finrank_quotient_add_finrank P; omega
  let b := Module.finBasis K (U ⧸ P)
  let e : Fin 3 → Fin (finrank K (U ⧸ P)) := Fin.castLE hq
  let y : Fin 3 → U := fun i => (Submodule.mkQ_surjective P (b (e i))).choose
  have hy : ∀ i, P.mkQ (y i) = b (e i) := fun i => (Submodule.mkQ_surjective P (b (e i))).choose_spec
  let Y : Fin 3 → Matrix (Fin 3) (Fin 3) K := fun i => (y i : Matrix (Fin 3) (Fin 3) K)
  obtain ⟨t, ht0, htc⟩ := exists_ne_zero_c2 3 Y
  set X := ∑ i, t i • Y i with hXdef
  have hXU : X ∈ U := U.sum_mem fun i _ => U.smul_mem _ (y i).2
  have hXy : (⟨X, hXU⟩ : U) = ∑ i, t i • y i := by
    apply Subtype.ext; simp [X, Y]
  have hnot : ∀ s : K, X ≠ s • (1 : Matrix (Fin 3) (Fin 3) K) := by
    intro s hs
    have h1 : (∑ i, t i • y i : U) = s • (⟨1, hI⟩ : U) := by
      rw [← hXy]; apply Subtype.ext; simp [hs]
    have h2 : ∑ i, t i • b (e i) = 0 := by
      have := congrArg P.mkQ h1
      simp only [map_sum, map_smul, hy] at this
      rw [this]
      have hmem : (⟨1, hI⟩ : U) ∈ P := Submodule.mem_span_singleton_self _
      simp [(Submodule.Quotient.mk_eq_zero P).mpr hmem]
    have hli : LinearIndependent K (b ∘ e) :=
      b.linearIndependent.comp e (Fin.castLE_injective hq)
    have := Fintype.linearIndependent_iff.mp hli t (by simpa using h2)
    exact ht0 (funext this)
  have htX : trace X = 0 := htr X hXU
  obtain ⟨a, ha, -⟩ := existsUnique_nilpotent_translate htX htc
  refine ⟨X + a • 1, U.add_mem hXU (U.smul_mem a hI), ?_, ha⟩
  intro h0
  apply hnot (-a)
  rw [neg_smul, eq_neg_iff_add_eq_zero]; exact h0

/-- the trace-zero matrices -/
abbrev sl3 (K : Type*) [Field K] : Submodule K (Matrix (Fin 3) (Fin 3) K) :=
  LinearMap.ker (Matrix.traceLinearMap (Fin 3) K K)

omit [CharP K 3] in
theorem finrank_sl3 : finrank K (sl3 K) = 8 := by
  show finrank K (LinearMap.ker (Matrix.traceLinearMap (Fin 3) K K)) = 8
  have hsurj : Function.Surjective (Matrix.traceLinearMap (Fin 3) K K) := fun r =>
    ⟨Matrix.diagonal ![r, 0, 0], by simp [Fin.sum_univ_three]⟩
  have h := LinearMap.finrank_range_add_finrank_ker (Matrix.traceLinearMap (Fin 3) K K)
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self,
    Module.finrank_matrix] at h
  simp at h
  omega

/-- Corollary: in characteristic three a nilpotent-free subspace of `M₃` of dimension at least five
does not contain the identity -/
theorem one_not_mem_of_nilFree [Fintype K] (W : Submodule K (Matrix (Fin 3) (Fin 3) K))
    (hW : ∀ X ∈ W, IsNilpotent X → X = 0) (hdim : 5 ≤ finrank K W) :
    (1 : Matrix (Fin 3) (Fin 3) K) ∉ W := by
  intro hI
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq W (sl3 K)
  have hle : finrank K ↥(W ⊔ sl3 K) ≤ 9 := by
    have := Submodule.finrank_le (W ⊔ sl3 K)
    simpa [Module.finrank_matrix] using this
  rw [finrank_sl3] at hsum
  obtain ⟨X, hXU, hX0, hXn⟩ := exists_nilpotent_of_one_mem (W ⊓ sl3 K)
    ⟨hI, by simpa using trace_one_three (K := K)⟩ (fun X hX => by simpa using hX.2) (by omega)
  exact hX0 (hW X hXU.1 hXn)

end char3

end NilFree
