import NilCore.Search

/-!
# Soundness of the search tree

If `root () = true` and every candidate passes `suppB`, then for every coefficient matrix `C` some
nonzero `y` makes `mk C y` nilpotent (`nilB C y = true`). The argument: a witness found at a node
uses only the columns of `C` fixed at that node, so it serves every completion of them; a node
without a witness has a child for each of the 27 possible next columns.
-/

namespace NilCore

/-- column `j` is among the first `d` in the order `ord` -/
def Fixed (d : Nat) (j : Fin 6) : Prop := ∃ k, k < d ∧ ord k = j

theorem fixedB_iff (d : Nat) (j : Fin 6) : fixedB d j = true ↔ Fixed d j := by
  simp [fixedB, Fixed, List.any_eq_true, List.mem_range]

theorem suppB_spec {d : Nat} {y : Vec} (h : suppB d y = true) :
    (∀ j, y j = 0 ∨ Fixed d j) ∧ ∃ j, y j ≠ 0 := by
  simp only [suppB, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.mem_finRange,
    true_and, forall_const, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨h1, j, hj⟩ := h
  refine ⟨fun j => ?_, j, hj⟩
  rcases h1 j with h | h
  · exact Or.inl h
  · exact Or.inr ((fixedB_iff d j).1 h)

/-- `C'` agrees with `C` on the first `d` columns -/
def Agree (d : Nat) (C C' : Coef) : Prop := ∀ j, Fixed d j → ∀ r, C' r j = C r j

theorem mul_zero3 : ∀ a : Fin 3, a * 0 = 0 := by decide

theorem u_congr {d : Nat} {C C' : Coef} {y : Vec} (hs : ∀ j, y j = 0 ∨ Fixed d j)
    (ha : Agree d C C') (r : Fin 3) : u C' y r = u C y r := by
  have h : ∀ j, C' r j * y j = C r j * y j := by
    intro j
    rcases hs j with h | h
    · rw [h, mul_zero3, mul_zero3]
    · rw [ha j h r]
  simp only [u, h]

theorem nilB_congr {d : Nat} {C C' : Coef} {y : Vec} (hs : ∀ j, y j = 0 ∨ Fixed d j)
    (ha : Agree d C C') : nilB C' y = nilB C y := by
  simp only [nilB, u_congr hs ha]

theorem wit_sound {C C' : Coef} {d : Nat} (hc : checkCands () = true) (hd : d < 7)
    (hw : wit C d = true) (ha : Agree d C C') :
    ∃ y : Vec, (∃ j, y j ≠ 0) ∧ nilB C' y = true := by
  simp only [wit, List.any_eq_true] at hw
  obtain ⟨a, hmem, hn⟩ := hw
  have hs : suppB d (ofArr a) = true := by
    simp only [checkCands, List.all_eq_true, List.mem_range] at hc
    exact hc d hd a hmem
  obtain ⟨hsupp, hne⟩ := suppB_spec hs
  exact ⟨ofArr a, hne, by rw [nilB_congr hsupp ha]; exact hn⟩

theorem mem_cols : ∀ a b c : Fin 3, (a, b, c) ∈ cols := by decide

theorem agree_setCol {d : Nat} {C C' : Coef} (ha : Agree d C C') :
    Agree (d + 1) (setCol C (ord d) (C' 0 (ord d), C' 1 (ord d), C' 2 (ord d))) C' := by
  intro j ⟨k, hk, hkj⟩ r
  by_cases hj : j = ord d
  · subst hj
    simp only [setCol, ite_true]
    rcases r with ⟨r, hr⟩
    match r, hr with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
  · have hk' : k < d := by
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h | h
      · exact h
      · subst h; exact absurd hkj.symm hj
    simp only [setCol, hj, ite_false]
    exact ha j ⟨k, hk', hkj⟩ r

theorem tree_sound (hc : checkCands () = true) :
    ∀ (f d : Nat) (C : Coef), d + f ≤ 6 → tree f d C = true →
      ∀ C', Agree d C C' → ∃ y : Vec, (∃ j, y j ≠ 0) ∧ nilB C' y = true
  | 0, d, C, hdf, ht, C', ha => wit_sound hc (by omega) ht ha
  | f + 1, d, C, hdf, ht, C', ha => by
    simp only [tree, Bool.or_eq_true, List.all_eq_true] at ht
    rcases ht with hw | hall
    · exact wit_sound hc (by omega) hw ha
    · exact tree_sound hc f (d + 1) _ (by omega) (hall _ (mem_cols _ _ _)) C' (agree_setCol ha)

/-- the search tree and the candidate check imply the statement for every `C` -/
theorem core (hr : root () = true) (hc : checkCands () = true) (C : Coef) :
    ∃ y : Vec, (∃ j, y j ≠ 0) ∧ nilB C y = true :=
  tree_sound hc 6 0 _ (by omega) hr C (fun _ ⟨k, hk, _⟩ => absurd hk (Nat.not_lt_zero k))

end NilCore
