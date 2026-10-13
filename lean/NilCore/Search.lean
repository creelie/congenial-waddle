/-!
# The search behind the theorem on nilpotent-free spaces of 3 × 3 matrices over 𝔽₃

A space `W` of `3 × 3` matrices over `𝔽₃` that meets the strictly upper triangular matrices only in
`0` and has dimension 6 is the graph of a linear map: for every `y ∈ 𝔽₃⁶` (the entries at the six
positions `(1,1), (2,2), (3,3), (2,1), (3,1), (3,2)`) it contains exactly one matrix `mk C y` with
these entries, and its entries at `(1,2), (1,3), (2,3)` are `-(C y)` for a `3 × 6` matrix `C`.
This file defines that matrix, a test that its cube vanishes, and a search tree over `C` that
closes a node as soon as some `y`, supported on the columns of `C` fixed so far, gives a nilpotent
matrix.
-/

namespace NilCore

/-- a coefficient matrix `C`: `C r j` with `r` an upper position and `j` a free position -/
abbrev Coef := Fin 3 → Fin 6 → Fin 3
/-- the free coordinates of a matrix -/
abbrev Vec := Fin 6 → Fin 3

/-- `(C y)_r` -/
def u (C : Coef) (y : Vec) (r : Fin 3) : Fin 3 :=
  C r 0 * y 0 + C r 1 * y 1 + C r 2 * y 2 + C r 3 * y 3 + C r 4 * y 4 + C r 5 * y 5

/-- `X³ = 0` for the matrix with rows `(a, b, c)`, `(d, e, f)`, `(g, h, i)`, with the entries of `X²`
and `X³` written out -/
def cubeZero (a b c d e f g h i : Fin 3) : Bool :=
  let p₀₀ := a*a + b*d + c*g; let p₀₁ := a*b + b*e + c*h; let p₀₂ := a*c + b*f + c*i
  let p₁₀ := d*a + e*d + f*g; let p₁₁ := d*b + e*e + f*h; let p₁₂ := d*c + e*f + f*i
  let p₂₀ := g*a + h*d + i*g; let p₂₁ := g*b + h*e + i*h; let p₂₂ := g*c + h*f + i*i
  p₀₀*a + p₀₁*d + p₀₂*g == 0 && p₀₀*b + p₀₁*e + p₀₂*h == 0 && p₀₀*c + p₀₁*f + p₀₂*i == 0 &&
  p₁₀*a + p₁₁*d + p₁₂*g == 0 && p₁₀*b + p₁₁*e + p₁₂*h == 0 && p₁₀*c + p₁₁*f + p₁₂*i == 0 &&
  p₂₀*a + p₂₁*d + p₂₂*g == 0 && p₂₀*b + p₂₁*e + p₂₂*h == 0 && p₂₀*c + p₂₁*f + p₂₂*i == 0

/-- `X = mk C y` has rows `(y₀, -u₀, -u₁)`, `(y₃, y₁, -u₂)`, `(y₄, y₅, y₂)`; this tests `X³ = 0` -/
def nilB (C : Coef) (y : Vec) : Bool :=
  cubeZero (y 0) (-u C y 0) (-u C y 1) (y 3) (y 1) (-u C y 2) (y 4) (y 5) (y 2)

/-- the order in which the columns of `C` are fixed: `(2,1), (3,1), (3,2), (1,1), (2,2), (3,3)` -/
def ord (d : Nat) : Fin 6 :=
  match d with
  | 0 => 3 | 1 => 4 | 2 => 5 | 3 => 0 | 4 => 1 | _ => 2

/-- `j` is one of the first `d` columns in the order `ord` -/
def fixedB (d : Nat) (j : Fin 6) : Bool :=
  (List.range d).any fun k => ord k == j

/-- the vector with value `v k` at column `ord k` for `k < d` and `0` elsewhere -/
def vecOf (d : Nat) (v : Nat → Fin 3) : Vec := fun j =>
  match (List.range d).find? (fun k => ord k == j) with
  | some k => v k
  | none => 0

/-- candidate witnesses at depth `d`: coefficient `1` at the newest column, anything at the older
ones, fewest nonzero entries first (any list would do: `checkCands` checks every candidate) -/
def cands (d : Nat) : List Vec :=
  if d = 0 then [] else
  let tails : List (List (Fin 3)) := (List.range (d - 1)).foldl
    (fun acc _ => acc.flatMap fun t => [(0 : Fin 3) :: t, 1 :: t, 2 :: t]) [[]]
  let ys := tails.map fun t => vecOf d fun k => if k = d - 1 then 1 else t.getD k 0
  let weight (y : Vec) : Nat := ((List.finRange 6).filter fun j => y j != 0).length
  let sorted := (List.range 7).flatMap fun w => ys.filter fun y => weight y == w
  sorted

/-- the vector stored in an array -/
def ofArr (a : Array (Fin 3)) : Vec := fun j => a.getD j.val 0

/-- the candidate lists, stored as arrays and computed once -/
def candTable : Array (List (Array (Fin 3))) :=
  (List.range 7).toArray.map fun d => (cands d).map fun y => (List.finRange 6).toArray.map y

/-- `y` is supported on the first `d` columns and is nonzero -/
def suppB (d : Nat) (y : Vec) : Bool :=
  (List.finRange 6).all (fun j => y j == 0 || fixedB d j) && (List.finRange 6).any (fun j => y j != 0)

/-- every candidate at every depth is supported on the fixed columns and nonzero -/
def checkCands (_ : Unit) : Bool :=
  (List.range 7).all fun d => (candTable.getD d []).all fun a => suppB d (ofArr a)

/-- some candidate is a witness -/
def wit (C : Coef) (d : Nat) : Bool :=
  (candTable.getD d []).any fun a => nilB C (ofArr a)

/-- the 27 possible columns -/
def cols : List (Fin 3 × Fin 3 × Fin 3) :=
  [0, 1, 2].flatMap fun a => [0, 1, 2].flatMap fun b => [0, 1, 2].map fun c => (a, b, c)

/-- replace column `k` of `C` -/
def setCol (C : Coef) (k : Fin 6) (v : Fin 3 × Fin 3 × Fin 3) : Coef := fun r j =>
  if j = k then (if r = 0 then v.1 else if r = 1 then v.2.1 else v.2.2) else C r j

/-- the search tree: `fuel` more columns may be fixed; `d` columns are fixed already -/
def tree : Nat → Nat → Coef → Bool
  | 0, d, C => wit C d
  | f + 1, d, C => wit C d || cols.all fun v => tree f (d + 1) (setCol C (ord d) v)

/-- the root: no column fixed, six to go -/
def root (_ : Unit) : Bool := tree 6 0 (fun _ _ => 0)

end NilCore
