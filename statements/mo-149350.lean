import Mathlib

/-!
# Orthogonal matrices minimizing squared bilinear measurements

Source: Matt, https://mathoverflow.net/questions/149350 (CC BY-SA 3.0).
Credit: @connoranderson.

For dimension two an explicit minimum is obtained from the smaller eigenvalues
of two real two-by-two matrices, one for each determinant sign. In variable
dimension we give a gap-preserving reduction from two-colorability of 3-uniform
hypergraphs. Its data entries are zero or one. With d vertices plus auxiliary
coordinates the number of measurement rows is d(d−1) plus the number of edges.
An inverse-polynomial positive gap separates the two cases. The reduction
gives a complexity obstruction to a polynomial-time algorithm for the general
problem (see Dinur, Regev and Smyth, https://cims.nyu.edu/~regev/papers/hyper_color.pdf).
-/

namespace OMA.S_mo_149350
open Matrix Finset Set
abbrev Mat (I : Type) := Matrix I I ℝ
def orth {I : Type} [Fintype I] [DecidableEq I] (M : Mat I) : Prop :=
  M.transpose * M = 1
def innerTerm {I : Type} [Fintype I] (a b : I → ℝ) (M : Mat I) : ℝ :=
  ∑ i, ∑ j, a i * M i j * b j
def cost {I R : Type} [Fintype I] [Fintype R] (A B : R → I → ℝ) (M : Mat I) : ℝ :=
  ∑ r, (innerTerm (A r) (B r) M)^2

abbrev Index (v m : ℕ) := Fin v ⊕ Fin m
abbrev Off (I : Type) := {p : I × I // p.1 ≠ p.2}
abbrev Measurement (v m : ℕ) := Off (Index v m) ⊕ Fin m
abbrev Edges (v m : ℕ) := Fin m → Fin 3 → Fin v

def twoColorable {v m : ℕ} (edges : Edges v m) : Prop :=
  ∃ c : Fin v → Bool, ∀ r, ¬ (c (edges r 0) = c (edges r 1) ∧
    c (edges r 1) = c (edges r 2))

def dataA (v m : ℕ) : Measurement v m → Index v m → ℝ
  | .inl p => Pi.single p.val.1 1
  | .inr _ => fun _ => 1

def dataB {v m : ℕ} (edges : Edges v m) : Measurement v m → Index v m → ℝ
  | .inl p => Pi.single p.val.2 1
  | .inr r => Pi.single (.inl (edges r 0)) 1 + Pi.single (.inl (edges r 1)) 1 +
      Pi.single (.inl (edges r 2)) 1 + Pi.single (.inr r) 1

noncomputable def tolerance (I : Type) [Fintype I] : ℝ := 1/(16*((Fintype.card I:ℝ)+1))

def planeU (a b : Fin 2 → ℝ) (ε : ℝ) : ℝ :=
  a 0 * b 0 + ε * a 1 * b 1
def planeV (a b : Fin 2 → ℝ) (ε : ℝ) : ℝ :=
  a 1 * b 0 - ε * a 0 * b 1

noncomputable def planeEigen {R : Type} [Fintype R] (A B : R → Fin 2 → ℝ) (ε : ℝ) : ℝ :=
  let p := ∑ r, (planeU (A r) (B r) ε)^2
  let q := ∑ r, planeU (A r) (B r) ε * planeV (A r) (B r) ε
  let s := ∑ r, (planeV (A r) (B r) ε)^2
  (p+s - Real.sqrt ((p-s)^2 + 4*q^2))/2

theorem main :
    (∀ (R : Type) [Fintype R] (A B : R → Fin 2 → ℝ),
      IsLeast {c : ℝ | ∃ M : Mat (Fin 2), orth M ∧ cost A B M = c}
        (min (planeEigen A B 1) (planeEigen A B (-1)))) ∧
    (∀ (v m : ℕ) (edges : Edges v m), (∀ r, Function.Injective (edges r)) →
      (∀ r i, (dataA v m r i = 0 ∨ dataA v m r i = 1) ∧
        (dataB edges r i = 0 ∨ dataB edges r i = 1)) ∧
      (twoColorable edges → ∃ M : Mat (Index v m), orth M ∧ cost (dataA v m) (dataB edges) M = 0) ∧
      (¬twoColorable edges → ∀ M : Mat (Index v m), orth M →
        (tolerance (Index v m))^2 ≤ cost (dataA v m) (dataB edges) M)) := by
  sorry
end OMA.S_mo_149350
