import Mathlib

/-!
# Zero diagonal odd powers and reflection symmetry of numerical ranges

Source: Astor, https://mathoverflow.net/questions/278672 (CC BY-SA 3.0).
Credit: @connoranderson.

A symmetric zero pattern is an undirected simple graph. Its odd powers
have zero diagonal for every real nonsymmetric realization exactly when
the graph is bipartite. In that case the two-coloring changes the sign
of the matrix by diagonal orthogonal conjugation, and complex conjugation
supplies reflection of the numerical range about the imaginary axis.

For an individual matrix, cancellations may give zero diagonal in every
odd power even on the complete triangle. The explicit nonsymmetric matrix
below has a symmetric and persymmetric support, satisfies A³=-5A, and
its numerical range contains 4 but excludes -4. Changing its entries to
their absolute values keeps its support and destroys the odd-power property.
-/

namespace OMA.S_mo_278672
open Matrix
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
def pattern {n : ℕ} (G : SimpleGraph (Fin n)) (A : Mat n) : Prop :=
  ∀ i j, A i j≠0 ↔ G.Adj i j
def oddDiagonal {n : ℕ} (A : Mat n) : Prop := ∀ k : ℕ,∀ i,(A^(2*k+1)) i i=0
def numRange {n : ℕ} (A : Mat n) : Set ℂ :=
  {z | ∃ x : Fin n → ℂ, x≠0 ∧ star x ⬝ᵥ ((A.map Complex.ofReal) *ᵥ x) = z*(star x ⬝ᵥ x)}
def reflected (S : Set ℂ) : Prop := ∀ z∈S,-star z∈S
def exampleA : Mat 3 := !![0,6,2; -2,0,1; 2,3,0]

theorem main :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.IsBipartite ↔
      ∀ A : Mat n, pattern G A → ¬A.IsSymm → oddDiagonal A) ∧
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Mat n), G.IsBipartite →
      pattern G A → reflected (numRange A)) ∧
    (pattern ⊤ exampleA ∧ ¬exampleA.IsSymm ∧
      (∀ i j, exampleA i j≠0 ↔ exampleA j.rev i.rev≠0) ∧
      (∃ B : Mat 3, pattern ⊤ B ∧ ¬B.IsSymm ∧ ¬oddDiagonal B)) ∧
    oddDiagonal exampleA ∧ (4:ℂ)∈numRange exampleA ∧ (-4:ℂ)∉numRange exampleA := by
  sorry
end OMA.S_mo_278672
