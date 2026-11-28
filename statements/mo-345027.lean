import Mathlib

/-!
# Sharp spectrum and realization for normalized matrix summands

Source: Arnold Neumaier, https://mathoverflow.net/questions/345027 (CC BY-SA 4.0).
Contribution by @connoranderson.

The j-th column is Aⱼu divided by the positive square root of uᵀAⱼu.
The output is its Gram matrix for the inverse of the sum of the Aⱼ.
The eigenvalue one is always attained. The converse constructs all possible
outputs using positive semidefinite summands of an identity matrix.
-/

namespace OMA.S_mo_345027
open Matrix Finset
open scoped Matrix
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
abbrev Vec (n : ℕ) := Fin n → ℝ
def admissible {n m : ℕ} (A : Fin m → Mat n) (u : Vec n) : Prop :=
  (∀ j, (A j).PosSemidef) ∧ (∑ j, A j).PosDef ∧ ∀ j, 0 < u ⬝ᵥ (A j *ᵥ u)
noncomputable def weight {n m} (A : Fin m → Mat n) (u : Vec n) (j : Fin m) : ℝ :=
  Real.sqrt (u ⬝ᵥ (A j *ᵥ u))
noncomputable def cols {n m} (A : Fin m → Mat n) (u : Vec n) :
    Matrix (Fin n) (Fin m) ℝ := fun i j => (A j *ᵥ u) i / weight A u j
noncomputable def output {n m} (A : Fin m → Mat n) (u : Vec n) : Mat m :=
  (cols A u)ᵀ * (∑ j,A j)⁻¹ * cols A u
def eligible {m : ℕ} (B : Mat m) : Prop :=
  B.PosSemidef ∧ (1-B).PosSemidef ∧ ∃ w : Vec m, (∀ j, 0<w j) ∧ B*ᵥw=w

/-- Real eigenvalues, characterized by a nonzero right eigenvector. -/
def eigs {m : ℕ} (B : Mat m) : Set ℝ := {t | ∃ x : Vec m, x ≠ 0 ∧ B *ᵥ x = t • x}

theorem main : (∀ (m n : ℕ) (A : Fin m → Mat n) (u : Vec n), 0 < m → admissible A u →
    eligible (output A u) ∧ IsGreatest (eigs (output A u)) 1 ∧
    ∀ t ∈ eigs (output A u), 0 ≤ t) ∧
    (∀ (m : ℕ) (B : Mat m), 0 < m → (eligible B ↔
      ∃ (A : Fin m → Mat m) (u : Vec m), admissible A u ∧ (∑ j,A j)=1 ∧ output A u=B)) := by
  sorry

end OMA.S_mo_345027
