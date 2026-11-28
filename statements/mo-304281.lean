import Mathlib

/-!
# Strict stability of the square block of a real row-orthogonal matrix

Source: Ludwig, https://mathoverflow.net/questions/304281 (CC BY-SA 4.0).
Contribution by @connoranderson.

The blocks A and B have n rows, and A is square. Row orthogonality of their
horizontal concatenation is written A Aᵀ + B Bᵀ = I. The real test matrix
stacks Bᵀ (Aᵀ)^j for j from 0 through n−1.
-/

namespace OMA.S_mo_304281
open Matrix
open scoped Matrix
abbrev Sq (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
def tests {n k : ℕ} (A : Sq n) (B : Matrix (Fin n) (Fin k) ℝ) :
    Matrix (Fin n × Fin k) (Fin n) ℝ := fun i j => (Bᵀ*(Aᵀ)^i.1.val) i.2 j
def stable {n : ℕ} (A : Sq n) : Prop :=
  ∀ z : ℂ, (A.map Complex.ofReal).charpoly.IsRoot z → ‖z‖ < 1

theorem main : ∀ (n k : ℕ) (A : Sq n) (B : Matrix (Fin n) (Fin k) ℝ),
    A*Aᵀ+B*Bᵀ=1 →
    (∀ z : ℂ, (A.map Complex.ofReal).charpoly.IsRoot z → ‖z‖ ≤ 1) ∧
    (stable A ↔ (tests A B).rank=n) := by
  sorry
end OMA.S_mo_304281
