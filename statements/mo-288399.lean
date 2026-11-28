import Mathlib

/-!
# A column bound for the smallest eigenvalue after deleting a coordinate

Source: https://mathoverflow.net/questions/288399 (Observation 2).
Formalization: Hengzhi He (@hehz2020), assisted by Codex.

The question specifically asks whether the smallest increase, over all principal
one-coordinate deletions, is at most the Euclidean norm of *each* off-diagonal
column divided by `n - 1`. The least Rayleigh quotient on the coordinate
hyperplane `x i = 0` is exactly the least eigenvalue of the corresponding
principal submatrix. The minimum over deletions is expressed by existence of
an index. The matrices are real symmetric, positive semidefinite and have unit
diagonal, as required for correlation matrices.
-/

namespace OMA.S_mo_288399

def normSq {n : ℕ} (x : Fin n → ℝ) : ℝ := ∑ i, (x i)^2

def quad {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * A i j * x j

/-- The least Rayleigh quotient on a nonzero subspace, written homogeneously. -/
def LeastOn {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (S : (Fin n → ℝ) → Prop) (l : ℝ) : Prop :=
  (∀ x, S x → l * normSq x ≤ quad A x) ∧
  ∃ x, S x ∧ 0 < normSq x ∧ quad A x = l * normSq x

theorem main : ∀ (n : ℕ), 2 ≤ n → ∀ A : Matrix (Fin n) (Fin n) ℝ,
    A.IsSymm → (∀ i, A i i = 1) → (∀ x, 0 ≤ quad A x) →
    ∀ (l : ℝ) (d : Fin n → ℝ),
      LeastOn A (fun _ => True) l →
      (∀ i, LeastOn A (fun x => x i = 0) (d i)) →
      ∀ j, ∃ i, ((n : ℝ) - 1) * (d i - l) ≤
        Real.sqrt (∑ k, if k = j then 0 else (A k j)^2) := by
  sorry

end OMA.S_mo_288399
