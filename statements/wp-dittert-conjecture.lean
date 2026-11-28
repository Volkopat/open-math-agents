import Mathlib

/-!
# Dittert conjecture (Dittert–Hajek conjecture)

Source: https://en.wikipedia.org/wiki/Dittert_conjecture
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Let `A = [a_ij]` be a square matrix of order `n` with nonnegative real entries whose entries sum
to `n`. Define
  `φ(A) = ∏_i (∑_j a_ij) + ∏_j (∑_i a_ij) - per(A)`.
The conjecture asserts that `φ` is (uniquely) maximized at `A = (1/n) J_n`, where `J_n` is the
all-ones matrix of order `n`.

Conventions:
* the order `n` is a positive natural number and matrices are indexed by `Fin n`;
* `per` is Mathlib's `Matrix.permanent`;
* the parenthetical "(uniquely)" of the source is included: the statement asserts both that
  `φ A ≤ φ ((1/n) J_n)` for every admissible `A`, and that equality forces `A = (1/n) J_n`.
  (`(1/n) J_n` itself is admissible, so it is a maximizer.)
-/

namespace OMA.S_wp_dittert_conjecture

open Matrix

/-- Dittert's function: product of the row sums plus product of the column sums minus the
permanent. -/
noncomputable def dittertPhi {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (∏ i, ∑ j, A i j) + (∏ j, ∑ i, A i j) - A.permanent

/-- The matrix `(1/n) J_n`, all of whose entries equal `1/n`. -/
noncomputable def uniformMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun _ _ => (1 : ℝ) / n

theorem main : ∀ n : ℕ, 0 < n → ∀ A : Matrix (Fin n) (Fin n) ℝ,
    (∀ i j, 0 ≤ A i j) → ∑ i, ∑ j, A i j = (n : ℝ) →
      dittertPhi A ≤ dittertPhi (uniformMatrix n) ∧
        (dittertPhi A = dittertPhi (uniformMatrix n) → A = uniformMatrix n) := by
  sorry

end OMA.S_wp_dittert_conjecture
