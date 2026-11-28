import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.NormNum

/-!
# Permanent first agreement of two nonnegative matrix power orbits

Source: https://mathoverflow.net/questions/375001
Question by Antonio AN, 27 October 2020, CC BY-SA 4.0.
The counterexample mechanism was given in source comments by Doriano Brogioli
(comment 950539) and Jochen Glueck (comment 950560). This formalization extends
the nilpotent-block-plus-identity construction to every positive n and normalizes
the initial row to satisfy all the row and column sum bounds.

For any positive n, take r = n + 1, A = 0_n direct-sum [1],
B = J_n direct-sum [1], and Gamma = (e_0 + e_n) / 2, where J_n has ones
on its superdiagonal. Their orbits first agree at n and agree forever thereafter.
The dimension varies with n. No claim is made about an additional lower bound
on n that depends on r, since no such hypothesis is specified in the question.
-/

open scoped BigOperators Matrix

noncomputable section

namespace OMA.S_mo_375001

/-- The exact counterexample properties, including both substochasticity directions,
non-nilpotency, first positive agreement at `n`, and agreement at every later time. -/
def CounterexampleAt (n : ℕ) : Prop :=
  ∃ (r : ℕ) (Γ : Fin r → ℝ) (A B : Matrix (Fin r) (Fin r) ℝ),
    0 < r ∧
    (∀ i, 0 ≤ Γ i) ∧ (∑ i, Γ i) ≤ 1 ∧ (∀ i, Γ i ≤ 1) ∧
    (∀ i j, 0 ≤ A i j) ∧ (∀ i j, 0 ≤ B i j) ∧
    (∀ i, (∑ j, A i j) ≤ 1) ∧ (∀ j, (∑ i, A i j) ≤ 1) ∧
    (∀ i, (∑ j, B i j) ≤ 1) ∧ (∀ j, (∑ i, B i j) ≤ 1) ∧
    (∀ k : ℕ, A ^ k ≠ 0) ∧ (∀ k : ℕ, B ^ k ≠ 0) ∧
    Γ ᵥ* A ^ n = Γ ᵥ* B ^ n ∧ Γ ᵥ* A ^ n ≠ 0 ∧
    (∀ k : ℕ, 0 < k → k < n → Γ ᵥ* A ^ k ≠ Γ ᵥ* B ^ k) ∧
    (∀ k : ℕ, n ≤ k → Γ ᵥ* A ^ k = Γ ᵥ* B ^ k)

theorem main : ∀ n : ℕ, 0 < n → CounterexampleAt n := by
  sorry

end OMA.S_mo_375001
