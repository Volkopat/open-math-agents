import Mathlib

/-!
# A077866: Expansion of (1-x)^(-1)/(1 - x - 2*x^2 + 2*x^3).

Source: https://oeis.org/A077866
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture: let b(n) be the number of subsets S of {1,2,...,n} having more than one element
such that (sum of least two elements of S) = max(S).
Then b(0) = b(1) = b(2) = 0 and b(n+3) = a(n) for n >= 0.
-/

namespace OMA.S_oeis_a077866

/-- Coefficients of `(1 - x)^(-1) / (1 - x - 2x^2 + 2x^3) = 1 / (1 - 2x - x^2 + 4x^3 - 2x^4)`. -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | 2 => 5
  | 3 => 8
  | n + 4 => 2 * a (n + 3) + a (n + 2) - 4 * a (n + 1) + 2 * a n

/-- A finite set of natural numbers has at least two elements and the sum of its least two
elements equals its maximum. -/
def isGoodSubset (S : Finset ℕ) : Prop :=
  ∃ x y m : ℕ, x ∈ S ∧ y ∈ S ∧ m ∈ S ∧ x < y ∧
    (∀ z ∈ S, x ≤ z) ∧ (∀ z ∈ S, z ≠ x → y ≤ z) ∧ (∀ z ∈ S, z ≤ m) ∧ x + y = m

open Classical in
/-- Number of subsets of `{1, ..., n}` satisfying `isGoodSubset`. -/
noncomputable def b (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter isGoodSubset).card

theorem main :
    b 0 = 0 ∧ b 1 = 0 ∧ b 2 = 0 ∧ ∀ n : ℕ, (b (n + 3) : ℤ) = a n := by sorry

end OMA.S_oeis_a077866
