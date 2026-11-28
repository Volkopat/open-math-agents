import Mathlib

/-!
# A242137: Numbers n such that there are no triangular numbers strictly between n^2 and n^2 + n.

Source: https://oeis.org/A242137
Credit: @Harsha0912

Conjecture (in the comments of A242137): for n > 2, a(n+1) - a(n) = either 2 or 3 or 5
(checked up to a(n) = 2^32).

Conventions:
* The triangular numbers are m*(m+1)/2 for natural m.
* n belongs to the sequence when no triangular number t satisfies n^2 < t < n^2 + n.
* The sequence has offset 1 (a(1) = 0), so a(n) is `Nat.nth P (n - 1)`.
-/

namespace OMA.S_oeis_a242137

/-- `n` is a term: no triangular number lies strictly between `n^2` and `n^2 + n`. -/
def P (n : ℕ) : Prop := ∀ m : ℕ, ¬ (n ^ 2 < m * (m + 1) / 2 ∧ m * (m + 1) / 2 < n ^ 2 + n)

/-- A242137 with offset 1: `a 1 = 0`, `a 2 = 1`, `a 3 = 2`, `a 4 = 4`, ... -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth P (n - 1)

/-- For `n > 2`, consecutive terms differ by 2, 3 or 5. -/
theorem main : ∀ n : ℕ, 2 < n →
    (a (n + 1) - a n = 2 ∨ a (n + 1) - a n = 3 ∨ a (n + 1) - a n = 5) := by
  sorry

end OMA.S_oeis_a242137
