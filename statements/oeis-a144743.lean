import Mathlib

/-!
# A144743: Recurrence sequence a(n) = a(n-1)^2 - a(n-1) - 1, a(0) = 3

Source: https://oeis.org/A144743

Conjecture (Jianing Song, Mar 19 2022):
Sequences A130282 and A144743 are disjoint.
Here A130282 consists of integers `m` for which there exists an integer `k` with `1 < k < m - 1`
such that `(m^2 - 1) * (k^2 - 1) + 1` is a perfect square.

Conventions:
- Offset: `0`, with `a 0 = 3`, `a 1 = 5`, `a 2 = 19`, `a 3 = 341`, ...
- Values are defined in `ℤ` to avoid natural-number subtraction pitfalls.
-/

namespace OMA.S_oeis_a144743

/-- The sequence A144743: `a 0 = 3` and `a (n + 1) = a n ^ 2 - a n - 1`. -/
def a : ℕ → ℤ
  | 0 => 3
  | n + 1 => a n ^ 2 - a n - 1

/-- Conjecture (Jianing Song): no term of A144743 belongs to A130282. -/
theorem main :
    ∀ n : ℕ, ¬ ∃ k : ℤ, 1 < k ∧ k < a n - 1 ∧
      ∃ s : ℤ, s ^ 2 = (a n ^ 2 - 1) * (k ^ 2 - 1) + 1 := by
  sorry

end OMA.S_oeis_a144743
