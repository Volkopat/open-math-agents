import Mathlib

/-!
# A067129: Numbers k such that sigma(k - 3) + sigma(k + 3) = sigma(2 * k)

Source: https://oeis.org/A067129

Conjecture (OEIS A067129):
Every integer `k ≥ 4` satisfying `σ(k - 3) + σ(k + 3) = σ(2 * k)` is odd.

Conventions:
- Offset: `1`; first terms: `5, 63, 99, 279, 355, 551, 561, 639, 1359, 1915, ...`.
- We require `4 ≤ k` so that `k - 3 ≥ 1` and `σ(k - 3)` is the sum of positive divisors
  of a positive integer.
-/

namespace OMA.S_oeis_a067129

/-- Sum of positive divisors `σ(n)` of `n : ℕ`. -/
def sigma (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors, d

/-- Membership predicate for OEIS A067129: `k ≥ 4` and `σ(k - 3) + σ(k + 3) = σ(2 * k)`. -/
def IsTerm (k : ℕ) : Prop :=
  4 ≤ k ∧ sigma (k - 3) + sigma (k + 3) = sigma (2 * k)

/-- Conjecture: all terms of OEIS A067129 are odd. -/
theorem main :
    ∀ k : ℕ, IsTerm k → Odd k := by
  sorry

end OMA.S_oeis_a067129
