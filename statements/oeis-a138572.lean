import Mathlib

/-!
# A138572: Numbers k that divide the sum of the digits of k^k in base 2

Source: https://oeis.org/A138572

Conjecture (OEIS A138572):
There are infinitely many positive integers `k` that divide the binary digit sum
(popcount) of `k^k`.

Conventions:
- Offset: `1`; first terms: `1` (`1^1 = 1`, popcount `1`), `6` (`6^6 = 46656`, popcount `6`),
  `122` (`122^122` has popcount divisible by `122`), ...
- `(Nat.digits 2 (k ^ k)).sum` computes the sum of base-2 digits of `k^k`.
-/

namespace OMA.S_oeis_a138572

/-- The set of positive integers `k` dividing the sum of base-2 digits of `k^k`
(OEIS A138572). -/
def S : Set ℕ :=
  {k : ℕ | 1 ≤ k ∧ k ∣ (Nat.digits 2 (k ^ k)).sum}

/-- Conjecture: there are infinitely many positive integers `k` dividing the binary digit
sum of `k^k`. -/
theorem main : Set.Infinite S := by
  sorry

end OMA.S_oeis_a138572
