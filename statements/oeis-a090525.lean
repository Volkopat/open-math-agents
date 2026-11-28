import Mathlib

/-!
# A090525: Least number k such that floor((n^n)/k) is prime, or 0 if no such number exists.

Source: https://oeis.org/A090525
Credit: @bnb9001

The sequence has offset 2. Here `n ^ n / k` is natural-number (floor) division, and the least
such `k` is `sInf`, which is `0` exactly when no such `k` exists (no `k = 0` qualifies, since
`n ^ n / 0 = 0` is not prime).

Conjecture: no term is zero. James Rayman notes that the conjecture is true.
-/

namespace OMA.S_oeis_a090525

/-- The least `k` such that `⌊n ^ n / k⌋` is prime, or `0` if there is none. -/
noncomputable def a (n : ℕ) : ℕ := sInf {k : ℕ | (n ^ n / k).Prime}

/-- For every `n ≥ 2`, `a n ≠ 0`. -/
theorem main : ∀ n : ℕ, 2 ≤ n → a n ≠ 0 := by
  sorry

end OMA.S_oeis_a090525
