import Mathlib

/-!
# A187941: least number with exactly `n` even divisors

Source: https://oeis.org/A187941
Credit: @Bondyboy2001

The sequence has offset `0`, but the conjecture is read for positive `n`: at `n = 0`,
`a 0 = 1 = 2 ^ 0`, while `0` is neither prime nor `1`.
-/

namespace OMA.S_oeis_a187941

/-- The number of even positive divisors of `m`. -/
def evenDivisorCount (m : ℕ) : ℕ :=
  (m.divisors.filter fun d => 2 ∣ d).card

/-- `a n` is the least positive integer having exactly `n` even divisors. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {m | 0 < m ∧ evenDivisorCount m = n}

/-- The conjecture: equality `a n = 2 ^ n` occurs only when `n` is prime or `n = 1`. -/
theorem main : ∀ n : ℕ, 0 < n → a n = 2 ^ n → n.Prime ∨ n = 1 := by
  sorry

end OMA.S_oeis_a187941
