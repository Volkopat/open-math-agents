import Mathlib

/-!
# A069056: Numbers k such that Sum_{d|k} d^2*mu(d) divides k^2

Source: https://oeis.org/A069056
Credit: @niclorusso

Conjecture (in the comments of A069056): if c > 2 and n > 1, Sum_{d|n} d^c*mu(d) never divides n^c.

Conventions:
* mu is the Möbius function, Mathlib's `ArithmeticFunction.moebius`; the sum runs over the positive
  divisors d of n (`Nat.divisors n`) and is computed in the integers (it can be negative).
* Divisibility is divisibility in the integers.
* c and n are natural numbers with c > 2 and n > 1.
-/

namespace OMA.S_oeis_a069056

open ArithmeticFunction

/-- `S c n = Sum_{d | n} d^c * mu(d)`, as an integer. -/
def S (c n : ℕ) : ℤ := ∑ d ∈ n.divisors, (d : ℤ) ^ c * moebius d

/-- The conjecture on A069056: for `c > 2` and `n > 1`, `Sum_{d|n} d^c * mu(d)` does not divide
`n^c`. -/
theorem main : ∀ c n : ℕ, 2 < c → 1 < n → ¬ (S c n ∣ (n : ℤ) ^ c) := by
  sorry

end OMA.S_oeis_a069056
