import Mathlib

/-!
# A155860: Number of ways to write 2n-1 as p + 2^x + 3*2^y with p an odd prime and x,y positive integers

Source: https://oeis.org/A155860
Credit: @niclorusso

Conjecture (Zhi-Wei Sun, Jan 21 2009, in the comments of A155860): a(n)>0 for n=6,7,...; in other
words, any odd integer m>10 can be written as the sum of an odd prime, a positive power of 2 and
three times a positive power of 2. (Verified for odd integers below 10^10.)

Conventions:
* The conjecture is stated in its second form: every odd m > 10 is p + 2^x + 3 * 2^y with p an odd
  prime (p /= 2) and x, y >= 1.
-/

namespace OMA.S_oeis_a155860

/-- Sun's conjecture on A155860: every odd `m > 10` is `p + 2^x + 3 * 2^y` with `p` an odd prime and
`x, y >= 1`. -/
theorem main : ∀ m : ℕ, Odd m → 10 < m → ∃ p x y : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ x ∧ 1 ≤ y ∧
    p + 2 ^ x + 3 * 2 ^ y = m := by
  sorry

end OMA.S_oeis_a155860
