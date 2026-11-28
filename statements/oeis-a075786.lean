import Mathlib

/-!
# A075786: Palindromic perfect powers.

Source: https://oeis.org/A075786
Credit: @divmxnd0x

Conjecture (stated in A075786): there are no palindromic perfect powers with prime exponent > 3.

Formalization notes:
* A perfect power with prime exponent `p` is `m^p` with `m ≥ 2` (for `m ≤ 1`, `m^p ∈ {0, 1}` is
  trivially palindromic and is not a perfect power in the intended sense); palindromic means in
  base 10 (the decimal digits read the same backwards).
-/

namespace OMA.S_oeis_a075786

/-- `n` is a palindrome in base 10. -/
def IsPalindrome (n : ℕ) : Prop := (Nat.digits 10 n).reverse = Nat.digits 10 n

/-- No `m^p` with `m ≥ 2` and `p` a prime `> 3` is a decimal palindrome. -/
theorem main : ∀ m p : ℕ, 2 ≤ m → p.Prime → 3 < p → ¬ IsPalindrome (m ^ p) := by
  sorry

end OMA.S_oeis_a075786
