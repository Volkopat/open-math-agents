import Mathlib

/-!
# A384955: Multinomial coefficient of the decimal digits of n

Source: https://oeis.org/A384955

Conjecture (OEIS A384955):
`a(n) = n` if and only if `n = 1` or `n = 1512`, where `a(n)` is the multinomial
coefficient `(d_1 + ... + d_r)! / (d_1! * ... * d_r!)` of the base-10 digits of `n`.

Conventions:
- Offset: `0`; `a(0) = 0! / 1 = 1`, `a(1) = 1! / 1! = 1`,
  `a(1512) = (1 + 5 + 1 + 2)! / (1! * 5! * 1! * 2!) = 9! / 240 = 1512`.
- `Nat.digits 10 n` returns the list of base-10 digits of `n` (`[]` for `n = 0`), and
  the denominator divides the numerator for every list of natural numbers.
-/

namespace OMA.S_oeis_a384955

/-- Multinomial coefficient of the base-10 digits of `n` (OEIS A384955). -/
def a (n : ℕ) : ℕ :=
  let ds := Nat.digits 10 n
  Nat.factorial ds.sum / (ds.map Nat.factorial).prod

/-- Conjecture: `a(n) = n` if and only if `n = 1` or `n = 1512`. -/
theorem main :
    ∀ n : ℕ, a n = n ↔ n = 1 ∨ n = 1512 := by
  sorry

end OMA.S_oeis_a384955
