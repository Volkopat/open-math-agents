import Mathlib

/-!
# A110076: largest inverse image of `10 ^ n` under the divisor-sum function

Source: https://oeis.org/A110076
Source data: https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A110/A110076.seq
Credit: @Bondyboy2001

The sequence value is the largest `m` with `sigma(m) = 10 ^ n`, or zero if there is no such
`m`. Every positive solution satisfies `m ≤ sigma(m)`, so searching through `10 ^ n` is exact.
-/

namespace OMA.S_oeis_a110076

/-- The largest `m` with `sigma(m) = 10 ^ n`, or zero if there is no such positive `m`. -/
def a (n : ℕ) : ℕ :=
  Nat.findGreatest (fun m => ArithmeticFunction.sigma 1 m = 10 ^ n) (10 ^ n)

/-- Firoozbakht's conjecture: the sequence is positive for every `n > 3`. -/
theorem main : ∀ n : ℕ, 3 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a110076
