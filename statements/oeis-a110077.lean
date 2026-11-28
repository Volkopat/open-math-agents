import Mathlib

/-!
# A110077: smallest inverse image of `10 ^ n` under the divisor-sum function

Source: https://oeis.org/A110077
Source data: https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A110/A110077.seq
Credit: @Bondyboy2001

The sequence value is the smallest positive `m` with `sigma(m) = 10 ^ n`, or zero if no such
`m` exists. In Mathlib `sInf` of an empty set of natural numbers is zero, so the set-valued
definition below has exactly the source's zero convention.
-/

namespace OMA.S_oeis_a110077

/-- The smallest positive `m` with `sigma(m) = 10 ^ n`, or zero if no such `m` exists. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {m : ℕ | 0 < m ∧ ArithmeticFunction.sigma 1 m = 10 ^ n}

/-- Firoozbakht's conjecture: the sequence is positive for every `n > 3`. -/
theorem main : ∀ n : ℕ, 3 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a110077
