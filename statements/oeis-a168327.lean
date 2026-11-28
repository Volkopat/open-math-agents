import Mathlib

/-!
# OEIS A168327: Primes of concatenated form "1 n^3".

Source: https://oeis.org/A168327
Credit: @unserus

OEIS: "(1) It is conjectured that sequence is infinite."
Concatenation is in base 10: the digit `1` followed by the digits of `n^3` is
`10^(number of digits of n^3) + n^3`, as in the OEIS examples `10^1 + 1^3 = 11`,
`10^2 + 3^3 = 127`, `10^4 + 13^3 = 12197`. `n` ranges over the positive integers.
-/

namespace OMA.S_oeis_a168327

/-- The digit `1` followed by the base-10 digits of `m`. -/
def prefixOne (m : ℕ) : ℕ := 10 ^ (Nat.digits 10 m).length + m

/-- The terms of A168327: primes of the form `"1" ++ n^3` for a positive integer `n`. -/
def a168327Set : Set ℕ := {q : ℕ | q.Prime ∧ ∃ n : ℕ, 0 < n ∧ q = prefixOne (n ^ 3)}

/-- A168327 is infinite. -/
theorem main : a168327Set.Infinite := by
  sorry

end OMA.S_oeis_a168327
