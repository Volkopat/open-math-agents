import Mathlib

/-!
# OEIS A168417: Primes q for which 1 concatenated with q^3 (A168327) is prime.

Source: https://oeis.org/A168417
Credit: @unserus

OEIS: "It is conjectured that this sequence is infinite."
Concatenation is in base 10: the digit `1` followed by the digits of `q^3` is
`10^(number of digits of q^3) + q^3`, as in the OEIS examples `"1 3^3" = 10^2 + 3^3 = 127` and
`"1 103^3" = 10^7 + 103^3 = 11092727`.
-/

namespace OMA.S_oeis_a168417

/-- The digit `1` followed by the base-10 digits of `m`. -/
def prefixOne (m : ℕ) : ℕ := 10 ^ (Nat.digits 10 m).length + m

/-- The terms of A168417: primes `q` such that `"1" ++ q^3` is prime. -/
def a168417Set : Set ℕ := {q : ℕ | q.Prime ∧ (prefixOne (q ^ 3)).Prime}

/-- A168417 is infinite. -/
theorem main : a168417Set.Infinite := by
  sorry

end OMA.S_oeis_a168417
