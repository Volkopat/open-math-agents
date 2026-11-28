import Mathlib

/-!
# OEIS A158521: Primes which yield primes when "13" is prefixed or appended.

Source: https://oeis.org/A158521
Credit: @unserus

OEIS: "It is conjectured that this sequence is infinite."
Concatenation is in base 10: prefixing "13" to `p` gives `13 * 10^(number of digits of p) + p`,
and appending it gives `100 * p + 13` (e.g. `p = 19`: `1319` and `1913`, both prime; `p = 3`:
`133 = 7 * 19`, so `3` is not a term, as in the OEIS examples).
-/

namespace OMA.S_oeis_a158521

/-- "13" written in front of `p`, in base 10. -/
def prefix13 (p : ℕ) : ℕ := 13 * 10 ^ (Nat.digits 10 p).length + p

/-- "13" written after `p`, in base 10. -/
def append13 (p : ℕ) : ℕ := 100 * p + 13

/-- The terms of A158521: primes `p` such that both `"13" ++ p` and `p ++ "13"` are prime. -/
def a158521Set : Set ℕ := {p : ℕ | p.Prime ∧ (prefix13 p).Prime ∧ (append13 p).Prime}

/-- A158521 is infinite. -/
theorem main : a158521Set.Infinite := by
  sorry

end OMA.S_oeis_a158521
