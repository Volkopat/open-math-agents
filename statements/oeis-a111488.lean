import Mathlib

/-!
# A111488: Primes with decimal digits drawn from {0, 1, 3, 6}

Source: https://oeis.org/A111488

The conjecture is that infinitely many primes have this property.
-/

namespace OMA.S_oeis_a111488

/-- Every digit of the ordinary base-ten expansion belongs to the allowed list. -/
def hasAllowedDigits (n : ℕ) : Bool :=
  (Nat.digits 10 n).all fun digit => [0, 1, 3, 6].contains digit

theorem main : {p : ℕ | p.Prime ∧ hasAllowedDigits p}.Infinite := by
  sorry

end OMA.S_oeis_a111488
