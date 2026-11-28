import Mathlib

/-!
# OEIS A144125: Primes of the form P_4(n) where P_4(n) is the Legendre polynomial of order 4
at n.

Source: https://oeis.org/A144125
Credit: @unserus

OEIS (C. R. Greathouse IV): "This sequence is infinite under Bunyakovsky's conjecture."
The open statement is that the sequence is infinite. The Legendre polynomial of order 4 is
`P_4(x) = (35 x^4 - 30 x^2 + 3) / 8`; a prime `p` has the form `P_4(n)` (for a natural number
`n`) exactly when `8 p = 35 n^4 - 30 n^2 + 3`, stated in `ℤ` (first term `10321 = P_4(7)`).
-/

namespace OMA.S_oeis_a144125

/-- The terms of A144125: primes `p = P_4(n)` for some natural number `n`. -/
def a144125Set : Set ℕ :=
  {p : ℕ | p.Prime ∧ ∃ n : ℕ, 8 * (p : ℤ) = 35 * (n : ℤ) ^ 4 - 30 * (n : ℤ) ^ 2 + 3}

/-- A144125 is infinite. -/
theorem main : a144125Set.Infinite := by
  sorry

end OMA.S_oeis_a144125
