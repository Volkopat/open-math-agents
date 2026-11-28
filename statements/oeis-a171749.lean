import Mathlib

/-!
# OEIS A171749: Odd primes of the form (1+n)*(2+2*n)+n*(3+2*n) = 4*n^2+7*n+2.

Source: https://oeis.org/A171749
Credit: @unserus

OEIS (C. R. Greathouse IV): "This sequence is infinite under the Bunyakovsky conjecture."
The open statement is that the sequence is infinite. `n` ranges over the natural numbers;
`n = 0` gives `2`, which is excluded as the sequence lists odd primes.
-/

namespace OMA.S_oeis_a171749

/-- The terms of A171749: odd primes of the form `4 n^2 + 7 n + 2`. -/
def a171749Set : Set ℕ := {p : ℕ | p.Prime ∧ Odd p ∧ ∃ n : ℕ, p = 4 * n ^ 2 + 7 * n + 2}

/-- A171749 is infinite. -/
theorem main : a171749Set.Infinite := by
  sorry

end OMA.S_oeis_a171749
