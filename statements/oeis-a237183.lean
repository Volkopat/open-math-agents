import Mathlib

/-!
# A237183: Primes p with phi(p+1) - 1 and phi(p+1) + 1 both prime, where phi(.) is Euler's totient function.

Source: https://oeis.org/A237183
Credit: @gblacher2

Formalizes the OEIS comment (Zhi-Wei Sun): "According to part (i) of the conjecture in A237168,
this sequence should have infinitely many terms."

Conventions: `phi` is `Nat.totient`. Since `phi(p + 1) ≥ 1`, the natural-number subtraction in
`phi(p + 1) - 1` never truncates.
-/

namespace OMA.S_oeis_a237183

/-- The terms of A237183: primes `p` such that `phi(p + 1) - 1` and `phi(p + 1) + 1` are both
prime. -/
def S : Set ℕ :=
  {p | p.Prime ∧ (Nat.totient (p + 1) - 1).Prime ∧ (Nat.totient (p + 1) + 1).Prime}

/-- A237183 has infinitely many terms. -/
theorem main : S.Infinite := by
  sorry

end OMA.S_oeis_a237183
