import Mathlib

/-!
# OEIS A349485: Moran numbers whose arithmetic derivative is also a Moran number.

Source: https://oeis.org/A349485
Credit: @unserus

OEIS: "Conjecture: The sequence is infinite."
A Moran number (A001101) is a `k ≥ 1` whose decimal digit sum divides `k` with a prime quotient
(`18 = 9 * 2`). The arithmetic derivative of `n ≥ 1` (A003415) is
`n' = ∑_{p ∣ n} v_p(n) * (n / p)` (so `p' = 1` and `(ab)' = a'b + ab'`). Both definitions are the
ones used in the merged statements for A001101 and A007850. OEIS examples: `18' = 21` and
`153' = 111`, both Moran numbers.
-/

namespace OMA.S_oeis_a349485

/-- Moran numbers (A001101): `k / (digit sum of k)` is a prime. -/
def IsMoran (k : ℕ) : Prop :=
  1 ≤ k ∧ (Nat.digits 10 k).sum ∣ k ∧ (k / (Nat.digits 10 k).sum).Prime

/-- The arithmetic derivative of `n ≥ 1` (A003415). -/
def arithDeriv (n : ℕ) : ℕ := ∑ p ∈ n.primeFactors, n.factorization p * (n / p)

/-- The terms of A349485: Moran numbers whose arithmetic derivative is a Moran number. -/
def a349485Set : Set ℕ := {n : ℕ | IsMoran n ∧ IsMoran (arithDeriv n)}

/-- A349485 is infinite. -/
theorem main : a349485Set.Infinite := by
  sorry

end OMA.S_oeis_a349485
