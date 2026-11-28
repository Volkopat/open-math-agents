import Mathlib

/-!
# A120123: a digit product times totient-of-digit-sum fixed point

Source: https://oeis.org/A120123
Source data: https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A120/A120123.seq
Credit: @Bondyboy2001

For a positive integer `m` with decimal digits `d₁, …, dₖ`, the sequence consists of the
solutions of `m = (d₁ * … * dₖ) * phi(d₁ + … + dₖ)`. Digit order is irrelevant here because
only the product and sum occur.
-/

namespace OMA.S_oeis_a120123

/-- The defining digit equation of A120123. -/
def IsDigitProductTotientSumFixedPoint (m : ℕ) : Prop :=
  m = (Nat.digits 10 m).prod * Nat.totient (Nat.digits 10 m).sum

/-- Firoozbakht's conjecture: `139968` is the largest term. -/
theorem main : IsGreatest {m : ℕ | 0 < m ∧ IsDigitProductTotientSumFixedPoint m} 139968 := by
  sorry

end OMA.S_oeis_a120123
