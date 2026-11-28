import Mathlib

/-!
# A120121: a digit-product and digit-sum fixed point of Euler's totient

Source: https://oeis.org/A120121
Source data: https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A120/A120121.seq
Credit: @Bondyboy2001

For a positive integer `m` with decimal digits `d₁, …, dₖ`, the sequence consists of the
solutions of `m = phi((d₁ * … * dₖ) * (d₁ + … + dₖ))`. Digit order is irrelevant here because
only the product and sum occur.
-/

namespace OMA.S_oeis_a120121

/-- The defining digit equation of A120121. -/
def IsDigitTotientFixedPoint (m : ℕ) : Prop :=
  m = Nat.totient ((Nat.digits 10 m).prod * (Nat.digits 10 m).sum)

/-- Firoozbakht's conjecture: `139968` is the largest term. -/
theorem main : IsGreatest {m : ℕ | 0 < m ∧ IsDigitTotientFixedPoint m} 139968 := by
  sorry

end OMA.S_oeis_a120121
