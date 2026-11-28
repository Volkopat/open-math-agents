import Mathlib

/-!
# A120122: a digit-product totient times digit-sum fixed point

Source: https://oeis.org/A120122
Source data: https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A120/A120122.seq
Credit: @Bondyboy2001

For a positive integer `m` with decimal digits `d₁, …, dₖ`, the sequence consists of the
solutions of `m = phi(d₁ * … * dₖ) * (d₁ + … + dₖ)`. Digit order is irrelevant here because
only the product and sum occur.
-/

namespace OMA.S_oeis_a120122

/-- The defining digit equation of A120122. -/
def IsDigitTotientProductFixedPoint (m : ℕ) : Prop :=
  m = Nat.totient (Nat.digits 10 m).prod * (Nat.digits 10 m).sum

/-- Firoozbakht's conjecture: `139968` is the largest term. -/
theorem main : IsGreatest {m : ℕ | 0 < m ∧ IsDigitTotientProductFixedPoint m} 139968 := by
  sorry

end OMA.S_oeis_a120122
