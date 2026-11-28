import Mathlib.Data.Rat.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OMA.S_oeis_a116184

/-- The generalized harmonic number `H(36, n) = ∑_{j=1}^{36} 1 / j^n` as a rational number. -/
def H36 (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.Icc (1 : ℕ) 36, ((j : ℚ) ^ n)⁻¹

/-- OEIS A116184 conjecture: every term of the arithmetic progression `3 + 36 * k` (`k ≥ 0`)
belongs to A116184, i.e. `37^3` divides the numerator of `H(36, 3 + 36 * k)`. -/
theorem main :
    ∀ k : ℕ, ((37 ^ 3 : ℕ) : ℤ) ∣ (H36 (3 + 36 * k)).num := by
  sorry

end OMA.S_oeis_a116184
