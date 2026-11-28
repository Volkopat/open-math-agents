import Mathlib

namespace OMA.S_oeis_a350410

open PowerSeries BigOperators

/-- Conjecture on OEIS A350410 (Paul D. Hanna):
If `A(x) = ∑_{n ≥ 0} a(n) x^n ∈ ℚ[[X]]` satisfies `0 = [x^n] ∑_{m=0}^n A(x)^(m^2) / m! for n > 1, with A(0) = -1, A(1) = 1`,
then every coefficient `a(n)` is an integer. -/
theorem main :
    ∀ A : PowerSeries ℚ,
      PowerSeries.coeff 0 A = -1 →
      PowerSeries.coeff 1 A = 1 →
      (∀ n : ℕ, 2 ≤ n →
        PowerSeries.coeff n (∑ m ∈ Finset.range (n + 1),
          PowerSeries.C ((1 : ℚ) / ((Nat.factorial m : ℕ) : ℚ)) * A ^ (m ^ 2)) = 0) →
      ∀ n : ℕ, ∃ z : ℤ, PowerSeries.coeff n A = (z : ℚ) := by
  sorry

end OMA.S_oeis_a350410
