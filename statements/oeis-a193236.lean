import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a193236

/-- OEIS A193236: Let S(x) = ∑_{n≥0} (2*n + 1) * (-3)^n * x^(n*(n+1)/2) ∈ ℤ[[x]],
and let A(x) ∈ ℤ[[x]] have A(0) = 1 and satisfy A(x)^3 * S(x) = 1.
Then 5 ∣ a(5*n + 4) and 7 ∣ a(7*n + 5) for all 
 ≥ 0. -/
theorem main :
    ∀ (A S : PowerSeries ℤ),
      PowerSeries.constantCoeff A = 1 →
      (∀ m : ℕ, PowerSeries.coeff m S =
        ∑ n ∈ Finset.range (m + 1),
          if n * (n + 1) / 2 = m then ((2 * n + 1 : ℕ) : ℤ) * (-3 : ℤ) ^ n else 0) →
      A ^ 3 * S = 1 →
      ∀ n : ℕ, (5 : ℤ) ∣ PowerSeries.coeff (5 * n + 4) A ∧
               (7 : ℤ) ∣ PowerSeries.coeff (7 * n + 5) A := by
  sorry

end OMA.S_oeis_a193236
