import Mathlib.RingTheory.PowerSeries.Log

/-! Sources: https://oeis.org/A249833 and https://oeis.org/A370382 -/

open scoped BigOperators

namespace OMA.S_oeis_a249833

def R : ℕ → ℕ → ℕ
  | 0, _ => 1
  | n + 1, q => R n (q + 1) + (q + 1) * ∑ j ∈ Finset.range (q + 1), q.choose j * R n j

theorem main :
    ∀ B : PowerSeries ℚ, B.constantCoeff = 1 →
      PowerSeries.derivative (R := ℚ) B = B + B ^ 2 * PowerSeries.logOf B →
      ∀ n : ℕ, (R n 0 : ℚ) = ((n + 1).factorial : ℚ) * PowerSeries.coeff (n + 1) B := by
  sorry

end OMA.S_oeis_a249833
