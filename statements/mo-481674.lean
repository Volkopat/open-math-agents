import Mathlib.RingTheory.PowerSeries.Derivative

/-! Source: https://mathoverflow.net/questions/481674
Sequences: https://oeis.org/A006351 and https://oeis.org/A379460 -/

namespace OMA.S_mo_481674

def R : ℕ → ℕ → ℕ
  | 0, _ => 1
  | n + 1, 0 => R n 0 + R n 1
  | n + 1, q + 1 => R (n + 1) q + (q + 2) * (R n (q + 1) + R n (q + 2))
termination_by n q => (n, q)

theorem main :
    ∀ B : PowerSeries ℚ, B.constantCoeff = 0 →
      PowerSeries.derivative (R := ℚ) B * (1 - B) = 1 + B →
      ∀ n : ℕ, (R n 0 : ℚ) = ((n + 1).factorial : ℚ) * PowerSeries.coeff (n + 1) B := by
  sorry

end OMA.S_mo_481674
