import Mathlib.RingTheory.PowerSeries.Derivative

/-! Source: https://mathoverflow.net/questions/481528
Sequence: https://oeis.org/A338193 -/

namespace OMA.S_mo_481528

def R : ℕ → ℕ → ℕ
  | 0, _ => 1
  | n + 1, 0 => R n 0 + (n + 1) * R n 1
  | n + 1, q + 1 => R (n + 1) q + (n + 1) * (R n (q + 1) + R n (q + 2))
termination_by n q => (n, q)

theorem main :
    ∀ A : PowerSeries ℚ, A.constantCoeff = 1 →
      let B := PowerSeries.derivative (R := ℚ) A
      B * (A - 2 * PowerSeries.X * B) = A * (A - PowerSeries.X * B) →
        ∀ n : ℕ, (R n 0 : ℚ) = ((n + 1).factorial : ℚ) * PowerSeries.coeff (n + 1) A := by
  sorry

end OMA.S_mo_481528
