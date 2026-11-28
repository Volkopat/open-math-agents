import Mathlib.RingTheory.PowerSeries.Exp

/-! Source: https://mathoverflow.net/questions/460786
Sequence: https://oeis.org/A235129 -/

open scoped BigOperators

namespace OMA.S_mo_460786

def R : ℕ → ℕ → ℕ
  | 0, q => if q = 0 then 1 else 0
  | n + 1, q => R n (q + 1) + (q + 1) * ∑ j ∈ Finset.range (q + 1), q.choose j * R n j

noncomputable def rhs : PowerSeries ℚ := 1 + PowerSeries.X * PowerSeries.exp ℚ

theorem main :
    ∀ A : PowerSeries ℚ, A.constantCoeff = 0 → PowerSeries.derivative (R := ℚ) A = rhs.subst A →
      ∀ n : ℕ, (R n 0 : ℚ) = ((n + 1).factorial : ℚ) * PowerSeries.coeff (n + 1) A := by
  sorry

end OMA.S_mo_460786
