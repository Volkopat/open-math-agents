import Mathlib.RingTheory.PowerSeries.Basic

/-! Source: https://mathoverflow.net/questions/490843
Sequence: https://oeis.org/A302285 -/

open scoped BigOperators

namespace OMA.S_mo_490843

def R : ℕ → ℕ → ℕ
  | 0, _ => 1
  | n + 1, k => R n (k + 1) + ∑ i ∈ (Finset.range (n + 1)).attach,
      ∑ j ∈ Finset.range (k + 1), k.choose j * R (n - i.val) j * R i.val (k - j)
termination_by n _k => n
decreasing_by
  · omega
  · omega
  · exact Finset.mem_range.mp i.property

/-- The relations among the F h are obtained by clearing each continued-fraction denominator. -/
theorem main :
    ∀ F : ℕ → PowerSeries ℤ,
      (∀ h : ℕ, F h = 1 + PowerSeries.X *
        (PowerSeries.C ((h + 1 : ℕ) : ℤ) * F h + F (h + 1) * F h)) →
      ∀ n : ℕ, (R n 0 : ℤ) = PowerSeries.coeff n (F 0) := by
  sorry

end OMA.S_mo_490843
