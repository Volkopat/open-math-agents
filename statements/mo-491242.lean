import Mathlib.RingTheory.PowerSeries.WellKnown

/-! Source: https://mathoverflow.net/questions/491242
Sequence: https://oeis.org/A382991 -/

open scoped BigOperators

namespace OMA.S_mo_491242

def R : ℕ → ℕ → ℕ
  | 0, _ => 1
  | n + 1, k => (n + 1 + k).choose k + ∑ j ∈ Finset.range (k + 2), (k + 1).choose j * R n j

noncomputable def geometric : PowerSeries ℤ := (PowerSeries.invOneSubPow ℤ 1).val

noncomputable def factor (j : ℕ) : PowerSeries ℤ :=
  PowerSeries.C ((j + 1 : ℕ) : ℤ) * PowerSeries.X + PowerSeries.X ^ 2 * geometric

/-- Each factor has zero constant coefficient, so only products through length n contribute. -/
noncomputable def a (n : ℕ) : ℤ :=
  PowerSeries.coeff n (∑ i ∈ Finset.range (n + 1), ∏ j ∈ Finset.range i, factor j)

theorem main : ∀ n : ℕ, (R n 0 : ℤ) = a (n + 1) := by
  sorry

end OMA.S_mo_491242
