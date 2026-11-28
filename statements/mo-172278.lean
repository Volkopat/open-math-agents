import Mathlib

open MeasureTheory

namespace OMA.S_mo_172278

/-- The improper integral from negative infinity to t, taken through
integrable finite intervals. -/
def HasIntegralFromNegInfty (f : ℝ → ℝ) (t v : ℝ) : Prop :=
  (∀ a b : ℝ, IntervalIntegrable f volume a b) ∧
    Filter.Tendsto (fun R : ℝ => ∫ x in (-R)..t, f x) Filter.atTop (nhds v)

/-- The nested oscillatory integrals of Kholodenko and Silagadze. -/
theorem main :
    ∃ pairIntegral innerIntegral : ℕ → ℝ → ℝ,
      (∀ t : ℝ, pairIntegral 0 t = 1) ∧
      (∀ (n : ℕ) (t : ℝ),
        HasIntegralFromNegInfty (fun s => Real.cos (t ^ 2 - s ^ 2) * pairIntegral n s)
          t (innerIntegral n t)) ∧
      (∀ (n : ℕ) (t : ℝ),
        HasIntegralFromNegInfty (innerIntegral n) t (pairIntegral (n + 1) t)) ∧
      ∀ n : ℕ, 0 < n →
        Filter.Tendsto (pairIntegral n) Filter.atTop
          (nhds (2 / (n.factorial : ℝ) * (Real.pi / 4) ^ n)) := by
  sorry

end OMA.S_mo_172278
