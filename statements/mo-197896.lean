import Mathlib

/-!
# Equality in an auction order-statistics inequality

Source: Econ, [Inequality with CDF of order statistics](https://mathoverflow.net/questions/197896)
(2015, CC BY-SA 3.0). Credit: @connoranderson (agent: Codex).

Write the total number of bidders as `N = k + 3`, so the highest and
second-highest bids are taken among `k + 2` competitors. The CDF has a
continuous strictly positive density on its support `[0,T]`. The
question gives the formulas below for the order statistics and for the
second-highest bid conditional on a highest bid of `x`.

The inner integral on the right of the displayed inequality runs up to
`x` for `x ≤ t` and up to `t` for `x ≥ t`. Its upper endpoint is thus
`min t x`. The value assigned to a conditional law at `x = 0` has no
effect on the integral. Choosing the threshold strictly inside the support
gives a binding inequality with positive integration length.
-/

open MeasureTheory Set Filter
open scoped Topology Interval
namespace OMA.S_mo_197896

structure Distribution (T : ℝ) (F f : ℝ → ℝ) : Prop where
  cdf_cont : Continuous F
  cdf_mono : Monotone F
  cdf_nonneg : ∀ x, 0 ≤ F x
  cdf_le_one : ∀ x, F x ≤ 1
  left : F 0 = 0
  right : F T = 1
  density_meas : Measurable f
  density_cont : ContinuousOn f (Icc 0 T)
  density_pos : ∀ x ∈ Icc 0 T, 0 < f x
  hasDeriv : ∀ x ∈ Ioo 0 T, HasDerivAt F (f x) x

noncomputable def maxDensity (k : ℕ) (F f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (k+2 : ℝ) * F x ^ (k+1) * f x

noncomputable def secondCDF (k : ℕ) (F : ℝ → ℝ) (s : ℝ) : ℝ :=
  F s^(k+2) + (k+2 : ℝ)*(1-F s)*F s^(k+1)

noncomputable def secondDensity (k : ℕ) (F f : ℝ → ℝ) (s : ℝ) : ℝ :=
  (k+1 : ℝ)*(k+2 : ℝ)*(1-F s)*F s^k*f s

noncomputable def givenCDF (k : ℕ) (F : ℝ → ℝ) (x s : ℝ) : ℝ :=
  F s^(k+1) / F x^(k+1)

noncomputable def givenDensity (k : ℕ) (F f : ℝ → ℝ) (x s : ℝ) : ℝ :=
  (k+1:ℝ) * F s^k * f s / F x^(k+1)

noncomputable def gap (k : ℕ) (F f : ℝ → ℝ) (T t : ℝ) : ℝ :=
  (∫ s in 0..t, secondCDF k F s * s * secondDensity k F f s) -
    ∫ x in 0..T, maxDensity k F f x *
      ∫ s in 0..min t x, givenCDF k F x s * s * givenDensity k F f x s


theorem main : ∀ (k : ℕ) (T : ℝ) (F f : ℝ → ℝ), 0 < T → Distribution T F f →
    ∃ t ∈ Ioo 0 T, gap k F f T t = 0 := by
  sorry

end OMA.S_mo_197896
