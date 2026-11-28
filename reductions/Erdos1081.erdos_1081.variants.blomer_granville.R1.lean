import FormalConjectures.ErdosProblems.«1081»
import Mathlib

/-!
Blomer and Granville (2006) on the counting function of sums of two squarefull numbers, split
into its two halves.

[BlGr06] proves the two-sided estimate: `A x` lies between `(log log x)^(-C)` and
`(log log x)^C` times `x / (log x)^alpha` for one constant `C`. The lower and the upper estimate
are independent results, each with a constant of its own; this reduction states them separately
(`H1`, `H2`) and combines them in `main` by taking the larger of the two constants. This is
legitimate because both sides get *easier* as the exponent `C` grows: for large `x` one has
`log log x >= 1`, so `(log log x)^C` is monotone in `C`, and it divides the lower side and
multiplies the upper side.
-/

-- Reduction Erdos1081.erdos_1081.variants.blomer_granville.R1 of Erdős Problem 1081 — blomer granville
-- Credit: @B221393
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_Erdos1081_erdos_1081_variants_blomer_granville_R1

open Filter

/-- The lower estimate of [BlGr06]: some constant `C > 0` with
`x / (log x)^alpha / (log log x)^C <= A x` for all large `x`. -/
def H1 : Prop := ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
  x / Real.log x ^ Erdos1081.alpha / Real.log (Real.log x) ^ C ≤ (Erdos1081.A x : ℝ)

/-- The upper estimate of [BlGr06]: some constant `C > 0` with
`A x <= x / (log x)^alpha * (log log x)^C` for all large `x`. -/
def H2 : Prop := ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
  (Erdos1081.A x : ℝ) ≤ x / Real.log x ^ Erdos1081.alpha * Real.log (Real.log x) ^ C

theorem main : H1 → H2 → type_of% @Erdos1081.erdos_1081.variants.blomer_granville := by
  rintro ⟨C₁, hC₁, hlow⟩ ⟨C₂, hC₂, hup⟩
  refine ⟨max C₁ C₂, lt_max_of_lt_left hC₁, ?_⟩
  have hloglog : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log (Real.log x) :=
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually
      (eventually_ge_atTop (1 : ℝ))
  have hxpos : ∀ᶠ x : ℝ in atTop, 0 < x := eventually_gt_atTop (0 : ℝ)
  have hlogpos : ∀ᶠ x : ℝ in atTop, 0 < Real.log x :=
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0 : ℝ))
  filter_upwards [hlow, hup, hloglog, hxpos, hlogpos] with x hlow hup hloglog hxpos hlogpos
  have hL : 0 < Real.log x ^ Erdos1081.alpha := Real.rpow_pos_of_pos hlogpos _
  have hbase : 0 ≤ x / Real.log x ^ Erdos1081.alpha := (div_pos hxpos hL).le
  constructor
  · refine le_trans ?_ hlow
    gcongr
    exact le_max_left C₁ C₂
  · refine le_trans hup ?_
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hloglog (le_max_right C₁ C₂)) hbase

end OMA.R_Erdos1081_erdos_1081_variants_blomer_granville_R1
