import FormalConjectures.ErdosProblems.«1057»

-- Reduction Erdos1057.erdos_1057.variants.pomerance.R1 of Erdős Problem 1057 — pomerance
-- Credit: @chris01-dev
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Write A(x) = log x * log log log x / log log x, so that L(x) = exp (A x) is the usual
-- function of Pomerance. The target says log (x / C(x)) / A(x) tends to 1. It is the
-- conjunction of two one-sided bounds of very different status.
--
-- H1 (known theorem): C(x) <= x / L(x)^(1 - eps) for every eps > 0 and all large x.
--   Pomerance, Selfridge and Wagstaff, The pseudoprimes to 25 * 10^9, Math. Comp. 35 (1980),
--   Theorem 6. This is the sharp form of the upper bound of Erdős; the variant upper_bound of
--   the same file only asks for some unspecified constant in place of 1 - eps.
--
-- H2 (open): C(x) >= x / L(x)^(1 + eps) for every eps > 0 and all large x.
--   This is the open core. It implies C(x) = x^(1 - o(1)), the main statement of Erdős
--   Problem 1057, while the best known lower bound is x^0.3389 (Lichtman 2022).

namespace OMA.R_Erdos1057_erdos_1057_variants_pomerance_R1

open Filter Topology

/-- Sharp upper bound (Pomerance, Selfridge and Wagstaff 1980). -/
def H1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop,
    Erdos1057.carmichaelCounting x ≤
      x * Real.exp (-(1 - ε) *
        (Real.log x * Real.log (Real.log (Real.log x)) / Real.log (Real.log x)))

/-- Matching lower bound (open: the heuristic of Pomerance). -/
def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop,
    x * Real.exp (-(1 + ε) *
        (Real.log x * Real.log (Real.log (Real.log x)) / Real.log (Real.log x))) ≤
      Erdos1057.carmichaelCounting x

theorem main : H1 → H2 → type_of% @Erdos1057.erdos_1057.variants.pomerance := by
  intro h1 h2
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  have hlll : ∀ᶠ x : ℝ in atTop, 0 < Real.log (Real.log (Real.log x)) :=
    (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp
      Real.tendsto_log_atTop)).eventually_gt_atTop 0
  have hll : ∀ᶠ x : ℝ in atTop, 0 < Real.log (Real.log x) :=
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_gt_atTop 0
  have hl : ∀ᶠ x : ℝ in atTop, 0 < Real.log x := Real.tendsto_log_atTop.eventually_gt_atTop 0
  filter_upwards [h1 (ε / 2) hε2, h2 (ε / 2) hε2, hlll, hll, hl, eventually_gt_atTop (0 : ℝ)]
    with x hup hlow hv hu ht hx
  have hA : 0 < Real.log x * Real.log (Real.log (Real.log x)) / Real.log (Real.log x) :=
    div_pos (mul_pos ht hv) hu
  have hden : 0 < Real.log x * Real.log (Real.log (Real.log x)) := mul_pos ht hv
  have hC : 0 < Erdos1057.carmichaelCounting x :=
    lt_of_lt_of_le (mul_pos hx (Real.exp_pos _)) hlow
  have hq : 0 < Erdos1057.carmichaelCounting x / x := div_pos hC hx
  have hlogle : Real.log (Erdos1057.carmichaelCounting x / x) ≤
      -(1 - ε / 2) *
        (Real.log x * Real.log (Real.log (Real.log x)) / Real.log (Real.log x)) := by
    rw [← Real.log_exp (-(1 - ε / 2) *
        (Real.log x * Real.log (Real.log (Real.log x)) / Real.log (Real.log x)))]
    apply Real.log_le_log hq
    rw [div_le_iff₀ hx]
    linarith [hup]
  have hlogge : -(1 + ε / 2) *
        (Real.log x * Real.log (Real.log (Real.log x)) / Real.log (Real.log x)) ≤
      Real.log (Erdos1057.carmichaelCounting x / x) := by
    rw [← Real.log_exp (-(1 + ε / 2) *
        (Real.log x * Real.log (Real.log (Real.log x)) / Real.log (Real.log x)))]
    apply Real.log_le_log (Real.exp_pos _)
    rw [le_div_iff₀ hx]
    linarith [hlow]
  have hmul : Real.log x * Real.log (Real.log (Real.log x)) / Real.log (Real.log x) *
      Real.log (Real.log x) = Real.log x * Real.log (Real.log (Real.log x)) := by
    field_simp
  rw [Real.dist_eq, abs_lt]
  constructor
  · rw [lt_sub_iff_add_lt, lt_div_iff₀ hden]
    nlinarith [mul_le_mul_of_nonneg_right hlogle hu.le]
  · rw [sub_lt_iff_lt_add, div_lt_iff₀ hden]
    nlinarith [mul_le_mul_of_nonneg_right hlogge hu.le]

end OMA.R_Erdos1057_erdos_1057_variants_pomerance_R1
