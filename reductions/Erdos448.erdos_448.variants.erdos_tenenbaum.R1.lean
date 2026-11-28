import FormalConjectures.ErdosProblems.«448»

/-! # Lower and upper density estimates for the Erdős–Tenenbaum limit -/

-- Credit: @deepqntm

namespace OMA.R_Erdos448_erdos_448_variants_erdos_tenenbaum_R1

open Erdos448 Filter Real Set Topology

/-- The lower power bound for the density of integers with unusually few occupied dyadic blocks. -/
def H1 : Prop :=
  ∀ p : ℝ, 1 < p → ∀ᶠ ε : ℝ in 𝓝[>] 0,
    ε ^ p ≤ {n : ℕ | (tauPlus n : ℝ) < ε * (n.divisors.card : ℝ)}.upperDensity

/-- The upper power bound from Erdős and Tenenbaum's Theorem 1. -/
def H2 : Prop :=
  ∀ η : ℝ, 0 < η → ∃ C > 0, ∀ᶠ ε : ℝ in 𝓝[>] 0,
    {n : ℕ | (tauPlus n : ℝ) < ε * (n.divisors.card : ℝ)}.upperDensity ≤ C * ε ^ (1 - η)

theorem main : H1 → H2 → type_of% @Erdos448.erdos_448.variants.erdos_tenenbaum := by
  intro lower upper
  let smallRatio (ε : ℝ) : Set ℕ := {n | (tauPlus n : ℝ) < ε * (n.divisors.card : ℝ)}
  change Tendsto (fun ε : ℝ => log (smallRatio ε).upperDensity / log ε) (𝓝[>] 0) (𝓝 1)
  have h01 : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ ε < 1 := by
    have hlo : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
    have hhi : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < 1 :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
    exact hlo.and hhi
  apply tendsto_order.mpr
  constructor
  · intro a ha
    let η := (1 - a) / 2
    have hη : 0 < η := by dsimp [η]; linarith
    obtain ⟨C, hC, hupper⟩ := upper η hη
    have hlog := ((tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero).atTop_mul_const hη).eventually
      (eventually_gt_atTop (log C))
    filter_upwards [h01, hupper, hlog, lower 2 (by norm_num)] with ε hε hU hCε hL
    have hD := lt_of_lt_of_le (Real.rpow_pos_of_pos hε.1 2) hL
    have hbound := Real.log_le_log hD hU
    rw [Real.log_mul hC.ne' (Real.rpow_pos_of_pos hε.1 _).ne', Real.log_rpow hε.1] at hbound
    have hneg := Real.log_neg hε.1 hε.2
    apply (lt_div_iff_of_neg hneg).mpr
    change log C < -log ε * η at hCε
    dsimp [η] at hCε hbound
    linarith
  · intro b hb
    let p := (1 + b) / 2
    have hp : 1 < p := by dsimp [p]; linarith
    filter_upwards [h01, lower p hp] with ε hε hL
    have hbound := Real.log_le_log (Real.rpow_pos_of_pos hε.1 p) hL
    rw [Real.log_rpow hε.1] at hbound
    have hneg := Real.log_neg hε.1 hε.2
    apply (div_lt_iff_of_neg hneg).mpr
    exact lt_of_lt_of_le (mul_lt_mul_of_neg_right (by dsimp [p]; linarith : p < b) hneg) hbound

end OMA.R_Erdos448_erdos_448_variants_erdos_tenenbaum_R1
