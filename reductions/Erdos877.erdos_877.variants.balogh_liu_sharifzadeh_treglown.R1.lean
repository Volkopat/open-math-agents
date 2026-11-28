import FormalConjectures.ErdosProblems.«877»

/-!
Reduction R1 of `Erdos877.erdos_877.variants.balogh_liu_sharifzadeh_treglown`.

The exponent `1/4` in Balogh–Liu–Sharifzadeh–Treglown has two sides.
* H1, the lower bound: `2^(n/4) < f_m(n)` for all large `n`. This is the statement of
  `erdos_877.variants.cameron_erdos` (Cameron–Erdős): every subset of the odd numbers in the
  upper half extends to a distinct maximal sum-free set.
* H2, the upper bound: for every `ε > 0`, `f_m(n) ≤ 2^((1/4 + ε) n)` for all large `n`. This is the
  container-method part of [BLST15].

Together they give `log₂ f_m(n) / n → 1/4`: the ratio lies in `(1/4, 1/4 + ε]` for all large `n`.
-/

namespace OMA.R_Erdos877_erdos_877_variants_balogh_liu_sharifzadeh_treglown_R1

open Filter Real

/-- The Cameron–Erdős lower bound. -/
def H1 : Prop := ∀ᶠ n : ℕ in atTop, (2 : ℝ) ^ ((n : ℝ) / 4) < Erdos877.fm n

/-- The upper bound of Balogh, Liu, Sharifzadeh and Treglown. -/
def H2 : Prop := ∀ ε : ℝ, 0 < ε →
  ∀ᶠ n : ℕ in atTop, (Erdos877.fm n : ℝ) ≤ (2 : ℝ) ^ ((1 / 4 + ε) * n)

theorem main : H1 → H2 →
    type_of% @Erdos877.erdos_877.variants.balogh_liu_sharifzadeh_treglown := by
  intro h1 h2
  rw [tendsto_order]
  have hlow : ∀ᶠ n : ℕ in atTop, (1 / 4 : ℝ) < logb 2 (Erdos877.fm n) / n := by
    filter_upwards [h1, eventually_gt_atTop 0] with n hn hn0
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    have hpos : (0 : ℝ) < (2 : ℝ) ^ ((n : ℝ) / 4) := by positivity
    have hlog : (n : ℝ) / 4 < logb 2 (Erdos877.fm n) := by
      have := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2) hpos hn
      rwa [Real.logb_rpow (by norm_num) (by norm_num)] at this
    rw [lt_div_iff₀ hn']
    linarith
  refine ⟨fun a ha => hlow.mono fun n hn => ha.trans hn, fun b hb => ?_⟩
  have hε : (0 : ℝ) < (b - 1 / 4) / 2 := by linarith
  filter_upwards [h1, h2 _ hε, eventually_gt_atTop 0] with n hn hup hn0
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hpos : (0 : ℝ) < Erdos877.fm n := lt_trans (by positivity) hn
  have hlog : logb 2 (Erdos877.fm n) ≤ (1 / 4 + (b - 1 / 4) / 2) * n := by
    have := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hpos hup
    rwa [Real.logb_rpow (by norm_num) (by norm_num)] at this
  rw [div_lt_iff₀ hn']
  nlinarith

end OMA.R_Erdos877_erdos_877_variants_balogh_liu_sharifzadeh_treglown_R1
