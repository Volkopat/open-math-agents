import FormalConjectures.ErdosProblems.«441»

/-!
The two-sided estimate of Chen and Dai splits into the lower bound from Erdős' construction and the one-sided
upper bound. For N at least 21 the comparison function sqrt(N / log N) * log log N is at least 1, so the constant
from the lower bound is absorbed.
-/

namespace OMA.R_Erdos441_erdos_441_variants_chen_dai_upper_bound_R1

open Filter Asymptotics

/-- The lower bound from Erdős' construction. -/
def H1 : Prop := ∃ C : ℝ, ∀ N : ℕ, √(9 / 8 * N) - C ≤ Erdos441.g N

/-- The one-sided upper bound of Chen and Dai. -/
def H2 : Prop := ∃ C : ℝ, ∀ᶠ N : ℕ in atTop,
  (Erdos441.g N : ℝ) ≤ √(9 / 8 * N) + C * (√(N / Real.log N) * Real.log (Real.log N))

lemma scale_ge_one (N : ℕ) (hN : 21 ≤ N) :
    1 ≤ √((N : ℝ) / Real.log N) * Real.log (Real.log N) := by
  have hNR : (21 : ℝ) ≤ N := by exact_mod_cast hN
  have he3 : Real.exp 3 ≤ 21 := by
    have h1 : Real.exp 3 = Real.exp 1 ^ 3 := by
      rw [← Real.exp_nat_mul]
      norm_num
    have h2 : Real.exp 1 ≤ 2.7183 := by
      have := Real.exp_one_lt_d9
      linarith
    rw [h1]
    calc Real.exp 1 ^ 3 ≤ (2.7183 : ℝ) ^ 3 := pow_le_pow_left₀ (Real.exp_pos 1).le h2 3
      _ ≤ 21 := by norm_num
  have hlog3 : 3 ≤ Real.log N := by
    have h := Real.log_le_log (Real.exp_pos 3) (he3.trans hNR)
    rwa [Real.log_exp] at h
  have hloglog : 1 ≤ Real.log (Real.log N) := by
    have he : Real.exp 1 ≤ Real.log N := by
      have := Real.exp_one_lt_d9
      linarith
    have h := Real.log_le_log (Real.exp_pos 1) he
    rwa [Real.log_exp] at h
  have hlogle : Real.log N ≤ N := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hsq : 1 ≤ √((N : ℝ) / Real.log N) := by
    rw [Real.one_le_sqrt, le_div_iff₀ (by linarith)]
    linarith
  calc (1 : ℝ) = 1 * 1 := by norm_num
    _ ≤ _ := mul_le_mul hsq hloglog (by norm_num) (by positivity)

theorem main : H1 → H2 → type_of% @Erdos441.erdos_441.variants.chen_dai_upper_bound := by
  rintro ⟨C₁, h1⟩ ⟨C₂, h2⟩
  apply IsBigO.of_bound (|C₁| + |C₂|)
  filter_upwards [h2, eventually_ge_atTop 21] with N hN hN21
  have hE := scale_ge_one N hN21
  have hE0 : 0 ≤ √((N : ℝ) / Real.log N) * Real.log (Real.log N) := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hE0, abs_le]
  have hlow := h1 N
  have ha1 : |C₁| ≤ |C₁| * (√((N : ℝ) / Real.log N) * Real.log (Real.log N)) :=
    le_mul_of_one_le_right (abs_nonneg _) hE
  have ha2 : C₂ * (√((N : ℝ) / Real.log N) * Real.log (Real.log N)) ≤
      |C₂| * (√((N : ℝ) / Real.log N) * Real.log (Real.log N)) :=
    mul_le_mul_of_nonneg_right (le_abs_self _) hE0
  have ha3 : 0 ≤ |C₂| * (√((N : ℝ) / Real.log N) * Real.log (Real.log N)) :=
    mul_nonneg (abs_nonneg _) hE0
  have ha4 : 0 ≤ |C₁| * (√((N : ℝ) / Real.log N) * Real.log (Real.log N)) :=
    mul_nonneg (abs_nonneg _) hE0
  have hc1 := le_abs_self C₁
  constructor
  · rw [add_mul]
    linarith
  · rw [add_mul]
    linarith

end OMA.R_Erdos441_erdos_441_variants_chen_dai_upper_bound_R1
