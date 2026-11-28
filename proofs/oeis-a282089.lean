import OMAStatements.S_oeis_a282089

open Filter Real
open scoped Topology

namespace OMA.S_oeis_a282089

private noncomputable def angle (n : ℕ) := π / (2:ℝ)^(n+3)

private theorem angle_pos (n : ℕ) : 0<angle n := by unfold angle; positivity

private theorem angle_succ (n : ℕ) : angle (n+1) = angle n/2 := by
  unfold angle
  rw [show n+1+3=(n+3)+1 by omega,pow_succ]
  ring

private theorem angle_le (n : ℕ) : angle n ≤ π/8 := by
  induction n with
  | zero => norm_num [angle]
  | succ n ih => rw [angle_succ]; linarith [angle_pos n]

private theorem a_radical (n : ℕ) : a n = sqrtTwoAddSeries 0 (n+1) := by
  induction n with
  | zero => simp [a,sqrtTwoAddSeries]
  | succ n ih => rw [a,sqrtTwoAddSeries,ih]

private theorem b_tan (n : ℕ) : b n = tan (angle n) := by
  rw [b,a_radical,a_radical,tan_eq_sin_div_cos]
  have hs := sin_pi_over_two_pow_succ (n+1)
  have hc := cos_pi_over_two_pow (n+2)
  change sin (angle n) = _ at hs
  change cos (angle n) = _ at hc
  rw [hs,hc]
  ring

private theorem no_pole {x : ℝ} (hl : -(π/2)<x) (hr : x<π/2) :
    ∀ k : ℤ, x ≠ (2*k+1)*π/2 := by
  intro k he
  exact (cos_pos_of_mem_Ioo ⟨hl,hr⟩).ne' (cos_eq_zero_iff.mpr ⟨k,he⟩)

private theorem c_tan (n : ℕ) : c n = tan (π/4-angle n) := by
  induction n with
  | zero =>
    rw [c,b_tan]
    congr 1
    simp [angle]
    ring
  | succ n ih =>
    rw [c,ih,b_tan]
    have h := angle_pos n
    have h' := angle_le n
    have h₁ : -(π/2)<π/4-angle n := by linarith [pi_pos]
    have h₂ : π/4-angle n<π/2 := by linarith [pi_pos]
    have h₃ : -(π/2)<angle (n+1) := by linarith [angle_pos (n+1),pi_pos]
    have h₄ : angle (n+1)<π/2 := by linarith [angle_le (n+1),pi_pos]
    rw [← tan_add' ⟨no_pole h₁ h₂,no_pole h₃ h₄⟩, angle_succ]
    congr 1
    ring

private theorem scaled_limit : Tendsto (fun n : ℕ => (2:ℝ)^(n+2)*(1-c n)) atTop (𝓝 π) := by
  have ha : Tendsto angle atTop (𝓝 0) := by
    have hg := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1:ℝ)/2<1)
    have ht := hg.const_mul (π/8)
    change Tendsto (fun n : ℕ => π/(2:ℝ)^(n+3)) atTop (𝓝 0)
    convert ht using 1
    · ext n
      rw [pow_add, div_pow]
      norm_num
      ring
    · simp
  have hn : Tendsto (fun n => -angle n) atTop (𝓝[<] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨by simpa using ha.neg, Eventually.of_forall ?_⟩
    intro n
    exact neg_lt_zero.mpr (angle_pos n)
  have hd : HasDerivAt tan 2 (π/4) := by
    have hp : cos (π/4) ≠ 0 := (cos_pos_of_mem_Ioo ⟨by linarith [pi_pos],by linarith [pi_pos]⟩).ne'
    convert (hasDerivAt_tan hp) using 1
    rw [cos_pi_div_four]
    norm_num [div_pow]
  have ht := hd.tendsto_slope_zero_left.comp hn
  have hres := ht.const_mul (π/2)
  convert hres using 1
  · ext n
    simp only [Function.comp_apply, smul_eq_mul, tan_pi_div_four, ← sub_eq_add_neg, ← c_tan]
    unfold angle
    field_simp [Real.pi_ne_zero]
    ring
  · ring_nf

private theorem series_converges : Summable (fun n : ℕ => 1-c n) := by
  have hb := scaled_limit.norm.eventually_lt_const (show ‖π‖ < π+1 by rw [Real.norm_eq_abs,abs_of_pos pi_pos]; linarith)
  have hs := (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1:ℝ)/2<1)).mul_left ((π+1)/4)
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [hb] with n hn
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (by positivity)] at hn
  rw [div_pow,one_pow,pow_add] at *
  norm_num at *
  apply (le_div_iff₀ (by positivity : 0<(2:ℝ)^n)).mpr
  nlinarith

end OMA.S_oeis_a282089

open OMA.S_oeis_a282089 in
theorem OMA.solution : type_of% @OMA.S_oeis_a282089.main := ⟨scaled_limit,series_converges⟩
