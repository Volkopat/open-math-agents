import OMAStatements.S_oeis_a248521
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
The difference of consecutive cotangents tends to 2/π. Thus consecutive
floors eventually differ by zero or one. Counting the unit differences
telescopes and gives density 2/π. Inverting this count gives the claimed
asymptotic for the increasing sequence of their indices.
-/

open Filter Topology
open OMA.S_oeis_a248521

namespace CotangentIndices

noncomputable def angle (n : ℕ) : ℝ := Real.pi / (2 * (n : ℝ))

lemma angle_pos {n : ℕ} (hn : 0 < n) : 0 < angle n := by
  unfold angle
  positivity

lemma sin_angle_pos {n : ℕ} (hn : 0 < n) : 0 < Real.sin (angle n) := by
  apply Real.sin_pos_of_pos_of_lt_pi (angle_pos hn)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  unfold angle
  apply (div_lt_iff₀ (by positivity)).2
  nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_left hn' Real.pi_pos.le]

lemma angle_limit : Tendsto angle atTop (𝓝 0) := by
  apply (tendsto_const_div_atTop_nhds_zero_nat (Real.pi / 2)).congr
  intro n
  unfold angle
  ring

lemma sinc_limit {f : ℕ → ℝ} (h : Tendsto f atTop (𝓝 0)) :
    Tendsto (fun n => Real.sinc (f n)) atTop (𝓝 1) := by
  simpa only [Real.sinc_zero, Function.comp_def] using
    (Real.continuous_sinc.tendsto 0).comp h

lemma cotangent_ratio :
    Tendsto (fun n : ℕ => Real.cot (angle n) / n) atTop (𝓝 (2 / Real.pi)) := by
  have hc : Tendsto (fun n => Real.cos (angle n)) atTop (𝓝 1) := by
    simpa only [Function.comp_def, Real.cos_zero] using
      (Real.continuous_cos.tendsto 0).comp angle_limit
  have h := (hc.div (sinc_limit angle_limit) one_ne_zero).const_mul (2 / Real.pi)
  rw [div_one, mul_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have ha := (angle_pos hn).ne'
  have hs := (sin_angle_pos hn).ne'
  change 2 / Real.pi * (Real.cos (angle n) / Real.sinc (angle n)) =
    Real.cot (angle n) / (n : ℝ)
  rw [Real.sinc_of_ne_zero ha, Real.cot_eq_cos_div_sin]
  have cancel : angle n * (2 * (n : ℝ)) = Real.pi := by
    unfold angle
    field_simp
  field_simp [Real.pi_ne_zero, ha, hs, hn']
  linear_combination Real.cos (angle n) * cancel

lemma gap_formula {n : ℕ} (hn : 0 < n) :
    Real.cot (angle (n+1)) - Real.cot (angle n) =
      (2 / Real.pi) * Real.sinc (angle n - angle (n+1)) /
        (Real.sinc (angle (n+1)) * Real.sinc (angle n)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have ha := (angle_pos (Nat.succ_pos n)).ne'
  have hb := (angle_pos hn).ne'
  have hsa := (sin_angle_pos (Nat.succ_pos n)).ne'
  have hsb := (sin_angle_pos hn).ne'
  have step : angle n - angle (n+1) =
      (2 / Real.pi) * angle (n+1) * angle n := by
    unfold angle
    push_cast
    field_simp [Real.pi_ne_zero, hn'.ne', (by positivity : (n : ℝ)+1 ≠ 0)]
    <;> ring
  have hdiff : angle n - angle (n+1) ≠ 0 := by
    rw [step]
    exact mul_ne_zero (mul_ne_zero (div_ne_zero (by norm_num) Real.pi_ne_zero) ha) hb
  have scaled : Real.pi * (angle n - angle (n+1)) = 2 * angle (n+1) * angle n := by
    rw [step]
    field_simp [Real.pi_ne_zero]
  calc
    _ = Real.sin (angle n - angle (n+1)) /
          (Real.sin (angle (n+1)) * Real.sin (angle n)) := by
      rw [Real.sin_sub, Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin]
      field_simp [hsa, hsb]
      <;> ring
    _ = _ := by
      rw [Real.sinc_of_ne_zero hdiff, Real.sinc_of_ne_zero ha, Real.sinc_of_ne_zero hb]
      field_simp [Real.pi_ne_zero, hsa, hsb, ha, hb, hdiff]
      linear_combination Real.sin (angle n-angle (n+1)) * scaled

lemma cotangent_gap :
    Tendsto (fun n : ℕ => Real.cot (angle (n+1)) - Real.cot (angle n))
      atTop (𝓝 (2 / Real.pi)) := by
  have hnext : Tendsto (fun n : ℕ => angle (n+1)) atTop (𝓝 0) :=
    angle_limit.comp (tendsto_add_atTop_nat 1)
  have hdiff := angle_limit.sub hnext
  rw [sub_zero] at hdiff
  have h := ((sinc_limit hdiff).const_mul (2 / Real.pi)).div
    ((sinc_limit hnext).mul (sinc_limit angle_limit)) (by norm_num)
  simp only [mul_one, div_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact (gap_formula hn).symm

lemma floor_ratio :
    Tendsto (fun n : ℕ => (height n : ℝ) / (n : ℝ)) atTop (𝓝 (2 / Real.pi)) := by
  have low := cotangent_ratio.sub (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  rw [sub_zero] at low
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' low cotangent_ratio
  · filter_upwards [eventually_gt_atTop 0] with n hn
    rw [← sub_div]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    have h := Int.lt_floor_add_one (Real.cot (angle n))
    change Real.cot (angle n) - 1 ≤ (⌊Real.cot (angle n)⌋ : ℤ)
    linarith
  · filter_upwards with n
    exact div_le_div_of_nonneg_right (Int.floor_le _) (Nat.cast_nonneg n)

lemma floor_steps : ∀ᶠ n : ℕ in atTop,
    height (n+1) = height n ∨ height (n+1) = height n + 1 := by
  have hpos : 0 < 2 / Real.pi := by positivity
  have hlt : 2 / Real.pi < 1 := by
    apply (div_lt_iff₀ Real.pi_pos).2
    linarith [Real.pi_gt_three]
  filter_upwards [cotangent_gap.eventually_const_lt hpos,
    cotangent_gap.eventually_lt_const hlt] with n lo hi
  change 0 < Real.cot (angle (n+1)) - Real.cot (angle n) at lo
  change Real.cot (angle (n+1)) - Real.cot (angle n) < 1 at hi
  have lb : height n ≤ height (n+1) :=
    Int.floor_mono (show Real.cot (angle n) ≤ Real.cot (angle (n+1)) by linarith)
  have ub : height (n+1) < height n + 2 := by
    apply Int.floor_lt.mpr
    have h := Int.lt_floor_add_one (Real.cot (angle n))
    change Real.cot (angle (n+1)) < ((⌊Real.cot (angle n)⌋ + 2 : ℤ) : ℝ)
    push_cast
    linarith
  omega

lemma count_from_steps (p : ℕ → Prop) [DecidablePred p] (H : ℕ → ℤ)
    (steps : ∀ᶠ n : ℕ in atTop, H (n+1) = H n + (if p n then 1 else 0)) :
    ∃ c : ℤ, ∀ᶠ n : ℕ in atTop, (Nat.count p n : ℤ) = H n + c := by
  obtain ⟨b, hb⟩ := eventually_atTop.1 steps
  refine ⟨(Nat.count p b : ℤ) - H b, eventually_atTop.2 ⟨b, ?_⟩⟩
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => omega
  | succ n hn ih =>
    rw [Nat.count_succ, Nat.cast_add, hb n hn]
    split <;> rename_i h
    all_goals simp [h] at * <;> omega

lemma enumeration (p : ℕ → Prop) [DecidablePred p] {s : ℝ} (hs : 0 < s)
    (hc : Tendsto (fun n : ℕ => (Nat.count p n : ℝ) / n) atTop (𝓝 s)) :
    Tendsto (fun n : ℕ => (Nat.nth p n : ℝ) / ((n : ℝ)+1)) atTop (𝓝 s⁻¹) := by
  classical
  have hinf : (Set.ofPred p).Infinite := by
    intro hfin
    have hzero : Tendsto (fun n : ℕ => (Nat.count p n : ℝ) / n) atTop (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        (tendsto_const_div_atTop_nhds_zero_nat (hfin.toFinset.card : ℝ))
      · filter_upwards with n
        positivity
      · filter_upwards with n
        exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.count_le_card hfin n)
          (Nat.cast_nonneg n)
    exact hs.ne' (tendsto_nhds_unique hc hzero)
  have hsub := hc.comp (Nat.nth_strictMono hinf).tendsto_atTop
  have hrat : Tendsto (fun n : ℕ => (n : ℝ) / (Nat.nth p n : ℝ)) atTop (𝓝 s) := by
    simpa only [Function.comp_def, Nat.count_nth_of_infinite hinf] using hsub
  have h := (hrat.inv₀ hs.ne').mul (tendsto_natCast_div_add_atTop (1:ℝ))
  rw [mul_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  change ((n : ℝ) / (Nat.nth p n : ℝ))⁻¹ * ((n : ℝ)/((n:ℝ)+1)) = _
  rw [inv_div, div_mul_div_cancel₀ hn']

lemma count_ratio (p : ℕ → Prop) [DecidablePred p] (H : ℕ → ℤ) {s : ℝ}
    (hlim : Tendsto (fun n : ℕ => (H n : ℝ)/n) atTop (𝓝 s))
    (steps : ∀ᶠ n : ℕ in atTop, H (n+1) = H n + (if p n then 1 else 0)) :
    Tendsto (fun n : ℕ => (Nat.count p n : ℝ)/n) atTop (𝓝 s) := by
  obtain ⟨c, hc⟩ := count_from_steps p H steps
  have h := hlim.add (tendsto_const_div_atTop_nhds_zero_nat (c : ℝ))
  rw [add_zero] at h
  apply h.congr'
  filter_upwards [hc] with n heq
  change (H n : ℝ)/n + (c : ℝ)/n = _
  rw [← add_div]
  congr 1
  exact_mod_cast heq.symm

end CotangentIndices

open CotangentIndices

theorem OMA.solution : type_of% @OMA.S_oeis_a248521.main := by
  classical
  have h := enumeration selected (show 0 < 2 / Real.pi by positivity)
  rw [inv_div] at h
  apply h
  apply count_ratio selected height floor_ratio
  filter_upwards [floor_steps, eventually_gt_atTop 0] with n step hn
  by_cases up : height (n+1) = height n+1
  · simpa [selected, hn, up] using up
  · simpa [selected, hn, up] using step.resolve_right up
