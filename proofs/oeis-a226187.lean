import OMAStatements.S_oeis_a226187
import Mathlib

/-!
# Hickerson's harmonic-number estimate

The two bounds are recorded in OEIS A002387. They follow by comparing
successive errors using two terms of the logarithm series. The errors
decrease to Euler's constant, while subtracting the proposed remainder
gives a sequence increasing to the same limit.

Source: https://oeis.org/A002387
-/

namespace HarmonicThreshold

open Filter Real
open scoped Topology

private theorem rationalBound (m : ℝ) (hm : 2 ≤ m) :
    let x := 1 / (2 * m)
    2 * (x ^ 3 / 3 + x ^ 5 / (1 - x ^ 2)) <
      1 / (24 * (m - 1) ^ 2) - 1 / (24 * m ^ 2) := by
  dsimp only
  have hm0 : 0 < m := by linarith
  have hm1 : 0 < m - 1 := by linarith
  have hquad : 0 < 4 * m ^ 2 - 1 := by nlinarith
  have hsquare : 1 - (1 / (2 * m)) ^ 2 = (4 * m ^ 2 - 1) / (4 * m ^ 2) := by
    field_simp [hm0.ne']
    ring
  have hl : 2 * ((1 / (2 * m)) ^ 3 / 3 + (1 / (2 * m)) ^ 5 / (1 - (1 / (2 * m)) ^ 2)) =
      (2 * m ^ 2 + 1) / (6 * m ^ 3 * (4 * m ^ 2 - 1)) := by
    rw [hsquare, div_div_eq_mul_div]
    generalize hD : 4 * m ^ 2 - 1 = denom
    have hdenom : denom ≠ 0 := hD ▸ hquad.ne'
    field_simp [hm0.ne', hdenom]
    rw [← hD]
    ring
  have hr : 1 / (24 * (m - 1) ^ 2) - 1 / (24 * m ^ 2) =
      (2 * m - 1) / (24 * m ^ 2 * (m - 1) ^ 2) := by
    field_simp [hm0.ne', hm1.ne']
    ring
  rw [hl, hr]
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
  have hlin₁ : 0 < 6 * m - 7 := by linarith
  have hlin₂ : 0 < 9 * m - 4 := by linarith
  have hp : 0 < 6 * m ^ 2 * (2 * m ^ 2 * (6 * m - 7) + (9 * m - 4)) := by positivity
  calc
    _ < (2 * m ^ 2 + 1) * (24 * m ^ 2 * (m - 1) ^ 2) +
        6 * m ^ 2 * (2 * m ^ 2 * (6 * m - 7) + (9 * m - 4)) := lt_add_of_pos_right _ hp
    _ = _ := by ring

private theorem logStep (m : ℝ) (hm : 2 ≤ m) :
    0 < log (m + 1 / 2) - log (m - 1 / 2) - 1 / m ∧
    log (m + 1 / 2) - log (m - 1 / 2) - 1 / m <
      1 / (24 * (m - 1) ^ 2) - 1 / (24 * m ^ 2) := by
  let x : ℝ := 1 / (2 * m)
  have hm0 : 0 < m := by linarith
  have hx0 : 0 < x := by dsimp [x]; positivity
  have hx1 : x < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  have hratio : (1 + x) / (1 - x) = (m + 1 / 2) / (m - 1 / 2) := by
    have hmhalf : 0 < m - 1 / 2 := by linarith
    dsimp only [x]
    field_simp [hm0.ne', hmhalf.ne']
  have hlog : log ((1 + x) / (1 - x)) = log (m + 1 / 2) - log (m - 1 / 2) := by
    rw [hratio, log_div (by linarith : m + 1 / 2 ≠ 0) (by linarith : m - 1 / 2 ≠ 0)]
  have hx2 : 2 * x = 1 / m := by dsimp only [x]; ring
  have hlow := sum_range_le_log_div hx0.le hx1 2
  have hupp := log_div_le_sum_range_add hx0.le hx1 2
  norm_num [Finset.sum_range_succ] at hlow hupp
  rw [hlog] at hlow hupp
  have hpos : 0 < x ^ 3 / 3 := by positivity
  have hrat := rationalBound m hm
  change 2 * (x ^ 3 / 3 + x ^ 5 / (1 - x ^ 2)) < _ at hrat
  constructor <;> linarith

private theorem shiftedHarmonicLimit :
    Tendsto (fun k : ℕ => (harmonic k : ℝ) - log ((k : ℝ) + 1 / 2)) atTop
      (𝓝 eulerMascheroniConstant) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_harmonic_sub_log_add_one
    tendsto_harmonic_sub_log ?_ ?_
  · filter_upwards with k
    have h : log ((k : ℝ) + 1 / 2) ≤ log ((k : ℝ) + 1) :=
      log_le_log (by positivity) (by linarith)
    linarith
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with k hk
    have h : log (k : ℝ) ≤ log ((k : ℝ) + 1 / 2) :=
      log_le_log (by exact_mod_cast hk) (by linarith)
    linarith

/-- The error in the half-integer approximation to the harmonic numbers. -/
theorem estimate (k : ℕ) (hk : 0 < k) :
    log ((k : ℝ) + 1 / 2) + eulerMascheroniConstant < (harmonic k : ℝ) ∧
    (harmonic k : ℝ) <
      log ((k : ℝ) + 1 / 2) + eulerMascheroniConstant + 1 / (24 * (k : ℝ) ^ 2) := by
  let d (j : ℕ) : ℝ := (harmonic (j + 1) : ℝ) - log ((j : ℝ) + 1 + 1 / 2)
  let e (j : ℕ) : ℝ := d j - 1 / (24 * ((j : ℝ) + 1) ^ 2)
  have hd : Tendsto d atTop (𝓝 eulerMascheroniConstant) := by
    simpa [d, Function.comp_def] using shiftedHarmonicLimit.comp (tendsto_add_atTop_nat 1)
  have hcast : Tendsto (fun j : ℕ => (j : ℝ) + 1) atTop atTop := by
    simpa [Function.comp_def] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hinv := (tendsto_inv_atTop_zero.comp hcast).pow 2
  have hrem : Tendsto (fun j : ℕ => 1 / (24 * ((j : ℝ) + 1) ^ 2)) atTop (𝓝 0) := by
    simpa [Function.comp_def, div_eq_mul_inv, mul_inv_rev, inv_pow, mul_comm] using
      (tendsto_const_nhds (x := (24 : ℝ)⁻¹)).mul hinv
  have he : Tendsto e atTop (𝓝 eulerMascheroniConstant) := by simpa [e] using hd.sub hrem
  have hsteps (j : ℕ) : d (j + 1) < d j ∧ e j < e (j + 1) := by
    have hh := logStep ((j : ℝ) + 2) (by linarith [Nat.cast_nonneg (α := ℝ) j])
    have hsub : (j : ℝ) + 2 - 1 / 2 = (j : ℝ) + 1 + 1 / 2 := by ring
    have hden : (j : ℝ) + 2 - 1 = (j : ℝ) + 1 := by ring
    rw [hsub, hden] at hh
    dsimp only [e, d]
    rw [harmonic_succ (j + 1)]
    push_cast
    have hplus : (j : ℝ) + 1 + 1 = (j : ℝ) + 2 := by ring
    rw [hplus]
    simp only [inv_eq_one_div]
    constructor <;> linarith only [hh.1, hh.2]
  have hda : Antitone d := antitone_nat_of_succ_le fun j => (hsteps j).1.le
  have hem : Monotone e := monotone_nat_of_le_succ fun j => (hsteps j).2.le
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  have hl := lt_of_le_of_lt (hda.le_of_tendsto hd (j + 1)) (hsteps j).1
  have hu := lt_of_lt_of_le (hsteps j).2 (hem.ge_of_tendsto he (j + 1))
  dsimp only [d] at hl
  dsimp only [e, d] at hu
  push_cast
  constructor <;> linarith

end HarmonicThreshold


namespace HarmonicThreshold

open Real

/-- The least positive index crossing a real level lies at or just below the rounded exponential. -/
theorem crossingBounds (t : ℝ) (ht : eulerMascheroniConstant < t) :
    let x := exp (t - eulerMascheroniConstant)
    let m := ⌊x + 1 / 2⌋₊
    let k := sInf {j : ℕ | 0 < j ∧ t < (harmonic j : ℝ)}
    0 < k ∧ m - 1 ≤ k ∧ k ≤ m := by
  let x := exp (t - eulerMascheroniConstant)
  let m := ⌊x + 1 / 2⌋₊
  let S := {j : ℕ | 0 < j ∧ t < (harmonic j : ℝ)}
  let k := sInf S
  have hx : 1 < x := by
    change 1 < exp (t - eulerMascheroniConstant)
    rw [← exp_zero, exp_lt_exp]
    linarith
  have hle : (m : ℝ) ≤ x + 1 / 2 := Nat.floor_le (by linarith)
  have hlt : x + 1 / 2 < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  have hm : 0 < m := by
    by_contra! h
    have hm0 : m = 0 := by omega
    simp [hm0] at hlt
    linarith
  have hlog : t - eulerMascheroniConstant < log ((m : ℝ) + 1 / 2) :=
    (lt_log_iff_exp_lt (by positivity)).mpr (by change x < _; linarith)
  have hmem : m ∈ S := ⟨hm, by linarith [(estimate m hm).1]⟩
  have hk : k ∈ S := Nat.sInf_mem ⟨m, hmem⟩
  refine ⟨hk.1, ?_, Nat.sInf_le hmem⟩
  change m - 1 ≤ k
  by_contra! h
  have hindex : k + 1 + 1 ≤ m := by omega
  have hindexR : (k : ℝ) + 1 + 1 ≤ (m : ℝ) := by exact_mod_cast hindex
  have hu : (k : ℝ) + 1 < x := by linarith
  have hlog' := log_lt_log (show 0 < (k : ℝ) + 1 by positivity) hu
  change log ((k : ℝ) + 1) < log (exp (t - eulerMascheroniConstant)) at hlog'
  rw [log_exp] at hlog'
  have hh := eulerMascheroniSeq_lt_eulerMascheroniConstant k
  unfold eulerMascheroniSeq at hh
  have hcross : t < (harmonic k : ℝ) := hk.2
  linarith

end HarmonicThreshold

namespace OMA.A226187

open OMA.S_oeis_a226187 Filter Real
open scoped Topology

private noncomputable def scale (n : ℕ) : ℝ :=
  exp ((n : ℝ) / 3 - eulerMascheroniConstant)

private theorem bounds (n : ℕ) (hn : 3 ≤ n) :
    0 < firstAbove n ∧
      scale n - 3 / 2 ≤ (firstAbove n : ℝ) ∧ (firstAbove n : ℝ) ≤ scale n + 1 / 2 := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have ht : eulerMascheroniConstant < (n : ℝ) / 3 := by
    linarith [eulerMascheroniConstant_lt_two_thirds]
  let m := ⌊scale n + 1 / 2⌋₊
  obtain ⟨hp, hl, hu⟩ := HarmonicThreshold.crossingBounds ((n : ℝ) / 3) ht
  change 0 < firstAbove n at hp
  change m - 1 ≤ firstAbove n at hl
  change firstAbove n ≤ m at hu
  have hlN : m ≤ firstAbove n + 1 := by omega
  have hlR : (m : ℝ) ≤ (firstAbove n : ℝ) + 1 := by exact_mod_cast hlN
  have huR : (firstAbove n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hu
  have hfloor : (m : ℝ) ≤ scale n + 1 / 2 := Nat.floor_le (by unfold scale; positivity)
  have hnext : scale n + 1 / 2 < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  exact ⟨hp, by linarith, huR.trans hfloor⟩

private theorem normalized :
    Tendsto (fun n : ℕ => (firstAbove n : ℝ) / scale n) atTop (𝓝 1) := by
  have harg : Tendsto (fun n : ℕ => (n : ℝ) / 3 - eulerMascheroniConstant) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    obtain ⟨N, hN⟩ := exists_nat_gt (3 * (b + eulerMascheroniConstant))
    filter_upwards [eventually_ge_atTop N] with n hn
    have hnR : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hscale : Tendsto scale atTop atTop := tendsto_exp_atTop.comp harg
  have herr : Tendsto (fun n : ℕ => (3 / 2 : ℝ) * (scale n)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (3 / 2 : ℝ))).mul (tendsto_inv_atTop_zero.comp hscale)
  have hlo : Tendsto (fun n : ℕ => 1 - (3 / 2 : ℝ) * (scale n)⁻¹) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub herr
  have hup : Tendsto (fun n : ℕ => 1 + (3 / 2 : ℝ) * (scale n)⁻¹) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add herr
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup ?_ ?_
  · filter_upwards [eventually_ge_atTop (3 : ℕ)] with n hn
    have hpos : 0 < scale n := exp_pos _
    apply (le_div_iff₀ hpos).2
    rw [sub_mul, one_mul, mul_assoc, inv_mul_cancel₀ hpos.ne', mul_one]
    exact (bounds n hn).2.1
  · filter_upwards [eventually_ge_atTop (3 : ℕ)] with n hn
    have hpos : 0 < scale n := exp_pos _
    apply (div_le_iff₀ hpos).2
    rw [add_mul, one_mul, mul_assoc, inv_mul_cancel₀ hpos.ne', mul_one]
    linarith [(bounds n hn).2.2]

end OMA.A226187

open OMA.S_oeis_a226187 OMA.A226187 Filter Real in
theorem OMA.solution : type_of% @OMA.S_oeis_a226187.main := by
  have hshift := normalized.comp (tendsto_add_atTop_nat 1)
  have hr := (hshift.div normalized one_ne_zero).mul (tendsto_const_nhds (x := exp (1 / 3)))
  simp only [div_one, one_mul] at hr
  apply hr.congr'
  filter_upwards [eventually_ge_atTop (3 : ℕ)] with n hn
  have hscale : scale (n + 1) = scale n * exp (1 / 3) := by
    unfold scale
    push_cast
    rw [show ((n : ℝ) + 1) / 3 - eulerMascheroniConstant =
      (n : ℝ) / 3 - eulerMascheroniConstant + 1 / 3 by ring, exp_add]
  have hp : (0 : ℝ) < firstAbove n := by exact_mod_cast (bounds n hn).1
  have hsn : scale n ≠ 0 := (exp_pos _).ne'
  change ((firstAbove (n + 1) : ℝ) / scale (n + 1)) / ((firstAbove n : ℝ) / scale n) *
    exp (1 / 3) = _
  rw [hscale]
  field_simp [hp.ne', hsn, (exp_pos (1 / 3)).ne']
