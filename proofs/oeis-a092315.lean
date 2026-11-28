import OMAStatements.S_oeis_a092315
import Mathlib

open Filter Topology
open scoped BigOperators

namespace OMA.OddHarmonic

private noncomputable def lower (x : ℝ) : ℝ := 1 / (48*x^2) - 7 / (1920*x^4)
private noncomputable def upper (x : ℝ) : ℝ := lower x + 31 / (16128*x^6)
private noncomputable def oddSum (n : ℕ) : ℝ := ∑ j ∈ Finset.range n, 1 / (2*(j : ℝ)+1)
private noncomputable def residue (n : ℕ) : ℝ := oddSum n - Real.log (4*(n : ℝ))/2

private theorem lower_step (z : ℝ) (hz : 0 ≤ z) :
    lower (z+1) - lower (z+2) ≤ (1/(2*z+3))^3/3 + (1/(2*z+3))^5/5 := by
  have hp : 0 < z + 1 := by positivity
  have hq : 0 < z + 2 := by positivity
  have hr : 0 < 2*z + 3 := by positivity
  have heq :
      (1/(2*z+3))^3/3 + (1/(2*z+3))^5/5 - (lower (z+1) - lower (z+2)) =
      (640*z^6 + 5760*z^5 + 21584*z^4 + 43104*z^3 + 48370*z^2 + 28902*z + 7179) /
        (1920*(z+1)^4*(z+2)^4*(2*z+3)^5) := by
    unfold lower
    field_simp [ne_of_gt hp, ne_of_gt hq, ne_of_gt hr]
    ring
  have h : 0 ≤ (640*z^6 + 5760*z^5 + 21584*z^4 + 43104*z^3 + 48370*z^2 + 28902*z + 7179) /
      (1920*(z+1)^4*(z+2)^4*(2*z+3)^5) := by positivity
  exact sub_nonneg.mp (heq ▸ h)

private theorem upper_step (z : ℝ) (hz : 0 ≤ z) :
    let t := 1/(2*z+3)
    t^3/3 + t^5/5 + t^7/7 + t^9/(1-t^2) ≤ upper (z+1) - upper (z+2) := by
  intro t
  have hp : 0 < z + 1 := by positivity
  have hq : 0 < z + 2 := by positivity
  have hr : 0 < 2*z + 3 := by positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hlt : t < 1 := by
    dsimp [t]
    apply (div_lt_iff₀ hr).2
    linarith
  have hsq : 0 < 1 - t^2 := by nlinarith [mul_nonneg ht (sub_nonneg.mpr hlt.le)]
  have htail : t^9/(1-t^2) = 1/(4*(z+1)*(z+2)*(2*z+3)^7) := by
    apply (div_eq_div_iff hsq.ne' (ne_of_gt (by positivity : 0 < 4*(z+1)*(z+2)*(2*z+3)^7))).2
    dsimp [t]
    field_simp [ne_of_gt hr]
    ring
  have heq : upper (z+1) - upper (z+2) - (t^3/3 + t^5/5 + t^7/7 + t^9/(1-t^2)) =
      (152768*z^10 + 2291520*z^9 + 15483888*z^8 + 62064576*z^7 + 163417284*z^6 +
        295296516*z^5 + 370797663*z^4 + 319404510*z^3 + 180588915*z^2 + 60502248*z + 9119007) /
      (80640*(z+1)^6*(z+2)^6*(2*z+3)^7) := by
    rw [htail]
    unfold upper lower
    dsimp [t]
    field_simp [ne_of_gt hp, ne_of_gt hq, ne_of_gt hr]
    ring
  rw [← sub_nonneg, heq]
  positivity

private theorem harmonic_split (n : ℕ) : (harmonic (2*n) : ℝ) = oddSum n + (harmonic n : ℝ)/2 := by
  induction n with
  | zero => norm_num [harmonic, oddSum]
  | succ n ih =>
    rw [show 2*(n+1) = (2*n+1)+1 by omega, harmonic_succ, harmonic_succ, harmonic_succ]
    simp only [Rat.cast_add, Rat.cast_inv, Rat.cast_natCast, Nat.cast_succ, Nat.cast_mul, Rat.cast_mul]
    rw [ih, show oddSum (n+1) = oddSum n + 1/(2*(n : ℝ)+1) by
      simp [oddSum, Finset.sum_range_succ]]
    field_simp
    ring

private theorem residue_limit :
    Tendsto residue atTop (𝓝 (Real.eulerMascheroniConstant / 2)) := by
  have hmul : Tendsto (fun n : ℕ => 2*n) atTop atTop := by
    exact tendsto_atTop_mono (fun n => by dsimp; omega) tendsto_id
  have h := (Real.tendsto_harmonic_sub_log.comp hmul).sub
    (Real.tendsto_harmonic_sub_log.div_const 2)
  convert h.congr' ?_ using 1
  · ring
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn' : 0 < (n : ℝ) := by positivity
    dsimp [residue, Function.comp_def]
    rw [harmonic_split, Nat.cast_mul, Nat.cast_ofNat,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hn'.ne',
      Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hn'.ne',
      show Real.log (4 : ℝ) = 2 * Real.log 2 by
        rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num]
    ring

private theorem residue_step (k : ℕ) (hk : 1 ≤ k) :
    lower (k : ℝ) - lower ((k : ℝ)+1) ≤ residue k - residue (k+1) ∧
      residue k - residue (k+1) ≤ upper (k : ℝ) - upper ((k : ℝ)+1) := by
  have hk' : 0 < (k : ℝ) := by positivity
  let t : ℝ := 1/(2*(k : ℝ)+1)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have ht' : t < 1 := by
    dsimp [t]
    apply (div_lt_iff₀ (by positivity)).2
    linarith
  have hratio : (1+t)/(1-t) = ((k : ℝ)+1)/(k : ℝ) := by
    have hnon : (1 - t) ≠ 0 := by linarith
    apply (div_eq_div_iff hnon hk'.ne').2
    dsimp [t]
    field_simp [ne_of_gt (by positivity : 0 < (2 : ℝ)*(k : ℝ) + 1)]
    ring
  have hdiff : residue k - residue (k+1) = 1/2 * Real.log ((1+t)/(1-t)) - t := by
    rw [hratio, Real.log_div (by positivity) hk'.ne']
    unfold residue oddSum
    rw [Finset.sum_range_succ, Nat.cast_succ,
      Real.log_mul (show (4 : ℝ) ≠ 0 by norm_num) hk'.ne',
      Real.log_mul (show (4 : ℝ) ≠ 0 by norm_num) (by positivity)]
    dsimp [t]
    ring
  have hlogL := Real.sum_range_le_log_div ht ht' 3
  have hlogU := Real.log_div_le_sum_range_add ht ht' 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hlogL hlogU
  norm_num at hlogL hlogU
  let z : ℝ := (k : ℝ)-1
  have hz : 0 ≤ z := by
    dsimp [z]
    exact sub_nonneg.mpr (by exact_mod_cast hk)
  have ha : z+1 = (k : ℝ) := by dsimp [z]; ring
  have hb : z+2 = (k : ℝ)+1 := by dsimp [z]; ring
  have hc : 2*z+3 = 2*(k : ℝ)+1 := by dsimp [z]; ring
  have hL := lower_step z hz
  have hU := upper_step z hz
  rw [ha,hb,hc] at hL hU
  change _ ≤ t^3/3 + t^5/5 at hL
  change t^3/3 + t^5/5 + t^7/7 + t^9/(1-t^2) ≤ _ at hU
  rw [hdiff]
  exact ⟨by linarith, by linarith⟩

private theorem inverse_power_limit (p : ℕ) (hp : p ≠ 0) (c : ℝ) :
    Tendsto (fun n : ℕ => c / (n : ℝ)^p) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  simpa [div_eq_mul_inv, inv_pow, zero_pow hp] using (h.pow p).const_mul c

private theorem correction_bounds (k : ℕ) (hk : 1 ≤ k) :
    residue k - upper (k : ℝ) ≤ Real.eulerMascheroniConstant/2 ∧
      Real.eulerMascheroniConstant/2 ≤ residue k - lower (k : ℝ) := by
  have hl : Tendsto (fun n : ℕ => lower (n : ℝ)) atTop (𝓝 0) := by
    have ha := inverse_power_limit 2 (by decide) (1/48)
    have hb := inverse_power_limit 4 (by decide) (7/1920)
    convert ha.sub hb using 1
    · funext n
      simp only [lower, div_div]
    · simp
  have hu : Tendsto (fun n : ℕ => upper (n : ℝ)) atTop (𝓝 0) := by
    have hc := inverse_power_limit 6 (by decide) (31/16128)
    convert hl.add hc using 1
    · funext n
      simp only [upper, div_div]
    · simp
  have hLower : Tendsto (fun n => residue n - upper (n : ℝ)) atTop
      (𝓝 (Real.eulerMascheroniConstant/2)) := by simpa using residue_limit.sub hu
  have hUpper : Tendsto (fun n => residue n - lower (n : ℝ)) atTop
      (𝓝 (Real.eulerMascheroniConstant/2)) := by simpa using residue_limit.sub hl
  constructor
  · apply ge_of_tendsto hLower
    filter_upwards [eventually_ge_atTop k] with j hj
    refine Nat.le_induction (le_refl _) (fun n hn ih => ih.trans ?_) j hj
    have hs := (residue_step n (hk.trans hn)).2
    rw [Nat.cast_succ]
    linarith
  · apply le_of_tendsto hUpper
    filter_upwards [eventually_ge_atTop k] with j hj
    refine Nat.le_induction (le_refl _) (fun n hn ih => le_trans ?_ ih) j hj
    have hs := (residue_step n (hk.trans hn)).1
    rw [Nat.cast_succ]
    linarith

private theorem lower_nonneg (x : ℝ) (hx : 1 ≤ x) : 0 ≤ lower x := by
  have hp : 0 < x := by linarith
  have hi : lower x = (40*x^2-7)/(1920*x^4) := by
    unfold lower
    field_simp [hp.ne']
    ring
  rw [hi]
  apply div_nonneg _ (by positivity)
  nlinarith [sq_nonneg (x-1)]

private def oddRat (k : ℕ) : ℚ := ∑ j ∈ Finset.range k, 1/(2*(j : ℚ)+1)

private theorem oddRat_cast (k : ℕ) : (oddRat k : ℝ) = oddSum k := by
  unfold oddRat oddSum
  push_cast
  rfl

private def logLower (r : ℚ) (n : ℕ) : ℚ :=
  let t := (r-1)/(r+1)
  2 * ∑ i ∈ Finset.range n, t^(2*i+1)/(2*(i : ℚ)+1)

private def logUpper (r : ℚ) (n : ℕ) : ℚ :=
  let t := (r-1)/(r+1)
  logLower r n + 2*t^(2*n+1)/(1-t^2)

private theorem log_interval (r : ℚ) (hr : 1 ≤ r) (n : ℕ) :
    (logLower r n : ℝ) ≤ Real.log (r : ℝ) ∧ Real.log (r : ℝ) ≤ (logUpper r n : ℝ) := by
  have hR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  let t : ℝ := ((r : ℝ)-1)/((r : ℝ)+1)
  have hd : 0 < (r : ℝ)+1 := by linarith
  have ht : 0 ≤ t := div_nonneg (sub_nonneg.mpr hR) hd.le
  have hlt : t < 1 := by
    dsimp [t]
    apply (div_lt_iff₀ hd).2
    linarith
  have hRat : (1+t)/(1-t) = (r : ℝ) := by
    have hz : 1-t ≠ 0 := by linarith
    apply (div_eq_iff hz).2
    dsimp [t]
    field_simp [hd.ne']
    ring
  have hL := Real.sum_range_le_log_div ht hlt n
  have hU := Real.log_div_le_sum_range_add ht hlt n
  rw [hRat] at hL hU
  constructor
  · unfold logLower
    push_cast
    change 2 * (∑ i ∈ Finset.range n, t^(2*i+1)/(2*(i : ℝ)+1)) ≤ _
    linarith
  · unfold logUpper logLower
    push_cast
    change _ ≤ 2 * (∑ i ∈ Finset.range n, t^(2*i+1)/(2*(i : ℝ)+1)) + 2*t^(2*n+1)/(1-t^2)
    rw [mul_div_assoc 2 (t^(2*n+1)) (1-t^2)]
    linarith

private def cutoff : ℕ := 81897532160125
private def ratioLo : ℚ := 81897532160125 / 70368744177664
private def ratioHi : ℚ := 655180257281000 / 562949953421312 - 1 / 562949953421312

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private theorem rational_lower :
    (34 : ℚ) < 2*oddRat 256 - 2*(7215525789851 / 22698142121947299840) +
      38*logLower 2 20 + logLower ratioLo 10 := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
private theorem rational_upper :
    2*oddRat 256 - 2*(873811 / 2748779069440) + 38*logUpper 2 20 +
      logUpper ratioHi 10 < (34 : ℚ) := by
  decide +kernel

private theorem log_bounds_at_cutoff :
    34 < Real.eulerMascheroniConstant + Real.log (4*(cutoff : ℝ)) ∧
    Real.eulerMascheroniConstant + Real.log (4*(cutoff : ℝ) - 1/2) < 34 := by
  have hRatLo : 1 ≤ ratioLo := by norm_num [ratioLo]
  have hRatHi : 1 ≤ ratioHi := by norm_num [ratioHi]
  have hPosLo : (ratioLo : ℝ) ≠ 0 := by exact_mod_cast (show ratioLo ≠ 0 by positivity)
  have hPosHi : (ratioHi : ℝ) ≠ 0 := by
    exact_mod_cast (show ratioHi ≠ 0 by norm_num [ratioHi])
  have hlog0 : Real.log (4*(256 : ℝ)) = 10 * Real.log 2 := by
    rw [show (4 : ℝ)*256 = 2^10 by norm_num, Real.log_pow]
    norm_num
  have hlogL : Real.log (4*(cutoff : ℝ)) = 48*Real.log 2 + Real.log (ratioLo : ℝ) := by
    rw [show 4*(cutoff : ℝ) = (2:ℝ)^48 * (ratioLo : ℝ) by norm_num [cutoff, ratioLo],
      Real.log_mul (by positivity) hPosLo, Real.log_pow]
    norm_num
  have hlogU : Real.log (4*(cutoff : ℝ)-1/2) = 48*Real.log 2 + Real.log (ratioHi : ℝ) := by
    rw [show 4*(cutoff : ℝ)-1/2 = (2:ℝ)^48 * (ratioHi : ℝ) by norm_num [cutoff, ratioHi],
      Real.log_mul (by positivity) hPosHi, Real.log_pow]
    norm_num
  have hcorr := correction_bounds 256 (by decide)
  have hlow : lower (256 : ℝ) = ((873811 / 2748779069440 : ℚ) : ℝ) := by norm_num [lower]
  have hupp : upper (256 : ℝ) = ((7215525789851 / 22698142121947299840 : ℚ) : ℝ) := by norm_num [upper, lower]
  simp only [residue, Nat.cast_ofNat, hlog0, hlow, hupp, ← oddRat_cast] at hcorr
  have h2 := log_interval 2 (by norm_num) 20
  have hL := (log_interval ratioLo hRatLo 10).1
  have hU := (log_interval ratioHi hRatHi 10).2
  have hNumL : (34 : ℝ) < 2*(oddRat 256 : ℝ) -
        2*((7215525789851 / 22698142121947299840 : ℚ) : ℝ) +
        38*(logLower 2 20 : ℝ) + (logLower ratioLo 10 : ℝ) := by exact_mod_cast rational_lower
  have hNumU : 2*(oddRat 256 : ℝ) - 2*((873811 / 2748779069440 : ℚ) : ℝ) +
      38*(logUpper 2 20 : ℝ) + (logUpper ratioHi 10 : ℝ) < (34 : ℝ) := by exact_mod_cast rational_upper
  constructor
  · rw [hlogL]
    push_cast at h2
    linarith [hcorr.1,h2.1]
  · rw [hlogU]
    push_cast at h2
    linarith [hcorr.2,h2.2]

end OMA.OddHarmonic

open OMA.OddHarmonic in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a092315.main) := by
  intro h
  have hcut : 1 ≤ cutoff := by decide
  have hCorr := (correction_bounds cutoff hcut).2
  have hNonneg := lower_nonneg (cutoff : ℝ) (by norm_num [cutoff])
  have hOdd : (17 : ℝ) < oddSum cutoff := by
    dsimp [residue] at hCorr
    linarith [log_bounds_at_cutoff.1]
  have hInf : OMA.S_oeis_a092315.a 17 ≤ cutoff - 1 := by
    apply Nat.sInf_le
    change (17 : ℝ) < oddSum (cutoff - 1 + 1)
    rwa [show cutoff-1+1 = cutoff by decide]
  have hPos : 0 < 4*(cutoff : ℝ)-1/2 := by norm_num [cutoff]
  have hExp : 4*(cutoff : ℝ)-1/2 < Real.exp (34 - Real.eulerMascheroniConstant) := by
    calc
      _ = Real.exp (Real.log (4*(cutoff : ℝ)-1/2)) := (Real.exp_log hPos).symm
      _ < _ := Real.exp_lt_exp.mpr (by linarith [log_bounds_at_cutoff.2])
  have hFloor : cutoff ≤ ⌊Real.exp (34 - Real.eulerMascheroniConstant)/4+1/8⌋₊ :=
    Nat.le_floor (by linarith)
  have hEq := h 17 (by decide)
  rw [show 2 * ((17 : ℕ) : ℝ) = 34 by norm_num] at hEq
  omega