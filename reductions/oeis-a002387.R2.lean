import OMAStatements.S_oeis_a002387
import Mathlib

/-!
# A002387 via two quadratic envelopes for the harmonic numbers
Credit: @Pixelstorm44
-/

namespace OMA.R_oeis_a002387_R2

open Real Filter Topology

private theorem log_increment (c t : ℝ) (hc : 0 < c) (ht : 0 < t) (ht1 : t ≤ 1) :
    ∃ u ∈ Set.Ioo 0 t,
      log (1+t+c*t^2) - log (1-t+c*t^2) - 2*t =
      t * (2*u^2*(1-3*c-c^2*u^2) / ((1+u+c*u^2)*(1-u+c*u^2))) := by
  let f := fun u : ℝ => log (1+u+c*u^2) - log (1-u+c*u^2) - 2*u
  have pos (u : ℝ) (hu : u ∈ Set.Icc 0 t) :
      0 < 1+u+c*u^2 ∧ 0 < 1-u+c*u^2 := by
    obtain ⟨hu0, hut⟩ := hu
    constructor
    · positivity
    · rcases eq_or_lt_of_le hu0 with h | h
      · simp [← h]
      · linarith [mul_pos hc (sq_pos_of_pos h)]
  have hd (u : ℝ) (hu : u ∈ Set.Icc 0 t) : HasDerivAt f
      (2*u^2*(1-3*c-c^2*u^2) / ((1+u+c*u^2)*(1-u+c*u^2))) u := by
    obtain ⟨hp, hm⟩ := pos u hu
    have idu := hasDerivAt_id' u
    have sq := (idu.pow 2).const_mul c
    have a := (((idu.const_add 1).add sq).log hp.ne')
    have b := (((idu.const_sub 1).add sq).log hm.ne')
    have d := (a.sub b).sub (idu.const_mul 2)
    change HasDerivAt f
      ((1+c*(2*u^(2-1)*1))/(1+u+c*u^2) -
       (-1+c*(2*u^(2-1)*1))/(1-u+c*u^2) - 2*1) u at d
    convert d using 1
    rw [div_eq_iff (mul_ne_zero hp.ne' hm.ne')]
    generalize ha : 1+u+c*u^2 = A at hp ⊢
    generalize hb : 1-u+c*u^2 = B at hm ⊢
    field_simp [hp.ne', hm.ne']
    rw [← ha, ← hb]
    ring
  obtain ⟨u, hu, he⟩ := exists_deriv_eq_slope f ht
    (fun u hu => (hd u hu).continuousAt.continuousWithinAt)
    (fun u hu => (hd u (Set.Ioo_subset_Icc_self hu)).differentiableAt.differentiableWithinAt)
  refine ⟨u, hu, ?_⟩
  rw [(hd u (Set.Ioo_subset_Icc_self hu)).deriv] at he
  have hzero : f 0 = 0 := by simp [f]
  rw [hzero, sub_zero, sub_zero, eq_div_iff ht.ne'] at he
  exact he.symm.trans (mul_comm _ _)

private theorem centered_limit (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) :
    Tendsto (fun k : ℕ => 2*(harmonic k : ℝ) - log ((k:ℝ)^2 + k + c))
      atTop (𝓝 (2*eulerMascheroniConstant)) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds.mul tendsto_harmonic_sub_log_add_one)
    (tendsto_const_nhds.mul tendsto_harmonic_sub_log)
  · filter_upwards with k
    have h := Real.log_le_log (show 0 < (k:ℝ)^2+k+c by positivity)
      (show (k:ℝ)^2+k+c ≤ ((k:ℝ)+1)^2 by nlinarith [Nat.cast_nonneg (α := ℝ) k])
    rw [Real.log_pow] at h
    try dsimp
    try push_cast at h
    linarith
  · filter_upwards [eventually_gt_atTop (0:ℕ)] with k hk
    have h := Real.log_le_log (show 0 < (k:ℝ)^2 by positivity)
      (show (k:ℝ)^2 ≤ (k:ℝ)^2+k+c by linarith [Nat.cast_nonneg (α := ℝ) k])
    rw [Real.log_pow] at h
    try dsimp
    try push_cast at h
    linarith

private theorem centered_step (c : ℝ) (hc : 0 < c) (k : ℕ) :
    let t := 1/((k:ℝ)+1)
    ∃ u ∈ Set.Ioo 0 t,
      (2*(harmonic k : ℝ) - log ((k:ℝ)^2+k+c)) -
      (2*(harmonic (k+1) : ℝ) - log (((k:ℝ)+1)^2+((k:ℝ)+1)+c)) =
      t * (2*u^2*(1-3*c-c^2*u^2) / ((1+u+c*u^2)*(1-u+c*u^2))) := by
  let x := (k:ℝ)+1
  let t := 1/x
  have hx : 0 < x := by dsimp [x]; positivity
  have ht : 0 < t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by dsimp [t,x]; rw [div_le_iff₀ (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) k]
  obtain ⟨u, hu, he⟩ := log_increment c t hc ht ht1
  refine ⟨u, hu, ?_⟩
  change _ = t * _
  rw [← he]
  have A : 1+t+c*t^2 = (x^2+x+c) / x^2 := by dsimp [t]; field_simp
  have B : 1-t+c*t^2 = ((k:ℝ)^2+k+c) / x^2 := by dsimp [t,x]; field_simp; ring
  rw [A, B, log_div (by positivity) (by positivity), log_div (by positivity) (by positivity),
    harmonic_succ]
  push_cast
  dsimp [t,x]
  ring

private theorem one_step_sign (c u : ℝ) (hc : 0 < c) (hu : 0 < u) (hu1 : u < 1) :
    0 < 2*u^2 / ((1+u+c*u^2)*(1-u+c*u^2)) := by
  have : 0 < 1-u := by linarith
  positivity

/-- A two-sided enclosure on the squared exponential scale. -/
theorem harmonic_square_bounds (k : ℕ) :
    let S := (k:ℝ)^2 + k + 1/3
    S - 1/(27*((k:ℝ)+1)^2) < exp (2*((harmonic k : ℝ)-eulerMascheroniConstant)) ∧
    exp (2*((harmonic k : ℝ)-eulerMascheroniConstant)) < S := by
  let c := 1/3 - 1/(27*((k:ℝ)+1)^2)
  have hk0 := Nat.cast_nonneg (α := ℝ) k
  have hk1 : 1 ≤ ((k:ℝ)+1)^2 := by nlinarith
  have hcsmall : 1/(27*((k:ℝ)+1)^2) ≤ 1/27 := by
    gcongr
    nlinarith
  have hc : 0 < c := by dsimp [c]; linarith
  have hc3 : c < 1/3 := by dsimp [c]; linarith [show 0 < 1/(27*((k:ℝ)+1)^2) by positivity]
  let F := fun (d : ℝ) (j : ℕ) =>
    2*(harmonic (j+k) : ℝ) - log (((j+k:ℕ):ℝ)^2 + ((j+k:ℕ):ℝ) + d)
  have limF (d : ℝ) (hd : 0 < d) (hd1 : d ≤ 1) :
      Tendsto (F d) atTop (𝓝 (2*eulerMascheroniConstant)) :=
    (tendsto_add_atTop_iff_nat k).2 (centered_limit d hd hd1)
  have anti : StrictAnti (F c) := by
    apply strictAnti_nat_of_succ_lt
    intro j
    obtain ⟨u, hu, he⟩ := centered_step c hc (j+k)
    have hu' : u < 1/((k:ℝ)+1) := hu.2.trans_le (by push_cast; gcongr; linarith [Nat.cast_nonneg (α := ℝ) j])
    have hu1 : u < 1 := hu'.trans_le (by rw [div_le_iff₀ (by positivity)]; linarith)
    have hsq : c^2*u^2 < (1/3:ℝ)^2*(1/((k:ℝ)+1))^2 := by
      gcongr
      exact hu.1.le
    have hfac : 0 < 1-3*c-c^2*u^2 := by
      have hh : (1/3:ℝ)^2*(1/((k:ℝ)+1))^2 = 3*(1/(27*((k:ℝ)+1)^2)) := by
        field_simp
        ring
      linarith only [hsq, hh, show c = 1/3 - 1/(27*((k:ℝ)+1)^2) from rfl]
    have hp := mul_pos (one_step_sign c u hc hu.1 hu1) hfac
    rw [div_mul_eq_mul_div] at hp
    have h := mul_pos (show 0 < 1/(((j+k:ℕ):ℝ)+1) by positivity) hp
    rw [← he] at h
    simpa only [F, Nat.succ_add, Nat.cast_succ] using sub_pos.mp h
  have mono : StrictMono (F (1/3)) := by
    apply strictMono_nat_of_lt_succ
    intro j
    obtain ⟨u, hu, he⟩ := centered_step (1/3) (by norm_num) (j+k)
    have hu1 : u < 1 := hu.2.trans_le (by rw [div_le_iff₀ (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) (j+k)])
    have hfac : 1-3*(1/3:ℝ)-(1/3:ℝ)^2*u^2 < 0 := by nlinarith [sq_pos_of_pos hu.1]
    have hp := mul_neg_of_pos_of_neg (one_step_sign (1/3) u (by norm_num) hu.1 hu1) hfac
    rw [div_mul_eq_mul_div] at hp
    have h := mul_neg_of_pos_of_neg (show 0 < 1/(((j+k:ℕ):ℝ)+1) by positivity) hp
    rw [← he] at h
    simpa only [F, Nat.succ_add, Nat.cast_succ] using sub_neg.mp h
  have lower := (anti (show 0 < 1 by decide)).trans_le' (anti.antitone.le_of_tendsto (limF c hc (by linarith)) 1)
  have upper := (mono (show 0 < 1 by decide)).trans_le (mono.monotone.ge_of_tendsto (limF (1/3) (by norm_num) (by norm_num)) 1)
  simp only [F, zero_add] at lower upper
  dsimp only
  constructor
  · have heq : (k:ℝ)^2+k+1/3-1/(27*((k:ℝ)+1)^2) = (k:ℝ)^2+k+c := by dsimp [c]; ring
    rw [heq, ← log_lt_iff_lt_exp (by positivity)]
    linarith
  · rw [← lt_log_iff_exp_lt (by positivity)]
    linarith

private theorem midpoint_sq_lt (k : ℕ) :
    ((k:ℝ)+1/2)^2 < (k:ℝ)^2+k+1/3-1/(27*((k:ℝ)+1)^2) := by
  have hk := Nat.cast_nonneg (α := ℝ) k
  have h : 1/(27*((k:ℝ)+1)^2) ≤ 1/27 := by gcongr; nlinarith
  nlinarith

/-- In particular both analytic inequalities required by the earlier reduction hold. -/
theorem harmonic_midpoint_error (k : ℕ) (hk : 0 < k) :
    log ((k:ℝ)+1/2) + eulerMascheroniConstant < (harmonic k:ℝ) ∧
    (harmonic k:ℝ) < log ((k:ℝ)+1/2) + eulerMascheroniConstant + 1/(24*(k:ℝ)^2) := by
  obtain ⟨hl, hu⟩ := harmonic_square_bounds k
  have pos : 0 < (k:ℝ)+1/2 := by positivity
  have hl' := Real.log_lt_log (sq_pos_of_pos pos) ((midpoint_sq_lt k).trans hl)
  rw [log_pow, log_exp] at hl'
  have hu' := Real.log_lt_log (exp_pos _) hu
  rw [log_exp] at hu'
  let m := (k:ℝ)+1/2
  have hlog := Real.log_le_sub_one_of_pos (show 0 < 1+1/(12*m^2) by dsimp [m]; positivity)
  have heq : (k:ℝ)^2+k+1/3 = m^2*(1+1/(12*m^2)) := by
    field_simp [show m ≠ 0 from pos.ne']
    dsimp [m]
    ring
  rw [heq, log_mul (pow_ne_zero _ pos.ne') (by dsimp [m]; positivity), log_pow] at hu'
  have hle : 1/(12*m^2) ≤ 1/(12*(k:ℝ)^2) := by
    dsimp [m]
    gcongr
    linarith
  have h24 : 1/(12*(k:ℝ)^2) = 2*(1/(24*(k:ℝ)^2)) := by field_simp; norm_num
  change log m + _ < _ ∧ _ < log m + _ + _
  change (2:ℝ)*log m < _ at hl'
  constructor <;> linarith

/-- Exclude the interior in which the rounded answer provably overshoots. -/
def H1 : Prop :=
  ∀ n k : ℕ, 1 < n →
    ((k:ℝ)+1/2)^2 ≤ exp (2*((n:ℝ)-eulerMascheroniConstant)) →
    (k:ℝ)^2+k+1/3-1/(27*((k:ℝ)+1)^2) < exp (2*((n:ℝ)-eulerMascheroniConstant))

/-- Only the boundary strip requires a comparison with an exact rational harmonic sum. -/
def H2 : Prop :=
  ∀ n k : ℕ, 1 < n →
    (k:ℝ)^2+k+1/3-1/(27*((k:ℝ)+1)^2) < exp (2*((n:ℝ)-eulerMascheroniConstant)) →
    exp (2*((n:ℝ)-eulerMascheroniConstant)) < (k:ℝ)^2+k+1/3 →
    harmonic k ≤ (n:ℚ)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a002387.main := by
  intro hinterior hstrip n hn
  let x := exp ((n:ℝ)-eulerMascheroniConstant)
  let m := ⌊x+1/2⌋₊
  have hx : 0 < x := exp_pos _
  have hsq : x^2 = exp (2*((n:ℝ)-eulerMascheroniConstant)) := by
    rw [two_mul, exp_add]; dsimp [x]; ring
  have hm : (m:ℝ) ≤ x+1/2 := Nat.floor_le (by positivity)
  have hround : x < (m:ℝ)+1/2 := by linarith [Nat.lt_floor_add_one (x+1/2)]
  constructor
  · have hl := ((midpoint_sq_lt m).trans (harmonic_square_bounds m).1)
    have h := (pow_lt_pow_left₀ hround hx.le (by decide : 2 ≠ 0)).trans hl
    rw [hsq, exp_lt_exp] at h
    exact_mod_cast (show (n:ℝ) < (harmonic m:ℝ) by linarith)
  · intro k hk
    change (n:ℚ) < harmonic k at hk
    change m ≤ k
    by_contra! hkm
    have hkm' : (k:ℝ)+1 ≤ (m:ℝ) := by exact_mod_cast hkm
    have hl : ((k:ℝ)+1/2)^2 ≤ x^2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    rw [hsq] at hl
    have hnr : (n:ℝ) < (harmonic k:ℝ) := by exact_mod_cast hk
    have hu := (exp_lt_exp.mpr (show 2*((n:ℝ)-eulerMascheroniConstant) <
      2*((harmonic k:ℝ)-eulerMascheroniConstant) by linarith)).trans (harmonic_square_bounds k).2
    exact (not_le.mpr hk) (hstrip n k hn (hinterior n k hn hl) hu)

/-- Both remaining conditions are necessary as well as jointly sufficient. -/
theorem conditions_necessary (h : type_of% @OMA.S_oeis_a002387.main) : H1 ∧ H2 := by
  have prev (n k : ℕ) (hn : 1 < n)
      (hmid : ((k:ℝ)+1/2)^2 ≤ exp (2*((n:ℝ)-eulerMascheroniConstant))) :
      harmonic k ≤ (n:ℚ) := by
    let x := exp ((n:ℝ)-eulerMascheroniConstant)
    have he : exp (2*((n:ℝ)-eulerMascheroniConstant)) = x^2 := by
      rw [two_mul, exp_add]; dsimp [x]; ring
    rw [he] at hmid
    have hle : (k:ℝ)+1/2 ≤ x := by nlinarith [show 0 < x from exp_pos _, Nat.cast_nonneg (α := ℝ) k]
    have hlt : k+1 ≤ ⌊x+1/2⌋₊ := by apply Nat.le_floor; push_cast; linarith
    by_contra! hk
    have := (h n hn).2 (show k ∈ {j:ℕ | (n:ℚ) < harmonic j} from hk)
    change ⌊x+1/2⌋₊ ≤ k at this
    omega
  constructor
  · intro n k hn hmid
    have hk : (harmonic k:ℝ) ≤ (n:ℝ) := by exact_mod_cast prev n k hn hmid
    exact (harmonic_square_bounds k).1.trans_le (exp_le_exp.mpr (by linarith))
  · intro n k hn hl _
    exact prev n k hn ((midpoint_sq_lt k).trans hl).le

end OMA.R_oeis_a002387_R2
