import OMAReductions.R_Arxiv_2607_05739_tan_arctan_sum_not_integer_R1
import Mathlib

/-! A certified phase enclosure for the Amdeberhan–Medina–Moll conjecture.
The calculation at 2048 and the fourth-order tail bound locate the phase
without the evaluation of an infinite sum. The two below- and above-word
windows are discharged here. The merged proof in PR #12274 separately
covers all remaining indices below 2^64. -/

namespace ArctanNumericPhase

namespace ArctanPhaseRefinement

private lemma nonneg_on_unit {f g : ℝ → ℝ} (hz : f 0 = 0)
    (hd : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f (g x) x)
    (hpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ g x)
    {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ f x := by
  have mono := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) 1)
    (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
    (fun y hy => (hd y (interior_subset hy)).hasDerivWithinAt)
    (fun y hy => hpos y (interior_subset hy))
  simpa only [hz] using mono (show (0 : ℝ) ∈ Set.Icc 0 1 from ⟨le_rfl, zero_le_one⟩)
    ⟨hx, hx1⟩ hx

/-- The midpoint inverse-square correction absorbs the cubic logarithmic defect. -/
theorem local_bound {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    let e := (20/3*x^3)/(4-x^2)^2 -
      (Real.log (1+x/2) - Real.log (1-x/2) - Real.arctan x)
    0 ≤ e ∧ e ≤ x^5 := by
  let e (y : ℝ) := (20/3*y^3)/(4-y^2)^2 -
    (Real.log (1+y/2) - Real.log (1-y/2) - Real.arctan y)
  let v (y : ℝ) := y^4*(380+5*y^2)/(3*(4-y^2)^3*(1+y^2))
  have hd (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1) : HasDerivAt e (v y) y := by
    obtain ⟨h₀,h₁⟩ := hy
    have hs : y^2 ≤ 1 := by nlinarith [mul_nonneg h₀ (sub_nonneg.mpr h₁)]
    have hD : 0 < 4-y^2 := by linarith
    have hp : 1+y/2 ≠ 0 := by linarith
    have hm : 1-y/2 ≠ 0 := by linarith
    have h₁' : HasDerivAt (fun z : ℝ => 1+z/2) (1/2) y := ((hasDerivAt_id y).div_const 2).const_add 1
    have h₂' : HasDerivAt (fun z : ℝ => 1-z/2) (-(1/2)) y := ((hasDerivAt_id y).div_const 2).const_sub 1
    have hlog := ((h₁'.log hp).sub (h₂'.log hm)).sub (Real.hasDerivAt_arctan y)
    have hpot := ((hasDerivAt_pow 3 y).const_mul (20/3 : ℝ)).div
      (((hasDerivAt_pow 2 y).const_sub 4).pow 2) (pow_ne_zero 2 hD.ne')
    convert hpot.sub hlog using 1 <;> first | rfl | skip
    dsimp [v]
    have hh : 2-y ≠ 0 := by linarith
    field_simp [hh]
    ring
  have hb (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ v y ∧ v y ≤ 5*y^4 := by
    obtain ⟨h₀,h₁⟩ := hy
    have hs : y^2 ≤ 1 := by nlinarith [mul_nonneg h₀ (sub_nonneg.mpr h₁)]
    have hD : 3 ≤ 4-y^2 := by linarith
    have hd3 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤3) hD 3
    have hden : 81 ≤ 3*(4-y^2)^3*(1+y^2) := by
      nlinarith only [hd3,mul_nonneg (pow_nonneg (show 0 ≤ 4-y^2 by linarith) 3) (sq_nonneg y)]
    dsimp [v]
    constructor
    · exact div_nonneg (by positivity) (by linarith only [hden])
    · apply (div_le_iff₀ (by linarith only [hden] : 0 < 3*(4-y^2)^3*(1+y^2))).mpr
      have hh : 380+5*y^2 ≤ 5*(3*(4-y^2)^3*(1+y^2)) := by linarith only [hs,hden]
      nlinarith only [mul_le_mul_of_nonneg_left hh (pow_nonneg h₀ 4)]
  have hz : e 0 = 0 := by norm_num [e]
  constructor
  · exact nonneg_on_unit hz hd (fun y hy => (hb y hy).1) hx hx1
  · apply sub_nonneg.mp
    apply nonneg_on_unit (f := fun y => y^5-e y) (g := fun y => 5*y^4-v y)
      (by norm_num [hz]) _ _ hx hx1
    · intro y hy
      convert (hasDerivAt_pow 5 y).sub (hd y hy) using 1 <;> rfl
    · exact fun y hy => sub_nonneg.mpr (hb y hy).2

private lemma midpoint_step (t : ℝ) (ht : 0 ≤ t) :
    let u := t+1
    let e := Real.arctan (1/u) -
      (Real.log (u+1/2) - Real.log (t+1/2)) +
      (5/(24*(t+1/2)^2) - 5/(24*(u+1/2)^2))
    0 ≤ e ∧ e ≤ (1/u)^5 := by
  let u := t+1
  have hu : 0 < u := by dsimp [u]; linarith
  have h₁ : 1/u ≤ 1 := (div_le_iff₀ hu).mpr (by dsimp [u]; linarith)
  have ha : 1+(1/u)/2 = (u+1/2)/u := by field_simp
  have hb : 1-(1/u)/2 = (t+1/2)/u := by dsimp [u]; field_simp; ring
  have hpos : 0 < t+1/2 := by linarith
  have he : (20/3*(1/u)^3)/(4-(1/u)^2)^2 =
      5/(24*(t+1/2)^2) - 5/(24*(u+1/2)^2) := by
    dsimp [u]
    have ht₀ : 0 < 2*t+1 := by linarith
    have ht₁ : 0 < 2*t+3 := by linarith
    have hd : 4-(1/(t+1))^2 = (2*t+1)*(2*t+3)/(t+1)^2 := by field_simp; ring
    rw [hd]
    field_simp [ht₀.ne',ht₁.ne']
    ring
  have h := local_bound (by positivity : 0 ≤ 1/u) h₁
  dsimp only at h
  rw [he, ha, hb, Real.log_div (by positivity) hu.ne', Real.log_div hpos.ne' hu.ne'] at h
  constructor <;> linarith only [h.1,h.2]

/-- A finite interval enclosure for the phase after the midpoint correction. -/
theorem finite_estimate {s : ℕ → ℝ}
    (step : ∀ n : ℕ, s (n+1) = s n + Real.arctan (1/((n:ℝ)+1)))
    (m n : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) :
    let a := fun k : ℕ => s k - Real.log ((k:ℝ)+1/2) - 5/(24*((k:ℝ)+1/2)^2)
    a m ≤ a n ∧ a n + 1/(4*(n:ℝ)^4) ≤ a m + 1/(4*(m:ℝ)^4) := by
  let a (k : ℕ) := s k - Real.log ((k:ℝ)+1/2) - 5/(24*((k:ℝ)+1/2)^2)
  change a m ≤ a n ∧ a n + _ ≤ a m + _
  induction n, hmn using Nat.le_induction with
  | base => exact ⟨le_rfl,le_rfl⟩
  | succ n hmn ih =>
    have hn : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0<n)
    obtain ⟨lo,hi⟩ := midpoint_step (n:ℝ) hn.le
    have difference : (1/((n:ℝ)+1))^5 ≤ 1/(4*(n:ℝ)^4) - 1/(4*((n:ℝ)+1)^4) := by
      apply sub_nonneg.mp
      field_simp
      ring_nf
      positivity
    have gain : a n ≤ a (n+1) ∧
        a (n+1) + 1/(4*((n+1:ℕ):ℝ)^4) ≤ a n + 1/(4*(n:ℝ)^4) := by
      dsimp only [a]
      rw [step,Nat.cast_succ]
      constructor <;> linarith only [lo,hi,difference]
    exact ⟨ih.1.trans gain.1, gain.2.trans ih.2⟩

end ArctanPhaseRefinement

open Finset Filter
open scoped Topology

set_option maxRecDepth 12000 in
set_option maxHeartbeats 6000000 in
theorem tan_angle_anchor_2048 :
    (3170601386840298533498 : ℝ)/(4*10^20) ≤
      ∑ k ∈ range 2048, Real.arctan (1/((k : ℝ)+1)) ∧
    (∑ k ∈ range 2048, Real.arctan (1/((k : ℝ)+1))) ≤
      (3170601386840298541747 : ℝ)/(4*10^20) := by
  let anchorPairs (k : ℕ) : ℕ :=
    if k ≤ 3 then 15 else if k ≤ 10 then 8 else if k ≤ 50 then 4 else 3

  let anchorTerm (k j : ℕ) : ℚ :=
    (-1)^j * (1/(k : ℚ))^(2*j+1) / (2*j+1 : ℕ)

  let anchorPartial (k : ℕ) : ℕ → ℚ := Nat.rec 0 (fun j v => v + anchorTerm k j)

  let anchorLo (k : ℕ) : ℤ := ⌊(10:ℚ)^20 * anchorPartial k (2*anchorPairs k)⌋
  let anchorHi (k : ℕ) : ℤ := ⌊(10:ℚ)^20 * anchorPartial k (2*anchorPairs k+1)⌋ + 1

  have anchor_partial_real (k j : ℕ) :
      Rat.cast (K := ℝ) (anchorPartial k j) = ∑ i ∈ range j,
        (-1)^i * ((1/(k:ℝ))^(2*i+1) / (2*i+1 : ℕ)) := by
    induction j with
    | zero => simp [anchorPartial]
    | succ j ih =>
      change ((anchorPartial k j + anchorTerm k j : ℚ) : ℝ) = _
      rw [Rat.cast_add, ih, sum_range_succ]
      congr 1
      simp [anchorTerm, mul_div_assoc]

  have anchor_term_bounds (k : ℕ) (hk : 2 ≤ k) :
      (↑(anchorLo k) : ℝ) ≤ (10:ℝ)^20 * Real.arctan (1/(k:ℝ)) ∧
        (10:ℝ)^20 * Real.arctan (1/(k:ℝ)) ≤ (↑(anchorHi k) : ℝ) := by
    let x : ℝ := 1/k
    have hk' : (1:ℝ) < k := by exact_mod_cast (show 1 < k by omega)
    have hx : 0 < x := by dsimp [x]; positivity
    have h1 : x < 1 := (div_lt_one (by linarith : (0:ℝ)<k)).mpr hk'
    let f (i : ℕ) := x^(2*i+1)/(2*i+1 : ℕ)
    have ha : Antitone f := by
      intro i j hij
      dsimp only [f]
      apply div_le_div₀ (by positivity) _ (by positivity) _
      · exact pow_le_pow_of_le_one hx.le h1.le (by omega)
      · exact_mod_cast (show 2*i+1 ≤ 2*j+1 by omega)
    have hconv : Tendsto (fun n => ∑ i ∈ range n, (-1)^i * f i) atTop (𝓝 (Real.arctan x)) := by
      simpa only [f, ← mul_div_assoc] using
        (Real.hasSum_arctan (by simpa [Real.norm_eq_abs, abs_of_pos hx] using h1)).tendsto_sum_nat
    have lo := ha.alternating_series_le_tendsto hconv (anchorPairs k)
    have hi := ha.tendsto_le_alternating_series hconv (anchorPairs k)
    change ∑ i ∈ range (2*anchorPairs k), (-1)^i*((1/(k:ℝ))^(2*i+1)/(2*i+1 : ℕ)) ≤ _ at lo
    change _ ≤ ∑ i ∈ range (2*anchorPairs k+1), (-1)^i*((1/(k:ℝ))^(2*i+1)/(2*i+1 : ℕ)) at hi
    rw [← anchor_partial_real] at lo hi
    have cas (q : ℚ) : (((10:ℚ)^20*q : ℚ) : ℝ) = (10:ℝ)^20 * (q:ℝ) := by push_cast; rfl
    have hfloor : (↑(anchorLo k) : ℝ) ≤ (10:ℝ)^20 * Rat.cast (K := ℝ) (anchorPartial k (2*anchorPairs k)) := by
      have bound (q : ℚ) : (⌊q⌋ : ℝ) ≤ (q : ℝ) := by exact_mod_cast Int.floor_le q
      exact (bound ((10:ℚ)^20 * anchorPartial k (2*anchorPairs k))).trans_eq (cas _)
    have hceil : (10:ℝ)^20 * Rat.cast (K := ℝ) (anchorPartial k (2*anchorPairs k+1)) ≤ (↑(anchorHi k) : ℝ) := by
      have bound (q : ℚ) : (q : ℝ) ≤ (⌊q⌋ : ℝ)+1 := by exact_mod_cast (Int.lt_floor_add_one q).le
      rw [← cas]
      dsimp only [anchorHi]
      rw [Int.cast_add, Int.cast_one]
      exact bound _
    exact ⟨hfloor.trans (mul_le_mul_of_nonneg_left lo (by positivity)),
      (mul_le_mul_of_nonneg_left hi (by positivity)).trans hceil⟩


  let anchorPrefix (f : ℕ → ℤ) (base : ℕ) : ℕ → ℤ := Nat.rec 0 (fun m v => v + f (base+m))

  have anchorPrefix_eq (f : ℕ → ℤ) (b m : ℕ) :
      anchorPrefix f b m = ∑ i ∈ range m, f (b+i) := by
    induction m with
    | zero => simp [anchorPrefix]
    | succ m ih =>
      change anchorPrefix f b m + f (b+m) = _
      rw [ih, sum_range_succ]

  have anchor_lo_exact : anchorPrefix anchorLo 2 2047 = 714110530370329802413 := by
    dsimp -iota only [anchorPrefix, anchorLo, anchorPartial, anchorPairs, anchorTerm]
    decide +kernel
  have anchor_hi_exact : anchorPrefix anchorHi 2 2047 = 714110530370329804475 := by
    dsimp -iota only [anchorPrefix, anchorHi, anchorPartial, anchorPairs, anchorTerm]
    decide +kernel

  let s : ℝ := ∑ k ∈ range 2047, Real.arctan (1/((2+k : ℕ) : ℝ))
  have lowSum : (714110530370329802413 : ℝ) ≤ (10:ℝ)^20*s := by
    calc
      _ = ∑ k ∈ range 2047, (↑(anchorLo (2+k)) : ℝ) := by
        exact_mod_cast anchor_lo_exact.symm.trans (anchorPrefix_eq anchorLo 2 2047)
      _ ≤ ∑ k ∈ range 2047, (10:ℝ)^20*Real.arctan (1/((2+k : ℕ) : ℝ)) :=
        sum_le_sum fun k _ => (anchor_term_bounds (2+k) (by omega)).1
      _ = _ := (mul_sum ..).symm
  have hiSum : (10:ℝ)^20*s ≤ (714110530370329804475 : ℝ) := by
    calc
      _ = ∑ k ∈ range 2047, (10:ℝ)^20*Real.arctan (1/((2+k : ℕ) : ℝ)) := mul_sum ..
      _ ≤ ∑ k ∈ range 2047, (↑(anchorHi (2+k)) : ℝ) :=
        sum_le_sum fun k _ => (anchor_term_bounds (2+k) (by omega)).2
      _ = _ := by exact_mod_cast (anchorPrefix_eq anchorHi 2 2047).symm.trans anchor_hi_exact
  have splitSum : (∑ k ∈ range 2048, Real.arctan (1/((k : ℝ)+1))) = s+Real.pi/4 := by
    rw [show 2048 = 2047+1 by decide, sum_range_succ']
    norm_num [s, Real.arctan_one, add_comm, add_left_comm, add_assoc]
  rw [splitSum]
  constructor <;> linarith only [lowSum,hiSum,Real.pi_gt_d20,Real.pi_lt_d20]

theorem tan_angle_anchor_Icc_2048 :
    (3170601386840298533498 : ℝ)/(4*10^20) ≤
      ∑ k ∈ Icc 1 (2048 : ℕ), Real.arctan (1/(k : ℝ)) ∧
    (∑ k ∈ Icc 1 (2048 : ℕ), Real.arctan (1/(k : ℝ))) ≤
      (3170601386840298541747 : ℝ)/(4*10^20) := by
  have shift (m : ℕ) : (∑ k ∈ Icc 1 m, Real.arctan (1/(k : ℝ))) =
      ∑ k ∈ range m, Real.arctan (1/((k : ℝ)+1)) := by
    induction m with
    | zero => simp
    | succ m ih => rw [sum_Icc_succ_top (by omega : 1 ≤ m+1), sum_range_succ, ih, Nat.cast_succ]
  rw [shift]; exact tan_angle_anchor_2048

/-- Certified logarithmic bounds at the anchor and uniform exclusion of the
nine half-turn crossings in the indicated range. -/
theorem tan_log_and_gaps :
    ((76248630969869257:ℝ)/10^16 ≤ Real.log ((2048:ℝ)+1/2) ∧
      Real.log ((2048:ℝ)+1/2) ≤ (76248630969869257+1:ℝ)/10^16) ∧
    ∀ s : ℕ → ℝ, Monotone s →
      (∀ n : ℕ, 1000000 ≤ n →
        0.30164032046750 ≤ s n - Real.log ((n:ℝ)+1/2) ∧
        s n - Real.log ((n:ℝ)+1/2) ≤ 0.30164032046780) →
      ∀ n : ℕ, 1000001 ≤ n → n ≤ 900000000000 →
        ∀ j : ℤ, 1/10^14 < |s n - (j:ℝ)*(Real.pi/2)| := by
  let tanLogSum (x : ℚ) : ℚ :=
    2 * ∑ i ∈ Finset.range 24, x^(2*i+1) / (2*(i:ℚ)+1)

  have tanLogSum_spec {x : ℚ} (hx : 0 ≤ x) (hx' : x ≤ 1/3) :
      (tanLogSum x : ℝ) ≤ Real.log ((1+(x:ℝ))/(1-x)) ∧
      Real.log ((1+(x:ℝ))/(1-x)) ≤ (tanLogSum x : ℝ) + 1 / 10^22 := by
    have h0 : 0 ≤ (x : ℝ) := by exact_mod_cast hx
    have h3 : (x : ℝ) ≤ 1/3 := by
      simpa using (Rat.cast_le (K := ℝ)).mpr hx'
    have h1 : (x : ℝ) < 1 := by linarith
    have lo := Real.sum_range_le_log_div h0 h1 24
    have hi := Real.log_div_le_sum_range_add h0 h1 24
    have den : (8:ℝ)/9 ≤ 1 - (x:ℝ)^2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr h3) (by linarith : 0 ≤ 1/3 + (x:ℝ))]
    have rem : (x:ℝ)^(2*24+1) / (1-(x:ℝ)^2) ≤ (1/3:ℝ)^49 / (8/9) := by
      exact div_le_div₀ (by norm_num) (pow_le_pow_left₀ h0 h3 _) (by norm_num) den
    have small : 2 * ((1/3:ℝ)^49 / (8/9)) ≤ 1/10^22 := by norm_num
    dsimp only [tanLogSum]
    push_cast
    exact ⟨by linarith, by linarith⟩

  let tanLogReduced (n : ℕ) : ℚ :=
    ((n:ℚ) + 1/2) / 2^n.log2

  let tanLogArg (n : ℕ) : ℚ :=
    (tanLogReduced n - 1) / (tanLogReduced n + 1)

  let tanLogApprox (n : ℕ) : ℚ :=
    n.log2 * tanLogSum (1/3) + tanLogSum (tanLogArg n)

  let tanLogCheck (n a : ℕ) : Bool :=
    decide (0 ≤ tanLogArg n ∧ tanLogArg n ≤ 1/3 ∧
      (a:ℚ)/10^16 ≤ tanLogApprox n ∧
      tanLogApprox n + (n.log2 + 1 : ℚ)/10^22 ≤ ((a:ℚ)+1)/10^16)

  let tanLogRows : List (ℕ × ℕ) :=
    [(2048,76248630969869257),
    (1000001,138155120579631491),
    (900000000000,275256606002712774),
    (1020217,138355263978231575),
    (1020218,138355273780058243),
    (4907733,154063227842351849),
    (4907734,154063229879952094),
    (23608544,169771192595544576),
    (23608545,169771193019120023),
    (113568370,185479155967856759),
    (113568371,185479156055909444),
    (546318079,201187119272719336),
    (546318080,201187119291023691),
    (2628050765,216895082545435406),
    (2628050766,216895082549240508),
    (12642178764,232603045814201931),
    (12642178765,232603045814992934),
    (60814914994,248311009082439027),
    (60814914995,248311009082603460),
    (292548773007,264018972350426521),
    (292548773008,264018972350460704)]

  have tanLogTable : tanLogRows.all (fun p => tanLogCheck p.1 p.2) = true := by
    dsimp only [tanLogRows, tanLogCheck, tanLogApprox, tanLogArg, tanLogReduced, tanLogSum]
    decide +kernel

  have tan_log_interval {n a : ℕ} (h : (n,a) ∈ tanLogRows) :
      (a:ℝ)/10^16 ≤ Real.log ((n:ℝ)+1/2) ∧
      Real.log ((n:ℝ)+1/2) ≤ ((a:ℝ)+1)/10^16 := by
    have hh := List.all_eq_true.mp tanLogTable (n,a) h
    change decide _ = true at hh
    rcases of_decide_eq_true hh with ⟨h0, h3, hlo, hhi⟩
    have ht := tanLogSum_spec h0 h3
    have htwo := tanLogSum_spec (by norm_num : (0:ℚ) ≤ 1/3) (le_refl (1/3))
    rw [show (1+((1/3:ℚ):ℝ))/(1-((1/3:ℚ):ℝ)) = 2 by norm_num] at htwo
    have hy : 0 < tanLogReduced n := by dsimp only [tanLogReduced]; positivity
    have hratio : (1+tanLogArg n)/(1-tanLogArg n) = tanLogReduced n := by
      dsimp only [tanLogArg]
      field_simp [show tanLogReduced n + 1 ≠ 0 by linarith]
      ring
    have hratioR : (1+(tanLogArg n:ℝ))/(1-tanLogArg n) = (tanLogReduced n:ℝ) := by
      exact_mod_cast hratio
    rw [hratioR] at ht
    have hm : ((n:ℝ)+1/2) = 2^n.log2 * (tanLogReduced n:ℝ) := by
      dsimp only [tanLogReduced]
      push_cast
      field_simp
    rw [hm, Real.log_mul (by positivity) (by exact_mod_cast hy.ne'), Real.log_pow]
    have hk : (0:ℝ) ≤ n.log2 := Nat.cast_nonneg _
    have hlow := (Rat.cast_le (K := ℝ)).mpr hlo
    have hhigh := (Rat.cast_le (K := ℝ)).mpr hhi
    simp only [tanLogApprox] at hlow hhigh
    push_cast at hlow hhigh
    constructor
    · exact hlow.trans (add_le_add (mul_le_mul_of_nonneg_left htwo.1 hk) ht.1)
    · linarith [mul_le_mul_of_nonneg_left htwo.2 hk, ht.2]


  let tanNineLeft (i : Fin 9) : ℕ × ℕ := tanLogRows.getD (3 + 2*i.val) (0,0)
  let tanNineRight (i : Fin 9) : ℕ × ℕ := tanLogRows.getD (4 + 2*i.val) (0,0)

  have tanNineTable : ∀ i : Fin 9,
      let l := tanNineLeft i
      let r := tanNineRight i
      1000000 ≤ l.1 ∧ r.1 = l.1 + 1 ∧ l ∈ tanLogRows ∧ r ∈ tanLogRows ∧
      ((l.2:ℚ)+1)/10^16 + 0.30164032046780 + 1/10^14 <
        ((i.val:ℚ)+9) * (3.14159265358979323846/2) ∧
      ((i.val:ℚ)+9) * (3.14159265358979323847/2) + 1/10^14 <
        (r.2:ℚ)/10^16 + 0.30164032046750 := by
    dsimp only [tanNineLeft, tanNineRight, tanLogRows]
    decide +kernel

  have tanInteriorGap (s : ℕ → ℝ) (mono : Monotone s)
      (offset : ∀ n : ℕ, 1000000 ≤ n →
        0.30164032046750 ≤ s n - Real.log ((n:ℝ)+1/2) ∧
        s n - Real.log ((n:ℝ)+1/2) ≤ 0.30164032046780)
      (n : ℕ) (i : Fin 9) :
      1/10^14 < |s n - ((i.val:ℝ)+9)*(Real.pi/2)| := by
    obtain ⟨hl, hadj, hleft, hright, hlow, hhigh⟩ := tanNineTable i
    have loR := (Rat.cast_lt (K := ℝ)).mpr hlow
    have hiR := (Rat.cast_lt (K := ℝ)).mpr hhigh
    push_cast at loR hiR
    have hpos : 0 ≤ (i.val:ℝ)+9 := by positivity
    by_cases hn : n ≤ (tanNineLeft i).1
    · have hlog := (tan_log_interval (n := (tanNineLeft i).1) (a := (tanNineLeft i).2) hleft).2
      have hs := (offset _ hl).2
      have hpi := mul_le_mul_of_nonneg_left (le_of_lt Real.pi_gt_d20) hpos
      apply lt_of_lt_of_le _ (neg_le_abs _)
      linarith only [loR, hlog, hs, mono hn, hpi]
    · have hn' : (tanNineRight i).1 ≤ n := by omega
      have hlog := (tan_log_interval (n := (tanNineRight i).1) (a := (tanNineRight i).2) hright).1
      have hs := (offset (tanNineRight i).1 (by omega)).1
      have hpi := mul_le_mul_of_nonneg_left (le_of_lt Real.pi_lt_d20) hpos
      apply lt_of_lt_of_le _ (le_abs_self _)
      linarith only [hiR, hlog, hs, mono hn', hpi]

  have tan_nine_gap (s : ℕ → ℝ) (mono : Monotone s)
      (offset : ∀ n : ℕ, 1000000 ≤ n →
        0.30164032046750 ≤ s n - Real.log ((n:ℝ)+1/2) ∧
        s n - Real.log ((n:ℝ)+1/2) ≤ 0.30164032046780)
      (n : ℕ) (lo : 1000001 ≤ n) (hi : n ≤ 900000000000) (j : ℤ) :
      1/10^14 < |s n-(j:ℝ)*(Real.pi/2)| := by
    by_cases jl : j ≤ 8
    · have hlog := (tan_log_interval (n := 1000001) (a := 138155120579631491) (by dsimp only [tanLogRows]; decide)).1
      have hs := (offset 1000001 (by decide)).1
      have hj : (j:ℝ)*(Real.pi/2) ≤ 8*(Real.pi/2) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast jl) (by positivity)
      apply lt_of_lt_of_le _ (le_abs_self _)
      linarith only [hj, hlog, hs, mono lo, Real.pi_lt_d20]
    by_cases ju : 18 ≤ j
    · have hlog := (tan_log_interval (n := 900000000000) (a := 275256606002712774) (by dsimp only [tanLogRows]; decide)).2
      have hs := (offset 900000000000 (by decide)).2
      have hj : 18*(Real.pi/2) ≤ (j:ℝ)*(Real.pi/2) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast ju) (by positivity)
      apply lt_of_lt_of_le _ (neg_le_abs _)
      linarith only [hj, hlog, hs, mono hi, Real.pi_gt_d20]
    let i : Fin 9 := ⟨(j-9).toNat, by omega⟩
    have he : (i.val:ℝ)+9 = j := by
      exact_mod_cast (show (i.val:ℤ)+9 = j by dsimp [i]; omega)
    simpa only [he] using tanInteriorGap s mono offset n i

  exact ⟨tan_log_interval (n := 2048) (a := 76248630969869257) (by dsimp only [tanLogRows]; decide), tan_nine_gap⟩

open Real

private theorem tan_phase_offset (s : ℕ → ℝ)
    (step : ∀ n : ℕ, s (n+1) = s n + Real.arctan (1/((n:ℝ)+1)))
    (anchor : (3170601386840298533498:ℝ)/(4*10^20) ≤ s 2048 ∧
      s 2048 ≤ (3170601386840298541747:ℝ)/(4*10^20))
    (n : ℕ) (hn : 1000000 ≤ n) :
    0.30164032046750 ≤ s n - Real.log ((n:ℝ)+1/2) ∧
       s n - Real.log ((n:ℝ)+1/2) ≤ 0.30164032046780 := by
  obtain ⟨LL,LU⟩ := tan_log_and_gaps.1
  obtain ⟨low,high⟩ := ArctanPhaseRefinement.finite_estimate step 2048 n (by decide) (by omega)
  have Npos : (1000000:ℝ) ≤ n := by exact_mod_cast hn
  have qpos : 0 ≤ 1/(4*(n:ℝ)^4) := by positivity
  have cpos : 0 ≤ 5/(24*((n:ℝ)+1/2)^2) := by positivity
  have cup : 5/(24*((n:ℝ)+1/2)^2) ≤ (5:ℝ)/(24*(1000000:ℝ)^2) := by
    gcongr
    linarith
  replace high := (le_add_of_nonneg_right qpos).trans high
  obtain ⟨amin,amax⟩ := anchor
  norm_num at LL LU low high amin amax cup qpos cpos ⊢
  constructor <;> linarith

/-- Throughout this dyadic interval the phase stays between the 28th and
29th half-turns, with a margin of more than one eighth on either side. -/
theorem tan_upper_sector (s : ℕ → ℝ) (n : ℕ) (lo : 2^64 ≤ n) (hi : n ≤ 2^65)
    (offset : 0.30164032046750 ≤ s n - Real.log ((n:ℝ)+1/2) ∧
      s n - Real.log ((n:ℝ)+1/2) ≤ 0.30164032046780) (j : ℤ) :
    1/8 < |s n - (j:ℝ)*(Real.pi/2)| := by
  have hlo : (2:ℝ)^64 ≤ n := by exact_mod_cast lo
  have hhi : (n:ℝ) ≤ 2^65 := by exact_mod_cast hi
  have l := Real.log_le_log (by positivity : (0:ℝ) < 2^64)
    (show (2:ℝ)^64 ≤ n+1/2 by linarith only [hlo])
  have u := Real.log_le_log (by positivity : (0:ℝ) < n+1/2)
    (show (n:ℝ)+1/2 ≤ 2^65*(101/100) by linarith only [hhi])
  rw [Real.log_pow] at l
  rw [Real.log_mul (by positivity) (by norm_num), Real.log_pow] at u
  have hcorr := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 101/100)
  by_cases hj : j ≤ 28
  · have hj' : (j:ℝ)*(Real.pi/2) ≤ 28*(Real.pi/2) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hj) (by positivity)
    apply lt_of_lt_of_le _ (le_abs_self _)
    linarith only [hj', l, offset.1, Real.log_two_gt_d9, Real.pi_lt_d4]
  · have hj' : 29*(Real.pi/2) ≤ (j:ℝ)*(Real.pi/2) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast (show 29 ≤ j by omega)) (by positivity)
    apply lt_of_lt_of_le _ (neg_le_abs _)
    linarith only [hj', u, hcorr, offset.2, Real.log_two_lt_d9, Real.pi_gt_d4]

/- The scaled-coordinate induction is HudZah's proof from Left to Solve PR #327.
   The complementary-angle and grid arguments are adapted from mattdorman's
   Arxiv.2607.05739.tan_arctan_sum_not_integer.R3, Left to Solve PR #9451. -/
namespace ArctanGridRefinement

open Arxiv.«2607.05739» Finset

private lemma scaled_coordinates (n : ℕ) :
    ∃ c : ℝ, 0 < c ∧
      Real.cos (∑ k ∈ Icc 1 n, Real.arctan k) = c * (A n : ℝ) ∧
      Real.sin (∑ k ∈ Icc 1 n, Real.arctan k) = c * (B n : ℝ) := by
  induction n with
  | zero =>
    exact ⟨1, zero_lt_one, by norm_num [A, gaussProd], by norm_num [B, gaussProd]⟩
  | succ n ih =>
    obtain ⟨c, hc, hcos, hsin⟩ := ih
    let t : ℝ := (n + 1 : ℕ)
    have ht := Real.cos_arctan_pos t
    have hs : Real.sin (Real.arctan t) = t * Real.cos (Real.arctan t) := by
      apply (div_eq_iff ht.ne').mp
      rw [← Real.tan_eq_sin_div_cos, Real.tan_arctan]
    have hp : gaussProd (n + 1) = gaussProd n * (⟨1, (n + 1 : ℕ)⟩ : GaussianInt) := by
      unfold gaussProd
      rw [prod_Icc_succ_top (by omega)]
    have ha : (A (n + 1) : ℝ) = A n - t * B n := by
      simp [A, B, hp, t, sub_eq_add_neg]
      ring
    have hb : (B (n + 1) : ℝ) = t * A n + B n := by
      simp [A, B, hp, t]
      ring
    refine ⟨c * Real.cos (Real.arctan t), mul_pos hc ht, ?_, ?_⟩
    · rw [sum_Icc_succ_top (by omega), Real.cos_add, hcos, hsin, ha]
      change _ - _ * Real.sin (Real.arctan t) = _
      rw [hs]
      ring
    · rw [sum_Icc_succ_top (by omega), Real.sin_add, hcos, hsin, hb]
      change _ + _ * Real.sin (Real.arctan t) = _
      rw [hs]
      ring

private lemma arctan_upper {t : ℝ} (ht : 0 ≤ t) : Real.arctan t ≤ t := by
  simpa only [Real.tan_arctan] using
    Real.le_tan (Real.arctan_nonneg.mpr ht) (Real.arctan_lt_pi_div_two t)

private lemma arctan_abs (t : ℝ) : |Real.arctan t| ≤ |t| := by
  rcases le_or_gt 0 t with h | h
  · simpa [abs_of_nonneg h, abs_of_nonneg (Real.arctan_nonneg.mpr h)] using arctan_upper h
  · simpa [abs_of_nonpos h.le, abs_of_nonpos (Real.arctan_le_zero.mpr h.le)] using
      arctan_upper (neg_nonneg.mpr h.le)

private lemma complementary_angles (n : ℕ) :
    (∑ j ∈ Icc 1 n, Real.arctan j) + angleSum n = (n:ℝ)*(Real.pi/2) := by
  unfold angleSum
  rw [← sum_add_distrib]
  calc
    _ = ∑ _j ∈ Icc 1 n, Real.pi/2 := by
      apply sum_congr rfl
      intro j hj
      have hp : 0 < (j:ℝ) := by exact_mod_cast (mem_Icc.mp hj).1
      rw [one_div,Real.arctan_inv_of_pos hp]
      ring
    _ = _ := by simp [Nat.card_Icc,nsmul_eq_mul]

theorem close_to_grid {n : ℕ} {m : ℤ} (hm : B n = A n*m) (hm₀ : m ≠ 0) :
    ∃ j : ℤ, |angleSum n - (j:ℝ)*(Real.pi/2)| ≤ 1/|(m:ℝ)| := by
  let θ := ∑ k ∈ Icc 1 n, Real.arctan k
  let ε := Real.arctan (1/(m:ℝ))
  obtain ⟨c,_hc,hcos,hsin⟩ := scaled_coordinates n
  have hε : Real.sin ε = (1/(m:ℝ)) * Real.cos ε := by
    apply (div_eq_iff (Real.cos_arctan_pos _).ne').mp
    exact (Real.tan_eq_sin_div_cos _).symm.trans (Real.tan_arctan _)
  have zm : (m:ℝ) ≠ 0 := by exact_mod_cast hm₀
  have hzero : Real.cos (θ+ε) = 0 := by
    rw [Real.cos_add,hε]
    dsimp only [θ]
    rw [hcos,hsin,hm,Int.cast_mul]
    field_simp
    ring
  obtain ⟨r,hr⟩ := Real.cos_eq_zero_iff.mp hzero
  let j : ℤ := n-(2*r+1)
  have hs := complementary_angles n
  change θ+angleSum n = _ at hs
  have he : angleSum n - (j:ℝ)*(Real.pi/2) = ε := by
    dsimp only [j]
    push_cast
    linarith only [hs,hr]
  refine ⟨j,?_⟩
  rw [he]
  simpa only [ε,abs_div,abs_one] using arctan_abs (1/(m:ℝ))

theorem zero_on_grid {n : ℕ} (hm : B n = A n*0) :
    ∃ j : ℤ, angleSum n = (j : ℝ)*(Real.pi/2) := by
  obtain ⟨c,_,_,hsin⟩ := scaled_coordinates n
  have hzero : Real.sin (∑ k ∈ Icc 1 n, Real.arctan k) = 0 := by
    simpa only [hm, mul_zero, Int.cast_zero] using hsin
  obtain ⟨k,hk⟩ := Real.sin_eq_zero_iff.mp hzero
  refine ⟨(n : ℤ)-2*k, ?_⟩
  push_cast
  linarith only [complementary_angles n, hk]

end ArctanGridRefinement

/- The Lucas witness, the prime and its square root of minus one are from
mattdorman's Arxiv.2607.05739.tan_arctan_sum_not_integer.R3 (PR #9451).
The binary-power and Lucas lemmas below are from R1 and R3. -/
namespace ArctanWordSlope

open Arxiv.«2607.05739»

/-- Binary modular powering, reducing after each square and multiply. -/
private lemma pow_bits (p a n : ℕ) :
    ((n.bits.foldr (fun b v => (if b then v*v*a else v*v)%p) 1 : ℕ) : ZMod p) = (a : ZMod p)^n := by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit b n hb ih =>
    rw [Nat.bits_append_bit n b hb,List.foldr_cons,ZMod.natCast_mod]
    cases b <;> simp [Nat.bit_val,Nat.cast_mul,ih,two_mul,pow_add]

/-- Lucas's criterion with the factors of the square root of `p-1` supplied explicitly. -/
private lemma from_witness (p k a : ℕ) (factors : List ℕ) (hs : p-1=k^2) (hf : factors.prod=k)
    (hp : ∀ q ∈ factors, q.Prime)
    (hc : let v (n : ℕ) := n.bits.foldr (fun b t => (if b then t*t*a else t*t)%p) 1
      v (p-1)=1 ∧ factors.all (fun q => decide ((v ((p-1)/q) : ZMod p) ≠ 1))=true) : p.Prime := by
  let v (n : ℕ) := n.bits.foldr (fun b t => (if b then t*t*a else t*t)%p) 1
  change v (p-1)=1 ∧ factors.all (fun q => decide ((v ((p-1)/q) : ZMod p) ≠ 1))=true at hc
  have hpow (n : ℕ) : (v n : ZMod p)=(a : ZMod p)^n := pow_bits p a n
  apply lucas_primality p (a : ZMod p)
  · rw [← hpow,hc.1,Nat.cast_one]
  · intro q hq hd
    have hmem : q ∈ factors := mem_list_primes_of_dvd_prod (Nat.prime_iff.mp hq)
      (fun b hb => Nat.prime_iff.mp (hp b hb)) (hf ▸ hq.dvd_of_dvd_pow (hs ▸ hd))
    have hv := of_decide_eq_true (List.all_eq_true.mp hc.2 q hmem)
    rwa [hpow] at hv

private lemma word_prime : Nat.Prime 63999977760001932101 := by
  apply from_witness 63999977760001932101 7999998610 2 [2, 5, 53, 193, 197, 397]
  · decide
  · decide
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num
  · decide +kernel

/-- A single split-prime test forces the absolute slope to be at least 7999998610. -/
theorem residue_bound {m : ℤ}
    (residue : (m : ZMod 63999977760001932101) = (7999998610 : ZMod 63999977760001932101)) :
    7999998610 ≤ |m| := by
  have hdiv : (63999977760001932101 : ℤ) ∣ m-7999998610 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub 7999998610 m 63999977760001932101).mp
      (by simpa only [Int.cast_ofNat] using residue.symm)
  rcases hdiv with ⟨q,hq⟩
  rcases le_or_gt 0 q with h | h
  · exact (show 7999998610 ≤ m by omega).trans (le_abs_self m)
  · exact (show 7999998610 ≤ -m by omega).trans (neg_le_abs m)

/-- Applies everywhere the split prime is larger than the index plus its root. -/
theorem slope_large {n : ℕ} {m : ℤ} (lo : 7999998610 ≤ n)
    (hi : n+7999998610 < 63999977760001932101) (hm : B n = A n*m) :
    7999998610 ≤ |m| := by
  apply residue_bound
  exact ArctanCert.signed_residue word_prime (by decide : 1 ≤ 7999998610) lo hi (by decide) hm

theorem word_slope {n : ℕ} {m : ℤ} (lo : 2^64 ≤ n) (hi : n ≤ 2^65)
    (hm : B n = A n*m) : 8 ≤ |m| := by
  have hlo : 7999998610 ≤ n := (by decide : 7999998610 ≤ 2^64).trans lo
  have hhi : n+7999998610 < 63999977760001932101 :=
    (Nat.add_le_add_right hi _).trans_lt (by decide)
  exact (by decide : (8:ℤ) ≤ 7999998610).trans (slope_large hlo hhi hm)

end ArctanWordSlope

open Arxiv.«2607.05739» Finset

private theorem tan_actual_step (n : ℕ) :
    angleSum (n+1) = angleSum n + Real.arctan (1/((n:ℝ)+1)) := by
  simp only [angleSum,sum_Icc_succ_top (by omega : 1 ≤ n+1), Nat.cast_succ]

private theorem tan_actual_offset (n : ℕ) (hn : 1000000 ≤ n) :
    0.30164032046750 ≤ angleSum n - Real.log ((n:ℝ)+1/2) ∧
      angleSum n - Real.log ((n:ℝ)+1/2) ≤ 0.30164032046780 :=
  tan_phase_offset angleSum tan_actual_step tan_angle_anchor_Icc_2048 n hn

private theorem tan_actual_grid {n : ℕ} {m : ℤ} (hm : B n = A n*m) :
    ∃ j : ℤ, |angleSum n - (j:ℝ)*(Real.pi/2)| ≤ 1/|(m:ℝ)| := by
  by_cases hz : m = 0
  · subst m
    obtain ⟨j,hj⟩ := ArctanGridRefinement.zero_on_grid hm
    exact ⟨j, by simp [hj]⟩
  exact ArctanGridRefinement.close_to_grid hm hz

/-- The first dyadic interval beyond the unsigned 64-bit range. -/
theorem nonintegral_from_two_pow_64_to_two_pow_65 {n : ℕ}
    (lo : 2^64 ≤ n) (hi : n ≤ 2^65) : ¬ IsIntegerValue n := by
  rintro ⟨m,hm⟩
  obtain ⟨j,hj⟩ := tan_actual_grid hm
  have H := ArctanWordSlope.word_slope lo hi hm
  have hr : (8:ℝ) ≤ |(m:ℝ)| := by exact_mod_cast H
  have reciprocal : 1/|(m:ℝ)| ≤ (1:ℝ)/8 := one_div_le_one_div_of_le (by norm_num) hr
  exact (not_lt_of_ge (hj.trans reciprocal)) (tan_upper_sector angleSum n lo hi
    (tan_actual_offset n ((by decide : 1000000 ≤ 2^64).trans lo)) j)

/-- The nine crossings in the parent CRT certificate's finite range. -/
private theorem tan_exclude_finite {n : ℕ} {m : ℤ} (lo : 1000000 < n) (hi : n ≤ 900000000000)
    (big : (10:ℤ)^119 ≤ |m|) (hm : B n = A n*m) : False := by
  have mono : Monotone angleSum := by
    apply monotone_nat_of_le_succ
    intro i
    rw [tan_actual_step]
    exact le_add_of_nonneg_right (Real.arctan_nonneg.mpr (by positivity))
  obtain ⟨j,hj⟩ := tan_actual_grid hm
  have H : (10:ℝ)^14 ≤ |(m:ℝ)| := by
    exact_mod_cast (show (10:ℤ)^14 ≤ |m| from (by norm_num : (10:ℤ)^14 ≤ 10^119).trans big)
  exact (not_lt_of_ge (hj.trans (one_div_le_one_div_of_le (by norm_num) H)))
    (tan_log_and_gaps.2 angleSum mono tan_actual_offset n lo hi j)

end ArctanNumericPhase

namespace OMA.R_Arxiv_2607_05739_tan_arctan_sum_not_integer_R1_H2_R1

open Arxiv.«2607.05739»

/-- Rule out surviving slopes in logarithmic bands centered at whole multiples of π. -/
def H1 : Prop :=
  ∀ n : ℕ, 900000000000 < n → (n < 2^64 ∨ 2^65 < n) →
    (∀ p : ℕ, p.Prime → p%4=3 → ¬(p:ℤ) ∣ A (n%p)) →
    let S : ℤ := 2^96 * ((n:ℤ)+1)^6
    let w : ℕ → ℤ × ℤ := Nat.rec (S,0) (fun j z =>
      (z.1 / ((j+1 : ℕ) : ℤ) - z.2, z.1 + z.2 / ((j+1 : ℕ) : ℤ)))
    ∀ (m k : ℤ), |m| ≤ 2*(n.factorial:ℤ) →
      |(w n).2-m*(w n).1| ≤ 4*(n:ℤ)*(1+|m|) →
      (∀ a p : ℕ, 1 ≤ a → a ≤ n → p.Prime → n+a < p → p ∣ 1+a^2 →
        (m : ZMod p) = (a : ZMod p)) →
      let x := Real.log ((n:ℝ)+1/2) - (k:ℝ)*Real.pi
      (-(1/|(m:ℝ)|) - 0.30164032046780 ≤ x) →
      x ≤ 1/|(m:ℝ)| - 0.30164032046750 →
      B n ≠ A n*m

/-- Rule out surviving slopes in bands centered at the odd half-multiples of π. -/
def H2 : Prop :=
  ∀ n : ℕ, 900000000000 < n → (n < 2^64 ∨ 2^65 < n) →
    (∀ p : ℕ, p.Prime → p%4=3 → ¬(p:ℤ) ∣ A (n%p)) →
    let S : ℤ := 2^96 * ((n:ℤ)+1)^6
    let w : ℕ → ℤ × ℤ := Nat.rec (S,0) (fun j z =>
      (z.1 / ((j+1 : ℕ) : ℤ) - z.2, z.1 + z.2 / ((j+1 : ℕ) : ℤ)))
    ∀ (m k : ℤ), |m| ≤ 2*(n.factorial:ℤ) →
      |(w n).2-m*(w n).1| ≤ 4*(n:ℤ)*(1+|m|) →
      (∀ a p : ℕ, 1 ≤ a → a ≤ n → p.Prime → n+a < p → p ∣ 1+a^2 →
        (m : ZMod p) = (a : ZMod p)) →
      let x := Real.log ((n:ℝ)+1/2) - ((k:ℝ)+1/2)*Real.pi
      (-(1/|(m:ℝ)|) - 0.30164032046780 ≤ x) →
      x ≤ 1/|(m:ℝ)| - 0.30164032046750 →
      B n ≠ A n*m

theorem main : H1 → H2 → OMA.R_Arxiv_2607_05739_tan_arctan_sum_not_integer_R1.H2 := by
  intro even odd n lo inert _ S w m mb large win signed hm
  by_cases small : n ≤ 900000000000
  · exact ArctanNumericPhase.tan_exclude_finite lo small (large small) hm
  by_cases word : 2^64 ≤ n ∧ n ≤ 2^65
  · exact ArctanNumericPhase.nonintegral_from_two_pow_64_to_two_pow_65 word.1 word.2 ⟨m,hm⟩
  have outside : n < 2^64 ∨ 2^65 < n := by omega
  obtain ⟨j,hj⟩ := ArctanNumericPhase.tan_actual_grid hm
  obtain ⟨hl,hu⟩ := abs_le.mp hj
  obtain ⟨ol,ou⟩ := ArctanNumericPhase.tan_actual_offset n (by omega)
  let k : ℤ := j/2
  rcases (show j = 2*k ∨ j = 2*k+1 by dsimp [k]; omega) with he | he
  · have hj' : (j:ℝ) = 2*(k:ℝ) := by exact_mod_cast he
    apply even n (by omega) outside inert m k mb win signed _ _ hm <;>
      rw [hj'] at hl hu <;> linarith only [hl,hu,ol,ou]
  · have hj' : (j:ℝ) = 2*(k:ℝ)+1 := by exact_mod_cast he
    apply odd n (by omega) outside inert m k mb win signed _ _ hm <;>
      rw [hj'] at hl hu <;> linarith only [hl,hu,ol,ou]

end OMA.R_Arxiv_2607_05739_tan_arctan_sum_not_integer_R1_H2_R1
