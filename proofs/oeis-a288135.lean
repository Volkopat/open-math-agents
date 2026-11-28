import OMAStatements.S_oeis_a288135
import Mathlib

/-! Clearing three short shifts turns the denominator into a series starting
with 1 - 2X. The bounded tail then preserves a fixed growth ratio for the inverse. -/

namespace A288135Proof

open Finset PowerSeries OMA.S_oeis_a288135
open scoped PowerSeries

private abbrev PS := PowerSeries ℚ
private noncomputable abbrev x : PS := X

private theorem coeff_product (F G : PS) (n : ℕ) :
    coeff n (F * G) = ∑ j ∈ range (n + 1), coeff j F * coeff (n - j) G := by
  rw [coeff_mul]
  exact Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i F * coeff j G) n

private theorem inverse_growth (H : PS) (h0 : coeff 0 H = 1) (h1 : coeff 1 H = -2)
    (hsmall : ∀ j, 2 ≤ j → j ≤ 5 → coeff j H = 0)
    (hlarge : ∀ j, 6 ≤ j → coeff j H ≤ 1) :
    let c := fun n => coeff n H⁻¹
    ∀ n, 0 < c n ∧ (∑ j ∈ range (n + 1), c j) ≤ 3 * c n ∧
      (1 ≤ n → (3 / 2 : ℚ) * c (n - 1) ≤ c n) := by
  let c := fun n => coeff n H⁻¹
  change ∀ n, 0 < c n ∧ (∑ j ∈ range (n + 1), c j) ≤ 3 * c n ∧
    (1 ≤ n → (3 / 2 : ℚ) * c (n - 1) ≤ c n)
  have hc0 : c 0 = 1 := by
    simp only [c, coeff_zero_eq_constantCoeff_apply, constantCoeff_inv]
    rw [← coeff_zero_eq_constantCoeff_apply, h0, inv_one]
  have hmul : H * H⁻¹ = 1 := by
    apply PowerSeries.mul_inv_cancel
    rw [← coeff_zero_eq_constantCoeff_apply, h0]
    norm_num
  have recurrence (n : ℕ) (hn : 1 ≤ n) :
      c n = 2 * c (n - 1) -
        ∑ j ∈ range (n - 5), coeff (6 + j) H * c (n - (6 + j)) := by
    have eq := congrArg (coeff n) hmul
    rw [coeff_product, coeff_one, if_neg (by omega)] at eq
    change (∑ j ∈ range (n + 1), coeff j H * c (n - j)) = 0 at eq
    by_cases hb : n ≤ 5
    · have hz : n - 5 = 0 := by omega
      rw [hz, sum_range_zero, sub_zero]
      interval_cases n <;>
        simp [sum_range_succ, h0, h1, hsmall 2 (by decide) (by decide),
          hsmall 3 (by decide) (by decide), hsmall 4 (by decide) (by decide),
          hsmall 5 (by decide) (by decide)] at eq ⊢ <;> linarith
    · rw [show n + 1 = 6 + (n - 5) by omega, sum_range_add] at eq
      simp only [show (6 : ℕ) = 5 + 1 by decide, sum_range_succ] at eq
      norm_num [h0, h1, hsmall 2 (by decide) (by decide),
        hsmall 3 (by decide) (by decide), hsmall 4 (by decide) (by decide),
        hsmall 5 (by decide) (by decide)] at eq
      linarith
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simp [hc0]
    have hn1 : 1 ≤ n := by omega
    have hprev := (ih (n - 1) (by omega)).1
    have htail : (∑ j ∈ range (n - 5), coeff (6 + j) H * c (n - (6 + j)))
        ≤ 1 / 2 * c (n - 1) := by
      by_cases h6 : 6 ≤ n
      · have hsum : (∑ j ∈ range (n - 5), c (n - (6 + j))) =
            ∑ j ∈ range (n - 5), c j := by
          rw [← sum_range_reflect (f := c)]
          apply sum_congr rfl
          intro j hj
          have hmem := mem_range.mp hj
          congr 1
          omega
        calc
          _ ≤ ∑ j ∈ range (n - 5), c (n - (6 + j)) := by
            apply sum_le_sum
            intro j hj
            exact mul_le_of_le_one_left (ih _ (by omega)).1.le (hlarge _ (by omega))
          _ = _ := hsum
          _ ≤ 3 * c (n - 6) := by
            rw [show n - 5 = n - 6 + 1 by omega]
            exact (ih _ (by omega)).2.1
          _ ≤ 1 / 2 * c (n - 1) := by
            have hs (i : ℕ) (hi : 1 ≤ i) (hi' : i ≤ 5) :
                (3 / 2 : ℚ) * c (n - (i+1)) ≤ c (n - i) := by
              simpa only [Nat.sub_sub] using (ih (n - i) (by omega)).2.2 (by omega)
            linarith [hs 1 (by decide) (by decide), hs 2 (by decide) (by decide),
              hs 3 (by decide) (by decide), hs 4 (by decide) (by decide),
              hs 5 (by decide) (by decide), (ih (n-6) (by omega)).1]
      · rw [show n - 5 = 0 by omega, sum_range_zero]
        positivity
    have hg : (3 / 2 : ℚ) * c (n - 1) ≤ c n := by
      linarith [recurrence n hn1]
    refine ⟨by linarith, ?_, fun _ => hg⟩
    rw [sum_range_succ]
    have hs := (ih (n - 1) (by omega)).2.1
    rw [show n - 1 + 1 = n by omega] at hs
    linarith


private noncomputable def multiplier : PS := (1 + x) * (1 - x ^ 2)

private theorem coeff_multiplier (F : PS) (n : ℕ) :
    coeff n (multiplier * F) = coeff n F
      + (if 1 ≤ n then coeff (n - 1) F else 0)
      - (if 2 ≤ n then coeff (n - 2) F else 0)
      - (if 3 ≤ n then coeff (n - 3) F else 0) := by
  rw [show multiplier * F = F + x ^ 1 * F - x ^ 2 * F - x ^ 3 * F by
    unfold multiplier
    ring]
  simp only [map_add, map_sub, coeff_X_pow_mul']

private theorem floor_weight (r : ℝ) (n k : ℕ)
    (hl : (k : ℝ) ≤ ((n : ℝ) + 1) * r) (hu : ((n : ℝ) + 1) * r < (k : ℝ) + 1) :
    weight r n = k := by
  have he : ⌊((n : ℝ) + 1) * r⌋ = (k : ℤ) := by
    apply Int.floor_eq_iff.mpr
    exact ⟨by simpa using hl, by simpa using hu⟩
  simp [weight, he]

private theorem floor_diff {r : ℝ} (hlo : 1 ≤ r) (hhi : r < 2) (n : ℕ) :
    1 ≤ weight r (n+1) - weight r n ∧ weight r (n+1) - weight r n ≤ 2 := by
  let t : ℝ := ((n : ℝ) + 1)*r
  have ht : ((↑(n + 1) : ℝ) + 1)*r = t + r := by
    push_cast
    dsimp [t]
    ring
  rw [weight, weight, ht]
  have h1 : ⌊t⌋ + 1 ≤ ⌊t+r⌋ := by
    apply Int.le_floor.mpr
    push_cast
    linarith [Int.floor_le t]
  have h2 : ⌊t+r⌋ < ⌊t⌋ + 3 := by
    apply Int.floor_lt.mpr
    push_cast
    linarith [Int.lt_floor_add_one t]
  have hh : ⌊t+r⌋ ≤ ⌊t⌋ + 2 := by omega
  have hlz : (1 : ℤ) ≤ ⌊t+r⌋ - ⌊t⌋ := by omega
  have huz : ⌊t+r⌋ - ⌊t⌋ ≤ (2 : ℤ) := by omega
  change 1 ≤ ((⌊t+r⌋ : ℤ) : ℚ) - ((⌊t⌋ : ℤ) : ℚ) ∧
    ((⌊t+r⌋ : ℤ) : ℚ) - ((⌊t⌋ : ℤ) : ℚ) ≤ 2
  constructor
  · rw [← Int.cast_sub]
    exact Int.cast_le.mpr hlz
  · rw [← Int.cast_sub]
    exact Int.cast_le.mpr huz

private theorem monotone_of_ratio {r : ℝ} (hlo : (3 / 2 : ℝ) ≤ r) (hhi : r < 8 / 5) :
    StrictMono (a r) := by
  let H := multiplier * denominator r
  let c := fun n => coeff n H⁻¹
  have w0 : weight r 0 = 1 := by apply floor_weight <;> norm_num <;> linarith
  have w1 : weight r 1 = 3 := by apply floor_weight <;> norm_num <;> linarith
  have w2 : weight r 2 = 4 := by apply floor_weight <;> norm_num <;> linarith
  have w3 : weight r 3 = 6 := by apply floor_weight <;> norm_num <;> linarith
  have w4 : weight r 4 = 7 := by apply floor_weight <;> norm_num <;> linarith
  have w5 : weight r 5 = 9 := by apply floor_weight <;> norm_num <;> linarith
  have hcoeff (i : ℕ) : coeff i H =
      (-1)^i * weight r i
      + (if 1 ≤ i then (-1)^(i-1) * weight r (i-1) else 0)
      - (if 2 ≤ i then (-1)^(i-2) * weight r (i-2) else 0)
      - (if 3 ≤ i then (-1)^(i-3) * weight r (i-3) else 0) := by
    simp only [H, coeff_multiplier, denominator, coeff_mk]
  have h0 : coeff 0 H = 1 := by rw [hcoeff]; norm_num [w0]
  have h1 : coeff 1 H = -2 := by rw [hcoeff]; norm_num [w0,w1]
  have hsmall : ∀ j, 2 ≤ j → j ≤ 5 → coeff j H = 0 := by
    intro j hj hj'
    interval_cases j <;> rw [hcoeff] <;> norm_num [w0,w1,w2,w3,w4,w5]
  have hlarge : ∀ j, 6 ≤ j → coeff j H ≤ 1 := by
    intro j hj
    let n := j-3
    have heq : j = n+3 := by dsimp [n]; omega
    rw [heq, hcoeff]
    simp only [if_pos (show 1 ≤ n+3 by omega), if_pos (show 2 ≤ n+3 by omega),
      if_pos (show 3 ≤ n+3 by omega), show n+3-1 = n+2 by omega,
      show n+3-2 = n+1 by omega, show n+3-3 = n by omega, pow_add]
    have hd1 := floor_diff (by linarith : 1 ≤ r) (by linarith : r < 2) (n+2)
    have hd2 := floor_diff (by linarith : 1 ≤ r) (by linarith : r < 2) n
    rcases neg_one_pow_eq_or (R := ℚ) n with hn | hn <;>
      rw [hn] <;> norm_num <;> linarith [hd1.1,hd1.2,hd2.1,hd2.2]
  have hg := inverse_growth H h0 h1 hsmall hlarge
  have hd : constantCoeff (denominator r) ≠ 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    simp [denominator, w0]
  have hH : H⁻¹ * H = 1 := by
    apply PowerSeries.inv_mul_cancel
    rw [← coeff_zero_eq_constantCoeff_apply, h0]
    norm_num
  have ha : (denominator r)⁻¹ = multiplier * H⁻¹ := by
    apply (inv_eq_iff_mul_eq_one hd).mpr
    rw [mul_comm multiplier, mul_assoc]
    exact hH
  have hf (n : ℕ) : a r n = c n + (if 1 ≤ n then c (n-1) else 0)
      - (if 2 ≤ n then c (n-2) else 0) - (if 3 ≤ n then c (n-3) else 0) := by
    unfold a
    rw [ha]
    exact coeff_multiplier H⁻¹ n
  have hpos (n : ℕ) : 0 < c n := (hg n).1
  have hstep (n : ℕ) : (3 / 2 : ℚ) * c n ≤ c (n+1) := by
    simpa using (hg (n+1)).2.2 (Nat.succ_pos n)
  have htwo (n : ℕ) : 2 * c n < c (n+2) := by
    linarith [hpos n, hstep n, hstep (n+1)]
  apply strictMono_nat_of_lt_succ
  intro n
  rw [hf, hf]
  by_cases hn : 3 ≤ n
  · simp only [if_pos (show 1 ≤ n by omega), if_pos (show 2 ≤ n by omega), if_pos hn,
      if_pos (show 1 ≤ n+1 by omega), if_pos (show 2 ≤ n+1 by omega),
      if_pos (show 3 ≤ n+1 by omega), show n+1-1 = n by omega,
      show n+1-2 = n-1 by omega, show n+1-3 = n-2 by omega]
    have ht := htwo (n-1)
    rw [show n-1+2 = n+1 by omega] at ht
    linarith [hpos (n-3)]
  · interval_cases n <;> norm_num <;> linarith [hpos 1, htwo 0, htwo 1]

end A288135Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a288135.main := by
  apply A288135Proof.monotone_of_ratio
  · exact (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
  · exact (Real.sqrt_lt (by norm_num) (by norm_num)).2 (by norm_num)
