import OMAStatements.S_oeis_a227512

namespace A227512P
open OMA.S_oeis_a227512 PowerSeries

lemma bnd (y : ℝ) (hy : 1 ≤ y) :
    12 * y ^ 3 - 9 * y / 5 - 1 / 10 < 1 / (Real.log ((2 * y + 1) / (2 * y - 1)) - 1 / y) ∧
      1 / (Real.log ((2 * y + 1) / (2 * y - 1)) - 1 / y) < 12 * y ^ 3 - 9 * y / 5 := by
  have hy0 : 0 < y := by linarith
  have h1 : 0 < 2 * y - 1 := by linarith
  have h2 : 0 < 2 * y + 1 := by linarith
  have hy0' : y ≠ 0 := hy0.ne'
  have h1' : 2 * y - 1 ≠ 0 := h1.ne'
  have h2' : 2 * y + 1 ≠ 0 := h2.ne'
  have ha : 0 < y - 1 / 2 := by linarith
  have ha' : y - 1 / 2 ≠ 0 := ha.ne'
  have hs := Real.hasSum_log_one_add_inv ha
  have e1 : 1 + (y - 1 / 2)⁻¹ = (2 * y + 1) / (2 * y - 1) := by
    have hi : (y - 1 / 2)⁻¹ = 2 / (2 * y - 1) := by
      rw [inv_eq_iff_eq_inv, inv_div]
      ring
    rw [hi, eq_div_iff h1', add_mul, div_mul_cancel₀ _ h1']
    ring
  have e2 : 1 / (2 * (y - 1 / 2) + 1) = 1 / (2 * y) := by
    congr 1
    ring
  rw [e1, e2] at hs
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = 1 / (2 * y) := ⟨_, rfl⟩
  rw [← hz] at hs
  have hz0 : 0 < z := by
    rw [hz]
    exact div_pos one_pos (by linarith)
  have hz1 : z < 1 := by
    rw [hz, div_lt_one (by linarith)]
    linarith
  have hyz : 1 / y = 2 * z := by
    rw [hz]
    field_simp
  set L := Real.log ((2 * y + 1) / (2 * y - 1)) with hL
  have hS : ∑ i ∈ Finset.range 4, (2 : ℝ) * (1 / (2 * (i : ℝ) + 1)) * z ^ (2 * i + 1) =
      2 * z + 2 / 3 * z ^ 3 + 2 / 5 * z ^ 5 + 2 / 7 * z ^ 7 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    push_cast
    ring
  have hlow := sum_le_hasSum (Finset.range 4)
    (fun i _ => mul_nonneg (mul_nonneg (by norm_num) (by positivity)) (pow_nonneg hz0.le _)) hs
  rw [hS] at hlow
  have htail := (hasSum_nat_add_iff' 4).mpr hs
  have hpt : ∀ k : ℕ, (2 : ℝ) * (1 / (2 * ((k + 4 : ℕ) : ℝ) + 1)) * z ^ (2 * (k + 4) + 1) ≤
      2 / 9 * z ^ 9 * (z ^ 2) ^ k := by
    intro k
    have hc : (1 : ℝ) / (2 * ((k + 4 : ℕ) : ℝ) + 1) ≤ 1 / 9 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      push_cast
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have hp : 0 ≤ z ^ 9 * (z ^ 2) ^ k := mul_nonneg (pow_nonneg hz0.le _) (pow_nonneg (sq_nonneg _) _)
    have e : z ^ (2 * (k + 4) + 1) = z ^ 9 * (z ^ 2) ^ k := by ring
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left hc hp]
  have hg := (hasSum_geometric_of_lt_one (sq_nonneg z) (by nlinarith : z ^ 2 < 1)).mul_left (2 / 9 * z ^ 9)
  have hup := hasSum_le hpt htail hg
  rw [hS] at hup
  rw [hyz]
  have h4 : 0 < 4 * y ^ 2 - 1 := by nlinarith
  have h4' : 4 * y ^ 2 - 1 ≠ 0 := h4.ne'
  have hA : 1 - z ^ 2 ≠ 0 := by nlinarith
  have hB : 576 * y ^ 7 * (4 * y ^ 2 - 1) ≠ 0 := (mul_pos (mul_pos (by norm_num) (pow_pos hy0 7)) h4).ne'
  have hT : 2 / 9 * z ^ 9 * (1 - z ^ 2)⁻¹ = 1 / (576 * y ^ 7 * (4 * y ^ 2 - 1)) := by
    rw [← div_eq_mul_inv, div_eq_div_iff hA hB, hz]
    field_simp
    ring
  rw [hT] at hup
  have key1 : (12 * y ^ 3 - 9 * y / 5) * (2 / 3 * z ^ 3 + 2 / 5 * z ^ 5 + 2 / 7 * z ^ 7) - 1 =
      3 * (16 * y ^ 2 - 15) / (11200 * y ^ 6) := by
    rw [hz]
    field_simp
    ring
  have key2 : 1 - (12 * y ^ 3 - 9 * y / 5 - 1 / 10) *
      (2 / 3 * z ^ 3 + 2 / 5 * z ^ 5 + 2 / 7 * z ^ 7 + 1 / (576 * y ^ 7 * (4 * y ^ 2 - 1))) =
      (3360 * y ^ 6 - 1728 * y ^ 5 - 336 * y ^ 4 - 48 * y ^ 3 - 36 * y ^ 2 - 90 * y - 5) /
        (100800 * y ^ 7 * (4 * y ^ 2 - 1)) := by
    obtain ⟨w, hwd⟩ : ∃ w : ℝ, w = 4 * y ^ 2 - 1 := ⟨_, rfl⟩
    have hw0 : w ≠ 0 := by rw [hwd]; exact h4'
    rw [← hwd, hz]
    field_simp
    rw [hwd]
    ring
  have ht : 0 ≤ y - 1 := by linarith
  have p1 : 0 < 3 * (16 * y ^ 2 - 15) / (11200 * y ^ 6) :=
    div_pos (by nlinarith) (by have := pow_pos hy0 6; linarith)
  have p2 : 0 < (3360 * y ^ 6 - 1728 * y ^ 5 - 336 * y ^ 4 - 48 * y ^ 3 - 36 * y ^ 2 - 90 * y - 5) /
        (100800 * y ^ 7 * (4 * y ^ 2 - 1)) := by
    apply div_pos
    · nlinarith [pow_nonneg ht 2, pow_nonneg ht 3, pow_nonneg ht 4, pow_nonneg ht 5, pow_nonneg ht 6]
    · exact mul_pos (mul_pos (by norm_num) (pow_pos hy0 7)) h4
  have hDl : 2 / 3 * z ^ 3 + 2 / 5 * z ^ 5 + 2 / 7 * z ^ 7 ≤ L - 2 * z := by linarith
  have hDu : L - 2 * z ≤ 2 / 3 * z ^ 3 + 2 / 5 * z ^ 5 + 2 / 7 * z ^ 7 + 1 / (576 * y ^ 7 * (4 * y ^ 2 - 1)) := by
    linarith
  have hD0 : 0 < L - 2 * z := by
    have := pow_pos hz0 3
    have := pow_pos hz0 5
    have := pow_pos hz0 7
    linarith
  have hy3 : y ≤ y ^ 3 := by nlinarith
  have hX : 0 ≤ 12 * y ^ 3 - 9 * y / 5 - 1 / 10 := by linarith
  constructor
  · rw [lt_div_iff₀ hD0]
    calc (12 * y ^ 3 - 9 * y / 5 - 1 / 10) * (L - 2 * z)
        ≤ (12 * y ^ 3 - 9 * y / 5 - 1 / 10) *
          (2 / 3 * z ^ 3 + 2 / 5 * z ^ 5 + 2 / 7 * z ^ 7 + 1 / (576 * y ^ 7 * (4 * y ^ 2 - 1))) :=
          mul_le_mul_of_nonneg_left hDu hX
      _ < 1 := by linarith
  · rw [div_lt_iff₀ hD0]
    calc (1 : ℝ) < (12 * y ^ 3 - 9 * y / 5) * (2 / 3 * z ^ 3 + 2 / 5 * z ^ 5 + 2 / 7 * z ^ 7) := by
          linarith
      _ ≤ (12 * y ^ 3 - 9 * y / 5) * (L - 2 * z) := mul_le_mul_of_nonneg_left hDl (by linarith)

def q (n : ℕ) : ℤ := ((9 * n / 5 : ℕ) : ℤ)

lemma hq (n : ℕ) : ⌊(9 * n / 5 : ℚ)⌋ = q n := by
  have := Rat.floor_natCast_div_natCast (9 * n) 5
  unfold q
  exact_mod_cast this

lemma cf' (n : ℕ) (hn : 1 ≤ n) : a n = 12 * (n : ℤ) ^ 3 - q n - 1 := by
  have hb := bnd (n : ℝ) (by exact_mod_cast hn)
  unfold a q
  rw [Int.floor_eq_iff]
  have hm := Nat.div_add_mod (9 * n) 5
  have hr : 9 * n % 5 ≤ 4 := by omega
  have hmR : (5 : ℝ) * ((9 * n / 5 : ℕ) : ℝ) + ((9 * n % 5 : ℕ) : ℝ) = 9 * (n : ℝ) := by
    exact_mod_cast hm
  have hrR : ((9 * n % 5 : ℕ) : ℝ) ≤ 4 := by exact_mod_cast hr
  have hr0 : (0 : ℝ) ≤ ((9 * n % 5 : ℕ) : ℝ) := Nat.cast_nonneg _
  generalize 9 * n / 5 = M at hmR ⊢
  generalize 9 * n % 5 = R at hmR hrR hr0
  push_cast
  constructor <;> linarith [hb.1, hb.2]

lemma cf (n : ℕ) (hn : 1 ≤ n) : a n = 12 * n ^ 3 - ⌊(9 * n / 5 : ℚ)⌋ - 1 := by
  rw [cf' n hn, hq]

lemma rec (n : ℕ) (hn : 9 ≤ n) : a n = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) + a (n - 5)
    - 3 * a (n - 6) + 3 * a (n - 7) - a (n - 8) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 9 := ⟨n - 9, by omega⟩
  simp only [show k + 9 - 1 = k + 8 by omega, show k + 9 - 2 = k + 7 by omega,
    show k + 9 - 3 = k + 6 by omega, show k + 9 - 5 = k + 4 by omega, show k + 9 - 6 = k + 3 by omega,
    show k + 9 - 7 = k + 2 by omega, show k + 9 - 8 = k + 1 by omega]
  rw [cf' (k + 9) (by omega), cf' (k + 8) (by omega), cf' (k + 7) (by omega), cf' (k + 6) (by omega),
    cf' (k + 4) (by omega), cf' (k + 3) (by omega), cf' (k + 2) (by omega), cf' (k + 1) (by omega)]
  have h1 : q (k + 9) = q (k + 4) + 9 := by simp only [q]; omega
  have h2 : q (k + 8) = q (k + 3) + 9 := by simp only [q]; omega
  have h3 : q (k + 7) = q (k + 2) + 9 := by simp only [q]; omega
  have h4 : q (k + 6) = q (k + 1) + 9 := by simp only [q]; omega
  push_cast
  linear_combination -h1 + 3 * h2 - 3 * h3 + h4

lemma cm (f : ℕ → ℤ) (d n : ℕ) :
    coeff n (PowerSeries.mk f * X ^ d) = if d ≤ n then f (n - d) else 0 := by
  rw [coeff_mul_X_pow', coeff_mk]

lemma gf : PowerSeries.mk (fun k => a (k + 1)) * ((-1 + X) ^ 4 * (1 + X + X ^ 2 + X ^ 3 + X ^ 4) : ℤ⟦X⟧) =
    10 + 62 * X + 72 * X ^ 2 + 72 * X ^ 3 + 72 * X ^ 4 + 63 * X ^ 5 + 8 * X ^ 6 + X ^ 7 := by
  set F : ℕ → ℤ := fun k => 12 * ((k : ℤ) + 1) ^ 3 - q (k + 1) - 1 with hF
  have hG : PowerSeries.mk (fun k => a (k + 1)) = PowerSeries.mk F := by
    congr 1
    funext k
    rw [hF, cf' (k + 1) (by omega)]
    push_cast
    ring
  rw [hG]
  have key : PowerSeries.mk F * ((-1 + X) ^ 4 * (1 + X + X ^ 2 + X ^ 3 + X ^ 4) : ℤ⟦X⟧) =
      PowerSeries.mk F - PowerSeries.mk F * X ^ 1 - PowerSeries.mk F * X ^ 1 - PowerSeries.mk F * X ^ 1 + PowerSeries.mk F * X ^ 2 + PowerSeries.mk F * X ^ 2 + PowerSeries.mk F * X ^ 2 - PowerSeries.mk F * X ^ 3 - PowerSeries.mk F * X ^ 5 + PowerSeries.mk F * X ^ 6 + PowerSeries.mk F * X ^ 6 + PowerSeries.mk F * X ^ 6 - PowerSeries.mk F * X ^ 7 - PowerSeries.mk F * X ^ 7 - PowerSeries.mk F * X ^ 7 + PowerSeries.mk F * X ^ 8 := by ring
  rw [key, show (10 + 62 * X + 72 * X ^ 2 + 72 * X ^ 3 + 72 * X ^ 4 + 63 * X ^ 5 + 8 * X ^ 6 + X ^ 7 : ℤ⟦X⟧) =
      C (10 : ℤ) + C (62 : ℤ) * X ^ 1 + C (72 : ℤ) * X ^ 2 + C (72 : ℤ) * X ^ 3 + C (72 : ℤ) * X ^ 4 + C (63 : ℤ) * X ^ 5 + C (8 : ℤ) * X ^ 6 + X ^ 7 by simp only [map_ofNat, pow_one] <;> ring]
  ext n
  simp only [map_sub, map_add, map_neg, cm, coeff_mk, coeff_X_pow, coeff_C, coeff_C_mul_X_pow]
  by_cases hn : 8 ≤ n
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
    simp only [show 1 ≤ m + 8 by omega, show 2 ≤ m + 8 by omega, show 3 ≤ m + 8 by omega, show 5 ≤ m + 8 by omega, show 6 ≤ m + 8 by omega, show 7 ≤ m + 8 by omega, show 8 ≤ m + 8 by omega, if_true, show m + 8 ≠ 0 by omega, show m + 8 ≠ 1 by omega, show m + 8 ≠ 2 by omega, show m + 8 ≠ 3 by omega, show m + 8 ≠ 4 by omega, show m + 8 ≠ 5 by omega, show m + 8 ≠ 6 by omega, show m + 8 ≠ 7 by omega, if_false, show m + 8 - 1 = m + 7 by omega, show m + 8 - 2 = m + 6 by omega, show m + 8 - 3 = m + 5 by omega, show m + 8 - 5 = m + 3 by omega, show m + 8 - 6 = m + 2 by omega, show m + 8 - 7 = m + 1 by omega, show m + 8 - 8 = m + 0 by omega, Nat.sub_zero, hF]
    have h0 : q (m + 9) = q (m + 4) + 9 := by simp only [q]; omega
    have h1 : q (m + 8) = q (m + 3) + 9 := by simp only [q]; omega
    have h2 : q (m + 7) = q (m + 2) + 9 := by simp only [q]; omega
    have h3 : q (m + 6) = q (m + 1) + 9 := by simp only [q]; omega
    push_cast
    linear_combination -h0 + 3 * h1 - 3 * h2 + h3
  · interval_cases n <;> simp [hF, q] <;> norm_num

end A227512P

theorem OMA.solution : type_of% @OMA.S_oeis_a227512.main :=
  ⟨A227512P.cf, A227512P.rec, A227512P.gf⟩
