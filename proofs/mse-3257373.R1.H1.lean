import OMAReductions.R_mse_3257373_R1

/-!
# Proof of `mse-3257373.R1.H1`

Using `riemannZeta_neg_nat_eq_bernoulli`, `bernoulli_eq_zero_of_odd`, Euler's formula
`hasSum_zeta_nat` (giving `bernoulli (4 * j + 2) > 0`), and the explicit Bernoulli recurrence
up to `B_24 = -236364091 / 2730`, we prove:
1. `⌊ζ(-2k)⌋ = 0` for all `k ≥ 1`;
2. `⌊ζ(-(4j + 1))⌋ < 0` for all `j`;
3. `⌊ζ(-23)⌋ = ⌊236364091 / 65520⌋ = 3607`.
-/

open OMA.S_mse_3257373

private lemma zeta_neg_re (n : ℕ) :
    (riemannZeta (-(n : ℂ))).re = (-1 : ℝ) ^ n * (bernoulli (n + 1) : ℝ) / ((n : ℝ) + 1) := by
  rw [riemannZeta_neg_nat_eq_bernoulli n]
  have hcast :
      ((-1 : ℂ) ^ n * (bernoulli (n + 1) : ℂ) / ((n : ℂ) + 1)) =
        (((-1 : ℝ) ^ n * (bernoulli (n + 1) : ℝ) / ((n : ℝ) + 1) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hcast, Complex.ofReal_re]

private lemma bernoulli_four_mul_add_two_pos (j : ℕ) :
    (0 : ℝ) < (bernoulli (4 * j + 2) : ℝ) := by
  have hk : 2 * j + 1 ≠ 0 := by omega
  have hsum := hasSum_zeta_nat hk
  have hnonneg : ∀ n : ℕ, (0 : ℝ) ≤ 1 / (n : ℝ) ^ (2 * (2 * j + 1)) := fun n => by positivity
  have h1_le : (1 : ℝ) / ((1 : ℕ) : ℝ) ^ (2 * (2 * j + 1)) ≤
      (-1 : ℝ) ^ ((2 * j + 1) + 1) * (2 : ℝ) ^ (2 * (2 * j + 1) - 1) *
        Real.pi ^ (2 * (2 * j + 1)) * (bernoulli (2 * (2 * j + 1)) : ℝ) /
        ((2 * (2 * j + 1)).factorial : ℝ) :=
    le_hasSum hsum 1 (fun n _ => hnonneg n)
  have h1_eq : (1 : ℝ) / ((1 : ℕ) : ℝ) ^ (2 * (2 * j + 1)) = 1 := by simp
  rw [h1_eq] at h1_le
  have hsign : (-1 : ℝ) ^ ((2 * j + 1) + 1) = 1 := by
    rw [show (2 * j + 1) + 1 = 2 * (j + 1) by omega, pow_mul]
    norm_num
  rw [hsign, one_mul, show 2 * (2 * j + 1) = 4 * j + 2 by omega] at h1_le
  have hden_pos : (0 : ℝ) < ((4 * j + 2).factorial : ℝ) := by positivity
  have hcoef_pos : (0 : ℝ) < (2 : ℝ) ^ (4 * j + 2 - 1) * Real.pi ^ (4 * j + 2) := by
    have hpi : 0 < Real.pi := Real.pi_pos
    positivity
  have hnum_pos :
      (0 : ℝ) < (2 : ℝ) ^ (4 * j + 2 - 1) * Real.pi ^ (4 * j + 2) *
        (bernoulli (4 * j + 2) : ℝ) := by
    have := (le_div_iff₀ hden_pos).mp h1_le
    linarith
  exact pos_of_mul_pos_right hnum_pos hcoef_pos.le

private lemma bernoulli'_24 : bernoulli' 24 = -236364091 / 2730 := by
  have b0 : bernoulli' 0 = 1 := bernoulli'_zero
  have b1 : bernoulli' 1 = 1 / 2 := bernoulli'_one
  have b2 : bernoulli' 2 = 1 / 6 := bernoulli'_two
  have bodd : ∀ k : ℕ, 1 ≤ k → bernoulli' (2 * k + 1) = 0 :=
    fun k hk => bernoulli'_eq_zero_of_odd ⟨k, rfl⟩ (by omega)
  have b3 : bernoulli' 3 = 0 := bodd 1 (by omega)
  have b5 : bernoulli' 5 = 0 := bodd 2 (by omega)
  have b7 : bernoulli' 7 = 0 := bodd 3 (by omega)
  have b9 : bernoulli' 9 = 0 := bodd 4 (by omega)
  have b11 : bernoulli' 11 = 0 := bodd 5 (by omega)
  have b13 : bernoulli' 13 = 0 := bodd 6 (by omega)
  have b15 : bernoulli' 15 = 0 := bodd 7 (by omega)
  have b17 : bernoulli' 17 = 0 := bodd 8 (by omega)
  have b19 : bernoulli' 19 = 0 := bodd 9 (by omega)
  have b21 : bernoulli' 21 = 0 := bodd 10 (by omega)
  have b23 : bernoulli' 23 = 0 := bodd 11 (by omega)
  have b4 : bernoulli' 4 = -1 / 30 := by
    have h := sum_bernoulli' 5
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
      b0, b1, b2, b3] at h
    set x := bernoulli' 4
    norm_num [Nat.choose] at h
    linarith
  have b6 : bernoulli' 6 = 1 / 42 := by
    have h := sum_bernoulli' 7
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
      b0, b1, b2, b3, b4, b5] at h
    set x := bernoulli' 6
    norm_num [Nat.choose] at h
    linarith
  have b8 : bernoulli' 8 = -1 / 30 := by
    have h := sum_bernoulli' 9
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
      b0, b1, b2, b3, b4, b5, b6, b7] at h
    set x := bernoulli' 8
    norm_num [Nat.choose] at h
    linarith
  have b10 : bernoulli' 10 = 5 / 66 := by
    have h := sum_bernoulli' 11
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
      b0, b1, b2, b3, b4, b5, b6, b7, b8, b9] at h
    set x := bernoulli' 10
    norm_num [Nat.choose] at h
    linarith
  have b12 : bernoulli' 12 = -691 / 2730 := by
    have h := sum_bernoulli' 13
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
      b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11] at h
    set x := bernoulli' 12
    norm_num [Nat.choose] at h
    linarith
  have b14 : bernoulli' 14 = 7 / 6 := by
    have h := sum_bernoulli' 15
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
      b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13] at h
    set x := bernoulli' 14
    norm_num [Nat.choose] at h
    linarith
  have b16 : bernoulli' 16 = -3617 / 510 := by
    have h := sum_bernoulli' 17
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
      b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15] at h
    set x := bernoulli' 16
    norm_num [Nat.choose] at h
    linarith
  have b18 : bernoulli' 18 = 43867 / 798 := by
    have h := sum_bernoulli' 19
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
      b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17] at h
    set x := bernoulli' 18
    norm_num [Nat.choose] at h
    linarith
  have b20 : bernoulli' 20 = -174611 / 330 := by
    have h := sum_bernoulli' 21
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
      b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19] at h
    set x := bernoulli' 20
    norm_num [Nat.choose] at h
    linarith
  have b22 : bernoulli' 22 = 854513 / 138 := by
    have h := sum_bernoulli' 23
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
      b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19,
      b20, b21] at h
    set x := bernoulli' 22
    norm_num [Nat.choose] at h
    linarith
  have h := sum_bernoulli' 25
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
    b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19,
    b20, b21, b22, b23] at h
  set x := bernoulli' 24
  norm_num [Nat.choose] at h
  linarith

theorem OMA.solution : OMA.R_mse_3257373_R1.H1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    unfold floorZetaNeg
    rw [zeta_neg_re (2 * k), bernoulli_eq_zero_of_odd ⟨k, rfl⟩ (by omega)]
    simp
  · intro j
    unfold floorZetaNeg
    rw [zeta_neg_re (4 * j + 1)]
    have hsign : (-1 : ℝ) ^ (4 * j + 1) = -1 := by
      rw [pow_succ, show 4 * j = 2 * (2 * j) by omega, pow_mul]
      norm_num
    rw [hsign, show 4 * j + 1 + 1 = 4 * j + 2 by omega]
    have hb : (0 : ℝ) < (bernoulli (4 * j + 2) : ℝ) := bernoulli_four_mul_add_two_pos j
    have hden : (0 : ℝ) < ((4 * j + 1 : ℕ) : ℝ) + 1 := by positivity
    have hneg : (-1 : ℝ) * (bernoulli (4 * j + 2) : ℝ) / (((4 * j + 1 : ℕ) : ℝ) + 1) < 0 := by
      rw [neg_one_mul, neg_div]
      exact neg_lt_zero.mpr (div_pos hb hden)
    exact Int.floor_lt.mpr (by simpa using hneg)
  · unfold floorZetaNeg
    rw [zeta_neg_re 23]
    have hb24 : bernoulli 24 = -236364091 / 2730 := by
      rw [bernoulli, bernoulli'_24]
      norm_num
    rw [show 23 + 1 = 24 by norm_num, hb24]
    refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩ <;> norm_num
