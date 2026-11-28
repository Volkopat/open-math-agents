import OMAReductions.R_Erdos877_erdos_877_variants_balogh_liu_sharifzadeh_treglown_R1_H2_R1

/-!
Proof of `OMA.R_Erdos877_erdos_877_variants_balogh_liu_sharifzadeh_treglown_R1_H2_R1.H1`.

Let `n = |s|` and `m = n / 64`, so every `A ∈ F` has `|A| ≤ m`. With `x = 1 / 16`,
`|F| ≤ ∑_{A ∈ F} x ^ |A| / x ^ m ≤ 16 ^ m ∑_{A ⊆ s} x ^ |A| = 16 ^ m (17 / 16) ^ n`.
Now `16 ^ m = 2 ^ (4 m) ≤ 2 ^ (n / 16)` and `(17 / 16) ^ 8 ≤ 2` gives `(17 / 16) ^ n ≤ 2 ^ (n / 8)`,
so `|F| ≤ 2 ^ (3 n / 16) ≤ 2 ^ (n / 4)`.
-/

open Finset

theorem OMA.solution :
    OMA.R_Erdos877_erdos_877_variants_balogh_liu_sharifzadeh_treglown_R1_H2_R1.H1 := by
  intro s F hF hsmall
  set n := s.card with hn
  set m := n / 64 with hm
  have hAm : ∀ A ∈ F, A.card ≤ m := fun A hA => by
    have := hsmall A hA
    omega
  -- Step 1: `|F| ≤ 16 ^ m * (17 / 16) ^ n`.
  have hx : ∀ A ∈ F, (1 : ℝ) ≤ (16 : ℝ) ^ m * (1 / 16 : ℝ) ^ A.card := by
    intro A hA
    have hk := hAm A hA
    have h16 : (16 : ℝ) ^ m = (16 : ℝ) ^ (m - A.card) * (16 : ℝ) ^ A.card := by
      rw [← pow_add, Nat.sub_add_cancel hk]
    rw [h16, mul_assoc, ← mul_pow, show (16 : ℝ) * (1 / 16) = 1 by norm_num, one_pow, mul_one]
    exact one_le_pow₀ (by norm_num)
  have hcount : (F.card : ℝ) ≤ (16 : ℝ) ^ m * ((17 : ℝ) / 16) ^ n := by
    calc (F.card : ℝ) = ∑ A ∈ F, (1 : ℝ) := by simp
      _ ≤ ∑ A ∈ F, (16 : ℝ) ^ m * (1 / 16 : ℝ) ^ A.card := Finset.sum_le_sum hx
      _ ≤ ∑ A ∈ s.powerset, (16 : ℝ) ^ m * (1 / 16 : ℝ) ^ A.card :=
          Finset.sum_le_sum_of_subset_of_nonneg hF (fun _ _ _ => by positivity)
      _ = (16 : ℝ) ^ m * ∑ A ∈ s.powerset, (1 / 16 : ℝ) ^ A.card * 1 ^ (s.card - A.card) := by
          rw [Finset.mul_sum]
          simp
      _ = (16 : ℝ) ^ m * ((17 : ℝ) / 16) ^ n := by
          rw [Finset.sum_pow_mul_eq_add_pow]
          norm_num
          exact hn.symm
  -- Step 2: the two exponential bounds.
  have h1 : (16 : ℝ) ^ m ≤ (2 : ℝ) ^ ((n : ℝ) / 16) := by
    have h4 : (16 : ℝ) ^ m = (2 : ℝ) ^ ((4 * m : ℕ) : ℝ) := by
      rw [Real.rpow_natCast, pow_mul]
      norm_num
    rw [h4]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have : 4 * m * 16 ≤ n := by omega
    have : ((4 * m : ℕ) : ℝ) * 16 ≤ (n : ℝ) := by exact_mod_cast this
    linarith
  have h2 : ((17 : ℝ) / 16) ^ n ≤ (2 : ℝ) ^ ((n : ℝ) / 8) := by
    have hbase : (17 : ℝ) / 16 ≤ (2 : ℝ) ^ ((1 : ℝ) / 8) := by
      have h8 : ((17 : ℝ) / 16) ^ (8 : ℕ) ≤ 2 := by norm_num
      have hroot := Real.rpow_le_rpow (by positivity) h8 (by norm_num : (0 : ℝ) ≤ 1 / 8)
      rwa [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
        show ((8 : ℕ) : ℝ) * (1 / 8) = 1 by norm_num, Real.rpow_one] at hroot
    calc ((17 : ℝ) / 16) ^ n ≤ ((2 : ℝ) ^ ((1 : ℝ) / 8)) ^ n :=
          pow_le_pow_left₀ (by positivity) hbase n
      _ = (2 : ℝ) ^ ((n : ℝ) / 8) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
          congr 1
          ring
  have h3 : (2 : ℝ) ^ ((n : ℝ) / 16) * (2 : ℝ) ^ ((n : ℝ) / 8) ≤ (2 : ℝ) ^ ((n : ℝ) / 4) := by
    rw [← Real.rpow_add (by norm_num)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  calc (F.card : ℝ) ≤ (16 : ℝ) ^ m * ((17 : ℝ) / 16) ^ n := hcount
    _ ≤ (2 : ℝ) ^ ((n : ℝ) / 16) * (2 : ℝ) ^ ((n : ℝ) / 8) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ ≤ (2 : ℝ) ^ ((n : ℝ) / 4) := h3
