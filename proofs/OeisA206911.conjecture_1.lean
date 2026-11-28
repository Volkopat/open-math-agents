import FormalConjectures.OEIS.«206911»

/-! Shorter proof of `OeisA206911.conjecture_1`. -/

open OeisA206911

theorem OMA.solution : type_of% @OeisA206911.conjecture_1 := by
  intro n hn
  by_cases hsmall : n < 5
  · interval_cases n <;> norm_num [diff, a_1, a_2, a_3, a_4, a_5]
  let E (k : ℕ) : ℝ := Real.exp (harmonic k : ℝ)
  have step (k : ℕ) : E (k + 1) = E k * Real.exp ((k + 1 : ℝ)⁻¹) := by
    simp [E, harmonic_succ, Real.exp_add]
  have exp_u (k : ℕ) (hk : 0 < k) : Real.exp ((k + 1 : ℝ)⁻¹) ≤ 1 + (k : ℝ)⁻¹ := by
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    calc _ ≤ 1 / (1 - (k + 1 : ℝ)⁻¹) :=
            Real.exp_bound_div_one_sub_of_interval (by positivity) (inv_lt_one_of_one_lt₀ (by linarith))
      _ = 1 + (k : ℝ)⁻¹ := by field_simp; simp [hk'.ne']
  have hEu (k : ℕ) (hk : 5 ≤ k) : E k ≤ 2 * k := by
    induction k, hk using Nat.le_induction with
    | base =>
      have hsum : (harmonic 5 : ℝ) = 137 / 60 := by norm_num [harmonic, Finset.sum_range_succ]
      have hlt : Real.exp (137 / 60) ^ 60 < (10 : ℝ) ^ 60 := by
        rw [← Real.exp_nat_mul, show (60 : ℕ) * (137 / 60 : ℝ) = (137 : ℕ) * 1 by norm_num,
          Real.exp_nat_mul]
        exact (pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_nonneg _) (by norm_num)).trans (by norm_num)
      dsimp only [E]; rw [hsum]; norm_num; exact (lt_of_pow_lt_pow_left₀ 60 (by norm_num) hlt).le
    | succ k hk ih =>
      have hk' : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      calc E (k + 1) = E k * Real.exp ((k + 1 : ℝ)⁻¹) := step k
        _ ≤ 2 * k * (1 + (k : ℝ)⁻¹) :=
            mul_le_mul ih (exp_u k (by omega)) (Real.exp_nonneg _) (by positivity)
        _ = 2 * ↑(k + 1) := by push_cast; field_simp
  have hEl (k : ℕ) : (k : ℝ) + 1 ≤ E k := by
    rw [← Real.exp_log (by positivity : (0 : ℝ) < k + 1)]
    exact Real.exp_le_exp.mpr (by simpa using log_add_one_le_harmonic k)
  have hlo : E n + 1 ≤ E (n + 1) := by
    rw [step]
    have := mul_le_mul (hEl n) (show ((n : ℝ) + 1)⁻¹ ≤ Real.exp ((n + 1 : ℝ)⁻¹) - 1 by
      linarith [Real.add_one_le_exp ((n + 1 : ℝ)⁻¹)]) (by positivity) (Real.exp_nonneg _)
    rw [mul_inv_cancel₀ (by positivity)] at this; linarith
  have hhi : E (n + 1) ≤ E n + 2 := by
    rw [step]
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have : E n * (n : ℝ)⁻¹ ≤ 2 := by
      rw [← div_eq_mul_inv]; exact (div_le_iff₀ hn').mpr (hEu n (by omega))
    nlinarith [mul_le_mul_of_nonneg_left (exp_u n hn) (Real.exp_nonneg (harmonic n : ℝ))]
  have hfl : ⌊E n - 1⌋ + 1 ≤ ⌊E (n + 1) - 1⌋ :=
    Int.le_floor.mpr (by push_cast; linarith [Int.floor_le (E n - 1)])
  have hfu : ⌊E (n + 1) - 1⌋ ≤ ⌊E n - 1⌋ + 2 :=
    Int.floor_le_iff.mpr (by push_cast; linarith [Int.lt_floor_add_one (E n - 1)])
  have fnn (k : ℕ) : 0 ≤ ⌊E k - 1⌋ :=
    Int.floor_nonneg.mpr (by linarith [hEl k, Nat.cast_nonneg (α := ℝ) k])
  dsimp only [E] at hfl hfu fnn
  unfold diff a; push_cast
  rw [Int.toNat_of_nonneg (fnn (n + 1)), Int.toNat_of_nonneg (fnn n)]
  omega
