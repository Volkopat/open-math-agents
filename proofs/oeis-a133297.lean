import OMAStatements.S_oeis_a133297

open Finset OMA.S_oeis_a133297

private theorem cancel_sign (j : ℕ) : (-1 : ℝ) ^ j * (-1) ^ j = 1 := by
  rw [← mul_pow]
  norm_num

private theorem finite_part (n : ℕ) (hn : 1 ≤ n) :
    a n = -((n - 1).factorial : ℝ) * (-1) ^ n *
      ∑ j ∈ range n, (-(n : ℝ)) ^ j / j.factorial := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hf : n.factorial = n * (n - 1).factorial := by
    cases n <;> simp_all [Nat.factorial_succ]
  rw [a, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_nbij' (n - ·) (n - ·) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    simp only [mem_Icc] at hk
    simp only [mem_range]
    omega
  · intro j hj
    simp only [mem_range] at hj
    simp only [mem_Icc]
    omega
  · intro k hk
    simp only [mem_Icc] at hk
    omega
  · intro j hj
    simp only [mem_range] at hj
    omega
  · intro k hk
    obtain ⟨_, hk⟩ := mem_Icc.mp hk
    have sign : (-1 : ℝ) ^ n = (-1) ^ k * (-1) ^ (n-k) := by
      rw [← pow_add, Nat.add_sub_of_le hk]
    rw [show (n : ℤ) - (k : ℤ) - 1 = ((n - k : ℕ) : ℤ) - 1 by omega,
      zpow_sub₀ hn0, zpow_natCast, zpow_one, hf, Nat.cast_mul, sign, pow_succ,
      neg_eq_neg_one_mul (n : ℝ), mul_pow]
    field_simp
    nlinarith only [cancel_sign (n-k)]

theorem OMA.solution : type_of% @OMA.S_oeis_a133297.main := by
  intro n hn
  let t (j : ℕ) : ℝ := (-(n : ℝ)) ^ j / j.factorial
  have hs : HasSum t (Real.exp (-(n : ℝ))) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp _
  have split := hs.summable.sum_add_tsum_nat_add n
  rw [hs.tsum_eq] at split
  have tail : (∑' k : ℕ, (-1 : ℝ) ^ k * n ^ (n+k) / ((n+k).factorial : ℝ)) =
      (-1 : ℝ) ^ n * ∑' k : ℕ, t (k+n) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro k
    dsimp [t]
    rw [Nat.add_comm k n, neg_eq_neg_one_mul (n : ℝ), mul_pow, pow_add (-1 : ℝ)]
    linear_combination -((-1 : ℝ) ^ k * (n : ℝ) ^ (n+k) / (n+k).factorial) * cancel_sign n
  have en : (-1 / Real.exp 1) ^ n = (-1 : ℝ) ^ n * Real.exp (-(n : ℝ)) := by
    rw [div_pow, Real.exp_neg, ← mul_one (n : ℝ), Real.exp_nat_mul]
    simp [div_eq_mul_inv]
  rw [finite_part n hn, tail, en, ← split]
  dsimp only [t]
  ring
