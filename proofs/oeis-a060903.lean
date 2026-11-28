import OMAStatements.S_oeis_a060903

namespace OMA.OeisA060903

open Real

lemma small : ∀ n < 100, 12 < n →
    ((∑ d ∈ n.divisors, d) + 1) ^ 2 * 9742 ≤ 3600 * n ^ 3 := by
  decide

lemma sigma_le (n : ℕ) : ((∑ d ∈ n.divisors, d : ℕ) : ℝ) ≤ n * (1 + Real.log n) := by
  have h1 : ((∑ d ∈ n.divisors, d : ℕ) : ℝ) = ∑ d ∈ n.divisors, (((n / d : ℕ)) : ℝ) := by
    push_cast
    exact (Nat.sum_div_divisors n (fun d => (d : ℝ))).symm
  have h2 : ∑ d ∈ n.divisors, (((n / d : ℕ)) : ℝ) ≤ ∑ d ∈ n.divisors, (n : ℝ) * (d : ℝ)⁻¹ :=
    Finset.sum_le_sum fun d _ => by
      rw [← div_eq_mul_inv]
      exact Nat.cast_div_le
  have h3 : ∑ d ∈ n.divisors, (n : ℝ) * (d : ℝ)⁻¹ ≤ ∑ d ∈ Finset.Icc 1 n, (n : ℝ) * (d : ℝ)⁻¹ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro d hd
      rw [Nat.mem_divisors] at hd
      rw [Finset.mem_Icc]
      exact ⟨Nat.pos_of_dvd_of_pos hd.1 (Nat.pos_of_ne_zero hd.2), Nat.le_of_dvd
        (Nat.pos_of_ne_zero hd.2) hd.1⟩
    · intro d _ _
      positivity
  have h4 : ∑ d ∈ Finset.Icc 1 n, (n : ℝ) * (d : ℝ)⁻¹ = n * (harmonic n : ℝ) := by
    rw [← Finset.mul_sum, harmonic_eq_sum_Icc]
    push_cast
    rfl
  have h5 := harmonic_le_one_add_log n
  have h6 : (0 : ℝ) ≤ n := by positivity
  nlinarith

lemma large (n : ℕ) (hn : 100 ≤ n) :
    ((∑ d ∈ n.divisors, d : ℕ) : ℝ) + 1 ≤ 6 * n * √n / π ^ 2 := by
  have hS := sigma_le n
  have hnR : (100 : ℝ) ≤ n := by exact_mod_cast hn
  set s := √(n : ℝ) with hs
  have hs2 : s ^ 2 = n := Real.sq_sqrt (by positivity)
  have hs10 : 10 ≤ s := by
    rw [hs, show (10 : ℝ) = √100 by
      rw [show (100 : ℝ) = 10 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hnR
  have hspos : 0 < s := by linarith
  have hlog : Real.log n = 2 * Real.log s := by
    rw [← hs2, Real.log_pow]
    push_cast
    ring
  have he1 := Real.exp_one_gt_d9
  have hE : (7.389 : ℝ) < Real.exp 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith
  have hexp : Real.log s - 2 + 1 ≤ s / Real.exp 2 := by
    have := Real.add_one_le_exp (Real.log s - 2)
    rwa [Real.exp_sub, Real.exp_log hspos] at this
  have hdiv : s / Real.exp 2 ≤ s / 7.389 :=
    div_le_div_of_nonneg_left hspos.le (by norm_num) hE.le
  have hL : Real.log n ≤ 2 * s / 7.389 + 2 := by
    rw [hlog]
    have : 2 * s / 7.389 = 2 * (s / 7.389) := by ring
    linarith
  have hpi := Real.pi_lt_d4
  have hpi0 := Real.pi_pos
  have hP : π ^ 2 < 9.87 := by nlinarith
  rw [le_div_iff₀ (by positivity)]
  have hS' : ((∑ d ∈ n.divisors, d : ℕ) : ℝ) ≤ s ^ 2 * (3 + 2 * s / 7.389) := by
    rw [hs2]
    have : (0 : ℝ) ≤ n := by positivity
    nlinarith
  have hS0 : (0 : ℝ) ≤ ((∑ d ∈ n.divisors, d : ℕ) : ℝ) := by positivity
  have key : (s ^ 2 * (3 + 2 * s / 7.389) + 1) * 9.87 ≤ 6 * s ^ 3 := by
    have k1 : 0 ≤ s ^ 3 - 10 * s ^ 2 := by
      have := mul_nonneg (sq_nonneg s) (sub_nonneg.mpr hs10)
      nlinarith
    have k2 : 100 ≤ s ^ 2 := by nlinarith
    have k3 : (s ^ 2 * (3 + 2 * s / 7.389) + 1) * 9.87
        = 29.61 * s ^ 2 + (2 * 9.87 / 7.389) * s ^ 3 + 9.87 := by ring
    rw [k3]
    have k4 : (2 * 9.87 / 7.389 : ℝ) ≤ 2.672 := by norm_num
    have k5 : 0 ≤ s ^ 3 := by positivity
    nlinarith
  rw [← hs2]
  nlinarith [sq_nonneg s]

end OMA.OeisA060903

open Real in
theorem OMA.solution : type_of% @OMA.S_oeis_a060903.main := by
  intro n hn
  apply Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
  apply Nat.le_floor
  rw [Nat.cast_succ]
  by_cases h : 100 ≤ n
  · exact OMA.OeisA060903.large n h
  · have hsm := OMA.OeisA060903.small n (by omega) hn
    set S := ∑ d ∈ n.divisors, d with hSdef
    have hpi := Real.pi_lt_d4
    have hpi0 := Real.pi_pos
    have hP4 : π ^ 4 < 97.42 := by
      have : π ^ 2 < 9.8697 := by nlinarith
      nlinarith
    have hsm' : ((S : ℝ) + 1) ^ 2 * 97.42 ≤ 36 * (n : ℝ) ^ 3 := by
      have : (((S + 1) ^ 2 * 9742 : ℕ) : ℝ) ≤ ((3600 * n ^ 3 : ℕ) : ℝ) := by exact_mod_cast hsm
      push_cast at this
      linarith
    have hn0 : (0 : ℝ) ≤ n := by positivity
    have hsq := Real.sq_sqrt hn0
    have hsq0 := Real.sqrt_nonneg (n : ℝ)
    rw [le_div_iff₀ (by positivity)]
    rw [← pow_le_pow_iff_left₀ (by positivity) (by positivity) (two_ne_zero)]
    have hS0 : (0 : ℝ) ≤ ((S : ℝ) + 1) ^ 2 := by positivity
    calc (((S : ℝ) + 1) * π ^ 2) ^ 2 = ((S : ℝ) + 1) ^ 2 * π ^ 4 := by ring
      _ ≤ ((S : ℝ) + 1) ^ 2 * 97.42 := by gcongr
      _ ≤ 36 * (n : ℝ) ^ 3 := hsm'
      _ = (6 * n * √n) ^ 2 := by
        rw [mul_pow, hsq]
        ring
