import OMAReductions.R_oeis_a368207_R1

/-!
The divisor-count limit used by the Bacher-number reduction.
Credit: @rgoldman73-dev. Standard elementary prime-factorization argument:
(k+1)^4 <= 64*2^k, with no constant needed for primes at least 16.
It yields tau(n)^4 <= 64^16*n. The loose fixed constant is sufficient
for the squeeze argument; no asymptotic theorem is assumed.
-/

namespace OMA.BacherDivisorLimit

open Finset Filter Topology

lemma fourth_step {k : ℕ} (hk : 5 ≤ k) : (k + 2) ^ 4 ≤ 2 * (k + 1) ^ 4 := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
  have he : 2 * (5 + t + 1) ^ 4 = (5 + t + 2) ^ 4 +
      t ^ 4 + 20 * t ^ 3 + 138 * t ^ 2 + 356 * t + 191 := by ring
  omega

lemma fourth_le (k : ℕ) : (k + 1) ^ 4 ≤ 64 * 2 ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    by_cases hk : k < 5
    · interval_cases k <;> norm_num
    · calc
        (k + 1 + 1) ^ 4 ≤ 2 * (k + 1) ^ 4 := fourth_step (by omega)
        _ ≤ 2 * (64 * 2 ^ k) := Nat.mul_le_mul_left 2 ih
        _ = 64 * 2 ^ (k + 1) := by rw [pow_succ]; ring

lemma factor_bound {p : ℕ} (hp : 2 ≤ p) (k : ℕ) :
    (k + 1) ^ 4 ≤ (if p < 16 then 64 else 1) * p ^ k := by
  by_cases h16 : p < 16
  · rw [if_pos h16]
    exact (fourth_le k).trans (Nat.mul_le_mul_left 64 (Nat.pow_le_pow_left hp k))
  · rw [if_neg h16, one_mul]
    have hk : k + 1 ≤ 2 ^ k := Nat.succ_le_of_lt Nat.lt_two_pow_self
    calc
      (k + 1) ^ 4 ≤ (2 ^ k) ^ 4 := Nat.pow_le_pow_left hk 4
      _ = 16 ^ k := by rw [← pow_mul, Nat.mul_comm k 4, pow_mul]; norm_num
      _ ≤ p ^ k := Nat.pow_le_pow_left (by omega) k

lemma divisor_fourth_bound {n : ℕ} (hn : n ≠ 0) :
    n.divisors.card ^ 4 ≤ 64 ^ 16 * n := by
  have hc : (n.primeFactors.filter (fun p => p < 16)).card ≤ 16 := by
    calc
      _ ≤ (Finset.range 16).card := Finset.card_le_card (by simp [Finset.subset_iff])
      _ = 16 := Finset.card_range _
  have hprod : (∏ p ∈ n.primeFactors, if p < 16 then 64 else 1) ≤ 64 ^ 16 := by
    simp only [Finset.prod_ite, Finset.prod_const, one_pow, mul_one]
    exact Nat.pow_le_pow_right (by omega) hc
  calc
    n.divisors.card ^ 4 = ∏ p ∈ n.primeFactors, (n.factorization p + 1) ^ 4 := by
      rw [Nat.card_divisors hn, Finset.prod_pow]
    _ ≤ ∏ p ∈ n.primeFactors,
        (if p < 16 then 64 else 1) * p ^ n.factorization p :=
      Finset.prod_le_prod' (fun p hp => factor_bound (Nat.prime_of_mem_primeFactors hp).two_le _)
    _ = (∏ p ∈ n.primeFactors, if p < 16 then 64 else 1) * n := by
      rw [Finset.prod_mul_distrib, ← Nat.prod_primeFactors_pow_factorization hn]
    _ ≤ 64 ^ 16 * n := Nat.mul_le_mul_right n hprod

lemma ratio_sq_bound {n : ℕ} (hn : 0 < n) :
    ((n.divisors.card : ℝ) / Real.sqrt n) ^ 2 ≤ (64 : ℝ) ^ 16 / Real.sqrt n := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnR
  have h4 : (n.divisors.card : ℝ) ^ 4 ≤ (64 : ℝ) ^ 16 * n := by
    exact_mod_cast divisor_fourth_bound (by omega : n ≠ 0)
  have hs2 := Real.sq_sqrt hnR.le
  have hC : 1 ≤ (64 : ℝ) ^ 16 := by norm_num
  have hc0 : 0 ≤ (n.divisors.card : ℝ) := by positivity
  have ht : (n.divisors.card : ℝ) ^ 2 ≤ (64 : ℝ) ^ 16 * Real.sqrt n := by
    nlinarith [sq_nonneg ((64 : ℝ) ^ 16 * Real.sqrt n - (n.divisors.card : ℝ) ^ 2)]
  rw [div_pow, hs2]
  apply (div_le_div_iff₀ hnR hs).mpr
  calc
    (n.divisors.card : ℝ) ^ 2 * Real.sqrt n ≤
        ((64 : ℝ) ^ 16 * Real.sqrt n) * Real.sqrt n :=
      mul_le_mul_of_nonneg_right ht hs.le
    _ = (64 : ℝ) ^ 16 * n := by rw [mul_assoc, ← pow_two, hs2]

theorem divisor_limit :
    Tendsto (fun n : ℕ => (n.divisors.card : ℝ) / Real.sqrt n) atTop (𝓝 0) := by
  have hs : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => (64 : ℝ) ^ 16 / Real.sqrt n) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.comp hs).const_mul ((64 : ℝ) ^ 16)
  have hsq : Tendsto (fun n : ℕ => ((n.divisors.card : ℝ) / Real.sqrt n) ^ 2)
      atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n => sq_nonneg _))
      (g := fun n : ℕ => (64 : ℝ) ^ 16 / Real.sqrt n) _ hinv
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact ratio_sq_bound (by omega)
  have hr := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  have he : ∀ n : ℕ, Real.sqrt (((n.divisors.card : ℝ) / Real.sqrt n) ^ 2) =
      (n.divisors.card : ℝ) / Real.sqrt n := fun n => Real.sqrt_sq (by positivity)
  simpa only [Function.comp_def, he, Real.sqrt_zero] using hr

end OMA.BacherDivisorLimit

theorem OMA.solution : OMA.R_oeis_a368207_R1.H2 :=
  OMA.BacherDivisorLimit.divisor_limit
