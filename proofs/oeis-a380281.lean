import OMAStatements.S_oeis_a380281

namespace OMA.S_oeis_a380281_Proof

open OMA.S_oeis_a380281 Finset

private lemma halfRising_succ (j : ℕ) :
    halfRising (j + 1) = halfRising j * ((j : ℝ) + 1 / 2) :=
  Finset.prod_range_succ _ j

private lemma oddProduct_succ (j : ℕ) :
    oddProduct (j + 1) = oddProduct j * (2 * j + 1) :=
  Finset.prod_range_succ _ j

private lemma halfRising_eq (j : ℕ) :
    halfRising j = (oddProduct j : ℝ) / (2 : ℝ) ^ j := by
  induction j with
  | zero =>
    simp [halfRising, oddProduct]
  | succ j ih =>
    rw [halfRising_succ, ih, oddProduct_succ, pow_succ]
    push_cast
    have h2 : (2 : ℝ) ^ j ≠ 0 := by positivity
    field_simp [h2]

private lemma factorial_two_mul (m : ℕ) :
    (2 * m).factorial = 2 ^ m * m.factorial * oddProduct m := by
  induction m with
  | zero =>
    simp [oddProduct]
  | succ m ih =>
    have h1 : 2 * (m + 1) = (2 * m + 1) + 1 := by ring
    rw [h1, Nat.factorial_succ, Nat.factorial_succ, ih, oddProduct_succ,
      Nat.factorial_succ, pow_succ]
    ring

private lemma choose_odd_identity {n k : ℕ} (hk : k ≤ n) :
    Nat.choose (2 * n + 1) (2 * k + 1) * oddProduct (n - k) * oddProduct k * (2 * k + 1) =
      oddProduct (n + 1) * Nat.choose n k := by
  have hpos : 0 < k.factorial * (n - k).factorial * 2 ^ n := by positivity
  apply Nat.eq_of_mul_eq_mul_right hpos
  have h1 : 2 * k + 1 ≤ 2 * n + 1 := by omega
  have hsub : 2 * n + 1 - (2 * k + 1) = 2 * (n - k) := by omega
  have hpow : 2 ^ k * 2 ^ (n - k) = 2 ^ n := by
    rw [← pow_add, Nat.add_sub_of_le hk]
  have hC1 : Nat.choose (2 * n + 1) (2 * k + 1) * (2 * k + 1).factorial * (2 * (n - k)).factorial =
      (2 * n + 1).factorial := by
    rw [← hsub]
    exact Nat.choose_mul_factorial_mul_factorial h1
  have hC2 : Nat.choose n k * k.factorial * (n - k).factorial = n.factorial :=
    Nat.choose_mul_factorial_mul_factorial hk
  have hf_n : (2 * n + 1).factorial = oddProduct (n + 1) * n.factorial * 2 ^ n := by
    rw [Nat.factorial_succ, factorial_two_mul, oddProduct_succ]
    ring
  have hf_k : (2 * k + 1).factorial = (2 * k + 1) * 2 ^ k * k.factorial * oddProduct k := by
    rw [Nat.factorial_succ, factorial_two_mul]
    ring
  have hf_nk : (2 * (n - k)).factorial = 2 ^ (n - k) * (n - k).factorial * oddProduct (n - k) :=
    factorial_two_mul (n - k)
  calc
    Nat.choose (2 * n + 1) (2 * k + 1) * oddProduct (n - k) * oddProduct k * (2 * k + 1) *
        (k.factorial * (n - k).factorial * 2 ^ n)
      = Nat.choose (2 * n + 1) (2 * k + 1) * oddProduct (n - k) * oddProduct k * (2 * k + 1) *
          (k.factorial * (n - k).factorial * (2 ^ k * 2 ^ (n - k))) := by rw [hpow]
    _ = Nat.choose (2 * n + 1) (2 * k + 1) * ((2 * k + 1) * 2 ^ k * k.factorial * oddProduct k) *
          (2 ^ (n - k) * (n - k).factorial * oddProduct (n - k)) := by ring
    _ = Nat.choose (2 * n + 1) (2 * k + 1) * (2 * k + 1).factorial * (2 * (n - k)).factorial := by
          rw [hf_k, hf_nk]
    _ = (2 * n + 1).factorial := hC1
    _ = oddProduct (n + 1) * n.factorial * 2 ^ n := hf_n
    _ = oddProduct (n + 1) * (Nat.choose n k * k.factorial * (n - k).factorial) * 2 ^ n := by
          rw [hC2]
    _ = oddProduct (n + 1) * Nat.choose n k * (k.factorial * (n - k).factorial * 2 ^ n) := by
          ring

private lemma entry_eq {n k : ℕ} (hk : k ≤ n) :
    entry n k = (oddProduct (n + 1) : ℝ) * ((Nat.choose n k : ℝ) / ((2 * k + 1 : ℕ) : ℝ)) := by
  have hne : ((2 * k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hstep : entry n k * ((2 * k + 1 : ℕ) : ℝ) =
      (oddProduct (n + 1) : ℝ) * (Nat.choose n k : ℝ) := by
    unfold entry
    rw [halfRising_eq, halfRising_eq]
    have hpow : (2 : ℝ) ^ n = (2 : ℝ) ^ (n - k) * (2 : ℝ) ^ k := by
      rw [← pow_add, Nat.sub_add_cancel hk]
    have h2nk : (2 : ℝ) ^ (n - k) ≠ 0 := by positivity
    have h2k : (2 : ℝ) ^ k ≠ 0 := by positivity
    rw [hpow]
    have hcancel : (2 : ℝ) ^ (n - k) * (2 : ℝ) ^ k * (Nat.choose (2 * n + 1) (2 * k + 1) : ℝ) *
        ((oddProduct (n - k) : ℝ) / (2 : ℝ) ^ (n - k)) * ((oddProduct k : ℝ) / (2 : ℝ) ^ k) *
        ((2 * k + 1 : ℕ) : ℝ) =
        (Nat.choose (2 * n + 1) (2 * k + 1) : ℝ) * (oddProduct (n - k) : ℝ) *
        (oddProduct k : ℝ) * ((2 * k + 1 : ℕ) : ℝ) := by
      field_simp [h2nk, h2k]
    rw [hcancel]
    exact_mod_cast choose_odd_identity hk
  rw [mul_div_assoc', eq_div_iff hne]
  exact hstep

private lemma integral_one_add_sq_pow (n : ℕ) :
    ∫ x : ℝ in (0 : ℝ)..1, (1 + x ^ 2) ^ n =
      ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℝ) / ((2 * k + 1 : ℕ) : ℝ) := by
  have hbin : ∀ x : ℝ, (1 + x ^ 2) ^ n =
      ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℝ) * x ^ (2 * k) := by
    intro x
    rw [add_comm, add_pow]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [one_pow, mul_one, ← pow_mul, mul_comm]
  simp_rw [hbin]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [intervalIntegral.integral_const_mul, integral_pow]
    rw [one_pow, zero_pow (Nat.succ_ne_zero _), sub_zero]
    push_cast
    ring
  · intro k _
    exact (continuous_const.mul (continuous_pow (2 * k))).intervalIntegrable 0 1

lemma main_proof : ∀ n : ℕ, ∑ k ∈ Finset.range (n + 1), entry n k =
    (oddProduct (n + 1) : ℝ) * ∫ x : ℝ in (0 : ℝ)..1, (1 + x ^ 2) ^ n := by
  intro n
  rw [integral_one_add_sq_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  exact entry_eq (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))

end OMA.S_oeis_a380281_Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a380281.main :=
  OMA.S_oeis_a380281_Proof.main_proof
