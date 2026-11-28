import OMAStatements.S_oeis_a059304

open Polynomial in
-- The double sum is the coefficient of X^n in ((1 + X) + 1)^(2n) = (X + 2)^(2n).
theorem oeis_a059304_sum (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
        Nat.choose n j * Nat.choose n k * Nat.choose (j + k) n) = 2 ^ n * Nat.choose (2 * n) n := by
  have e : (1 + X + 1 : ℕ[X]) = X + C 2 := by
    have h2 : (C 2 : ℕ[X]) = 1 + 1 := by
      rw [← C_1, ← C_add]
      rfl
    rw [h2]
    ring
  have hS : (∑ j ∈ Finset.range (n + 1), (n.choose j : ℕ[X]) * (1 + X : ℕ[X]) ^ j) =
      (X + C 2) ^ n := by
    rw [← e, add_pow]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [one_pow, mul_one, mul_comm]
  have key : (∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
      ((n.choose j * n.choose k : ℕ) : ℕ[X]) * (1 + X : ℕ[X]) ^ (j + k)) =
      (X + C 2) ^ (2 * n) := by
    rw [two_mul, pow_add, ← hS, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    push_cast
    ring
  have hc := congrArg (fun p : ℕ[X] => p.coeff n) key
  simp only [finsetSum_coeff, coeff_natCast_mul, coeff_one_add_X_pow, coeff_X_add_C_pow,
    Nat.cast_id] at hc
  have e2 : 2 * n - n = n := by omega
  rw [e2] at hc
  exact hc

theorem OMA.solution : type_of% @OMA.S_oeis_a059304.main := by
  intro n
  rw [oeis_a059304_sum n]
  unfold OMA.S_oeis_a059304.a
  have hf : (2 * n).factorial = (2 * n).choose n * n.factorial ^ 2 := by
    have h := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
    have e2 : 2 * n - n = n := by omega
    rw [e2] at h
    rw [← h]
    ring
  rw [hf, ← mul_assoc]
  exact Nat.mul_div_cancel _ (pow_pos (Nat.factorial_pos n) 2)
