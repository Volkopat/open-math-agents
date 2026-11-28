import OMAStatements.S_oeis_a039692
import Mathlib

-- Problem oeis-a039692: with entry(n, m) = n! * Sum_{k=0..n} c(k, m) * C(k, n-k) / k!, where c are the unsigned
-- Stirling numbers of the first kind, the row sums are Sum_{m=0..n} entry(n, m) = n! * Fibonacci(n+1).
-- Upstream: statements/oeis-a039692.lean (declaration OMA.S_oeis_a039692.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Proof: swap the two sums. For k <= n, Sum_{m=0..n} c(k, m) = k!, because the c(k, m) are the coefficients of the
-- rising factorial x(x+1)...(x+k-1), whose value at x = 1 is k!, and c(k, m) = 0 for m > k. So the k! cancels and
-- the row sum is n! * Sum_{k=0..n} C(k, n-k) = n! * F(n+1) (the Fibonacci numbers as diagonal sums of Pascal's
-- triangle).

open Finset Polynomial OMA.S_oeis_a039692

private lemma stirlingFirst_zero_right_mul_a039692 (j : ℕ) : Nat.stirlingFirst j 0 * j = 0 := by
  cases j with
  | zero => rfl
  | succ j =>
    have h : Nat.stirlingFirst (j + 1) 0 = 0 := rfl
    rw [h, zero_mul]

private lemma coeff_ascPochhammer_a039692 :
    ∀ j k : ℕ, (ascPochhammer ℕ j).coeff k = Nat.stirlingFirst j k := by
  intro j
  induction j with
  | zero =>
    intro k
    rw [ascPochhammer_zero, coeff_one]
    cases k with
    | zero => rfl
    | succ k => rfl
  | succ j ih =>
    intro k
    rw [ascPochhammer_succ_right, mul_add, coeff_add, coeff_mul_natCast]
    cases k with
    | zero =>
      rw [coeff_mul_X_zero, ih 0, Nat.cast_id, stirlingFirst_zero_right_mul_a039692]
      rfl
    | succ k =>
      rw [coeff_mul_X, ih k, ih (k + 1), Nat.stirlingFirst_succ_succ, Nat.cast_id]
      ring

private lemma sum_stirlingFirst_a039692 (n k : ℕ) (hk : k ≤ n) :
    ∑ m ∈ range (n + 1), Nat.stirlingFirst k m = k.factorial := by
  have h1 : (ascPochhammer ℕ k).eval 1 = k.factorial := by
    have h := ascPochhammer_eval_one ℕ k
    simpa using h
  have hdeg : (ascPochhammer ℕ k).natDegree < n + 1 := by
    rw [ascPochhammer_natDegree]
    omega
  have h2 := eval_eq_sum_range' hdeg (1 : ℕ)
  rw [h1] at h2
  rw [h2]
  apply sum_congr rfl
  intro m _
  rw [coeff_ascPochhammer_a039692, one_pow, mul_one]

theorem OMA.solution : type_of% @OMA.S_oeis_a039692.main := by
  intro n _
  unfold entry
  rw [← mul_sum]
  congr 1
  rw [sum_comm]
  have hk : ∀ k ∈ range (n + 1),
      ∑ m ∈ range (n + 1), (Nat.stirlingFirst k m : ℚ) * (k.choose (n - k) : ℚ) / k.factorial
        = (k.choose (n - k) : ℚ) := by
    intro k hk
    rw [mem_range] at hk
    rw [← sum_div, ← sum_mul]
    have hS : ∑ m ∈ range (n + 1), (Nat.stirlingFirst k m : ℚ) = (k.factorial : ℚ) := by
      exact_mod_cast sum_stirlingFirst_a039692 n k (by omega)
    rw [hS]
    have hf : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    field_simp
  rw [sum_congr rfl hk, Nat.fib_succ_eq_sum_choose, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  push_cast
  rfl
