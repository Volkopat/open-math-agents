import OMAStatements.S_oeis_a071011

/-! Formalization of the divisibility conjecture listed in OEIS A071011.
The two-square characterization supplies a prime congruent to 3 modulo 4
with odd exponent. Its divisor-sum factor groups into pairs, each divisible by 4. -/

open scoped BigOperators

private theorem four_dvd_pair_sum {p : ℕ} (hp : p % 4 = 3) (k : ℕ) :
    4 ∣ ∑ i ∈ Finset.range (2 * k), p ^ i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega, Finset.sum_range_succ,
      Finset.sum_range_succ]
    have hpair : p ^ (2 * k) + p ^ (2 * k + 1) = p ^ (2 * k) * (1 + p) := by
      rw [pow_succ]
      ring
    rw [add_assoc, hpair]
    exact dvd_add ih (dvd_mul_of_dvd_right (by omega : 4 ∣ 1 + p) _)

theorem OMA.solution : type_of% @OMA.S_oeis_a071011.main := by
  intro m hm
  have hm0 : m ≠ 0 := by
    intro h
    exact hm ⟨0, 0, by subst m; norm_num⟩
  rw [Nat.eq_sq_add_sq_iff] at hm
  push Not at hm
  obtain ⟨p, hp, hpmod, hpodd⟩ := hm
  have hExp : Odd (m.factorization p) := by
    rw [Nat.factorization_def _ (Nat.prime_of_mem_primeFactors hp)]
    exact Nat.not_even_iff_odd.mp hpodd
  obtain ⟨k, hk⟩ := hExp
  have hEven : m.factorization p + 1 = 2 * (k + 1) := by omega
  apply Nat.mod_eq_zero_of_dvd
  rw [ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hm0]
  simp only [mul_one]
  refine (four_dvd_pair_sum hpmod (k + 1)).trans ?_
  rw [← hEven]
  exact Finset.dvd_prod_of_mem _ hp

