import OMAStatements.S_oeis_a279915

/-! The counterexample x=127, y=173369889 is due to @agchua (#26182).
Retain that witness and its prime-power factorization; apply the multiplicative
sigma API directly to evaluate it. This refutes part (i) only. -/

namespace A279915Sigma

theorem hsig : ArithmeticFunction.sigma 1 173369889 = 349491681 := by
  rw [show 173369889 = 3 ^ 4 * 7 ^ 2 * 11 ^ 2 * 19 ^ 2 by norm_num]
  rw [(ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime
    (by norm_num : Nat.Coprime (3 ^ 4 * 7 ^ 2 * 11 ^ 2) (19 ^ 2))]
  rw [(ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime
    (by norm_num : Nat.Coprime (3 ^ 4 * 7 ^ 2) (11 ^ 2))]
  rw [(ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime
    (by norm_num : Nat.Coprime (3 ^ 4) (7 ^ 2))]
  rw [ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_three,
    ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7),
    ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11),
    ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 19)]
  norm_num [Finset.sum_range_succ]

end A279915Sigma

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a279915.main) := by
  intro H
  have key : Nat.totient 127 * ArithmeticFunction.sigma 1 173369889 =
      2 * 127 * 173369889 := by
    rw [A279915Sigma.hsig, Nat.totient_prime (by norm_num : Nat.Prime 127)]
  obtain ⟨r, hr⟩ := H.1.2 127 173369889 (by norm_num) (by norm_num) key
  omega
