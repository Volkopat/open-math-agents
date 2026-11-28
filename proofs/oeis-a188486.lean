import OMAStatements.S_oeis_a188486
import Mathlib

-- Counterexample n = 550564 = 2^2 * 7^2 * 53^2, the first term of OEIS A188486 (Weisstein):
-- sigma(n) = 7 * 57 * 2863 = 1142337 = 2 * 550564 + 203^2, and 203 is odd.

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a188486.main) := by
  intro h
  have key : ArithmeticFunction.sigma 1 550564 = 1142337 := by
    rw [show (550564 : ℕ) = (2 ^ 2 * 7 ^ 2) * 53 ^ 2 by norm_num,
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num),
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num)]
    simp [Finset.sum_range_succ]
  exact h 550564 (by norm_num) 203 (by norm_num) ⟨101, by norm_num⟩ (by rw [key]; norm_num)
