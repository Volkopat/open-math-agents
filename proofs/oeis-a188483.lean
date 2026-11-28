import OMAStatements.S_oeis_a188483
import Mathlib

-- Counterexample n = 742^2 = 550564 = 2^2 * 7^2 * 53^2 (OEIS A188483/A188486: the squares of A188483 are
-- counterexamples to Kravitz's conjecture): sigma(n) = 7 * 57 * 2863 = 1142337 = 2 * 550564 + 203^2.

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a188483.main) := by
  intro h
  have key : ArithmeticFunction.sigma 1 550564 = 1142337 := by
    rw [show (550564 : ℕ) = (2 ^ 2 * 7 ^ 2) * 53 ^ 2 by norm_num,
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num),
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (by norm_num),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num)]
    simp [Finset.sum_range_succ]
  have hs : OMA.S_oeis_a188483.sigma 550564 = 1142337 := by
    unfold OMA.S_oeis_a188483.sigma
    rw [← ArithmeticFunction.sigma_one_apply]
    exact key
  exact h 550564 (by norm_num) ⟨101, by rw [hs]; norm_num⟩
