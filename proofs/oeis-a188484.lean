import OMAStatements.S_oeis_a188484
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic

namespace OMA.P_oeis_a188484

open OMA.S_oeis_a188484

private lemma sigma_550564 : ∑ d ∈ (550564 : ℕ).divisors, d = 1142337 := by
  have hfac : (550564 : ℕ) = 2 ^ 2 * (7 ^ 2 * 53 ^ 2) := by norm_num
  have hc1 : Nat.Coprime (2 ^ 2) (7 ^ 2 * 53 ^ 2) :=
    ((by norm_num : Nat.Coprime 2 7).pow 2 2).mul_right ((by norm_num : Nat.Coprime 2 53).pow 2 2)
  have hc2 : Nat.Coprime (7 ^ 2) (53 ^ 2) := (by norm_num : Nat.Coprime 7 53).pow 2 2
  have hsig : ArithmeticFunction.sigma 1 550564 = 1142337 := by
    rw [hfac,
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hc1,
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hc2,
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7),
      ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 53)]
    norm_num [Finset.sum_range_succ]
  rw [← ArithmeticFunction.sigma_one_apply]
  exact hsig

private theorem prove_disproof : ¬ (type_of% @OMA.S_oeis_a188484.main) := by
  intro h
  have h550564 := h 550564 (by norm_num)
  apply h550564
  refine ⟨101, ?_⟩
  unfold abundance
  have hs : (∑ d ∈ (550564 : ℕ).divisors, (d : ℤ)) = 1142337 := by
    rw [← Nat.cast_sum, sigma_550564]
    norm_num
  rw [hs]
  norm_num

end OMA.P_oeis_a188484

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a188484.main) :=
  OMA.P_oeis_a188484.prove_disproof
