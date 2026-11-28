import OMAStatements.S_oeis_a283107
import Mathlib

open ArithmeticFunction in
theorem OMA.solution : type_of% @OMA.S_oeis_a283107.main := by
  intro k hk hp
  obtain ⟨e, m, hm, he⟩ := Nat.exists_eq_two_pow_mul_odd (show k - 1 ≠ 0 by omega)
  have s : sigma 1 (2 ^ (e + 2)) = mersenne (e + 3) := by
    simp_rw [sigma_one_apply_prime_pow Nat.prime_two, mersenne, show 2 = 1 + 1 from rfl,
      ← geom_sum_mul_add 1 (e + 3)]; norm_num
  rw [show 4 * (k - 1) = 2 ^ (e + 2) * m by rw [he, pow_add]; ring] at hp ⊢
  rw [isMultiplicative_sigma.map_mul_of_coprime (hm.coprime_two_left.pow_left _), s,
    Nat.prime_mul_iff, sigma_eq_one_iff] at hp
  rcases hp with ⟨h, rfl⟩ | ⟨-, h⟩
  · rw [mul_one, sigma_zero_apply_prime_pow Nat.prime_two]; exact h.of_mersenne
  · have := one_lt_mersenne.2 (show 1 < e + 3 by omega); omega
