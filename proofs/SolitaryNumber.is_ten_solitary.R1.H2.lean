import OMAReductions.R_SolitaryNumber_is_ten_solitary_R1

open ArithmeticFunction in
open scoped ArithmeticFunction.sigma in
theorem OMA.solution : OMA.R_SolitaryNumber_is_ten_solitary_R1.H2 := by
  have key {n : ℕ} : Odd n → Odd (σ 1 n) → IsSquare n := by
    induction n using Nat.recOnPosPrimePosCoprime with
    | zero => simp
    | one => simp
    | prime_pow p k hp hk =>
      intro hn hσ
      have h (i : ℕ) : Odd (p ^ i) := ((Nat.odd_pow_iff hk.ne').1 hn).pow
      rw [sigma_one_apply_prime_pow hp, Finset.odd_sum_iff_odd_card_odd] at hσ
      simp [h, Nat.odd_iff] at hσ
      exact ⟨p ^ (k / 2), by rw [← pow_add]; congr 1; omega⟩
    | coprime a b ha hb hab ihA ihB =>
      intro hn hσ
      rw [isMultiplicative_sigma.map_mul_of_coprime hab] at hσ
      exact (ihA (Nat.odd_mul.1 hn).1 (Nat.odd_mul.1 hσ).1).mul (ihB (Nat.odd_mul.1 hn).2 (Nat.odd_mul.1 hσ).2)
  intro m hm h
  exact key hm (Nat.odd_iff.2 (by obtain ⟨t, rfl⟩ := hm; omega))
