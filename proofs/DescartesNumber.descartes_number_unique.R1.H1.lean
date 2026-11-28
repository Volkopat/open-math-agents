import OMAReductions.R_DescartesNumber_descartes_number_unique_R1
import Mathlib

/-! In a Descartes factorization `σ(m)(w+1) = 2mw` with `m w` odd. Writing `w = 2c+1` gives
`σ(m)(c+1) = m(2c+1)`, which is odd: so `σ(m)` is odd, forcing the odd number `m` to be a square,
and `c + 1` is odd, so `w ≡ 1 (mod 4)`. -/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- An odd number with odd divisor sum is a square. -/
lemma odd_sigma_square {n : ℕ} : Odd n → Odd (σ 1 n) → IsSquare n := by
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

theorem OMA.solution : OMA.R_DescartesNumber_descartes_number_unique_R1.H1 := by
  rintro m w ⟨-, hodd, -, heq⟩
  obtain ⟨hm, hw⟩ := Nat.odd_mul.1 hodd
  obtain ⟨c, rfl⟩ := hw
  have e : σ 1 m * (c + 1) = m * (2 * c + 1) := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 by norm_num)
    linarith [heq]
  have ho : Odd (σ 1 m * (c + 1)) := by rw [e]; exact hm.mul (odd_two_mul_add_one c)
  obtain ⟨hs, hc⟩ := Nat.odd_mul.1 ho
  refine ⟨odd_sigma_square hm hs, ?_⟩
  obtain ⟨d, hd⟩ := hc
  omega
