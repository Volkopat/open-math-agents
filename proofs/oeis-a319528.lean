import OMAStatements.S_oeis_a319528
import Mathlib

/-! Proof for OEIS A319528. If `7 ∤ n`, multiplicativity and `σ(7) = 8` give `σ(7n) = 8 σ(n)`. If
`7 ∣ n`, write `n = 7^e m` with `e ≥ 1`, `7 ∤ m`; then `σ(7n) = σ(7^(e+1)) σ(m)` and
`σ(7^(e+1)) = 7 σ(7^e) + 1`, so `σ(7n) = 8 σ(n)` would force `σ(7^e) = 1`, while `σ(7^e) ≥ 8`.
Credit: Sudharsan Rajendiran -/

namespace OMA.P319528
open ArithmeticFunction

lemma sigma_pow7 (k : ℕ) : sigma 1 (7 ^ (k + 1)) = 7 * sigma 1 (7 ^ k) + 1 := by
  rw [sigma_one_apply_prime_pow (by norm_num), sigma_one_apply_prime_pow (by norm_num),
    Finset.sum_range_succ', Finset.mul_sum]
  simp [pow_succ, mul_comm]

lemma sigma_seven : sigma 1 7 = 8 := by
  have := sigma_pow7 0; simpa using this

end OMA.P319528

theorem OMA.solution : type_of% @OMA.S_oeis_a319528.main := by
  intro n hn
  open ArithmeticFunction in
  constructor
  · intro h h7
    obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : n ≠ 0) 7 (by norm_num)
    have hm0 : m ≠ 0 := by rintro rfl; simp at hm
    have he : e ≠ 0 := by
      rintro rfl; simp at h7; exact hm h7
    have hcop : ∀ j, Nat.Coprime (7 ^ j) m := fun j =>
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr hm)
    rw [show 7 * (7 ^ e * m) = 7 ^ (e + 1) * m by ring,
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (hcop _),
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (hcop _),
      OMA.P319528.sigma_pow7] at h
    have hsm : 0 < ArithmeticFunction.sigma 1 m := by
      rw [ArithmeticFunction.sigma_one_apply]
      exact Finset.sum_pos (fun d hd => Nat.pos_of_mem_divisors hd) ⟨1, by simp [hm0]⟩
    have hse : 8 ≤ ArithmeticFunction.sigma 1 (7 ^ e) := by
      obtain ⟨j, rfl⟩ : ∃ j, e = j + 1 := ⟨e - 1, by omega⟩
      rw [OMA.P319528.sigma_pow7]
      have : 1 ≤ ArithmeticFunction.sigma 1 (7 ^ j) := by
        rw [ArithmeticFunction.sigma_one_apply]
        exact Finset.sum_pos (fun d hd => Nat.pos_of_mem_divisors hd) ⟨1, by simp⟩
      omega
    have : 8 * ArithmeticFunction.sigma 1 (7 ^ e) = 7 * ArithmeticFunction.sigma 1 (7 ^ e) + 1 := by
      rw [← mul_assoc] at h
      exact Nat.eq_of_mul_eq_mul_right hsm h.symm
    omega
  · intro h7
    have hcop : Nat.Coprime 7 n := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h7
    rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, OMA.P319528.sigma_seven]

