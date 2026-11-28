import OMAStatements.S_oeis_a239050
import Mathlib

/-!
# A239050: 4σ(n) = σ(3n) exactly when 3 ∤ n

If 3 ∤ n, σ is multiplicative and σ(3) = 4. If n = 3^e·m with e ≥ 1 and 3 ∤ m, then
σ(3n) = (3σ(3^e) + 1)σ(m) while 4σ(n) = 4σ(3^e)σ(m); equality would force σ(3^e) = 1, but
σ(3^e) ≥ 4 (the argument in the entry).
-/

namespace PA239050
open ArithmeticFunction

theorem sigma_pow_succ (e : ℕ) : sigma 1 (3 ^ (e + 1)) = 3 * sigma 1 (3 ^ e) + 1 := by
  rw [sigma_one_apply_prime_pow (by norm_num), sigma_one_apply_prime_pow (by norm_num),
    Finset.sum_range_succ', Finset.mul_sum]
  simp only [pow_succ, pow_zero]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem sigma_pow_ge (e : ℕ) (he : 1 ≤ e) : 4 ≤ sigma 1 (3 ^ e) := by
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
  rw [sigma_pow_succ]
  have : 1 ≤ sigma 1 (3 ^ k) := (sigma_pos_iff).mpr (by positivity)
  omega

end PA239050

open ArithmeticFunction in
theorem OMA.solution : type_of% @OMA.S_oeis_a239050.main := by
  intro n hn
  unfold OMA.S_oeis_a239050.a
  constructor
  · intro h h3
    obtain ⟨e, m, hm3, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : n ≠ 0) 3 (by norm_num)
    have he : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with rfl | he
      · simp at h3; exact absurd h3 hm3
      · exact he
    have hcop : ∀ k, Nat.Coprime (3 ^ k) m := fun k =>
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr hm3)
    rw [← mul_assoc, ← pow_succ', isMultiplicative_sigma.map_mul_of_coprime (hcop _),
      isMultiplicative_sigma.map_mul_of_coprime (hcop _), PA239050.sigma_pow_succ] at h
    have hm : 0 < sigma 1 m := (sigma_pos_iff).mpr (by
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp at hm3
      · exact hm)
    have h' : (4 * sigma 1 (3 ^ e)) * sigma 1 m = (3 * sigma 1 (3 ^ e) + 1) * sigma 1 m := by
      rw [← h]; ring
    have := Nat.eq_of_mul_eq_mul_right hm h'
    have := PA239050.sigma_pow_ge e he
    omega
  · intro h3
    have hcop : Nat.Coprime 3 n := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h3
    rw [isMultiplicative_sigma.map_mul_of_coprime hcop]
    congr 1
