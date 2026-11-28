import OMAStatements.S_oeis_a400825
import Mathlib

/-
A400825: for N = (2^k - 1) 2^(k+4) + 1, if 2^((N-1)/4) = -1 modulo N then N is prime.

(N-1)/4 = (2^k - 1) 2^(k+2). Let q be the least prime factor of N; q is odd. Modulo q the
element x = 2^(2^k - 1) satisfies x^(2^(k+2)) = -1, which is not 1, and x^(2^(k+3)) = 1, so x
has order 2^(k+3), which divides q - 1. Hence q >= 8 * 2^k + 1. If N were composite then
q^2 <= N <= 16 * 4^k + 1, which is impossible.
-/

namespace OMA.P400825

lemma main' (k : ℕ) (hk : 1 ≤ k)
    (h : (2 : ZMod ((2 ^ k - 1) * 2 ^ (k + 4) + 1)) ^
      (((2 ^ k - 1) * 2 ^ (k + 4) + 1 - 1) / 4) = -1) :
    ((2 ^ k - 1) * 2 ^ (k + 4) + 1).Prime := by
  by_contra hnp
  have ht : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hpos : 0 < (2 ^ k - 1) * 2 ^ (k + 4) := Nat.mul_pos (by omega) (by positivity)
  have hq2 : (2 ^ k - 1) * 2 ^ (k + 4) + 1 = 2 * ((2 ^ k - 1) * 2 ^ (k + 3)) + 1 := by ring
  have he : ((2 ^ k - 1) * 2 ^ (k + 4) + 1 - 1) / 4 = (2 ^ k - 1) * 2 ^ (k + 2) := by
    have : (2 ^ k - 1) * 2 ^ (k + 4) + 1 - 1 = (2 ^ k - 1) * 2 ^ (k + 2) * 4 := by
      rw [Nat.add_sub_cancel]; ring
    rw [this, Nat.mul_div_cancel _ (by norm_num)]
  rw [he] at h
  generalize hN : (2 ^ k - 1) * 2 ^ (k + 4) + 1 = N at h hnp hq2
  have hqp : N.minFac.Prime := Nat.minFac_prime (by omega)
  have hqd : N.minFac ∣ N := Nat.minFac_dvd N
  have hsq : N.minFac ^ 2 ≤ N := Nat.minFac_sq_le_self (by omega) hnp
  have hne2 : N.minFac ≠ 2 := by
    intro h2
    have := (Nat.minFac_eq_two_iff N).1 h2
    omega
  generalize N.minFac = q at hqp hqd hsq hne2
  have := Fact.mk hqp
  have : Fact (2 < q) := ⟨by have := hqp.two_le; omega⟩
  have h' : (2 : ZMod q) ^ ((2 ^ k - 1) * 2 ^ (k + 2)) = -1 := by
    have := congrArg (ZMod.castHom hqd (ZMod q)) h
    rwa [map_pow, map_neg, map_one, map_ofNat] at this
  have hx1 : ¬ ((2 : ZMod q) ^ (2 ^ k - 1)) ^ 2 ^ (k + 2) = 1 := by
    rw [← pow_mul, h']
    exact ZMod.neg_one_ne_one
  have hx2 : ((2 : ZMod q) ^ (2 ^ k - 1)) ^ 2 ^ (k + 2 + 1) = 1 := by
    rw [pow_succ 2 (k + 2), pow_mul, ← pow_mul (2 : ZMod q), h']
    norm_num
  have ho := orderOf_eq_prime_pow hx1 hx2
  have hx0 : (2 : ZMod q) ^ (2 ^ k - 1) ≠ 0 := by
    intro hx0
    rw [hx0, zero_pow (by positivity)] at hx2
    exact zero_ne_one hx2
  have hd : 2 ^ (k + 2 + 1) ∣ q - 1 := ho ▸ ZMod.orderOf_dvd_card_sub_one hx0
  have hle := Nat.le_of_dvd (by have := hqp.two_le; omega) hd
  have e3 : 2 ^ (k + 2 + 1) = 8 * 2 ^ k := by ring
  have e4 : 2 ^ (k + 4) = 16 * 2 ^ k := by ring
  have hNle : N ≤ 2 ^ k * (16 * 2 ^ k) + 1 := by
    rw [← hN, e4]
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.sub_le _ _)) 1
  have hq8 : 8 * 2 ^ k + 1 ≤ q := by omega
  nlinarith [Nat.mul_le_mul hq8 hq8]

end OMA.P400825

theorem OMA.solution : type_of% @OMA.S_oeis_a400825.main := fun k hk h => OMA.P400825.main' k hk h
