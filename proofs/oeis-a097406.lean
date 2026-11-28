import OMAStatements.S_oeis_a097406
import Mathlib

/-!
# OEIS A097406: primitive prime factors of `2^n - 1` are `≡ 1 (mod n)`

Let `p` be a prime dividing `2^n - 1` (`n ≥ 1`) and let `o` be the multiplicative order of `2`
modulo `p`. Then `o ∣ n`, and `o ∣ p - 1` by Fermat's little theorem.

* If `p` is a primitive prime factor of `2^n - 1` (it divides no `2^m - 1` with `1 ≤ m < n`),
  then `o = n`, because `p ∣ 2^o - 1` and `1 ≤ o ≤ n`.
* If `n` is prime, then `o ∈ {1, n}`, and `o = 1` would mean `p ∣ 2 - 1`.

In both cases `n = o ∣ p - 1`, that is `p = k n + 1`.
-/

open OMA.S_oeis_a097406

namespace OMA.A097406

/-- `p ∣ 2^m - 1` iff `2^m = 1` in `ZMod p`. -/
lemma dvd_iff (p m : ℕ) : p ∣ 2 ^ m - 1 ↔ (2 : ZMod p) ^ m = 1 := by
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub Nat.one_le_two_pow]
  push_cast
  exact sub_eq_zero

/-- If the order of `2` modulo the prime `p` is `n ≥ 1`, then `p = k n + 1`. -/
lemma of_order (n p : ℕ) (hn : 1 ≤ n) (hp : p.Prime) (ho : orderOf (2 : ZMod p) = n) :
    ∃ k : ℕ, p = k * n + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h0
    have h1 : (2 : ZMod p) ^ n = 1 := by rw [← ho]; exact pow_orderOf_eq_one _
    rw [h0, zero_pow (by omega)] at h1
    exact zero_ne_one h1
  have hdvd : n ∣ p - 1 := ho ▸ ZMod.orderOf_dvd_card_sub_one h2
  obtain ⟨k, hk⟩ := hdvd
  exact ⟨k, by have := hp.pos; rw [mul_comm] at hk; omega⟩

end OMA.A097406

open OMA.A097406 in
theorem OMA.solution : type_of% @OMA.S_oeis_a097406.main := by
  constructor
  · -- primitive prime factors
    rintro n p hn ⟨hp, hdvd, hprim⟩ -
    apply of_order n p hn hp
    have h1 : (2 : ZMod p) ^ n = 1 := (dvd_iff p n).mp hdvd
    have hon : orderOf (2 : ZMod p) ∣ n := orderOf_dvd_of_pow_eq_one h1
    have hopos : 0 < orderOf (2 : ZMod p) :=
      Nat.pos_of_dvd_of_pos hon (by omega)
    have hle : orderOf (2 : ZMod p) ≤ n := Nat.le_of_dvd (by omega) hon
    by_contra hne
    have hlt : orderOf (2 : ZMod p) < n := lt_of_le_of_ne hle hne
    exact hprim _ hopos hlt ((dvd_iff p _).mpr (pow_orderOf_eq_one _))
  · -- prime exponents
    intro n p hn hp hdvd
    apply of_order n p hn.one_lt.le hp
    have h1 : (2 : ZMod p) ^ n = 1 := (dvd_iff p n).mp hdvd
    have hon : orderOf (2 : ZMod p) ∣ n := orderOf_dvd_of_pow_eq_one h1
    rcases (Nat.dvd_prime hn).mp hon with h | h
    · -- order `1` would give `p ∣ 1`
      exfalso
      have h' : (2 : ZMod p) ^ 1 = 1 := by
        have hpow := pow_orderOf_eq_one (2 : ZMod p)
        rwa [h] at hpow
      have hp1 : p ∣ 2 ^ 1 - 1 := (dvd_iff p 1).mpr h'
      have := Nat.le_of_dvd (by norm_num) hp1
      have := hp.two_le
      omega
    · exact h
