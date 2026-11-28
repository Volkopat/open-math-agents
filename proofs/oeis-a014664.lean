import OMAStatements.S_oeis_a014664
import Mathlib

/-
A014664: for an odd prime p with p^2 not dividing 2^(p-1) - 1, the order of 2 modulo p^k is
d p^(k-1), where d is the order of 2 modulo p.

2^n = 1 in ZMod N exactly when N divides 2^n - 1, so p divides 2^n - 1 exactly when d divides n.
Lifting the exponent: v_p(2^(d m) - 1) = v_p(2^d - 1) + v_p(m). Taking m = (p - 1)/d, which is
prime to p, shows v_p(2^d - 1) = v_p(2^(p-1) - 1), which is 1 by assumption. Hence p^k divides
2^(d m) - 1 exactly when p^(k-1) divides m, and the two divisibilities between the order and
d p^(k-1) follow.
-/

namespace OMA.P014664

lemma pow_eq_one_iff (N n : ℕ) : (2 : ZMod N) ^ n = 1 ↔ N ∣ 2 ^ n - 1 := by
  have h : ((2 ^ n - 1 : ℕ) : ZMod N) = (2 : ZMod N) ^ n - 1 := by
    rw [Nat.cast_sub Nat.one_le_two_pow]
    simp
  rw [← ZMod.natCast_eq_zero_iff, h, sub_eq_zero]

lemma main' :
    ∀ p k : ℕ, Nat.Prime p → Odd p → ¬ (p ^ 2 ∣ 2 ^ (p - 1) - 1) → 1 ≤ k →
      orderOf (2 : ZMod (p ^ k)) = orderOf (2 : ZMod p) * p ^ (k - 1) := by
  intro p k hp hodd hw hk
  have := Fact.mk hp
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact absurd hodd (by decide)
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 ((ZMod.natCast_eq_zero_iff 2 p).1 h'))
  obtain ⟨d, hd⟩ : ∃ d, d = orderOf (2 : ZMod p) := ⟨_, rfl⟩
  rw [← hd]
  have hdp : d ∣ p - 1 := hd ▸ ZMod.orderOf_dvd_card_sub_one h2
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdp (by have := hp.two_le; omega)
  have hA : ∀ n, p ∣ 2 ^ n - 1 ↔ d ∣ n := fun n => by
    rw [← pow_eq_one_iff, hd, orderOf_dvd_iff_pow_eq_one]
  have hpd : p ∣ 2 ^ d - 1 := (hA d).2 dvd_rfl
  have hnd : ¬ p ∣ 2 ^ d := fun h =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  have hlt : 1 < 2 ^ d := Nat.one_lt_two_pow hd0.ne'
  have hV : ∀ m, m ≠ 0 →
      padicValNat p (2 ^ (d * m) - 1) = padicValNat p (2 ^ d - 1) + padicValNat p m := by
    intro m hm
    have h := padicValNat.pow_sub_pow hodd hlt hpd hnd hm
    rw [one_pow, ← pow_mul] at h
    exact h
  have hv1 : padicValNat p (2 ^ d - 1) = 1 := by
    obtain ⟨e, he⟩ := hdp
    have he0 : e ≠ 0 := by
      rintro rfl
      have := hp.two_le
      omega
    have h1 := hV e he0
    rw [← he] at h1
    have hpe : ¬ p ∣ e := by
      intro h
      have h3 := Nat.le_of_dvd (Nat.pos_of_ne_zero he0) h
      have h4 : e ≤ p - 1 := by
        rw [he]
        exact Nat.le_mul_of_pos_left e hd0
      omega
    rw [padicValNat.eq_zero_of_not_dvd hpe, add_zero] at h1
    have hne : 2 ^ (p - 1) - 1 ≠ 0 := by
      have : 1 < 2 ^ (p - 1) := Nat.one_lt_two_pow (by have := hp.two_le; omega)
      omega
    have hle : ¬ 2 ≤ padicValNat p (2 ^ (p - 1) - 1) := fun h =>
      hw ((padicValNat_dvd_iff_le hne).2 h)
    have hge : 1 ≤ padicValNat p (2 ^ d - 1) :=
      (padicValNat_dvd_iff_le (by omega : 2 ^ d - 1 ≠ 0)).1 (by simpa using hpd)
    omega
  have hB : ∀ m, m ≠ 0 → (p ^ k ∣ 2 ^ (d * m) - 1 ↔ p ^ (k - 1) ∣ m) := by
    intro m hm
    have hne : 2 ^ (d * m) - 1 ≠ 0 := by
      have : 1 < 2 ^ (d * m) := Nat.one_lt_two_pow (Nat.mul_ne_zero hd0.ne' hm)
      omega
    rw [padicValNat_dvd_iff_le hne, padicValNat_dvd_iff_le hm, hV m hm, hv1]
    omega
  apply Nat.dvd_antisymm
  · rw [orderOf_dvd_iff_pow_eq_one, pow_eq_one_iff]
    exact (hB (p ^ (k - 1)) (pow_ne_zero _ hp.ne_zero)).2 dvd_rfl
  · have hN := pow_orderOf_eq_one (2 : ZMod (p ^ k))
    rw [pow_eq_one_iff] at hN
    have hpN : p ∣ 2 ^ orderOf (2 : ZMod (p ^ k)) - 1 :=
      (dvd_pow_self p (by omega : k ≠ 0)).trans hN
    obtain ⟨m, hm⟩ := (hA _).1 hpN
    rw [hm] at hN ⊢
    rcases Nat.eq_zero_or_pos m with rfl | hmpos
    · simp
    · exact Nat.mul_dvd_mul_left d ((hB m hmpos.ne').1 hN)

end OMA.P014664

theorem OMA.solution : type_of% @OMA.S_oeis_a014664.main := OMA.P014664.main'
