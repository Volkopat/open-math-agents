import OMAReductions.R_OeisA2326_conjecture2_R2

-- Step OeisA2326.conjecture2.R2.H1: hypothesis H1 of reduction OeisA2326.conjecture2.R2
-- Credit: @Ezekia1
-- One kernel computation shows that p ^ 2 does not divide 2 ^ (p - 1) - 1 for 1 ≤ p ≤ 1000.
-- Lifting the exponent then gives, by induction on m ≥ 1, that the order of 2 modulo p ^ (m + 1)
-- is p times the order modulo p ^ m. The bound on k is not needed.

namespace OMA.A2326H1

/-- The order of 2 modulo n. -/
noncomputable def od (n : ℕ) : ℕ := orderOf (2 : ZMod n)

/-- No number from 1 to 1000 is a Wieferich number. -/
theorem wief : ∀ p : ℕ, p < 1001 → 1 ≤ p → 2 ^ (p - 1) % p ^ 2 ≠ 1 := by
  decide +kernel

theorem two_pow_eq_one_iff (n e : ℕ) : (2 : ZMod n) ^ e = 1 ↔ n ∣ 2 ^ e - 1 := by
  have h1 : (1 : ℕ) ≤ 2 ^ e := Nat.one_le_two_pow
  rw [← Nat.modEq_iff_dvd' h1, ← ZMod.natCast_eq_natCast_iff]
  push_cast
  exact eq_comm

theorem od_dvd_iff (n e : ℕ) : od n ∣ e ↔ n ∣ 2 ^ e - 1 := by
  rw [od, orderOf_dvd_iff_pow_eq_one, two_pow_eq_one_iff]

theorem dvd_od (n : ℕ) : n ∣ 2 ^ od n - 1 := (od_dvd_iff n (od n)).mp dvd_rfl

theorem od_pos (n : ℕ) (hn : Nat.Coprime 2 n) : 0 < od n := by
  have hpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h] at hn
      simp at hn
    · exact h
  have h := Nat.ModEq.pow_totient hn
  have h2 : od n ∣ Nat.totient n := by
    rw [od_dvd_iff]
    exact (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp h.symm
  exact Nat.pos_of_dvd_of_pos h2 (Nat.totient_pos.mpr hpos)

theorem coprime_two (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (j : ℕ) : Nat.Coprime 2 (p ^ j) :=
  Nat.Coprime.pow_right j ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))

/-- One lifting step. -/
theorem step (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (m : ℕ) (hm : 1 ≤ m)
    (hv : ¬ p ^ (m + 1) ∣ 2 ^ od (p ^ m) - 1) :
    od (p ^ (m + 1)) = p * od (p ^ m) ∧ ¬ p ^ (m + 1 + 1) ∣ 2 ^ od (p ^ (m + 1)) - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hdpos0 : 0 < od (p ^ m) := od_pos _ (coprime_two p hp hp2 m)
  have hpm0 : p ^ m ∣ 2 ^ od (p ^ m) - 1 := dvd_od (p ^ m)
  have hdvd20 : od (p ^ m) ∣ od (p ^ (m + 1)) := by
    rw [od_dvd_iff]
    exact (pow_dvd_pow p (Nat.le_succ m)).trans (dvd_od (p ^ (m + 1)))
  obtain ⟨d, hd⟩ : ∃ d, od (p ^ m) = d := ⟨_, rfl⟩
  rw [hd] at hv hdpos0 hpm0 hdvd20
  rw [hd]
  have hx1 : 1 < 2 ^ d := Nat.one_lt_two_pow (by omega)
  have hpd : p ∣ 2 ^ d - 1 := (dvd_pow_self p (by omega : m ≠ 0)).trans hpm0
  have hnp : ¬ p ∣ 2 ^ d := fun h =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  have hlte := padicValNat.pow_sub_pow hodd hx1 hpd hnp (n := p) hp.ne_zero
  rw [one_pow, padicValNat_self, ← pow_mul] at hlte
  have hne : 2 ^ d - 1 ≠ 0 := by omega
  have hne' : 2 ^ (d * p) - 1 ≠ 0 := by
    have : 1 < 2 ^ (d * p) := Nat.one_lt_two_pow (Nat.mul_ne_zero (by omega) hp.ne_zero)
    omega
  have hvm : padicValNat p (2 ^ d - 1) = m := by
    have h1 : m ≤ padicValNat p (2 ^ d - 1) := (padicValNat_dvd_iff_le hne).mp hpm0
    have h2 : ¬ m + 1 ≤ padicValNat p (2 ^ d - 1) := fun h =>
      hv ((padicValNat_dvd_iff_le hne).mpr h)
    omega
  rw [hvm] at hlte
  have hdvd1 : od (p ^ (m + 1)) ∣ d * p := by
    rw [od_dvd_iff, padicValNat_dvd_iff_le hne', hlte]
  obtain ⟨c, hc⟩ := hdvd20
  have hcp : c ∣ p := by
    rw [hc] at hdvd1
    exact Nat.dvd_of_mul_dvd_mul_left hdpos0 hdvd1
  rcases (Nat.dvd_prime hp).mp hcp with h1 | h1
  · exfalso
    apply hv
    have h3 := dvd_od (p ^ (m + 1))
    rw [hc, h1, mul_one] at h3
    exact h3
  · rw [hc, h1]
    refine ⟨mul_comm d p, ?_⟩
    rw [padicValNat_dvd_iff_le hne', hlte]
    omega

/-- The exact power of p in 2 ^ (order) - 1, for every exponent. -/
theorem exact (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hw : ¬ p ^ 2 ∣ 2 ^ (p - 1) - 1) :
    ∀ m, 1 ≤ m → ¬ p ^ (m + 1) ∣ 2 ^ od (p ^ m) - 1 := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    intro h
    apply hw
    have h1 : od (p ^ 1) ∣ p - 1 := by
      rw [od_dvd_iff, pow_one]
      have h2 := Nat.ModEq.pow_totient ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
      rw [Nat.totient_prime hp] at h2
      exact (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp h2.symm
    exact h.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 h1)
  | succ m hm ih => exact (step p hp hp2 m hm ih).2

theorem a_eq (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (m : ℕ) :
    OeisA2326.a ((p ^ m - 1) / 2) = od (p ^ m) := by
  have hodd : Odd (p ^ m) := (hp.odd_of_ne_two hp2).pow
  obtain ⟨t, ht⟩ := hodd
  have h : 2 * ((p ^ m - 1) / 2) + 1 = p ^ m := by omega
  unfold OeisA2326.a od
  rw [h]

end OMA.A2326H1

open OMA.A2326H1 in
theorem OMA.solution : OMA.R_OeisA2326_conjecture2_R2.H1 := by
  intro k hk _ p hp hp2 hp1000
  have hw : ¬ p ^ 2 ∣ 2 ^ (p - 1) - 1 := fun h => by
    have h1 : 1 ≡ 2 ^ (p - 1) [MOD p ^ 2] := (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mpr h
    have h2 : 1 % p ^ 2 = 2 ^ (p - 1) % p ^ 2 := h1
    rw [Nat.mod_eq_of_lt (Nat.one_lt_pow (by norm_num) hp.one_lt)] at h2
    exact wief p (by omega) hp.pos h2.symm
  rw [a_eq p hp hp2, a_eq p hp hp2]
  exact (step p hp hp2 k (by omega) (exact p hp hp2 hw k (by omega))).1
