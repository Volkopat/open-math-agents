import OMAReductions.R_mo_342353_R1

namespace OMA.Proof_mo_342353_R1_H1

private lemma digit_le_of_not_dvd_choose (p : ℕ) [Fact p.Prime] :
    ∀ (i a b : ℕ), ¬ p ∣ Nat.choose a b → b / p ^ i % p ≤ a / p ^ i % p := by
  intro i
  induction i with
  | zero =>
    intro a b hnd
    simp only [pow_zero, Nat.div_one]
    have hluc := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p) (n := a) (k := b)
    by_contra hgt
    have hzero : Nat.choose (a % p) (b % p) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [hzero, zero_mul] at hluc
    exact hnd (Nat.modEq_zero_iff_dvd.mp hluc)
  | succ i ih =>
    intro a b hnd
    have hluc := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p) (n := a) (k := b)
    have hnd_div : ¬ p ∣ Nat.choose (a / p) (b / p) := by
      intro hd
      have h0 : Nat.choose (a % p) (b % p) * Nat.choose (a / p) (b / p) ≡ 0 [MOD p] :=
        Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_right hd _)
      exact hnd (Nat.modEq_zero_iff_dvd.mp (hluc.trans h0))
    have hrec := ih (a / p) (b / p) hnd_div
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, ← pow_succ'] at hrec
    exact hrec

end OMA.Proof_mo_342353_R1_H1

theorem OMA.solution : OMA.R_mo_342353_R1.H1 := by
  intro n hn1 hodd hcong p hp hpn i
  open OMA.Proof_mo_342353_R1_H1 in
  have : Fact p.Prime := ⟨hp⟩
  have hnd : ¬ p ∣ Nat.choose (n - 1) ((n - 1) / 2) := by
    intro hdvd
    have hp_dvd_n3 : (p : ℤ) ∣ (n : ℤ) ^ 3 :=
      (Int.natCast_dvd_natCast.mpr hpn).trans (dvd_pow_self (n : ℤ) (by decide))
    have hmod_p : ((Nat.choose (n - 1) ((n - 1) / 2) : ℤ) ≡
        (-1) ^ ((n - 1) / 2) * 4 ^ (n - 1) [ZMOD (p : ℤ)]) :=
      hcong.of_dvd hp_dvd_n3
    have hc0 : ((Nat.choose (n - 1) ((n - 1) / 2) : ℤ) ≡ 0 [ZMOD (p : ℤ)]) :=
      Int.modEq_zero_iff_dvd.mpr (Int.natCast_dvd_natCast.mpr hdvd)
    have hrhs0 : (p : ℤ) ∣ (-1 : ℤ) ^ ((n - 1) / 2) * 4 ^ (n - 1) :=
      Int.modEq_zero_iff_dvd.mp (hmod_p.symm.trans hc0)
    have hp_dvd_4pow : (p : ℤ) ∣ (4 : ℤ) ^ (n - 1) := by
      rcases neg_one_pow_eq_or ℤ ((n - 1) / 2) with h1 | hm1
      · simpa [h1] using hrhs0
      · rw [hm1, neg_one_mul] at hrhs0
        exact dvd_neg.mp hrhs0
    have hp_nat : p ∣ 4 ^ (n - 1) := by
      have : ((p : ℕ) : ℤ) ∣ ((4 ^ (n - 1) : ℕ) : ℤ) := by simpa using hp_dvd_4pow
      exact Int.natCast_dvd_natCast.mp this
    have hp4 : p ∣ 4 := hp.dvd_of_dvd_pow hp_nat
    have hp2 : p = 2 := by
      have : p ∣ 2 ^ 2 := by simpa using hp4
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow this)
    subst hp2
    exact hodd.not_two_dvd_nat hpn
  exact digit_le_of_not_dvd_choose p i (n - 1) ((n - 1) / 2) hnd
