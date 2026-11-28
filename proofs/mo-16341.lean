import OMAStatements.S_mo_16341

namespace OMA.Divisibility16341

private theorem prime_factor_three (s : ℕ) (hs : s % 4 = 3) :
    ∃ p : ℕ, p.Prime ∧ p ∣ s ∧ p % 4 = 3 := by
  induction s using Nat.strong_induction_on with
  | h s ih =>
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (show s ≠ 1 by omega)
      by_cases hr : p % 4 = 3
      · exact ⟨p, hp, hpd, hr⟩
      obtain ⟨q, hq⟩ := hpd
      have hm := congrArg (fun x : ℕ => x % 4) hq
      rw [hs, Nat.mul_mod p q 4] at hm
      have hb := Nat.mod_lt p (show 0 < 4 by decide)
      have he : p % 4 = 1 := by
        rcases (show p%4 = 0 ∨ p%4 = 1 ∨ p%4 = 2 by omega) with h0 | h1 | h2
        · rw [h0] at hm
          omega
        · exact h1
        · rw [h2] at hm
          omega
      rw [he, one_mul] at hm
      have hqr : q % 4 = 3 := by omega
      have hq2 : 2*q ≤ p*q := Nat.mul_le_mul_right _ hp.two_le
      have hlt : q < s := by omega
      obtain ⟨r, hprime, hrd, hr4⟩ := ih q hlt hqr
      refine ⟨r, hprime, ?_, hr4⟩
      rw [hq]
      exact hrd.trans (dvd_mul_left _ _)

private theorem left_factor {m : ℕ} (hm : 1 ≤ m) : ((m-1 : ℕ) : ℤ) ∣ (m : ℤ)^2 - 1 := by
  refine ⟨(m : ℤ) + 1, ?_⟩
  rw [Int.natCast_sub hm]
  push_cast
  ring

private theorem right_factor (m : ℕ) : ((m+1 : ℕ) : ℤ) ∣ (m : ℤ)^2 - 1 := by
  refine ⟨(m : ℤ) - 1, ?_⟩
  push_cast
  ring

private theorem mod_eight_denominator (m : ℕ) (hm : m % 2 = 1) :
    (8 : ℤ) ∣ (m : ℤ)^2 - 1 := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp
  push_cast
  rw [← ZMod.natCast_mod m 8]
  have hc : m%8 = 1 ∨ m%8 = 3 ∨ m%8 = 5 ∨ m%8 = 7 := by omega
  rcases hc with hc | hc | hc | hc <;> rw [hc] <;> decide

private theorem odd_impossible {m n : ℕ} (hm : 3 ≤ m) (hn : 0 < n) (ho : m % 2 = 1)
    (hd : (m : ℤ)^2 - 1 ∣ (3 : ℤ)^m + ((n.factorial : ℤ)-2)^m) : False := by
  have he := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mpr
    ((mod_eight_denominator m ho).trans hd)
  push_cast at he
  have hmexp : m = 2*(m/2)+1 := by omega
  have hthree : (3 : ZMod 8)^m = 3 := by
    conv_lhs => rw [hmexp]
    rw [pow_add, pow_mul, show (3 : ZMod 8)^2 = 1 by decide, one_pow, one_mul, pow_one]
  rw [hthree] at he
  by_cases h1 : n = 1
  · subst n
    have hbase : (Nat.factorial 1 : ZMod 8) - 2 = -1 := by decide
    have hpow : (-1 : ZMod 8)^m = -1 := by
      conv_lhs => rw [hmexp]
      rw [pow_add, pow_mul, show (-1 : ZMod 8)^2 = 1 by decide, one_pow, one_mul, pow_one]
    rw [hbase, hpow] at he
    exact (by decide : (3 : ZMod 8) + (-1) ≠ 0) he
  have hc : ((n.factorial : ZMod 8)-2)^3 = 0 := by
    by_cases h2 : n = 2
    · subst n
      decide
    by_cases h3 : n = 3
    · subst n
      decide
    have hf : 8 ∣ n.factorial :=
      (show 8 ∣ Nat.factorial 4 by decide).trans (Nat.factorial_dvd_factorial (by omega))
    rw [(ZMod.natCast_eq_zero_iff _ _).mpr hf]
    decide
  have hz := pow_eq_zero_of_le hm hc
  rw [hz, add_zero] at he
  exact (by decide : (3 : ZMod 8) ≠ 0) he

private theorem three_dvd_factorial_sub_two {m n : ℕ} (hm : 0 < m) (h : m % 2 = 0)
    (hd : (m : ℤ)^2 - 1 ∣ (3 : ℤ)^m + ((n.factorial : ℤ)-2)^m) :
    (3 : ℤ) ∣ (n.factorial : ℤ) - 2 := by
  have hex : ∃ s : ℕ, s % 4 = 3 ∧ (s : ℤ) ∣ (m : ℤ)^2-1 := by
    by_cases h4 : m % 4 = 0
    · exact ⟨m-1, by omega, left_factor (by omega)⟩
    · exact ⟨m+1, by omega, right_factor m⟩
  obtain ⟨s, hs, hsd⟩ := hex
  obtain ⟨p, hp, hdiv, hp4⟩ := prime_factor_three s hs
  let _ : Fact p.Prime := ⟨hp⟩
  have hdvd : (p : ℤ) ∣ (3 : ℤ)^m + ((n.factorial : ℤ)-2)^m := by
    have hc : (p : ℤ) ∣ (s : ℤ) := by exact_mod_cast hdiv
    exact (hc.trans hsd).trans hd
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdvd
  push_cast at hz
  have hbase : (3 : ZMod p) = 0 := by
    by_contra h0
    have hsquare : ((3 : ZMod p)^(m/2))^2 = -(((n.factorial : ZMod p)-2)^(m/2))^2 := by
      rw [← pow_mul, ← pow_mul, show m/2*2 = m by omega]
      linear_combination hz
    exact ZMod.mod_four_ne_three_of_sq_eq_neg_sq (pow_ne_zero _ h0) hsquare hp4
  have hprime : p = 3 :=
    (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
      ((ZMod.natCast_eq_zero_iff 3 p).mp hbase)
  have htwo : ((n.factorial : ZMod p)-2)^m = 0 := by
    simpa only [hbase, zero_pow hm.ne', zero_add] using hz
  have hzero : (n.factorial : ZMod p) - 2 = 0 := eq_zero_of_pow_eq_zero htwo
  have hd' := (ZMod.intCast_zmod_eq_zero_iff_dvd ((n.factorial : ℤ)-2) p).mp (by
    push_cast
    exact hzero)
  simpa [hprime] using hd'

private theorem factorial_index {n : ℕ} (hn : 0 < n)
    (hd : (3 : ℤ) ∣ (n.factorial : ℤ) - 2) : n = 2 := by
  have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr hd
  push_cast at h
  have he := sub_eq_zero.mp h
  have hlt : n < 3 := by
    by_contra! hl
    have hz : (n.factorial : ZMod 3) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr
      (Nat.dvd_factorial (by decide) hl)
    rw [hz] at he
    exact (by decide : (0 : ZMod 3) ≠ 2) he
  have hn1 : n ≠ 1 := by
    rintro rfl
    exact (by decide : (Nat.factorial 1 : ZMod 3) ≠ 2) he
  omega

private theorem three_dvd_of_dvd_power {k m : ℕ} (hk : k ≠ 1) (hd : k ∣ 3^m) : 3 ∣ k := by
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hk
  have he := Nat.prime_eq_prime_of_dvd_pow hq Nat.prime_three (hqd.trans hd)
  simpa [he] using hqd

theorem classification (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    (((m:ℤ)^2-1 ∣ (3:ℤ)^m+((n.factorial:ℤ)-2)^m) ↔ (m=2 ∧ n=2)) := by
  constructor
  · intro hd
    have hm1 : m ≠ 1 := by
      rintro rfl
      norm_num at hd
      have hp : (0 : ℤ) < (n.factorial : ℤ) := by exact_mod_cast Nat.factorial_pos n
      omega
    by_cases he : m % 2 = 0
    · have htwo : n = 2 := factorial_index hn (three_dvd_factorial_sub_two hm he hd)
      subst n
      have hpower : (m : ℤ)^2 - 1 ∣ (3 : ℤ)^m := by
        simpa [Nat.factorial, zero_pow hm.ne'] using hd
      refine ⟨?_, rfl⟩
      by_contra hneq
      have hL : m-1 ∣ 3^m := by exact_mod_cast (left_factor hm).trans hpower
      have hR : m+1 ∣ 3^m := by exact_mod_cast (right_factor m).trans hpower
      have hL3 := three_dvd_of_dvd_power (by omega) hL
      have hR3 := three_dvd_of_dvd_power (by omega) hR
      omega
    · exact False.elim (odd_impossible (by omega) hn (by omega) hd)
  · rintro ⟨rfl, rfl⟩
    decide

end OMA.Divisibility16341

theorem OMA.solution : type_of% @OMA.S_mo_16341.main := OMA.Divisibility16341.classification