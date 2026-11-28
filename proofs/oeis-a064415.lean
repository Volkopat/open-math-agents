import OMAStatements.S_oeis_a064415
import Mathlib

namespace OMA.P_oeis_a064415

open OMA.S_oeis_a064415

private lemma iterPhi_ge_two (n : ℕ) (hn : 2 ≤ n) :
    iterPhi n = 1 + iterPhi (Nat.totient n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [iterPhi]

private lemma iterPhi_pos (n : ℕ) (hn : 2 ≤ n) : 1 ≤ iterPhi n := by
  rw [iterPhi_ge_two n hn]; omega

private lemma totient_even : ∀ n : ℕ, 3 ≤ n → Nat.totient n % 2 = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases h2 : n % 2 = 0
    · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
      by_cases hm2 : 2 ∣ m
      · rw [Nat.totient_mul_of_prime_of_dvd Nat.prime_two hm2]; omega
      · have hm3 : 3 ≤ m := by omega
        have hcop : Nat.Coprime 2 m := by
          rw [Nat.coprime_two_left]; exact Nat.odd_iff.mpr (by omega)
        rw [Nat.totient_mul hcop, Nat.totient_two, one_mul]
        exact ih m (by omega) hm3
    · let p := n.minFac
      have hp : Nat.Prime p := Nat.minFac_prime (by omega)
      have hpdvd : p ∣ n := Nat.minFac_dvd n
      have hp_odd : p % 2 = 1 := by
        rcases hp.eq_two_or_odd with h | h
        · rw [h] at hpdvd; omega
        · exact h
      obtain ⟨m, hm⟩ := hpdvd
      by_cases hpm : p ∣ m
      · have hm3 : 3 ≤ m := by
          have := Nat.le_of_dvd (by nlinarith) hpm
          have := hp.two_le
          omega
        rw [hm, Nat.totient_mul_of_prime_of_dvd hp hpm, Nat.mul_mod, ih m (by nlinarith [hp.two_le]) hm3]
        simp
      · have hcop : Nat.Coprime p m := hp.coprime_iff_not_dvd.mpr hpm
        rw [hm, Nat.totient_mul hcop, Nat.totient_prime hp, Nat.mul_mod]
        have : (p - 1) % 2 = 0 := by omega
        rw [this]; simp

private lemma a064415_one : a064415 1 = 0 := by
  simp [a064415, iterPhi]

private lemma a064415_two : a064415 2 = 1 := by
  have h : iterPhi 2 = 1 := by
    rw [iterPhi_ge_two 2 (le_refl 2), Nat.totient_two, iterPhi]
  simp [a064415, h]

private lemma a064415_of_odd_ge_three (n : ℕ) (hn : 3 ≤ n) (hodd : n % 2 = 1) :
    a064415 n = a064415 (Nat.totient n) := by
  simp only [a064415, show ¬(n % 2 = 0) by omega, ↓reduceIte, totient_even n hn]
  rw [iterPhi_ge_two n (by omega)]
  omega

private lemma a064415_two_mul : ∀ m : ℕ, 1 ≤ m → a064415 (2 * m) = a064415 m + 1 := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm
    by_cases hm1 : m = 1
    · subst hm1; simp [a064415_one, a064415_two]
    · by_cases hev : m % 2 = 0
      · -- m >= 2 even: phi(2*m) = 2 * phi(m)!
        have hphi : Nat.totient (2 * m) = 2 * Nat.totient m :=
          Nat.totient_mul_of_prime_of_dvd Nat.prime_two (Nat.dvd_of_mod_eq_zero hev)
        have hphim_pos : 1 ≤ Nat.totient m := Nat.totient_pos.mpr (by omega)
        have hphim_lt : Nat.totient m < m := Nat.totient_lt m (by omega)
        have h1 : a064415 (2 * m) = 1 + iterPhi (2 * Nat.totient m) := by
          simp only [a064415, show (2 * m) % 2 = 0 by omega, ↓reduceIte]
          rw [iterPhi_ge_two (2 * m) (by omega), hphi]
        have h2 : a064415 m = 1 + iterPhi (Nat.totient m) := by
          simp only [a064415, hev, ↓reduceIte]
          rw [iterPhi_ge_two m (by omega)]
        have h3 : iterPhi (2 * Nat.totient m) = a064415 (2 * Nat.totient m) := by
          simp [a064415]
        have h4 : a064415 (2 * Nat.totient m) = a064415 (Nat.totient m) + 1 :=
          ih (Nat.totient m) hphim_lt hphim_pos
        have h5 : a064415 (Nat.totient m) = iterPhi (Nat.totient m) := by
          by_cases hm2 : m = 2
          · subst hm2; simp [Nat.totient_two, a064415_one, iterPhi]
          · simp [a064415, totient_even m (by omega)]
        omega
      · -- m >= 3 odd: phi(2*m) = phi(m)!
        have hcop : Nat.Coprime 2 m := by
          rw [Nat.coprime_two_left]; exact Nat.odd_iff.mpr (by omega)
        have hphi : Nat.totient (2 * m) = Nat.totient m := by
          rw [Nat.totient_mul hcop, Nat.totient_two, one_mul]
        have h1 : a064415 (2 * m) = 1 + iterPhi (Nat.totient m) := by
          simp only [a064415, show (2 * m) % 2 = 0 by omega, ↓reduceIte]
          rw [iterPhi_ge_two (2 * m) (by omega), hphi]
        have h2 : a064415 m = iterPhi (Nat.totient m) := by
          simp only [a064415, hev, ↓reduceIte]
          rw [iterPhi_ge_two m (by omega)]
          omega
        omega

private lemma a064415_mul :
    ∀ N : ℕ, ∀ m n : ℕ, m * n = N → 1 ≤ m → 1 ≤ n → a064415 (m * n) = a064415 m + a064415 n := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro m n hmn hm hn
    by_cases hm1 : m = 1
    · subst hm1; simp [a064415_one]
    · by_cases hn1 : n = 1
      · subst hn1; simp [a064415_one]
      · by_cases hm2 : m % 2 = 0
        · obtain ⟨m', hm'⟩ : ∃ m', m = 2 * m' := ⟨m / 2, by omega⟩
          have hm'1 : 1 ≤ m' := by omega
          rw [hm', mul_assoc, a064415_two_mul (m' * n) (by nlinarith), a064415_two_mul m' hm'1]
          have hlt : m' * n < N := by nlinarith
          rw [ih (m' * n) hlt m' n rfl hm'1 hn]
          ring
        · by_cases hn2 : n % 2 = 0
          · obtain ⟨n', hn'⟩ : ∃ n', n = 2 * n' := ⟨n / 2, by omega⟩
            have hn'1 : 1 ≤ n' := by omega
            rw [hn', show m * (2 * n') = 2 * (m * n') by ring,
              a064415_two_mul (m * n') (by nlinarith), a064415_two_mul n' hn'1]
            have hlt : m * n' < N := by nlinarith
            rw [ih (m * n') hlt m n' rfl hm hn'1]
            ring
          · -- Both m >= 3 and n >= 3 are odd! Factor out a prime p dividing n!
            have hn_ge3 : 3 ≤ n := by omega
            have hm_ge3 : 3 ≤ m := by omega
            let p := n.minFac
            have hp_prime : Nat.Prime p := Nat.minFac_prime (by omega)
            have hp_dvd : p ∣ n := Nat.minFac_dvd n
            have hp_ge3 : 3 ≤ p := by
              have hp2 := hp_prime.two_le
              have hp_ne2 : p ≠ 2 := by
                intro h2; rw [h2] at hp_dvd; omega
              omega
            have hp_odd : p % 2 = 1 := by
              rcases hp_prime.eq_two_or_odd with h2 | hodd
              · omega
              · exact hodd
            obtain ⟨n', hn'⟩ := hp_dvd
            have hn'1 : 1 ≤ n' := by
              by_contra h0; push Not at h0
              have : n' = 0 := by omega
              rw [this, mul_zero] at hn'; omega
            -- First prove a(k * p) = a(k) + a(p) for any odd k >= 3 with k * p <= N!
            have hmul_p : ∀ k : ℕ, 3 ≤ k → k % 2 = 1 → k * p ≤ N →
                a064415 (k * p) = a064415 k + a064415 p := by
              intro k hk3 hk_odd hkpN
              have hkp_odd : (k * p) % 2 = 1 := by
                rw [Nat.mul_mod, hk_odd, hp_odd]
              rw [a064415_of_odd_ge_three (k * p) (by nlinarith) hkp_odd]
              have hphik_pos : 1 ≤ Nat.totient k := Nat.totient_pos.mpr (by omega)
              have hphik_lt : Nat.totient k < k := Nat.totient_lt k (by omega)
              by_cases hpk : p ∣ k
              · have hphi : Nat.totient (k * p) = Nat.totient k * p := by
                  rw [mul_comm k p, Nat.totient_mul_of_prime_of_dvd hp_prime hpk, mul_comm p]
                rw [hphi]
                have hlt : Nat.totient k * p < N := by nlinarith
                rw [ih (Nat.totient k * p) hlt (Nat.totient k) p rfl hphik_pos (by omega)]
                rw [← a064415_of_odd_ge_three k hk3 hk_odd]
              · have hcop : Nat.Coprime k p := (hp_prime.coprime_iff_not_dvd.mpr hpk).symm
                have hphi : Nat.totient (k * p) = Nat.totient k * (p - 1) := by
                  rw [Nat.totient_mul hcop, Nat.totient_prime hp_prime]
                rw [hphi]
                have hp1_lt : p - 1 < p := by omega
                have hlt : Nat.totient k * (p - 1) < N := by nlinarith
                rw [ih (Nat.totient k * (p - 1)) hlt (Nat.totient k) (p - 1) rfl hphik_pos (by omega)]
                rw [← a064415_of_odd_ge_three k hk3 hk_odd]
                have hap : a064415 p = a064415 (p - 1) := by
                  rw [a064415_of_odd_ge_three p hp_ge3 hp_odd, Nat.totient_prime hp_prime]
                rw [hap]
            by_cases hn'1_eq : n' = 1
            · -- n = p!
              have hnp : n = p := by rw [hn', hn'1_eq, mul_one]
              rw [hnp]
              exact hmul_p m hm_ge3 (by omega) (by rw [← hnp]; exact le_of_eq hmn)
            · -- n = p * n' with n' >= 3 odd!
              have hn'_odd : n' % 2 = 1 := by
                by_contra h
                have : 2 ∣ n' := Nat.dvd_of_mod_eq_zero (by omega)
                have : 2 ∣ n := dvd_trans this ⟨p, by rw [hn', mul_comm]⟩
                omega
              have hmn'_lt : m * n' < N := by nlinarith
              have hpn'_lt : p * n' < N := by nlinarith
              have hmn'_odd : (m * n') % 2 = 1 := by
                rw [Nat.mul_mod, show m % 2 = 1 by omega, hn'_odd]
              rw [hn', show m * (p * n') = (m * n') * p by ring,
                hmul_p (m * n') (by nlinarith) hmn'_odd (by nlinarith),
                ih (m * n') hmn'_lt m n' rfl hm hn'1,
                mul_comm p n', hmul_p n' (by omega) hn'_odd (by nlinarith)]
              ring

private theorem main_proved :
    (a064415 1 = 0 ∧ a064415 2 = 1) ∧
    (∀ m n : ℕ, 1 ≤ m → 1 ≤ n → a064415 (m * n) = a064415 m + a064415 n) ∧
    (∀ p : ℕ, Nat.Prime p → 3 ≤ p → a064415 p = 1 + a064415 ((p - 1) / 2)) ∧
    (∀ k : ℕ, a064415 (2 ^ k) = k ∧ a064415 (3 ^ k) = k) := by
  have hmul : ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → a064415 (m * n) = a064415 m + a064415 n :=
    fun m n hm hn => a064415_mul (m * n) m n rfl hm hn
  refine ⟨⟨a064415_one, a064415_two⟩, hmul, ?_, ?_⟩
  · intro p hp hp3
    have hp_odd : p % 2 = 1 := by
      rcases hp.eq_two_or_odd with h2 | hodd <;> omega
    rw [a064415_of_odd_ge_three p hp3 hp_odd, Nat.totient_prime hp]
    have h2 : p - 1 = 2 * ((p - 1) / 2) := by omega
    conv_lhs => rw [h2]
    rw [a064415_two_mul ((p - 1) / 2) (by omega), add_comm]
  · intro k
    have ha3 : a064415 3 = 1 := by
      rw [a064415_of_odd_ge_three 3 (le_refl 3) (by decide), Nat.totient_prime Nat.prime_three]
      simpa using a064415_two
    induction k with
    | zero => simp [a064415_one]
    | succ k ih =>
      constructor
      · rw [pow_succ, hmul (2 ^ k) 2 (Nat.one_le_two_pow) (by omega), ih.1, a064415_two]
      · rw [pow_succ, hmul (3 ^ k) 3 (Nat.one_le_iff_ne_zero.mpr (by positivity)) (by omega), ih.2, ha3]

end OMA.P_oeis_a064415

theorem OMA.solution : type_of% @OMA.S_oeis_a064415.main :=
  OMA.P_oeis_a064415.main_proved
