import OMAStatements.S_oeis_a242076

-- Proof of the statement in #26225 (statement by @dwilfand-sys). Credit for the proof: @bnb9001
-- For k = 4t+2, 5 | 2^k+1 forces the Fermat factor to be 5 (j = 1); then the Aurifeuillean
-- factorization 4x^4+1 = (2x^2-2x+1)(2x^2+2x+1), x = 2^t, makes (2^k+1)/5 composite for t >= 2,
-- and t = 0 gives q = 1; so k = 6 (65 = 5 * 13).

namespace OMA_OEIS_A242076_Proof

open OMA.S_oeis_a242076

theorem pow16_mod5 (t : ℕ) : 16 ^ t % 5 = 1 := by
  rw [Nat.pow_mod]; norm_num

/-- 5 divides `2^(2^j) + 1` only for `j = 1` -/
theorem five_dvd_fermat (j : ℕ) (h : 5 ∣ 2 ^ (2 ^ j) + 1) : j = 1 := by
  rcases (show j = 0 ∨ j = 1 ∨ 2 ≤ j by omega) with h0 | h1 | h2
  · subst h0; norm_num at h
  · exact h1
  · exfalso
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
    have e : 2 ^ (2 ^ (i + 2)) = 16 ^ (2 ^ i) := by
      rw [show 2 ^ (i + 2) = 4 * 2 ^ i by ring, pow_mul]; norm_num
    rw [e] at h
    have := pow16_mod5 (2 ^ i)
    omega

theorem aurif (x : ℕ) (hx : 1 ≤ x) :
    4 * x ^ 4 + 1 = (2 * x * (x - 1) + 1) * (2 * x * (x + 1) + 1) := by
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
  rw [Nat.add_sub_cancel]; ring

theorem stmt' : ∀ k : ℕ, (isTerm k ∧ 2 ∣ k ∧ ¬ 4 ∣ k) ↔ k = 6 := by
  intro k
  constructor
  · rintro ⟨⟨j, q, hq, he⟩, h2, h4⟩
    obtain ⟨t, rfl⟩ : ∃ t, k = 4 * t + 2 := ⟨k / 4, by omega⟩
    set x := 2 ^ t with hx
    have hx1 : 1 ≤ x := Nat.one_le_two_pow
    have hk : 2 ^ (4 * t + 2) = 4 * x ^ 4 := by
      rw [hx, pow_add, mul_comm 4 t, pow_mul, ← pow_mul, mul_comm t 4, pow_mul]; norm_num; ring
    rw [hk] at he
    have hx4 : x ^ 4 = 16 ^ t := by rw [hx, ← pow_mul, mul_comm, pow_mul]; norm_num
    -- the Fermat factor is 5
    have h5 : 5 ∣ (2 ^ (2 ^ j) + 1) * q := by
      rw [← he, Nat.dvd_iff_mod_eq_zero, hx4]
      have := pow16_mod5 t
      omega
    have hj : j = 1 := by
      rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 5)).mp h5 with hF | hQ
      · exact five_dvd_fermat j hF
      · exfalso
        have hq5 : q = 5 := ((Nat.prime_dvd_prime_iff_eq (by norm_num) hq).mp hQ).symm
        subst hq5
        rw [hx4] at he
        rcases (show j = 0 ∨ 1 ≤ j by omega) with hj0 | hj1
        · subst hj0; norm_num at he; omega
        · obtain ⟨w, hw⟩ : ∃ w, 2 ^ (2 ^ j) = 4 * w := by
            refine ⟨2 ^ (2 ^ j - 2), ?_⟩
            have : 2 ≤ 2 ^ j := by
              calc 2 = 2 ^ 1 := by norm_num
                _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj1
            rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
          rw [hw] at he
          have hw1 : 1 ≤ w := by
            rcases Nat.eq_zero_or_pos w with h | h
            · rw [h] at hw; have := Nat.two_pow_pos (2 ^ j); omega
            · exact h
          rcases (show t = 0 ∨ 1 ≤ t by omega) with ht | ht
          · subst ht; norm_num at he; omega
          · -- 16^t = 5w + 1 is even, so w is odd, so w = 1
            have hev : 16 ^ t % 2 = 0 := by
              obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
              rw [pow_succ]; omega
            have hwodd : w % 2 = 1 := by omega
            have hw' : w = 1 := by
              by_contra hne
              have : 2 ∣ w := by
                have h2w : 2 ^ (2 ^ j) = 2 ^ 2 * w := by rw [hw]; norm_num
                have hjj : 2 ^ j ≠ 2 := by
                  intro heq
                  rw [heq] at h2w
                  omega
                have : 3 ≤ 2 ^ j := by
                  have : 2 ≤ 2 ^ j := by
                    calc 2 = 2 ^ 1 := by norm_num
                      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj1
                  omega
                refine ⟨2 ^ (2 ^ j - 3), ?_⟩
                have e3 : 2 ^ (2 ^ j) = 2 ^ 3 * 2 ^ (2 ^ j - 3) := by
                  rw [← pow_add]; congr 1; omega
                omega
              omega
            subst hw'
            have : 16 ≤ 16 ^ t := by
              calc 16 = 16 ^ 1 := by norm_num
                _ ≤ 16 ^ t := Nat.pow_le_pow_right (by norm_num) ht
            omega
    subst hj
    norm_num at he
    -- 4 x^4 + 1 = 5 q with the Aurifeuillean factorization
    rw [aurif x hx1] at he
    set A := 2 * x * (x - 1) + 1
    set B := 2 * x * (x + 1) + 1
    rcases (show t = 0 ∨ t = 1 ∨ 2 ≤ t by omega) with ht | ht | ht
    · subst ht
      simp [hx, A, B] at he
      rw [he] at hq; exact absurd hq Nat.not_prime_one
    · subst ht; rfl
    · exfalso
      have hx4' : 4 ≤ x := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) ht
      have hA : 25 ≤ A := by
        have : 2 * 4 * 3 ≤ 2 * x * (x - 1) := Nat.mul_le_mul (by omega) (by omega)
        omega
      have hB : 25 ≤ B := by
        have : 2 * 4 * 5 ≤ 2 * x * (x + 1) := Nat.mul_le_mul (by omega) (by omega)
        omega
      have hdvd : q ∣ A * B := ⟨5, by rw [he]; ring⟩
      rcases (Nat.Prime.dvd_mul hq).mp hdvd with ⟨c, hc⟩ | ⟨c, hc⟩
      · rw [hc] at he
        have : 5 = c * B := by
          apply Nat.eq_of_mul_eq_mul_left hq.pos
          rw [← mul_assoc, he]; ring
        have : B ≤ 5 := by
          rcases Nat.eq_zero_or_pos c with h | h
          · rw [h] at this; omega
          · nlinarith
        omega
      · rw [hc] at he
        have : 5 = A * c := by
          apply Nat.eq_of_mul_eq_mul_left hq.pos
          rw [show q * (A * c) = A * (q * c) by ring, he]; ring
        have : A ≤ 5 := by
          rcases Nat.eq_zero_or_pos c with h | h
          · rw [h] at this; omega
          · nlinarith
        omega
  · rintro rfl
    exact ⟨⟨1, 13, by norm_num, by norm_num⟩, by norm_num, by norm_num⟩

end OMA_OEIS_A242076_Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a242076.main := OMA_OEIS_A242076_Proof.stmt'
