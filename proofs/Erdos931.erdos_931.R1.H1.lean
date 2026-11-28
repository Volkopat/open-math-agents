import OMAReductions.R_Erdos931_erdos_931_R1
import Mathlib

-- Step Erdos931.erdos_931.R1.H1: hypothesis H1 of reduction Erdos931.erdos_931.R1
-- Credit: @ivillar
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! Let `P` be the common prime set, `|P| ≤ 3`. Every prime of the first block is at most its end,
which is at most `n₂`; so no member of the second block is prime. Both `2` and `3` lie in `P`,
hence at most one prime `q ≥ 5` does, and it divides at most one of `n₂+1, n₂+2, n₂+3`. Two of
these are therefore `{2,3}`-smooth, at distance `1` or `2`. Writing smooth numbers as `2^a 3^b`,
the congruences of `3^d` modulo `80` show that consecutive `{2,3}`-smooth numbers are at most
`8, 9`, so `n₂ ≤ 15`. The composite triples below `18` leave `n₂ = 7` (block `8, 9, 10`) or
`n₂ = 13` (which needs both `5` and `7`). Then `k₂ = 3` since `11` is prime, the first block must
contain `5` and must not contain `7`, so it ends at `5` or `6`. The converse is a computation. -/

open Finset

namespace P4E931

def S23 (y : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ y → p = 2 ∨ p = 3

theorem s23_form (y : ℕ) (hy : 0 < y) (h : S23 y) : ∃ a b : ℕ, y = 2 ^ a * 3 ^ b := by
  induction y using Nat.strong_induction_on with
  | h y ih =>
    by_cases h1 : y = 1
    · exact ⟨0, 0, by simp [h1]⟩
    · have hp := Nat.minFac_prime h1
      obtain ⟨m, hm⟩ := Nat.minFac_dvd y
      have hm0 : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · rw [h0, mul_zero] at hm; omega
        · exact h0
      have hmlt : m < y := by
        have h2 := hp.two_le
        have : 2 * m ≤ y.minFac * m := Nat.mul_le_mul_right m h2
        omega
      have hms : S23 m := fun p hpp hpd => h p hpp (hm ▸ Dvd.dvd.mul_left hpd _)
      obtain ⟨a, b, hab⟩ := ih m hmlt hm0 hms
      rcases h _ hp (Nat.minFac_dvd y) with h2 | h3
      · exact ⟨a + 1, b, by rw [hm, h2, hab]; ring⟩
      · exact ⟨a, b + 1, by rw [hm, h3, hab]; ring⟩

theorem pow3_mod80 (d : ℕ) : (3 ^ d % 80 = 1 ∧ d % 4 = 0) ∨ (3 ^ d % 80 = 3 ∧ d % 4 = 1) ∨
    (3 ^ d % 80 = 9 ∧ d % 4 = 2) ∨ (3 ^ d % 80 = 27 ∧ d % 4 = 3) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ, Nat.mul_mod]
    rcases ih with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1] <;> omega

theorem pow2_mod5 (a : ℕ) : 2 ^ a % 5 ≠ 0 := by
  intro h
  have h5 : 5 ∣ 2 ^ a := Nat.dvd_of_mod_eq_zero h
  have := (Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).mp
    ((Nat.Prime.dvd_of_dvd_pow (by norm_num) h5))
  omega

theorem consec (x : ℕ) (hx : 0 < x) (h1 : S23 x) (h2 : S23 (x + 1)) : x ≤ 8 := by
  obtain ⟨a, b, ha⟩ := s23_form x hx h1
  obtain ⟨c, d, hc⟩ := s23_form (x + 1) (by omega) h2
  rcases Nat.eq_zero_or_pos a with ha0 | ha0
  · -- x = 3^b
    rw [ha0, pow_zero, one_mul] at ha
    rcases Nat.eq_zero_or_pos b with hb0 | hb0
    · rw [hb0] at ha; omega
    · have hd0 : d = 0 := by
        by_contra hd
        have h3x : 3 ∣ x := by rw [ha]; exact dvd_pow_self 3 (by omega)
        have h3x1 : 3 ∣ x + 1 := by rw [hc]; exact Dvd.dvd.mul_left (dvd_pow_self 3 hd) _
        omega
      rw [hd0, pow_zero, mul_one] at hc
      have hc2 : c ≤ 2 := by
        by_contra hc3
        have h8 : 8 ∣ x + 1 := by
          rw [hc]; exact (Nat.pow_dvd_pow 2 (show 3 ≤ c by omega))
        have := pow3_mod80 b
        rw [← ha] at this
        omega
      have : x + 1 ≤ 4 := by
        rw [hc]; calc 2 ^ c ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hc2
          _ = 4 := by norm_num
      omega
  · -- x even, so c = 0
    have hc0 : c = 0 := by
      by_contra hc'
      have h2x : 2 ∣ x := by rw [ha]; exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
      have h2x1 : 2 ∣ x + 1 := by rw [hc]; exact Dvd.dvd.mul_right (dvd_pow_self 2 hc') _
      omega
    rw [hc0, pow_zero, one_mul] at hc
    have hb0 : b = 0 := by
      by_contra hb
      have h3x : 3 ∣ x := by rw [ha]; exact Dvd.dvd.mul_left (dvd_pow_self 3 hb) _
      have hd : d ≠ 0 := by
        intro hd; rw [hd, pow_zero] at hc; omega
      have h3x1 : 3 ∣ x + 1 := by rw [hc]; exact dvd_pow_self 3 hd
      omega
    rw [hb0, pow_zero, mul_one] at ha
    have ha3 : a ≤ 3 := by
      by_contra ha4
      have h16 : 16 ∣ x := by rw [ha]; exact Nat.pow_dvd_pow 2 (show 4 ≤ a by omega)
      have h5 := pow2_mod5 a
      have := pow3_mod80 d
      rw [← hc] at this
      rw [← ha] at h5
      omega
    rw [ha]
    calc 2 ^ a ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) ha3
      _ = 8 := by norm_num

theorem gap2 (x : ℕ) (hx : 0 < x) (h1 : S23 x) (h2 : S23 (x + 2)) : x ≤ 16 := by
  rcases Nat.even_or_odd x with ⟨y, hy⟩ | hodd
  · have hy0 : 0 < y := by omega
    have hsy : S23 y := fun p hp hpd => h1 p hp (by rw [hy]; exact Dvd.dvd.mul_left hpd _ |>.trans (by rw [← two_mul]))
    have hsy1 : S23 (y + 1) := fun p hp hpd => h2 p hp (by
      have : x + 2 = 2 * (y + 1) := by omega
      rw [this]; exact Dvd.dvd.mul_left hpd _)
    have := consec y hy0 hsy hsy1
    omega
  · obtain ⟨a, b, ha⟩ := s23_form x hx h1
    have ha0 : a = 0 := by
      by_contra ha'
      have : 2 ∣ x := by rw [ha]; exact Dvd.dvd.mul_right (dvd_pow_self 2 ha') _
      obtain ⟨k, hk⟩ := hodd
      omega
    rw [ha0, pow_zero, one_mul] at ha
    rcases Nat.eq_zero_or_pos b with hb0 | hb0
    · rw [hb0] at ha; omega
    · exfalso
      obtain ⟨c, d, hc⟩ := s23_form (x + 2) (by omega) h2
      have h3x : 3 ∣ x := by rw [ha]; exact dvd_pow_self 3 (by omega)
      have hc0 : c = 0 := by
        by_contra hc'
        have : 2 ∣ x + 2 := by rw [hc]; exact Dvd.dvd.mul_right (dvd_pow_self 2 hc') _
        obtain ⟨k, hk⟩ := hodd
        omega
      rw [hc0, pow_zero, one_mul] at hc
      have hd : d ≠ 0 := by intro hd; rw [hd, pow_zero] at hc; omega
      have : 3 ∣ x + 2 := by rw [hc]; exact dvd_pow_self 3 hd
      omega

end P4E931

open P4E931 in
theorem OMA.solution : OMA.R_Erdos931_erdos_931_R1.H1 := by
  intro k₁ k₂ n₁ n₂ hk₂ hk₁ hsep
  have hB1 : (∏ i ∈ Icc 1 k₁, (n₁ + i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i hi => by have := (mem_Icc.mp hi).1; omega)
  have hB2 : (∏ j ∈ Icc 1 k₂, (n₂ + j)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j hj => by have := (mem_Icc.mp hj).1; omega)
  have mem1 : ∀ i, 1 ≤ i → i ≤ k₁ → ∀ p, p.Prime → p ∣ n₁ + i →
      p ∈ (∏ i ∈ Icc 1 k₁, (n₁ + i)).primeFactors := by
    intro i hi1 hi2 p hp hpd
    exact Nat.mem_primeFactors.mpr
      ⟨hp, hpd.trans (Finset.dvd_prod_of_mem _ (mem_Icc.mpr ⟨hi1, hi2⟩)), hB1⟩
  have mem2 : ∀ j, 1 ≤ j → j ≤ k₂ → ∀ p, p.Prime → p ∣ n₂ + j →
      p ∈ (∏ j ∈ Icc 1 k₂, (n₂ + j)).primeFactors := by
    intro j hj1 hj2 p hp hpd
    exact Nat.mem_primeFactors.mpr
      ⟨hp, hpd.trans (Finset.dvd_prod_of_mem _ (mem_Icc.mpr ⟨hj1, hj2⟩)), hB2⟩
  have fac1 : ∀ p ∈ (∏ i ∈ Icc 1 k₁, (n₁ + i)).primeFactors,
      ∃ i, 1 ≤ i ∧ i ≤ k₁ ∧ p ∣ n₁ + i := by
    intro p hp
    obtain ⟨hpp, hpd, -⟩ := Nat.mem_primeFactors.mp hp
    obtain ⟨i, hi, hpi⟩ := (Prime.dvd_finsetProd_iff hpp.prime _).mp hpd
    exact ⟨i, (mem_Icc.mp hi).1, (mem_Icc.mp hi).2, hpi⟩
  have fac2 : ∀ p ∈ (∏ j ∈ Icc 1 k₂, (n₂ + j)).primeFactors,
      ∃ j, 1 ≤ j ∧ j ≤ k₂ ∧ p ∣ n₂ + j := by
    intro p hp
    obtain ⟨hpp, hpd, -⟩ := Nat.mem_primeFactors.mp hp
    obtain ⟨j, hj, hpj⟩ := (Prime.dvd_finsetProd_iff hpp.prime _).mp hpd
    exact ⟨j, (mem_Icc.mp hj).1, (mem_Icc.mp hj).2, hpj⟩
  constructor
  · rintro ⟨heq, hcard⟩
    have small : ∀ p ∈ (∏ j ∈ Icc 1 k₂, (n₂ + j)).primeFactors, p ≤ n₁ + k₁ := by
      intro p hp
      rw [← heq] at hp
      obtain ⟨i, hi1, hi2, hpi⟩ := fac1 p hp
      have := Nat.le_of_dvd (by omega) hpi
      omega
    have hother : ∀ p ∈ (∏ j ∈ Icc 1 k₂, (n₂ + j)).primeFactors,
        ∀ q ∈ (∏ j ∈ Icc 1 k₂, (n₂ + j)).primeFactors,
        p ≠ 2 → p ≠ 3 → q ≠ 2 → q ≠ 3 → p = q := by
      intro p hp q hq hp2 hp3 hq2 hq3
      by_contra hpq
      have h2P : 2 ∈ (∏ j ∈ Icc 1 k₂, (n₂ + j)).primeFactors := by
        rcases Nat.even_or_odd n₂ with ⟨m, hm⟩ | ⟨m, hm⟩
        · exact mem2 2 (by omega) (by omega) 2 Nat.prime_two ⟨m + 1, by omega⟩
        · exact mem2 1 (by omega) (by omega) 2 Nat.prime_two ⟨m + 1, by omega⟩
      have h3P : 3 ∈ (∏ j ∈ Icc 1 k₂, (n₂ + j)).primeFactors := by
        rcases (show n₂ % 3 = 0 ∨ n₂ % 3 = 1 ∨ n₂ % 3 = 2 by omega) with h | h | h
        · exact mem2 3 (by omega) (by omega) 3 Nat.prime_three (by omega)
        · exact mem2 2 (by omega) (by omega) 3 Nat.prime_three (by omega)
        · exact mem2 1 (by omega) (by omega) 3 Nat.prime_three (by omega)
      have hsub : ({2, 3, p, q} : Finset ℕ) ⊆ (∏ j ∈ Icc 1 k₂, (n₂ + j)).primeFactors := by
        intro r hr
        simp only [Finset.mem_insert, Finset.mem_singleton] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> assumption
      have h4 : ({2, 3, p, q} : Finset ℕ).card = 4 := by
        rw [Finset.card_eq_four]
        exact ⟨2, 3, p, q, by norm_num, by omega, by omega, by omega, by omega, hpq, rfl⟩
      have := Finset.card_le_card hsub
      omega
    have noprime : ∀ j, 1 ≤ j → j ≤ k₂ → ¬ (n₂ + j).Prime := by
      intro j hj1 hj2 hp
      have := small _ (mem2 j hj1 hj2 _ hp dvd_rfl)
      omega
    have key : ∀ j₁ j₂, 1 ≤ j₁ → j₁ < j₂ → j₂ ≤ 3 → ¬ S23 (n₂ + j₁) → ¬ S23 (n₂ + j₂) →
        False := by
      intro j₁ j₂ h1 h12 h23 hs1 hs2
      simp only [S23, not_forall, not_or] at hs1 hs2
      obtain ⟨p, hp, hpd, hp2, hp3⟩ := hs1
      obtain ⟨q, hq, hqd, hq2, hq3⟩ := hs2
      have hpq := hother p (mem2 j₁ (by omega) (by omega) p hp hpd) q
        (mem2 j₂ (by omega) (by omega) q hq hqd) hp2 hp3 hq2 hq3
      subst hpq
      have hdiff : p ∣ (n₂ + j₂) - (n₂ + j₁) := Nat.dvd_sub hqd hpd
      rw [show (n₂ + j₂) - (n₂ + j₁) = j₂ - j₁ by omega] at hdiff
      have := Nat.le_of_dvd (by omega) hdiff
      have := hp.two_le
      omega
    have hn₂ : n₂ ≤ 15 := by
      by_cases s1 : S23 (n₂ + 1)
      · by_cases s2 : S23 (n₂ + 2)
        · have := consec (n₂ + 1) (by omega) s1
            (by rw [show n₂ + 1 + 1 = n₂ + 2 by omega]; exact s2)
          omega
        · have s3 : S23 (n₂ + 3) := by
            by_contra s3; exact key 2 3 (by omega) (by omega) (by omega) s2 s3
          have := gap2 (n₂ + 1) (by omega) s1
            (by rw [show n₂ + 1 + 2 = n₂ + 3 by omega]; exact s3)
          omega
      · have s2 : S23 (n₂ + 2) := by
          by_contra s2; exact key 1 2 (by omega) (by omega) (by omega) s1 s2
        have s3 : S23 (n₂ + 3) := by
          by_contra s3; exact key 1 3 (by omega) (by omega) (by omega) s1 s3
        have := consec (n₂ + 2) (by omega) s2
          (by rw [show n₂ + 2 + 1 = n₂ + 3 by omega]; exact s3)
        omega
    have np1 := noprime 1 (by omega) (by omega)
    have np2 := noprime 2 (by omega) (by omega)
    have np3 := noprime 3 (by omega) (by omega)
    have h13 : n₂ ≠ 13 := by
      intro h
      subst h
      have h5 := mem2 2 (by omega) (by omega) 5 (by norm_num) (by norm_num)
      have h7 := mem2 1 (by omega) (by omega) 7 (by norm_num) (by norm_num)
      have := hother 5 h5 7 h7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      omega
    have h7 : n₂ = 7 := by
      have hn3 : 3 ≤ n₂ := by omega
      interval_cases n₂ <;> first
        | rfl
        | (norm_num at np1; done)
        | (norm_num at np2; done)
        | (norm_num at np3; done)
        | exact absurd rfl h13
    subst h7
    have hk : k₂ = 3 := by
      by_contra h
      have := noprime 4 (by omega) (by omega)
      norm_num at this
    subst hk
    have h5 := small 5 (mem2 3 (by omega) (by omega) 5 (by norm_num) (by norm_num))
    have hE7 : n₁ + k₁ ≠ 7 := by
      intro hE
      have h7 := mem1 k₁ (by omega) le_rfl 7 (by norm_num) (by rw [hE])
      rw [heq] at h7
      obtain ⟨j, hj1, hj2, hj⟩ := fac2 7 h7
      omega
    exact ⟨rfl, rfl, by omega⟩
  · rintro ⟨rfl, rfl, hE⟩
    have h720 : ∏ j ∈ Icc 1 3, (7 + j) = 720 := by decide
    have hpf : Nat.primeFactors 720 = {2, 3, 5} := by
      rw [← Nat.toFinset_factors]; simp [Nat.primeFactorsList_ofNat]
    rw [h720, hpf]
    refine ⟨?_, by decide⟩
    have : n₁ ≤ 3 := by omega
    have : k₁ ≤ 6 := by omega
    interval_cases n₁ <;> interval_cases k₁ <;> (try omega) <;>
      (rw [← Nat.toFinset_factors]; simp [Finset.prod_Icc_succ_top, Nat.primeFactorsList_ofNat])
