import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H1_R1

/-! Reduction of Erdos1052 step H2 (`5^2 ∥ n`, `a ≡ 2 (mod 4)`, odd prime factors `≥ 971`). -/

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H1.R1.H2.R1 of step Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H1.R1.H2
-- Credit: @Progren
-- Proves two general theorems for the case 5^2 || n, a = v2(n) >= 43, a = 2 mod 4:
--   1. even_mod8: Aurifeuillean factorization of 4^d + 1 eliminates all odd prime factors d | a
--      with d = 5 or 7 mod 8 (both coprime factors after dividing out 5 are 2 mod 3, forcing two
--      distinct primes in P with 3 | p + 1).
--   2. three_mem: A telescoping product bound on P \ {7, 13} shows prod (p + 1)/p <= 80/63 if
--      3 not in P, contradicting (25/16) * 2^a / (2^a + 1) >= 25/17. Hence 3 | n is forced.
-- Splits the remaining case into H1 (all odd prime factors of a are 1 mod 8) and H2 (at least
-- one odd prime factor of a is 3 mod 8).

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H1_R1_H2_R1

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1 hiding H1 H2 H3 H4 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H1_R1 hiding H1 H2 H3 main

-- H1: 3 | n and every odd prime factor d of a satisfies d >= 971 and d = 1 mod 8.
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 5) → n.factorization 5 = 2 →
    43 ≤ padicValNat 2 n → padicValNat 2 n % 4 = 2 →
    3 ∣ n →
    (∀ d : ℕ, d.Prime → d ≠ 2 → d ∣ padicValNat 2 n → 971 ≤ d ∧ d % 8 = 1) →
    padicValNat 2 n ≤ A

-- H2: 3 | n, every odd prime factor d of a satisfies d >= 971 and (d % 8 = 1 ∨ d % 8 = 3),
-- and a has at least one odd prime factor d with d % 8 = 3.
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 5) → n.factorization 5 = 2 →
    43 ≤ padicValNat 2 n → padicValNat 2 n % 4 = 2 →
    3 ∣ n →
    (∀ d : ℕ, d.Prime → d ≠ 2 → d ∣ padicValNat 2 n → 971 ≤ d ∧ (d % 8 = 1 ∨ d % 8 = 3)) →
    (∃ d : ℕ, d.Prime ∧ d ≠ 2 ∧ d ∣ padicValNat 2 n ∧ d % 8 = 3) →
    padicValNat 2 n ≤ A

/- ### Part 1: Aurifeuillean elimination of odd prime factors `d ≡ 5, 7 (mod 8)` -/

theorem four_pow_odd_add_one_mod25 (k : ℕ) :
    (4 ^ (2 * k + 1) + 1) % 25 = (5 * (2 * k + 1)) % 25 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have hstep : 4 ^ (2 * (k + 1) + 1) + 1 = 16 * (4 ^ (2 * k + 1) + 1) - 15 := by
      have h1 : 4 ^ (2 * (k + 1) + 1) = 16 * 4 ^ (2 * k + 1) := by
        rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega, pow_add]
        ring
      omega
    have hge : 15 ≤ 16 * (4 ^ (2 * k + 1) + 1) := by
      have : 1 ≤ 4 ^ (2 * k + 1) := Nat.one_le_pow _ _ (by norm_num)
      omega
    omega

private lemma not_dvd_25_two_pow_two_mul {d : ℕ} (hd : d % 2 = 1) (hd5 : ¬ 5 ∣ d) :
    ¬ 25 ∣ 2 ^ (2 * d) + 1 := by
  have hk : d = 2 * (d / 2) + 1 := by omega
  have h4 : 2 ^ (2 * d) = 4 ^ d := by
    rw [pow_mul]
    norm_num
  rw [h4, hk]
  intro h25
  have hmod : (4 ^ (2 * (d / 2) + 1) + 1) % 25 = 0 := Nat.mod_eq_zero_of_dvd h25
  rw [four_pow_odd_add_one_mod25] at hmod
  have : 5 ∣ 2 * (d / 2) + 1 := by omega
  rw [← hk] at this
  exact hd5 this

private lemma two_pow_mod3 (n : ℕ) : 2 ^ n % 3 = if n % 2 = 0 then 1 else 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    split_ifs at ih ⊢ <;> omega

private lemma two_pow_mod5 (n : ℕ) :
    2 ^ n % 5 = match n % 4 with | 0 => 1 | 1 => 2 | 2 => 4 | _ => 3 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Nat.mul_mod, ih]
    have h4 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
    rcases h4 with h | h | h | h <;> simp [h, Nat.add_mod]

private lemma aurifeuillean_prod (k : ℕ) :
    (2 ^ (2 * k + 1) + 1 - 2 ^ (k + 1)) * (2 ^ (2 * k + 1) + 1 + 2 ^ (k + 1)) =
      2 ^ (2 * (2 * k + 1)) + 1 := by
  have hle : 2 ^ (k + 1) ≤ 2 ^ (2 * k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  zify [show 2 ^ (k + 1) ≤ 2 ^ (2 * k + 1) + 1 by omega]
  have hsq : ((2 : ℤ) ^ (k + 1)) ^ 2 = 2 * (2 : ℤ) ^ (2 * k + 1) := by
    rw [← pow_mul, ← pow_succ']
    congr 1
    omega
  have h2d : (2 : ℤ) ^ (2 * (2 * k + 1)) = ((2 : ℤ) ^ (2 * k + 1)) ^ 2 := by
    rw [mul_comm, pow_mul]
  linarith [hsq, h2d]

private lemma aurifeuillean_coprime (k : ℕ) :
    Nat.Coprime (2 ^ (2 * k + 1) + 1 - 2 ^ (k + 1)) (2 ^ (2 * k + 1) + 1 + 2 ^ (k + 1)) := by
  set L := 2 ^ (2 * k + 1) + 1 - 2 ^ (k + 1)
  set M := 2 ^ (2 * k + 1) + 1 + 2 ^ (k + 1)
  have hle : 2 ^ (k + 1) ≤ 2 ^ (2 * k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hLodd : L % 2 = 1 := by
    have h1 : 2 ∣ 2 ^ (2 * k + 1) := dvd_pow_self 2 (by omega)
    have h2 : 2 ∣ 2 ^ (k + 1) := dvd_pow_self 2 (by omega)
    omega
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hne
  have hp := Nat.minFac_prime hne
  have hpg : (Nat.gcd L M).minFac ∣ Nat.gcd L M := Nat.minFac_dvd _
  have hpL : (Nat.gcd L M).minFac ∣ L := hpg.trans (Nat.gcd_dvd_left L M)
  have hpM : (Nat.gcd L M).minFac ∣ M := hpg.trans (Nat.gcd_dvd_right L M)
  have hsub : M - L = 2 ^ (k + 2) := by
    have : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by rw [pow_succ']
    omega
  have hp2 : (Nat.gcd L M).minFac ∣ 2 ^ (k + 2) := by
    rw [← hsub]
    exact Nat.dvd_sub hpM hpL
  have hq2 : (Nat.gcd L M).minFac = 2 :=
    (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hp2)
  rw [hq2] at hpL
  omega

theorem even_mod8 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hm : m % 4 = 2) {d : ℕ} (hd : d.Prime) (hd2 : d ≠ 2) (hd5 : d ≠ 5) (hda : d ∣ m)
    (h8 : d % 8 = 5 ∨ d % 8 = 7) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨-, S2, S3, -, -, -, -, -⟩ := facts hP (hK5 2) E
  have hdo : d % 2 = 1 := hd.eq_two_or_odd.resolve_left hd2
  have hD : 2 ^ (2 * d) + 1 ∣ 2 ^ m + 1 := by
    have := one_add_pow_dvd_of_odd_mul (z := 2) (mod_of_dvd_two_mod_four hda hdo hm)
    rwa [add_comm 1 (2 ^ (2 * d)), add_comm 1 (2 ^ m)] at this
  have hnd25 : ¬ 25 ∣ 2 ^ (2 * d) + 1 := by
    apply not_dvd_25_two_pow_two_mul hdo
    intro h5d
    exact hd5 ((Nat.prime_dvd_prime_iff_eq (by norm_num) hd).mp h5d).symm
  set k := d / 2
  have hdk : d = 2 * k + 1 := by omega
  set L := 2 ^ (2 * k + 1) + 1 - 2 ^ (k + 1)
  set M := 2 ^ (2 * k + 1) + 1 + 2 ^ (k + 1)
  have hLM : L * M = 2 ^ (2 * d) + 1 := by rw [hdk]; exact aurifeuillean_prod k
  have hcop : Nat.Coprime L M := aurifeuillean_coprime k
  have hle : 2 ^ (k + 1) ≤ 2 ^ (2 * k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hLodd : L % 2 = 1 := by
    have h1 : 2 ∣ 2 ^ (2 * k + 1) := dvd_pow_self 2 (by omega)
    have h2 : 2 ∣ 2 ^ (k + 1) := dvd_pow_self 2 (by omega)
    omega
  have hModd : M % 2 = 1 := by
    have h1 : 2 ∣ 2 ^ (2 * k + 1) := dvd_pow_self 2 (by omega)
    have h2 : 2 ∣ 2 ^ (k + 1) := dvd_pow_self 2 (by omega)
    omega
  -- Construct coprime odd numbers A, B dividing 2^(2d)+1, neither divisible by 5, both ≡ 2 (mod 3).
  have hAB : ∃ A B : ℕ, A ∣ L ∧ B ∣ M ∧ A % 3 = 2 ∧ B % 3 = 2 ∧ ¬ 5 ∣ A ∧ ¬ 5 ∣ B := by
    have hm3d : 2 ^ (2 * k + 1) % 3 = 2 := by rw [two_pow_mod3]; simp
    rcases h8 with h8 | h8
    · -- d ≡ 5 (mod 8) => k ≡ 2 (mod 4), k + 1 ≡ 3 (mod 4)
      have hm3k : 2 ^ (k + 1) % 3 = 2 := by rw [two_pow_mod3]; split_ifs <;> omega
      have hm5d : 2 ^ (2 * k + 1) % 5 = 2 := by
        rw [two_pow_mod5, show (2 * k + 1) % 4 = 1 by omega]; rfl
      have hm5k : 2 ^ (k + 1) % 5 = 3 := by
        rw [two_pow_mod5, show (k + 1) % 4 = 3 by omega]; rfl
      have hL5 : 5 ∣ L := by omega
      have hL3 : L % 3 = 1 := by omega
      have hM3 : M % 3 = 2 := by omega
      refine ⟨L / 5, M, Nat.div_dvd_of_dvd hL5, dvd_refl M, ?_, hM3, ?_, ?_⟩
      · have h5q : 5 * (L / 5) = L := Nat.mul_div_cancel' hL5
        omega
      · intro h5A
        apply hnd25
        rw [← hLM]
        have h25L : 25 ∣ L := by
          obtain ⟨t, ht⟩ := h5A
          refine ⟨t, ?_⟩
          have h5q : 5 * (L / 5) = L := Nat.mul_div_cancel' hL5
          omega
        exact h25L.mul_right M
      · intro h5M
        apply hnd25
        rw [← hLM]
        exact mul_dvd_mul hL5 h5M
    · -- d ≡ 7 (mod 8) => k ≡ 3 (mod 4), k + 1 ≡ 0 (mod 4)
      have hm3k : 2 ^ (k + 1) % 3 = 1 := by rw [two_pow_mod3]; split_ifs <;> omega
      have hm5d : 2 ^ (2 * k + 1) % 5 = 3 := by
        rw [two_pow_mod5, show (2 * k + 1) % 4 = 3 by omega]; rfl
      have hm5k : 2 ^ (k + 1) % 5 = 1 := by
        rw [two_pow_mod5, show (k + 1) % 4 = 0 by omega]; rfl
      have hM5 : 5 ∣ M := by omega
      have hL3 : L % 3 = 2 := by omega
      have hM3 : M % 3 = 1 := by omega
      refine ⟨L, M / 5, dvd_refl L, Nat.div_dvd_of_dvd hM5, hL3, ?_, ?_, ?_⟩
      · have h5q : 5 * (M / 5) = M := Nat.mul_div_cancel' hM5
        omega
      · intro h5L
        apply hnd25
        rw [← hLM]
        exact mul_dvd_mul h5L hM5
      · intro h5B
        apply hnd25
        rw [← hLM]
        have h25M : 25 ∣ M := by
          obtain ⟨t, ht⟩ := h5B
          refine ⟨t, ?_⟩
          have h5q : 5 * (M / 5) = M := Nat.mul_div_cancel' hM5
          omega
        exact h25M.mul_left L
  obtain ⟨A, B, hAL, hBM, hA3, hB3, hA5, hB5⟩ := hAB
  obtain ⟨p1, hp1, hp1A, hp13⟩ := exists_prime_mod3 A hA3
  obtain ⟨p2, hp2, hp2B, hp23⟩ := exists_prime_mod3 B hB3
  have hp1L : p1 ∣ L := hp1A.trans hAL
  have hp2M : p2 ∣ M := hp2B.trans hBM
  have hp1ne2 : p1 ≠ 2 := by rintro rfl; omega
  have hp2ne2 : p2 ≠ 2 := by rintro rfl; omega
  have hp1ne5 : p1 ≠ 5 := by rintro rfl; exact hA5 hp1A
  have hp2ne5 : p2 ≠ 5 := by rintro rfl; exact hB5 hp2B
  have hp1ne : p1 ≠ p2 := by
    rintro rfl
    have h1 : p1 ∣ Nat.gcd L M := Nat.dvd_gcd hp1L hp2M
    rw [hcop.gcd_eq_one] at h1
    exact hp1.not_dvd_one h1
  have hp1P : p1 ∈ P := S2 p1 hp1 hp1ne2 (hnz hp1ne5) ((hp1L.mul_right M).trans (hLM ▸ hD))
  have hp2P : p2 ∈ P := S2 p2 hp2 hp2ne2 (hnz hp2ne5) ((hp2M.mul_left L).trans (hLM ▸ hD))
  have h3p1 : 3 ∣ p1 + 1 := Nat.dvd_of_mod_eq_zero (by omega)
  have h3p2 : 3 ∣ p2 + 1 := Nat.dvd_of_mod_eq_zero (by omega)
  exact hp1ne (S3 3 (by norm_num) (by norm_num) (hnz (by norm_num)) p1 hp1P p2 hp2P h3p1 h3p2)

/- ### Part 2: Telescoping product bound forcing `3 ∣ n` -/

private lemma five_dvd_two_pow_two_mod4 {m : ℕ} (hm : m % 4 = 2) : 5 ∣ 2 ^ m + 1 := by
  have h2m : 2 ^ m % 5 = 4 := by rw [two_pow_mod5, hm]; rfl
  omega

private lemma prod_sub_one_le_sub_one {S : Finset ℕ} (hS : ∀ q ∈ S, 2 ≤ q) (hne : S.Nonempty) :
    ∏ q ∈ S, (q - 1) ≤ (∏ q ∈ S, q) - 1 := by
  induction S using Finset.induction with
  | empty => exact absurd hne Finset.not_nonempty_empty
  | insert a s ha ih =>
    have ha2 : 2 ≤ a := hS a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    rcases s.eq_empty_or_nonempty with rfl | hsne
    · simp
    · have ih' := ih (fun q hq => hS q (Finset.mem_insert_of_mem hq)) hsne
      have hpos : 1 ≤ ∏ q ∈ s, q := Finset.one_le_prod' (fun q hq => by
        have := hS q (Finset.mem_insert_of_mem hq); omega)
      have hle : (a - 1) * ∏ q ∈ s, (q - 1) ≤ (a - 1) * ((∏ q ∈ s, q) - 1) :=
        Nat.mul_le_mul_left _ ih'
      calc (a - 1) * ∏ q ∈ s, (q - 1)
          ≤ (a - 1) * ((∏ q ∈ s, q) - 1) := hle
        _ ≤ a * (∏ q ∈ s, q) - 1 := by
            zify [show 1 ≤ a by omega, hpos, show 1 ≤ a * ∏ q ∈ s, q by nlinarith]
            nlinarith

private lemma prod_two_pow_bound_aux (N : ℕ) (hN : 3 ≤ N) :
    ∏ k ∈ Finset.Icc 4 N, ((2 : ℚ) ^ k / (2 ^ k - 1)) ≤ (8 / 7 : ℚ) * (1 - 1 / (2 : ℚ) ^ N) := by
  induction N, hN using Nat.le_induction with
  | base =>
    have h : Finset.Icc 4 3 = ∅ := Finset.Icc_eq_empty (by omega)
    rw [h, Finset.prod_empty]
    norm_num
  | succ N hN ih =>
    have hIcc : Finset.Icc 4 (N + 1) = insert (N + 1) (Finset.Icc 4 N) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnot : N + 1 ∉ Finset.Icc 4 N := by simp
    rw [hIcc, Finset.prod_insert hnot]
    have h2N : (1 : ℚ) ≤ (2 : ℚ) ^ N := one_le_pow₀ (by norm_num)
    have h2N1 : (2 : ℚ) ≤ (2 : ℚ) ^ (N + 1) := by
      rw [pow_succ]
      linarith
    have hpos1 : (0 : ℚ) < (2 : ℚ) ^ (N + 1) - 1 := by linarith
    have hpos2 : (0 : ℚ) < (2 : ℚ) ^ (N + 1) := by positivity
    have hfac : (0 : ℚ) ≤ (2 : ℚ) ^ (N + 1) / ((2 : ℚ) ^ (N + 1) - 1) := by positivity
    calc ((2 : ℚ) ^ (N + 1) / ((2 : ℚ) ^ (N + 1) - 1)) *
            ∏ k ∈ Finset.Icc 4 N, ((2 : ℚ) ^ k / (2 ^ k - 1))
        ≤ ((2 : ℚ) ^ (N + 1) / ((2 : ℚ) ^ (N + 1) - 1)) *
            ((8 / 7 : ℚ) * (1 - 1 / (2 : ℚ) ^ N)) := mul_le_mul_of_nonneg_left ih hfac
      _ ≤ (8 / 7 : ℚ) * (1 - 1 / (2 : ℚ) ^ (N + 1)) := by
          have hpow : (2 : ℚ) ^ (N + 1) = 2 * (2 : ℚ) ^ N := by rw [pow_succ']
          have h2Npos : (0 : ℚ) < (2 : ℚ) ^ N := by positivity
          rw [← mul_assoc, mul_comm ((2 : ℚ) ^ (N + 1) / ((2 : ℚ) ^ (N + 1) - 1)) (8 / 7 : ℚ),
            mul_assoc]
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          rw [show (1 : ℚ) - 1 / (2 : ℚ) ^ N = ((2 : ℚ) ^ N - 1) / (2 : ℚ) ^ N by field_simp]
          rw [show (1 : ℚ) - 1 / (2 : ℚ) ^ (N + 1) = ((2 : ℚ) ^ (N + 1) - 1) / (2 : ℚ) ^ (N + 1) by
            field_simp]
          rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) hpos2]
          nlinarith [hpow]

private lemma prod_two_pow_bound (N : ℕ) :
    ∏ k ∈ Finset.Icc 4 N, ((2 : ℚ) ^ k / (2 ^ k - 1)) ≤ 8 / 7 := by
  by_cases hN : 3 ≤ N
  · calc ∏ k ∈ Finset.Icc 4 N, ((2 : ℚ) ^ k / (2 ^ k - 1))
        ≤ (8 / 7 : ℚ) * (1 - 1 / (2 : ℚ) ^ N) := prod_two_pow_bound_aux N hN
      _ ≤ (8 / 7 : ℚ) * 1 := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          have : (0 : ℚ) ≤ 1 / (2 : ℚ) ^ N := by positivity
          linarith
      _ = 8 / 7 := mul_one _
  · have h : Finset.Icc 4 N = ∅ := Finset.Icc_eq_empty (by omega)
    rw [h, Finset.prod_empty]
    norm_num

private lemma eq_two_pow_of_prime_dvd {k : ℕ} (hk : 0 < k)
    (h2 : ∀ q : ℕ, q.Prime → q ∣ k → q = 2) : ∃ s : ℕ, k = 2 ^ s := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hk1 : k = 1
    · exact ⟨0, by simp [hk1]⟩
    · have hp := Nat.minFac_prime hk1
      have hpd : k.minFac ∣ k := Nat.minFac_dvd k
      have hq2 : k.minFac = 2 := h2 k.minFac hp hpd
      have h2k : 2 ∣ k := hq2 ▸ hpd
      obtain ⟨t, ht⟩ := h2k
      have ht0 : 0 < t := by omega
      have htk : t < k := by omega
      obtain ⟨s, hs⟩ := ih t htk ht0 (fun q hq hqt => h2 q hq (hqt.trans (ht ▸ dvd_mul_left t 2)))
      exact ⟨s + 1, by rw [ht, hs, pow_succ']⟩

theorem three_mem {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hm : m % 4 = 2) (hm4 : 4 ≤ m) : 3 ∈ P := by
  by_contra h3P
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, -, S3, -, -, -, S7, S8⟩ := facts hP (hK5 2) E
  have h13P : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have h7P : 7 ∈ P := S1 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13 h13P (by norm_num)
  set P' := (P.erase 13).erase 7
  have hP'sub : P' ⊆ P := (Finset.erase_subset 7 _).trans (Finset.erase_subset 13 P)
  have h7in : 7 ∈ P.erase 13 := Finset.mem_erase.mpr ⟨by norm_num, h7P⟩
  -- Step 1: Exact rational product over P'
  have hprod_eq : ∏ p ∈ P', (((p : ℚ) + 1) / (p : ℚ)) =
      (25 / 16 : ℚ) * ((2 : ℚ) ^ m / ((2 : ℚ) ^ m + 1)) := by
    have hL1 : ∏ p ∈ P, (p + 1) = 8 * (14 * ∏ p ∈ P', (p + 1)) := by
      rw [← Finset.mul_prod_erase P (fun p => p + 1) h13P,
        ← Finset.mul_prod_erase (P.erase 13) (fun p => p + 1) h7in]
      ring
    have hR1 : ∏ p ∈ P, p = 7 * (13 * ∏ p ∈ P', p) := by
      rw [← Finset.mul_prod_erase P (fun p => p) h13P,
        ← Finset.mul_prod_erase (P.erase 13) (fun p => p) h7in]
      ring
    rw [hL1, hR1] at E
    have hEqQ : ((2 : ℚ) ^ m + 1) * 26 * (8 * (14 * ∏ p ∈ P', ((p : ℚ) + 1))) =
        (2 : ℚ) ^ (m + 1) * 25 * (7 * (13 * ∏ p ∈ P', (p : ℚ))) := by
      have h := congrArg (Nat.cast (R := ℚ)) E
      simpa [Nat.cast_prod] using h
    have hprod_ne : (∏ p ∈ P', (p : ℚ)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro p hp
      have := (hP p (hP'sub hp)).1.ne_zero
      exact_mod_cast this
    have h2m_ne : ((2 : ℚ) ^ m + 1) ≠ 0 := by positivity
    rw [Finset.prod_div_distrib]
    field_simp [hprod_ne, h2m_ne]
    rw [pow_succ' (2 : ℚ) m] at hEqQ
    linarith
  have hlower : (25 / 17 : ℚ) ≤ ∏ p ∈ P', (((p : ℚ) + 1) / (p : ℚ)) := by
    rw [hprod_eq]
    have h16 : (16 : ℚ) ≤ (2 : ℚ) ^ m := by
      have : 2 ^ 4 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm4
      exact_mod_cast this
    have hpos : (0 : ℚ) < (2 : ℚ) ^ m + 1 := by positivity
    rw [show (25 / 17 : ℚ) = (25 / 16 : ℚ) * (16 / 17) by norm_num]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    rw [div_le_div_iff₀ (by norm_num) hpos]
    linarith
  -- Step 2: Telescoping product bound over leaves L = {p ∈ P' | C p = ∅}
  let C : ℕ → Finset ℕ := fun p => P'.filter (fun q => q ∣ p + 1)
  let L := P'.filter (fun p => C p = ∅)
  let I := P'.filter (fun p => (C p).Nonempty)
  have hdisj : (I : Set ℕ).PairwiseDisjoint C := by
    intro p1 hp1 p2 hp2 hne
    change Disjoint (C p1) (C p2)
    rw [Finset.disjoint_left]
    intro q hq1 hq2
    simp only [C, Finset.mem_filter] at hq1 hq2
    have hqP := hP'sub hq1.1
    have hq5 : q ≠ 5 := fun h => h5 (h ▸ hqP)
    exact hne (S3 q (hP q hqP).1 (hP q hqP).2 (hnz hq5)
      p1 (hP'sub (Finset.mem_filter.mp hp1).1)
      p2 (hP'sub (Finset.mem_filter.mp hp2).1) hq1.2 hq2.2)
  have hUsub : I.biUnion C ⊆ P' := by
    intro q hq
    rw [Finset.mem_biUnion] at hq
    obtain ⟨p, -, hqp⟩ := hq
    exact (Finset.mem_filter.mp hqp).1
  have hstepI : ∀ p ∈ I, (((p : ℚ) + 1) / ((p : ℚ) - 1)) *
      ∏ q ∈ C p, (((q : ℚ) - 1) / (q : ℚ)) ≤ 1 := by
    intro p hpI
    have hpP' := (Finset.mem_filter.mp hpI).1
    have hCne := (Finset.mem_filter.mp hpI).2
    have hp_prime := (hP p (hP'sub hpP')).1
    have hp_ne2 := (hP p (hP'sub hpP')).2
    have hQ_dvd : ∏ q ∈ C p, q ∣ p + 1 := by
      apply Finset.prod_primes_dvd
      · intro q hq
        exact (hP q (hP'sub (Finset.mem_filter.mp hq).1)).1.prime
      · intro q hq
        exact (Finset.mem_filter.mp hq).2
    have h2_dvd : 2 ∣ p + 1 := by
      have := hp_prime.eq_two_or_odd.resolve_left hp_ne2
      omega
    have hcop2Q : Nat.Coprime 2 (∏ q ∈ C p, q) := by
      apply Nat.Coprime.prod_right
      intro q hq
      have hqp := hP q (hP'sub (Finset.mem_filter.mp hq).1)
      exact (Nat.prime_two.coprime_iff_not_dvd).mpr (fun h => hqp.2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hqp.1).mp h).symm)
    have h2Q_dvd : 2 * ∏ q ∈ C p, q ∣ p + 1 := hcop2Q.mul_dvd_of_dvd_of_dvd h2_dvd hQ_dvd
    have h2Q_le : 2 * ∏ q ∈ C p, q ≤ p + 1 := Nat.le_of_dvd (by omega) h2Q_dvd
    have hsub1 : ∏ q ∈ C p, (q - 1) ≤ (∏ q ∈ C p, q) - 1 :=
      prod_sub_one_le_sub_one (fun q hq => (hP q (hP'sub (Finset.mem_filter.mp hq).1)).1.two_le) hCne
    have hQge2 : 2 ≤ ∏ q ∈ C p, q := by
      obtain ⟨q0, hq0⟩ := hCne
      have hq02 : 2 ≤ q0 := (hP q0 (hP'sub (Finset.mem_filter.mp hq0).1)).1.two_le
      calc 2 ≤ q0 := hq02
        _ ≤ ∏ q ∈ C p, q := Finset.single_le_prod' (fun q hq => (hP q (hP'sub (Finset.mem_filter.mp hq).1)).1.one_le) hq0
    have hprod_sub_eq : (∏ q ∈ C p, ((q : ℚ) - 1)) = ((∏ q ∈ C p, (q - 1) : ℕ) : ℚ) := by
      rw [Nat.cast_prod]
      apply Finset.prod_congr rfl
      intro q hq
      have hq1 : 1 ≤ q := (hP q (hP'sub (Finset.mem_filter.mp hq).1)).1.one_le
      exact (Nat.cast_sub hq1).symm
    have hsub1Q : ∏ q ∈ C p, ((q : ℚ) - 1) ≤ (∏ q ∈ C p, (q : ℚ)) - 1 := by
      rw [hprod_sub_eq, ← Nat.cast_prod]
      have h1 : ((∏ q ∈ C p, (q - 1) : ℕ) : ℚ) ≤ (((∏ q ∈ C p, q) - 1 : ℕ) : ℚ) :=
        Nat.cast_le.mpr hsub1
      rwa [Nat.cast_sub (by omega : 1 ≤ ∏ q ∈ C p, q), Nat.cast_one] at h1
    have hQpos : (0 : ℚ) < ∏ q ∈ C p, (q : ℚ) := by
      apply Finset.prod_pos
      intro q hq
      have := (hP q (hP'sub (Finset.mem_filter.mp hq).1)).1.pos
      exact_mod_cast this
    have hp1pos : (0 : ℚ) < (p : ℚ) - 1 := by
      have := hp_prime.two_le
      have : (2 : ℚ) ≤ p := by exact_mod_cast this
      linarith
    rw [Finset.prod_div_distrib, div_mul_div_comm, div_le_one (by positivity)]
    have h2Q_leQ : 2 * ∏ q ∈ C p, (q : ℚ) ≤ (p : ℚ) + 1 := by
      have : ((2 * ∏ q ∈ C p, q : ℕ) : ℚ) ≤ ((p + 1 : ℕ) : ℚ) := by exact_mod_cast h2Q_le
      simpa using this
    nlinarith [hsub1Q, h2Q_leQ, hQpos, hp1pos]
  have htele : ∏ p ∈ P', (((p : ℚ) + 1) / (p : ℚ)) ≤ ∏ p ∈ L, (((p : ℚ) + 1) / ((p : ℚ) - 1)) := by
    have hsplit : ∏ p ∈ P', (((p : ℚ) + 1) / (p : ℚ)) =
        (∏ p ∈ P', (((p : ℚ) + 1) / ((p : ℚ) - 1))) * (∏ p ∈ P', (((p : ℚ) - 1) / (p : ℚ))) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro p hp
      have hp2 : (2 : ℚ) ≤ p := by exact_mod_cast (hP p (hP'sub hp)).1.two_le
      have hp0 : (p : ℚ) ≠ 0 := by linarith
      have hp1 : (p : ℚ) - 1 ≠ 0 := by linarith
      field_simp [hp0, hp1]
    rw [hsplit]
    have hLI : ∏ p ∈ P', (((p : ℚ) + 1) / ((p : ℚ) - 1)) =
        (∏ p ∈ L, (((p : ℚ) + 1) / ((p : ℚ) - 1))) * (∏ p ∈ I, (((p : ℚ) + 1) / ((p : ℚ) - 1))) := by
      have hIeq : I = P'.filter (fun p => ¬ C p = ∅) := by
        ext p; simp [I, Finset.nonempty_iff_ne_empty]
      rw [hIeq, Finset.prod_filter_mul_prod_filter_not]
    rw [hLI, mul_assoc]
    have hUle : ∏ q ∈ P', (((q : ℚ) - 1) / (q : ℚ)) ≤ ∏ q ∈ I.biUnion C, (((q : ℚ) - 1) / (q : ℚ)) := by
      rw [← Finset.prod_sdiff hUsub]
      have hle1 : ∏ q ∈ P' \ I.biUnion C, (((q : ℚ) - 1) / (q : ℚ)) ≤ 1 := by
        apply Finset.prod_le_one
        · intro q hq
          have hq2 : (2 : ℚ) ≤ q := by exact_mod_cast (hP q (hP'sub (Finset.mem_sdiff.mp hq).1)).1.two_le
          have : (0 : ℚ) ≤ (q : ℚ) - 1 := by linarith
          positivity
        · intro q hq
          have hq2 : (2 : ℚ) ≤ q := by exact_mod_cast (hP q (hP'sub (Finset.mem_sdiff.mp hq).1)).1.two_le
          rw [div_le_one (by linarith)]
          linarith
      have hnonneg : 0 ≤ ∏ q ∈ I.biUnion C, (((q : ℚ) - 1) / (q : ℚ)) := by
        apply Finset.prod_nonneg
        intro q hq
        have hq2 : (2 : ℚ) ≤ q := by exact_mod_cast (hP q (hP'sub (hUsub hq))).1.two_le
        have : (0 : ℚ) ≤ (q : ℚ) - 1 := by linarith
        positivity
      nlinarith
    have hLnonneg : 0 ≤ ∏ p ∈ L, (((p : ℚ) + 1) / ((p : ℚ) - 1)) := by
      apply Finset.prod_nonneg
      intro p hp
      have hp2 : (2 : ℚ) ≤ p := by exact_mod_cast (hP p (hP'sub (Finset.mem_filter.mp hp).1)).1.two_le
      have : (0 : ℚ) < (p : ℚ) - 1 := by linarith
      positivity
    have hInonneg : 0 ≤ ∏ p ∈ I, (((p : ℚ) + 1) / ((p : ℚ) - 1)) := by
      apply Finset.prod_nonneg
      intro p hp
      have hp2 : (2 : ℚ) ≤ p := by exact_mod_cast (hP p (hP'sub (Finset.mem_filter.mp hp).1)).1.two_le
      have : (0 : ℚ) < (p : ℚ) - 1 := by linarith
      positivity
    have hIprod : (∏ p ∈ I, (((p : ℚ) + 1) / ((p : ℚ) - 1))) *
        (∏ q ∈ I.biUnion C, (((q : ℚ) - 1) / (q : ℚ))) ≤ 1 := by
      rw [Finset.prod_biUnion hdisj, ← Finset.prod_mul_distrib]
      apply Finset.prod_le_one
      · intro p hp
        have hp2 : (2 : ℚ) ≤ p := by exact_mod_cast (hP p (hP'sub (Finset.mem_filter.mp hp).1)).1.two_le
        have : (0 : ℚ) < (p : ℚ) - 1 := by linarith
        apply mul_nonneg (by positivity)
        apply Finset.prod_nonneg
        intro q hq
        have hq2 : (2 : ℚ) ≤ q := by exact_mod_cast (hP q (hP'sub (Finset.mem_filter.mp hq).1)).1.two_le
        have : (0 : ℚ) ≤ (q : ℚ) - 1 := by linarith
        positivity
      · exact hstepI
    calc (∏ p ∈ L, (((p : ℚ) + 1) / ((p : ℚ) - 1))) *
          ((∏ p ∈ I, (((p : ℚ) + 1) / ((p : ℚ) - 1))) * ∏ q ∈ P', (((q : ℚ) - 1) / (q : ℚ)))
        ≤ (∏ p ∈ L, (((p : ℚ) + 1) / ((p : ℚ) - 1))) *
          ((∏ p ∈ I, (((p : ℚ) + 1) / ((p : ℚ) - 1))) * ∏ q ∈ I.biUnion C, (((q : ℚ) - 1) / (q : ℚ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hUle hInonneg) hLnonneg
      _ ≤ (∏ p ∈ L, (((p : ℚ) + 1) / ((p : ℚ) - 1))) * 1 :=
          mul_le_mul_of_nonneg_left hIprod hLnonneg
      _ = ∏ p ∈ L, (((p : ℚ) + 1) / ((p : ℚ) - 1)) := mul_one _
  -- Step 3: Bound the leaf product by (10/9) * (8/7) = 80/63
  let L5 := L.filter (fun p => 5 ∣ p + 1)
  let L0 := L.filter (fun p => ¬ 5 ∣ p + 1)
  have hLsplit : ∏ p ∈ L, (((p : ℚ) + 1) / ((p : ℚ) - 1)) =
      (∏ p ∈ L5, (((p : ℚ) + 1) / ((p : ℚ) - 1))) * (∏ p ∈ L0, (((p : ℚ) + 1) / ((p : ℚ) - 1))) :=
    (Finset.prod_filter_mul_prod_filter_not L (fun p => 5 ∣ p + 1) _).symm
  -- At most one p ∈ L5
  have hL5_sub : L5.card ≤ 1 := by
    by_contra hgt
    have h1lt : 1 < L5.card := by omega
    obtain ⟨p1, hp1, p2, hp2, hne⟩ := Finset.one_lt_card.mp h1lt
    have h5m : 5 ∣ 2 ^ m + 1 := five_dvd_two_pow_two_mod4 hm
    have hp1P : p1 ∈ P := hP'sub (Finset.mem_filter.mp (Finset.mem_filter.mp hp1).1).1
    have hp2P : p2 ∈ P := hP'sub (Finset.mem_filter.mp (Finset.mem_filter.mp hp2).1).1
    have h5p1 : 5 ∣ p1 + 1 := (Finset.mem_filter.mp hp1).2
    have h5p2 : 5 ∣ p2 + 1 := (Finset.mem_filter.mp hp2).2
    have hsub : ({p1, p2} : Finset ℕ) ⊆ P := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hp1P
      · rw [Finset.mem_singleton.mp hx]; exact hp2P
    have hprod_dvd : (p1 + 1) * (p2 + 1) ∣ ∏ p ∈ P, (p + 1) := by
      have := Finset.prod_dvd_prod_of_subset _ _ (fun x => x + 1) hsub
      rwa [Finset.prod_pair hne] at this
    have h125_lhs : 5 ^ 3 ∣ (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) := by
      have h1 : 5 * (5 * 5) ∣ (2 ^ m + 1) * ((p1 + 1) * (p2 + 1)) :=
        mul_dvd_mul h5m (mul_dvd_mul h5p1 h5p2)
      have h2 : (2 ^ m + 1) * ((p1 + 1) * (p2 + 1)) ∣ (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) := by
        rw [show (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) =
          (1 + 5 ^ 2) * ((2 ^ m + 1) * ∏ p ∈ P, (p + 1)) by ring]
        exact (mul_dvd_mul_left (2 ^ m + 1) hprod_dvd).mul_left (1 + 5 ^ 2)
      exact h1.trans h2
    rw [E] at h125_lhs
    have h5_rhs : 5 ∣ 2 ^ (m + 1) * ∏ p ∈ P, p := by
      have : 5 ^ 2 * 5 ∣ 5 ^ 2 * (2 ^ (m + 1) * ∏ p ∈ P, p) := by
        convert h125_lhs using 1 <;> ring
      exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 5 ^ 2)).mp this
    rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 5)).mp h5_rhs with h52 | h5prod
    · have := (Nat.Prime.dvd_of_dvd_pow (by norm_num) h52)
      omega
    · obtain ⟨q, hqP, h5q⟩ := (Prime.dvd_finsetProd_iff (by norm_num : Nat.Prime 5).prime _).mp h5prod
      have hqeq : 5 = q := (Nat.prime_dvd_prime_iff_eq (by norm_num) (hP q hqP).1).mp h5q
      exact h5 (hqeq ▸ hqP)
  have hL5_bound : ∏ p ∈ L5, (((p : ℚ) + 1) / ((p : ℚ) - 1)) ≤ 10 / 9 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hL5_sub with h0 | h1
    · rw [Finset.card_eq_zero.mp h0, Finset.prod_empty]; norm_num
    · obtain ⟨p, hpL5⟩ := Finset.card_eq_one.mp h1
      rw [hpL5, Finset.prod_singleton]
      have hp_mem : p ∈ L5 := hpL5 ▸ Finset.mem_singleton_self p
      have hpP' : p ∈ P' := (Finset.mem_filter.mp (Finset.mem_filter.mp hp_mem).1).1
      have h5p : 5 ∣ p + 1 := (Finset.mem_filter.mp hp_mem).2
      have hpP : p ∈ P := hP'sub hpP'
      have hp_pr := (hP p hpP).1
      have hp_ne2 := (hP p hpP).2
      have hp_ne3 : p ≠ 3 := fun h => h3P (h ▸ hpP)
      have hp_ne5 : p ≠ 5 := fun h => h5 (h ▸ hpP)
      have hp_ne7 : p ≠ 7 := (Finset.mem_erase.mp hpP').1
      have hp_ne13 : p ≠ 13 := (Finset.mem_erase.mp (Finset.mem_erase.mp hpP').2).1
      have hp19 : 19 ≤ p := by
        by_contra hlt
        have : p = 4 ∨ p = 9 ∨ p = 14 := by omega
        rcases this with rfl | rfl | rfl <;> norm_num at hp_pr
      have hp19Q : (19 : ℚ) ≤ p := by exact_mod_cast hp19
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
  -- Bound L0 using prod_two_pow_bound
  have hL0_pow : ∀ p ∈ L0, ∃ k : ℕ, 4 ≤ k ∧ p + 1 = 2 ^ (k + 1) := by
    intro p hpL0
    have hpL := (Finset.mem_filter.mp hpL0).1
    have hnot5 := (Finset.mem_filter.mp hpL0).2
    have hpP' := (Finset.mem_filter.mp hpL).1
    have hCp := (Finset.mem_filter.mp hpL).2
    have hpP := hP'sub hpP'
    have h2only : ∀ q : ℕ, q.Prime → q ∣ p + 1 → q = 2 := by
      intro q hq hqp
      by_contra hq2
      have hq5 : q ≠ 5 := fun h => hnot5 (h ▸ hqp)
      have hqP : q ∈ P := S1 q hq hq2 (hnz hq5) p hpP hqp
      have hq13 : q ≠ 13 := by
        rintro rfl
        exact S8 13 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num) p hpP hqp
      have hq7 : q ≠ 7 := by
        rintro rfl
        have hp13 : p = 13 := S3 7 (by norm_num) (by norm_num) (hnz (by norm_num))
          p hpP 13 h13P hqp (by norm_num)
        exact (Finset.mem_erase.mp (Finset.mem_erase.mp hpP').2).1 hp13
      have hqP' : q ∈ P' := Finset.mem_erase.mpr ⟨hq7, Finset.mem_erase.mpr ⟨hq13, hqP⟩⟩
      have hqC : q ∈ C p := Finset.mem_filter.mpr ⟨hqP', hqp⟩
      rw [hCp] at hqC
      exact Finset.notMem_empty q hqC
    obtain ⟨s, hs⟩ := eq_two_pow_of_prime_dvd (by omega) h2only
    have hp_pr := (hP p hpP).1
    have hp_ne3 : p ≠ 3 := fun h => h3P (h ▸ hpP)
    have hp_ne7 : p ≠ 7 := (Finset.mem_erase.mp hpP').1
    have hp2 : 2 ≤ p := hp_pr.two_le
    have hs5 : 5 ≤ s := by
      by_contra hlt
      have hs4 : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 := by omega
      rcases hs4 with rfl | rfl | rfl | rfl | rfl <;> norm_num at hs
      · omega
      · have : p = 1 := by omega
        subst this; norm_num at hp_pr
      · omega
      · omega
      · have : p = 15 := by omega
        subst this; norm_num at hp_pr
    exact ⟨s - 1, by omega, by rwa [Nat.sub_add_cancel (by omega)]⟩
  have hL0_bound : ∏ p ∈ L0, (((p : ℚ) + 1) / ((p : ℚ) - 1)) ≤ 8 / 7 := by
    let f : ℕ → ℕ := fun p => padicValNat 2 (p + 1) - 1
    have hf_spec : ∀ p ∈ L0, 4 ≤ f p ∧ p + 1 = 2 ^ (f p + 1) := by
      intro p hp
      obtain ⟨k, hk4, hk⟩ := hL0_pow p hp
      have hv : padicValNat 2 (p + 1) = k + 1 := by
        rw [hk, padicValNat.prime_pow]
      have hfk : f p = k := by simp [f, hv]
      exact ⟨hfk ▸ hk4, hfk ▸ hk⟩
    have hf_inj : Set.InjOn f L0 := by
      intro p1 hp1 p2 hp2 heq
      have h1 := (hf_spec p1 hp1).2
      have h2 := (hf_spec p2 hp2).2
      rw [heq] at h1
      omega
    have hprod_img : ∏ p ∈ L0, (((p : ℚ) + 1) / ((p : ℚ) - 1)) =
        ∏ k ∈ L0.image f, ((2 : ℚ) ^ k / ((2 : ℚ) ^ k - 1)) := by
      rw [Finset.prod_image hf_inj]
      apply Finset.prod_congr rfl
      intro p hp
      obtain ⟨hk4, hk⟩ := hf_spec p hp
      have hp1Q : (p : ℚ) + 1 = 2 * (2 : ℚ) ^ (f p) := by
        have : ((p + 1 : ℕ) : ℚ) = ((2 ^ (f p + 1) : ℕ) : ℚ) := by exact_mod_cast hk
        push_cast [pow_succ'] at this
        linarith
      have h2ge : (2 : ℚ) ≤ (2 : ℚ) ^ (f p) := by
        have : 2 ^ 1 ≤ 2 ^ (f p) := Nat.pow_le_pow_right (by norm_num) (by omega)
        exact_mod_cast this
      have hp1sub : (p : ℚ) - 1 = 2 * ((2 : ℚ) ^ (f p) - 1) := by linarith
      rw [hp1Q, hp1sub]
      have hne : ((2 : ℚ) ^ (f p) - 1) ≠ 0 := by linarith
      field_simp [hne]
    rw [hprod_img]
    set N := (L0.image f).sup id + 4
    have hsub : L0.image f ⊆ Finset.Icc 4 N := by
      intro k hk
      rw [Finset.mem_image] at hk
      obtain ⟨p, hp, rfl⟩ := hk
      rw [Finset.mem_Icc]
      refine ⟨(hf_spec p hp).1, ?_⟩
      have hle : f p ≤ (L0.image f).sup id := Finset.le_sup (f := id) (Finset.mem_image_of_mem f hp)
      omega
    calc ∏ k ∈ L0.image f, ((2 : ℚ) ^ k / ((2 : ℚ) ^ k - 1))
        ≤ ∏ k ∈ Finset.Icc 4 N, ((2 : ℚ) ^ k / ((2 : ℚ) ^ k - 1)) := by
          rw [← Finset.prod_sdiff hsub]
          have hge1 : 1 ≤ ∏ k ∈ Finset.Icc 4 N \ L0.image f, ((2 : ℚ) ^ k / ((2 : ℚ) ^ k - 1)) := by
            apply Finset.one_le_prod
            intro k hk
            have hk4 : 4 ≤ k := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp hk).1).1
            have h2k : (2 : ℚ) ≤ (2 : ℚ) ^ k := by
              have : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
              exact_mod_cast this
            rw [one_le_div (by linarith)]
            linarith
          have hnonneg : 0 ≤ ∏ k ∈ L0.image f, ((2 : ℚ) ^ k / ((2 : ℚ) ^ k - 1)) := by
            apply Finset.prod_nonneg
            intro k hk
            have hk4 : 4 ≤ k := (Finset.mem_Icc.mp (hsub hk)).1
            have h2k : (2 : ℚ) ≤ (2 : ℚ) ^ k := by
              have : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
              exact_mod_cast this
            have : (0 : ℚ) < (2 : ℚ) ^ k - 1 := by linarith
            positivity
          nlinarith
      _ ≤ 8 / 7 := prod_two_pow_bound N
  -- Step 4: Contradiction: 25/17 <= 80/63
  have hL0_nonneg : 0 ≤ ∏ p ∈ L0, (((p : ℚ) + 1) / ((p : ℚ) - 1)) := by
    apply Finset.prod_nonneg
    intro p hp
    have hp2 : (2 : ℚ) ≤ p := by exact_mod_cast (hP p (hP'sub (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1)).1.two_le
    have : (0 : ℚ) < (p : ℚ) - 1 := by linarith
    positivity
  have hfinal : (25 / 17 : ℚ) ≤ (10 / 9 : ℚ) * (8 / 7 : ℚ) := by
    calc (25 / 17 : ℚ)
        ≤ ∏ p ∈ P', (((p : ℚ) + 1) / (p : ℚ)) := hlower
      _ ≤ ∏ p ∈ L, (((p : ℚ) + 1) / ((p : ℚ) - 1)) := htele
      _ = (∏ p ∈ L5, (((p : ℚ) + 1) / ((p : ℚ) - 1))) *
          (∏ p ∈ L0, (((p : ℚ) + 1) / ((p : ℚ) - 1))) := hLsplit
      _ ≤ (10 / 9 : ℚ) * (8 / 7 : ℚ) :=
          mul_le_mul hL5_bound hL0_bound hL0_nonneg (by norm_num)
  norm_num at hfinal

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H1_R1.H2 := by
  rintro ⟨A1, h1⟩ ⟨A2, h2⟩
  refine ⟨A1 + A2, fun n h hS he h43 hm hd971 => ?_⟩
  obtain ⟨hP, h5, E⟩ := setup h hS
  rw [he] at E
  have h3P : 3 ∈ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({5} : Finset ℕ)) :=
    three_mem hP h5 E hm (by omega)
  have h3n : 3 ∣ n := (Nat.mem_primeFactors.mp (Finset.mem_erase.mp (Finset.mem_filter.mp h3P).1).2).2.1
  have hd13 : ∀ d : ℕ, d.Prime → d ≠ 2 → d ∣ padicValNat 2 n → 971 ≤ d ∧ (d % 8 = 1 ∨ d % 8 = 3) := by
    intro d hd hd2 hda
    have hge := hd971 d hd hd2 hda
    refine ⟨hge, ?_⟩
    have hdo : d % 2 = 1 := hd.eq_two_or_odd.resolve_left hd2
    rcases (by omega : d % 8 = 1 ∨ d % 8 = 3 ∨ d % 8 = 5 ∨ d % 8 = 7) with h8 | h8 | h8 | h8
    · exact Or.inl h8
    · exact Or.inr h8
    · exact (even_mod8 hP h5 E hm hd hd2 (by omega) hda (Or.inl h8)).elim
    · exact (even_mod8 hP h5 E hm hd hd2 (by omega) hda (Or.inr h8)).elim
  by_cases hex : ∃ d : ℕ, d.Prime ∧ d ≠ 2 ∧ d ∣ padicValNat 2 n ∧ d % 8 = 3
  · have := h2 n h hS he h43 hm h3n hd13 hex
    omega
  · have hd1 : ∀ d : ℕ, d.Prime → d ≠ 2 → d ∣ padicValNat 2 n → 971 ≤ d ∧ d % 8 = 1 := by
      intro d hd hd2 hda
      obtain ⟨hge, h8⟩ := hd13 d hd hd2 hda
      refine ⟨hge, h8.resolve_right (fun h3 => hex ⟨d, hd, hd2, hda, h3⟩)⟩
    have := h1 n h hS he h43 hm h3n hd1
    omega

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H1_R1_H2_R1
