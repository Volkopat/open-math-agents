import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H3.R1
-- Credit: @adammcarter
-- Splits step H3 of Erdos1052.erdos_1052.R1.H2.R1.H1.R1 (the 2-adic valuation is bounded over the
-- unitary perfect numbers with at least two repeated odd primes whose set S of repeated odd primes
-- is not admissible) by the 3-ledger: how often 3 divides n and where its factors of 3 come from.
-- Proving the four H proves the step.
--
-- Notation: n unitary perfect, a = padicValNat 2 n, e(q) = n.factorization q, S = the repeated odd
-- primes (q prime, q odd, q^2 | n).  Balance equation: the product over the primes q of n of
-- (1 + q^e(q)) is 2n.  A SOURCE of 3 is a prime q of n with 3 | 1 + q^e(q); for q = 2 this means
-- a odd, for an odd q it means q = 2 mod 3 and e(q) odd.  Every 3 dividing 2n comes from a source.
--
-- PROVED BELOW, no hypothesis needed (for any set S, any number of repeated primes):
--   (1) 3 simple (3 divides n exactly once) and a odd (branch_odd): 2^a + 1 is the only source,
--       so 3 does not divide a (else 9 | 2^a + 1); no simple prime is 2 mod 3; every z in S with
--       z = 2 mod 3 has even exponent; and for every prime d = 2 mod 3 dividing a, (2^d + 1)/3 is
--       2 mod 3, so it has a prime factor r = 2 mod 3, and r must be a REPEATED prime: some r in S
--       with r = 2 mod 3 divides 2^d + 1.
--   (2) 3 simple and a even (branch_even): exactly one odd prime q of n with q = 2 mod 3 has odd
--       exponent (it is the unique source); q is not 8 mod 9 and 3 does not divide e(q); and if
--       e(q) = 5 mod 6 then (q^e + 1)/(q + 1) is 2 mod 3 and gives a prime r in S, r different
--       from q, r = 2 mod 3, r | 1 + q^e(q).
--   (3) 3 does not divide n (branch_none): a is even and at least 2; every simple odd prime is
--       1 mod 3; every prime q = 2 mod 3 of n has even exponent; some z in S with z = 2 mod 3
--       divides 2^a + 1; the prime Fermat numbers are forced into S (a = 2 mod 4 gives 5 in S,
--       a = 4 mod 8 gives 17, a = 8 mod 16 gives 257, a = 16 mod 32 gives 65537); and n has an
--       odd number of distinct prime factors (reduce the balance equation mod 3).
--
-- H1 (OPEN): 3 is a repeated prime (3 in S).
-- H2 (OPEN): 3 simple, a odd, with the conditions (1).
-- H3 (OPEN): 3 simple, a even, with the conditions (2).
-- H4 (OPEN): 3 does not divide n, with the conditions (3).
-- Each H keeps the parent conditions (at least two repeated odd primes, S not admissible).
-- No known unitary perfect number has two repeated odd primes; the lemmas are stated for any S
-- and hold on 6, 60, 90, 87360 and Wall's number.

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 (prod_eq_two_mul prod_primeFactors_pow_self
  two_dvd_of_isUnitaryPerfect exists_quot_mod one_add_pow_dvd_of_odd_mul three_dvd_two_pow_add_one)
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1 (exists_prime_mod3)

-- H1: 3 is one of the repeated odd primes.
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) → 2 ≤ S.card →
    ¬ ((∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) ∧
      ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097) →
    3 ∈ S →
    padicValNat 2 n ≤ A

-- H2: 3 divides n exactly once and a is odd, with the proved conditions (1) of the header.
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) → 2 ≤ S.card →
    ¬ ((∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) ∧
      ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097) →
    n.factorization 3 = 1 → padicValNat 2 n % 2 = 1 → padicValNat 2 n % 3 ≠ 0 →
    (∀ p ∈ n.primeFactors, p ≠ 2 → n.factorization p = 1 → p % 3 ≠ 2) →
    (∀ z ∈ S, z % 3 = 2 → n.factorization z % 2 = 0) →
    (∀ d : ℕ, d.Prime → d ∣ padicValNat 2 n → d % 3 = 2 → ∃ r ∈ S, r % 3 = 2 ∧ r ∣ 2 ^ d + 1) →
    padicValNat 2 n ≤ A

-- H3: 3 divides n exactly once and a is even, with the proved conditions (2) of the header.
def H3 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) → 2 ≤ S.card →
    ¬ ((∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) ∧
      ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097) →
    n.factorization 3 = 1 → padicValNat 2 n % 2 = 0 →
    (∃ q ∈ n.primeFactors, q % 3 = 2 ∧ n.factorization q % 2 = 1 ∧ q % 9 ≠ 8 ∧
      n.factorization q % 3 ≠ 0 ∧
      (n.factorization q % 6 = 5 → ∃ r ∈ S, r ≠ q ∧ r % 3 = 2 ∧ r ∣ 1 + q ^ n.factorization q) ∧
      ∀ q' ∈ n.primeFactors, q' % 3 = 2 → n.factorization q' % 2 = 1 → q' = q) →
    padicValNat 2 n ≤ A

-- H4: 3 does not divide n, with the proved conditions (3) of the header.
def H4 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) → 2 ≤ S.card →
    ¬ ((∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) ∧
      ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097) →
    ¬ 3 ∣ n → padicValNat 2 n % 2 = 0 → 2 ≤ padicValNat 2 n →
    (∀ p ∈ n.primeFactors, p ≠ 2 → n.factorization p = 1 → p % 3 = 1) →
    (∀ q ∈ n.primeFactors, q % 3 = 2 → n.factorization q % 2 = 0) →
    (∃ z ∈ S, z % 3 = 2 ∧ z ∣ 2 ^ padicValNat 2 n + 1) →
    (padicValNat 2 n % 4 = 2 → 5 ∈ S) → (padicValNat 2 n % 8 = 4 → 17 ∈ S) →
    (padicValNat 2 n % 16 = 8 → 257 ∈ S) → (padicValNat 2 n % 32 = 16 → 65537 ∈ S) →
    n.primeFactors.card % 2 = 1 →
    padicValNat 2 n ≤ A

-- Section 1. Sources in the balance equation.

theorem fact2_eq (n : ℕ) : n.factorization 2 = padicValNat 2 n :=
  Nat.factorization_def n Nat.prime_two

theorem fact_pos {n p : ℕ} (hp : p ∈ n.primeFactors) : 1 ≤ n.factorization p := by
  have h : p ∈ n.factorization.support := by rwa [Nat.support_factorization]
  have := Finsupp.mem_support_iff.mp h
  omega

theorem cop2 {c : ℕ} (hc : c.Prime) (hc2 : c ≠ 2) : Nat.Coprime c 2 :=
  (Nat.coprime_primes hc Nat.prime_two).mpr hc2

theorem dvd_of_dvd_two_mul {n c : ℕ} (hc : Nat.Coprime c 2) (h : c ∣ 2 * n) : c ∣ n :=
  hc.dvd_of_dvd_mul_left h

-- A divisor of one factor 1 + q^e(q) divides 2n.
theorem dvd_two_mul_of_src {n q c : ℕ} (h : Erdos1052.IsUnitaryPerfect n) (hq : q ∈ n.primeFactors)
    (hc : c ∣ 1 + q ^ n.factorization q) : c ∣ 2 * n := by
  rw [← prod_eq_two_mul h]
  exact hc.trans (Finset.dvd_prod_of_mem (fun p => 1 + p ^ n.factorization p) hq)

-- Two different sources of c give c * c dividing 2n.
theorem two_src {n q1 q2 c : ℕ} (h : Erdos1052.IsUnitaryPerfect n) (hq1 : q1 ∈ n.primeFactors)
    (hq2 : q2 ∈ n.primeFactors) (hne : q1 ≠ q2)
    (h1 : c ∣ 1 + q1 ^ n.factorization q1) (h2 : c ∣ 1 + q2 ^ n.factorization q2) :
    c * c ∣ 2 * n := by
  rw [← prod_eq_two_mul h, ← Finset.mul_prod_erase _ _ hq1,
    ← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨hne.symm, hq2⟩), ← mul_assoc]
  exact Dvd.dvd.mul_right (mul_dvd_mul h1 h2) _

theorem le_fact_of_sq {n c : ℕ} (hn : n ≠ 0) (hc : c.Prime) (hc2 : c ≠ 2) (h : c * c ∣ 2 * n) :
    2 ≤ n.factorization c := by
  have hcop : Nat.Coprime (c * c) 2 := Nat.Coprime.mul (cop2 hc hc2) (cop2 hc hc2)
  have h' : c ^ 2 ∣ n := by rw [sq]; exact hcop.dvd_of_dvd_mul_left h
  exact (hc.pow_dvd_iff_le_factorization hn).mp h'

-- Section 2. Powers mod 3.

theorem two_pow_even (k : ℕ) : 2 ^ (2 * k) % 3 = 1 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add, Nat.mul_mod, ih]
    norm_num

theorem pmod_two_even {q e : ℕ} (hq : q % 3 = 2) (he : e % 2 = 0) : q ^ e % 3 = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, e = 2 * k := ⟨e / 2, by omega⟩
  rw [Nat.pow_mod, hq]
  exact two_pow_even k

theorem pmod_two_odd {q e : ℕ} (hq : q % 3 = 2) (he : e % 2 = 1) : q ^ e % 3 = 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, e = 2 * k + 1 := ⟨e / 2, by omega⟩
  rw [Nat.pow_mod, hq, pow_succ, Nat.mul_mod, two_pow_even k]

theorem pmod_one {q e : ℕ} (hq : q % 3 = 1) : q ^ e % 3 = 1 := by
  rw [Nat.pow_mod, hq, one_pow]
  norm_num

-- Section 3. The three branches.

theorem branch_odd {n : ℕ} {S : Finset ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) (h3 : n.factorization 3 = 1)
    (ha : padicValNat 2 n % 2 = 1) :
    padicValNat 2 n % 3 ≠ 0 ∧
    (∀ p ∈ n.primeFactors, p ≠ 2 → n.factorization p = 1 → p % 3 ≠ 2) ∧
    (∀ z ∈ S, z % 3 = 2 → n.factorization z % 2 = 0) ∧
    (∀ d : ℕ, d.Prime → d ∣ padicValNat 2 n → d % 3 = 2 → ∃ r ∈ S, r % 3 = 2 ∧ r ∣ 2 ^ d + 1) := by
  have hn : n ≠ 0 := h.2.ne'
  have h2pf : 2 ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two, two_dvd_of_isUnitaryPerfect h, hn⟩
  rw [← fact2_eq n] at ha ⊢
  have h3src : 3 ∣ 1 + 2 ^ n.factorization 2 := by
    rw [add_comm]; exact three_dvd_two_pow_add_one ha
  have huniq : ∀ q ∈ n.primeFactors, q ≠ 2 → ¬ 3 ∣ 1 + q ^ n.factorization q := by
    intro q hq hq2 hd
    have := le_fact_of_sq hn Nat.prime_three (by norm_num) (two_src h h2pf hq (Ne.symm hq2) h3src hd)
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h0
    have h6 : n.factorization 2 % (2 * 3) = 3 := by omega
    have h9 : 3 * 3 ∣ 1 + 2 ^ n.factorization 2 :=
      calc 3 * 3 = 1 + 2 ^ 3 := by norm_num
        _ ∣ 1 + 2 ^ n.factorization 2 := one_add_pow_dvd_of_odd_mul h6
    have := le_fact_of_sq hn Nat.prime_three (by norm_num) (dvd_two_mul_of_src h h2pf h9)
    omega
  · intro p hp hp2 hp1 hp3
    apply huniq p hp hp2
    rw [hp1, pow_one]
    omega
  · intro z hz hz3
    have hzp := (hS z).mp hz
    have hzpf : z ∈ n.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hzp.1, (dvd_pow_self z (by norm_num)).trans hzp.2.2, hn⟩
    by_contra hodd
    apply huniq z hzpf hzp.2.1
    have := pmod_two_odd (e := n.factorization z) hz3 (by omega)
    omega
  · intro d hd hdm hd3
    have hd2 : d ≠ 2 := by
      rintro rfl
      omega
    have hdodd : d % 2 = 1 := Nat.odd_iff.mp (hd.eq_two_or_odd'.resolve_left hd2)
    obtain ⟨k, hk⟩ := hdm
    have hkodd : k % 2 = 1 := by
      have : Odd (d * k) := hk ▸ Nat.odd_iff.mpr ha
      exact Nat.odd_iff.mp (Nat.odd_mul.mp this).2
    have hmod : n.factorization 2 % (2 * d) = d := by
      obtain ⟨j, rfl⟩ : ∃ j, k = 2 * j + 1 := ⟨k / 2, by omega⟩
      have hd1 := hd.two_le
      rw [hk, show d * (2 * j + 1) = d + 2 * d * j by ring, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt (by omega)]
    obtain ⟨Q, hQ, hQm⟩ := exists_quot_mod (z := 2) (e := d) (Nat.odd_iff.mpr hdodd)
    have hQ3 : Q % 3 = 2 := by
      norm_num at hQm
      omega
    obtain ⟨r, hr, hrQ, hr3⟩ := exists_prime_mod3 Q hQ3
    have hrd : r ∣ 1 + 2 ^ d := by
      rw [hQ]
      exact Dvd.dvd.mul_left hrQ _
    have hr2 : r ≠ 2 := by
      rintro rfl
      have h2d : 2 ∣ 2 ^ d := dvd_pow_self 2 hd.ne_zero
      have : 2 ∣ 1 := (Nat.dvd_add_right h2d).mp (by rw [add_comm]; exact hrd)
      omega
    have hra : r ∣ 2 * n := dvd_two_mul_of_src h h2pf (hrd.trans (one_add_pow_dvd_of_odd_mul hmod))
    have hrn : r ∣ n := dvd_of_dvd_two_mul (cop2 hr hr2) hra
    have hrpf : r ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hr, hrn, hn⟩
    have hr1 := fact_pos hrpf
    have hfr : 2 ≤ n.factorization r := by
      by_contra hlt
      apply huniq r hrpf hr2
      rw [show n.factorization r = 1 by omega, pow_one]
      omega
    refine ⟨r, (hS r).mpr ⟨hr, hr2, (hr.pow_dvd_iff_le_factorization hn).mpr hfr⟩, hr3, ?_⟩
    rw [add_comm]
    exact hrd

theorem branch_even {n : ℕ} {S : Finset ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) (h3 : n.factorization 3 = 1)
    (ha : padicValNat 2 n % 2 = 0) :
    ∃ q ∈ n.primeFactors, q % 3 = 2 ∧ n.factorization q % 2 = 1 ∧ q % 9 ≠ 8 ∧
      n.factorization q % 3 ≠ 0 ∧
      (n.factorization q % 6 = 5 → ∃ r ∈ S, r ≠ q ∧ r % 3 = 2 ∧ r ∣ 1 + q ^ n.factorization q) ∧
      ∀ q' ∈ n.primeFactors, q' % 3 = 2 → n.factorization q' % 2 = 1 → q' = q := by
  have hn : n ≠ 0 := h.2.ne'
  rw [← fact2_eq n] at ha
  have h3pf : 3 ∈ n.primeFactors := by
    rw [← Nat.support_factorization]
    exact Finsupp.mem_support_iff.mpr (by omega)
  have h3d : 3 ∣ 2 * n := Dvd.dvd.mul_left (Nat.dvd_of_mem_primeFactors h3pf) 2
  rw [← prod_eq_two_mul h] at h3d
  obtain ⟨q, hq, hq3⟩ := (Prime.dvd_finsetProd_iff Nat.prime_three.prime _).mp h3d
  have hqp := Nat.prime_of_mem_primeFactors hq
  have hqm : q % 3 = 2 ∧ n.factorization q % 2 = 1 := by
    rcases (by omega : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2) with h0 | h1 | h2
    · have hq3' : q = 3 :=
        ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hqp).mp (Nat.dvd_of_mod_eq_zero h0)).symm
      subst hq3'
      rw [h3] at hq3
      norm_num at hq3
    · have := pmod_one (e := n.factorization q) h1
      omega
    · refine ⟨h2, ?_⟩
      by_contra he
      have := pmod_two_even (e := n.factorization q) h2 (by omega)
      omega
  have huniq : ∀ q1 ∈ n.primeFactors, ∀ q2 ∈ n.primeFactors, q1 ≠ q2 →
      3 ∣ 1 + q1 ^ n.factorization q1 → 3 ∣ 1 + q2 ^ n.factorization q2 → False := by
    intro q1 hq1 q2 hq2 hne h1 h2
    have := le_fact_of_sq hn Nat.prime_three (by norm_num) (two_src h hq1 hq2 hne h1 h2)
    omega
  have hsrc : ∀ q' ∈ n.primeFactors, q' % 3 = 2 → n.factorization q' % 2 = 1 →
      3 ∣ 1 + q' ^ n.factorization q' := by
    intro q' _ hq'3 hq'o
    have := pmod_two_odd (e := n.factorization q') hq'3 hq'o
    omega
  have hq2 : q ≠ 2 := by
    rintro rfl
    omega
  have hqodd : q % 2 = 1 := Nat.odd_iff.mp (hqp.eq_two_or_odd'.resolve_left hq2)
  obtain ⟨Q, hQ, hQm⟩ := exists_quot_mod (z := q) (e := n.factorization q) (Nat.odd_iff.mpr hqm.2)
  have h3q : 3 ∣ q + 1 := by omega
  have hQ3 : Q % 3 = n.factorization q % 3 := Nat.ModEq.of_dvd h3q hQm
  have hQ2 : Q % 2 = n.factorization q % 2 := Nat.ModEq.of_dvd (by omega : 2 ∣ q + 1) hQm
  refine ⟨q, hq, hqm.1, hqm.2, ?_, ?_, ?_, ?_⟩
  · intro h8
    have h9 : 3 * 3 ∣ 1 + q ^ n.factorization q := by
      rw [hQ]
      exact Dvd.dvd.mul_right (by omega : 3 * 3 ∣ q + 1) _
    have := le_fact_of_sq hn Nat.prime_three (by norm_num) (dvd_two_mul_of_src h hq h9)
    omega
  · intro h0
    have h9 : 3 * 3 ∣ 1 + q ^ n.factorization q := by
      rw [hQ]
      exact mul_dvd_mul h3q (Nat.dvd_of_mod_eq_zero (by omega))
    have := le_fact_of_sq hn Nat.prime_three (by norm_num) (dvd_two_mul_of_src h hq h9)
    omega
  · intro h5
    have hQ32 : Q % 3 = 2 := by omega
    obtain ⟨r, hr, hrQ, hr3⟩ := exists_prime_mod3 Q hQ32
    have hrd : r ∣ 1 + q ^ n.factorization q := by
      rw [hQ]
      exact Dvd.dvd.mul_left hrQ _
    have hr2 : r ≠ 2 := by
      rintro rfl
      omega
    have hrq : r ≠ q := by
      intro hrq
      have he1 := fact_pos hq
      have h1 : q ∣ q ^ n.factorization q := dvd_pow_self q (by omega)
      have h1' : q ∣ 1 + q ^ n.factorization q := hrq ▸ hrd
      have : q ∣ 1 := (Nat.dvd_add_right h1).mp (by rw [add_comm]; exact h1')
      exact hqp.one_lt.ne' (Nat.dvd_one.mp this)
    have hrn : r ∣ n := dvd_of_dvd_two_mul (cop2 hr hr2) (dvd_two_mul_of_src h hq hrd)
    have hrpf : r ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hr, hrn, hn⟩
    have hfr : 2 ≤ n.factorization r := by
      by_contra hlt
      have hr1 : n.factorization r = 1 := by
        have := fact_pos hrpf
        omega
      exact huniq q hq r hrpf (Ne.symm hrq) (hsrc q hq hqm.1 hqm.2)
        (by rw [hr1, pow_one]; omega)
    exact ⟨r, (hS r).mpr ⟨hr, hr2, (hr.pow_dvd_iff_le_factorization hn).mpr hfr⟩, hrq, hr3, hrd⟩
  · intro q' hq' hq'3 hq'o
    by_contra hne
    exact huniq q hq q' hq' (Ne.symm hne) (hsrc q hq hqm.1 hqm.2) (hsrc q' hq' hq'3 hq'o)

theorem branch_none {n : ℕ} {S : Finset ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) (h3 : ¬ 3 ∣ n) :
    padicValNat 2 n % 2 = 0 ∧ 2 ≤ padicValNat 2 n ∧
    (∀ p ∈ n.primeFactors, p ≠ 2 → n.factorization p = 1 → p % 3 = 1) ∧
    (∀ q ∈ n.primeFactors, q % 3 = 2 → n.factorization q % 2 = 0) ∧
    (∃ z ∈ S, z % 3 = 2 ∧ z ∣ 2 ^ padicValNat 2 n + 1) ∧
    (padicValNat 2 n % 4 = 2 → 5 ∈ S) ∧ (padicValNat 2 n % 8 = 4 → 17 ∈ S) ∧
    (padicValNat 2 n % 16 = 8 → 257 ∈ S) ∧ (padicValNat 2 n % 32 = 16 → 65537 ∈ S) ∧
    n.primeFactors.card % 2 = 1 := by
  have hn : n ≠ 0 := h.2.ne'
  have h2pf : 2 ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two, two_dvd_of_isUnitaryPerfect h, hn⟩
  rw [← fact2_eq n]
  have hno : ∀ q ∈ n.primeFactors, ¬ 3 ∣ 1 + q ^ n.factorization q := fun q hq hd =>
    h3 (dvd_of_dvd_two_mul (by norm_num) (dvd_two_mul_of_src h hq hd))
  have hm1 := fact_pos h2pf
  have hmeven : n.factorization 2 % 2 = 0 := by
    by_contra ho
    exact hno 2 h2pf (by rw [add_comm]; exact three_dvd_two_pow_add_one (by omega))
  have hq2 : ∀ q ∈ n.primeFactors, q % 3 = 2 → n.factorization q % 2 = 0 := by
    intro q hq hq3
    by_contra ho
    have := pmod_two_odd (e := n.factorization q) hq3 (by omega)
    exact hno q hq (by omega)
  have hmemS : ∀ z, z.Prime → z ≠ 2 → z % 3 = 2 → z ∣ 1 + 2 ^ n.factorization 2 → z ∈ S := by
    intro z hz hz2 hz3 hzd
    have hzn : z ∣ n := dvd_of_dvd_two_mul (cop2 hz hz2) (dvd_two_mul_of_src h h2pf hzd)
    have hzpf : z ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hz, hzn, hn⟩
    have h1 := hq2 z hzpf hz3
    have h2 := fact_pos hzpf
    exact (hS z).mpr ⟨hz, hz2, (hz.pow_dvd_iff_le_factorization hn).mpr (by omega)⟩
  have hG : ∀ p ∈ n.primeFactors, p ^ n.factorization p % 3 = 1 := by
    intro p hp
    have h0 : p % 3 ≠ 0 := fun h0 =>
      h3 ((Nat.dvd_of_mod_eq_zero h0).trans (Nat.dvd_of_mem_primeFactors hp))
    rcases (by omega : p % 3 = 1 ∨ p % 3 = 2) with h1 | h2
    · exact pmod_one h1
    · exact pmod_two_even h2 (hq2 p hp h2)
  refine ⟨hmeven, by omega, ?_, hq2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp hp2 hp1
    have h0 : p % 3 ≠ 0 := fun h0 =>
      h3 ((Nat.dvd_of_mod_eq_zero h0).trans (Nat.dvd_of_mem_primeFactors hp))
    by_contra hne
    exact hno p hp (by rw [hp1, pow_one]; omega)
  · have h2m : (2 ^ n.factorization 2 + 1) % 3 = 2 := by
      have := pmod_two_even (q := 2) (e := n.factorization 2) (by norm_num) hmeven
      omega
    obtain ⟨z, hz, hzd, hz3⟩ := exists_prime_mod3 _ h2m
    have hz2 : z ≠ 2 := by
      rintro rfl
      have h2d : 2 ∣ 2 ^ n.factorization 2 := dvd_pow_self 2 (by omega)
      have : 2 ∣ 1 := (Nat.dvd_add_right h2d).mp hzd
      omega
    exact ⟨z, hmemS z hz hz2 hz3 (by rw [add_comm]; exact hzd), hz3, hzd⟩
  · intro h4
    exact hmemS 5 (by norm_num) (by norm_num) (by norm_num)
      (calc 5 = 1 + 2 ^ 2 := by norm_num
        _ ∣ 1 + 2 ^ n.factorization 2 := one_add_pow_dvd_of_odd_mul (by omega))
  · intro h4
    exact hmemS 17 (by norm_num) (by norm_num) (by norm_num)
      (calc 17 = 1 + 2 ^ 4 := by norm_num
        _ ∣ 1 + 2 ^ n.factorization 2 := one_add_pow_dvd_of_odd_mul (by omega))
  · intro h4
    exact hmemS 257 (by norm_num) (by norm_num) (by norm_num)
      (calc 257 = 1 + 2 ^ 8 := by norm_num
        _ ∣ 1 + 2 ^ n.factorization 2 := one_add_pow_dvd_of_odd_mul (by omega))
  · intro h4
    exact hmemS 65537 (by norm_num) (by norm_num) (by norm_num)
      (calc 65537 = 1 + 2 ^ 16 := by norm_num
        _ ∣ 1 + 2 ^ n.factorization 2 := one_add_pow_dvd_of_odd_mul (by omega))
  · have hF : ∀ p ∈ n.primeFactors, (1 + p ^ n.factorization p) % 3 = 2 := by
      intro p hp
      have := hG p hp
      omega
    have e1 : (∏ p ∈ n.primeFactors, (1 + p ^ n.factorization p)) % 3 = 2 ^ n.primeFactors.card % 3 := by
      rw [Finset.prod_nat_mod, Finset.prod_congr rfl hF, Finset.prod_const]
    have e2 : n % 3 = 1 := by
      rw [← prod_primeFactors_pow_self hn, Finset.prod_nat_mod, Finset.prod_congr rfl hG,
        Finset.prod_const_one]
      norm_num
    rw [prod_eq_two_mul h] at e1
    by_contra hc
    have := pmod_two_even (q := 2) (e := n.primeFactors.card) (by norm_num) (by omega)
    omega

-- Section 4. The step.

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1.H3 := by
  rintro ⟨A1, h1⟩ ⟨A2, h2⟩ ⟨A3, h3⟩ ⟨A4, h4⟩
  refine ⟨A1 + A2 + A3 + A4, fun n h S hS hc hna => ?_⟩
  have hn : n ≠ 0 := h.2.ne'
  by_cases h3S : 3 ∈ S
  · have := h1 n h S hS hc hna h3S
    omega
  by_cases h3n : 3 ∣ n
  · have hf3 : n.factorization 3 = 1 := by
      have h1' := Nat.prime_three.factorization_pos_of_dvd hn h3n
      have : ¬ 2 ≤ n.factorization 3 := fun h2' => h3S ((hS 3).mpr ⟨Nat.prime_three, by norm_num,
        (Nat.prime_three.pow_dvd_iff_le_factorization hn).mpr h2'⟩)
      omega
    rcases Nat.mod_two_eq_zero_or_one (padicValNat 2 n) with he | ho
    · have := h3 n h S hS hc hna hf3 he (branch_even h hS hf3 he)
      omega
    · obtain ⟨c1, c2, c3, c4⟩ := branch_odd h hS hf3 ho
      have := h2 n h S hS hc hna hf3 ho c1 c2 c3 c4
      omega
  · obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := branch_none h hS h3n
    have := h4 n h S hS hc hna h3n c1 c2 c3 c4 c5 c6 c7 c8 c9 c10
    omega

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1
