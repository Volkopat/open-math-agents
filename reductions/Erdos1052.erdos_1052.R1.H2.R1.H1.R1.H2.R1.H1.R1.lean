import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1

/-! A reduction file for Erdős Problem 1052 (see the comment below). -/

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H1.R1
-- Credit: @adammcarter
-- Splits step H1 of Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1 (5 the only repeated odd prime of the
-- unitary perfect number n, 5^2 exactly dividing n, a = v2(n) >= 43) by a mod 4, with new class
-- kills built in.  Proving the three H proves the step.
--
-- Notation: P = the simple odd primes of n, (E) (2^a + 1) * 26 * prod (p + 1) = 2^(a+1) * 25 * prod p.
-- Every odd prime other than 5 occurs exactly once on the left of (E) if it lies in P and not at
-- all otherwise; 5 occurs exactly twice.  26 = 2 * 13 forces 13 in P, and 14 forces 7.  When a is
-- an odd multiple of d, 2^d + 1 divides 2^a + 1, so every prime factor of 2^d + 1 other than 5 is in P.
--
-- PROVED BELOW (no hypothesis needed):
--   odd_mod3: a odd, d a prime factor of a with d = 2 mod 3 is impossible.  (2^d + 1)/3 is 2 mod 3,
--     so it has a prime factor c = 2 mod 3; c is in P and 3 divides both 2^a + 1 and c + 1.
--   odd_sieve: a odd, d a prime factor of a with d = 1 mod 3 and 43 <= d <= 1776 is impossible.
--   even_sieve: a = 2 mod 4, d an odd prime factor of a with 101 <= d <= 970 is impossible
--     (class 2d; 5 divides 2^(2d) + 1, so one more p with 5 | p + 1 fills the 5-ledger).
--   fermat20: v2(a) is not r for r in R20 = {36, 38, 39, 42, 52, 55, 58, 62, 63, 66, 71, 73, 77, 81, 91, 93, 99, 117, 125, 144, 147, 150, 201, 207, 215, 226, 228, 250} (a known prime factor
--     k 2^(r+2) + 1 of the Fermat number 2^(2^r) + 1 starts a forced chain).
--   Each class d has its own lemma c20_d (c20_f for Fermat levels): a chain of forced simple
--   primes from the prime factors of 2^d + 1 (or from 13 and 7) ending in a prime with two
--   sources, a square dividing some p + 1 or 2^d + 1, or 5^3 dividing the left side of (E).
--   295 class lemmas (129 odd primes, 138 classes 2d, 28 Fermat levels), 229 Lucas certificates.
--
-- H1 (OPEN): a odd, every prime factor of a at least 1777 and 1 mod 3.
-- H2 (OPEN): a = 2 mod 4, every odd prime factor of a at least 971.
-- H3 (OPEN): 4 | a, v2(a) not in the parent's set R5 and not in R20.
-- No known unitary perfect number has 5^2 exactly dividing it with 5 its only repeated odd prime.

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H1_R1

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1 hiding H1 H2 H3 H4 main

-- H1: a = v2(n) is bounded over the unitary perfect numbers whose only repeated odd prime is 5,
-- with 5^2 exactly dividing n, a odd, a >= 43, and every prime factor of a at least 1777 and 1 mod 3.
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 5) → n.factorization 5 = 2 →
    43 ≤ padicValNat 2 n → padicValNat 2 n % 2 = 1 →
    (∀ d : ℕ, d.Prime → d ∣ padicValNat 2 n → 1777 ≤ d ∧ d % 3 = 1) →
    padicValNat 2 n ≤ A

-- H2: the same with a = 2 mod 4 and every odd prime factor of a at least 971.
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 5) → n.factorization 5 = 2 →
    43 ≤ padicValNat 2 n → padicValNat 2 n % 4 = 2 →
    (∀ d : ℕ, d.Prime → d ≠ 2 → d ∣ padicValNat 2 n → 971 ≤ d) →
    padicValNat 2 n ≤ A

-- H3: the same with 4 dividing a, v2(a) not in R5 (the parent's set) and not in the new set R20.
def H3 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 5) → n.factorization 5 = 2 →
    43 ≤ padicValNat 2 n → padicValNat 2 n % 4 = 0 →
    (∀ r ∈ ({2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 25, 26, 27, 28, 29, 30, 31, 32} : Finset ℕ),
      padicValNat 2 n % 2 ^ (r + 1) ≠ 2 ^ r) →
    (∀ r ∈ ({36, 38, 39, 42, 52, 55, 58, 62, 63, 66, 71, 73, 77, 81, 91, 93, 99, 117, 125, 144, 147, 150, 201, 207, 215, 226, 228, 250} : Finset ℕ),
      padicValNat 2 n % 2 ^ (r + 1) ≠ 2 ^ r) →
    padicValNat 2 n ≤ A


-- a odd and d a prime factor of a with d = 2 mod 3: (2^d + 1)/3 = 2 mod 3 has a prime factor
-- c = 2 mod 3; c is a simple prime of n and 3 divides both 2^a + 1 and c + 1 (two sources of 3).
theorem odd_mod3 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hm : m % 2 = 1) {d : ℕ} (hd : d.Prime) (hda : d ∣ m) (h3 : d % 3 = 2) : False := by
  have hnz : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨-, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have hdo : Odd d := by
    rcases hd.eq_two_or_odd with h | h
    · subst h
      omega
    · exact Nat.odd_iff.mpr h
  have hD : 1 + 2 ^ d ∣ 2 ^ m + 1 := by
    rw [add_comm (2 ^ m)]
    exact one_add_pow_dvd_of_odd_mul (mod_of_dvd_odd hda hm)
  obtain ⟨Q, hQ, hQm⟩ := exists_quot_mod (z := 2) (e := d) hdo
  have hQ3 : Q % 3 = 2 := by
    have : Q % (2 + 1) = d % (2 + 1) := hQm
    norm_num at this
    omega
  obtain ⟨c, hc, hcQ, hc3⟩ := exists_prime_mod3 Q hQ3
  have hcd : c ∣ 2 ^ m + 1 := by
    have h1 : c ∣ (2 + 1) * Q := hcQ.mul_left _
    rw [← hQ] at h1
    exact h1.trans hD
  have hc2 : c ≠ 2 := by
    rintro rfl
    have h2 : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
    have : 2 ∣ 1 := (Nat.dvd_add_right h2).mp hcd
    omega
  have hc5 : c ≠ 5 := by
    rintro rfl
    exact five_not_dvd_of_odd hm hcd
  have gc : c ∈ P := S2 c hc hc2 (hnz hc5) hcd
  exact S4 3 (by norm_num) (by norm_num) (hnz (by norm_num)) (three_dvd_two_pow_add_one hm) c gc
    (Nat.dvd_of_mod_eq_zero (by omega))

theorem prime_2932031007403 : Nat.Prime 2932031007403 := by
  refine lucas_primality 2932031007403 (3 : ZMod 2932031007403) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 2932031007403 - 1 = [2 ^ 1, 3 ^ 1, 7 ^ 2, 43 ^ 1, 127 ^ 1, 337 ^ 1, 5419 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_768614336404564651 : Nat.Prime 768614336404564651 := by
  refine lucas_primality 768614336404564651 (3 : ZMod 768614336404564651) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 768614336404564651 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 2, 7 ^ 1, 11 ^ 1, 13 ^ 1, 31 ^ 1, 41 ^ 1, 61 ^ 1, 151 ^ 1, 331 ^ 1, 1321 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_201487636602438195784363 : Nat.Prime 201487636602438195784363 := by
  refine lucas_primality 201487636602438195784363 (3 : ZMod 201487636602438195784363) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 201487636602438195784363 - 1 = [2 ^ 1, 3 ^ 1, 7 ^ 1, 79 ^ 1, 2731 ^ 1, 8191 ^ 1, 121369 ^ 1, 22366891 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_251906329 : Nat.Prime 251906329 := by
  refine lucas_primality 251906329 (7 : ZMod 251906329) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 251906329 - 1 = [2 ^ 3, 3 ^ 3, 83 ^ 1, 14051 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_415141630193 : Nat.Prime 415141630193 := by
  refine lucas_primality 415141630193 (3 : ZMod 415141630193) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 415141630193 - 1 = [2 ^ 4, 103 ^ 1, 251906329 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_251906329 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_104124649 : Nat.Prime 104124649 := by
  refine lucas_primality 104124649 (7 : ZMod 104124649) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 104124649 - 1 = [2 ^ 3, 3 ^ 1, 53 ^ 1, 109 ^ 1, 751 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_77158673929 : Nat.Prime 77158673929 := by
  refine lucas_primality 77158673929 (11 : ZMod 77158673929) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 77158673929 - 1 = [2 ^ 3, 3 ^ 3, 7 ^ 1, 73 ^ 1, 699053 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_56713727820156410577229101238628035243 : Nat.Prime 56713727820156410577229101238628035243 := by
  refine lucas_primality 56713727820156410577229101238628035243 (3 : ZMod 56713727820156410577229101238628035243) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 56713727820156410577229101238628035243 - 1 = [2 ^ 1, 3 ^ 2, 7 ^ 2, 19 ^ 1, 43 ^ 1, 73 ^ 1, 127 ^ 1, 337 ^ 1, 5419 ^ 1, 92737 ^ 1, 649657 ^ 1, 77158673929 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_77158673929 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_18717738334417 : Nat.Prime 18717738334417 := by
  refine lucas_primality 18717738334417 (5 : ZMod 18717738334417) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 18717738334417 - 1 = [2 ^ 4, 3 ^ 2, 11 ^ 1, 19 ^ 1, 23 ^ 1, 131 ^ 1, 151 ^ 1, 1367 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_11281292593 : Nat.Prime 11281292593 := by
  refine lucas_primality 11281292593 (5 : ZMod 11281292593) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 11281292593 - 1 = [2 ^ 4, 3 ^ 1, 163 ^ 1, 1441883 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_71925114571 : Nat.Prime 71925114571 := by
  refine lucas_primality 71925114571 (2 : ZMod 71925114571) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 71925114571 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 1, 29527 ^ 1, 81197 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_242099935645987 : Nat.Prime 242099935645987 := by
  refine lucas_primality 242099935645987 (3 : ZMod 242099935645987) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 242099935645987 - 1 = [2 ^ 1, 3 ^ 2, 11 ^ 1, 17 ^ 1, 71925114571 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_71925114571 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_33057806959 : Nat.Prime 33057806959 := by
  refine lucas_primality 33057806959 (3 : ZMod 33057806959) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 33057806959 - 1 = [2 ^ 1, 3 ^ 2, 11 ^ 1, 757 ^ 1, 220553 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_267823007376498379256993682056860433753700498963798805883563 : Nat.Prime 267823007376498379256993682056860433753700498963798805883563 := by
  refine lucas_primality 267823007376498379256993682056860433753700498963798805883563 (3 : ZMod 267823007376498379256993682056860433753700498963798805883563) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 267823007376498379256993682056860433753700498963798805883563 - 1 = [2 ^ 1, 3 ^ 2, 7 ^ 1, 19 ^ 1, 23 ^ 1, 67 ^ 1, 73 ^ 1, 89 ^ 1, 199 ^ 1, 683 ^ 1, 5347 ^ 1, 20857 ^ 1, 153649 ^ 1, 599479 ^ 1, 33057806959 ^ 1, 242099935645987 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_33057806959 | exact prime_242099935645987 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_1348959352853811313 : Nat.Prime 1348959352853811313 := by
  refine lucas_primality 1348959352853811313 (7 : ZMod 1348959352853811313) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 1348959352853811313 - 1 = [2 ^ 4, 3 ^ 2, 197 ^ 1, 3987311 ^ 1, 11925869 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_219256122131 : Nat.Prime 219256122131 := by
  refine lucas_primality 219256122131 (6 : ZMod 219256122131) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 219256122131 - 1 = [2 ^ 1, 5 ^ 1, 223 ^ 1, 293 ^ 1, 335567 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_25792643401363 : Nat.Prime 25792643401363 := by
  refine lucas_primality 25792643401363 (3 : ZMod 25792643401363) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 25792643401363 - 1 = [2 ^ 1, 3 ^ 2, 67 ^ 1, 277 ^ 1, 4703 ^ 1, 16417 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_1249678499 : Nat.Prime 1249678499 := by
  refine lucas_primality 1249678499 (6 : ZMod 1249678499) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 1249678499 - 1 = [2 ^ 1, 29 ^ 1, 307 ^ 1, 70183 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_84159375948762099254554456081 : Nat.Prime 84159375948762099254554456081 := by
  refine lucas_primality 84159375948762099254554456081 (83 : ZMod 84159375948762099254554456081) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 84159375948762099254554456081 - 1 = [2 ^ 4, 3 ^ 2, 5 ^ 1, 7 ^ 1, 13 ^ 1, 17 ^ 1, 97 ^ 1, 257 ^ 1, 421 ^ 1, 673 ^ 1, 859 ^ 1, 90841 ^ 1, 137089 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_308761441 : Nat.Prime 308761441 := by
  refine lucas_primality 308761441 (17 : ZMod 308761441) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 308761441 - 1 = [2 ^ 5, 3 ^ 1, 5 ^ 1, 13 ^ 1, 49481 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 : Nat.Prime 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 := by
  refine lucas_primality 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 (7 : ZMod 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 1, 7 ^ 1, 13 ^ 2, 17 ^ 1, 53 ^ 1, 79 ^ 1, 157 ^ 1, 241 ^ 1, 313 ^ 1, 1249 ^ 1, 1613 ^ 1, 2731 ^ 1, 3121 ^ 1, 8191 ^ 1, 21841 ^ 1, 121369 ^ 1, 858001 ^ 1, 22366891 ^ 1, 308761441 ^ 1, 84159375948762099254554456081 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_308761441 | exact prime_84159375948762099254554456081 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_131282633 : Nat.Prime 131282633 := by
  refine lucas_primality 131282633 (3 : ZMod 131282633) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 131282633 - 1 = [2 ^ 3, 13 ^ 1, 349 ^ 1, 3617 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_15012732261073 : Nat.Prime 15012732261073 := by
  refine lucas_primality 15012732261073 (5 : ZMod 15012732261073) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 15012732261073 - 1 = [2 ^ 4, 3 ^ 1, 7 ^ 1, 13 ^ 1, 379 ^ 1, 9068551 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_477572942758053959 : Nat.Prime 477572942758053959 := by
  refine lucas_primality 477572942758053959 (11 : ZMod 477572942758053959) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 477572942758053959 - 1 = [2 ^ 1, 52859 ^ 1, 153701 ^ 1, 29390981 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_176596029450915408652219208387 : Nat.Prime 176596029450915408652219208387 := by
  refine lucas_primality 176596029450915408652219208387 (5 : ZMod 176596029450915408652219208387) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 176596029450915408652219208387 - 1 = [2 ^ 1, 409 ^ 1, 761 ^ 1, 594023 ^ 1, 477572942758053959 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_477572942758053959 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_99759313 : Nat.Prime 99759313 := by
  refine lucas_primality 99759313 (7 : ZMod 99759313) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 99759313 - 1 = [2 ^ 4, 3 ^ 2, 43 ^ 1, 16111 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_53870029021 : Nat.Prime 53870029021 := by
  refine lucas_primality 53870029021 (10 : ZMod 53870029021) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 53870029021 - 1 = [2 ^ 2, 3 ^ 3, 5 ^ 1, 99759313 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_99759313 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_6224050496636423881 : Nat.Prime 6224050496636423881 := by
  refine lucas_primality 6224050496636423881 (19 : ZMod 6224050496636423881) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 6224050496636423881 - 1 = [2 ^ 3, 3 ^ 1, 5 ^ 1, 11 ^ 1, 13 ^ 1, 6733 ^ 1, 53870029021 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_53870029021 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_86937537337017568769809 : Nat.Prime 86937537337017568769809 := by
  refine lucas_primality 86937537337017568769809 (7 : ZMod 86937537337017568769809) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 86937537337017568769809 - 1 = [2 ^ 4, 3 ^ 2, 97 ^ 1, 6224050496636423881 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_6224050496636423881 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_8159927869564849092796028544559 : Nat.Prime 8159927869564849092796028544559 := by
  refine lucas_primality 8159927869564849092796028544559 (3 : ZMod 8159927869564849092796028544559) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 8159927869564849092796028544559 - 1 = [2 ^ 1, 3 ^ 1, 13 ^ 1, 1203329 ^ 1, 86937537337017568769809 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_86937537337017568769809 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_45957593887 : Nat.Prime 45957593887 := by
  refine lucas_primality 45957593887 (3 : ZMod 45957593887) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 45957593887 - 1 = [2 ^ 1, 3 ^ 1, 127 ^ 1, 4903 ^ 1, 12301 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_25644337388947 : Nat.Prime 25644337388947 := by
  refine lucas_primality 25644337388947 (2 : ZMod 25644337388947) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 25644337388947 - 1 = [2 ^ 1, 3 ^ 2, 31 ^ 1, 45957593887 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_45957593887 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_6885357560205319573060633896800918448254904729193 : Nat.Prime 6885357560205319573060633896800918448254904729193 := by
  refine lucas_primality 6885357560205319573060633896800918448254904729193 (5 : ZMod 6885357560205319573060633896800918448254904729193) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 6885357560205319573060633896800918448254904729193 - 1 = [2 ^ 3, 3 ^ 2, 457 ^ 1, 25644337388947 ^ 1, 8159927869564849092796028544559 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_25644337388947 | exact prime_8159927869564849092796028544559 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_6870297251 : Nat.Prime 6870297251 := by
  refine lucas_primality 6870297251 (2 : ZMod 6870297251) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 6870297251 - 1 = [2 ^ 1, 5 ^ 3, 53 ^ 1, 67 ^ 1, 71 ^ 1, 109 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_42994320196759 : Nat.Prime 42994320196759 := by
  refine lucas_primality 42994320196759 (6 : ZMod 42994320196759) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 42994320196759 - 1 = [2 ^ 1, 3 ^ 1, 7 ^ 1, 149 ^ 1, 6870297251 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_6870297251 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_76834966209858049526107 : Nat.Prime 76834966209858049526107 := by
  refine lucas_primality 76834966209858049526107 (3 : ZMod 76834966209858049526107) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 76834966209858049526107 - 1 = [2 ^ 1, 3 ^ 1, 463 ^ 1, 643303 ^ 1, 42994320196759 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_42994320196759 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_11107596471035777 : Nat.Prime 11107596471035777 := by
  refine lucas_primality 11107596471035777 (3 : ZMod 11107596471035777) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 11107596471035777 - 1 = [2 ^ 7, 43 ^ 2, 61 ^ 1, 15107 ^ 1, 50929 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_1311493493 : Nat.Prime 1311493493 := by
  refine lucas_primality 1311493493 (2 : ZMod 1311493493) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 1311493493 - 1 = [2 ^ 2, 17 ^ 1, 19286669 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_2622986987 : Nat.Prime 2622986987 := by
  refine lucas_primality 2622986987 (2 : ZMod 2622986987) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 2622986987 - 1 = [2 ^ 1, 1311493493 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_1311493493 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_227020551154913939039124941009 : Nat.Prime 227020551154913939039124941009 := by
  refine lucas_primality 227020551154913939039124941009 (3 : ZMod 227020551154913939039124941009) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 227020551154913939039124941009 - 1 = [2 ^ 4, 487 ^ 1, 2622986987 ^ 1, 11107596471035777 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_2622986987 | exact prime_11107596471035777 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_58421933 : Nat.Prime 58421933 := by
  refine lucas_primality 58421933 (3 : ZMod 58421933) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 58421933 - 1 = [2 ^ 2, 23 ^ 1, 635021 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_1533926272849 : Nat.Prime 1533926272849 := by
  refine lucas_primality 1533926272849 (7 : ZMod 1533926272849) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 1533926272849 - 1 = [2 ^ 4, 3 ^ 1, 547 ^ 1, 58421933 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_58421933 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_2655094158137 : Nat.Prime 2655094158137 := by
  refine lucas_primality 2655094158137 (3 : ZMod 2655094158137) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 2655094158137 - 1 = [2 ^ 3, 7 ^ 2, 25121 ^ 1, 269623 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_21240753265097 : Nat.Prime 21240753265097 := by
  refine lucas_primality 21240753265097 (3 : ZMod 21240753265097) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 21240753265097 - 1 = [2 ^ 3, 2655094158137 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_2655094158137 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_9293424294571360217 : Nat.Prime 9293424294571360217 := by
  refine lucas_primality 9293424294571360217 (3 : ZMod 9293424294571360217) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 9293424294571360217 - 1 = [2 ^ 3, 7 ^ 1, 13 ^ 1, 601 ^ 1, 21240753265097 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_21240753265097 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_16071603472405643 : Nat.Prime 16071603472405643 := by
  refine lucas_primality 16071603472405643 (5 : ZMod 16071603472405643) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 16071603472405643 - 1 = [2 ^ 1, 7 ^ 1, 19 ^ 1, 149 ^ 1, 112303 ^ 1, 3610771 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_29507463975336760549 : Nat.Prime 29507463975336760549 := by
  refine lucas_primality 29507463975336760549 (2 : ZMod 29507463975336760549) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 29507463975336760549 - 1 = [2 ^ 2, 3 ^ 3, 17 ^ 1, 16071603472405643 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_16071603472405643 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_531134351556061689883 : Nat.Prime 531134351556061689883 := by
  refine lucas_primality 531134351556061689883 (2 : ZMod 531134351556061689883) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 531134351556061689883 - 1 = [2 ^ 1, 3 ^ 2, 29507463975336760549 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_29507463975336760549 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_256314897168614389937238381983 : Nat.Prime 256314897168614389937238381983 := by
  refine lucas_primality 256314897168614389937238381983 (5 : ZMod 256314897168614389937238381983) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 256314897168614389937238381983 - 1 = [2 ^ 1, 7 ^ 1, 34470011 ^ 1, 531134351556061689883 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_531134351556061689883 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_164369159 : Nat.Prime 164369159 := by
  refine lucas_primality 164369159 (11 : ZMod 164369159) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 164369159 - 1 = [2 ^ 1, 17 ^ 1, 29 ^ 1, 166703 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_25590149046774347981202272819030594888551561664601203 : Nat.Prime 25590149046774347981202272819030594888551561664601203 := by
  refine lucas_primality 25590149046774347981202272819030594888551561664601203 (2 : ZMod 25590149046774347981202272819030594888551561664601203) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 25590149046774347981202272819030594888551561664601203 - 1 = [2 ^ 1, 7 ^ 1, 113 ^ 1, 376679 ^ 1, 1019297 ^ 1, 164369159 ^ 1, 256314897168614389937238381983 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_164369159 | exact prime_256314897168614389937238381983 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_16702656934141 : Nat.Prime 16702656934141 := by
  refine lucas_primality 16702656934141 (2 : ZMod 16702656934141) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 16702656934141 - 1 = [2 ^ 2, 3 ^ 2, 5 ^ 1, 17 ^ 1, 19 ^ 2, 337 ^ 1, 44867 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_6288254243965628477636023561015424303471232712386461634292714267317577 : Nat.Prime 6288254243965628477636023561015424303471232712386461634292714267317577 := by
  refine lucas_primality 6288254243965628477636023561015424303471232712386461634292714267317577 (5 : ZMod 6288254243965628477636023561015424303471232712386461634292714267317577) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 6288254243965628477636023561015424303471232712386461634292714267317577 - 1 = [2 ^ 3, 3 ^ 1, 613 ^ 1, 16702656934141 ^ 1, 25590149046774347981202272819030594888551561664601203 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_16702656934141 | exact prime_25590149046774347981202272819030594888551561664601203 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_183977408777 : Nat.Prime 183977408777 := by
  refine lucas_primality 183977408777 (3 : ZMod 183977408777) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 183977408777 - 1 = [2 ^ 3, 7 ^ 1, 23917 ^ 1, 137363 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_10434830671013887 : Nat.Prime 10434830671013887 := by
  refine lucas_primality 10434830671013887 (3 : ZMod 10434830671013887) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 10434830671013887 - 1 = [2 ^ 1, 3 ^ 2, 23 ^ 1, 137 ^ 1, 183977408777 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_183977408777 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_22516719107 : Nat.Prime 22516719107 := by
  refine lucas_primality 22516719107 (6 : ZMod 22516719107) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 22516719107 - 1 = [2 ^ 1, 7 ^ 1, 13217 ^ 1, 121687 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_42950384009562181214071993694251019581 : Nat.Prime 42950384009562181214071993694251019581 := by
  refine lucas_primality 42950384009562181214071993694251019581 (2 : ZMod 42950384009562181214071993694251019581) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 42950384009562181214071993694251019581 - 1 = [2 ^ 2, 3 ^ 2, 5 ^ 1, 191 ^ 1, 5317049 ^ 1, 22516719107 ^ 1, 10434830671013887 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_22516719107 | exact prime_10434830671013887 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_8001317744027 : Nat.Prime 8001317744027 := by
  refine lucas_primality 8001317744027 (2 : ZMod 8001317744027) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 8001317744027 - 1 = [2 ^ 1, 349 ^ 1, 28901 ^ 1, 396637 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_1011606064769 : Nat.Prime 1011606064769 := by
  refine lucas_primality 1011606064769 (3 : ZMod 1011606064769) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 1011606064769 - 1 = [2 ^ 7, 13 ^ 1, 17 ^ 1, 35760961 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_1390592824293524364231980562441146229143737645544470260326177213 : Nat.Prime 1390592824293524364231980562441146229143737645544470260326177213 := by
  refine lucas_primality 1390592824293524364231980562441146229143737645544470260326177213 (2 : ZMod 1390592824293524364231980562441146229143737645544470260326177213) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 1390592824293524364231980562441146229143737645544470260326177213 - 1 = [2 ^ 2, 1011606064769 ^ 1, 8001317744027 ^ 1, 42950384009562181214071993694251019581 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_1011606064769 | exact prime_8001317744027 | exact prime_42950384009562181214071993694251019581 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_390194442361 : Nat.Prime 390194442361 := by
  refine lucas_primality 390194442361 (21 : ZMod 390194442361) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 390194442361 - 1 = [2 ^ 3, 3 ^ 2, 5 ^ 1, 211 ^ 1, 5136841 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_1257388159910804265763446600825278256318012249697661907431303034629811311740864601663325811 : Nat.Prime 1257388159910804265763446600825278256318012249697661907431303034629811311740864601663325811 := by
  refine lucas_primality 1257388159910804265763446600825278256318012249697661907431303034629811311740864601663325811 (7 : ZMod 1257388159910804265763446600825278256318012249697661907431303034629811311740864601663325811) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 1257388159910804265763446600825278256318012249697661907431303034629811311740864601663325811 - 1 = [2 ^ 1, 3 ^ 2, 5 ^ 1, 37 ^ 1, 59 ^ 1, 293 ^ 1, 619 ^ 1, 65033 ^ 1, 390194442361 ^ 1, 1390592824293524364231980562441146229143737645544470260326177213 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_390194442361 | exact prime_1390592824293524364231980562441146229143737645544470260326177213 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_1081756861144651 : Nat.Prime 1081756861144651 := by
  refine lucas_primality 1081756861144651 (14 : ZMod 1081756861144651) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 1081756861144651 - 1 = [2 ^ 1, 3 ^ 2, 5 ^ 2, 53 ^ 1, 643 ^ 1, 5507 ^ 1, 12809 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_1330725593 : Nat.Prime 1330725593 := by
  refine lucas_primality 1330725593 (3 : ZMod 1330725593) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 1330725593 - 1 = [2 ^ 3, 7 ^ 1, 17 ^ 1, 31 ^ 1, 67 ^ 1, 673 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_4668478921 : Nat.Prime 4668478921 := by
  refine lucas_primality 4668478921 (47 : ZMod 4668478921) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 4668478921 - 1 = [2 ^ 3, 3 ^ 2, 5 ^ 1, 7 ^ 2, 383 ^ 1, 691 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_396485324677401403 : Nat.Prime 396485324677401403 := by
  refine lucas_primality 396485324677401403 (5 : ZMod 396485324677401403) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 396485324677401403 - 1 = [2 ^ 1, 3 ^ 1, 83 ^ 1, 733 ^ 1, 2141 ^ 1, 7043 ^ 1, 72031 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_4837281211903733 : Nat.Prime 4837281211903733 := by
  refine lucas_primality 4837281211903733 (2 : ZMod 4837281211903733) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 4837281211903733 - 1 = [2 ^ 2, 17 ^ 1, 347 ^ 1, 40093 ^ 1, 5113219 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_29023687271422399 : Nat.Prime 29023687271422399 := by
  refine lucas_primality 29023687271422399 (6 : ZMod 29023687271422399) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 29023687271422399 - 1 = [2 ^ 1, 3 ^ 1, 4837281211903733 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_4837281211903733 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_7737049283 : Nat.Prime 7737049283 := by
  refine lucas_primality 7737049283 (5 : ZMod 7737049283) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 7737049283 - 1 = [2 ^ 1, 17 ^ 1, 89 ^ 1, 2556857 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_33407751111787921302306812882603339179 : Nat.Prime 33407751111787921302306812882603339179 := by
  refine lucas_primality 33407751111787921302306812882603339179 (7 : ZMod 33407751111787921302306812882603339179) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 33407751111787921302306812882603339179 - 1 = [2 ^ 1, 3 ^ 1, 739 ^ 1, 33552401 ^ 1, 7737049283 ^ 1, 29023687271422399 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_7737049283 | exact prime_29023687271422399 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_311939705107 : Nat.Prime 311939705107 := by
  refine lucas_primality 311939705107 (5 : ZMod 311939705107) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 311939705107 - 1 = [2 ^ 1, 3 ^ 2, 17 ^ 1, 383 ^ 1, 2661647 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_1694552555570396957 : Nat.Prime 1694552555570396957 := by
  refine lucas_primality 1694552555570396957 (2 : ZMod 1694552555570396957) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 1694552555570396957 - 1 = [2 ^ 2, 7 ^ 1, 131 ^ 1, 1481 ^ 1, 311939705107 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_311939705107 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_85090262025411912798799 : Nat.Prime 85090262025411912798799 := by
  refine lucas_primality 85090262025411912798799 (3 : ZMod 85090262025411912798799) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 85090262025411912798799 - 1 = [2 ^ 1, 3 ^ 1, 8369 ^ 1, 1694552555570396957 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_1694552555570396957 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_1254041923 : Nat.Prime 1254041923 := by
  refine lucas_primality 1254041923 (2 : ZMod 1254041923) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 1254041923 - 1 = [2 ^ 1, 3 ^ 1, 7 ^ 1, 29858141 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_1670387555589396065115340644130166959 : Nat.Prime 1670387555589396065115340644130166959 := by
  refine lucas_primality 1670387555589396065115340644130166959 (3 : ZMod 1670387555589396065115340644130166959) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 1670387555589396065115340644130166959 - 1 = [2 ^ 1, 3 ^ 1, 2609 ^ 1, 1254041923 ^ 1, 85090262025411912798799 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_1254041923 | exact prime_85090262025411912798799 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_9867402931 : Nat.Prime 9867402931 := by
  refine lucas_primality 9867402931 (3 : ZMod 9867402931) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 9867402931 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 1, 7 ^ 2, 11 ^ 1, 610229 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_616712683 : Nat.Prime 616712683 := by
  refine lucas_primality 616712683 (2 : ZMod 616712683) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 616712683 - 1 = [2 ^ 1, 3 ^ 1, 1109 ^ 1, 92683 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_2466850733 : Nat.Prime 2466850733 := by
  refine lucas_primality 2466850733 (2 : ZMod 2466850733) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 2466850733 - 1 = [2 ^ 2, 616712683 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_616712683 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_417817067 : Nat.Prime 417817067 := by
  refine lucas_primality 417817067 (5 : ZMod 417817067) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 417817067 - 1 = [2 ^ 1, 757 ^ 1, 275969 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_7102927740195899 : Nat.Prime 7102927740195899 := by
  refine lucas_primality 7102927740195899 (6 : ZMod 7102927740195899) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 7102927740195899 - 1 = [2 ^ 1, 13 ^ 1, 41 ^ 1, 811 ^ 1, 20431 ^ 1, 402133 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_131147801 : Nat.Prime 131147801 := by
  refine lucas_primality 131147801 (3 : ZMod 131147801) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 131147801 - 1 = [2 ^ 3, 5 ^ 2, 7 ^ 1, 113 ^ 1, 829 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_63384337 : Nat.Prime 63384337 := by
  refine lucas_primality 63384337 (17 : ZMod 63384337) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 63384337 - 1 = [2 ^ 4, 3 ^ 3, 31 ^ 1, 4733 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_8156908781432775187914049 : Nat.Prime 8156908781432775187914049 := by
  refine lucas_primality 8156908781432775187914049 (23 : ZMod 8156908781432775187914049) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 8156908781432775187914049 - 1 = [2 ^ 6, 3 ^ 1, 7 ^ 1, 907 ^ 1, 1279 ^ 1, 1553 ^ 1, 53149 ^ 1, 63384337 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_63384337 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_3921815533 : Nat.Prime 3921815533 := by
  refine lucas_primality 3921815533 (2 : ZMod 3921815533) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 3921815533 - 1 = [2 ^ 2, 3 ^ 1, 389 ^ 1, 840149 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_24651922299337 : Nat.Prime 24651922299337 := by
  refine lucas_primality 24651922299337 (15 : ZMod 24651922299337) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 24651922299337 - 1 = [2 ^ 3, 3 ^ 2, 29 ^ 1, 1033 ^ 1, 11429309 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_26015176530521 : Nat.Prime 26015176530521 := by
  refine lucas_primality 26015176530521 (3 : ZMod 26015176530521) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 26015176530521 - 1 = [2 ^ 3, 5 ^ 1, 31 ^ 2, 73 ^ 1, 1051 ^ 1, 8821 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_114584129081 : Nat.Prime 114584129081 := by
  refine lucas_primality 114584129081 (3 : ZMod 114584129081) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 114584129081 - 1 = [2 ^ 3, 5 ^ 1, 1063 ^ 1, 2694829 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_7681945177 : Nat.Prime 7681945177 := by
  refine lucas_primality 7681945177 (15 : ZMod 7681945177) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 7681945177 - 1 = [2 ^ 3, 3 ^ 3, 17 ^ 1, 19 ^ 1, 103 ^ 1, 1069 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_121398914459 : Nat.Prime 121398914459 := by
  refine lucas_primality 121398914459 (6 : ZMod 121398914459) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 121398914459 - 1 = [2 ^ 1, 107 ^ 1, 1087 ^ 1, 521881 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_70533063399945787 : Nat.Prime 70533063399945787 := by
  refine lucas_primality 70533063399945787 (3 : ZMod 70533063399945787) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 70533063399945787 - 1 = [2 ^ 1, 3 ^ 1, 397 ^ 1, 1117 ^ 1, 8353 ^ 1, 3173623 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_1236213602544341 : Nat.Prime 1236213602544341 := by
  refine lucas_primality 1236213602544341 (2 : ZMod 1236213602544341) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 1236213602544341 - 1 = [2 ^ 2, 5 ^ 1, 7 ^ 1, 107 ^ 1, 10427 ^ 1, 7914479 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_747995764491504408871 : Nat.Prime 747995764491504408871 := by
  refine lucas_primality 747995764491504408871 (3 : ZMod 747995764491504408871) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 747995764491504408871 - 1 = [2 ^ 1, 3 ^ 6, 5 ^ 1, 83 ^ 1, 1236213602544341 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_1236213602544341 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_67404461 : Nat.Prime 67404461 := by
  refine lucas_primality 67404461 (2 : ZMod 67404461) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 67404461 - 1 = [2 ^ 2, 5 ^ 1, 647 ^ 1, 5209 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_1271397223 : Nat.Prime 1271397223 := by
  refine lucas_primality 1271397223 (3 : ZMod 1271397223) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 1271397223 - 1 = [2 ^ 1, 3 ^ 4, 7848131 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_43227505583 : Nat.Prime 43227505583 := by
  refine lucas_primality 43227505583 (5 : ZMod 43227505583) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 43227505583 - 1 = [2 ^ 1, 17 ^ 1, 1271397223 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_1271397223 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_73008878983 : Nat.Prime 73008878983 := by
  refine lucas_primality 73008878983 (3 : ZMod 73008878983) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 73008878983 - 1 = [2 ^ 1, 3 ^ 1, 13 ^ 1, 19 ^ 2, 2592829 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_44183884133846854069247 : Nat.Prime 44183884133846854069247 := by
  refine lucas_primality 44183884133846854069247 (5 : ZMod 44183884133846854069247) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 44183884133846854069247 - 1 = [2 ^ 1, 7 ^ 1, 43227505583 ^ 1, 73008878983 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_43227505583 | exact prime_73008878983 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_26664334916566271989490176818526188623612993733773073764132624439822811 : Nat.Prime 26664334916566271989490176818526188623612993733773073764132624439822811 := by
  refine lucas_primality 26664334916566271989490176818526188623612993733773073764132624439822811 (7 : ZMod 26664334916566271989490176818526188623612993733773073764132624439822811) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 26664334916566271989490176818526188623612993733773073764132624439822811 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 1, 31 ^ 1, 53 ^ 1, 1123 ^ 1, 33797 ^ 1, 6398267 ^ 1, 67404461 ^ 1, 747995764491504408871 ^ 1, 44183884133846854069247 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_67404461 | exact prime_747995764491504408871 | exact prime_44183884133846854069247 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_5297035427 : Nat.Prime 5297035427 := by
  refine lucas_primality 5297035427 (5 : ZMod 5297035427) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 5297035427 - 1 = [2 ^ 1, 29 ^ 1, 41 ^ 1, 1129 ^ 1, 1973 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_1809697712203883 : Nat.Prime 1809697712203883 := by
  refine lucas_primality 1809697712203883 (5 : ZMod 1809697712203883) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 1809697712203883 - 1 = [2 ^ 1, 1213 ^ 1, 45061 ^ 1, 16554437 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_5680156935617 : Nat.Prime 5680156935617 := by
  refine lucas_primality 5680156935617 (3 : ZMod 5680156935617) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 5680156935617 - 1 = [2 ^ 6, 79 ^ 1, 1231 ^ 1, 912631 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_155752053019 : Nat.Prime 155752053019 := by
  refine lucas_primality 155752053019 (3 : ZMod 155752053019) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 155752053019 - 1 = [2 ^ 1, 3 ^ 1, 577 ^ 1, 1297 ^ 1, 34687 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_53204563686868873577 : Nat.Prime 53204563686868873577 := by
  refine lucas_primality 53204563686868873577 (3 : ZMod 53204563686868873577) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 53204563686868873577 - 1 = [2 ^ 3, 11 ^ 1, 47 ^ 1, 1303 ^ 1, 2445139 ^ 1, 4037573 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_102725010187 : Nat.Prime 102725010187 := by
  refine lucas_primality 102725010187 (3 : ZMod 102725010187) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 102725010187 - 1 = [2 ^ 1, 3 ^ 1, 17 ^ 1, 31 ^ 1, 1321 ^ 1, 24593 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_19953254651513 : Nat.Prime 19953254651513 := by
  refine lucas_primality 19953254651513 (5 : ZMod 19953254651513) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 19953254651513 - 1 = [2 ^ 3, 7 ^ 1, 13 ^ 1, 19 ^ 1, 163 ^ 1, 337 ^ 1, 26261 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_113738319658736238418567892099 : Nat.Prime 113738319658736238418567892099 := by
  refine lucas_primality 113738319658736238418567892099 (6 : ZMod 113738319658736238418567892099) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 113738319658736238418567892099 - 1 = [2 ^ 1, 31 ^ 1, 1381 ^ 1, 2707 ^ 1, 24593449 ^ 1, 19953254651513 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_19953254651513 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_112804057 : Nat.Prime 112804057 := by
  refine lucas_primality 112804057 (13 : ZMod 112804057) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 112804057 - 1 = [2 ^ 3, 3 ^ 3, 367 ^ 1, 1423 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_1963384481 : Nat.Prime 1963384481 := by
  refine lucas_primality 1963384481 (3 : ZMod 1963384481) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 1963384481 - 1 = [2 ^ 5, 5 ^ 1, 733 ^ 1, 16741 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_1548733385688649 : Nat.Prime 1548733385688649 := by
  refine lucas_primality 1548733385688649 (17 : ZMod 1548733385688649) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 1548733385688649 - 1 = [2 ^ 3, 3 ^ 1, 23 ^ 1, 1429 ^ 1, 1963384481 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_1963384481 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_233843479 : Nat.Prime 233843479 := by
  refine lucas_primality 233843479 (6 : ZMod 233843479) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 233843479 - 1 = [2 ^ 1, 3 ^ 1, 11 ^ 1, 31 ^ 1, 37 ^ 1, 3089 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_65010825596791 : Nat.Prime 65010825596791 := by
  refine lucas_primality 65010825596791 (7 : ZMod 65010825596791) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 65010825596791 - 1 = [2 ^ 1, 3 ^ 2, 5 ^ 1, 3089 ^ 1, 233843479 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_233843479 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_1238047460871066723939449 : Nat.Prime 1238047460871066723939449 := by
  refine lucas_primality 1238047460871066723939449 (3 : ZMod 1238047460871066723939449) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 1238047460871066723939449 - 1 = [2 ^ 3, 277 ^ 1, 1447 ^ 1, 5939 ^ 1, 65010825596791 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_65010825596791 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_52447489 : Nat.Prime 52447489 := by
  refine lucas_primality 52447489 (7 : ZMod 52447489) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 52447489 - 1 = [2 ^ 8, 3 ^ 1, 47 ^ 1, 1453 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_75123590402137 : Nat.Prime 75123590402137 := by
  refine lucas_primality 75123590402137 (5 : ZMod 75123590402137) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 75123590402137 - 1 = [2 ^ 3, 3 ^ 1, 224221 ^ 1, 13960109 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_8806588255661716237 : Nat.Prime 8806588255661716237 := by
  refine lucas_primality 8806588255661716237 (5 : ZMod 8806588255661716237) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 8806588255661716237 - 1 = [2 ^ 2, 3 ^ 1, 9769 ^ 1, 75123590402137 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_75123590402137 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_139790041 : Nat.Prime 139790041 := by
  refine lucas_primality 139790041 (7 : ZMod 139790041) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 139790041 - 1 = [2 ^ 3, 3 ^ 1, 5 ^ 1, 13 ^ 2, 61 ^ 1, 113 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_3538966647017366178930789720372963502043 : Nat.Prime 3538966647017366178930789720372963502043 := by
  refine lucas_primality 3538966647017366178930789720372963502043 (5 : ZMod 3538966647017366178930789720372963502043) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 3538966647017366178930789720372963502043 - 1 = [2 ^ 1, 7 ^ 1, 239 ^ 1, 347 ^ 1, 1459 ^ 1, 1697 ^ 1, 139790041 ^ 1, 8806588255661716237 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_139790041 | exact prime_8806588255661716237 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_118241447 : Nat.Prime 118241447 := by
  refine lucas_primality 118241447 (5 : ZMod 118241447) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 118241447 - 1 = [2 ^ 1, 19 ^ 1, 211 ^ 1, 14747 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_87238974742151728369 : Nat.Prime 87238974742151728369 := by
  refine lucas_primality 87238974742151728369 (7 : ZMod 87238974742151728369) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 87238974742151728369 - 1 = [2 ^ 4, 3 ^ 1, 73 ^ 1, 1471 ^ 1, 143141 ^ 1, 118241447 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_118241447 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_12344417513 : Nat.Prime 12344417513 := by
  refine lucas_primality 12344417513 (5 : ZMod 12344417513) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 12344417513 - 1 = [2 ^ 3, 7 ^ 2, 1489 ^ 1, 21149 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_45512329 : Nat.Prime 45512329 := by
  refine lucas_primality 45512329 (13 : ZMod 45512329) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 45512329 - 1 = [2 ^ 3, 3 ^ 1, 1229 ^ 1, 1543 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_1592062201 : Nat.Prime 1592062201 := by
  refine lucas_primality 1592062201 (13 : ZMod 1592062201) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 1592062201 - 1 = [2 ^ 3, 3 ^ 2, 5 ^ 2, 571 ^ 1, 1549 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_2370424657 : Nat.Prime 2370424657 := by
  refine lucas_primality 2370424657 (15 : ZMod 2370424657) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 2370424657 - 1 = [2 ^ 4, 3 ^ 1, 1553 ^ 1, 31799 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_154414585369847792316011 : Nat.Prime 154414585369847792316011 := by
  refine lucas_primality 154414585369847792316011 (6 : ZMod 154414585369847792316011) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 154414585369847792316011 - 1 = [2 ^ 1, 5 ^ 1, 1597 ^ 1, 15767 ^ 1, 258707 ^ 1, 2370424657 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_2370424657 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_1151642337187 : Nat.Prime 1151642337187 := by
  refine lucas_primality 1151642337187 (3 : ZMod 1151642337187) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 1151642337187 - 1 = [2 ^ 1, 3 ^ 1, 11 ^ 2, 443 ^ 1, 1657 ^ 1, 2161 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_128103172114064024002337 : Nat.Prime 128103172114064024002337 := by
  refine lucas_primality 128103172114064024002337 (3 : ZMod 128103172114064024002337) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 128103172114064024002337 - 1 = [2 ^ 5, 1663 ^ 1, 23747 ^ 1, 8798221 ^ 1, 11521633 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_507628568479 : Nat.Prime 507628568479 := by
  refine lucas_primality 507628568479 (7 : ZMod 507628568479) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 507628568479 - 1 = [2 ^ 1, 3 ^ 1, 43 ^ 2, 59 ^ 1, 79 ^ 1, 9817 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_30645536679077231 : Nat.Prime 30645536679077231 := by
  refine lucas_primality 30645536679077231 (7 : ZMod 30645536679077231) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 30645536679077231 - 1 = [2 ^ 1, 5 ^ 1, 6037 ^ 1, 507628568479 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_507628568479 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_986965297 : Nat.Prime 986965297 := by
  refine lucas_primality 986965297 (5 : ZMod 986965297) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 986965297 - 1 = [2 ^ 4, 3 ^ 1, 20561777 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_181476487261139117879115643 : Nat.Prime 181476487261139117879115643 := by
  refine lucas_primality 181476487261139117879115643 (5 : ZMod 181476487261139117879115643) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 181476487261139117879115643 - 1 = [2 ^ 1, 3 ^ 1, 986965297 ^ 1, 30645536679077231 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_986965297 | exact prime_30645536679077231 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_144176258689 : Nat.Prime 144176258689 := by
  refine lucas_primality 144176258689 (13 : ZMod 144176258689) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 144176258689 - 1 = [2 ^ 7, 3 ^ 1, 7 ^ 1, 11 ^ 2, 443281 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_104596703801178343 : Nat.Prime 104596703801178343 := by
  refine lucas_primality 104596703801178343 (3 : ZMod 104596703801178343) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 104596703801178343 - 1 = [2 ^ 1, 3 ^ 1, 13 ^ 1, 71 ^ 1, 131 ^ 1, 144176258689 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_144176258689 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_4948983910284158284280949700383491609217577054379 : Nat.Prime 4948983910284158284280949700383491609217577054379 := by
  refine lucas_primality 4948983910284158284280949700383491609217577054379 (7 : ZMod 4948983910284158284280949700383491609217577054379) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 4948983910284158284280949700383491609217577054379 - 1 = [2 ^ 1, 7 ^ 1, 11 ^ 1, 1693 ^ 1, 104596703801178343 ^ 1, 181476487261139117879115643 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_104596703801178343 | exact prime_181476487261139117879115643 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_12209847761303531 : Nat.Prime 12209847761303531 := by
  refine lucas_primality 12209847761303531 (6 : ZMod 12209847761303531) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 12209847761303531 - 1 = [2 ^ 1, 5 ^ 1, 13 ^ 2, 151 ^ 1, 1723 ^ 1, 27769069 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_46591999 : Nat.Prime 46591999 := by
  refine lucas_primality 46591999 (6 : ZMod 46591999) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 46591999 - 1 = [2 ^ 1, 3 ^ 1, 167 ^ 1, 46499 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_186367997 : Nat.Prime 186367997 := by
  refine lucas_primality 186367997 (2 : ZMod 186367997) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 186367997 - 1 = [2 ^ 2, 46591999 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_46591999 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_130611215276657814724409 : Nat.Prime 130611215276657814724409 := by
  refine lucas_primality 130611215276657814724409 (3 : ZMod 130611215276657814724409) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 130611215276657814724409 - 1 = [2 ^ 3, 227 ^ 1, 1229 ^ 1, 1741 ^ 1, 180361 ^ 1, 186367997 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_186367997 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_1016572313 : Nat.Prime 1016572313 := by
  refine lucas_primality 1016572313 (3 : ZMod 1016572313) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 1016572313 - 1 = [2 ^ 3, 7 ^ 1, 1747 ^ 1, 10391 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_4893972298219433321 : Nat.Prime 4893972298219433321 := by
  refine lucas_primality 4893972298219433321 (3 : ZMod 4893972298219433321) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 4893972298219433321 - 1 = [2 ^ 3, 5 ^ 1, 47 ^ 1, 73 ^ 1, 1019 ^ 1, 1753 ^ 1, 19962949 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_269665073 : Nat.Prime 269665073 := by
  refine lucas_primality 269665073 (3 : ZMod 269665073) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 269665073 - 1 = [2 ^ 4, 131 ^ 1, 128657 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_2854495385411919762116496381035264358442074113 : Nat.Prime 2854495385411919762116496381035264358442074113 := by
  refine lucas_primality 2854495385411919762116496381035264358442074113 (3 : ZMod 2854495385411919762116496381035264358442074113) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 2854495385411919762116496381035264358442074113 - 1 = [2 ^ 76, 7 ^ 1, 31 ^ 1, 151 ^ 1, 601 ^ 1, 1801 ^ 1, 100801 ^ 1, 10567201 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_2790467761 : Nat.Prime 2790467761 := by
  refine lucas_primality 2790467761 (41 : ZMod 2790467761) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 2790467761 - 1 = [2 ^ 4, 3 ^ 1, 5 ^ 1, 103 ^ 1, 157 ^ 1, 719 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_75005713 : Nat.Prime 75005713 := by
  refine lucas_primality 75005713 (5 : ZMod 75005713) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 75005713 - 1 = [2 ^ 4, 3 ^ 2, 167 ^ 1, 3119 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_13625405957 : Nat.Prime 13625405957 := by
  refine lucas_primality 13625405957 (3 : ZMod 13625405957) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 13625405957 - 1 = [2 ^ 2, 17 ^ 1, 59 ^ 1, 67 ^ 1, 173 ^ 1, 293 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_95110361 : Nat.Prime 95110361 := by
  refine lucas_primality 95110361 (3 : ZMod 95110361) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 95110361 - 1 = [2 ^ 3, 5 ^ 1, 59 ^ 1, 191 ^ 1, 211 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_77852679293 : Nat.Prime 77852679293 := by
  refine lucas_primality 77852679293 (3 : ZMod 77852679293) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 77852679293 - 1 = [2 ^ 2, 29 ^ 1, 239 ^ 1, 839 ^ 1, 3347 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_165768537521 : Nat.Prime 165768537521 := by
  refine lucas_primality 165768537521 (3 : ZMod 165768537521) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 165768537521 - 1 = [2 ^ 4, 5 ^ 1, 47 ^ 1, 2887 ^ 1, 15271 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_111349165273 : Nat.Prime 111349165273 := by
  refine lucas_primality 111349165273 (5 : ZMod 111349165273) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 111349165273 - 1 = [2 ^ 3, 3 ^ 1, 47 ^ 1, 61 ^ 1, 331 ^ 1, 4889 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_35273039401 : Nat.Prime 35273039401 := by
  refine lucas_primality 35273039401 (7 : ZMod 35273039401) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 35273039401 - 1 = [2 ^ 3, 3 ^ 2, 5 ^ 2, 47 ^ 1, 293 ^ 1, 1423 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_47392381 : Nat.Prime 47392381 := by
  refine lucas_primality 47392381 (6 : ZMod 47392381) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 47392381 - 1 = [2 ^ 2, 3 ^ 2, 5 ^ 1, 7 ^ 1, 29 ^ 1, 1297 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_3108270227561166513471139050917630250627849827446163307471742778796333223910258298061 : Nat.Prime 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061 := by
  refine lucas_primality 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061 (7 : ZMod 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061 - 1 = [2 ^ 2, 3 ^ 3, 5 ^ 1, 11 ^ 1, 29 ^ 1, 31 ^ 1, 41 ^ 1, 43 ^ 1, 71 ^ 1, 113 ^ 1, 127 ^ 1, 281 ^ 1, 283 ^ 1, 86171 ^ 1, 122921 ^ 1, 1681003 ^ 1, 7416361 ^ 1, 47392381 ^ 1, 35273039401 ^ 1, 111349165273 ^ 1, 165768537521 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_47392381 | exact prime_35273039401 | exact prime_111349165273 | exact prime_165768537521 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_344759057 : Nat.Prime 344759057 := by
  refine lucas_primality 344759057 (3 : ZMod 344759057) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 344759057 - 1 = [2 ^ 4, 101 ^ 1, 317 ^ 1, 673 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_43872038849 : Nat.Prime 43872038849 := by
  refine lucas_primality 43872038849 (3 : ZMod 43872038849) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 43872038849 - 1 = [2 ^ 6, 11 ^ 1, 41 ^ 1, 307 ^ 1, 4951 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_2931542417 : Nat.Prime 2931542417 := by
  refine lucas_primality 2931542417 (3 : ZMod 2931542417) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 2931542417 - 1 = [2 ^ 4, 11 ^ 1, 1913 ^ 1, 8707 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_119782433 : Nat.Prime 119782433 := by
  refine lucas_primality 119782433 (3 : ZMod 119782433) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 119782433 - 1 = [2 ^ 5, 7 ^ 1, 11 ^ 1, 173 ^ 1, 281 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_18347988927920572092886567162416695526372519913346248798338768106859275713914500070771500472538615219486721 : Nat.Prime 18347988927920572092886567162416695526372519913346248798338768106859275713914500070771500472538615219486721 := by
  refine lucas_primality 18347988927920572092886567162416695526372519913346248798338768106859275713914500070771500472538615219486721 (11 : ZMod 18347988927920572092886567162416695526372519913346248798338768106859275713914500070771500472538615219486721) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 18347988927920572092886567162416695526372519913346248798338768106859275713914500070771500472538615219486721 - 1 = [2 ^ 177, 3 ^ 1, 5 ^ 1, 17 ^ 1, 23 ^ 1, 89 ^ 1, 257 ^ 1, 353 ^ 1, 397 ^ 1, 683 ^ 1, 2113 ^ 1, 229153 ^ 1, 119782433 ^ 1, 2931542417 ^ 1, 43872038849 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_119782433 | exact prime_2931542417 | exact prime_43872038849 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_2898300473 : Nat.Prime 2898300473 := by
  refine lucas_primality 2898300473 (3 : ZMod 2898300473) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 2898300473 - 1 = [2 ^ 3, 23 ^ 1, 67 ^ 1, 235099 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_67035835028187281 : Nat.Prime 67035835028187281 := by
  refine lucas_primality 67035835028187281 (3 : ZMod 67035835028187281) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 67035835028187281 - 1 = [2 ^ 4, 5 ^ 1, 131 ^ 1, 2207 ^ 1, 2898300473 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_2898300473 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_231809917527471617699 : Nat.Prime 231809917527471617699 := by
  refine lucas_primality 231809917527471617699 (2 : ZMod 231809917527471617699) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 231809917527471617699 - 1 = [2 ^ 1, 7 ^ 1, 13 ^ 1, 19 ^ 1, 67035835028187281 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_67035835028187281 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_463619835054943235399 : Nat.Prime 463619835054943235399 := by
  refine lucas_primality 463619835054943235399 (11 : ZMod 463619835054943235399) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 463619835054943235399 - 1 = [2 ^ 1, 231809917527471617699 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_231809917527471617699 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_8345157030988978237183 : Nat.Prime 8345157030988978237183 := by
  refine lucas_primality 8345157030988978237183 (3 : ZMod 8345157030988978237183) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 8345157030988978237183 - 1 = [2 ^ 1, 3 ^ 2, 463619835054943235399 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_463619835054943235399 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_37201708625305146303973352041 : Nat.Prime 37201708625305146303973352041 := by
  refine lucas_primality 37201708625305146303973352041 (19 : ZMod 37201708625305146303973352041) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 37201708625305146303973352041 - 1 = [2 ^ 3, 3 ^ 2, 5 ^ 1, 7 ^ 1, 29 ^ 1, 61 ^ 1, 8345157030988978237183 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_8345157030988978237183 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_2305843009213693951 : Nat.Prime 2305843009213693951 := by
  refine lucas_primality 2305843009213693951 (37 : ZMod 2305843009213693951) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 2305843009213693951 - 1 = [2 ^ 1, 3 ^ 2, 5 ^ 2, 7 ^ 1, 11 ^ 1, 13 ^ 1, 31 ^ 1, 41 ^ 1, 61 ^ 1, 151 ^ 1, 331 ^ 1, 1321 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_300613450595050653169853516389035139504087366260264943426013315702268533480936328328948524855350568033150042113 : Nat.Prime 300613450595050653169853516389035139504087366260264943426013315702268533480936328328948524855350568033150042113 := by
  refine lucas_primality 300613450595050653169853516389035139504087366260264943426013315702268533480936328328948524855350568033150042113 (5 : ZMod 300613450595050653169853516389035139504087366260264943426013315702268533480936328328948524855350568033150042113) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 300613450595050653169853516389035139504087366260264943426013315702268533480936328328948524855350568033150042113 - 1 = [2 ^ 184, 7 ^ 1, 367 ^ 1, 55633 ^ 1, 2305843009213693951 ^ 1, 37201708625305146303973352041 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_2305843009213693951 | exact prime_37201708625305146303973352041 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_165963031279777 : Nat.Prime 165963031279777 := by
  refine lucas_primality 165963031279777 (19 : ZMod 165963031279777) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 165963031279777 - 1 = [2 ^ 5, 3 ^ 4, 61 ^ 1, 127 ^ 1, 8264999 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_773339215189 : Nat.Prime 773339215189 := by
  refine lucas_primality 773339215189 (6 : ZMod 773339215189) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 773339215189 - 1 = [2 ^ 2, 3 ^ 1, 443 ^ 1, 9283 ^ 1, 15671 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_16694937341 : Nat.Prime 16694937341 := by
  refine lucas_primality 16694937341 (3 : ZMod 16694937341) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 16694937341 - 1 = [2 ^ 2, 5 ^ 1, 463 ^ 1, 1802909 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_45232564075409 : Nat.Prime 45232564075409 := by
  refine lucas_primality 45232564075409 (3 : ZMod 45232564075409) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 45232564075409 - 1 = [2 ^ 4, 337 ^ 1, 547 ^ 1, 15336067 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_91441702997 : Nat.Prime 91441702997 := by
  refine lucas_primality 91441702997 (3 : ZMod 91441702997) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 91441702997 - 1 = [2 ^ 2, 7 ^ 2, 101 ^ 1, 557 ^ 1, 8293 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_33714884229217 : Nat.Prime 33714884229217 := by
  refine lucas_primality 33714884229217 (5 : ZMod 33714884229217) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 33714884229217 - 1 = [2 ^ 5, 3 ^ 1, 523 ^ 1, 15091 ^ 1, 44497 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_6773252811881236867 : Nat.Prime 6773252811881236867 := by
  refine lucas_primality 6773252811881236867 (2 : ZMod 6773252811881236867) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 6773252811881236867 - 1 = [2 ^ 1, 3 ^ 2, 11161 ^ 1, 33714884229217 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_33714884229217 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_23360190343863455255753897 : Nat.Prime 23360190343863455255753897 := by
  refine lucas_primality 23360190343863455255753897 (3 : ZMod 23360190343863455255753897) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 23360190343863455255753897 - 1 = [2 ^ 3, 593 ^ 1, 727 ^ 1, 6773252811881236867 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_6773252811881236867 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_7889023609 : Nat.Prime 7889023609 := by
  refine lucas_primality 7889023609 (7 : ZMod 7889023609) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 7889023609 - 1 = [2 ^ 3, 3 ^ 1, 607 ^ 1, 541531 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_62248793 : Nat.Prime 62248793 := by
  refine lucas_primality 62248793 (3 : ZMod 62248793) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 62248793 - 1 = [2 ^ 3, 61 ^ 1, 199 ^ 1, 641 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_7981661881 : Nat.Prime 7981661881 := by
  refine lucas_primality 7981661881 (11 : ZMod 7981661881) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 7981661881 - 1 = [2 ^ 3, 3 ^ 2, 5 ^ 1, 29 ^ 2, 41 ^ 1, 643 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_302326397 : Nat.Prime 302326397 := by
  refine lucas_primality 302326397 (2 : ZMod 302326397) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 302326397 - 1 = [2 ^ 2, 239 ^ 1, 316241 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_437768622857 : Nat.Prime 437768622857 := by
  refine lucas_primality 437768622857 (3 : ZMod 437768622857) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 437768622857 - 1 = [2 ^ 3, 181 ^ 1, 302326397 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_302326397 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_26214220912037007616369852597 : Nat.Prime 26214220912037007616369852597 := by
  refine lucas_primality 26214220912037007616369852597 (5 : ZMod 26214220912037007616369852597) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 26214220912037007616369852597 - 1 = [2 ^ 2, 3 ^ 1, 41 ^ 1, 653 ^ 1, 162251 ^ 1, 1148753 ^ 1, 437768622857 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_437768622857 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_93405283373 : Nat.Prime 93405283373 := by
  refine lucas_primality 93405283373 (3 : ZMod 93405283373) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 93405283373 - 1 = [2 ^ 2, 661 ^ 1, 1051 ^ 1, 33613 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_1951402384429 : Nat.Prime 1951402384429 := by
  refine lucas_primality 1951402384429 (14 : ZMod 1951402384429) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 1951402384429 - 1 = [2 ^ 2, 3 ^ 1, 7 ^ 1, 41 ^ 1, 317 ^ 1, 683 ^ 1, 2617 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_195140238443 : Nat.Prime 195140238443 := by
  refine lucas_primality 195140238443 (2 : ZMod 195140238443) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 195140238443 - 1 = [2 ^ 1, 197 ^ 1, 521 ^ 1, 950633 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_4846812462461 : Nat.Prime 4846812462461 := by
  refine lucas_primality 4846812462461 (3 : ZMod 4846812462461) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 4846812462461 - 1 = [2 ^ 2, 5 ^ 1, 71 ^ 1, 389 ^ 1, 701 ^ 1, 12517 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_260683037 : Nat.Prime 260683037 := by
  refine lucas_primality 260683037 (3 : ZMod 260683037) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 260683037 - 1 = [2 ^ 2, 239 ^ 1, 367 ^ 1, 743 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_94743137 : Nat.Prime 94743137 := by
  refine lucas_primality 94743137 (3 : ZMod 94743137) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 94743137 - 1 = [2 ^ 5, 929 ^ 1, 3187 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_83940354459118810481 : Nat.Prime 83940354459118810481 := by
  refine lucas_primality 83940354459118810481 (3 : ZMod 83940354459118810481) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 83940354459118810481 - 1 = [2 ^ 4, 5 ^ 1, 757 ^ 1, 1193 ^ 1, 12263 ^ 1, 94743137 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_94743137 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_1508116661 : Nat.Prime 1508116661 := by
  refine lucas_primality 1508116661 (3 : ZMod 1508116661) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 1508116661 - 1 = [2 ^ 2, 5 ^ 1, 769 ^ 1, 98057 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_1131019499249 : Nat.Prime 1131019499249 := by
  refine lucas_primality 1131019499249 (3 : ZMod 1131019499249) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 1131019499249 - 1 = [2 ^ 4, 797 ^ 1, 4339 ^ 1, 20441 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_1036321259 : Nat.Prime 1036321259 := by
  refine lucas_primality 1036321259 (2 : ZMod 1036321259) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 1036321259 - 1 = [2 ^ 1, 7 ^ 1, 17 ^ 1, 23 ^ 1, 31 ^ 2, 197 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_44771151031319 : Nat.Prime 44771151031319 := by
  refine lucas_primality 44771151031319 (11 : ZMod 44771151031319) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 44771151031319 - 1 = [2 ^ 1, 21601 ^ 1, 1036321259 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_1036321259 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_441085379960554789 : Nat.Prime 441085379960554789 := by
  refine lucas_primality 441085379960554789 (6 : ZMod 441085379960554789) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 441085379960554789 - 1 = [2 ^ 2, 3 ^ 1, 821 ^ 1, 44771151031319 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_44771151031319 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_2489535877 : Nat.Prime 2489535877 := by
  refine lucas_primality 2489535877 (2 : ZMod 2489535877) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 2489535877 - 1 = [2 ^ 2, 3 ^ 1, 19 ^ 1, 10919017 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_464235512584146182617 : Nat.Prime 464235512584146182617 := by
  refine lucas_primality 464235512584146182617 (5 : ZMod 464235512584146182617) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 464235512584146182617 - 1 = [2 ^ 3, 3 ^ 1, 11 ^ 1, 127 ^ 1, 829 ^ 1, 6709 ^ 1, 2489535877 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_2489535877 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_4702664630197 : Nat.Prime 4702664630197 := by
  refine lucas_primality 4702664630197 (5 : ZMod 4702664630197) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 4702664630197 - 1 = [2 ^ 2, 3 ^ 2, 13 ^ 1, 17 ^ 1, 857 ^ 1, 689713 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_1982764321 : Nat.Prime 1982764321 := by
  refine lucas_primality 1982764321 (11 : ZMod 1982764321) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 1982764321 - 1 = [2 ^ 5, 3 ^ 1, 5 ^ 1, 887 ^ 1, 4657 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_36684968468392674349 : Nat.Prime 36684968468392674349 := by
  refine lucas_primality 36684968468392674349 (6 : ZMod 36684968468392674349) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 36684968468392674349 - 1 = [2 ^ 2, 3 ^ 1, 907 ^ 1, 5981 ^ 1, 298937 ^ 1, 1885151 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_2809306768001 : Nat.Prime 2809306768001 := by
  refine lucas_primality 2809306768001 (11 : ZMod 2809306768001) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 2809306768001 - 1 = [2 ^ 7, 5 ^ 3, 953 ^ 1, 184241 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_2748779069441 : Nat.Prime 2748779069441 := by
  refine lucas_primality 2748779069441 (3 : ZMod 2748779069441) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 2748779069441 - 1 = [2 ^ 39, 5 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_6597069766657 : Nat.Prime 6597069766657 := by
  refine lucas_primality 6597069766657 (5 : ZMod 6597069766657) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 6597069766657 - 1 = [2 ^ 41, 3 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_46179488366593 : Nat.Prime 46179488366593 := by
  refine lucas_primality 46179488366593 (11 : ZMod 46179488366593) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 46179488366593 - 1 = [2 ^ 41, 3 ^ 1, 7 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_1529992420282859521 : Nat.Prime 1529992420282859521 := by
  refine lucas_primality 1529992420282859521 (11 : ZMod 1529992420282859521) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 1529992420282859521 - 1 = [2 ^ 45, 3 ^ 1, 5 ^ 1, 13 ^ 1, 223 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_733985329951 : Nat.Prime 733985329951 := by
  refine lucas_primality 733985329951 (3 : ZMod 733985329951) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 733985329951 - 1 = [2 ^ 1, 3 ^ 3, 5 ^ 2, 23 ^ 1, 37 ^ 1, 131 ^ 1, 4877 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_69545110012857251 : Nat.Prime 69545110012857251 := by
  refine lucas_primality 69545110012857251 (2 : ZMod 69545110012857251) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 69545110012857251 - 1 = [2 ^ 1, 5 ^ 3, 379 ^ 1, 733985329951 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_733985329951 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_74201307460556292097 : Nat.Prime 74201307460556292097 := by
  refine lucas_primality 74201307460556292097 (5 : ZMod 74201307460556292097) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 74201307460556292097 - 1 = [2 ^ 54, 3 ^ 1, 1373 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_4179340454199820289 : Nat.Prime 4179340454199820289 := by
  refine lucas_primality 4179340454199820289 (3 : ZMod 4179340454199820289) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 4179340454199820289 - 1 = [2 ^ 57, 29 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_219055085875300925441 : Nat.Prime 219055085875300925441 := by
  refine lucas_primality 219055085875300925441 (3 : ZMod 219055085875300925441) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 219055085875300925441 - 1 = [2 ^ 61, 5 ^ 1, 19 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_12857380619375557476353 : Nat.Prime 12857380619375557476353 := by
  refine lucas_primality 12857380619375557476353 (3 : ZMod 12857380619375557476353) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 12857380619375557476353 - 1 = [2 ^ 64, 17 ^ 1, 41 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_1328165573307087716353 : Nat.Prime 1328165573307087716353 := by
  refine lucas_primality 1328165573307087716353 (7 : ZMod 1328165573307087716353) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 1328165573307087716353 - 1 = [2 ^ 67, 3 ^ 2].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_9097024474706080249 : Nat.Prime 9097024474706080249 := by
  refine lucas_primality 9097024474706080249 (22 : ZMod 9097024474706080249) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 9097024474706080249 - 1 = [2 ^ 3, 3 ^ 2, 7 ^ 2, 127 ^ 1, 337 ^ 1, 92737 ^ 1, 649657 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_4457323664018586376077313 : Nat.Prime 4457323664018586376077313 := by
  refine lucas_primality 4457323664018586376077313 (5 : ZMod 4457323664018586376077313) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 4457323664018586376077313 - 1 = [2 ^ 69, 3 ^ 2, 839 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_6450752615599935361908737 : Nat.Prime 6450752615599935361908737 := by
  refine lucas_primality 6450752615599935361908737 (3 : ZMod 6450752615599935361908737) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 6450752615599935361908737 - 1 = [2 ^ 73, 683 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_188894659314785808547841 : Nat.Prime 188894659314785808547841 := by
  refine lucas_primality 188894659314785808547841 (3 : ZMod 188894659314785808547841) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 188894659314785808547841 - 1 = [2 ^ 75, 5 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_256896736668108699625062401 : Nat.Prime 256896736668108699625062401 := by
  refine lucas_primality 256896736668108699625062401 (3 : ZMod 256896736668108699625062401) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 256896736668108699625062401 - 1 = [2 ^ 79, 5 ^ 2, 17 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_5241902353849032101525979137 : Nat.Prime 5241902353849032101525979137 := by
  refine lucas_primality 5241902353849032101525979137 (3 : ZMod 5241902353849032101525979137) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 5241902353849032101525979137 - 1 = [2 ^ 84, 271 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_14072902366596202965053244178433 : Nat.Prime 14072902366596202965053244178433 := by
  refine lucas_primality 14072902366596202965053244178433 (3 : ZMod 14072902366596202965053244178433) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 14072902366596202965053244178433 - 1 = [2 ^ 93, 7 ^ 2, 29 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_7316007754729683197725441917976577 : Nat.Prime 7316007754729683197725441917976577 := by
  refine lucas_primality 7316007754729683197725441917976577 (3 : ZMod 7316007754729683197725441917976577) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 7316007754729683197725441917976577 - 1 = [2 ^ 96, 107 ^ 1, 863 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_329244355096077565991935730125897729 : Nat.Prime 329244355096077565991935730125897729 := by
  refine lucas_primality 329244355096077565991935730125897729 (29 : ZMod 329244355096077565991935730125897729) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 329244355096077565991935730125897729 - 1 = [2 ^ 104, 3 ^ 1, 7 ^ 1, 773 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_9304595970494411110326649421962412033 : Nat.Prime 9304595970494411110326649421962412033 := by
  refine lucas_primality 9304595970494411110326649421962412033 (3 : ZMod 9304595970494411110326649421962412033) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 9304595970494411110326649421962412033 - 1 = [2 ^ 120, 7 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_850705917302346158658436518579420528641 : Nat.Prime 850705917302346158658436518579420528641 := by
  refine lucas_primality 850705917302346158658436518579420528641 (17 : ZMod 850705917302346158658436518579420528641) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 850705917302346158658436518579420528641 - 1 = [2 ^ 127, 5 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_3032901347000164747248857685080177164813336577 : Nat.Prime 3032901347000164747248857685080177164813336577 := by
  refine lucas_primality 3032901347000164747248857685080177164813336577 (3 : ZMod 3032901347000164747248857685080177164813336577) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 3032901347000164747248857685080177164813336577 - 1 = [2 ^ 147, 17 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_2230074519853062314153571827264836150598041600001 : Nat.Prime 2230074519853062314153571827264836150598041600001 := by
  refine lucas_primality 2230074519853062314153571827264836150598041600001 (7 : ZMod 2230074519853062314153571827264836150598041600001) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 2230074519853062314153571827264836150598041600001 - 1 = [2 ^ 149, 5 ^ 5].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_124204803210043452689216278205372864748572142206977 : Nat.Prime 124204803210043452689216278205372864748572142206977 := by
  refine lucas_primality 124204803210043452689216278205372864748572142206977 (15 : ZMod 124204803210043452689216278205372864748572142206977) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 124204803210043452689216278205372864748572142206977 - 1 = [2 ^ 154, 3 ^ 1, 7 ^ 2, 37 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_124569837190956926160012901398286924947521176078042100592562667521 : Nat.Prime 124569837190956926160012901398286924947521176078042100592562667521 := by
  refine lucas_primality 124569837190956926160012901398286924947521176078042100592562667521 (31 : ZMod 124569837190956926160012901398286924947521176078042100592562667521) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 124569837190956926160012901398286924947521176078042100592562667521 - 1 = [2 ^ 204, 3 ^ 1, 5 ^ 1, 17 ^ 1, 19 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_2468256835981809063232453773836025757474103798450369795022913537 : Nat.Prime 2468256835981809063232453773836025757474103798450369795022913537 := by
  refine lucas_primality 2468256835981809063232453773836025757474103798450369795022913537 (7 : ZMod 2468256835981809063232453773836025757474103798450369795022913537) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 2468256835981809063232453773836025757474103798450369795022913537 - 1 = [2 ^ 209, 3 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_6763365995538079644113691573900682504384080816814065022974359599316993 : Nat.Prime 6763365995538079644113691573900682504384080816814065022974359599316993 := by
  refine lucas_primality 6763365995538079644113691573900682504384080816814065022974359599316993 (3 : ZMod 6763365995538079644113691573900682504384080816814065022974359599316993) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 6763365995538079644113691573900682504384080816814065022974359599316993 - 1 = [2 ^ 217, 163 ^ 1, 197 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_12940774400232307101440167241769422723345829322819474790929732919623681 : Nat.Prime 12940774400232307101440167241769422723345829322819474790929732919623681 := by
  refine lucas_primality 12940774400232307101440167241769422723345829322819474790929732919623681 (7 : ZMod 12940774400232307101440167241769422723345829322819474790929732919623681) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 12940774400232307101440167241769422723345829322819474790929732919623681 - 1 = [2 ^ 229, 3 ^ 1, 5 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_855131645861 : Nat.Prime 855131645861 := by
  refine lucas_primality 855131645861 (3 : ZMod 855131645861) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 855131645861 - 1 = [2 ^ 2, 5 ^ 1, 89 ^ 1, 1109 ^ 1, 433193 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_199346322480330839701 : Nat.Prime 199346322480330839701 := by
  refine lucas_primality 199346322480330839701 (2 : ZMod 199346322480330839701) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 199346322480330839701 - 1 = [2 ^ 2, 3 ^ 1, 5 ^ 2, 89 ^ 1, 8731 ^ 1, 855131645861 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by first | exact prime_855131645861 | norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_100075322028463174917803960003016869060541080096470605049856601245089793 : Nat.Prime 100075322028463174917803960003016869060541080096470605049856601245089793 := by
  refine lucas_primality 100075322028463174917803960003016869060541080096470605049856601245089793 (3 : ZMod 100075322028463174917803960003016869060541080096470605049856601245089793) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 100075322028463174917803960003016869060541080096470605049856601245089793 - 1 = [2 ^ 231, 29 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

theorem prime_2916513247664901672231194184906326679054237738765821706743837897199311952805889 : Nat.Prime 2916513247664901672231194184906326679054237738765821706743837897199311952805889 := by
  refine lucas_primality 2916513247664901672231194184906326679054237738765821706743837897199311952805889 (3 : ZMod 2916513247664901672231194184906326679054237738765821706743837897199311952805889) (by reduce_mod_char) (fun q hq hd => ?_)
  have e : 2916513247664901672231194184906326679054237738765821706743837897199311952805889 - 1 = [2 ^ 252, 13 ^ 1, 31 ^ 1].prod := by norm_num
  rw [e] at hd
  obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl <;>
  · rw [(Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)]
    reduce_mod_char
    decide

-- c is not the repeated prime 5.
theorem nz5 {c : ℕ} (h : c ≠ 5) : c ∉ ({5} : Finset ℕ) := fun h' => h (Finset.mem_singleton.mp h')

-- c divides x when x is 0 in ZMod c (used to check that c divides 1 + 2^d).
theorem tw {c x : ℕ} (h : ((x : ℕ) : ZMod c) = 0) : c ∣ x := by
  rwa [ZMod.natCast_eq_zero_iff] at h

-- One more simple prime q with 5^i dividing q + 1 joins the 5-adic count.
theorem bud5_cons {j i q : ℕ} {P S : Finset ℕ}
    (h : S ⊆ P ∧ 5 ^ j ∣ ∏ p ∈ S, (p + 1)) (hq : q ∈ P) (hqS : q ∉ S)
    (h3 : 5 ^ i ∣ q + 1) :
    insert q S ⊆ P ∧ 5 ^ (j + i) ∣ ∏ p ∈ insert q S, (p + 1) := by
  refine ⟨Finset.insert_subset hq h.1, ?_⟩
  rw [Finset.prod_insert hqS, pow_add, mul_comm (5 ^ j)]
  exact mul_dvd_mul h3 h.2

-- The 5-ledger: 5 occurs exactly twice in (2^a + 1) * 26 * prod (p + 1).
theorem bud5_kill {m R i j : ℕ} {P F : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hR : R ∣ 2 ^ m + 1) (hF : F ⊆ P) (hi : 5 ^ i ∣ R) (hij : 2 + 1 ≤ i + j)
    (hj : 5 ^ j ∣ ∏ p ∈ F, (p + 1)) : False := by
  refine kill_v5 hP h5 E hR hF ((pow_dvd_pow 5 hij).trans ?_)
  rw [pow_add]
  exact mul_dvd_mul (hi.mul_right _) hj

-- a an odd multiple of 43: 3 divides 2^43 + 1 and 83 + 1.
theorem c20_d43 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 43 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g2932031007403 : 2932031007403 ∈ P := S2 2932031007403 prime_2932031007403 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 2932031007403) (x := 1 + 2 ^ 43) (by push_cast; reduce_mod_char)).trans hd)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (nz5 (by norm_num)) 2932031007403 g2932031007403 (by norm_num)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 43) (by push_cast; reduce_mod_char)).trans hd) 83 g83 (by norm_num)

-- a an odd multiple of 61: 13 divides 5^2 + 1 and 2833 + 1.
theorem c20_d61 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 61 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, -, -, S8⟩ := facts hP (hK5 2) E
  have g768614336404564651 : 768614336404564651 ∈ P := S2 768614336404564651 prime_768614336404564651 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 768614336404564651) (x := 1 + 2 ^ 61) (by push_cast; reduce_mod_char)).trans hd)
  have g2833 : 2833 ∈ P := S1 2833 (by norm_num) (by norm_num) (nz5 (by norm_num)) 768614336404564651 g768614336404564651 (by norm_num)
  exact S8 13 (by norm_num) (by norm_num) (nz5 (by norm_num)) (by norm_num) 2833 g2833 (by norm_num)

-- a an odd multiple of 67: 13 divides 5^2 + 1 and 7327657 + 1.
theorem c20_d67 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 67 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, -, -, S8⟩ := facts hP (hK5 2) E
  have g7327657 : 7327657 ∈ P := S2 7327657 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 7327657) (x := 1 + 2 ^ 67) (by push_cast; reduce_mod_char)).trans hd)
  exact S8 13 (by norm_num) (by norm_num) (nz5 (by norm_num)) (by norm_num) 7327657 g7327657 (by norm_num)

-- a an odd multiple of 73: 3 divides 2^73 + 1 and 11 + 1.
theorem c20_d73 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 73 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g1753 : 1753 ∈ P := S2 1753 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 1753) (x := 1 + 2 ^ 73) (by push_cast; reduce_mod_char)).trans hd)
  have g877 : 877 ∈ P := S1 877 (by norm_num) (by norm_num) (nz5 (by norm_num)) 1753 g1753 (by norm_num)
  have g439 : 439 ∈ P := S1 439 (by norm_num) (by norm_num) (nz5 (by norm_num)) 877 g877 (by norm_num)
  have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (nz5 (by norm_num)) 439 g439 (by norm_num)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 73) (by push_cast; reduce_mod_char)).trans hd) 11 g11 (by norm_num)

-- a an odd multiple of 79: 3 divides 2^79 + 1 and 617 + 1.
theorem c20_d79 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 79 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g201487636602438195784363 : 201487636602438195784363 ∈ P := S2 201487636602438195784363 prime_201487636602438195784363 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 201487636602438195784363) (x := 1 + 2 ^ 79) (by push_cast; reduce_mod_char)).trans hd)
  have g617 : 617 ∈ P := S1 617 (by norm_num) (by norm_num) (nz5 (by norm_num)) 201487636602438195784363 g201487636602438195784363 (by norm_num)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 79) (by push_cast; reduce_mod_char)).trans hd) 617 g617 (by norm_num)

-- a an odd multiple of 97: 3^2 divides 971 + 1.
theorem c20_d97 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 97 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g971 : 971 ∈ P := S2 971 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 971) (x := 1 + 2 ^ 97) (by push_cast; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 971 g971 (by norm_num)

-- a an odd multiple of 103: 3 divides 2^103 + 1 and 415141630193 + 1.
theorem c20_d103 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 103 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g415141630193 : 415141630193 ∈ P := S2 415141630193 prime_415141630193 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 415141630193) (x := 1 + 2 ^ 103) (by push_cast; reduce_mod_char)).trans hd)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 103) (by push_cast; reduce_mod_char)).trans hd) 415141630193 g415141630193 (by norm_num)

-- a an odd multiple of 109: 7 divides 104124649 + 1 and 13 + 1.
theorem c20_d109 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 109 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, S3, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g104124649 : 104124649 ∈ P := S2 104124649 prime_104124649 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 104124649) (x := 1 + 2 ^ 109) (by push_cast; reduce_mod_char)).trans hd)
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (nz5 (by norm_num)) (by norm_num)
  exact absurd (S3 7 (by norm_num) (by norm_num) (nz5 (by norm_num)) 104124649 g104124649 13 g13 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 127: 3 divides 2^127 + 1 and 11 + 1.
theorem c20_d127 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 127 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g56713727820156410577229101238628035243 : 56713727820156410577229101238628035243 ∈ P := S2 56713727820156410577229101238628035243 prime_56713727820156410577229101238628035243 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 56713727820156410577229101238628035243) (x := 1 + 2 ^ 127) (by push_cast; reduce_mod_char)).trans hd)
  have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (nz5 (by norm_num)) 56713727820156410577229101238628035243 g56713727820156410577229101238628035243 (by norm_num)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 127) (by push_cast; reduce_mod_char)).trans hd) 11 g11 (by norm_num)

-- a an odd multiple of 139: 3^2 divides 17 + 1.
theorem c20_d139 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 139 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g4506937 : 4506937 ∈ P := S2 4506937 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 4506937) (x := 1 + 2 ^ 139) (by push_cast; reduce_mod_char)).trans hd)
  have g17 : 17 ∈ P := S1 17 (by norm_num) (by norm_num) (nz5 (by norm_num)) 4506937 g4506937 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 17 g17 (by norm_num)

-- a an odd multiple of 151: 3 divides 2^151 + 1 and 2351 + 1.
theorem c20_d151 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 151 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g18717738334417 : 18717738334417 ∈ P := S2 18717738334417 prime_18717738334417 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 18717738334417) (x := 1 + 2 ^ 151) (by push_cast; reduce_mod_char)).trans hd)
  have g2351 : 2351 ∈ P := S1 2351 (by norm_num) (by norm_num) (nz5 (by norm_num)) 18717738334417 g18717738334417 (by norm_num)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 151) (by push_cast; reduce_mod_char)).trans hd) 2351 g2351 (by norm_num)

-- a an odd multiple of 157: 7 divides 2350291 + 1 and 13 + 1.
theorem c20_d157 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 157 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, S3, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g2350291 : 2350291 ∈ P := S2 2350291 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 2350291) (x := 1 + 2 ^ 157) (by push_cast; reduce_mod_char)).trans hd)
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (nz5 (by norm_num)) (by norm_num)
  exact absurd (S3 7 (by norm_num) (by norm_num) (nz5 (by norm_num)) 2350291 g2350291 13 g13 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 163: 13 divides 5^2 + 1 and 11281292593 + 1.
theorem c20_d163 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 163 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, -, -, S8⟩ := facts hP (hK5 2) E
  have g11281292593 : 11281292593 ∈ P := S2 11281292593 prime_11281292593 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 11281292593) (x := 1 + 2 ^ 163) (by push_cast; reduce_mod_char)).trans hd)
  exact S8 13 (by norm_num) (by norm_num) (nz5 (by norm_num)) (by norm_num) 11281292593 g11281292593 (by norm_num)

-- a an odd multiple of 181: 3 divides 2^181 + 1 and 1811 + 1.
theorem c20_d181 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 181 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g1811 : 1811 ∈ P := S2 1811 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 1811) (x := 1 + 2 ^ 181) (by push_cast; reduce_mod_char)).trans hd)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 181) (by push_cast; reduce_mod_char)).trans hd) 1811 g1811 (by norm_num)

-- a an odd multiple of 193: 3 divides 2^193 + 1 and 6563 + 1.
theorem c20_d193 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 193 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g6563 : 6563 ∈ P := S2 6563 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 6563) (x := 1 + 2 ^ 193) (by push_cast; reduce_mod_char)).trans hd)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 193) (by push_cast; reduce_mod_char)).trans hd) 6563 g6563 (by norm_num)

-- a an odd multiple of 199: 7 divides 13 + 1 and 1348959352853811313 + 1.
theorem c20_d199 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 199 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, S3, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (nz5 (by norm_num)) (by norm_num)
  have g267823007376498379256993682056860433753700498963798805883563 : 267823007376498379256993682056860433753700498963798805883563 ∈ P := S2 267823007376498379256993682056860433753700498963798805883563 prime_267823007376498379256993682056860433753700498963798805883563 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 267823007376498379256993682056860433753700498963798805883563) (x := 1 + 2 ^ 199) (by push_cast; reduce_mod_char)).trans hd)
  have g1348959352853811313 : 1348959352853811313 ∈ P := S1 1348959352853811313 prime_1348959352853811313 (by norm_num) (nz5 (by norm_num)) 267823007376498379256993682056860433753700498963798805883563 g267823007376498379256993682056860433753700498963798805883563 (by norm_num)
  exact absurd (S3 7 (by norm_num) (by norm_num) (nz5 (by norm_num)) 13 g13 1348959352853811313 g1348959352853811313 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 211: 3^2 divides 4643 + 1.
theorem c20_d211 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 211 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g4643 : 4643 ∈ P := S2 4643 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 4643) (x := 1 + 2 ^ 211) (by push_cast; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 4643 g4643 (by norm_num)

-- a an odd multiple of 223: 3^2 divides 219256122131 + 1.
theorem c20_d223 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 223 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g219256122131 : 219256122131 ∈ P := S2 219256122131 prime_219256122131 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 219256122131) (x := 1 + 2 ^ 223) (by push_cast; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 219256122131 g219256122131 (by norm_num)

-- a an odd multiple of 229: 3 divides 2^229 + 1 and 18754643 + 1.
theorem c20_d229 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 229 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g18754643 : 18754643 ∈ P := S2 18754643 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 18754643) (x := 1 + 2 ^ 229) (by push_cast; reduce_mod_char)).trans hd)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 229) (by push_cast; reduce_mod_char)).trans hd) 18754643 g18754643 (by norm_num)

-- a an odd multiple of 241: 3^2 divides 2411 + 1.
theorem c20_d241 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 241 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g2411 : 2411 ∈ P := S2 2411 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 2411) (x := 1 + 2 ^ 241) (by push_cast; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 2411 g2411 (by norm_num)

-- a an odd multiple of 271: 3 divides 2^271 + 1 and 11 + 1.
theorem c20_d271 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 271 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g1627 : 1627 ∈ P := S2 1627 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 1627) (x := 1 + 2 ^ 271) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (nz5 (by norm_num)) 1627 g1627 (by norm_num)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 271) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 11 g11 (by norm_num)

-- a an odd multiple of 277: 7 divides 25792643401363 + 1 and 13 + 1.
theorem c20_d277 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 277 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, S3, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g25792643401363 : 25792643401363 ∈ P := S2 25792643401363 prime_25792643401363 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 25792643401363) (x := 1 + 2 ^ 277) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (nz5 (by norm_num)) (by norm_num)
  exact absurd (S3 7 (by norm_num) (by norm_num) (nz5 (by norm_num)) 25792643401363 g25792643401363 13 g13 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 283: 3^2 divides 17 + 1.
theorem c20_d283 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 283 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g1699 : 1699 ∈ P := S2 1699 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 1699) (x := 1 + 2 ^ 283) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g17 : 17 ∈ P := S1 17 (by norm_num) (by norm_num) (nz5 (by norm_num)) 1699 g1699 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 17 g17 (by norm_num)

-- a an odd multiple of 307: 3 divides 2^307 + 1 and 1249678499 + 1.
theorem c20_d307 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 307 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g1249678499 : 1249678499 ∈ P := S2 1249678499 prime_1249678499 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 1249678499) (x := 1 + 2 ^ 307) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 307) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 1249678499 g1249678499 (by norm_num)

-- a an odd multiple of 313: 3 divides 2^313 + 1 and 64067 + 1.
theorem c20_d313 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 313 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 : 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 ∈ P := S2 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 prime_5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731) (x := 1 + 2 ^ 313) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g64067 : 64067 ∈ P := S1 64067 (by norm_num) (by norm_num) (nz5 (by norm_num)) 5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 g5562466239377370006237035693149875298444543026970449921737087520370363869220418099018130434731 (by norm_num)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 313) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 64067 g64067 (by norm_num)

-- a an odd multiple of 331: 3 divides 2^331 + 1 and 5297 + 1.
theorem c20_d331 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 331 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g5297 : 5297 ∈ P := S2 5297 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 5297) (x := 1 + 2 ^ 331) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 331) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 5297 g5297 (by norm_num)

-- a an odd multiple of 337: 3 divides 2^337 + 1 and 21569 + 1.
theorem c20_d337 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 337 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g21569 : 21569 ∈ P := S2 21569 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 21569) (x := 1 + 2 ^ 337) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 337) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 21569 g21569 (by norm_num)

-- a an odd multiple of 349: 3 divides 2^349 + 1 and 131282633 + 1.
theorem c20_d349 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 349 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g131282633 : 131282633 ∈ P := S2 131282633 prime_131282633 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 131282633) (x := 1 + 2 ^ 349) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 349) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 131282633 g131282633 (by norm_num)

-- a an odd multiple of 367: 3 divides 2^367 + 1 and 29 + 1.
theorem c20_d367 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 367 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g2203 : 2203 ∈ P := S2 2203 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 2203) (x := 1 + 2 ^ 367) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (nz5 (by norm_num)) 2203 g2203 (by norm_num)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 367) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 29 g29 (by norm_num)

-- a an odd multiple of 373: 3 divides 2^373 + 1 and 15107 + 1.
theorem c20_d373 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 373 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g60427 : 60427 ∈ P := S2 60427 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 60427) (x := 1 + 2 ^ 373) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g15107 : 15107 ∈ P := S1 15107 (by norm_num) (by norm_num) (nz5 (by norm_num)) 60427 g60427 (by norm_num)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 373) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 15107 g15107 (by norm_num)

-- a an odd multiple of 379: 3 divides 2^379 + 1 and 47 + 1.
theorem c20_d379 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 379 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g15012732261073 : 15012732261073 ∈ P := S2 15012732261073 prime_15012732261073 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 15012732261073) (x := 1 + 2 ^ 379) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g47 : 47 ∈ P := S1 47 (by norm_num) (by norm_num) (nz5 (by norm_num)) 15012732261073 g15012732261073 (by norm_num)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 379) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 47 g47 (by norm_num)

-- a an odd multiple of 397: 3^2 divides 13499 + 1.
theorem c20_d397 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 397 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g13499 : 13499 ∈ P := S2 13499 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 13499) (x := 1 + 2 ^ 397) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 13499 g13499 (by norm_num)

-- a an odd multiple of 409: 3^2 divides 176596029450915408652219208387 + 1.
theorem c20_d409 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 409 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g176596029450915408652219208387 : 176596029450915408652219208387 ∈ P := S2 176596029450915408652219208387 prime_176596029450915408652219208387 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 176596029450915408652219208387) (x := 1 + 2 ^ 409) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 176596029450915408652219208387 g176596029450915408652219208387 (by norm_num)

-- a an odd multiple of 421: 3^2 divides 4211 + 1.
theorem c20_d421 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 421 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g4211 : 4211 ∈ P := S2 4211 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 4211) (x := 1 + 2 ^ 421) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 4211 g4211 (by norm_num)

-- a an odd multiple of 433: 3^2 divides 71 + 1.
theorem c20_d433 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 433 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g2837017 : 2837017 ∈ P := S2 2837017 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 2837017) (x := 1 + 2 ^ 433) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g71 : 71 ∈ P := S1 71 (by norm_num) (by norm_num) (nz5 (by norm_num)) 2837017 g2837017 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 71 g71 (by norm_num)

-- a an odd multiple of 439: 13 divides 5^2 + 1 and 3740281 + 1.
theorem c20_d439 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 439 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, -, -, S8⟩ := facts hP (hK5 2) E
  have g3740281 : 3740281 ∈ P := S2 3740281 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 3740281) (x := 1 + 2 ^ 439) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S8 13 (by norm_num) (by norm_num) (nz5 (by norm_num)) (by norm_num) 3740281 g3740281 (by norm_num)

-- a an odd multiple of 457: 3 divides 2^457 + 1 and 1451 + 1.
theorem c20_d457 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 457 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g6885357560205319573060633896800918448254904729193 : 6885357560205319573060633896800918448254904729193 ∈ P := S2 6885357560205319573060633896800918448254904729193 prime_6885357560205319573060633896800918448254904729193 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 6885357560205319573060633896800918448254904729193) (x := 1 + 2 ^ 457) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g1451 : 1451 ∈ P := S1 1451 (by norm_num) (by norm_num) (nz5 (by norm_num)) 6885357560205319573060633896800918448254904729193 g6885357560205319573060633896800918448254904729193 (by norm_num)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 457) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 1451 g1451 (by norm_num)

-- a an odd multiple of 463: 3 divides 2^463 + 1 and 182201 + 1.
theorem c20_d463 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 463 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g76834966209858049526107 : 76834966209858049526107 ∈ P := S2 76834966209858049526107 prime_76834966209858049526107 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 76834966209858049526107) (x := 1 + 2 ^ 463) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g182201 : 182201 ∈ P := S1 182201 (by norm_num) (by norm_num) (nz5 (by norm_num)) 76834966209858049526107 g76834966209858049526107 (by norm_num)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 463) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 182201 g182201 (by norm_num)

-- a an odd multiple of 487: 3 divides 2^487 + 1 and 227020551154913939039124941009 + 1.
theorem c20_d487 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 487 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g227020551154913939039124941009 : 227020551154913939039124941009 ∈ P := S2 227020551154913939039124941009 prime_227020551154913939039124941009 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 227020551154913939039124941009) (x := 1 + 2 ^ 487) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 487) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 227020551154913939039124941009 g227020551154913939039124941009 (by norm_num)

-- a an odd multiple of 499: 3^2 divides 163673 + 1.
theorem c20_d499 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 499 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g163673 : 163673 ∈ P := S2 163673 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 163673) (x := 1 + 2 ^ 499) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 163673 g163673 (by norm_num)

-- a an odd multiple of 523: 3 divides 2^523 + 1 and 11 + 1.
theorem c20_d523 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 523 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g36667531 : 36667531 ∈ P := S2 36667531 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 36667531) (x := 1 + 2 ^ 523) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (nz5 (by norm_num)) 36667531 g36667531 (by norm_num)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 523) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 11 g11 (by norm_num)

-- a an odd multiple of 541: 3^2 divides 86561 + 1.
theorem c20_d541 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 541 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g86561 : 86561 ∈ P := S2 86561 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 86561) (x := 1 + 2 ^ 541) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 86561 g86561 (by norm_num)

-- a an odd multiple of 547: 3^2 divides 17 + 1.
theorem c20_d547 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 547 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g1533926272849 : 1533926272849 ∈ P := S2 1533926272849 prime_1533926272849 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 1533926272849) (x := 1 + 2 ^ 547) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g150517 : 150517 ∈ P := S1 150517 (by norm_num) (by norm_num) (nz5 (by norm_num)) 1533926272849 g1533926272849 (by norm_num)
  have g17 : 17 ∈ P := S1 17 (by norm_num) (by norm_num) (nz5 (by norm_num)) 150517 g150517 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 17 g17 (by norm_num)

-- a an odd multiple of 571: 3 divides 2^571 + 1 and 9137 + 1.
theorem c20_d571 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 571 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g9137 : 9137 ∈ P := S2 9137 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 9137) (x := 1 + 2 ^ 571) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 571) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 9137 g9137 (by norm_num)

-- a an odd multiple of 577: 3 divides 2^577 + 1 and 75011 + 1.
theorem c20_d577 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 577 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g75011 : 75011 ∈ P := S2 75011 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 75011) (x := 1 + 2 ^ 577) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 577) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 75011 g75011 (by norm_num)

-- a an odd multiple of 601: 3^2 divides 9293424294571360217 + 1.
theorem c20_d601 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 601 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g9293424294571360217 : 9293424294571360217 ∈ P := S2 9293424294571360217 prime_9293424294571360217 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 9293424294571360217) (x := 1 + 2 ^ 601) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 9293424294571360217 g9293424294571360217 (by norm_num)

-- a an odd multiple of 607: 3 divides 2^607 + 1 and 115331 + 1.
theorem c20_d607 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 607 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g115331 : 115331 ∈ P := S2 115331 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 115331) (x := 1 + 2 ^ 607) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 607) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 115331 g115331 (by norm_num)

-- a an odd multiple of 613: 13 divides 5^2 + 1 and 6288254243965628477636023561015424303471232712386461634292714267317577 + 1.
theorem c20_d613 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 613 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, -, -, S8⟩ := facts hP (hK5 2) E
  have g6288254243965628477636023561015424303471232712386461634292714267317577 : 6288254243965628477636023561015424303471232712386461634292714267317577 ∈ P := S2 6288254243965628477636023561015424303471232712386461634292714267317577 prime_6288254243965628477636023561015424303471232712386461634292714267317577 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 6288254243965628477636023561015424303471232712386461634292714267317577) (x := 1 + 2 ^ 613) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S8 13 (by norm_num) (by norm_num) (nz5 (by norm_num)) (by norm_num) 6288254243965628477636023561015424303471232712386461634292714267317577 g6288254243965628477636023561015424303471232712386461634292714267317577 (by norm_num)

-- a an odd multiple of 619: 3 divides 2^619 + 1 and 23 + 1.
theorem c20_d619 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 619 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g1257388159910804265763446600825278256318012249697661907431303034629811311740864601663325811 : 1257388159910804265763446600825278256318012249697661907431303034629811311740864601663325811 ∈ P := S2 1257388159910804265763446600825278256318012249697661907431303034629811311740864601663325811 prime_1257388159910804265763446600825278256318012249697661907431303034629811311740864601663325811 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 1257388159910804265763446600825278256318012249697661907431303034629811311740864601663325811) (x := 1 + 2 ^ 619) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g23 : 23 ∈ P := S1 23 (by norm_num) (by norm_num) (nz5 (by norm_num)) 1257388159910804265763446600825278256318012249697661907431303034629811311740864601663325811 g1257388159910804265763446600825278256318012249697661907431303034629811311740864601663325811 (by norm_num)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 619) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 23 g23 (by norm_num)

-- a an odd multiple of 631: 3 divides 2^631 + 1 and 8309009 + 1.
theorem c20_d631 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 631 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g8309009 : 8309009 ∈ P := S2 8309009 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 8309009) (x := 1 + 2 ^ 631) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 631) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 8309009 g8309009 (by norm_num)

-- a an odd multiple of 643: 7 divides 1081756861144651 + 1 and 13 + 1.
theorem c20_d643 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 643 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, S3, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g1081756861144651 : 1081756861144651 ∈ P := S2 1081756861144651 prime_1081756861144651 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 1081756861144651) (x := 1 + 2 ^ 643) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (nz5 (by norm_num)) (by norm_num)
  exact absurd (S3 7 (by norm_num) (by norm_num) (nz5 (by norm_num)) 1081756861144651 g1081756861144651 13 g13 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 661: 3 divides 2^661 + 1 and 4611137 + 1.
theorem c20_d661 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 661 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g4611137 : 4611137 ∈ P := S2 4611137 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 4611137) (x := 1 + 2 ^ 661) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 661) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 4611137 g4611137 (by norm_num)

-- a an odd multiple of 673: 3 divides 2^673 + 1 and 1330725593 + 1.
theorem c20_d673 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 673 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g1330725593 : 1330725593 ∈ P := S2 1330725593 prime_1330725593 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 1330725593) (x := 1 + 2 ^ 673) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 673) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 1330725593 g1330725593 (by norm_num)

-- a an odd multiple of 691: 37^2 divides 4668478921 + 1.
theorem c20_d691 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 691 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g4668478921 : 4668478921 ∈ P := S2 4668478921 prime_4668478921 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 4668478921) (x := 1 + 2 ^ 691) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 37 (by norm_num) (by norm_num) (nz5 (by norm_num)) 4668478921 g4668478921 (by norm_num)

-- a an odd multiple of 709: 3 divides 2^709 + 1 and 263 + 1.
theorem c20_d709 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 709 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g340321 : 340321 ∈ P := S2 340321 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 340321) (x := 1 + 2 ^ 709) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g263 : 263 ∈ P := S1 263 (by norm_num) (by norm_num) (nz5 (by norm_num)) 340321 g340321 (by norm_num)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 709) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 263 g263 (by norm_num)

-- a an odd multiple of 727: 3 divides 2^727 + 1 and 11633 + 1.
theorem c20_d727 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 727 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g11633 : 11633 ∈ P := S2 11633 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 11633) (x := 1 + 2 ^ 727) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 727) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 11633 g11633 (by norm_num)

-- a an odd multiple of 733: 3^2 divides 4797953 + 1.
theorem c20_d733 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 733 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g396485324677401403 : 396485324677401403 ∈ P := S2 396485324677401403 prime_396485324677401403 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 396485324677401403) (x := 1 + 2 ^ 733) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g4797953 : 4797953 ∈ P := S1 4797953 (by norm_num) (by norm_num) (nz5 (by norm_num)) 396485324677401403 g396485324677401403 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 4797953 g4797953 (by norm_num)

-- a an odd multiple of 739: 3^2 divides 2466850733 + 1.
theorem c20_d739 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 739 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g33407751111787921302306812882603339179 : 33407751111787921302306812882603339179 ∈ P := S2 33407751111787921302306812882603339179 prime_33407751111787921302306812882603339179 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 33407751111787921302306812882603339179) (x := 1 + 2 ^ 739) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g1670387555589396065115340644130166959 : 1670387555589396065115340644130166959 ∈ P := S1 1670387555589396065115340644130166959 prime_1670387555589396065115340644130166959 (by norm_num) (nz5 (by norm_num)) 33407751111787921302306812882603339179 g33407751111787921302306812882603339179 (by norm_num)
  have g9867402931 : 9867402931 ∈ P := S1 9867402931 prime_9867402931 (by norm_num) (nz5 (by norm_num)) 1670387555589396065115340644130166959 g1670387555589396065115340644130166959 (by norm_num)
  have g2466850733 : 2466850733 ∈ P := S1 2466850733 prime_2466850733 (by norm_num) (nz5 (by norm_num)) 9867402931 g9867402931 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 2466850733 g2466850733 (by norm_num)

-- a an odd multiple of 751: 3 divides 2^751 + 1 and 11 + 1.
theorem c20_d751 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 751 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g274867 : 274867 ∈ P := S2 274867 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 274867) (x := 1 + 2 ^ 751) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (nz5 (by norm_num)) 274867 g274867 (by norm_num)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 751) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 11 g11 (by norm_num)

-- a an odd multiple of 757: 3 divides 2^757 + 1 and 417817067 + 1.
theorem c20_d757 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 757 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g417817067 : 417817067 ∈ P := S2 417817067 prime_417817067 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 417817067) (x := 1 + 2 ^ 757) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 757) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 417817067 g417817067 (by norm_num)

-- a an odd multiple of 769: 3 divides 2^769 + 1 and 11 + 1.
theorem c20_d769 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 769 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g36913 : 36913 ∈ P := S2 36913 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 36913) (x := 1 + 2 ^ 769) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g18457 : 18457 ∈ P := S1 18457 (by norm_num) (by norm_num) (nz5 (by norm_num)) 36913 g36913 (by norm_num)
  have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (nz5 (by norm_num)) 18457 g18457 (by norm_num)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 769) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 11 g11 (by norm_num)

-- a an odd multiple of 787: 3 divides 2^787 + 1 and 942827 + 1.
theorem c20_d787 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 787 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g942827 : 942827 ∈ P := S2 942827 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 942827) (x := 1 + 2 ^ 787) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 787) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 942827 g942827 (by norm_num)

-- a an odd multiple of 811: 3^2 divides 7102927740195899 + 1.
theorem c20_d811 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 811 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g7102927740195899 : 7102927740195899 ∈ P := S2 7102927740195899 prime_7102927740195899 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 7102927740195899) (x := 1 + 2 ^ 811) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 7102927740195899 g7102927740195899 (by norm_num)

-- a an odd multiple of 823: 3^2 divides 17 + 1.
theorem c20_d823 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 823 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g316033 : 316033 ∈ P := S2 316033 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 316033) (x := 1 + 2 ^ 823) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g158017 : 158017 ∈ P := S1 158017 (by norm_num) (by norm_num) (nz5 (by norm_num)) 316033 g316033 (by norm_num)
  have g11287 : 11287 ∈ P := S1 11287 (by norm_num) (by norm_num) (nz5 (by norm_num)) 158017 g158017 (by norm_num)
  have g17 : 17 ∈ P := S1 17 (by norm_num) (by norm_num) (nz5 (by norm_num)) 11287 g11287 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 17 g17 (by norm_num)

-- a an odd multiple of 829: 3^2 divides 131147801 + 1.
theorem c20_d829 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 829 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g131147801 : 131147801 ∈ P := S2 131147801 prime_131147801 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 131147801) (x := 1 + 2 ^ 829) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 131147801 g131147801 (by norm_num)

-- a an odd multiple of 853: 3^2 divides 2465171 + 1.
theorem c20_d853 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 853 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g2465171 : 2465171 ∈ P := S2 2465171 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 2465171) (x := 1 + 2 ^ 853) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 2465171 g2465171 (by norm_num)

-- a an odd multiple of 859: 3 divides 2^859 + 1 and 2027 + 1.
theorem c20_d859 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 859 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g4045891 : 4045891 ∈ P := S2 4045891 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 4045891) (x := 1 + 2 ^ 859) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g2027 : 2027 ∈ P := S1 2027 (by norm_num) (by norm_num) (nz5 (by norm_num)) 4045891 g4045891 (by norm_num)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 859) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 2027 g2027 (by norm_num)

-- a an odd multiple of 877: 3 divides 2^877 + 1 and 29819 + 1.
theorem c20_d877 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 877 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g29819 : 29819 ∈ P := S2 29819 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 29819) (x := 1 + 2 ^ 877) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 877) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 29819 g29819 (by norm_num)

-- a an odd multiple of 883: 3 divides 2^883 + 1 and 294923 + 1.
theorem c20_d883 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 883 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g294923 : 294923 ∈ P := S2 294923 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 294923) (x := 1 + 2 ^ 883) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 883) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 294923 g294923 (by norm_num)

-- a an odd multiple of 907: 13 divides 5^2 + 1 and 3921815533 + 1.
theorem c20_d907 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 907 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, -, -, S8⟩ := facts hP (hK5 2) E
  have g8156908781432775187914049 : 8156908781432775187914049 ∈ P := S2 8156908781432775187914049 prime_8156908781432775187914049 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 8156908781432775187914049) (x := 1 + 2 ^ 907) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g3921815533 : 3921815533 ∈ P := S1 3921815533 prime_3921815533 (by norm_num) (nz5 (by norm_num)) 8156908781432775187914049 g8156908781432775187914049 (by norm_num)
  exact S8 13 (by norm_num) (by norm_num) (nz5 (by norm_num)) (by norm_num) 3921815533 g3921815533 (by norm_num)

-- a an odd multiple of 919: 3^2 divides 14968673 + 1.
theorem c20_d919 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 919 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g14968673 : 14968673 ∈ P := S2 14968673 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 14968673) (x := 1 + 2 ^ 919) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 14968673 g14968673 (by norm_num)

-- a an odd multiple of 937: 3^2 divides 1431737 + 1.
theorem c20_d937 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 937 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g1431737 : 1431737 ∈ P := S2 1431737 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 1431737) (x := 1 + 2 ^ 937) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 1431737 g1431737 (by norm_num)

-- a an odd multiple of 967: 3 divides 2^967 + 1 and 47 + 1.
theorem c20_d967 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 967 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g440953 : 440953 ∈ P := S2 440953 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 440953) (x := 1 + 2 ^ 967) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g47 : 47 ∈ P := S1 47 (by norm_num) (by norm_num) (nz5 (by norm_num)) 440953 g440953 (by norm_num)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 967) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 47 g47 (by norm_num)

-- a an odd multiple of 991: 3 divides 2^991 + 1 and 3060209 + 1.
theorem c20_d991 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 991 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g3060209 : 3060209 ∈ P := S2 3060209 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 3060209) (x := 1 + 2 ^ 991) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 991) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 3060209 g3060209 (by norm_num)

-- a an odd multiple of 997: 3 divides 2^997 + 1 and 614153 + 1.
theorem c20_d997 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 997 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g614153 : 614153 ∈ P := S2 614153 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 614153) (x := 1 + 2 ^ 997) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 997) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 614153 g614153 (by norm_num)

-- a an odd multiple of 1009: 3 divides 2^1009 + 1 and 11 + 1.
theorem c20_d1009 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1009 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g962587 : 962587 ∈ P := S2 962587 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 962587) (x := 1 + 2 ^ 1009) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (nz5 (by norm_num)) 962587 g962587 (by norm_num)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 1009) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 11 g11 (by norm_num)

-- a an odd multiple of 1021: 3 divides 2^1021 + 1 and 10211 + 1.
theorem c20_d1021 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1021 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g10211 : 10211 ∈ P := S2 10211 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 10211) (x := 1 + 2 ^ 1021) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 1021) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 10211 g10211 (by norm_num)

-- a an odd multiple of 1033: 89^2 divides 586153 + 1.
theorem c20_d1033 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1033 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g24651922299337 : 24651922299337 ∈ P := S2 24651922299337 prime_24651922299337 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 24651922299337) (x := 1 + 2 ^ 1033) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g586153 : 586153 ∈ P := S1 586153 (by norm_num) (by norm_num) (nz5 (by norm_num)) 24651922299337 g24651922299337 (by norm_num)
  exact S6 89 (by norm_num) (by norm_num) (nz5 (by norm_num)) 586153 g586153 (by norm_num)

-- a an odd multiple of 1039: 3 divides 2^1039 + 1 and 47 + 1.
theorem c20_d1039 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1039 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g155851 : 155851 ∈ P := S2 155851 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 155851) (x := 1 + 2 ^ 1039) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g47 : 47 ∈ P := S1 47 (by norm_num) (by norm_num) (nz5 (by norm_num)) 155851 g155851 (by norm_num)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 1039) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 47 g47 (by norm_num)

-- a an odd multiple of 1051: 3^2 divides 26015176530521 + 1.
theorem c20_d1051 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1051 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g26015176530521 : 26015176530521 ∈ P := S2 26015176530521 prime_26015176530521 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 26015176530521) (x := 1 + 2 ^ 1051) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 26015176530521 g26015176530521 (by norm_num)

-- a an odd multiple of 1063: 3^2 divides 114584129081 + 1.
theorem c20_d1063 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1063 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g114584129081 : 114584129081 ∈ P := S2 114584129081 prime_114584129081 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 114584129081) (x := 1 + 2 ^ 1063) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 114584129081 g114584129081 (by norm_num)

-- a an odd multiple of 1069: 7 divides 13 + 1 and 7573 + 1.
theorem c20_d1069 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1069 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, S3, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (nz5 (by norm_num)) (by norm_num)
  have g7681945177 : 7681945177 ∈ P := S2 7681945177 prime_7681945177 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 7681945177) (x := 1 + 2 ^ 1069) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g7573 : 7573 ∈ P := S1 7573 (by norm_num) (by norm_num) (nz5 (by norm_num)) 7681945177 g7681945177 (by norm_num)
  exact absurd (S3 7 (by norm_num) (by norm_num) (nz5 (by norm_num)) 13 g13 7573 g7573 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 1087: 3 divides 2^1087 + 1 and 121398914459 + 1.
theorem c20_d1087 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1087 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g121398914459 : 121398914459 ∈ P := S2 121398914459 prime_121398914459 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 121398914459) (x := 1 + 2 ^ 1087) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 1087) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 121398914459 g121398914459 (by norm_num)

-- a an odd multiple of 1093: 3 divides 2^1093 + 1 and 306041 + 1.
theorem c20_d1093 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1093 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g306041 : 306041 ∈ P := S2 306041 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 306041) (x := 1 + 2 ^ 1093) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 1093) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 306041 g306041 (by norm_num)

-- a an odd multiple of 1117: 3^2 divides 1619 + 1.
theorem c20_d1117 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1117 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g70533063399945787 : 70533063399945787 ∈ P := S2 70533063399945787 prime_70533063399945787 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 70533063399945787) (x := 1 + 2 ^ 1117) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g1619 : 1619 ∈ P := S1 1619 (by norm_num) (by norm_num) (nz5 (by norm_num)) 70533063399945787 g70533063399945787 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 1619 g1619 (by norm_num)

-- a an odd multiple of 1123: 7^2 divides 97 + 1.
theorem c20_d1123 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1123 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g26664334916566271989490176818526188623612993733773073764132624439822811 : 26664334916566271989490176818526188623612993733773073764132624439822811 ∈ P := S2 26664334916566271989490176818526188623612993733773073764132624439822811 prime_26664334916566271989490176818526188623612993733773073764132624439822811 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 26664334916566271989490176818526188623612993733773073764132624439822811) (x := 1 + 2 ^ 1123) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g97 : 97 ∈ P := S1 97 (by norm_num) (by norm_num) (nz5 (by norm_num)) 26664334916566271989490176818526188623612993733773073764132624439822811 g26664334916566271989490176818526188623612993733773073764132624439822811 (by norm_num)
  exact S6 7 (by norm_num) (by norm_num) (nz5 (by norm_num)) 97 g97 (by norm_num)

-- a an odd multiple of 1129: 3^2 divides 5297035427 + 1.
theorem c20_d1129 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1129 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g5297035427 : 5297035427 ∈ P := S2 5297035427 prime_5297035427 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 5297035427) (x := 1 + 2 ^ 1129) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 5297035427 g5297035427 (by norm_num)

-- a an odd multiple of 1153: 3 divides 2^1153 + 1 and 101 + 1.
theorem c20_d1153 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1153 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g27673 : 27673 ∈ P := S2 27673 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 27673) (x := 1 + 2 ^ 1153) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g101 : 101 ∈ P := S1 101 (by norm_num) (by norm_num) (nz5 (by norm_num)) 27673 g27673 (by norm_num)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 1153) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 101 g101 (by norm_num)

-- a an odd multiple of 1171: 3 divides 2^1171 + 1 and 25763 + 1.
theorem c20_d1171 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1171 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g25763 : 25763 ∈ P := S2 25763 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 25763) (x := 1 + 2 ^ 1171) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 1171) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 25763 g25763 (by norm_num)

-- a an odd multiple of 1201: 3 divides 2^1201 + 1 and 481001 + 1.
theorem c20_d1201 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1201 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g1924003 : 1924003 ∈ P := S2 1924003 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 1924003) (x := 1 + 2 ^ 1201) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g481001 : 481001 ∈ P := S1 481001 (by norm_num) (by norm_num) (nz5 (by norm_num)) 1924003 g1924003 (by norm_num)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 1201) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 481001 g481001 (by norm_num)

-- a an odd multiple of 1213: 3 divides 2^1213 + 1 and 1809697712203883 + 1.
theorem c20_d1213 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1213 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g1809697712203883 : 1809697712203883 ∈ P := S2 1809697712203883 prime_1809697712203883 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 1809697712203883) (x := 1 + 2 ^ 1213) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 1213) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 1809697712203883 g1809697712203883 (by norm_num)

-- a an odd multiple of 1231: 3^2 divides 5680156935617 + 1.
theorem c20_d1231 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1231 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g5680156935617 : 5680156935617 ∈ P := S2 5680156935617 prime_5680156935617 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 5680156935617) (x := 1 + 2 ^ 1231) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 5680156935617 g5680156935617 (by norm_num)

-- a an odd multiple of 1237: 3 divides 2^1237 + 1 and 19793 + 1.
theorem c20_d1237 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1237 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g19793 : 19793 ∈ P := S2 19793 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 19793) (x := 1 + 2 ^ 1237) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 1237) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 19793 g19793 (by norm_num)

-- a an odd multiple of 1249: 3 divides 2^1249 + 1 and 42467 + 1.
theorem c20_d1249 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1249 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g42467 : 42467 ∈ P := S2 42467 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 42467) (x := 1 + 2 ^ 1249) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 1249) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 42467 g42467 (by norm_num)

-- a an odd multiple of 1279: 7^2 divides 3107971 + 1.
theorem c20_d1279 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1279 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g3107971 : 3107971 ∈ P := S2 3107971 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 3107971) (x := 1 + 2 ^ 1279) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 7 (by norm_num) (by norm_num) (nz5 (by norm_num)) 3107971 g3107971 (by norm_num)

-- a an odd multiple of 1291: 3^2 divides 28403 + 1.
theorem c20_d1291 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1291 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g28403 : 28403 ∈ P := S2 28403 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 28403) (x := 1 + 2 ^ 1291) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 28403 g28403 (by norm_num)

-- a an odd multiple of 1297: 3 divides 2^1297 + 1 and 1973 + 1.
theorem c20_d1297 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1297 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g155752053019 : 155752053019 ∈ P := S2 155752053019 prime_155752053019 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 155752053019) (x := 1 + 2 ^ 1297) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g1973 : 1973 ∈ P := S1 1973 (by norm_num) (by norm_num) (nz5 (by norm_num)) 155752053019 g155752053019 (by norm_num)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 1297) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 1973 g1973 (by norm_num)

-- a an odd multiple of 1303: 3^2 divides 53204563686868873577 + 1.
theorem c20_d1303 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1303 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g53204563686868873577 : 53204563686868873577 ∈ P := S2 53204563686868873577 prime_53204563686868873577 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 53204563686868873577) (x := 1 + 2 ^ 1303) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 53204563686868873577 g53204563686868873577 (by norm_num)

-- a an odd multiple of 1321: 13 divides 5^2 + 1 and 103 + 1.
theorem c20_d1321 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1321 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, -, -, S8⟩ := facts hP (hK5 2) E
  have g102725010187 : 102725010187 ∈ P := S2 102725010187 prime_102725010187 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 102725010187) (x := 1 + 2 ^ 1321) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g103 : 103 ∈ P := S1 103 (by norm_num) (by norm_num) (nz5 (by norm_num)) 102725010187 g102725010187 (by norm_num)
  exact S8 13 (by norm_num) (by norm_num) (nz5 (by norm_num)) (by norm_num) 103 g103 (by norm_num)

-- a an odd multiple of 1327: 3 divides 2^1327 + 1 and 11 + 1.
theorem c20_d1327 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1327 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g7963 : 7963 ∈ P := S2 7963 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 7963) (x := 1 + 2 ^ 1327) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (nz5 (by norm_num)) 7963 g7963 (by norm_num)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 1327) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 11 g11 (by norm_num)

-- a an odd multiple of 1381: 3^2 divides 113738319658736238418567892099 + 1.
theorem c20_d1381 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1381 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g113738319658736238418567892099 : 113738319658736238418567892099 ∈ P := S2 113738319658736238418567892099 prime_113738319658736238418567892099 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 113738319658736238418567892099) (x := 1 + 2 ^ 1381) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 113738319658736238418567892099 g113738319658736238418567892099 (by norm_num)

-- a an odd multiple of 1399: 13 divides 5^2 + 1 and 103 + 1.
theorem c20_d1399 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1399 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, -, -, S8⟩ := facts hP (hK5 2) E
  have g33577 : 33577 ∈ P := S2 33577 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 33577) (x := 1 + 2 ^ 1399) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g103 : 103 ∈ P := S1 103 (by norm_num) (by norm_num) (nz5 (by norm_num)) 33577 g33577 (by norm_num)
  exact S8 13 (by norm_num) (by norm_num) (nz5 (by norm_num)) (by norm_num) 103 g103 (by norm_num)

-- a an odd multiple of 1423: 3 divides 2^1423 + 1 and 113 + 1.
theorem c20_d1423 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1423 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g112804057 : 112804057 ∈ P := S2 112804057 prime_112804057 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 112804057) (x := 1 + 2 ^ 1423) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g113 : 113 ∈ P := S1 113 (by norm_num) (by norm_num) (nz5 (by norm_num)) 112804057 g112804057 (by norm_num)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 1423) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 113 g113 (by norm_num)

-- a an odd multiple of 1429: 7 divides 1548733385688649 + 1 and 13 + 1.
theorem c20_d1429 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1429 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, S3, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g1548733385688649 : 1548733385688649 ∈ P := S2 1548733385688649 prime_1548733385688649 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 1548733385688649) (x := 1 + 2 ^ 1429) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (nz5 (by norm_num)) (by norm_num)
  exact absurd (S3 7 (by norm_num) (by norm_num) (nz5 (by norm_num)) 1548733385688649 g1548733385688649 13 g13 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 1447: 3 divides 2^1447 + 1 and 1238047460871066723939449 + 1.
theorem c20_d1447 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1447 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g1238047460871066723939449 : 1238047460871066723939449 ∈ P := S2 1238047460871066723939449 prime_1238047460871066723939449 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 1238047460871066723939449) (x := 1 + 2 ^ 1447) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 1447) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 1238047460871066723939449 g1238047460871066723939449 (by norm_num)

-- a an odd multiple of 1453: 7^2 divides 1567 + 1.
theorem c20_d1453 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1453 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g52447489 : 52447489 ∈ P := S2 52447489 prime_52447489 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 52447489) (x := 1 + 2 ^ 1453) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g1567 : 1567 ∈ P := S1 1567 (by norm_num) (by norm_num) (nz5 (by norm_num)) 52447489 g52447489 (by norm_num)
  exact S6 7 (by norm_num) (by norm_num) (nz5 (by norm_num)) 1567 g1567 (by norm_num)

-- a an odd multiple of 1459: 3 divides 2^1459 + 1 and 3538966647017366178930789720372963502043 + 1.
theorem c20_d1459 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1459 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g3538966647017366178930789720372963502043 : 3538966647017366178930789720372963502043 ∈ P := S2 3538966647017366178930789720372963502043 prime_3538966647017366178930789720372963502043 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 3538966647017366178930789720372963502043) (x := 1 + 2 ^ 1459) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 1459) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 3538966647017366178930789720372963502043 g3538966647017366178930789720372963502043 (by norm_num)

-- a an odd multiple of 1471: 7 divides 87238974742151728369 + 1 and 13 + 1.
theorem c20_d1471 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1471 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, S3, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g87238974742151728369 : 87238974742151728369 ∈ P := S2 87238974742151728369 prime_87238974742151728369 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 87238974742151728369) (x := 1 + 2 ^ 1471) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (nz5 (by norm_num)) (by norm_num)
  exact absurd (S3 7 (by norm_num) (by norm_num) (nz5 (by norm_num)) 87238974742151728369 g87238974742151728369 13 g13 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 1483: 3^2 divides 31994243 + 1.
theorem c20_d1483 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1483 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g31994243 : 31994243 ∈ P := S2 31994243 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 31994243) (x := 1 + 2 ^ 1483) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 31994243 g31994243 (by norm_num)

-- a an odd multiple of 1489: 3^2 divides 12344417513 + 1.
theorem c20_d1489 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1489 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g12344417513 : 12344417513 ∈ P := S2 12344417513 prime_12344417513 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 12344417513) (x := 1 + 2 ^ 1489) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 12344417513 g12344417513 (by norm_num)

-- a an odd multiple of 1531: 3 divides 2^1531 + 1 and 2297 + 1.
theorem c20_d1531 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1531 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g9187 : 9187 ∈ P := S2 9187 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 9187) (x := 1 + 2 ^ 1531) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g2297 : 2297 ∈ P := S1 2297 (by norm_num) (by norm_num) (nz5 (by norm_num)) 9187 g9187 (by norm_num)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 1531) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 2297 g2297 (by norm_num)

-- a an odd multiple of 1543: 3 divides 2^1543 + 1 and 4551233 + 1.
theorem c20_d1543 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1543 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g45512329 : 45512329 ∈ P := S2 45512329 prime_45512329 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 45512329) (x := 1 + 2 ^ 1543) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g4551233 : 4551233 ∈ P := S1 4551233 (by norm_num) (by norm_num) (nz5 (by norm_num)) 45512329 g45512329 (by norm_num)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 1543) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 4551233 g4551233 (by norm_num)

-- a an odd multiple of 1549: 3^2 divides 107 + 1.
theorem c20_d1549 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1549 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g1592062201 : 1592062201 ∈ P := S2 1592062201 prime_1592062201 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 1592062201) (x := 1 + 2 ^ 1549) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g107 : 107 ∈ P := S1 107 (by norm_num) (by norm_num) (nz5 (by norm_num)) 1592062201 g1592062201 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 107 g107 (by norm_num)

-- a an odd multiple of 1567: 3 divides 2^1567 + 1 and 2351 + 1.
theorem c20_d1567 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1567 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g9403 : 9403 ∈ P := S2 9403 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 9403) (x := 1 + 2 ^ 1567) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g2351 : 2351 ∈ P := S1 2351 (by norm_num) (by norm_num) (nz5 (by norm_num)) 9403 g9403 (by norm_num)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 1567) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 2351 g2351 (by norm_num)

-- a an odd multiple of 1579: 3^2 divides 34739 + 1.
theorem c20_d1579 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1579 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g34739 : 34739 ∈ P := S2 34739 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 34739) (x := 1 + 2 ^ 1579) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 34739 g34739 (by norm_num)

-- a an odd multiple of 1597: 3 divides 2^1597 + 1 and 154414585369847792316011 + 1.
theorem c20_d1597 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1597 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g154414585369847792316011 : 154414585369847792316011 ∈ P := S2 154414585369847792316011 prime_154414585369847792316011 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 154414585369847792316011) (x := 1 + 2 ^ 1597) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 1597) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 154414585369847792316011 g154414585369847792316011 (by norm_num)

-- a an odd multiple of 1609: 3^2 divides 16091 + 1.
theorem c20_d1609 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1609 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g16091 : 16091 ∈ P := S2 16091 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 16091) (x := 1 + 2 ^ 1609) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 16091 g16091 (by norm_num)

-- a an odd multiple of 1621: 3^2 divides 647 + 1.
theorem c20_d1621 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1621 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g2995609 : 2995609 ∈ P := S2 2995609 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 2995609) (x := 1 + 2 ^ 1621) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g647 : 647 ∈ P := S1 647 (by norm_num) (by norm_num) (nz5 (by norm_num)) 2995609 g2995609 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 647 g647 (by norm_num)

-- a an odd multiple of 1627: 3^2 divides 1978433 + 1.
theorem c20_d1627 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1627 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g1978433 : 1978433 ∈ P := S2 1978433 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 1978433) (x := 1 + 2 ^ 1627) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 1978433 g1978433 (by norm_num)

-- a an odd multiple of 1657: 7 divides 1151642337187 + 1 and 13 + 1.
theorem c20_d1657 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1657 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, S3, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g1151642337187 : 1151642337187 ∈ P := S2 1151642337187 prime_1151642337187 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 1151642337187) (x := 1 + 2 ^ 1657) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (nz5 (by norm_num)) (by norm_num)
  exact absurd (S3 7 (by norm_num) (by norm_num) (nz5 (by norm_num)) 1151642337187 g1151642337187 13 g13 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 1663: 3^2 divides 128103172114064024002337 + 1.
theorem c20_d1663 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1663 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g128103172114064024002337 : 128103172114064024002337 ∈ P := S2 128103172114064024002337 prime_128103172114064024002337 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 128103172114064024002337) (x := 1 + 2 ^ 1663) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 128103172114064024002337 g128103172114064024002337 (by norm_num)

-- a an odd multiple of 1669: 3 divides 2^1669 + 1 and 16691 + 1.
theorem c20_d1669 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1669 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g16691 : 16691 ∈ P := S2 16691 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 16691) (x := 1 + 2 ^ 1669) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 1669) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 16691 g16691 (by norm_num)

-- a an odd multiple of 1693: 3 divides 2^1693 + 1 and 4948983910284158284280949700383491609217577054379 + 1.
theorem c20_d1693 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1693 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g4948983910284158284280949700383491609217577054379 : 4948983910284158284280949700383491609217577054379 ∈ P := S2 4948983910284158284280949700383491609217577054379 prime_4948983910284158284280949700383491609217577054379 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 4948983910284158284280949700383491609217577054379) (x := 1 + 2 ^ 1693) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 1693) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 4948983910284158284280949700383491609217577054379 g4948983910284158284280949700383491609217577054379 (by norm_num)

-- a an odd multiple of 1699: 3 divides 2^1699 + 1 and 118931 + 1.
theorem c20_d1699 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1699 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g118931 : 118931 ∈ P := S2 118931 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 118931) (x := 1 + 2 ^ 1699) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 1699) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 118931 g118931 (by norm_num)

-- a an odd multiple of 1723: 3^2 divides 12209847761303531 + 1.
theorem c20_d1723 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1723 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g12209847761303531 : 12209847761303531 ∈ P := S2 12209847761303531 prime_12209847761303531 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 12209847761303531) (x := 1 + 2 ^ 1723) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 12209847761303531 g12209847761303531 (by norm_num)

-- a an odd multiple of 1741: 3 divides 2^1741 + 1 and 130611215276657814724409 + 1.
theorem c20_d1741 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1741 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g130611215276657814724409 : 130611215276657814724409 ∈ P := S2 130611215276657814724409 prime_130611215276657814724409 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 130611215276657814724409) (x := 1 + 2 ^ 1741) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 1741) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 130611215276657814724409 g130611215276657814724409 (by norm_num)

-- a an odd multiple of 1747: 3 divides 2^1747 + 1 and 1016572313 + 1.
theorem c20_d1747 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1747 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g1016572313 : 1016572313 ∈ P := S2 1016572313 prime_1016572313 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 1016572313) (x := 1 + 2 ^ 1747) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 1747) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 1016572313 g1016572313 (by norm_num)

-- a an odd multiple of 1753: 3^2 divides 4893972298219433321 + 1.
theorem c20_d1753 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1753 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g4893972298219433321 : 4893972298219433321 ∈ P := S2 4893972298219433321 prime_4893972298219433321 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 4893972298219433321) (x := 1 + 2 ^ 1753) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 4893972298219433321 g4893972298219433321 (by norm_num)

-- a an odd multiple of 1759: 3 divides 2^1759 + 1 and 15099257 + 1.
theorem c20_d1759 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1759 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, S4, -, -, -, -⟩ := facts hP (hK5 2) E
  have g15099257 : 15099257 ∈ P := S2 15099257 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 15099257) (x := 1 + 2 ^ 1759) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S4 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) ((tw (c := 3) (x := 1 + 2 ^ 1759) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd) 15099257 g15099257 (by norm_num)

-- a an odd multiple of 202: 3^2 divides 809 + 1.
theorem c20_d202 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 202 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g809 : 809 ∈ P := S2 809 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 809) (x := 1 + 2 ^ 202) (by push_cast; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 809 g809 (by norm_num)

-- a an odd multiple of 206: 3^2 divides 41201 + 1.
theorem c20_d206 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 206 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g41201 : 41201 ∈ P := S2 41201 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 41201) (x := 1 + 2 ^ 206) (by push_cast; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 41201 g41201 (by norm_num)

-- a an odd multiple of 214: 13 divides 5^2 + 1 and 857 + 1.
theorem c20_d214 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 214 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, -, -, S8⟩ := facts hP (hK5 2) E
  have g857 : 857 ∈ P := S2 857 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 857) (x := 1 + 2 ^ 214) (by push_cast; reduce_mod_char)).trans hd)
  exact S8 13 (by norm_num) (by norm_num) (nz5 (by norm_num)) (by norm_num) 857 g857 (by norm_num)

-- a an odd multiple of 218: 3^2 divides 5669 + 1.
theorem c20_d218 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 218 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g5669 : 5669 ∈ P := S2 5669 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 5669) (x := 1 + 2 ^ 218) (by push_cast; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 5669 g5669 (by norm_num)

-- a an odd multiple of 226: 7^2 divides 58309 + 1.
theorem c20_d226 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 226 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g58309 : 58309 ∈ P := S2 58309 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 58309) (x := 1 + 2 ^ 226) (by push_cast; reduce_mod_char)).trans hd)
  exact S6 7 (by norm_num) (by norm_num) (nz5 (by norm_num)) 58309 g58309 (by norm_num)

-- a an odd multiple of 254: 13 divides 5^2 + 1 and 18797 + 1.
theorem c20_d254 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 254 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, -, -, S8⟩ := facts hP (hK5 2) E
  have g18797 : 18797 ∈ P := S2 18797 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 18797) (x := 1 + 2 ^ 254) (by push_cast; reduce_mod_char)).trans hd)
  exact S8 13 (by norm_num) (by norm_num) (nz5 (by norm_num)) (by norm_num) 18797 g18797 (by norm_num)

-- a an odd multiple of 262: 3^2 divides 269665073 + 1.
theorem c20_d262 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 262 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g269665073 : 269665073 ∈ P := S2 269665073 prime_269665073 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 269665073) (x := 1 + 2 ^ 262) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 269665073 g269665073 (by norm_num)

-- a an odd multiple of 274: 3^2 divides 23633 + 1.
theorem c20_d274 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 274 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g189061 : 189061 ∈ P := S2 189061 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 189061) (x := 1 + 2 ^ 274) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g94531 : 94531 ∈ P := S1 94531 (by norm_num) (by norm_num) (nz5 (by norm_num)) 189061 g189061 (by norm_num)
  have g23633 : 23633 ∈ P := S1 23633 (by norm_num) (by norm_num) (nz5 (by norm_num)) 94531 g94531 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 23633 g23633 (by norm_num)

-- a an odd multiple of 278: 3^2 divides 557 + 1.
theorem c20_d278 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 278 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g557 : 557 ∈ P := S2 557 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 557) (x := 1 + 2 ^ 278) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 557 g557 (by norm_num)

-- a an odd multiple of 298: 3^2 divides 179 + 1.
theorem c20_d298 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 298 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g1789 : 1789 ∈ P := S2 1789 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 1789) (x := 1 + 2 ^ 298) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g179 : 179 ∈ P := S1 179 (by norm_num) (by norm_num) (nz5 (by norm_num)) 1789 g1789 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 179 g179 (by norm_num)

-- a an odd multiple of 302: 11^2 divides 67759 + 1.
theorem c20_d302 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 302 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g2854495385411919762116496381035264358442074113 : 2854495385411919762116496381035264358442074113 ∈ P := S2 2854495385411919762116496381035264358442074113 prime_2854495385411919762116496381035264358442074113 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 2854495385411919762116496381035264358442074113) (x := 1 + 2 ^ 302) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g18837001 : 18837001 ∈ P := S1 18837001 (by norm_num) (by norm_num) (nz5 (by norm_num)) 2854495385411919762116496381035264358442074113 g2854495385411919762116496381035264358442074113 (by norm_num)
  have g67759 : 67759 ∈ P := S1 67759 (by norm_num) (by norm_num) (nz5 (by norm_num)) 18837001 g18837001 (by norm_num)
  exact S6 11 (by norm_num) (by norm_num) (nz5 (by norm_num)) 67759 g67759 (by norm_num)

-- a an odd multiple of 314: 3^2 divides 1493 + 1.
theorem c20_d314 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 314 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g2790467761 : 2790467761 ∈ P := S2 2790467761 prime_2790467761 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 2790467761) (x := 1 + 2 ^ 314) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g1493 : 1493 ∈ P := S1 1493 (by norm_num) (by norm_num) (nz5 (by norm_num)) 2790467761 g2790467761 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 1493 g1493 (by norm_num)

-- a an odd multiple of 326: 3^2 divides 7807049 + 1.
theorem c20_d326 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 326 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g7807049 : 7807049 ∈ P := S2 7807049 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 7807049) (x := 1 + 2 ^ 326) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 7807049 g7807049 (by norm_num)

-- a an odd multiple of 334: 7 divides 75005713 + 1 and 13 + 1.
theorem c20_d334 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 334 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, S3, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g75005713 : 75005713 ∈ P := S2 75005713 prime_75005713 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 75005713) (x := 1 + 2 ^ 334) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (nz5 (by norm_num)) (by norm_num)
  exact absurd (S3 7 (by norm_num) (by norm_num) (nz5 (by norm_num)) 75005713 g75005713 13 g13 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 346: 3 divides 13625405957 + 1 and 11 + 1.
theorem c20_d346 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 346 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, S3, -, -, -, -, -⟩ := facts hP (hK5 2) E
  have g13625405957 : 13625405957 ∈ P := S2 13625405957 prime_13625405957 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 13625405957) (x := 1 + 2 ^ 346) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (nz5 (by norm_num)) 13625405957 g13625405957 (by norm_num)
  have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (nz5 (by norm_num)) 43 g43 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 13625405957 g13625405957 11 g11 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 358: 7 divides 31815461 + 1 and 13 + 1.
theorem c20_d358 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 358 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, S3, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g31815461 : 31815461 ∈ P := S2 31815461 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 31815461) (x := 1 + 2 ^ 358) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (nz5 (by norm_num)) (by norm_num)
  exact absurd (S3 7 (by norm_num) (by norm_num) (nz5 (by norm_num)) 31815461 g31815461 13 g13 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 362: 3^2 divides 9413 + 1.
theorem c20_d362 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 362 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g9413 : 9413 ∈ P := S2 9413 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 9413) (x := 1 + 2 ^ 362) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 9413 g9413 (by norm_num)

-- a an odd multiple of 382: 7^2 divides 3821 + 1.
theorem c20_d382 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 382 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g3821 : 3821 ∈ P := S2 3821 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 3821) (x := 1 + 2 ^ 382) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 7 (by norm_num) (by norm_num) (nz5 (by norm_num)) 3821 g3821 (by norm_num)

-- a an odd multiple of 386: 3^2 divides 773 + 1.
theorem c20_d386 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 386 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g773 : 773 ∈ P := S2 773 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 773) (x := 1 + 2 ^ 386) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 773 g773 (by norm_num)

-- a an odd multiple of 394: 7 divides 52009 + 1 and 13 + 1.
theorem c20_d394 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 394 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, S3, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g52009 : 52009 ∈ P := S2 52009 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 52009) (x := 1 + 2 ^ 394) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (nz5 (by norm_num)) (by norm_num)
  exact absurd (S3 7 (by norm_num) (by norm_num) (nz5 (by norm_num)) 52009 g52009 13 g13 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 398: 7 divides 797 + 1 and 13 + 1.
theorem c20_d398 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 398 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, S3, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g797 : 797 ∈ P := S2 797 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 797) (x := 1 + 2 ^ 398) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (nz5 (by norm_num)) (by norm_num)
  exact absurd (S3 7 (by norm_num) (by norm_num) (nz5 (by norm_num)) 797 g797 13 g13 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 422: 3^2 divides 95110361 + 1.
theorem c20_d422 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 422 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g95110361 : 95110361 ∈ P := S2 95110361 prime_95110361 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 95110361) (x := 1 + 2 ^ 422) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 95110361 g95110361 (by norm_num)

-- a an odd multiple of 446: 3 divides 11597 + 1 and 6530333 + 1.
theorem c20_d446 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 446 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, S3, -, -, -, -, -⟩ := facts hP (hK5 2) E
  have g11597 : 11597 ∈ P := S2 11597 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 11597) (x := 1 + 2 ^ 446) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g6530333 : 6530333 ∈ P := S2 6530333 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 6530333) (x := 1 + 2 ^ 446) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact absurd (S3 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 11597 g11597 6530333 g6530333 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 454: 5^3 divides (2^454 + 1) * prod (p + 1) over p in {5449}.
theorem c20_d454 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 454 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, -, -, -⟩ := facts hP (hK5 2) E
  have g5449 : 5449 ∈ P := S2 5449 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 5449) (x := 1 + 2 ^ 454) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have b0 : (∅ : Finset ℕ) ⊆ P ∧ 5 ^ 0 ∣ ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
    ⟨Finset.empty_subset _, by rw [pow_zero]; exact one_dvd _⟩
  have b1 := bud5_cons b0 g5449 (by simp) (by norm_num : 5 ^ 2 ∣ 5449 + 1)
  exact bud5_kill (i := 1) hP h5 E hd b1.1 (tw (c := 5) (x := 1 + 2 ^ 454) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)) (by norm_num) b1.2

-- a an odd multiple of 458: 5^4 divides (2^458 + 1) * prod (p + 1) over p in {2749}.
theorem c20_d458 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 458 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, -, -, -⟩ := facts hP (hK5 2) E
  have g2749 : 2749 ∈ P := S2 2749 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 2749) (x := 1 + 2 ^ 458) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have b0 : (∅ : Finset ℕ) ⊆ P ∧ 5 ^ 0 ∣ ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
    ⟨Finset.empty_subset _, by rw [pow_zero]; exact one_dvd _⟩
  have b1 := bud5_cons b0 g2749 (by simp) (by norm_num : 5 ^ 3 ∣ 2749 + 1)
  exact bud5_kill (i := 1) hP h5 E hd b1.1 (tw (c := 5) (x := 1 + 2 ^ 458) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)) (by norm_num) b1.2

-- a an odd multiple of 466: 13^2 divides 30757 + 1.
theorem c20_d466 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 466 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g30757 : 30757 ∈ P := S2 30757 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 30757) (x := 1 + 2 ^ 466) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 13 (by norm_num) (by norm_num) (nz5 (by norm_num)) 30757 g30757 (by norm_num)

-- a an odd multiple of 478: 13 divides 5^2 + 1 and 77852679293 + 1.
theorem c20_d478 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 478 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, -, -, S8⟩ := facts hP (hK5 2) E
  have g77852679293 : 77852679293 ∈ P := S2 77852679293 prime_77852679293 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 77852679293) (x := 1 + 2 ^ 478) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S8 13 (by norm_num) (by norm_num) (nz5 (by norm_num)) (by norm_num) 77852679293 g77852679293 (by norm_num)

-- a an odd multiple of 482: 3^2 divides 251 + 1.
theorem c20_d482 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 482 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g15594629 : 15594629 ∈ P := S2 15594629 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 15594629) (x := 1 + 2 ^ 482) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g251 : 251 ∈ P := S1 251 (by norm_num) (by norm_num) (nz5 (by norm_num)) 15594629 g15594629 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 251 g251 (by norm_num)

-- a an odd multiple of 502: 3^2 divides 5021 + 1.
theorem c20_d502 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 502 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g5021 : 5021 ∈ P := S2 5021 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 5021) (x := 1 + 2 ^ 502) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 5021 g5021 (by norm_num)

-- a an odd multiple of 514: 3^2 divides 71 + 1.
theorem c20_d514 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 514 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g28564009 : 28564009 ∈ P := S2 28564009 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 28564009) (x := 1 + 2 ^ 514) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g71 : 71 ∈ P := S1 71 (by norm_num) (by norm_num) (nz5 (by norm_num)) 28564009 g28564009 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 71 g71 (by norm_num)

-- a an odd multiple of 526: 3^2 divides 731141 + 1.
theorem c20_d526 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 526 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g731141 : 731141 ∈ P := S2 731141 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 731141) (x := 1 + 2 ^ 526) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 731141 g731141 (by norm_num)

-- a an odd multiple of 538: 3^2 divides 5381 + 1.
theorem c20_d538 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 538 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g5381 : 5381 ∈ P := S2 5381 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 5381) (x := 1 + 2 ^ 538) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 5381 g5381 (by norm_num)

-- a an odd multiple of 542: 3^2 divides 1309337 + 1.
theorem c20_d542 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 542 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g10474693 : 10474693 ∈ P := S2 10474693 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 10474693) (x := 1 + 2 ^ 542) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g5237347 : 5237347 ∈ P := S1 5237347 (by norm_num) (by norm_num) (nz5 (by norm_num)) 10474693 g10474693 (by norm_num)
  have g1309337 : 1309337 ∈ P := S1 1309337 (by norm_num) (by norm_num) (nz5 (by norm_num)) 5237347 g5237347 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 1309337 g1309337 (by norm_num)

-- a an odd multiple of 554: 3^2 divides 14543 + 1.
theorem c20_d554 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 554 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g232681 : 232681 ∈ P := S2 232681 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 232681) (x := 1 + 2 ^ 554) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g116341 : 116341 ∈ P := S1 116341 (by norm_num) (by norm_num) (nz5 (by norm_num)) 232681 g232681 (by norm_num)
  have g58171 : 58171 ∈ P := S1 58171 (by norm_num) (by norm_num) (nz5 (by norm_num)) 116341 g116341 (by norm_num)
  have g14543 : 14543 ∈ P := S1 14543 (by norm_num) (by norm_num) (nz5 (by norm_num)) 58171 g58171 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 14543 g14543 (by norm_num)

-- a an odd multiple of 562: 7 divides 3373 + 1 and 3827221 + 1.
theorem c20_d562 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 562 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, S3, -, -, -, -, -⟩ := facts hP (hK5 2) E
  have g3373 : 3373 ∈ P := S2 3373 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 3373) (x := 1 + 2 ^ 562) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g3827221 : 3827221 ∈ P := S2 3827221 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 3827221) (x := 1 + 2 ^ 562) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact absurd (S3 7 (by norm_num) (by norm_num) (nz5 (by norm_num)) 3373 g3373 3827221 g3827221 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 566: 3^2 divides 449 + 1.
theorem c20_d566 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 566 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g3108270227561166513471139050917630250627849827446163307471742778796333223910258298061 : 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061 ∈ P := S2 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061 prime_3108270227561166513471139050917630250627849827446163307471742778796333223910258298061 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061) (x := 1 + 2 ^ 566) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g449 : 449 ∈ P := S1 449 (by norm_num) (by norm_num) (nz5 (by norm_num)) 3108270227561166513471139050917630250627849827446163307471742778796333223910258298061 g3108270227561166513471139050917630250627849827446163307471742778796333223910258298061 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 449 g449 (by norm_num)

-- a an odd multiple of 586: 17^2 divides 22396921 + 1.
theorem c20_d586 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 586 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g22396921 : 22396921 ∈ P := S2 22396921 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 22396921) (x := 1 + 2 ^ 586) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 17 (by norm_num) (by norm_num) (nz5 (by norm_num)) 22396921 g22396921 (by norm_num)

-- a an odd multiple of 614: 3^2 divides 93329 + 1.
theorem c20_d614 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 614 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g93329 : 93329 ∈ P := S2 93329 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 93329) (x := 1 + 2 ^ 614) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 93329 g93329 (by norm_num)

-- a an odd multiple of 622: 3^2 divides 21149 + 1.
theorem c20_d622 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 622 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g21149 : 21149 ∈ P := S2 21149 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 21149) (x := 1 + 2 ^ 622) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 21149 g21149 (by norm_num)

-- a an odd multiple of 626: 3^2 divides 42569 + 1.
theorem c20_d626 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 626 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g42569 : 42569 ∈ P := S2 42569 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 42569) (x := 1 + 2 ^ 626) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 42569 g42569 (by norm_num)

-- a an odd multiple of 634: 3^2 divides 344759057 + 1.
theorem c20_d634 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 634 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g344759057 : 344759057 ∈ P := S2 344759057 prime_344759057 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 344759057) (x := 1 + 2 ^ 634) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 344759057 g344759057 (by norm_num)

-- a an odd multiple of 662: 3 divides 589181 + 1 and 11 + 1.
theorem c20_d662 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 662 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, S3, -, -, -, -, -⟩ := facts hP (hK5 2) E
  have g589181 : 589181 ∈ P := S2 589181 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 589181) (x := 1 + 2 ^ 662) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (nz5 (by norm_num)) 589181 g589181 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 589181 g589181 11 g11 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 674: 3^2 divides 2549069 + 1.
theorem c20_d674 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 674 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g2549069 : 2549069 ∈ P := S2 2549069 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 2549069) (x := 1 + 2 ^ 674) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 2549069 g2549069 (by norm_num)

-- a an odd multiple of 694: 7 divides 5575597 + 1 and 13 + 1.
theorem c20_d694 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 694 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, S3, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g5575597 : 5575597 ∈ P := S2 5575597 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 5575597) (x := 1 + 2 ^ 694) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (nz5 (by norm_num)) (by norm_num)
  exact absurd (S3 7 (by norm_num) (by norm_num) (nz5 (by norm_num)) 5575597 g5575597 13 g13 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 698: 3^2 divides 763613 + 1.
theorem c20_d698 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 698 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g763613 : 763613 ∈ P := S2 763613 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 763613) (x := 1 + 2 ^ 698) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 763613 g763613 (by norm_num)

-- a an odd multiple of 706: 7 divides 13 + 1 and 22253377 + 1.
theorem c20_d706 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 706 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, S3, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (nz5 (by norm_num)) (by norm_num)
  have g18347988927920572092886567162416695526372519913346248798338768106859275713914500070771500472538615219486721 : 18347988927920572092886567162416695526372519913346248798338768106859275713914500070771500472538615219486721 ∈ P := S2 18347988927920572092886567162416695526372519913346248798338768106859275713914500070771500472538615219486721 prime_18347988927920572092886567162416695526372519913346248798338768106859275713914500070771500472538615219486721 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 18347988927920572092886567162416695526372519913346248798338768106859275713914500070771500472538615219486721) (x := 1 + 2 ^ 706) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g22253377 : 22253377 ∈ P := S1 22253377 (by norm_num) (by norm_num) (nz5 (by norm_num)) 18347988927920572092886567162416695526372519913346248798338768106859275713914500070771500472538615219486721 g18347988927920572092886567162416695526372519913346248798338768106859275713914500070771500472538615219486721 (by norm_num)
  exact absurd (S3 7 (by norm_num) (by norm_num) (nz5 (by norm_num)) 13 g13 22253377 g22253377 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 718: 13 divides 5^2 + 1 and 1429 + 1.
theorem c20_d718 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 718 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, -, -, S8⟩ := facts hP (hK5 2) E
  have g585889 : 585889 ∈ P := S2 585889 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 585889) (x := 1 + 2 ^ 718) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g1429 : 1429 ∈ P := S1 1429 (by norm_num) (by norm_num) (nz5 (by norm_num)) 585889 g585889 (by norm_num)
  exact S8 13 (by norm_num) (by norm_num) (nz5 (by norm_num)) (by norm_num) 1429 g1429 (by norm_num)

-- a an odd multiple of 734: 3 divides 300613450595050653169853516389035139504087366260264943426013315702268533480936328328948524855350568033150042113 + 1 and 23 + 1.
theorem c20_d734 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 734 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, S3, -, -, -, -, -⟩ := facts hP (hK5 2) E
  have g300613450595050653169853516389035139504087366260264943426013315702268533480936328328948524855350568033150042113 : 300613450595050653169853516389035139504087366260264943426013315702268533480936328328948524855350568033150042113 ∈ P := S2 300613450595050653169853516389035139504087366260264943426013315702268533480936328328948524855350568033150042113 prime_300613450595050653169853516389035139504087366260264943426013315702268533480936328328948524855350568033150042113 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 300613450595050653169853516389035139504087366260264943426013315702268533480936328328948524855350568033150042113) (x := 1 + 2 ^ 734) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g165963031279777 : 165963031279777 ∈ P := S1 165963031279777 prime_165963031279777 (by norm_num) (nz5 (by norm_num)) 300613450595050653169853516389035139504087366260264943426013315702268533480936328328948524855350568033150042113 g300613450595050653169853516389035139504087366260264943426013315702268533480936328328948524855350568033150042113 (by norm_num)
  have g23 : 23 ∈ P := S1 23 (by norm_num) (by norm_num) (nz5 (by norm_num)) 165963031279777 g165963031279777 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 300613450595050653169853516389035139504087366260264943426013315702268533480936328328948524855350568033150042113 g300613450595050653169853516389035139504087366260264943426013315702268533480936328328948524855350568033150042113 23 g23 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 746: 3^2 divides 1493 + 1.
theorem c20_d746 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 746 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g1493 : 1493 ∈ P := S2 1493 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 1493) (x := 1 + 2 ^ 746) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 1493 g1493 (by norm_num)

-- a an odd multiple of 758: 13 divides 5^2 + 1 and 4549 + 1.
theorem c20_d758 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 758 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, -, -, S8⟩ := facts hP (hK5 2) E
  have g4549 : 4549 ∈ P := S2 4549 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 4549) (x := 1 + 2 ^ 758) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S8 13 (by norm_num) (by norm_num) (nz5 (by norm_num)) (by norm_num) 4549 g4549 (by norm_num)

-- a an odd multiple of 766: 11^2 divides 4597 + 1.
theorem c20_d766 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 766 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g4597 : 4597 ∈ P := S2 4597 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 4597) (x := 1 + 2 ^ 766) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 11 (by norm_num) (by norm_num) (nz5 (by norm_num)) 4597 g4597 (by norm_num)

-- a an odd multiple of 778: 3^2 divides 17117 + 1.
theorem c20_d778 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 778 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g17117 : 17117 ∈ P := S2 17117 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 17117) (x := 1 + 2 ^ 778) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 17117 g17117 (by norm_num)

-- a an odd multiple of 794: 11^2 divides 25409 + 1.
theorem c20_d794 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 794 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g25409 : 25409 ∈ P := S2 25409 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 25409) (x := 1 + 2 ^ 794) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 11 (by norm_num) (by norm_num) (nz5 (by norm_num)) 25409 g25409 (by norm_num)

-- a an odd multiple of 802: 3^2 divides 107 + 1.
theorem c20_d802 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 802 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g3209 : 3209 ∈ P := S2 3209 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 3209) (x := 1 + 2 ^ 802) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g107 : 107 ∈ P := S1 107 (by norm_num) (by norm_num) (nz5 (by norm_num)) 3209 g3209 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 107 g107 (by norm_num)

-- a an odd multiple of 818: 3^2 divides 1637 + 1.
theorem c20_d818 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 818 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g1637 : 1637 ∈ P := S2 1637 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 1637) (x := 1 + 2 ^ 818) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 1637 g1637 (by norm_num)

-- a an odd multiple of 838: 3 divides 53633 + 1 and 63689 + 1.
theorem c20_d838 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 838 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, S3, -, -, -, -, -⟩ := facts hP (hK5 2) E
  have g53633 : 53633 ∈ P := S2 53633 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 53633) (x := 1 + 2 ^ 838) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g63689 : 63689 ∈ P := S2 63689 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 63689) (x := 1 + 2 ^ 838) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact absurd (S3 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 53633 g53633 63689 g63689 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 842: 3^2 divides 31142213 + 1.
theorem c20_d842 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 842 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g31142213 : 31142213 ∈ P := S2 31142213 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 31142213) (x := 1 + 2 ^ 842) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 31142213 g31142213 (by norm_num)

-- a an odd multiple of 862: 7^2 divides 97 + 1.
theorem c20_d862 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 862 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g91373 : 91373 ∈ P := S2 91373 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 91373) (x := 1 + 2 ^ 862) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g97 : 97 ∈ P := S1 97 (by norm_num) (by norm_num) (nz5 (by norm_num)) 91373 g91373 (by norm_num)
  exact S6 7 (by norm_num) (by norm_num) (nz5 (by norm_num)) 97 g97 (by norm_num)

-- a an odd multiple of 866: 17^2 divides 1733 + 1.
theorem c20_d866 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 866 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g1733 : 1733 ∈ P := S2 1733 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 1733) (x := 1 + 2 ^ 866) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 17 (by norm_num) (by norm_num) (nz5 (by norm_num)) 1733 g1733 (by norm_num)

-- a an odd multiple of 878: 37 divides 695377 + 1 and 9397 + 1.
theorem c20_d878 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 878 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, S3, -, -, -, -, -⟩ := facts hP (hK5 2) E
  have g695377 : 695377 ∈ P := S2 695377 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 695377) (x := 1 + 2 ^ 878) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g9397 : 9397 ∈ P := S1 9397 (by norm_num) (by norm_num) (nz5 (by norm_num)) 695377 g695377 (by norm_num)
  exact absurd (S3 37 (by norm_num) (by norm_num) (nz5 (by norm_num)) 695377 g695377 9397 g9397 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 886: 37^2 divides 773339215189 + 1.
theorem c20_d886 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 886 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g773339215189 : 773339215189 ∈ P := S2 773339215189 prime_773339215189 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 773339215189) (x := 1 + 2 ^ 886) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 37 (by norm_num) (by norm_num) (nz5 (by norm_num)) 773339215189 g773339215189 (by norm_num)

-- a an odd multiple of 898: 3 divides 3593 + 1 and 165233 + 1.
theorem c20_d898 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 898 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, S3, -, -, -, -, -⟩ := facts hP (hK5 2) E
  have g3593 : 3593 ∈ P := S2 3593 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 3593) (x := 1 + 2 ^ 898) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g165233 : 165233 ∈ P := S2 165233 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 165233) (x := 1 + 2 ^ 898) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact absurd (S3 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 3593 g3593 165233 g165233 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 914: 7 divides 13 + 1 and 83 + 1.
theorem c20_d914 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 914 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, S3, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (nz5 (by norm_num)) (by norm_num)
  have g71293 : 71293 ∈ P := S2 71293 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 71293) (x := 1 + 2 ^ 914) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g829 : 829 ∈ P := S1 829 (by norm_num) (by norm_num) (nz5 (by norm_num)) 71293 g71293 (by norm_num)
  have g83 : 83 ∈ P := S1 83 (by norm_num) (by norm_num) (nz5 (by norm_num)) 829 g829 (by norm_num)
  exact absurd (S3 7 (by norm_num) (by norm_num) (nz5 (by norm_num)) 13 g13 83 g83 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 922: 3 divides 14753 + 1 and 7278269 + 1.
theorem c20_d922 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 922 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, S3, -, -, -, -, -⟩ := facts hP (hK5 2) E
  have g14753 : 14753 ∈ P := S2 14753 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 14753) (x := 1 + 2 ^ 922) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g7278269 : 7278269 ∈ P := S2 7278269 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 7278269) (x := 1 + 2 ^ 922) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact absurd (S3 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 14753 g14753 7278269 g7278269 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 926: 3^2 divides 16694937341 + 1.
theorem c20_d926 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 926 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g16694937341 : 16694937341 ∈ P := S2 16694937341 prime_16694937341 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 16694937341) (x := 1 + 2 ^ 926) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 16694937341 g16694937341 (by norm_num)

-- a an odd multiple of 934: 13 divides 5^2 + 1 and 1372981 + 1.
theorem c20_d934 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 934 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, -, -, S8⟩ := facts hP (hK5 2) E
  have g1372981 : 1372981 ∈ P := S2 1372981 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 1372981) (x := 1 + 2 ^ 934) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S8 13 (by norm_num) (by norm_num) (nz5 (by norm_num)) (by norm_num) 1372981 g1372981 (by norm_num)

-- a an odd multiple of 958: 11 divides 39557737 + 1 and 571 + 1.
theorem c20_d958 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 958 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, S3, -, -, -, -, -⟩ := facts hP (hK5 2) E
  have g39557737 : 39557737 ∈ P := S2 39557737 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 39557737) (x := 1 + 2 ^ 958) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g571 : 571 ∈ P := S1 571 (by norm_num) (by norm_num) (nz5 (by norm_num)) 39557737 g39557737 (by norm_num)
  exact absurd (S3 11 (by norm_num) (by norm_num) (nz5 (by norm_num)) 39557737 g39557737 571 g571 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 974: 13 divides 5^2 + 1 and 1949 + 1.
theorem c20_d974 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 974 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, -, -, S8⟩ := facts hP (hK5 2) E
  have g1949 : 1949 ∈ P := S2 1949 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 1949) (x := 1 + 2 ^ 974) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S8 13 (by norm_num) (by norm_num) (nz5 (by norm_num)) (by norm_num) 1949 g1949 (by norm_num)

-- a an odd multiple of 982: 3 divides 3929 + 1 and 34631213 + 1.
theorem c20_d982 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 982 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, S3, -, -, -, -, -⟩ := facts hP (hK5 2) E
  have g3929 : 3929 ∈ P := S2 3929 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 3929) (x := 1 + 2 ^ 982) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g34631213 : 34631213 ∈ P := S2 34631213 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 34631213) (x := 1 + 2 ^ 982) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact absurd (S3 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 3929 g3929 34631213 g34631213 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 998: 3^2 divides 1997 + 1.
theorem c20_d998 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 998 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g1997 : 1997 ∈ P := S2 1997 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 1997) (x := 1 + 2 ^ 998) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 1997 g1997 (by norm_num)

-- a an odd multiple of 1006: 3^2 divides 10061 + 1.
theorem c20_d1006 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1006 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g10061 : 10061 ∈ P := S2 10061 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 10061) (x := 1 + 2 ^ 1006) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 10061 g10061 (by norm_num)

-- a an odd multiple of 1018: 7 divides 4073 + 1 and 103837 + 1.
theorem c20_d1018 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1018 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, S3, -, -, -, -, -⟩ := facts hP (hK5 2) E
  have g4073 : 4073 ∈ P := S2 4073 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 4073) (x := 1 + 2 ^ 1018) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g103837 : 103837 ∈ P := S2 103837 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 103837) (x := 1 + 2 ^ 1018) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact absurd (S3 7 (by norm_num) (by norm_num) (nz5 (by norm_num)) 4073 g4073 103837 g103837 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 1042: 7 divides 16673 + 1 and 13 + 1.
theorem c20_d1042 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1042 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, S3, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g16673 : 16673 ∈ P := S2 16673 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 16673) (x := 1 + 2 ^ 1042) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (nz5 (by norm_num)) (by norm_num)
  exact absurd (S3 7 (by norm_num) (by norm_num) (nz5 (by norm_num)) 16673 g16673 13 g13 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 1046: 3^2 divides 8369 + 1.
theorem c20_d1046 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1046 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g8369 : 8369 ∈ P := S2 8369 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 8369) (x := 1 + 2 ^ 1046) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 8369 g8369 (by norm_num)

-- a an odd multiple of 1082: 3^2 divides 17 + 1.
theorem c20_d1082 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1082 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g1281089 : 1281089 ∈ P := S2 1281089 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 1281089) (x := 1 + 2 ^ 1082) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g42703 : 42703 ∈ P := S1 42703 (by norm_num) (by norm_num) (nz5 (by norm_num)) 1281089 g1281089 (by norm_num)
  have g17 : 17 ∈ P := S1 17 (by norm_num) (by norm_num) (nz5 (by norm_num)) 42703 g42703 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 17 g17 (by norm_num)

-- a an odd multiple of 1094: 3^2 divides 107 + 1.
theorem c20_d1094 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1094 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g45232564075409 : 45232564075409 ∈ P := S2 45232564075409 prime_45232564075409 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 45232564075409) (x := 1 + 2 ^ 1094) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g281837 : 281837 ∈ P := S1 281837 (by norm_num) (by norm_num) (nz5 (by norm_num)) 45232564075409 g45232564075409 (by norm_num)
  have g107 : 107 ∈ P := S1 107 (by norm_num) (by norm_num) (nz5 (by norm_num)) 281837 g281837 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 107 g107 (by norm_num)

-- a an odd multiple of 1114: 3^2 divides 91441702997 + 1.
theorem c20_d1114 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1114 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g91441702997 : 91441702997 ∈ P := S2 91441702997 prime_91441702997 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 91441702997) (x := 1 + 2 ^ 1114) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 91441702997 g91441702997 (by norm_num)

-- a an odd multiple of 1126: 3^2 divides 89 + 1.
theorem c20_d1126 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1126 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g51797 : 51797 ∈ P := S2 51797 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 51797) (x := 1 + 2 ^ 1126) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g89 : 89 ∈ P := S1 89 (by norm_num) (by norm_num) (nz5 (by norm_num)) 51797 g51797 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 89 g89 (by norm_num)

-- a an odd multiple of 1138: 13 divides 5^2 + 1 and 37690561 + 1.
theorem c20_d1138 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1138 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, -, -, S8⟩ := facts hP (hK5 2) E
  have g37690561 : 37690561 ∈ P := S2 37690561 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 37690561) (x := 1 + 2 ^ 1138) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S8 13 (by norm_num) (by norm_num) (nz5 (by norm_num)) (by norm_num) 37690561 g37690561 (by norm_num)

-- a an odd multiple of 1142: 3^2 divides 276821 + 1.
theorem c20_d1142 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1142 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g5536417 : 5536417 ∈ P := S2 5536417 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 5536417) (x := 1 + 2 ^ 1142) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g2768209 : 2768209 ∈ P := S1 2768209 (by norm_num) (by norm_num) (nz5 (by norm_num)) 5536417 g5536417 (by norm_num)
  have g276821 : 276821 ∈ P := S1 276821 (by norm_num) (by norm_num) (nz5 (by norm_num)) 2768209 g2768209 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 276821 g276821 (by norm_num)

-- a an odd multiple of 1154: 7 divides 2309 + 1 and 13 + 1.
theorem c20_d1154 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1154 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, S3, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g2309 : 2309 ∈ P := S2 2309 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 2309) (x := 1 + 2 ^ 1154) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (nz5 (by norm_num)) (by norm_num)
  exact absurd (S3 7 (by norm_num) (by norm_num) (nz5 (by norm_num)) 2309 g2309 13 g13 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 1174: 3^2 divides 1601 + 1.
theorem c20_d1174 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1174 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g35221 : 35221 ∈ P := S2 35221 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 35221) (x := 1 + 2 ^ 1174) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g1601 : 1601 ∈ P := S1 1601 (by norm_num) (by norm_num) (nz5 (by norm_num)) 35221 g35221 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 1601 g1601 (by norm_num)

-- a an odd multiple of 1186: 3^2 divides 23360190343863455255753897 + 1.
theorem c20_d1186 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1186 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g23360190343863455255753897 : 23360190343863455255753897 ∈ P := S2 23360190343863455255753897 prime_23360190343863455255753897 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 23360190343863455255753897) (x := 1 + 2 ^ 1186) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 23360190343863455255753897 g23360190343863455255753897 (by norm_num)

-- a an odd multiple of 1198: 17 divides 4793 + 1 and 86257 + 1.
theorem c20_d1198 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1198 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, S3, -, -, -, -, -⟩ := facts hP (hK5 2) E
  have g4793 : 4793 ∈ P := S2 4793 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 4793) (x := 1 + 2 ^ 1198) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g86257 : 86257 ∈ P := S2 86257 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 86257) (x := 1 + 2 ^ 1198) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact absurd (S3 17 (by norm_num) (by norm_num) (nz5 (by norm_num)) 4793 g4793 86257 g86257 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 1202: 3^2 divides 17 + 1.
theorem c20_d1202 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1202 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g685141 : 685141 ∈ P := S2 685141 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 685141) (x := 1 + 2 ^ 1202) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g67 : 67 ∈ P := S1 67 (by norm_num) (by norm_num) (nz5 (by norm_num)) 685141 g685141 (by norm_num)
  have g17 : 17 ∈ P := S1 17 (by norm_num) (by norm_num) (nz5 (by norm_num)) 67 g67 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 17 g17 (by norm_num)

-- a an odd multiple of 1214: 13 divides 5^2 + 1 and 7889023609 + 1.
theorem c20_d1214 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1214 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, -, -, S8⟩ := facts hP (hK5 2) E
  have g7889023609 : 7889023609 ∈ P := S2 7889023609 prime_7889023609 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 7889023609) (x := 1 + 2 ^ 1214) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S8 13 (by norm_num) (by norm_num) (nz5 (by norm_num)) (by norm_num) 7889023609 g7889023609 (by norm_num)

-- a an odd multiple of 1226: 3 divides 17458241 + 1 and 23 + 1.
theorem c20_d1226 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1226 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, S3, -, -, -, -, -⟩ := facts hP (hK5 2) E
  have g17458241 : 17458241 ∈ P := S2 17458241 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 17458241) (x := 1 + 2 ^ 1226) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g23 : 23 ∈ P := S1 23 (by norm_num) (by norm_num) (nz5 (by norm_num)) 17458241 g17458241 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 17458241 g17458241 23 g23 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 1234: 3^2 divides 86381 + 1.
theorem c20_d1234 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1234 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g86381 : 86381 ∈ P := S2 86381 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 86381) (x := 1 + 2 ^ 1234) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 86381 g86381 (by norm_num)

-- a an odd multiple of 1238: 3^2 divides 284741 + 1.
theorem c20_d1238 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1238 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g284741 : 284741 ∈ P := S2 284741 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 284741) (x := 1 + 2 ^ 1238) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 284741 g284741 (by norm_num)

-- a an odd multiple of 1262: 3^2 divides 328121 + 1.
theorem c20_d1262 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1262 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g328121 : 328121 ∈ P := S2 328121 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 328121) (x := 1 + 2 ^ 1262) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 328121 g328121 (by norm_num)

-- a an odd multiple of 1282: 3 divides 62248793 + 1 and 1487 + 1.
theorem c20_d1282 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1282 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, S3, -, -, -, -, -⟩ := facts hP (hK5 2) E
  have g62248793 : 62248793 ∈ P := S2 62248793 prime_62248793 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 62248793) (x := 1 + 2 ^ 1282) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g1487 : 1487 ∈ P := S1 1487 (by norm_num) (by norm_num) (nz5 (by norm_num)) 62248793 g62248793 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 62248793 g62248793 1487 g1487 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 1286: 3^2 divides 53 + 1.
theorem c20_d1286 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1286 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g7981661881 : 7981661881 ∈ P := S2 7981661881 prime_7981661881 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 7981661881) (x := 1 + 2 ^ 1286) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g53 : 53 ∈ P := S1 53 (by norm_num) (by norm_num) (nz5 (by norm_num)) 7981661881 g7981661881 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 53 g53 (by norm_num)

-- a an odd multiple of 1294: 3^2 divides 9679121 + 1.
theorem c20_d1294 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1294 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g9679121 : 9679121 ∈ P := S2 9679121 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 9679121) (x := 1 + 2 ^ 1294) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 9679121 g9679121 (by norm_num)

-- a an odd multiple of 1306: 3^2 divides 233 + 1.
theorem c20_d1306 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1306 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g26214220912037007616369852597 : 26214220912037007616369852597 ∈ P := S2 26214220912037007616369852597 prime_26214220912037007616369852597 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 26214220912037007616369852597) (x := 1 + 2 ^ 1306) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g233 : 233 ∈ P := S1 233 (by norm_num) (by norm_num) (nz5 (by norm_num)) 26214220912037007616369852597 g26214220912037007616369852597 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 233 g233 (by norm_num)

-- a an odd multiple of 1318: 3^2 divides 5273 + 1.
theorem c20_d1318 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1318 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g5273 : 5273 ∈ P := S2 5273 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 5273) (x := 1 + 2 ^ 1318) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 5273 g5273 (by norm_num)

-- a an odd multiple of 1322: 13 divides 5^2 + 1 and 93405283373 + 1.
theorem c20_d1322 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1322 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, -, -, S8⟩ := facts hP (hK5 2) E
  have g93405283373 : 93405283373 ∈ P := S2 93405283373 prime_93405283373 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 93405283373) (x := 1 + 2 ^ 1322) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S8 13 (by norm_num) (by norm_num) (nz5 (by norm_num)) (by norm_num) 93405283373 g93405283373 (by norm_num)

-- a an odd multiple of 1346: 3 divides 2693 + 1 and 26921 + 1.
theorem c20_d1346 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1346 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, S3, -, -, -, -, -⟩ := facts hP (hK5 2) E
  have g2693 : 2693 ∈ P := S2 2693 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 2693) (x := 1 + 2 ^ 1346) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g26921 : 26921 ∈ P := S2 26921 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 26921) (x := 1 + 2 ^ 1346) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact absurd (S3 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 2693 g2693 26921 g26921 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 1354: 3^2 divides 5417 + 1.
theorem c20_d1354 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1354 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g5417 : 5417 ∈ P := S2 5417 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 5417) (x := 1 + 2 ^ 1354) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 5417 g5417 (by norm_num)

-- a an odd multiple of 1366: 3^2 divides 195140238443 + 1.
theorem c20_d1366 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1366 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g1951402384429 : 1951402384429 ∈ P := S2 1951402384429 prime_1951402384429 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 1951402384429) (x := 1 + 2 ^ 1366) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g195140238443 : 195140238443 ∈ P := S1 195140238443 prime_195140238443 (by norm_num) (nz5 (by norm_num)) 1951402384429 g1951402384429 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 195140238443 g195140238443 (by norm_num)

-- a an odd multiple of 1382: 7^2 divides 97 + 1.
theorem c20_d1382 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1382 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g11057 : 11057 ∈ P := S2 11057 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 11057) (x := 1 + 2 ^ 1382) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g97 : 97 ∈ P := S1 97 (by norm_num) (by norm_num) (nz5 (by norm_num)) 11057 g11057 (by norm_num)
  exact S6 7 (by norm_num) (by norm_num) (nz5 (by norm_num)) 97 g97 (by norm_num)

-- a an odd multiple of 1402: 3 divides 4846812462461 + 1 and 137 + 1.
theorem c20_d1402 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1402 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, S3, -, -, -, -, -⟩ := facts hP (hK5 2) E
  have g4846812462461 : 4846812462461 ∈ P := S2 4846812462461 prime_4846812462461 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 4846812462461) (x := 1 + 2 ^ 1402) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g1093 : 1093 ∈ P := S1 1093 (by norm_num) (by norm_num) (nz5 (by norm_num)) 4846812462461 g4846812462461 (by norm_num)
  have g547 : 547 ∈ P := S1 547 (by norm_num) (by norm_num) (nz5 (by norm_num)) 1093 g1093 (by norm_num)
  have g137 : 137 ∈ P := S1 137 (by norm_num) (by norm_num) (nz5 (by norm_num)) 547 g547 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 4846812462461 g4846812462461 137 g137 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 1418: 3 divides 2837 + 1 and 11 + 1.
theorem c20_d1418 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1418 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, S3, -, -, -, -, -⟩ := facts hP (hK5 2) E
  have g2837 : 2837 ∈ P := S2 2837 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 2837) (x := 1 + 2 ^ 1418) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (nz5 (by norm_num)) 2837 g2837 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 2837 g2837 11 g11 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 1438: 3^2 divides 863 + 1.
theorem c20_d1438 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1438 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g8629 : 8629 ∈ P := S2 8629 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 8629) (x := 1 + 2 ^ 1438) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g863 : 863 ∈ P := S1 863 (by norm_num) (by norm_num) (nz5 (by norm_num)) 8629 g8629 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 863 g863 (by norm_num)

-- a an odd multiple of 1454: 7^2 divides 97 + 1.
theorem c20_d1454 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1454 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g2909 : 2909 ∈ P := S2 2909 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 2909) (x := 1 + 2 ^ 1454) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g97 : 97 ∈ P := S1 97 (by norm_num) (by norm_num) (nz5 (by norm_num)) 2909 g2909 (by norm_num)
  exact S6 7 (by norm_num) (by norm_num) (nz5 (by norm_num)) 97 g97 (by norm_num)

-- a an odd multiple of 1466: 3 divides 627449 + 1 and 47 + 1.
theorem c20_d1466 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1466 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, S3, -, -, -, -, -⟩ := facts hP (hK5 2) E
  have g627449 : 627449 ∈ P := S2 627449 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 627449) (x := 1 + 2 ^ 1466) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g47 : 47 ∈ P := S1 47 (by norm_num) (by norm_num) (nz5 (by norm_num)) 627449 g627449 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 627449 g627449 47 g47 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 1478: 13 divides 5^2 + 1 and 6139613 + 1.
theorem c20_d1478 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1478 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, -, -, S8⟩ := facts hP (hK5 2) E
  have g6139613 : 6139613 ∈ P := S2 6139613 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 6139613) (x := 1 + 2 ^ 1478) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S8 13 (by norm_num) (by norm_num) (nz5 (by norm_num)) (by norm_num) 6139613 g6139613 (by norm_num)

-- a an odd multiple of 1486: 3^2 divides 260683037 + 1.
theorem c20_d1486 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1486 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g260683037 : 260683037 ∈ P := S2 260683037 prime_260683037 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 260683037) (x := 1 + 2 ^ 1486) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 260683037 g260683037 (by norm_num)

-- a an odd multiple of 1502: 7^2 divides 4507 + 1.
theorem c20_d1502 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1502 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g9013 : 9013 ∈ P := S2 9013 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 9013) (x := 1 + 2 ^ 1502) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g4507 : 4507 ∈ P := S1 4507 (by norm_num) (by norm_num) (nz5 (by norm_num)) 9013 g9013 (by norm_num)
  exact S6 7 (by norm_num) (by norm_num) (nz5 (by norm_num)) 4507 g4507 (by norm_num)

-- a an odd multiple of 1514: 3^2 divides 32507 + 1.
theorem c20_d1514 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1514 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g83940354459118810481 : 83940354459118810481 ∈ P := S2 83940354459118810481 prime_83940354459118810481 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 83940354459118810481) (x := 1 + 2 ^ 1514) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g32507 : 32507 ∈ P := S1 32507 (by norm_num) (by norm_num) (nz5 (by norm_num)) 83940354459118810481 g83940354459118810481 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 32507 g32507 (by norm_num)

-- a an odd multiple of 1522: 3 divides 1567661 + 1 and 227 + 1.
theorem c20_d1522 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1522 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, S3, -, -, -, -, -⟩ := facts hP (hK5 2) E
  have g1567661 : 1567661 ∈ P := S2 1567661 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 1567661) (x := 1 + 2 ^ 1522) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g227 : 227 ∈ P := S1 227 (by norm_num) (by norm_num) (nz5 (by norm_num)) 1567661 g1567661 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 1567661 g1567661 227 g227 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 1538: 3^2 divides 1508116661 + 1.
theorem c20_d1538 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1538 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g1508116661 : 1508116661 ∈ P := S2 1508116661 prime_1508116661 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 1508116661) (x := 1 + 2 ^ 1538) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 1508116661 g1508116661 (by norm_num)

-- a an odd multiple of 1546: 3^2 divides 961613 + 1.
theorem c20_d1546 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1546 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g961613 : 961613 ∈ P := S2 961613 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 961613) (x := 1 + 2 ^ 1546) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 961613 g961613 (by norm_num)

-- a an odd multiple of 1574: 13 divides 5^2 + 1 and 406093 + 1.
theorem c20_d1574 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1574 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, -, -, S8⟩ := facts hP (hK5 2) E
  have g406093 : 406093 ∈ P := S2 406093 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 406093) (x := 1 + 2 ^ 1574) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S8 13 (by norm_num) (by norm_num) (nz5 (by norm_num)) (by norm_num) 406093 g406093 (by norm_num)

-- a an odd multiple of 1594: 3^2 divides 1131019499249 + 1.
theorem c20_d1594 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1594 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g1131019499249 : 1131019499249 ∈ P := S2 1131019499249 prime_1131019499249 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 1131019499249) (x := 1 + 2 ^ 1594) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 1131019499249 g1131019499249 (by norm_num)

-- a an odd multiple of 1618: 13 divides 5^2 + 1 and 6473 + 1.
theorem c20_d1618 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1618 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, -, -, S8⟩ := facts hP (hK5 2) E
  have g6473 : 6473 ∈ P := S2 6473 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 6473) (x := 1 + 2 ^ 1618) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S8 13 (by norm_num) (by norm_num) (nz5 (by norm_num)) (by norm_num) 6473 g6473 (by norm_num)

-- a an odd multiple of 1622: 3 divides 5336381 + 1 and 2687 + 1.
theorem c20_d1622 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1622 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, S3, -, -, -, -, -⟩ := facts hP (hK5 2) E
  have g5336381 : 5336381 ∈ P := S2 5336381 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 5336381) (x := 1 + 2 ^ 1622) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g2687 : 2687 ∈ P := S1 2687 (by norm_num) (by norm_num) (nz5 (by norm_num)) 5336381 g5336381 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 5336381 g5336381 2687 g2687 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 1642: 3^2 divides 521 + 1.
theorem c20_d1642 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1642 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g441085379960554789 : 441085379960554789 ∈ P := S2 441085379960554789 prime_441085379960554789 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 441085379960554789) (x := 1 + 2 ^ 1642) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g521 : 521 ∈ P := S1 521 (by norm_num) (by norm_num) (nz5 (by norm_num)) 441085379960554789 g441085379960554789 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 521 g521 (by norm_num)

-- a an odd multiple of 1646: 7 divides 19753 + 1 and 13 + 1.
theorem c20_d1646 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1646 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, S3, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g19753 : 19753 ∈ P := S2 19753 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 19753) (x := 1 + 2 ^ 1646) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (nz5 (by norm_num)) (by norm_num)
  exact absurd (S3 7 (by norm_num) (by norm_num) (nz5 (by norm_num)) 19753 g19753 13 g13 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 1654: 7^2 divides 148861 + 1.
theorem c20_d1654 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1654 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g148861 : 148861 ∈ P := S2 148861 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 148861) (x := 1 + 2 ^ 1654) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 7 (by norm_num) (by norm_num) (nz5 (by norm_num)) 148861 g148861 (by norm_num)

-- a an odd multiple of 1658: 3^2 divides 32939 + 1.
theorem c20_d1658 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1658 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g464235512584146182617 : 464235512584146182617 ∈ P := S2 464235512584146182617 prime_464235512584146182617 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 464235512584146182617) (x := 1 + 2 ^ 1658) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g32939 : 32939 ∈ P := S1 32939 (by norm_num) (by norm_num) (nz5 (by norm_num)) 464235512584146182617 g464235512584146182617 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 32939 g32939 (by norm_num)

-- a an odd multiple of 1678: 3^2 divides 5564249 + 1.
theorem c20_d1678 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1678 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g5564249 : 5564249 ∈ P := S2 5564249 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 5564249) (x := 1 + 2 ^ 1678) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 5564249 g5564249 (by norm_num)

-- a an odd multiple of 1706: 3 divides 3413 + 1 and 569 + 1.
theorem c20_d1706 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1706 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, S3, -, -, -, -, -⟩ := facts hP (hK5 2) E
  have g3413 : 3413 ∈ P := S2 3413 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 3413) (x := 1 + 2 ^ 1706) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g569 : 569 ∈ P := S1 569 (by norm_num) (by norm_num) (nz5 (by norm_num)) 3413 g3413 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 3413 g3413 569 g569 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 1714: 3^2 divides 593 + 1.
theorem c20_d1714 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1714 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g4702664630197 : 4702664630197 ∈ P := S2 4702664630197 prime_4702664630197 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 4702664630197) (x := 1 + 2 ^ 1714) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g593 : 593 ∈ P := S1 593 (by norm_num) (by norm_num) (nz5 (by norm_num)) 4702664630197 g4702664630197 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 593 g593 (by norm_num)

-- a an odd multiple of 1718: 3^2 divides 53 + 1.
theorem c20_d1718 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1718 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g41233 : 41233 ∈ P := S2 41233 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 41233) (x := 1 + 2 ^ 1718) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g53 : 53 ∈ P := S1 53 (by norm_num) (by norm_num) (nz5 (by norm_num)) 41233 g41233 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 53 g53 (by norm_num)

-- a an odd multiple of 1726: 13 divides 5^2 + 1 and 31069 + 1.
theorem c20_d1726 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1726 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, -, -, S8⟩ := facts hP (hK5 2) E
  have g62137 : 62137 ∈ P := S2 62137 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 62137) (x := 1 + 2 ^ 1726) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g31069 : 31069 ∈ P := S1 31069 (by norm_num) (by norm_num) (nz5 (by norm_num)) 62137 g62137 (by norm_num)
  exact S8 13 (by norm_num) (by norm_num) (nz5 (by norm_num)) (by norm_num) 31069 g31069 (by norm_num)

-- a an odd multiple of 1754: 3^2 divides 17891 + 1.
theorem c20_d1754 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1754 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g178909 : 178909 ∈ P := S2 178909 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 178909) (x := 1 + 2 ^ 1754) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g17891 : 17891 ∈ P := S1 17891 (by norm_num) (by norm_num) (nz5 (by norm_num)) 178909 g178909 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 17891 g17891 (by norm_num)

-- a an odd multiple of 1762: 41^2 divides 292493 + 1.
theorem c20_d1762 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1762 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g292493 : 292493 ∈ P := S2 292493 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 292493) (x := 1 + 2 ^ 1762) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 41 (by norm_num) (by norm_num) (nz5 (by norm_num)) 292493 g292493 (by norm_num)

-- a an odd multiple of 1766: 7 divides 10597 + 1 and 13 + 1.
theorem c20_d1766 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1766 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, S3, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g10597 : 10597 ∈ P := S2 10597 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 10597) (x := 1 + 2 ^ 1766) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (nz5 (by norm_num)) (by norm_num)
  exact absurd (S3 7 (by norm_num) (by norm_num) (nz5 (by norm_num)) 10597 g10597 13 g13 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 1774: 7^2 divides 1982764321 + 1.
theorem c20_d1774 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1774 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g1982764321 : 1982764321 ∈ P := S2 1982764321 prime_1982764321 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 1982764321) (x := 1 + 2 ^ 1774) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 7 (by norm_num) (by norm_num) (nz5 (by norm_num)) 1982764321 g1982764321 (by norm_num)

-- a an odd multiple of 1814: 5^3 divides (2^1814 + 1) * prod (p + 1) over p in {36684968468392674349}.
theorem c20_d1814 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1814 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, -, -, -⟩ := facts hP (hK5 2) E
  have g36684968468392674349 : 36684968468392674349 ∈ P := S2 36684968468392674349 prime_36684968468392674349 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 36684968468392674349) (x := 1 + 2 ^ 1814) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have b0 : (∅ : Finset ℕ) ⊆ P ∧ 5 ^ 0 ∣ ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
    ⟨Finset.empty_subset _, by rw [pow_zero]; exact one_dvd _⟩
  have b1 := bud5_cons b0 g36684968468392674349 (by simp) (by norm_num : 5 ^ 2 ∣ 36684968468392674349 + 1)
  exact bud5_kill (i := 1) hP h5 E hd b1.1 (tw (c := 5) (x := 1 + 2 ^ 1814) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)) (by norm_num) b1.2

-- a an odd multiple of 1822: 3 divides 29153 + 1 and 113 + 1.
theorem c20_d1822 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1822 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, S3, -, -, -, -, -⟩ := facts hP (hK5 2) E
  have g29153 : 29153 ∈ P := S2 29153 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 29153) (x := 1 + 2 ^ 1822) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g113 : 113 ∈ P := S1 113 (by norm_num) (by norm_num) (nz5 (by norm_num)) 29153 g29153 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 29153 g29153 113 g113 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 1838: 3 divides 3677 + 1 and 169097 + 1.
theorem c20_d1838 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1838 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, S3, -, -, -, -, -⟩ := facts hP (hK5 2) E
  have g3677 : 3677 ∈ P := S2 3677 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 3677) (x := 1 + 2 ^ 1838) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g169097 : 169097 ∈ P := S2 169097 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 169097) (x := 1 + 2 ^ 1838) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact absurd (S3 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 3677 g3677 169097 g169097 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 1858: 3^2 divides 7433 + 1.
theorem c20_d1858 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1858 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g7433 : 7433 ∈ P := S2 7433 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 7433) (x := 1 + 2 ^ 1858) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 7433 g7433 (by norm_num)

-- a an odd multiple of 1874: 13^2 divides 802073 + 1.
theorem c20_d1874 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1874 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g802073 : 802073 ∈ P := S2 802073 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 802073) (x := 1 + 2 ^ 1874) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 13 (by norm_num) (by norm_num) (nz5 (by norm_num)) 802073 g802073 (by norm_num)

-- a an odd multiple of 1882: 3^2 divides 3383837 + 1.
theorem c20_d1882 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1882 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g3383837 : 3383837 ∈ P := S2 3383837 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 3383837) (x := 1 + 2 ^ 1882) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 3383837 g3383837 (by norm_num)

-- a an odd multiple of 1894: 3^2 divides 141803 + 1.
theorem c20_d1894 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1894 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g6522937 : 6522937 ∈ P := S2 6522937 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 6522937) (x := 1 + 2 ^ 1894) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g141803 : 141803 ∈ P := S1 141803 (by norm_num) (by norm_num) (nz5 (by norm_num)) 6522937 g6522937 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 141803 g141803 (by norm_num)

-- a an odd multiple of 1906: 83^2 divides 2809306768001 + 1.
theorem c20_d1906 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1906 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g2809306768001 : 2809306768001 ∈ P := S2 2809306768001 prime_2809306768001 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 2809306768001) (x := 1 + 2 ^ 1906) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 83 (by norm_num) (by norm_num) (nz5 (by norm_num)) 2809306768001 g2809306768001 (by norm_num)

-- a an odd multiple of 1934: 3 divides 328781 + 1 and 1481 + 1.
theorem c20_d1934 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1934 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, S3, -, -, -, -, -⟩ := facts hP (hK5 2) E
  have g328781 : 328781 ∈ P := S2 328781 (by norm_num) (by norm_num) (nz5 (by norm_num))
    ((tw (c := 328781) (x := 1 + 2 ^ 1934) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g1481 : 1481 ∈ P := S1 1481 (by norm_num) (by norm_num) (nz5 (by norm_num)) 328781 g328781 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 328781 g328781 1481 g1481 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 68719476736: 7 divides 2748779069441 + 1 and 13 + 1.
theorem c20_f36 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 68719476736 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, S3, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g2748779069441 : 2748779069441 ∈ P := S2 2748779069441 prime_2748779069441 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 2748779069441) (x := 1 + 2 ^ 68719476736) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (nz5 (by norm_num)) (by norm_num)
  exact absurd (S3 7 (by norm_num) (by norm_num) (nz5 (by norm_num)) 2748779069441 g2748779069441 13 g13 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 274877906944: 7 divides 6597069766657 + 1 and 13 + 1.
theorem c20_f38 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 274877906944 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, S3, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g6597069766657 : 6597069766657 ∈ P := S2 6597069766657 prime_6597069766657 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 6597069766657) (x := 1 + 2 ^ 274877906944) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (nz5 (by norm_num)) (by norm_num)
  exact absurd (S3 7 (by norm_num) (by norm_num) (nz5 (by norm_num)) 6597069766657 g6597069766657 13 g13 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 549755813888: 11 divides 46179488366593 + 1 and 263 + 1.
theorem c20_f39 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 549755813888 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, S3, -, -, -, -, -⟩ := facts hP (hK5 2) E
  have g46179488366593 : 46179488366593 ∈ P := S2 46179488366593 prime_46179488366593 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 46179488366593) (x := 1 + 2 ^ 549755813888) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g263 : 263 ∈ P := S1 263 (by norm_num) (by norm_num) (nz5 (by norm_num)) 46179488366593 g46179488366593 (by norm_num)
  exact absurd (S3 11 (by norm_num) (by norm_num) (nz5 (by norm_num)) 46179488366593 g46179488366593 263 g263 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 4398046511104: 3^2 divides 69545110012857251 + 1.
theorem c20_f42 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 4398046511104 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g1529992420282859521 : 1529992420282859521 ∈ P := S2 1529992420282859521 prime_1529992420282859521 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 1529992420282859521) (x := 1 + 2 ^ 4398046511104) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g69545110012857251 : 69545110012857251 ∈ P := S1 69545110012857251 prime_69545110012857251 (by norm_num) (nz5 (by norm_num)) 1529992420282859521 g1529992420282859521 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 69545110012857251 g69545110012857251 (by norm_num)

-- a an odd multiple of 4503599627370496: 13 divides 5^2 + 1 and 1567903 + 1.
theorem c20_f52 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 4503599627370496 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, -, -, S8⟩ := facts hP (hK5 2) E
  have g74201307460556292097 : 74201307460556292097 ∈ P := S2 74201307460556292097 prime_74201307460556292097 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 74201307460556292097) (x := 1 + 2 ^ 4503599627370496) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g1567903 : 1567903 ∈ P := S1 1567903 (by norm_num) (by norm_num) (nz5 (by norm_num)) 74201307460556292097 g74201307460556292097 (by norm_num)
  exact S8 13 (by norm_num) (by norm_num) (nz5 (by norm_num)) (by norm_num) 1567903 g1567903 (by norm_num)

-- a an odd multiple of 36028797018963968: 3^2 divides 4179340454199820289 + 1.
theorem c20_f55 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 36028797018963968 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g4179340454199820289 : 4179340454199820289 ∈ P := S2 4179340454199820289 prime_4179340454199820289 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 4179340454199820289) (x := 1 + 2 ^ 36028797018963968) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 4179340454199820289 g4179340454199820289 (by norm_num)

-- a an odd multiple of 288230376151711744: 3 divides 219055085875300925441 + 1 and 1667 + 1.
theorem c20_f58 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 288230376151711744 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, S3, -, -, -, -, -⟩ := facts hP (hK5 2) E
  have g219055085875300925441 : 219055085875300925441 ∈ P := S2 219055085875300925441 prime_219055085875300925441 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 219055085875300925441) (x := 1 + 2 ^ 288230376151711744) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g1667 : 1667 ∈ P := S1 1667 (by norm_num) (by norm_num) (nz5 (by norm_num)) 219055085875300925441 g219055085875300925441 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 219055085875300925441 g219055085875300925441 1667 g1667 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 4611686018427387904: 13 divides 5^2 + 1 and 12857380619375557476353 + 1.
theorem c20_f62 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 4611686018427387904 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, -, -, S8⟩ := facts hP (hK5 2) E
  have g12857380619375557476353 : 12857380619375557476353 ∈ P := S2 12857380619375557476353 prime_12857380619375557476353 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 12857380619375557476353) (x := 1 + 2 ^ 4611686018427387904) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S8 13 (by norm_num) (by norm_num) (nz5 (by norm_num)) (by norm_num) 12857380619375557476353 g12857380619375557476353 (by norm_num)

-- a an odd multiple of 9223372036854775808: 13 divides 5^2 + 1 and 9097024474706080249 + 1.
theorem c20_f63 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 9223372036854775808 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, -, -, S8⟩ := facts hP (hK5 2) E
  have g1328165573307087716353 : 1328165573307087716353 ∈ P := S2 1328165573307087716353 prime_1328165573307087716353 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 1328165573307087716353) (x := 1 + 2 ^ 9223372036854775808) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g9097024474706080249 : 9097024474706080249 ∈ P := S1 9097024474706080249 prime_9097024474706080249 (by norm_num) (nz5 (by norm_num)) 1328165573307087716353 g1328165573307087716353 (by norm_num)
  exact S8 13 (by norm_num) (by norm_num) (nz5 (by norm_num)) (by norm_num) 9097024474706080249 g9097024474706080249 (by norm_num)

-- a an odd multiple of 73786976294838206464: 7 divides 4457323664018586376077313 + 1 and 13 + 1.
theorem c20_f66 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 73786976294838206464 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, S3, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g4457323664018586376077313 : 4457323664018586376077313 ∈ P := S2 4457323664018586376077313 prime_4457323664018586376077313 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 4457323664018586376077313) (x := 1 + 2 ^ 73786976294838206464) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (nz5 (by norm_num)) (by norm_num)
  exact absurd (S3 7 (by norm_num) (by norm_num) (nz5 (by norm_num)) 4457323664018586376077313 g4457323664018586376077313 13 g13 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 2361183241434822606848: 3^2 divides 6450752615599935361908737 + 1.
theorem c20_f71 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 2361183241434822606848 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g6450752615599935361908737 : 6450752615599935361908737 ∈ P := S2 6450752615599935361908737 prime_6450752615599935361908737 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 6450752615599935361908737) (x := 1 + 2 ^ 2361183241434822606848) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 6450752615599935361908737 g6450752615599935361908737 (by norm_num)

-- a an odd multiple of 9444732965739290427392: 7^2 divides 188894659314785808547841 + 1.
theorem c20_f73 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 9444732965739290427392 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g188894659314785808547841 : 188894659314785808547841 ∈ P := S2 188894659314785808547841 prime_188894659314785808547841 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 188894659314785808547841) (x := 1 + 2 ^ 9444732965739290427392) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 7 (by norm_num) (by norm_num) (nz5 (by norm_num)) 188894659314785808547841 g188894659314785808547841 (by norm_num)

-- a an odd multiple of 151115727451828646838272: 11^2 divides 256896736668108699625062401 + 1.
theorem c20_f77 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 151115727451828646838272 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g256896736668108699625062401 : 256896736668108699625062401 ∈ P := S2 256896736668108699625062401 prime_256896736668108699625062401 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 256896736668108699625062401) (x := 1 + 2 ^ 151115727451828646838272) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 11 (by norm_num) (by norm_num) (nz5 (by norm_num)) 256896736668108699625062401 g256896736668108699625062401 (by norm_num)

-- a an odd multiple of 2417851639229258349412352: 13 divides 5^2 + 1 and 5241902353849032101525979137 + 1.
theorem c20_f81 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 2417851639229258349412352 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, -, -, S8⟩ := facts hP (hK5 2) E
  have g5241902353849032101525979137 : 5241902353849032101525979137 ∈ P := S2 5241902353849032101525979137 prime_5241902353849032101525979137 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 5241902353849032101525979137) (x := 1 + 2 ^ 2417851639229258349412352) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S8 13 (by norm_num) (by norm_num) (nz5 (by norm_num)) (by norm_num) 5241902353849032101525979137 g5241902353849032101525979137 (by norm_num)

-- a an odd multiple of 2475880078570760549798248448: 3 divides 14072902366596202965053244178433 + 1 and 690233 + 1.
theorem c20_f91 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 2475880078570760549798248448 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, S3, -, -, -, -, -⟩ := facts hP (hK5 2) E
  have g14072902366596202965053244178433 : 14072902366596202965053244178433 ∈ P := S2 14072902366596202965053244178433 prime_14072902366596202965053244178433 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 14072902366596202965053244178433) (x := 1 + 2 ^ 2475880078570760549798248448) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g690233 : 690233 ∈ P := S1 690233 (by norm_num) (by norm_num) (nz5 (by norm_num)) 14072902366596202965053244178433 g14072902366596202965053244178433 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 14072902366596202965053244178433 g14072902366596202965053244178433 690233 g690233 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 9903520314283042199192993792: 3 divides 7316007754729683197725441917976577 + 1 and 41 + 1.
theorem c20_f93 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 9903520314283042199192993792 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, S3, -, -, -, -, -⟩ := facts hP (hK5 2) E
  have g7316007754729683197725441917976577 : 7316007754729683197725441917976577 ∈ P := S2 7316007754729683197725441917976577 prime_7316007754729683197725441917976577 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 7316007754729683197725441917976577) (x := 1 + 2 ^ 9903520314283042199192993792) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g41 : 41 ∈ P := S1 41 (by norm_num) (by norm_num) (nz5 (by norm_num)) 7316007754729683197725441917976577 g7316007754729683197725441917976577 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 7316007754729683197725441917976577 g7316007754729683197725441917976577 41 g41 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 633825300114114700748351602688: 3^2 divides 17 + 1.
theorem c20_f99 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 633825300114114700748351602688 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g329244355096077565991935730125897729 : 329244355096077565991935730125897729 ∈ P := S2 329244355096077565991935730125897729 prime_329244355096077565991935730125897729 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 329244355096077565991935730125897729) (x := 1 + 2 ^ 633825300114114700748351602688) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g17 : 17 ∈ P := S1 17 (by norm_num) (by norm_num) (nz5 (by norm_num)) 329244355096077565991935730125897729 g329244355096077565991935730125897729 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 17 g17 (by norm_num)

-- a an odd multiple of 166153499473114484112975882535043072: 3^2 divides 9304595970494411110326649421962412033 + 1.
theorem c20_f117 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 166153499473114484112975882535043072 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g9304595970494411110326649421962412033 : 9304595970494411110326649421962412033 ∈ P := S2 9304595970494411110326649421962412033 prime_9304595970494411110326649421962412033 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 9304595970494411110326649421962412033) (x := 1 + 2 ^ 166153499473114484112975882535043072) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 9304595970494411110326649421962412033 g9304595970494411110326649421962412033 (by norm_num)

-- a an odd multiple of 42535295865117307932921825928971026432: 3 divides 850705917302346158658436518579420528641 + 1 and 23 + 1.
theorem c20_f125 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 42535295865117307932921825928971026432 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, S3, -, -, -, -, -⟩ := facts hP (hK5 2) E
  have g850705917302346158658436518579420528641 : 850705917302346158658436518579420528641 ∈ P := S2 850705917302346158658436518579420528641 prime_850705917302346158658436518579420528641 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 850705917302346158658436518579420528641) (x := 1 + 2 ^ 42535295865117307932921825928971026432) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g23 : 23 ∈ P := S1 23 (by norm_num) (by norm_num) (nz5 (by norm_num)) 850705917302346158658436518579420528641 g850705917302346158658436518579420528641 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 850705917302346158658436518579420528641 g850705917302346158658436518579420528641 23 g23 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 22300745198530623141535718272648361505980416: 3 divides 3032901347000164747248857685080177164813336577 + 1 and 11 + 1.
theorem c20_f144 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 22300745198530623141535718272648361505980416 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, S3, -, -, -, -, -⟩ := facts hP (hK5 2) E
  have g3032901347000164747248857685080177164813336577 : 3032901347000164747248857685080177164813336577 ∈ P := S2 3032901347000164747248857685080177164813336577 prime_3032901347000164747248857685080177164813336577 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 3032901347000164747248857685080177164813336577) (x := 1 + 2 ^ 22300745198530623141535718272648361505980416) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (nz5 (by norm_num)) 3032901347000164747248857685080177164813336577 g3032901347000164747248857685080177164813336577 (by norm_num)
  exact absurd (S3 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 3032901347000164747248857685080177164813336577 g3032901347000164747248857685080177164813336577 11 g11 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 178405961588244985132285746181186892047843328: 7 divides 2230074519853062314153571827264836150598041600001 + 1 and 13 + 1.
theorem c20_f147 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 178405961588244985132285746181186892047843328 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, S3, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g2230074519853062314153571827264836150598041600001 : 2230074519853062314153571827264836150598041600001 ∈ P := S2 2230074519853062314153571827264836150598041600001 prime_2230074519853062314153571827264836150598041600001 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 2230074519853062314153571827264836150598041600001) (x := 1 + 2 ^ 178405961588244985132285746181186892047843328) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (nz5 (by norm_num)) (by norm_num)
  exact absurd (S3 7 (by norm_num) (by norm_num) (nz5 (by norm_num)) 2230074519853062314153571827264836150598041600001 g2230074519853062314153571827264836150598041600001 13 g13 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 1427247692705959881058285969449495136382746624: 13 divides 5^2 + 1 and 124204803210043452689216278205372864748572142206977 + 1.
theorem c20_f150 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1427247692705959881058285969449495136382746624 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, -, -, S8⟩ := facts hP (hK5 2) E
  have g124204803210043452689216278205372864748572142206977 : 124204803210043452689216278205372864748572142206977 ∈ P := S2 124204803210043452689216278205372864748572142206977 prime_124204803210043452689216278205372864748572142206977 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 124204803210043452689216278205372864748572142206977) (x := 1 + 2 ^ 1427247692705959881058285969449495136382746624) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S8 13 (by norm_num) (by norm_num) (nz5 (by norm_num)) (by norm_num) 124204803210043452689216278205372864748572142206977 g124204803210043452689216278205372864748572142206977 (by norm_num)

-- a an odd multiple of 3213876088517980551083924184682325205044405987565585670602752: 3^2 divides 683 + 1.
theorem c20_f201 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 3213876088517980551083924184682325205044405987565585670602752 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g124569837190956926160012901398286924947521176078042100592562667521 : 124569837190956926160012901398286924947521176078042100592562667521 ∈ P := S2 124569837190956926160012901398286924947521176078042100592562667521 prime_124569837190956926160012901398286924947521176078042100592562667521 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 124569837190956926160012901398286924947521176078042100592562667521) (x := 1 + 2 ^ 3213876088517980551083924184682325205044405987565585670602752) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g683 : 683 ∈ P := S1 683 (by norm_num) (by norm_num) (nz5 (by norm_num)) 124569837190956926160012901398286924947521176078042100592562667521 g124569837190956926160012901398286924947521176078042100592562667521 (by norm_num)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 683 g683 (by norm_num)

-- a an odd multiple of 205688069665150755269371147819668813122841983204197482918576128: 7 divides 2468256835981809063232453773836025757474103798450369795022913537 + 1 and 13 + 1.
theorem c20_f207 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 205688069665150755269371147819668813122841983204197482918576128 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, S3, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g2468256835981809063232453773836025757474103798450369795022913537 : 2468256835981809063232453773836025757474103798450369795022913537 ∈ P := S2 2468256835981809063232453773836025757474103798450369795022913537 prime_2468256835981809063232453773836025757474103798450369795022913537 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 2468256835981809063232453773836025757474103798450369795022913537) (x := 1 + 2 ^ 205688069665150755269371147819668813122841983204197482918576128) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (nz5 (by norm_num)) (by norm_num)
  exact absurd (S3 7 (by norm_num) (by norm_num) (nz5 (by norm_num)) 2468256835981809063232453773836025757474103798450369795022913537 g2468256835981809063232453773836025757474103798450369795022913537 13 g13 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 52656145834278593348959013841835216159447547700274555627155488768: 3^2 divides 6763365995538079644113691573900682504384080816814065022974359599316993 + 1.
theorem c20_f215 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 52656145834278593348959013841835216159447547700274555627155488768 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g6763365995538079644113691573900682504384080816814065022974359599316993 : 6763365995538079644113691573900682504384080816814065022974359599316993 ∈ P := S2 6763365995538079644113691573900682504384080816814065022974359599316993 prime_6763365995538079644113691573900682504384080816814065022974359599316993 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 6763365995538079644113691573900682504384080816814065022974359599316993) (x := 1 + 2 ^ 52656145834278593348959013841835216159447547700274555627155488768) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 6763365995538079644113691573900682504384080816814065022974359599316993 g6763365995538079644113691573900682504384080816814065022974359599316993 (by norm_num)

-- a an odd multiple of 107839786668602559178668060348078522694548577690162289924414440996864: 7 divides 13 + 1 and 199346322480330839701 + 1.
theorem c20_f226 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 107839786668602559178668060348078522694548577690162289924414440996864 ∣ 2 ^ m + 1) : False := by
  obtain ⟨S1, S2, S3, -, -, -, S7, -⟩ := facts hP (hK5 2) E
  have g13 : 13 ∈ P := S7 13 (by norm_num) (by norm_num) (nz5 (by norm_num)) (by norm_num)
  have g12940774400232307101440167241769422723345829322819474790929732919623681 : 12940774400232307101440167241769422723345829322819474790929732919623681 ∈ P := S2 12940774400232307101440167241769422723345829322819474790929732919623681 prime_12940774400232307101440167241769422723345829322819474790929732919623681 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 12940774400232307101440167241769422723345829322819474790929732919623681) (x := 1 + 2 ^ 107839786668602559178668060348078522694548577690162289924414440996864) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  have g199346322480330839701 : 199346322480330839701 ∈ P := S1 199346322480330839701 prime_199346322480330839701 (by norm_num) (nz5 (by norm_num)) 12940774400232307101440167241769422723345829322819474790929732919623681 g12940774400232307101440167241769422723345829322819474790929732919623681 (by norm_num)
  exact absurd (S3 7 (by norm_num) (by norm_num) (nz5 (by norm_num)) 13 g13 199346322480330839701 g199346322480330839701 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 431359146674410236714672241392314090778194310760649159697657763987456: 3^2 divides 100075322028463174917803960003016869060541080096470605049856601245089793 + 1.
theorem c20_f228 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 431359146674410236714672241392314090778194310760649159697657763987456 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g100075322028463174917803960003016869060541080096470605049856601245089793 : 100075322028463174917803960003016869060541080096470605049856601245089793 ∈ P := S2 100075322028463174917803960003016869060541080096470605049856601245089793 prime_100075322028463174917803960003016869060541080096470605049856601245089793 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 100075322028463174917803960003016869060541080096470605049856601245089793) (x := 1 + 2 ^ 431359146674410236714672241392314090778194310760649159697657763987456) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 100075322028463174917803960003016869060541080096470605049856601245089793 g100075322028463174917803960003016869060541080096470605049856601245089793 (by norm_num)

-- a an odd multiple of 1809251394333065553493296640760748560207343510400633813116524750123642650624: 3^2 divides 2916513247664901672231194184906326679054237738765821706743837897199311952805889 + 1.
theorem c20_f250 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (_h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    (hd : 1 + 2 ^ 1809251394333065553493296640760748560207343510400633813116524750123642650624 ∣ 2 ^ m + 1) : False := by
  obtain ⟨-, S2, -, -, -, S6, -, -⟩ := facts hP (hK5 2) E
  have g2916513247664901672231194184906326679054237738765821706743837897199311952805889 : 2916513247664901672231194184906326679054237738765821706743837897199311952805889 ∈ P := S2 2916513247664901672231194184906326679054237738765821706743837897199311952805889 prime_2916513247664901672231194184906326679054237738765821706743837897199311952805889 (by norm_num) (nz5 (by norm_num))
    ((tw (c := 2916513247664901672231194184906326679054237738765821706743837897199311952805889) (x := 1 + 2 ^ 1809251394333065553493296640760748560207343510400633813116524750123642650624) (by rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]; reduce_mod_char)).trans hd)
  exact S6 3 (by norm_num) (by norm_num) (nz5 (by norm_num)) 2916513247664901672231194184906326679054237738765821706743837897199311952805889 g2916513247664901672231194184906326679054237738765821706743837897199311952805889 (by norm_num)

theorem odd_sieve_0 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    {d : ℕ} (hd : d.Prime) (h3 : d % 3 = 1) (hD : 1 + 2 ^ d ∣ 2 ^ m + 1)
    (lo : 43 ≤ d) (hi : d ≤ 192) : False := by
  interval_cases d
  · exact c20_d43 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d61 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d67 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d73 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d79 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d97 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d103 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d109 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d127 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d139 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d151 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d157 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d163 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d181 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega

theorem odd_sieve_1 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    {d : ℕ} (hd : d.Prime) (h3 : d % 3 = 1) (hD : 1 + 2 ^ d ∣ 2 ^ m + 1)
    (lo : 193 ≤ d) (hi : d ≤ 342) : False := by
  interval_cases d
  · exact c20_d193 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d199 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d211 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d223 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d229 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d241 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d271 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d277 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d283 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d307 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d313 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d331 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d337 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega

theorem odd_sieve_2 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    {d : ℕ} (hd : d.Prime) (h3 : d % 3 = 1) (hD : 1 + 2 ^ d ∣ 2 ^ m + 1)
    (lo : 343 ≤ d) (hi : d ≤ 492) : False := by
  interval_cases d
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d349 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d367 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d373 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d379 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d397 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d409 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d421 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d433 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d439 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d457 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d463 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d487 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega

theorem odd_sieve_3 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    {d : ℕ} (hd : d.Prime) (h3 : d % 3 = 1) (hD : 1 + 2 ^ d ∣ 2 ^ m + 1)
    (lo : 493 ≤ d) (hi : d ≤ 642) : False := by
  interval_cases d
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d499 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d523 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d541 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d547 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d571 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d577 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d601 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d607 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d613 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d619 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d631 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega

theorem odd_sieve_4 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    {d : ℕ} (hd : d.Prime) (h3 : d % 3 = 1) (hD : 1 + 2 ^ d ∣ 2 ^ m + 1)
    (lo : 643 ≤ d) (hi : d ≤ 792) : False := by
  interval_cases d
  · exact c20_d643 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d661 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d673 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d691 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d709 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d727 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d733 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d739 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d751 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d757 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d769 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d787 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega

theorem odd_sieve_5 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    {d : ℕ} (hd : d.Prime) (h3 : d % 3 = 1) (hD : 1 + 2 ^ d ∣ 2 ^ m + 1)
    (lo : 793 ≤ d) (hi : d ≤ 942) : False := by
  interval_cases d
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d811 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d823 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d829 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d853 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d859 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d877 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d883 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d907 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d919 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d937 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega

theorem odd_sieve_6 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    {d : ℕ} (hd : d.Prime) (h3 : d % 3 = 1) (hD : 1 + 2 ^ d ∣ 2 ^ m + 1)
    (lo : 943 ≤ d) (hi : d ≤ 1092) : False := by
  interval_cases d
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d967 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d991 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d997 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d1009 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d1021 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d1033 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d1039 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d1051 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d1063 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d1069 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d1087 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega

theorem odd_sieve_7 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    {d : ℕ} (hd : d.Prime) (h3 : d % 3 = 1) (hD : 1 + 2 ^ d ∣ 2 ^ m + 1)
    (lo : 1093 ≤ d) (hi : d ≤ 1242) : False := by
  interval_cases d
  · exact c20_d1093 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d1117 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d1123 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d1129 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d1153 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d1171 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d1201 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d1213 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d1231 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d1237 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega

theorem odd_sieve_8 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    {d : ℕ} (hd : d.Prime) (h3 : d % 3 = 1) (hD : 1 + 2 ^ d ∣ 2 ^ m + 1)
    (lo : 1243 ≤ d) (hi : d ≤ 1392) : False := by
  interval_cases d
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d1249 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d1279 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d1291 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d1297 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d1303 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d1321 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d1327 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d1381 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega

theorem odd_sieve_9 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    {d : ℕ} (hd : d.Prime) (h3 : d % 3 = 1) (hD : 1 + 2 ^ d ∣ 2 ^ m + 1)
    (lo : 1393 ≤ d) (hi : d ≤ 1542) : False := by
  interval_cases d
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d1399 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d1423 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d1429 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d1447 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d1453 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d1459 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d1471 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d1483 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d1489 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d1531 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega

theorem odd_sieve_10 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    {d : ℕ} (hd : d.Prime) (h3 : d % 3 = 1) (hD : 1 + 2 ^ d ∣ 2 ^ m + 1)
    (lo : 1543 ≤ d) (hi : d ≤ 1692) : False := by
  interval_cases d
  · exact c20_d1543 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d1549 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d1567 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d1579 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d1597 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d1609 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d1621 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d1627 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d1657 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d1663 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d1669 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega

theorem odd_sieve_11 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    {d : ℕ} (hd : d.Prime) (h3 : d % 3 = 1) (hD : 1 + 2 ^ d ∣ 2 ^ m + 1)
    (lo : 1693 ≤ d) (hi : d ≤ 1776) : False := by
  interval_cases d
  · exact c20_d1693 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d1699 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d1723 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d1741 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d1747 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d1753 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact c20_d1759 hP h5 E hD
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega
  · exact absurd hd (by norm_num)
  · omega
  · omega

-- a odd, d a prime factor of a with d = 1 mod 3 and 43 <= d <= 1776: impossible.
theorem odd_sieve {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    {d : ℕ} (hd : d.Prime) (h3 : d % 3 = 1) (hD : 1 + 2 ^ d ∣ 2 ^ m + 1)
    (lo : 43 ≤ d) (hi : d ≤ 1776) : False := by
  rcases Nat.lt_or_ge d 193 with k0 | k0
  · exact odd_sieve_0 hP h5 E hd h3 hD (by omega) (by omega)
  rcases Nat.lt_or_ge d 343 with k1 | k1
  · exact odd_sieve_1 hP h5 E hd h3 hD (by omega) (by omega)
  rcases Nat.lt_or_ge d 493 with k2 | k2
  · exact odd_sieve_2 hP h5 E hd h3 hD (by omega) (by omega)
  rcases Nat.lt_or_ge d 643 with k3 | k3
  · exact odd_sieve_3 hP h5 E hd h3 hD (by omega) (by omega)
  rcases Nat.lt_or_ge d 793 with k4 | k4
  · exact odd_sieve_4 hP h5 E hd h3 hD (by omega) (by omega)
  rcases Nat.lt_or_ge d 943 with k5 | k5
  · exact odd_sieve_5 hP h5 E hd h3 hD (by omega) (by omega)
  rcases Nat.lt_or_ge d 1093 with k6 | k6
  · exact odd_sieve_6 hP h5 E hd h3 hD (by omega) (by omega)
  rcases Nat.lt_or_ge d 1243 with k7 | k7
  · exact odd_sieve_7 hP h5 E hd h3 hD (by omega) (by omega)
  rcases Nat.lt_or_ge d 1393 with k8 | k8
  · exact odd_sieve_8 hP h5 E hd h3 hD (by omega) (by omega)
  rcases Nat.lt_or_ge d 1543 with k9 | k9
  · exact odd_sieve_9 hP h5 E hd h3 hD (by omega) (by omega)
  rcases Nat.lt_or_ge d 1693 with k10 | k10
  · exact odd_sieve_10 hP h5 E hd h3 hD (by omega) (by omega)
  exact odd_sieve_11 hP h5 E hd h3 hD (by omega) (by omega)

theorem even_sieve_0 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    {d : ℕ} (hd : d.Prime) (hD : 1 + 2 ^ (2 * d) ∣ 2 ^ m + 1)
    (lo : 101 ≤ d) (hi : d ≤ 250) : False := by
  interval_cases d
  · exact c20_d202 hP h5 E (by rw [show 2 * 101 = 202 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact c20_d206 hP h5 E (by rw [show 2 * 103 = 206 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d214 hP h5 E (by rw [show 2 * 107 = 214 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact c20_d218 hP h5 E (by rw [show 2 * 109 = 218 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d226 hP h5 E (by rw [show 2 * 113 = 226 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d254 hP h5 E (by rw [show 2 * 127 = 254 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d262 hP h5 E (by rw [show 2 * 131 = 262 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d274 hP h5 E (by rw [show 2 * 137 = 274 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact c20_d278 hP h5 E (by rw [show 2 * 139 = 278 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d298 hP h5 E (by rw [show 2 * 149 = 298 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact c20_d302 hP h5 E (by rw [show 2 * 151 = 302 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d314 hP h5 E (by rw [show 2 * 157 = 314 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d326 hP h5 E (by rw [show 2 * 163 = 326 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d334 hP h5 E (by rw [show 2 * 167 = 334 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d346 hP h5 E (by rw [show 2 * 173 = 346 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d358 hP h5 E (by rw [show 2 * 179 = 358 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact c20_d362 hP h5 E (by rw [show 2 * 181 = 362 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d382 hP h5 E (by rw [show 2 * 191 = 382 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact c20_d386 hP h5 E (by rw [show 2 * 193 = 386 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d394 hP h5 E (by rw [show 2 * 197 = 394 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact c20_d398 hP h5 E (by rw [show 2 * 199 = 398 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d422 hP h5 E (by rw [show 2 * 211 = 422 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d446 hP h5 E (by rw [show 2 * 223 = 446 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d454 hP h5 E (by rw [show 2 * 227 = 454 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact c20_d458 hP h5 E (by rw [show 2 * 229 = 458 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d466 hP h5 E (by rw [show 2 * 233 = 466 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d478 hP h5 E (by rw [show 2 * 239 = 478 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact c20_d482 hP h5 E (by rw [show 2 * 241 = 482 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)

theorem even_sieve_1 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    {d : ℕ} (hd : d.Prime) (hD : 1 + 2 ^ (2 * d) ∣ 2 ^ m + 1)
    (lo : 251 ≤ d) (hi : d ≤ 400) : False := by
  interval_cases d
  · exact c20_d502 hP h5 E (by rw [show 2 * 251 = 502 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d514 hP h5 E (by rw [show 2 * 257 = 514 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d526 hP h5 E (by rw [show 2 * 263 = 526 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d538 hP h5 E (by rw [show 2 * 269 = 538 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact c20_d542 hP h5 E (by rw [show 2 * 271 = 542 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d554 hP h5 E (by rw [show 2 * 277 = 554 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d562 hP h5 E (by rw [show 2 * 281 = 562 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact c20_d566 hP h5 E (by rw [show 2 * 283 = 566 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d586 hP h5 E (by rw [show 2 * 293 = 586 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d614 hP h5 E (by rw [show 2 * 307 = 614 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d622 hP h5 E (by rw [show 2 * 311 = 622 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact c20_d626 hP h5 E (by rw [show 2 * 313 = 626 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d634 hP h5 E (by rw [show 2 * 317 = 634 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d662 hP h5 E (by rw [show 2 * 331 = 662 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d674 hP h5 E (by rw [show 2 * 337 = 674 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d694 hP h5 E (by rw [show 2 * 347 = 694 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact c20_d698 hP h5 E (by rw [show 2 * 349 = 698 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d706 hP h5 E (by rw [show 2 * 353 = 706 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d718 hP h5 E (by rw [show 2 * 359 = 718 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d734 hP h5 E (by rw [show 2 * 367 = 734 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d746 hP h5 E (by rw [show 2 * 373 = 746 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d758 hP h5 E (by rw [show 2 * 379 = 758 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d766 hP h5 E (by rw [show 2 * 383 = 766 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d778 hP h5 E (by rw [show 2 * 389 = 778 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d794 hP h5 E (by rw [show 2 * 397 = 794 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)

theorem even_sieve_2 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    {d : ℕ} (hd : d.Prime) (hD : 1 + 2 ^ (2 * d) ∣ 2 ^ m + 1)
    (lo : 401 ≤ d) (hi : d ≤ 550) : False := by
  interval_cases d
  · exact c20_d802 hP h5 E (by rw [show 2 * 401 = 802 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d818 hP h5 E (by rw [show 2 * 409 = 818 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d838 hP h5 E (by rw [show 2 * 419 = 838 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact c20_d842 hP h5 E (by rw [show 2 * 421 = 842 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d862 hP h5 E (by rw [show 2 * 431 = 862 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact c20_d866 hP h5 E (by rw [show 2 * 433 = 866 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d878 hP h5 E (by rw [show 2 * 439 = 878 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d886 hP h5 E (by rw [show 2 * 443 = 886 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d898 hP h5 E (by rw [show 2 * 449 = 898 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d914 hP h5 E (by rw [show 2 * 457 = 914 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d922 hP h5 E (by rw [show 2 * 461 = 922 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact c20_d926 hP h5 E (by rw [show 2 * 463 = 926 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d934 hP h5 E (by rw [show 2 * 467 = 934 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d958 hP h5 E (by rw [show 2 * 479 = 958 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d974 hP h5 E (by rw [show 2 * 487 = 974 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d982 hP h5 E (by rw [show 2 * 491 = 982 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d998 hP h5 E (by rw [show 2 * 499 = 998 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1006 hP h5 E (by rw [show 2 * 503 = 1006 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1018 hP h5 E (by rw [show 2 * 509 = 1018 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1042 hP h5 E (by rw [show 2 * 521 = 1042 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact c20_d1046 hP h5 E (by rw [show 2 * 523 = 1046 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1082 hP h5 E (by rw [show 2 * 541 = 1082 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1094 hP h5 E (by rw [show 2 * 547 = 1094 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)

theorem even_sieve_3 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    {d : ℕ} (hd : d.Prime) (hD : 1 + 2 ^ (2 * d) ∣ 2 ^ m + 1)
    (lo : 551 ≤ d) (hi : d ≤ 700) : False := by
  interval_cases d
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1114 hP h5 E (by rw [show 2 * 557 = 1114 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1126 hP h5 E (by rw [show 2 * 563 = 1126 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1138 hP h5 E (by rw [show 2 * 569 = 1138 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact c20_d1142 hP h5 E (by rw [show 2 * 571 = 1142 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1154 hP h5 E (by rw [show 2 * 577 = 1154 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1174 hP h5 E (by rw [show 2 * 587 = 1174 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1186 hP h5 E (by rw [show 2 * 593 = 1186 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1198 hP h5 E (by rw [show 2 * 599 = 1198 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact c20_d1202 hP h5 E (by rw [show 2 * 601 = 1202 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1214 hP h5 E (by rw [show 2 * 607 = 1214 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1226 hP h5 E (by rw [show 2 * 613 = 1226 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1234 hP h5 E (by rw [show 2 * 617 = 1234 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact c20_d1238 hP h5 E (by rw [show 2 * 619 = 1238 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1262 hP h5 E (by rw [show 2 * 631 = 1262 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1282 hP h5 E (by rw [show 2 * 641 = 1282 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact c20_d1286 hP h5 E (by rw [show 2 * 643 = 1286 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1294 hP h5 E (by rw [show 2 * 647 = 1294 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1306 hP h5 E (by rw [show 2 * 653 = 1306 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1318 hP h5 E (by rw [show 2 * 659 = 1318 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact c20_d1322 hP h5 E (by rw [show 2 * 661 = 1322 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1346 hP h5 E (by rw [show 2 * 673 = 1346 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1354 hP h5 E (by rw [show 2 * 677 = 1354 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1366 hP h5 E (by rw [show 2 * 683 = 1366 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1382 hP h5 E (by rw [show 2 * 691 = 1382 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)

theorem even_sieve_4 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    {d : ℕ} (hd : d.Prime) (hD : 1 + 2 ^ (2 * d) ∣ 2 ^ m + 1)
    (lo : 701 ≤ d) (hi : d ≤ 850) : False := by
  interval_cases d
  · exact c20_d1402 hP h5 E (by rw [show 2 * 701 = 1402 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1418 hP h5 E (by rw [show 2 * 709 = 1418 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1438 hP h5 E (by rw [show 2 * 719 = 1438 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1454 hP h5 E (by rw [show 2 * 727 = 1454 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1466 hP h5 E (by rw [show 2 * 733 = 1466 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1478 hP h5 E (by rw [show 2 * 739 = 1478 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1486 hP h5 E (by rw [show 2 * 743 = 1486 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1502 hP h5 E (by rw [show 2 * 751 = 1502 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1514 hP h5 E (by rw [show 2 * 757 = 1514 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1522 hP h5 E (by rw [show 2 * 761 = 1522 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1538 hP h5 E (by rw [show 2 * 769 = 1538 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1546 hP h5 E (by rw [show 2 * 773 = 1546 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1574 hP h5 E (by rw [show 2 * 787 = 1574 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1594 hP h5 E (by rw [show 2 * 797 = 1594 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1618 hP h5 E (by rw [show 2 * 809 = 1618 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact c20_d1622 hP h5 E (by rw [show 2 * 811 = 1622 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1642 hP h5 E (by rw [show 2 * 821 = 1642 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact c20_d1646 hP h5 E (by rw [show 2 * 823 = 1646 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1654 hP h5 E (by rw [show 2 * 827 = 1654 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact c20_d1658 hP h5 E (by rw [show 2 * 829 = 1658 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1678 hP h5 E (by rw [show 2 * 839 = 1678 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)

theorem even_sieve_5 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    {d : ℕ} (hd : d.Prime) (hD : 1 + 2 ^ (2 * d) ∣ 2 ^ m + 1)
    (lo : 851 ≤ d) (hi : d ≤ 970) : False := by
  interval_cases d
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1706 hP h5 E (by rw [show 2 * 853 = 1706 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1714 hP h5 E (by rw [show 2 * 857 = 1714 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact c20_d1718 hP h5 E (by rw [show 2 * 859 = 1718 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1726 hP h5 E (by rw [show 2 * 863 = 1726 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1754 hP h5 E (by rw [show 2 * 877 = 1754 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1762 hP h5 E (by rw [show 2 * 881 = 1762 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact c20_d1766 hP h5 E (by rw [show 2 * 883 = 1766 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1774 hP h5 E (by rw [show 2 * 887 = 1774 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1814 hP h5 E (by rw [show 2 * 907 = 1814 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1822 hP h5 E (by rw [show 2 * 911 = 1822 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1838 hP h5 E (by rw [show 2 * 919 = 1838 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1858 hP h5 E (by rw [show 2 * 929 = 1858 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1874 hP h5 E (by rw [show 2 * 937 = 1874 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1882 hP h5 E (by rw [show 2 * 941 = 1882 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1894 hP h5 E (by rw [show 2 * 947 = 1894 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1906 hP h5 E (by rw [show 2 * 953 = 1906 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact c20_d1934 hP h5 E (by rw [show 2 * 967 = 1934 from rfl] at hD; exact hD)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)
  · exact absurd hd (by norm_num)

-- a = 2 mod 4, d an odd prime factor of a with 101 <= d <= 970: impossible.
theorem even_sieve {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p)
    {d : ℕ} (hd : d.Prime) (hD : 1 + 2 ^ (2 * d) ∣ 2 ^ m + 1)
    (lo : 101 ≤ d) (hi : d ≤ 970) : False := by
  rcases Nat.lt_or_ge d 251 with k0 | k0
  · exact even_sieve_0 hP h5 E hd hD (by omega) (by omega)
  rcases Nat.lt_or_ge d 401 with k1 | k1
  · exact even_sieve_1 hP h5 E hd hD (by omega) (by omega)
  rcases Nat.lt_or_ge d 551 with k2 | k2
  · exact even_sieve_2 hP h5 E hd hD (by omega) (by omega)
  rcases Nat.lt_or_ge d 701 with k3 | k3
  · exact even_sieve_3 hP h5 E hd hD (by omega) (by omega)
  rcases Nat.lt_or_ge d 851 with k4 | k4
  · exact even_sieve_4 hP h5 E hd hD (by omega) (by omega)
  exact even_sieve_5 hP h5 E hd hD (by omega) (by omega)

-- 4 | a: v2(a) is not r for r in {36, 38, 39, 42, 52, 55, 58, 62, 63, 66, 71, 73, 77, 81, 91, 93, 99, 117, 125, 144, 147, 150, 201, 207, 215, 226, 228, 250} (known prime factors of Fermat numbers).
theorem fermat20 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h5 : 5 ∉ P)
    (E : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p) :
    ∀ r ∈ ({36, 38, 39, 42, 52, 55, 58, 62, 63, 66, 71, 73, 77, 81, 91, 93, 99, 117, 125, 144, 147, 150, 201, 207, 215, 226, 228, 250} : Finset ℕ), m % 2 ^ (r + 1) ≠ 2 ^ r := by
  intro r hr h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have h2 : m % (2 * 2 ^ 36) = 2 ^ 36 := by rw [← pow_succ']; exact h
    have h3 := one_add_pow_dvd_of_odd_mul (z := 2) h2
    rw [add_comm 1 (2 ^ m), show (2 : ℕ) ^ 36 = 68719476736 from by norm_num] at h3
    exact c20_f36 hP h5 E h3
  · have h2 : m % (2 * 2 ^ 38) = 2 ^ 38 := by rw [← pow_succ']; exact h
    have h3 := one_add_pow_dvd_of_odd_mul (z := 2) h2
    rw [add_comm 1 (2 ^ m), show (2 : ℕ) ^ 38 = 274877906944 from by norm_num] at h3
    exact c20_f38 hP h5 E h3
  · have h2 : m % (2 * 2 ^ 39) = 2 ^ 39 := by rw [← pow_succ']; exact h
    have h3 := one_add_pow_dvd_of_odd_mul (z := 2) h2
    rw [add_comm 1 (2 ^ m), show (2 : ℕ) ^ 39 = 549755813888 from by norm_num] at h3
    exact c20_f39 hP h5 E h3
  · have h2 : m % (2 * 2 ^ 42) = 2 ^ 42 := by rw [← pow_succ']; exact h
    have h3 := one_add_pow_dvd_of_odd_mul (z := 2) h2
    rw [add_comm 1 (2 ^ m), show (2 : ℕ) ^ 42 = 4398046511104 from by norm_num] at h3
    exact c20_f42 hP h5 E h3
  · have h2 : m % (2 * 2 ^ 52) = 2 ^ 52 := by rw [← pow_succ']; exact h
    have h3 := one_add_pow_dvd_of_odd_mul (z := 2) h2
    rw [add_comm 1 (2 ^ m), show (2 : ℕ) ^ 52 = 4503599627370496 from by norm_num] at h3
    exact c20_f52 hP h5 E h3
  · have h2 : m % (2 * 2 ^ 55) = 2 ^ 55 := by rw [← pow_succ']; exact h
    have h3 := one_add_pow_dvd_of_odd_mul (z := 2) h2
    rw [add_comm 1 (2 ^ m), show (2 : ℕ) ^ 55 = 36028797018963968 from by norm_num] at h3
    exact c20_f55 hP h5 E h3
  · have h2 : m % (2 * 2 ^ 58) = 2 ^ 58 := by rw [← pow_succ']; exact h
    have h3 := one_add_pow_dvd_of_odd_mul (z := 2) h2
    rw [add_comm 1 (2 ^ m), show (2 : ℕ) ^ 58 = 288230376151711744 from by norm_num] at h3
    exact c20_f58 hP h5 E h3
  · have h2 : m % (2 * 2 ^ 62) = 2 ^ 62 := by rw [← pow_succ']; exact h
    have h3 := one_add_pow_dvd_of_odd_mul (z := 2) h2
    rw [add_comm 1 (2 ^ m), show (2 : ℕ) ^ 62 = 4611686018427387904 from by norm_num] at h3
    exact c20_f62 hP h5 E h3
  · have h2 : m % (2 * 2 ^ 63) = 2 ^ 63 := by rw [← pow_succ']; exact h
    have h3 := one_add_pow_dvd_of_odd_mul (z := 2) h2
    rw [add_comm 1 (2 ^ m), show (2 : ℕ) ^ 63 = 9223372036854775808 from by norm_num] at h3
    exact c20_f63 hP h5 E h3
  · have h2 : m % (2 * 2 ^ 66) = 2 ^ 66 := by rw [← pow_succ']; exact h
    have h3 := one_add_pow_dvd_of_odd_mul (z := 2) h2
    rw [add_comm 1 (2 ^ m), show (2 : ℕ) ^ 66 = 73786976294838206464 from by norm_num] at h3
    exact c20_f66 hP h5 E h3
  · have h2 : m % (2 * 2 ^ 71) = 2 ^ 71 := by rw [← pow_succ']; exact h
    have h3 := one_add_pow_dvd_of_odd_mul (z := 2) h2
    rw [add_comm 1 (2 ^ m), show (2 : ℕ) ^ 71 = 2361183241434822606848 from by norm_num] at h3
    exact c20_f71 hP h5 E h3
  · have h2 : m % (2 * 2 ^ 73) = 2 ^ 73 := by rw [← pow_succ']; exact h
    have h3 := one_add_pow_dvd_of_odd_mul (z := 2) h2
    rw [add_comm 1 (2 ^ m), show (2 : ℕ) ^ 73 = 9444732965739290427392 from by norm_num] at h3
    exact c20_f73 hP h5 E h3
  · have h2 : m % (2 * 2 ^ 77) = 2 ^ 77 := by rw [← pow_succ']; exact h
    have h3 := one_add_pow_dvd_of_odd_mul (z := 2) h2
    rw [add_comm 1 (2 ^ m), show (2 : ℕ) ^ 77 = 151115727451828646838272 from by norm_num] at h3
    exact c20_f77 hP h5 E h3
  · have h2 : m % (2 * 2 ^ 81) = 2 ^ 81 := by rw [← pow_succ']; exact h
    have h3 := one_add_pow_dvd_of_odd_mul (z := 2) h2
    rw [add_comm 1 (2 ^ m), show (2 : ℕ) ^ 81 = 2417851639229258349412352 from by norm_num] at h3
    exact c20_f81 hP h5 E h3
  · have h2 : m % (2 * 2 ^ 91) = 2 ^ 91 := by rw [← pow_succ']; exact h
    have h3 := one_add_pow_dvd_of_odd_mul (z := 2) h2
    rw [add_comm 1 (2 ^ m), show (2 : ℕ) ^ 91 = 2475880078570760549798248448 from by norm_num] at h3
    exact c20_f91 hP h5 E h3
  · have h2 : m % (2 * 2 ^ 93) = 2 ^ 93 := by rw [← pow_succ']; exact h
    have h3 := one_add_pow_dvd_of_odd_mul (z := 2) h2
    rw [add_comm 1 (2 ^ m), show (2 : ℕ) ^ 93 = 9903520314283042199192993792 from by norm_num] at h3
    exact c20_f93 hP h5 E h3
  · have h2 : m % (2 * 2 ^ 99) = 2 ^ 99 := by rw [← pow_succ']; exact h
    have h3 := one_add_pow_dvd_of_odd_mul (z := 2) h2
    rw [add_comm 1 (2 ^ m), show (2 : ℕ) ^ 99 = 633825300114114700748351602688 from by norm_num] at h3
    exact c20_f99 hP h5 E h3
  · have h2 : m % (2 * 2 ^ 117) = 2 ^ 117 := by rw [← pow_succ']; exact h
    have h3 := one_add_pow_dvd_of_odd_mul (z := 2) h2
    rw [add_comm 1 (2 ^ m), show (2 : ℕ) ^ 117 = 166153499473114484112975882535043072 from by norm_num] at h3
    exact c20_f117 hP h5 E h3
  · have h2 : m % (2 * 2 ^ 125) = 2 ^ 125 := by rw [← pow_succ']; exact h
    have h3 := one_add_pow_dvd_of_odd_mul (z := 2) h2
    rw [add_comm 1 (2 ^ m), show (2 : ℕ) ^ 125 = 42535295865117307932921825928971026432 from by norm_num] at h3
    exact c20_f125 hP h5 E h3
  · have h2 : m % (2 * 2 ^ 144) = 2 ^ 144 := by rw [← pow_succ']; exact h
    have h3 := one_add_pow_dvd_of_odd_mul (z := 2) h2
    rw [add_comm 1 (2 ^ m), show (2 : ℕ) ^ 144 = 22300745198530623141535718272648361505980416 from by norm_num] at h3
    exact c20_f144 hP h5 E h3
  · have h2 : m % (2 * 2 ^ 147) = 2 ^ 147 := by rw [← pow_succ']; exact h
    have h3 := one_add_pow_dvd_of_odd_mul (z := 2) h2
    rw [add_comm 1 (2 ^ m), show (2 : ℕ) ^ 147 = 178405961588244985132285746181186892047843328 from by norm_num] at h3
    exact c20_f147 hP h5 E h3
  · have h2 : m % (2 * 2 ^ 150) = 2 ^ 150 := by rw [← pow_succ']; exact h
    have h3 := one_add_pow_dvd_of_odd_mul (z := 2) h2
    rw [add_comm 1 (2 ^ m), show (2 : ℕ) ^ 150 = 1427247692705959881058285969449495136382746624 from by norm_num] at h3
    exact c20_f150 hP h5 E h3
  · have h2 : m % (2 * 2 ^ 201) = 2 ^ 201 := by rw [← pow_succ']; exact h
    have h3 := one_add_pow_dvd_of_odd_mul (z := 2) h2
    rw [add_comm 1 (2 ^ m), show (2 : ℕ) ^ 201 = 3213876088517980551083924184682325205044405987565585670602752 from by norm_num] at h3
    exact c20_f201 hP h5 E h3
  · have h2 : m % (2 * 2 ^ 207) = 2 ^ 207 := by rw [← pow_succ']; exact h
    have h3 := one_add_pow_dvd_of_odd_mul (z := 2) h2
    rw [add_comm 1 (2 ^ m), show (2 : ℕ) ^ 207 = 205688069665150755269371147819668813122841983204197482918576128 from by norm_num] at h3
    exact c20_f207 hP h5 E h3
  · have h2 : m % (2 * 2 ^ 215) = 2 ^ 215 := by rw [← pow_succ']; exact h
    have h3 := one_add_pow_dvd_of_odd_mul (z := 2) h2
    rw [add_comm 1 (2 ^ m), show (2 : ℕ) ^ 215 = 52656145834278593348959013841835216159447547700274555627155488768 from by norm_num] at h3
    exact c20_f215 hP h5 E h3
  · have h2 : m % (2 * 2 ^ 226) = 2 ^ 226 := by rw [← pow_succ']; exact h
    have h3 := one_add_pow_dvd_of_odd_mul (z := 2) h2
    rw [add_comm 1 (2 ^ m), show (2 : ℕ) ^ 226 = 107839786668602559178668060348078522694548577690162289924414440996864 from by norm_num] at h3
    exact c20_f226 hP h5 E h3
  · have h2 : m % (2 * 2 ^ 228) = 2 ^ 228 := by rw [← pow_succ']; exact h
    have h3 := one_add_pow_dvd_of_odd_mul (z := 2) h2
    rw [add_comm 1 (2 ^ m), show (2 : ℕ) ^ 228 = 431359146674410236714672241392314090778194310760649159697657763987456 from by norm_num] at h3
    exact c20_f228 hP h5 E h3
  · have h2 : m % (2 * 2 ^ 250) = 2 ^ 250 := by rw [← pow_succ']; exact h
    have h3 := one_add_pow_dvd_of_odd_mul (z := 2) h2
    rw [add_comm 1 (2 ^ m), show (2 : ℕ) ^ 250 = 1809251394333065553493296640760748560207343510400633813116524750123642650624 from by norm_num] at h3
    exact c20_f250 hP h5 E h3


theorem main : H1 → H2 → H3 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1.H1 := by
  rintro ⟨A1, h1⟩ ⟨A2, h2⟩ ⟨A3, h3⟩
  refine ⟨A1 + A2 + A3, fun n h hS he h43 hodd h24 h65 hR => ?_⟩
  obtain ⟨hP, h5, E⟩ := setup h hS
  rw [he] at E
  have hD : ∀ e0 : ℕ, padicValNat 2 n % (2 * e0) = e0 → 1 + 2 ^ e0 ∣ 2 ^ padicValNat 2 n + 1 :=
    fun e0 he0 => by
      have := one_add_pow_dvd_of_odd_mul (z := 2) he0
      rwa [add_comm 1 (2 ^ padicValNat 2 n)] at this
  rcases (by omega : padicValNat 2 n % 2 = 1 ∨ padicValNat 2 n % 4 = 2 ∨ padicValNat 2 n % 4 = 0)
    with ha | ha | ha
  · have := h1 n h hS he h43 ha (fun d hd hda => by
      have h43d := hodd ha d hd hda
      have hD' := hD d (mod_of_dvd_odd hda ha)
      have h3 : d % 3 = 1 := by
        rcases (by omega : d % 3 = 0 ∨ d % 3 = 1 ∨ d % 3 = 2) with h0 | h0 | h0
        · exfalso
          have h3d : 3 ∣ d := Nat.dvd_of_mod_eq_zero h0
          have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hd).mp h3d
          omega
        · exact h0
        · exact (odd_mod3 hP h5 E ha hd hda h0).elim
      refine ⟨?_, h3⟩
      by_contra hlt
      push Not at hlt
      exact odd_sieve hP h5 E hd h3 hD' h43d (by omega))
    omega
  · have := h2 n h hS he h43 ha (fun d hd hd2 hda => by
      have h101 := h24 ha d hd hd2 hda
      have hdo : d % 2 = 1 := hd.eq_two_or_odd.resolve_left hd2
      have hD' := hD (2 * d) (mod_of_dvd_two_mod_four hda hdo ha)
      by_contra hlt
      push Not at hlt
      exact even_sieve hP h5 E hd hD' h101 (by omega))
    omega
  · have := h3 n h hS he h43 ha hR (fermat20 hP h5 E)
    omega

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H1_R1
