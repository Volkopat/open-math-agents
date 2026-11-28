import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H1.R1.H1.R1
-- Credit: @adammcarter
-- Splits step H1 of Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H1.R1 (3 is the only repeated odd prime, its
-- exponent e is 5 or 7, a = the 2-adic valuation of n is no odd multiple of the 73 listed values)
-- by the exponent e, with a much longer list of excluded classes of a built in.  Proving H1 and H2
-- proves the step.
--
-- Notation: n unitary perfect, every odd prime other than 3 divides n exactly once (the simple
-- primes), e = n.factorization 3, a = padicValNat 2 n.  a is an ODD MULTIPLE of d when
-- a mod 2d = d; then 2^d + 1 divides 2^a + 1.  Balance equation:
--   (2^a + 1)(3^e + 1) prod (p + 1) = 2^(a+1) 3^e prod p   (products over the simple primes p).
--
-- PROVED BELOW (no hypothesis needed), for e = 5 and for e = 7:
--   (1) a is no odd multiple of ANY d with 10 <= d <= 257 other than 11 and 13
--       (sieve_e5, sieve_e7).
--   (2) a is no odd multiple of 2^k for 9 <= k <= 19 (fermat_e5, fermat_e7; known prime factors
--       of the Fermat numbers F9, ..., F19; 16, ..., 256 are in (1)).
--   (3) if a is odd, at most 4 primes p = 2 mod 3 divide a (odd_count_e5, odd_count_e7).
--   (4) a >= 262 (lower_e5, lower_e7): below 262, (1) leaves only a <= 9, a = 11, a = 13, and
--       there the primes forced by 2^a + 1 and 3^e + 1 hold more than a + 1 factors of 2.
--   Together: the 2-adic valuation s of a is 0, 1, 2, 3 or at least 20.  If a is odd, every prime
--   factor of a is 3, 5, 7, 11, 13 or larger than 257 (and 15, 21, 25, 27, 33, ... do not divide
--   a).  If s = 1, 2, 3, every odd prime factor of a is larger than 128, 64, 32 (or is 3, s = 1).
-- Method (forced roots): every prime q of 2^d + 1 divides n, so q is simple, every odd prime
-- other than 3 of q + 1 is simple again, and so on.  Each odd prime other than 3 has exactly one
-- source on the left of the balance equation, and 3 has exactly e sources.  Each lemma k18_d<d>
-- (any e), k18e5_d<d>, k18e7_d<d> follows such a chain to a prime with two sources, a square, or
-- more than e factors of 3 (the chain 3^5 + 1 = 4 * 61, 62 = 2 * 31 for e = 5 and
-- 3^7 + 1 = 4 * 547, 548 = 4 * 137, 138 = 2 * 3 * 23, 24 = 8 * 3 for e = 7 is used too).
-- The primes above 4.3 * 10^7 are certified by the Lucas test (theorems prime_<p>).
-- (3) needs no factorization: for an odd prime p = 2 mod 3 the number (2^p + 1) / 3 is 2 mod 3, so
-- 2^p + 1 has a prime factor q = 2 mod 3, different p give different q, and each such q + 1 uses
-- a factor of 3; 2^a + 1 itself uses one more.
--
-- H1 (OPEN): e = 5, a >= 262 outside all these classes.
-- H2 (OPEN): e = 7, a >= 262 outside all these classes.
-- No known unitary perfect number satisfies the hypotheses of H1 or H2.

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H1_R1

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 hiding H1 H2 H3 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1 hiding H1 H2 H3 main

-- H1: the 2-adic valuation a is bounded over the unitary perfect numbers whose only repeated odd
-- prime is 3, with exponent 5, a >= 262, a no odd multiple of any d in 10..257 except 11, 13,
-- nor of 2^9, ..., 2^19, and, when a is odd, at most 4 primes p = 2 mod 3 dividing a.
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    n.factorization 3 = 5 →
    262 ≤ padicValNat 2 n →
    (∀ d, 10 ≤ d → d ≤ 257 → d ∉ ({11, 13} : Finset ℕ) → padicValNat 2 n % (2 * d) ≠ d) →
    (∀ d ∈ ({512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144,
        524288} : Finset ℕ), padicValNat 2 n % (2 * d) ≠ d) →
    (padicValNat 2 n % 2 = 1 →
      ((padicValNat 2 n).primeFactors.filter (fun p => p % 3 = 2)).card ≤ 4) →
    padicValNat 2 n ≤ A

-- H2: the same with exponent 7.
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    (∀ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n ↔ p = 3) →
    n.factorization 3 = 7 →
    262 ≤ padicValNat 2 n →
    (∀ d, 10 ≤ d → d ≤ 257 → d ∉ ({11, 13} : Finset ℕ) → padicValNat 2 n % (2 * d) ≠ d) →
    (∀ d ∈ ({512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144,
        524288} : Finset ℕ), padicValNat 2 n % (2 * d) ≠ d) →
    (padicValNat 2 n % 2 = 1 →
      ((padicValNat 2 n).primeFactors.filter (fun p => p % 3 = 2)).card ≤ 4) →
    padicValNat 2 n ≤ A

theorem prime_715827883 : Nat.Prime 715827883 := by
  refine lucas_primality 715827883 (5 : ZMod 715827883) ?_ (fun q hq hd => ?_)
  · rw [show 715827883 - 1 = 715827882 from by norm_num]
    reduce_mod_char
  · have e : 715827883 - 1 = [2 ^ 1, 3 ^ 1, 7 ^ 1, 11 ^ 1, 31 ^ 1, 151 ^ 1, 331 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (715827883 - 1) / 2 = 357913941 from by norm_num]
      have h2 : (5 : ZMod 715827883) ^ 357913941 = ((715827882 : ℕ) : ZMod 715827883) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (715827883 - 1) / 3 = 238609294 from by norm_num]
      have h2 : (5 : ZMod 715827883) ^ 238609294 = ((151888732 : ℕ) : ZMod 715827883) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (715827883 - 1) / 7 = 102261126 from by norm_num]
      have h2 : (5 : ZMod 715827883) ^ 102261126 = ((131416656 : ℕ) : ZMod 715827883) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (715827883 - 1) / 11 = 65075262 from by norm_num]
      have h2 : (5 : ZMod 715827883) ^ 65075262 = ((423957234 : ℕ) : ZMod 715827883) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (715827883 - 1) / 31 = 23091222 from by norm_num]
      have h2 : (5 : ZMod 715827883) ^ 23091222 = ((4096 : ℕ) : ZMod 715827883) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (715827883 - 1) / 151 = 4740582 from by norm_num]
      have h2 : (5 : ZMod 715827883) ^ 4740582 = ((451339760 : ℕ) : ZMod 715827883) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (715827883 - 1) / 331 = 2162622 from by norm_num]
      have h2 : (5 : ZMod 715827883) ^ 2162622 = ((446444286 : ℕ) : ZMod 715827883) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_4278255361 : Nat.Prime 4278255361 := by
  refine lucas_primality 4278255361 (23 : ZMod 4278255361) ?_ (fun q hq hd => ?_)
  · rw [show 4278255361 - 1 = 4278255360 from by norm_num]
    reduce_mod_char
  · have e : 4278255361 - 1 = [2 ^ 8, 3 ^ 1, 5 ^ 1, 17 ^ 1, 65537 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4278255361 - 1) / 2 = 2139127680 from by norm_num]
      have h2 : (23 : ZMod 4278255361) ^ 2139127680 = ((4278255360 : ℕ) : ZMod 4278255361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4278255361 - 1) / 3 = 1426085120 from by norm_num]
      have h2 : (23 : ZMod 4278255361) ^ 1426085120 = ((265752886 : ℕ) : ZMod 4278255361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4278255361 - 1) / 5 = 855651072 from by norm_num]
      have h2 : (23 : ZMod 4278255361) ^ 855651072 = ((65536 : ℕ) : ZMod 4278255361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4278255361 - 1) / 17 = 251662080 from by norm_num]
      have h2 : (23 : ZMod 4278255361) ^ 251662080 = ((2887654611 : ℕ) : ZMod 4278255361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4278255361 - 1) / 65537 = 65280 from by norm_num]
      have h2 : (23 : ZMod 4278255361) ^ 65280 = ((1936053211 : ℕ) : ZMod 4278255361) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2139127681 : Nat.Prime 2139127681 := by
  refine lucas_primality 2139127681 (14 : ZMod 2139127681) ?_ (fun q hq hd => ?_)
  · rw [show 2139127681 - 1 = 2139127680 from by norm_num]
    reduce_mod_char
  · have e : 2139127681 - 1 = [2 ^ 7, 3 ^ 1, 5 ^ 1, 17 ^ 1, 65537 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2139127681 - 1) / 2 = 1069563840 from by norm_num]
      have h2 : (14 : ZMod 2139127681) ^ 1069563840 = ((2139127680 : ℕ) : ZMod 2139127681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2139127681 - 1) / 3 = 713042560 from by norm_num]
      have h2 : (14 : ZMod 2139127681) ^ 713042560 = ((1280083319 : ℕ) : ZMod 2139127681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2139127681 - 1) / 5 = 427825536 from by norm_num]
      have h2 : (14 : ZMod 2139127681) ^ 427825536 = ((1177214020 : ℕ) : ZMod 2139127681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2139127681 - 1) / 17 = 125831040 from by norm_num]
      have h2 : (14 : ZMod 2139127681) ^ 125831040 = ((1566319278 : ℕ) : ZMod 2139127681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2139127681 - 1) / 65537 = 32640 from by norm_num]
      have h2 : (14 : ZMod 2139127681) ^ 32640 = ((574960972 : ℕ) : ZMod 2139127681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_8831418697 : Nat.Prime 8831418697 := by
  refine lucas_primality 8831418697 (15 : ZMod 8831418697) ?_ (fun q hq hd => ?_)
  · rw [show 8831418697 - 1 = 8831418696 from by norm_num]
    reduce_mod_char
  · have e : 8831418697 - 1 = [2 ^ 3, 3 ^ 2, 41 ^ 1, 2991673 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8831418697 - 1) / 2 = 4415709348 from by norm_num]
      have h2 : (15 : ZMod 8831418697) ^ 4415709348 = ((8831418696 : ℕ) : ZMod 8831418697) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8831418697 - 1) / 3 = 2943806232 from by norm_num]
      have h2 : (15 : ZMod 8831418697) ^ 2943806232 = ((5431831338 : ℕ) : ZMod 8831418697) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8831418697 - 1) / 41 = 215400456 from by norm_num]
      have h2 : (15 : ZMod 8831418697) ^ 215400456 = ((8831287625 : ℕ) : ZMod 8831418697) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8831418697 - 1) / 2991673 = 2952 from by norm_num]
      have h2 : (15 : ZMod 8831418697) ^ 2952 = ((2310795530 : ℕ) : ZMod 8831418697) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2932031007403 : Nat.Prime 2932031007403 := by
  refine lucas_primality 2932031007403 (3 : ZMod 2932031007403) ?_ (fun q hq hd => ?_)
  · rw [show 2932031007403 - 1 = 2932031007402 from by norm_num]
    reduce_mod_char
  · have e : 2932031007403 - 1 = [2 ^ 1, 3 ^ 1, 7 ^ 2, 43 ^ 1, 127 ^ 1, 337 ^ 1, 5419 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2932031007403 - 1) / 2 = 1466015503701 from by norm_num]
      have h2 : (3 : ZMod 2932031007403) ^ 1466015503701 = ((2932031007402 : ℕ) : ZMod 2932031007403) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2932031007403 - 1) / 3 = 977343669134 from by norm_num]
      have h2 : (3 : ZMod 2932031007403) ^ 977343669134 = ((1616581872411 : ℕ) : ZMod 2932031007403) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2932031007403 - 1) / 7 = 418861572486 from by norm_num]
      have h2 : (3 : ZMod 2932031007403) ^ 418861572486 = ((622869028911 : ℕ) : ZMod 2932031007403) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2932031007403 - 1) / 43 = 68186767614 from by norm_num]
      have h2 : (3 : ZMod 2932031007403) ^ 68186767614 = ((2931494136491 : ℕ) : ZMod 2932031007403) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2932031007403 - 1) / 127 = 23086858326 from by norm_num]
      have h2 : (3 : ZMod 2932031007403) ^ 23086858326 = ((1610672779439 : ℕ) : ZMod 2932031007403) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2932031007403 - 1) / 337 = 8700388746 from by norm_num]
      have h2 : (3 : ZMod 2932031007403) ^ 8700388746 = ((1777987394008 : ℕ) : ZMod 2932031007403) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2932031007403 - 1) / 5419 = 541064958 from by norm_num]
      have h2 : (3 : ZMod 2932031007403) ^ 541064958 = ((2145654789947 : ℕ) : ZMod 2932031007403) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2931542417 : Nat.Prime 2931542417 := by
  refine lucas_primality 2931542417 (3 : ZMod 2931542417) ?_ (fun q hq hd => ?_)
  · rw [show 2931542417 - 1 = 2931542416 from by norm_num]
    reduce_mod_char
  · have e : 2931542417 - 1 = [2 ^ 4, 11 ^ 1, 1913 ^ 1, 8707 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2931542417 - 1) / 2 = 1465771208 from by norm_num]
      have h2 : (3 : ZMod 2931542417) ^ 1465771208 = ((2931542416 : ℕ) : ZMod 2931542417) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2931542417 - 1) / 11 = 266503856 from by norm_num]
      have h2 : (3 : ZMod 2931542417) ^ 266503856 = ((1363424879 : ℕ) : ZMod 2931542417) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2931542417 - 1) / 1913 = 1532432 from by norm_num]
      have h2 : (3 : ZMod 2931542417) ^ 1532432 = ((1273031522 : ℕ) : ZMod 2931542417) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2931542417 - 1) / 8707 = 336688 from by norm_num]
      have h2 : (3 : ZMod 2931542417) ^ 336688 = ((1179572524 : ℕ) : ZMod 2931542417) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_165768537521 : Nat.Prime 165768537521 := by
  refine lucas_primality 165768537521 (3 : ZMod 165768537521) ?_ (fun q hq hd => ?_)
  · rw [show 165768537521 - 1 = 165768537520 from by norm_num]
    reduce_mod_char
  · have e : 165768537521 - 1 = [2 ^ 4, 5 ^ 1, 47 ^ 1, 2887 ^ 1, 15271 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (165768537521 - 1) / 2 = 82884268760 from by norm_num]
      have h2 : (3 : ZMod 165768537521) ^ 82884268760 = ((165768537520 : ℕ) : ZMod 165768537521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (165768537521 - 1) / 5 = 33153707504 from by norm_num]
      have h2 : (3 : ZMod 165768537521) ^ 33153707504 = ((68616265392 : ℕ) : ZMod 165768537521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (165768537521 - 1) / 47 = 3526990160 from by norm_num]
      have h2 : (3 : ZMod 165768537521) ^ 3526990160 = ((165734983089 : ℕ) : ZMod 165768537521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (165768537521 - 1) / 2887 = 57418960 from by norm_num]
      have h2 : (3 : ZMod 165768537521) ^ 57418960 = ((6910349427 : ℕ) : ZMod 165768537521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (165768537521 - 1) / 15271 = 10855120 from by norm_num]
      have h2 : (3 : ZMod 165768537521) ^ 10855120 = ((78255376458 : ℕ) : ZMod 165768537521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_4363953127297 : Nat.Prime 4363953127297 := by
  refine lucas_primality 4363953127297 (5 : ZMod 4363953127297) ?_ (fun q hq hd => ?_)
  · rw [show 4363953127297 - 1 = 4363953127296 from by norm_num]
    reduce_mod_char
  · have e : 4363953127297 - 1 = [2 ^ 7, 3 ^ 1, 7 ^ 2, 127 ^ 1, 337 ^ 1, 5419 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4363953127297 - 1) / 2 = 2181976563648 from by norm_num]
      have h2 : (5 : ZMod 4363953127297) ^ 2181976563648 = ((4363953127296 : ℕ) : ZMod 4363953127297) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4363953127297 - 1) / 3 = 1454651042432 from by norm_num]
      have h2 : (5 : ZMod 4363953127297) ^ 1454651042432 = ((3735730723197 : ℕ) : ZMod 4363953127297) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4363953127297 - 1) / 7 = 623421875328 from by norm_num]
      have h2 : (5 : ZMod 4363953127297) ^ 623421875328 = ((4329593388929 : ℕ) : ZMod 4363953127297) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4363953127297 - 1) / 127 = 34361835648 from by norm_num]
      have h2 : (5 : ZMod 4363953127297) ^ 34361835648 = ((741582913463 : ℕ) : ZMod 4363953127297) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4363953127297 - 1) / 337 = 12949415808 from by norm_num]
      have h2 : (5 : ZMod 4363953127297) ^ 12949415808 = ((551396850060 : ℕ) : ZMod 4363953127297) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4363953127297 - 1) / 5419 = 805305984 from by norm_num]
      have h2 : (5 : ZMod 4363953127297) ^ 805305984 = ((603965658536 : ℕ) : ZMod 4363953127297) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_67254877 : Nat.Prime 67254877 := by
  refine lucas_primality 67254877 (2 : ZMod 67254877) ?_ (fun q hq hd => ?_)
  · rw [show 67254877 - 1 = 67254876 from by norm_num]
    reduce_mod_char
  · have e : 67254877 - 1 = [2 ^ 2, 3 ^ 2, 13 ^ 1, 131 ^ 1, 1097 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (67254877 - 1) / 2 = 33627438 from by norm_num]
      have h2 : (2 : ZMod 67254877) ^ 33627438 = ((67254876 : ℕ) : ZMod 67254877) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (67254877 - 1) / 3 = 22418292 from by norm_num]
      have h2 : (2 : ZMod 67254877) ^ 22418292 = ((32183595 : ℕ) : ZMod 67254877) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (67254877 - 1) / 13 = 5173452 from by norm_num]
      have h2 : (2 : ZMod 67254877) ^ 5173452 = ((19873645 : ℕ) : ZMod 67254877) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (67254877 - 1) / 131 = 513396 from by norm_num]
      have h2 : (2 : ZMod 67254877) ^ 513396 = ((18959693 : ℕ) : ZMod 67254877) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (67254877 - 1) / 1097 = 61308 from by norm_num]
      have h2 : (2 : ZMod 67254877) ^ 61308 = ((36918246 : ℕ) : ZMod 67254877) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_28059810762433 : Nat.Prime 28059810762433 := by
  refine lucas_primality 28059810762433 (5 : ZMod 28059810762433) ?_ (fun q hq hd => ?_)
  · rw [show 28059810762433 - 1 = 28059810762432 from by norm_num]
    reduce_mod_char
  · have e : 28059810762433 - 1 = [2 ^ 6, 3 ^ 1, 41 ^ 1, 53 ^ 1, 67254877 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (28059810762433 - 1) / 2 = 14029905381216 from by norm_num]
      have h2 : (5 : ZMod 28059810762433) ^ 14029905381216 = ((28059810762432 : ℕ) : ZMod 28059810762433) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (28059810762433 - 1) / 3 = 9353270254144 from by norm_num]
      have h2 : (5 : ZMod 28059810762433) ^ 9353270254144 = ((25962592041197 : ℕ) : ZMod 28059810762433) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (28059810762433 - 1) / 41 = 684385628352 from by norm_num]
      have h2 : (5 : ZMod 28059810762433) ^ 684385628352 = ((2428815610770 : ℕ) : ZMod 28059810762433) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (28059810762433 - 1) / 53 = 529430391744 from by norm_num]
      have h2 : (5 : ZMod 28059810762433) ^ 529430391744 = ((28059810762305 : ℕ) : ZMod 28059810762433) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_67254877).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (28059810762433 - 1) / 67254877 = 417216 from by norm_num]
      have h2 : (5 : ZMod 28059810762433) ^ 417216 = ((27349741008203 : ℕ) : ZMod 28059810762433) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1275445943747 : Nat.Prime 1275445943747 := by
  refine lucas_primality 1275445943747 (2 : ZMod 1275445943747) ?_ (fun q hq hd => ?_)
  · rw [show 1275445943747 - 1 = 1275445943746 from by norm_num]
    reduce_mod_char
  · have e : 1275445943747 - 1 = [2 ^ 1, 13 ^ 1, 227 ^ 1, 12239 ^ 1, 17657 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1275445943747 - 1) / 2 = 637722971873 from by norm_num]
      have h2 : (2 : ZMod 1275445943747) ^ 637722971873 = ((1275445943746 : ℕ) : ZMod 1275445943747) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1275445943747 - 1) / 13 = 98111226442 from by norm_num]
      have h2 : (2 : ZMod 1275445943747) ^ 98111226442 = ((315239952175 : ℕ) : ZMod 1275445943747) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1275445943747 - 1) / 227 = 5618704598 from by norm_num]
      have h2 : (2 : ZMod 1275445943747) ^ 5618704598 = ((537351048113 : ℕ) : ZMod 1275445943747) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1275445943747 - 1) / 12239 = 104211614 from by norm_num]
      have h2 : (2 : ZMod 1275445943747) ^ 104211614 = ((804237427832 : ℕ) : ZMod 1275445943747) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1275445943747 - 1) / 17657 = 72234578 from by norm_num]
      have h2 : (2 : ZMod 1275445943747) ^ 72234578 = ((1261028853167 : ℕ) : ZMod 1275445943747) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1221691517 : Nat.Prime 1221691517 := by
  refine lucas_primality 1221691517 (2 : ZMod 1221691517) ?_ (fun q hq hd => ?_)
  · rw [show 1221691517 - 1 = 1221691516 from by norm_num]
    reduce_mod_char
  · have e : 1221691517 - 1 = [2 ^ 2, 673 ^ 1, 453823 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1221691517 - 1) / 2 = 610845758 from by norm_num]
      have h2 : (2 : ZMod 1221691517) ^ 610845758 = ((1221691516 : ℕ) : ZMod 1221691517) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1221691517 - 1) / 673 = 1815292 from by norm_num]
      have h2 : (2 : ZMod 1221691517) ^ 1815292 = ((1173629453 : ℕ) : ZMod 1221691517) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1221691517 - 1) / 453823 = 2692 from by norm_num]
      have h2 : (2 : ZMod 1221691517) ^ 2692 = ((256891420 : ℕ) : ZMod 1221691517) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_107367629 : Nat.Prime 107367629 := by
  refine lucas_primality 107367629 (3 : ZMod 107367629) ?_ (fun q hq hd => ?_)
  · rw [show 107367629 - 1 = 107367628 from by norm_num]
    reduce_mod_char
  · have e : 107367629 - 1 = [2 ^ 2, 29 ^ 1, 113 ^ 1, 8191 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (107367629 - 1) / 2 = 53683814 from by norm_num]
      have h2 : (3 : ZMod 107367629) ^ 53683814 = ((107367628 : ℕ) : ZMod 107367629) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (107367629 - 1) / 29 = 3702332 from by norm_num]
      have h2 : (3 : ZMod 107367629) ^ 3702332 = ((105270605 : ℕ) : ZMod 107367629) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (107367629 - 1) / 113 = 950156 from by norm_num]
      have h2 : (3 : ZMod 107367629) ^ 950156 = ((85379517 : ℕ) : ZMod 107367629) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (107367629 - 1) / 8191 = 13108 from by norm_num]
      have h2 : (3 : ZMod 107367629) ^ 13108 = ((97781882 : ℕ) : ZMod 107367629) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_768614336404564651 : Nat.Prime 768614336404564651 := by
  refine lucas_primality 768614336404564651 (3 : ZMod 768614336404564651) ?_ (fun q hq hd => ?_)
  · rw [show 768614336404564651 - 1 = 768614336404564650 from by norm_num]
    reduce_mod_char
  · have e : 768614336404564651 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 2, 7 ^ 1, 11 ^ 1, 13 ^ 1, 31 ^ 1, 41 ^ 1, 61 ^ 1, 151 ^ 1, 331 ^ 1, 1321 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (768614336404564651 - 1) / 2 = 384307168202282325 from by norm_num]
      have h2 : (3 : ZMod 768614336404564651) ^ 384307168202282325 = ((768614336404564650 : ℕ) : ZMod 768614336404564651) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (768614336404564651 - 1) / 3 = 256204778801521550 from by norm_num]
      have h2 : (3 : ZMod 768614336404564651) ^ 256204778801521550 = ((243065045915817725 : ℕ) : ZMod 768614336404564651) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (768614336404564651 - 1) / 5 = 153722867280912930 from by norm_num]
      have h2 : (3 : ZMod 768614336404564651) ^ 153722867280912930 = ((754529885435533861 : ℕ) : ZMod 768614336404564651) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (768614336404564651 - 1) / 7 = 109802048057794950 from by norm_num]
      have h2 : (3 : ZMod 768614336404564651) ^ 109802048057794950 = ((3782361620868430 : ℕ) : ZMod 768614336404564651) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (768614336404564651 - 1) / 11 = 69874030582233150 from by norm_num]
      have h2 : (3 : ZMod 768614336404564651) ^ 69874030582233150 = ((258177292182522579 : ℕ) : ZMod 768614336404564651) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (768614336404564651 - 1) / 13 = 59124179723428050 from by norm_num]
      have h2 : (3 : ZMod 768614336404564651) ^ 59124179723428050 = ((89030510150922805 : ℕ) : ZMod 768614336404564651) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (768614336404564651 - 1) / 31 = 24794010851760150 from by norm_num]
      have h2 : (3 : ZMod 768614336404564651) ^ 24794010851760150 = ((478446363355159889 : ℕ) : ZMod 768614336404564651) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (768614336404564651 - 1) / 41 = 18746691131818650 from by norm_num]
      have h2 : (3 : ZMod 768614336404564651) ^ 18746691131818650 = ((16212047901619696 : ℕ) : ZMod 768614336404564651) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (768614336404564651 - 1) / 61 = 12600235023025650 from by norm_num]
      have h2 : (3 : ZMod 768614336404564651) ^ 12600235023025650 = ((759607137149823659 : ℕ) : ZMod 768614336404564651) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (768614336404564651 - 1) / 151 = 5090161168242150 from by norm_num]
      have h2 : (3 : ZMod 768614336404564651) ^ 5090161168242150 = ((273041510166617890 : ℕ) : ZMod 768614336404564651) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (768614336404564651 - 1) / 331 = 2322097693065150 from by norm_num]
      have h2 : (3 : ZMod 768614336404564651) ^ 2322097693065150 = ((106391769181428972 : ℕ) : ZMod 768614336404564651) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (768614336404564651 - 1) / 1321 = 581842798186650 from by norm_num]
      have h2 : (3 : ZMod 768614336404564651) ^ 581842798186650 = ((348054768387184126 : ℕ) : ZMod 768614336404564651) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_56409643 : Nat.Prime 56409643 := by
  refine lucas_primality 56409643 (3 : ZMod 56409643) ?_ (fun q hq hd => ?_)
  · rw [show 56409643 - 1 = 56409642 from by norm_num]
    reduce_mod_char
  · have e : 56409643 - 1 = [2 ^ 1, 3 ^ 3, 71 ^ 1, 14713 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56409643 - 1) / 2 = 28204821 from by norm_num]
      have h2 : (3 : ZMod 56409643) ^ 28204821 = ((56409642 : ℕ) : ZMod 56409643) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56409643 - 1) / 3 = 18803214 from by norm_num]
      have h2 : (3 : ZMod 56409643) ^ 18803214 = ((39676424 : ℕ) : ZMod 56409643) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56409643 - 1) / 71 = 794502 from by norm_num]
      have h2 : (3 : ZMod 56409643) ^ 794502 = ((53765441 : ℕ) : ZMod 56409643) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56409643 - 1) / 14713 = 3834 from by norm_num]
      have h2 : (3 : ZMod 56409643) ^ 3834 = ((53217898 : ℕ) : ZMod 56409643) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_408485041 : Nat.Prime 408485041 := by
  refine lucas_primality 408485041 (14 : ZMod 408485041) ?_ (fun q hq hd => ?_)
  · rw [show 408485041 - 1 = 408485040 from by norm_num]
    reduce_mod_char
  · have e : 408485041 - 1 = [2 ^ 4, 3 ^ 1, 5 ^ 1, 643 ^ 1, 2647 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (408485041 - 1) / 2 = 204242520 from by norm_num]
      have h2 : (14 : ZMod 408485041) ^ 204242520 = ((408485040 : ℕ) : ZMod 408485041) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (408485041 - 1) / 3 = 136161680 from by norm_num]
      have h2 : (14 : ZMod 408485041) ^ 136161680 = ((140641119 : ℕ) : ZMod 408485041) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (408485041 - 1) / 5 = 81697008 from by norm_num]
      have h2 : (14 : ZMod 408485041) ^ 81697008 = ((335297734 : ℕ) : ZMod 408485041) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (408485041 - 1) / 643 = 635280 from by norm_num]
      have h2 : (14 : ZMod 408485041) ^ 635280 = ((387566083 : ℕ) : ZMod 408485041) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (408485041 - 1) / 2647 = 154320 from by norm_num]
      have h2 : (14 : ZMod 408485041) ^ 154320 = ((217854788 : ℕ) : ZMod 408485041) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1795918038741070627 : Nat.Prime 1795918038741070627 := by
  refine lucas_primality 1795918038741070627 (3 : ZMod 1795918038741070627) ?_ (fun q hq hd => ?_)
  · rw [show 1795918038741070627 - 1 = 1795918038741070626 from by norm_num]
    reduce_mod_char
  · have e : 1795918038741070627 - 1 = [2 ^ 1, 3 ^ 1, 73 ^ 1, 811 ^ 1, 12377 ^ 1, 408485041 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1795918038741070627 - 1) / 2 = 897959019370535313 from by norm_num]
      have h2 : (3 : ZMod 1795918038741070627) ^ 897959019370535313 = ((1795918038741070626 : ℕ) : ZMod 1795918038741070627) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1795918038741070627 - 1) / 3 = 598639346247023542 from by norm_num]
      have h2 : (3 : ZMod 1795918038741070627) ^ 598639346247023542 = ((921337008399566903 : ℕ) : ZMod 1795918038741070627) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1795918038741070627 - 1) / 73 = 24601616969055762 from by norm_num]
      have h2 : (3 : ZMod 1795918038741070627) ^ 24601616969055762 = ((1795918038741062435 : ℕ) : ZMod 1795918038741070627) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1795918038741070627 - 1) / 811 = 2214448876376166 from by norm_num]
      have h2 : (3 : ZMod 1795918038741070627) ^ 2214448876376166 = ((677514307306795143 : ℕ) : ZMod 1795918038741070627) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1795918038741070627 - 1) / 12377 = 145101239293938 from by norm_num]
      have h2 : (3 : ZMod 1795918038741070627) ^ 145101239293938 = ((432233706032238227 : ℕ) : ZMod 1795918038741070627) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_408485041).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1795918038741070627 - 1) / 408485041 = 4396533186 from by norm_num]
      have h2 : (3 : ZMod 1795918038741070627) ^ 4396533186 = ((704525249629462922 : ℕ) : ZMod 1795918038741070627) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_194247044059 : Nat.Prime 194247044059 := by
  refine lucas_primality 194247044059 (10 : ZMod 194247044059) ?_ (fun q hq hd => ?_)
  · rw [show 194247044059 - 1 = 194247044058 from by norm_num]
    reduce_mod_char
  · have e : 194247044059 - 1 = [2 ^ 1, 3 ^ 1, 1553 ^ 1, 20846431 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (194247044059 - 1) / 2 = 97123522029 from by norm_num]
      have h2 : (10 : ZMod 194247044059) ^ 97123522029 = ((194247044058 : ℕ) : ZMod 194247044059) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (194247044059 - 1) / 3 = 64749014686 from by norm_num]
      have h2 : (10 : ZMod 194247044059) ^ 64749014686 = ((128897037365 : ℕ) : ZMod 194247044059) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (194247044059 - 1) / 1553 = 125078586 from by norm_num]
      have h2 : (10 : ZMod 194247044059) ^ 125078586 = ((28685034248 : ℕ) : ZMod 194247044059) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (194247044059 - 1) / 20846431 = 9318 from by norm_num]
      have h2 : (10 : ZMod 194247044059) ^ 9318 = ((71173260157 : ℕ) : ZMod 194247044059) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_448979509685267657 : Nat.Prime 448979509685267657 := by
  refine lucas_primality 448979509685267657 (3 : ZMod 448979509685267657) ?_ (fun q hq hd => ?_)
  · rw [show 448979509685267657 - 1 = 448979509685267656 from by norm_num]
    reduce_mod_char
  · have e : 448979509685267657 - 1 = [2 ^ 3, 59 ^ 2, 83 ^ 1, 194247044059 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (448979509685267657 - 1) / 2 = 224489754842633828 from by norm_num]
      have h2 : (3 : ZMod 448979509685267657) ^ 224489754842633828 = ((448979509685267656 : ℕ) : ZMod 448979509685267657) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (448979509685267657 - 1) / 59 = 7609822198055384 from by norm_num]
      have h2 : (3 : ZMod 448979509685267657) ^ 7609822198055384 = ((382227398645814846 : ℕ) : ZMod 448979509685267657) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (448979509685267657 - 1) / 83 = 5409391682955032 from by norm_num]
      have h2 : (3 : ZMod 448979509685267657) ^ 5409391682955032 = ((401033488626267068 : ℕ) : ZMod 448979509685267657) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_194247044059).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (448979509685267657 - 1) / 194247044059 = 2311384 from by norm_num]
      have h2 : (3 : ZMod 448979509685267657) ^ 2311384 = ((357932517406598667 : ℕ) : ZMod 448979509685267657) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1247165304681299 : Nat.Prime 1247165304681299 := by
  refine lucas_primality 1247165304681299 (2 : ZMod 1247165304681299) ?_ (fun q hq hd => ?_)
  · rw [show 1247165304681299 - 1 = 1247165304681298 from by norm_num]
    reduce_mod_char
  · have e : 1247165304681299 - 1 = [2 ^ 1, 71 ^ 1, 1675721 ^ 1, 5241239 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1247165304681299 - 1) / 2 = 623582652340649 from by norm_num]
      have h2 : (2 : ZMod 1247165304681299) ^ 623582652340649 = ((1247165304681298 : ℕ) : ZMod 1247165304681299) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1247165304681299 - 1) / 71 = 17565708516638 from by norm_num]
      have h2 : (2 : ZMod 1247165304681299) ^ 17565708516638 = ((445800491574287 : ℕ) : ZMod 1247165304681299) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1247165304681299 - 1) / 1675721 = 744255938 from by norm_num]
      have h2 : (2 : ZMod 1247165304681299) ^ 744255938 = ((622839404468740 : ℕ) : ZMod 1247165304681299) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1247165304681299 - 1) / 5241239 = 237952382 from by norm_num]
      have h2 : (2 : ZMod 1247165304681299) ^ 237952382 = ((43682376917029 : ℕ) : ZMod 1247165304681299) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_24943306093625981 : Nat.Prime 24943306093625981 := by
  refine lucas_primality 24943306093625981 (2 : ZMod 24943306093625981) ?_ (fun q hq hd => ?_)
  · rw [show 24943306093625981 - 1 = 24943306093625980 from by norm_num]
    reduce_mod_char
  · have e : 24943306093625981 - 1 = [2 ^ 2, 5 ^ 1, 1247165304681299 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (24943306093625981 - 1) / 2 = 12471653046812990 from by norm_num]
      have h2 : (2 : ZMod 24943306093625981) ^ 12471653046812990 = ((24943306093625980 : ℕ) : ZMod 24943306093625981) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (24943306093625981 - 1) / 5 = 4988661218725196 from by norm_num]
      have h2 : (2 : ZMod 24943306093625981) ^ 4988661218725196 = ((17134921030180525 : ℕ) : ZMod 24943306093625981) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1247165304681299).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (24943306093625981 - 1) / 1247165304681299 = 20 from by norm_num]
      have h2 : (2 : ZMod 24943306093625981) ^ 20 = ((1048576 : ℕ) : ZMod 24943306093625981) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_201487636602438195784363 : Nat.Prime 201487636602438195784363 := by
  refine lucas_primality 201487636602438195784363 (3 : ZMod 201487636602438195784363) ?_ (fun q hq hd => ?_)
  · rw [show 201487636602438195784363 - 1 = 201487636602438195784362 from by norm_num]
    reduce_mod_char
  · have e : 201487636602438195784363 - 1 = [2 ^ 1, 3 ^ 1, 7 ^ 1, 79 ^ 1, 2731 ^ 1, 8191 ^ 1, 121369 ^ 1, 22366891 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (201487636602438195784363 - 1) / 2 = 100743818301219097892181 from by norm_num]
      have h2 : (3 : ZMod 201487636602438195784363) ^ 100743818301219097892181 = ((201487636602438195784362 : ℕ) : ZMod 201487636602438195784363) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (201487636602438195784363 - 1) / 3 = 67162545534146065261454 from by norm_num]
      have h2 : (3 : ZMod 201487636602438195784363) ^ 67162545534146065261454 = ((174764665359156168207072 : ℕ) : ZMod 201487636602438195784363) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (201487636602438195784363 - 1) / 7 = 28783948086062599397766 from by norm_num]
      have h2 : (3 : ZMod 201487636602438195784363) ^ 28783948086062599397766 = ((29273057550190743161093 : ℕ) : ZMod 201487636602438195784363) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (201487636602438195784363 - 1) / 79 = 2550476412689091085878 from by norm_num]
      have h2 : (3 : ZMod 201487636602438195784363) ^ 2550476412689091085878 = ((201487636602438195783851 : ℕ) : ZMod 201487636602438195784363) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (201487636602438195784363 - 1) / 2731 = 73777970194960891902 from by norm_num]
      have h2 : (3 : ZMod 201487636602438195784363) ^ 73777970194960891902 = ((201259714364220629927590 : ℕ) : ZMod 201487636602438195784363) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (201487636602438195784363 - 1) / 8191 = 24598661531246269782 from by norm_num]
      have h2 : (3 : ZMod 201487636602438195784363) ^ 24598661531246269782 = ((14751952106037037567816 : ℕ) : ZMod 201487636602438195784363) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (201487636602438195784363 - 1) / 121369 = 1660124385983555898 from by norm_num]
      have h2 : (3 : ZMod 201487636602438195784363) ^ 1660124385983555898 = ((34935602779351748259168 : ℕ) : ZMod 201487636602438195784363) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (201487636602438195784363 - 1) / 22366891 = 9008298766352382 from by norm_num]
      have h2 : (3 : ZMod 201487636602438195784363) ^ 9008298766352382 = ((59199625598676820678420 : ℕ) : ZMod 201487636602438195784363) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_43872038849 : Nat.Prime 43872038849 := by
  refine lucas_primality 43872038849 (3 : ZMod 43872038849) ?_ (fun q hq hd => ?_)
  · rw [show 43872038849 - 1 = 43872038848 from by norm_num]
    reduce_mod_char
  · have e : 43872038849 - 1 = [2 ^ 6, 11 ^ 1, 41 ^ 1, 307 ^ 1, 4951 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (43872038849 - 1) / 2 = 21936019424 from by norm_num]
      have h2 : (3 : ZMod 43872038849) ^ 21936019424 = ((43872038848 : ℕ) : ZMod 43872038849) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (43872038849 - 1) / 11 = 3988367168 from by norm_num]
      have h2 : (3 : ZMod 43872038849) ^ 3988367168 = ((41161382298 : ℕ) : ZMod 43872038849) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (43872038849 - 1) / 41 = 1070049728 from by norm_num]
      have h2 : (3 : ZMod 43872038849) ^ 1070049728 = ((37061802221 : ℕ) : ZMod 43872038849) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (43872038849 - 1) / 307 = 142905664 from by norm_num]
      have h2 : (3 : ZMod 43872038849) ^ 142905664 = ((20366645494 : ℕ) : ZMod 43872038849) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (43872038849 - 1) / 4951 = 8861248 from by norm_num]
      have h2 : (3 : ZMod 43872038849) ^ 8861248 = ((10833867250 : ℕ) : ZMod 43872038849) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_62020897 : Nat.Prime 62020897 := by
  refine lucas_primality 62020897 (15 : ZMod 62020897) ?_ (fun q hq hd => ?_)
  · rw [show 62020897 - 1 = 62020896 from by norm_num]
    reduce_mod_char
  · have e : 62020897 - 1 = [2 ^ 5, 3 ^ 1, 7 ^ 1, 17 ^ 1, 61 ^ 1, 89 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62020897 - 1) / 2 = 31010448 from by norm_num]
      have h2 : (15 : ZMod 62020897) ^ 31010448 = ((62020896 : ℕ) : ZMod 62020897) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62020897 - 1) / 3 = 20673632 from by norm_num]
      have h2 : (15 : ZMod 62020897) ^ 20673632 = ((56823456 : ℕ) : ZMod 62020897) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62020897 - 1) / 7 = 8860128 from by norm_num]
      have h2 : (15 : ZMod 62020897) ^ 8860128 = ((18046535 : ℕ) : ZMod 62020897) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62020897 - 1) / 17 = 3648288 from by norm_num]
      have h2 : (15 : ZMod 62020897) ^ 3648288 = ((16437779 : ℕ) : ZMod 62020897) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62020897 - 1) / 61 = 1016736 from by norm_num]
      have h2 : (15 : ZMod 62020897) ^ 1016736 = ((10148853 : ℕ) : ZMod 62020897) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62020897 - 1) / 89 = 696864 from by norm_num]
      have h2 : (15 : ZMod 62020897) ^ 696864 = ((20504155 : ℕ) : ZMod 62020897) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_291280009243618888211558641 : Nat.Prime 291280009243618888211558641 := by
  refine lucas_primality 291280009243618888211558641 (17 : ZMod 291280009243618888211558641) ?_ (fun q hq hd => ?_)
  · rw [show 291280009243618888211558641 - 1 = 291280009243618888211558640 from by norm_num]
    reduce_mod_char
  · have e : 291280009243618888211558641 - 1 = [2 ^ 4, 3 ^ 1, 5 ^ 1, 23 ^ 1, 89 ^ 1, 353 ^ 1, 397 ^ 1, 683 ^ 1, 2113 ^ 1, 2931542417 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (291280009243618888211558641 - 1) / 2 = 145640004621809444105779320 from by norm_num]
      have h2 : (17 : ZMod 291280009243618888211558641) ^ 145640004621809444105779320 = ((291280009243618888211558640 : ℕ) : ZMod 291280009243618888211558641) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (291280009243618888211558641 - 1) / 3 = 97093336414539629403852880 from by norm_num]
      have h2 : (17 : ZMod 291280009243618888211558641) ^ 97093336414539629403852880 = ((196862240352772859638815643 : ℕ) : ZMod 291280009243618888211558641) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (291280009243618888211558641 - 1) / 5 = 58256001848723777642311728 from by norm_num]
      have h2 : (17 : ZMod 291280009243618888211558641) ^ 58256001848723777642311728 = ((226422760817323650608589186 : ℕ) : ZMod 291280009243618888211558641) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (291280009243618888211558641 - 1) / 23 = 12664348227983429922241680 from by norm_num]
      have h2 : (17 : ZMod 291280009243618888211558641) ^ 12664348227983429922241680 = ((1099511627776 : ℕ) : ZMod 291280009243618888211558641) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (291280009243618888211558641 - 1) / 89 = 3272809092624931328219760 from by norm_num]
      have h2 : (17 : ZMod 291280009243618888211558641) ^ 3272809092624931328219760 = ((244541012352108629298555847 : ℕ) : ZMod 291280009243618888211558641) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (291280009243618888211558641 - 1) / 353 = 825155833551328295216880 from by norm_num]
      have h2 : (17 : ZMod 291280009243618888211558641) ^ 825155833551328295216880 = ((122682591409445444172767863 : ℕ) : ZMod 291280009243618888211558641) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (291280009243618888211558641 - 1) / 397 = 733702794064531204563120 from by norm_num]
      have h2 : (17 : ZMod 291280009243618888211558641) ^ 733702794064531204563120 = ((102296552950312578359460701 : ℕ) : ZMod 291280009243618888211558641) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (291280009243618888211558641 - 1) / 683 = 426471463021403935888080 from by norm_num]
      have h2 : (17 : ZMod 291280009243618888211558641) ^ 426471463021403935888080 = ((203876141923365505088160050 : ℕ) : ZMod 291280009243618888211558641) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (291280009243618888211558641 - 1) / 2113 = 137851400493903875159280 from by norm_num]
      have h2 : (17 : ZMod 291280009243618888211558641) ^ 137851400493903875159280 = ((106468545151370911547646210 : ℕ) : ZMod 291280009243618888211558641) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_2931542417).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (291280009243618888211558641 - 1) / 2931542417 = 99360666778855920 from by norm_num]
      have h2 : (17 : ZMod 291280009243618888211558641) ^ 99360666778855920 = ((205488228518351039590322151 : ℕ) : ZMod 291280009243618888211558641) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_97591777 : Nat.Prime 97591777 := by
  refine lucas_primality 97591777 (7 : ZMod 97591777) ?_ (fun q hq hd => ?_)
  · rw [show 97591777 - 1 = 97591776 from by norm_num]
    reduce_mod_char
  · have e : 97591777 - 1 = [2 ^ 5, 3 ^ 1, 1016581 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (97591777 - 1) / 2 = 48795888 from by norm_num]
      have h2 : (7 : ZMod 97591777) ^ 48795888 = ((97591776 : ℕ) : ZMod 97591777) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (97591777 - 1) / 3 = 32530592 from by norm_num]
      have h2 : (7 : ZMod 97591777) ^ 32530592 = ((68362468 : ℕ) : ZMod 97591777) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (97591777 - 1) / 1016581 = 96 from by norm_num]
      have h2 : (7 : ZMod 97591777) ^ 96 = ((34396951 : ℕ) : ZMod 97591777) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_48795889 : Nat.Prime 48795889 := by
  refine lucas_primality 48795889 (17 : ZMod 48795889) ?_ (fun q hq hd => ?_)
  · rw [show 48795889 - 1 = 48795888 from by norm_num]
    reduce_mod_char
  · have e : 48795889 - 1 = [2 ^ 4, 3 ^ 1, 1016581 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (48795889 - 1) / 2 = 24397944 from by norm_num]
      have h2 : (17 : ZMod 48795889) ^ 24397944 = ((48795888 : ℕ) : ZMod 48795889) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (48795889 - 1) / 3 = 16265296 from by norm_num]
      have h2 : (17 : ZMod 48795889) ^ 16265296 = ((35160361 : ℕ) : ZMod 48795889) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (48795889 - 1) / 1016581 = 48 from by norm_num]
      have h2 : (17 : ZMod 48795889) ^ 48 = ((16064391 : ℕ) : ZMod 48795889) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_845100400152152934331135470251 : Nat.Prime 845100400152152934331135470251 := by
  refine lucas_primality 845100400152152934331135470251 (6 : ZMod 845100400152152934331135470251) ?_ (fun q hq hd => ?_)
  · rw [show 845100400152152934331135470251 - 1 = 845100400152152934331135470250 from by norm_num]
    reduce_mod_char
  · have e : 845100400152152934331135470251 - 1 = [2 ^ 1, 5 ^ 3, 11 ^ 1, 31 ^ 1, 41 ^ 1, 101 ^ 1, 251 ^ 1, 601 ^ 1, 1801 ^ 1, 4051 ^ 1, 8101 ^ 1, 268501 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (845100400152152934331135470251 - 1) / 2 = 422550200076076467165567735125 from by norm_num]
      have h2 : (6 : ZMod 845100400152152934331135470251) ^ 422550200076076467165567735125 = ((845100400152152934331135470250 : ℕ) : ZMod 845100400152152934331135470251) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (845100400152152934331135470251 - 1) / 5 = 169020080030430586866227094050 from by norm_num]
      have h2 : (6 : ZMod 845100400152152934331135470251) ^ 169020080030430586866227094050 = ((262235513280179507202218746463 : ℕ) : ZMod 845100400152152934331135470251) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (845100400152152934331135470251 - 1) / 11 = 76827309104741175848285042750 from by norm_num]
      have h2 : (6 : ZMod 845100400152152934331135470251) ^ 76827309104741175848285042750 = ((643575463884633856536890059931 : ℕ) : ZMod 845100400152152934331135470251) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (845100400152152934331135470251 - 1) / 31 = 27261303230714610784875337750 from by norm_num]
      have h2 : (6 : ZMod 845100400152152934331135470251) ^ 27261303230714610784875337750 = ((397238571030998904916109490708 : ℕ) : ZMod 845100400152152934331135470251) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (845100400152152934331135470251 - 1) / 41 = 20612204881759827666613060250 from by norm_num]
      have h2 : (6 : ZMod 845100400152152934331135470251) ^ 20612204881759827666613060250 = ((378774382257504293065163714098 : ℕ) : ZMod 845100400152152934331135470251) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (845100400152152934331135470251 - 1) / 101 = 8367330694575771627040945250 from by norm_num]
      have h2 : (6 : ZMod 845100400152152934331135470251) ^ 8367330694575771627040945250 = ((845100400152152934331101915819 : ℕ) : ZMod 845100400152152934331135470251) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (845100400152152934331135470251 - 1) / 251 = 3366933865148019658689782750 from by norm_num]
      have h2 : (6 : ZMod 845100400152152934331135470251) ^ 3366933865148019658689782750 = ((486017372309480382572060270590 : ℕ) : ZMod 845100400152152934331135470251) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (845100400152152934331135470251 - 1) / 601 = 1406157071800587245143320250 from by norm_num]
      have h2 : (6 : ZMod 845100400152152934331135470251) ^ 1406157071800587245143320250 = ((329185655697627947999692254908 : ℕ) : ZMod 845100400152152934331135470251) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (845100400152152934331135470251 - 1) / 1801 = 469239533676931112899020250 from by norm_num]
      have h2 : (6 : ZMod 845100400152152934331135470251) ^ 469239533676931112899020250 = ((146795240610035330108268443054 : ℕ) : ZMod 845100400152152934331135470251) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (845100400152152934331135470251 - 1) / 4051 = 208615255530030346662832750 from by norm_num]
      have h2 : (6 : ZMod 845100400152152934331135470251) ^ 208615255530030346662832750 = ((301830993492707295756446867204 : ℕ) : ZMod 845100400152152934331135470251) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (845100400152152934331135470251 - 1) / 8101 = 104320503660307731678945250 from by norm_num]
      have h2 : (6 : ZMod 845100400152152934331135470251) ^ 104320503660307731678945250 = ((645687928776479073429150328768 : ℕ) : ZMod 845100400152152934331135470251) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (845100400152152934331135470251 - 1) / 268501 = 3147475801401681685845250 from by norm_num]
      have h2 : (6 : ZMod 845100400152152934331135470251) ^ 3147475801401681685845250 = ((592269414167863919831068676721 : ℕ) : ZMod 845100400152152934331135470251) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_19616871237013 : Nat.Prime 19616871237013 := by
  refine lucas_primality 19616871237013 (2 : ZMod 19616871237013) ?_ (fun q hq hd => ?_)
  · rw [show 19616871237013 - 1 = 19616871237012 from by norm_num]
    reduce_mod_char
  · have e : 19616871237013 - 1 = [2 ^ 2, 3 ^ 3, 7 ^ 1, 1217 ^ 1, 21321481 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19616871237013 - 1) / 2 = 9808435618506 from by norm_num]
      have h2 : (2 : ZMod 19616871237013) ^ 9808435618506 = ((19616871237012 : ℕ) : ZMod 19616871237013) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19616871237013 - 1) / 3 = 6538957079004 from by norm_num]
      have h2 : (2 : ZMod 19616871237013) ^ 6538957079004 = ((14694400646156 : ℕ) : ZMod 19616871237013) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19616871237013 - 1) / 7 = 2802410176716 from by norm_num]
      have h2 : (2 : ZMod 19616871237013) ^ 2802410176716 = ((16893456537515 : ℕ) : ZMod 19616871237013) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19616871237013 - 1) / 1217 = 16119039636 from by norm_num]
      have h2 : (2 : ZMod 19616871237013) ^ 16119039636 = ((13250485890143 : ℕ) : ZMod 19616871237013) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19616871237013 - 1) / 21321481 = 920052 from by norm_num]
      have h2 : (2 : ZMod 19616871237013) ^ 920052 = ((3801259099541 : ℕ) : ZMod 19616871237013) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_8142767081771726171 : Nat.Prime 8142767081771726171 := by
  refine lucas_primality 8142767081771726171 (6 : ZMod 8142767081771726171) ?_ (fun q hq hd => ?_)
  · rw [show 8142767081771726171 - 1 = 8142767081771726170 from by norm_num]
    reduce_mod_char
  · have e : 8142767081771726171 - 1 = [2 ^ 1, 5 ^ 1, 13 ^ 1, 31 ^ 1, 103 ^ 1, 19616871237013 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8142767081771726171 - 1) / 2 = 4071383540885863085 from by norm_num]
      have h2 : (6 : ZMod 8142767081771726171) ^ 4071383540885863085 = ((8142767081771726170 : ℕ) : ZMod 8142767081771726171) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8142767081771726171 - 1) / 5 = 1628553416354345234 from by norm_num]
      have h2 : (6 : ZMod 8142767081771726171) ^ 1628553416354345234 = ((1161840165056618686 : ℕ) : ZMod 8142767081771726171) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8142767081771726171 - 1) / 13 = 626366698597825090 from by norm_num]
      have h2 : (6 : ZMod 8142767081771726171) ^ 626366698597825090 = ((356824796340725650 : ℕ) : ZMod 8142767081771726171) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8142767081771726171 - 1) / 31 = 262669905863604070 from by norm_num]
      have h2 : (6 : ZMod 8142767081771726171) ^ 262669905863604070 = ((6182947312878445319 : ℕ) : ZMod 8142767081771726171) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8142767081771726171 - 1) / 103 = 79055991085162390 from by norm_num]
      have h2 : (6 : ZMod 8142767081771726171) ^ 79055991085162390 = ((64 : ℕ) : ZMod 8142767081771726171) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_19616871237013).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8142767081771726171 - 1) / 19616871237013 = 415090 from by norm_num]
      have h2 : (6 : ZMod 8142767081771726171) ^ 415090 = ((874678119364056690 : ℕ) : ZMod 8142767081771726171) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_78919881726271091143763623681 : Nat.Prime 78919881726271091143763623681 := by
  refine lucas_primality 78919881726271091143763623681 (47 : ZMod 78919881726271091143763623681) ?_ (fun q hq hd => ?_)
  · rw [show 78919881726271091143763623681 - 1 = 78919881726271091143763623680 from by norm_num]
    reduce_mod_char
  · have e : 78919881726271091143763623681 - 1 = [2 ^ 8, 3 ^ 2, 5 ^ 1, 7 ^ 1, 13 ^ 1, 17 ^ 1, 97 ^ 1, 193 ^ 1, 241 ^ 1, 673 ^ 1, 65537 ^ 1, 22253377 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (78919881726271091143763623681 - 1) / 2 = 39459940863135545571881811840 from by norm_num]
      have h2 : (47 : ZMod 78919881726271091143763623681) ^ 39459940863135545571881811840 = ((78919881726271091143763623680 : ℕ) : ZMod 78919881726271091143763623681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (78919881726271091143763623681 - 1) / 3 = 26306627242090363714587874560 from by norm_num]
      have h2 : (47 : ZMod 78919881726271091143763623681) ^ 26306627242090363714587874560 = ((8214642464917845850339246354 : ℕ) : ZMod 78919881726271091143763623681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (78919881726271091143763623681 - 1) / 5 = 15783976345254218228752724736 from by norm_num]
      have h2 : (47 : ZMod 78919881726271091143763623681) ^ 15783976345254218228752724736 = ((31854139748206241317368478197 : ℕ) : ZMod 78919881726271091143763623681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (78919881726271091143763623681 - 1) / 7 = 11274268818038727306251946240 from by norm_num]
      have h2 : (47 : ZMod 78919881726271091143763623681) ^ 11274268818038727306251946240 = ((21302793566101981363153694503 : ℕ) : ZMod 78919881726271091143763623681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (78919881726271091143763623681 - 1) / 13 = 6070760132790083934135663360 from by norm_num]
      have h2 : (47 : ZMod 78919881726271091143763623681) ^ 6070760132790083934135663360 = ((78919881726271090044251995905 : ℕ) : ZMod 78919881726271091143763623681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (78919881726271091143763623681 - 1) / 17 = 4642345983898299479044919040 from by norm_num]
      have h2 : (47 : ZMod 78919881726271091143763623681) ^ 4642345983898299479044919040 = ((39535619060177055188489950195 : ℕ) : ZMod 78919881726271091143763623681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (78919881726271091143763623681 - 1) / 97 = 813607028105887537564573440 from by norm_num]
      have h2 : (47 : ZMod 78919881726271091143763623681) ^ 813607028105887537564573440 = ((51697113434694986693332778386 : ℕ) : ZMod 78919881726271091143763623681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (78919881726271091143763623681 - 1) / 193 = 408911304281197363439189760 from by norm_num]
      have h2 : (47 : ZMod 78919881726271091143763623681) ^ 408911304281197363439189760 = ((48743744806705915190953386915 : ℕ) : ZMod 78919881726271091143763623681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (78919881726271091143763623681 - 1) / 241 = 327468388905689174870388480 from by norm_num]
      have h2 : (47 : ZMod 78919881726271091143763623681) ^ 327468388905689174870388480 = ((76946074205182011108173878933 : ℕ) : ZMod 78919881726271091143763623681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (78919881726271091143763623681 - 1) / 673 = 117265797513032824879292160 from by norm_num]
      have h2 : (47 : ZMod 78919881726271091143763623681) ^ 117265797513032824879292160 = ((39595816621489989450750861552 : ℕ) : ZMod 78919881726271091143763623681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (78919881726271091143763623681 - 1) / 65537 = 1204203453412134994640640 from by norm_num]
      have h2 : (47 : ZMod 78919881726271091143763623681) ^ 1204203453412134994640640 = ((62084221376730397287934025095 : ℕ) : ZMod 78919881726271091143763623681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (78919881726271091143763623681 - 1) / 22253377 = 3546422717157539331840 from by norm_num]
      have h2 : (47 : ZMod 78919881726271091143763623681) ^ 3546422717157539331840 = ((28547152273361814519905640550 : ℕ) : ZMod 78919881726271091143763623681) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_39459940863135545571881811841 : Nat.Prime 39459940863135545571881811841 := by
  refine lucas_primality 39459940863135545571881811841 (23 : ZMod 39459940863135545571881811841) ?_ (fun q hq hd => ?_)
  · rw [show 39459940863135545571881811841 - 1 = 39459940863135545571881811840 from by norm_num]
    reduce_mod_char
  · have e : 39459940863135545571881811841 - 1 = [2 ^ 7, 3 ^ 2, 5 ^ 1, 7 ^ 1, 13 ^ 1, 17 ^ 1, 97 ^ 1, 193 ^ 1, 241 ^ 1, 673 ^ 1, 65537 ^ 1, 22253377 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (39459940863135545571881811841 - 1) / 2 = 19729970431567772785940905920 from by norm_num]
      have h2 : (23 : ZMod 39459940863135545571881811841) ^ 19729970431567772785940905920 = ((39459940863135545571881811840 : ℕ) : ZMod 39459940863135545571881811841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (39459940863135545571881811841 - 1) / 3 = 13153313621045181857293937280 from by norm_num]
      have h2 : (23 : ZMod 39459940863135545571881811841) ^ 13153313621045181857293937280 = ((39217345858976652508074178636 : ℕ) : ZMod 39459940863135545571881811841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (39459940863135545571881811841 - 1) / 5 = 7891988172627109114376362368 from by norm_num]
      have h2 : (23 : ZMod 39459940863135545571881811841) ^ 7891988172627109114376362368 = ((20380168119287385906301143989 : ℕ) : ZMod 39459940863135545571881811841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (39459940863135545571881811841 - 1) / 7 = 5637134409019363653125973120 from by norm_num]
      have h2 : (23 : ZMod 39459940863135545571881811841) ^ 5637134409019363653125973120 = ((13380944174232866041095229720 : ℕ) : ZMod 39459940863135545571881811841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (39459940863135545571881811841 - 1) / 13 = 3035380066395041967067831680 from by norm_num]
      have h2 : (23 : ZMod 39459940863135545571881811841) ^ 3035380066395041967067831680 = ((24745956665057359303134273624 : ℕ) : ZMod 39459940863135545571881811841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (39459940863135545571881811841 - 1) / 17 = 2321172991949149739522459520 from by norm_num]
      have h2 : (23 : ZMod 39459940863135545571881811841) ^ 2321172991949149739522459520 = ((9184356594572997438725056611 : ℕ) : ZMod 39459940863135545571881811841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (39459940863135545571881811841 - 1) / 97 = 406803514052943768782286720 from by norm_num]
      have h2 : (23 : ZMod 39459940863135545571881811841) ^ 406803514052943768782286720 = ((4114705258024739740005425002 : ℕ) : ZMod 39459940863135545571881811841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (39459940863135545571881811841 - 1) / 193 = 204455652140598681719594880 from by norm_num]
      have h2 : (23 : ZMod 39459940863135545571881811841) ^ 204455652140598681719594880 = ((15666056825064694354548227679 : ℕ) : ZMod 39459940863135545571881811841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (39459940863135545571881811841 - 1) / 241 = 163734194452844587435194240 from by norm_num]
      have h2 : (23 : ZMod 39459940863135545571881811841) ^ 163734194452844587435194240 = ((14089849546075145621943352980 : ℕ) : ZMod 39459940863135545571881811841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (39459940863135545571881811841 - 1) / 673 = 58632898756516412439646080 from by norm_num]
      have h2 : (23 : ZMod 39459940863135545571881811841) ^ 58632898756516412439646080 = ((8813390274325502539643483010 : ℕ) : ZMod 39459940863135545571881811841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (39459940863135545571881811841 - 1) / 65537 = 602101726706067497320320 from by norm_num]
      have h2 : (23 : ZMod 39459940863135545571881811841) ^ 602101726706067497320320 = ((7728550258037527879866018562 : ℕ) : ZMod 39459940863135545571881811841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (39459940863135545571881811841 - 1) / 22253377 = 1773211358578769665920 from by norm_num]
      have h2 : (23 : ZMod 39459940863135545571881811841) ^ 1773211358578769665920 = ((2059565084969888498130179539 : ℕ) : ZMod 39459940863135545571881811841) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_19729970431567772785940905921 : Nat.Prime 19729970431567772785940905921 := by
  refine lucas_primality 19729970431567772785940905921 (22 : ZMod 19729970431567772785940905921) ?_ (fun q hq hd => ?_)
  · rw [show 19729970431567772785940905921 - 1 = 19729970431567772785940905920 from by norm_num]
    reduce_mod_char
  · have e : 19729970431567772785940905921 - 1 = [2 ^ 6, 3 ^ 2, 5 ^ 1, 7 ^ 1, 13 ^ 1, 17 ^ 1, 97 ^ 1, 193 ^ 1, 241 ^ 1, 673 ^ 1, 65537 ^ 1, 22253377 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19729970431567772785940905921 - 1) / 2 = 9864985215783886392970452960 from by norm_num]
      have h2 : (22 : ZMod 19729970431567772785940905921) ^ 9864985215783886392970452960 = ((19729970431567772785940905920 : ℕ) : ZMod 19729970431567772785940905921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19729970431567772785940905921 - 1) / 3 = 6576656810522590928646968640 from by norm_num]
      have h2 : (22 : ZMod 19729970431567772785940905921) ^ 6576656810522590928646968640 = ((9622386831297383732792173527 : ℕ) : ZMod 19729970431567772785940905921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19729970431567772785940905921 - 1) / 5 = 3945994086313554557188181184 from by norm_num]
      have h2 : (22 : ZMod 19729970431567772785940905921) ^ 3945994086313554557188181184 = ((6913475373460510520722007056 : ℕ) : ZMod 19729970431567772785940905921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19729970431567772785940905921 - 1) / 7 = 2818567204509681826562986560 from by norm_num]
      have h2 : (22 : ZMod 19729970431567772785940905921) ^ 2818567204509681826562986560 = ((14292593964574779767895659196 : ℕ) : ZMod 19729970431567772785940905921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19729970431567772785940905921 - 1) / 13 = 1517690033197520983533915840 from by norm_num]
      have h2 : (22 : ZMod 19729970431567772785940905921) ^ 1517690033197520983533915840 = ((9431147359863237225918603695 : ℕ) : ZMod 19729970431567772785940905921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19729970431567772785940905921 - 1) / 17 = 1160586495974574869761229760 from by norm_num]
      have h2 : (22 : ZMod 19729970431567772785940905921) ^ 1160586495974574869761229760 = ((15914327967838321037169770649 : ℕ) : ZMod 19729970431567772785940905921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19729970431567772785940905921 - 1) / 97 = 203401757026471884391143360 from by norm_num]
      have h2 : (22 : ZMod 19729970431567772785940905921) ^ 203401757026471884391143360 = ((15619466099747315215999803101 : ℕ) : ZMod 19729970431567772785940905921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19729970431567772785940905921 - 1) / 193 = 102227826070299340859797440 from by norm_num]
      have h2 : (22 : ZMod 19729970431567772785940905921) ^ 102227826070299340859797440 = ((17324429200036549644466141513 : ℕ) : ZMod 19729970431567772785940905921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19729970431567772785940905921 - 1) / 241 = 81867097226422293717597120 from by norm_num]
      have h2 : (22 : ZMod 19729970431567772785940905921) ^ 81867097226422293717597120 = ((2285300649970218387238211418 : ℕ) : ZMod 19729970431567772785940905921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19729970431567772785940905921 - 1) / 673 = 29316449378258206219823040 from by norm_num]
      have h2 : (22 : ZMod 19729970431567772785940905921) ^ 29316449378258206219823040 = ((15657842976115509111525984398 : ℕ) : ZMod 19729970431567772785940905921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19729970431567772785940905921 - 1) / 65537 = 301050863353033748660160 from by norm_num]
      have h2 : (22 : ZMod 19729970431567772785940905921) ^ 301050863353033748660160 = ((18678769332342394453315266862 : ℕ) : ZMod 19729970431567772785940905921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (19729970431567772785940905921 - 1) / 22253377 = 886605679289384832960 from by norm_num]
      have h2 : (22 : ZMod 19729970431567772785940905921) ^ 886605679289384832960 = ((5159055463131104032371628220 : ℕ) : ZMod 19729970431567772785940905921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_9864985215783886392970452961 : Nat.Prime 9864985215783886392970452961 := by
  refine lucas_primality 9864985215783886392970452961 (22 : ZMod 9864985215783886392970452961) ?_ (fun q hq hd => ?_)
  · rw [show 9864985215783886392970452961 - 1 = 9864985215783886392970452960 from by norm_num]
    reduce_mod_char
  · have e : 9864985215783886392970452961 - 1 = [2 ^ 5, 3 ^ 2, 5 ^ 1, 7 ^ 1, 13 ^ 1, 17 ^ 1, 97 ^ 1, 193 ^ 1, 241 ^ 1, 673 ^ 1, 65537 ^ 1, 22253377 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9864985215783886392970452961 - 1) / 2 = 4932492607891943196485226480 from by norm_num]
      have h2 : (22 : ZMod 9864985215783886392970452961) ^ 4932492607891943196485226480 = ((9864985215783886392970452960 : ℕ) : ZMod 9864985215783886392970452961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9864985215783886392970452961 - 1) / 3 = 3288328405261295464323484320 from by norm_num]
      have h2 : (22 : ZMod 9864985215783886392970452961) ^ 3288328405261295464323484320 = ((1370950800923509901867947876 : ℕ) : ZMod 9864985215783886392970452961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9864985215783886392970452961 - 1) / 5 = 1972997043156777278594090592 from by norm_num]
      have h2 : (22 : ZMod 9864985215783886392970452961) ^ 1972997043156777278594090592 = ((2306205942038158337588354256 : ℕ) : ZMod 9864985215783886392970452961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9864985215783886392970452961 - 1) / 7 = 1409283602254840913281493280 from by norm_num]
      have h2 : (22 : ZMod 9864985215783886392970452961) ^ 1409283602254840913281493280 = ((6694988963205026561048928318 : ℕ) : ZMod 9864985215783886392970452961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9864985215783886392970452961 - 1) / 13 = 758845016598760491766957920 from by norm_num]
      have h2 : (22 : ZMod 9864985215783886392970452961) ^ 758845016598760491766957920 = ((189032893469805174127725152 : ℕ) : ZMod 9864985215783886392970452961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9864985215783886392970452961 - 1) / 17 = 580293247987287434880614880 from by norm_num]
      have h2 : (22 : ZMod 9864985215783886392970452961) ^ 580293247987287434880614880 = ((534236587989126161303339127 : ℕ) : ZMod 9864985215783886392970452961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9864985215783886392970452961 - 1) / 97 = 101700878513235942195571680 from by norm_num]
      have h2 : (22 : ZMod 9864985215783886392970452961) ^ 101700878513235942195571680 = ((9465594342738468873431350388 : ℕ) : ZMod 9864985215783886392970452961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9864985215783886392970452961 - 1) / 193 = 51113913035149670429898720 from by norm_num]
      have h2 : (22 : ZMod 9864985215783886392970452961) ^ 51113913035149670429898720 = ((9596057805721895791066337269 : ℕ) : ZMod 9864985215783886392970452961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9864985215783886392970452961 - 1) / 241 = 40933548613211146858798560 from by norm_num]
      have h2 : (22 : ZMod 9864985215783886392970452961) ^ 40933548613211146858798560 = ((8621503188500762433696094400 : ℕ) : ZMod 9864985215783886392970452961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9864985215783886392970452961 - 1) / 673 = 14658224689129103109911520 from by norm_num]
      have h2 : (22 : ZMod 9864985215783886392970452961) ^ 14658224689129103109911520 = ((2426402769772901353903747413 : ℕ) : ZMod 9864985215783886392970452961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9864985215783886392970452961 - 1) / 65537 = 150525431676516874330080 from by norm_num]
      have h2 : (22 : ZMod 9864985215783886392970452961) ^ 150525431676516874330080 = ((9630190872468189644976636103 : ℕ) : ZMod 9864985215783886392970452961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (9864985215783886392970452961 - 1) / 22253377 = 443302839644692416480 from by norm_num]
      have h2 : (22 : ZMod 9864985215783886392970452961) ^ 443302839644692416480 = ((6963457736354780959136908660 : ℕ) : ZMod 9864985215783886392970452961) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2015036747 : Nat.Prime 2015036747 := by
  refine lucas_primality 2015036747 (2 : ZMod 2015036747) ?_ (fun q hq hd => ?_)
  · rw [show 2015036747 - 1 = 2015036746 from by norm_num]
    reduce_mod_char
  · have e : 2015036747 - 1 = [2 ^ 1, 1499 ^ 1, 672127 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2015036747 - 1) / 2 = 1007518373 from by norm_num]
      have h2 : (2 : ZMod 2015036747) ^ 1007518373 = ((2015036746 : ℕ) : ZMod 2015036747) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2015036747 - 1) / 1499 = 1344254 from by norm_num]
      have h2 : (2 : ZMod 2015036747) ^ 1344254 = ((1051705440 : ℕ) : ZMod 2015036747) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2015036747 - 1) / 672127 = 2998 from by norm_num]
      have h2 : (2 : ZMod 2015036747) ^ 2998 = ((375711850 : ℕ) : ZMod 2015036747) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3930642404161115957412877 : Nat.Prime 3930642404161115957412877 := by
  refine lucas_primality 3930642404161115957412877 (5 : ZMod 3930642404161115957412877) ?_ (fun q hq hd => ?_)
  · rw [show 3930642404161115957412877 - 1 = 3930642404161115957412876 from by norm_num]
    reduce_mod_char
  · have e : 3930642404161115957412877 - 1 = [2 ^ 2, 3 ^ 2, 71 ^ 1, 747619 ^ 1, 1020797 ^ 1, 2015036747 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3930642404161115957412877 - 1) / 2 = 1965321202080557978706438 from by norm_num]
      have h2 : (5 : ZMod 3930642404161115957412877) ^ 1965321202080557978706438 = ((3930642404161115957412876 : ℕ) : ZMod 3930642404161115957412877) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3930642404161115957412877 - 1) / 3 = 1310214134720371985804292 from by norm_num]
      have h2 : (5 : ZMod 3930642404161115957412877) ^ 1310214134720371985804292 = ((439116418162607589718757 : ℕ) : ZMod 3930642404161115957412877) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3930642404161115957412877 - 1) / 71 = 55361160621987548695956 from by norm_num]
      have h2 : (5 : ZMod 3930642404161115957412877) ^ 55361160621987548695956 = ((1812583854303226300124395 : ℕ) : ZMod 3930642404161115957412877) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3930642404161115957412877 - 1) / 747619 = 5257547499677129604 from by norm_num]
      have h2 : (5 : ZMod 3930642404161115957412877) ^ 5257547499677129604 = ((2339603836036992424799058 : ℕ) : ZMod 3930642404161115957412877) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3930642404161115957412877 - 1) / 1020797 = 3850562260822784508 from by norm_num]
      have h2 : (5 : ZMod 3930642404161115957412877) ^ 3850562260822784508 = ((2781576561478501305094400 : ℕ) : ZMod 3930642404161115957412877) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_2015036747).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3930642404161115957412877 - 1) / 2015036747 = 1950655445868708 from by norm_num]
      have h2 : (5 : ZMod 3930642404161115957412877) ^ 1950655445868708 = ((3152136657026076984855019 : ℕ) : ZMod 3930642404161115957412877) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_84115747449047881488635567801 : Nat.Prime 84115747449047881488635567801 := by
  refine lucas_primality 84115747449047881488635567801 (3 : ZMod 84115747449047881488635567801) ?_ (fun q hq hd => ?_)
  · rw [show 84115747449047881488635567801 - 1 = 84115747449047881488635567800 from by norm_num]
    reduce_mod_char
  · have e : 84115747449047881488635567801 - 1 = [2 ^ 3, 5 ^ 2, 107 ^ 1, 3930642404161115957412877 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (84115747449047881488635567801 - 1) / 2 = 42057873724523940744317783900 from by norm_num]
      have h2 : (3 : ZMod 84115747449047881488635567801) ^ 42057873724523940744317783900 = ((84115747449047881488635567800 : ℕ) : ZMod 84115747449047881488635567801) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (84115747449047881488635567801 - 1) / 5 = 16823149489809576297727113560 from by norm_num]
      have h2 : (3 : ZMod 84115747449047881488635567801) ^ 16823149489809576297727113560 = ((66705453820491592437102493489 : ℕ) : ZMod 84115747449047881488635567801) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (84115747449047881488635567801 - 1) / 107 = 786128480832223191482575400 from by norm_num]
      have h2 : (3 : ZMod 84115747449047881488635567801) ^ 786128480832223191482575400 = ((4722366482869645213696 : ℕ) : ZMod 84115747449047881488635567801) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_3930642404161115957412877).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (84115747449047881488635567801 - 1) / 3930642404161115957412877 = 21400 from by norm_num]
      have h2 : (3 : ZMod 84115747449047881488635567801) ^ 21400 = ((48611057662445443857658080481 : ℕ) : ZMod 84115747449047881488635567801) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_104124649 : Nat.Prime 104124649 := by
  refine lucas_primality 104124649 (7 : ZMod 104124649) ?_ (fun q hq hd => ?_)
  · rw [show 104124649 - 1 = 104124648 from by norm_num]
    reduce_mod_char
  · have e : 104124649 - 1 = [2 ^ 3, 3 ^ 1, 53 ^ 1, 109 ^ 1, 751 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (104124649 - 1) / 2 = 52062324 from by norm_num]
      have h2 : (7 : ZMod 104124649) ^ 52062324 = ((104124648 : ℕ) : ZMod 104124649) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (104124649 - 1) / 3 = 34708216 from by norm_num]
      have h2 : (7 : ZMod 104124649) ^ 34708216 = ((94708873 : ℕ) : ZMod 104124649) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (104124649 - 1) / 53 = 1964616 from by norm_num]
      have h2 : (7 : ZMod 104124649) ^ 1964616 = ((85293978 : ℕ) : ZMod 104124649) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (104124649 - 1) / 109 = 955272 from by norm_num]
      have h2 : (7 : ZMod 104124649) ^ 955272 = ((1024 : ℕ) : ZMod 104124649) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (104124649 - 1) / 751 = 138648 from by norm_num]
      have h2 : (7 : ZMod 104124649) ^ 138648 = ((57914564 : ℕ) : ZMod 104124649) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_636190001 : Nat.Prime 636190001 := by
  refine lucas_primality 636190001 (3 : ZMod 636190001) ?_ (fun q hq hd => ?_)
  · rw [show 636190001 - 1 = 636190000 from by norm_num]
    reduce_mod_char
  · have e : 636190001 - 1 = [2 ^ 4, 5 ^ 4, 113 ^ 1, 563 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (636190001 - 1) / 2 = 318095000 from by norm_num]
      have h2 : (3 : ZMod 636190001) ^ 318095000 = ((636190000 : ℕ) : ZMod 636190001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (636190001 - 1) / 5 = 127238000 from by norm_num]
      have h2 : (3 : ZMod 636190001) ^ 127238000 = ((188418694 : ℕ) : ZMod 636190001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (636190001 - 1) / 113 = 5630000 from by norm_num]
      have h2 : (3 : ZMod 636190001) ^ 5630000 = ((636181809 : ℕ) : ZMod 636190001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (636190001 - 1) / 563 = 1130000 from by norm_num]
      have h2 : (3 : ZMod 636190001) ^ 1130000 = ((25819350 : ℕ) : ZMod 636190001) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_77158673929 : Nat.Prime 77158673929 := by
  refine lucas_primality 77158673929 (11 : ZMod 77158673929) ?_ (fun q hq hd => ?_)
  · rw [show 77158673929 - 1 = 77158673928 from by norm_num]
    reduce_mod_char
  · have e : 77158673929 - 1 = [2 ^ 3, 3 ^ 3, 7 ^ 1, 73 ^ 1, 699053 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (77158673929 - 1) / 2 = 38579336964 from by norm_num]
      have h2 : (11 : ZMod 77158673929) ^ 38579336964 = ((77158673928 : ℕ) : ZMod 77158673929) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (77158673929 - 1) / 3 = 25719557976 from by norm_num]
      have h2 : (11 : ZMod 77158673929) ^ 25719557976 = ((2097151 : ℕ) : ZMod 77158673929) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (77158673929 - 1) / 7 = 11022667704 from by norm_num]
      have h2 : (11 : ZMod 77158673929) ^ 11022667704 = ((8589930496 : ℕ) : ZMod 77158673929) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (77158673929 - 1) / 73 = 1056968136 from by norm_num]
      have h2 : (11 : ZMod 77158673929) ^ 1056968136 = ((73884964140 : ℕ) : ZMod 77158673929) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (77158673929 - 1) / 699053 = 110376 from by norm_num]
      have h2 : (11 : ZMod 77158673929) ^ 110376 = ((43682531219 : ℕ) : ZMod 77158673929) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_56713727820156410577229101238628035243 : Nat.Prime 56713727820156410577229101238628035243 := by
  refine lucas_primality 56713727820156410577229101238628035243 (3 : ZMod 56713727820156410577229101238628035243) ?_ (fun q hq hd => ?_)
  · rw [show 56713727820156410577229101238628035243 - 1 = 56713727820156410577229101238628035242 from by norm_num]
    reduce_mod_char
  · have e : 56713727820156410577229101238628035243 - 1 = [2 ^ 1, 3 ^ 2, 7 ^ 2, 19 ^ 1, 43 ^ 1, 73 ^ 1, 127 ^ 1, 337 ^ 1, 5419 ^ 1, 92737 ^ 1, 649657 ^ 1, 77158673929 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56713727820156410577229101238628035243 - 1) / 2 = 28356863910078205288614550619314017621 from by norm_num]
      have h2 : (3 : ZMod 56713727820156410577229101238628035243) ^ 28356863910078205288614550619314017621 = ((56713727820156410577229101238628035242 : ℕ) : ZMod 56713727820156410577229101238628035243) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56713727820156410577229101238628035243 - 1) / 3 = 18904575940052136859076367079542678414 from by norm_num]
      have h2 : (3 : ZMod 56713727820156410577229101238628035243) ^ 18904575940052136859076367079542678414 = ((13898838222708156118891936879880683890 : ℕ) : ZMod 56713727820156410577229101238628035243) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56713727820156410577229101238628035243 - 1) / 7 = 8101961117165201511032728748375433606 from by norm_num]
      have h2 : (3 : ZMod 56713727820156410577229101238628035243) ^ 8101961117165201511032728748375433606 = ((22413134788282663057132454040641006030 : ℕ) : ZMod 56713727820156410577229101238628035243) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56713727820156410577229101238628035243 - 1) / 19 = 2984933043166126872485742170454107118 from by norm_num]
      have h2 : (3 : ZMod 56713727820156410577229101238628035243) ^ 2984933043166126872485742170454107118 = ((21686871186406268342679139743340261140 : ℕ) : ZMod 56713727820156410577229101238628035243) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56713727820156410577229101238628035243 - 1) / 43 = 1318923902794335129703002354386698494 from by norm_num]
      have h2 : (3 : ZMod 56713727820156410577229101238628035243) ^ 1318923902794335129703002354386698494 = ((48481389567981860097400250027525513468 : ℕ) : ZMod 56713727820156410577229101238628035243) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56713727820156410577229101238628035243 - 1) / 73 = 776900381098033021605878099159288154 from by norm_num]
      have h2 : (3 : ZMod 56713727820156410577229101238628035243) ^ 776900381098033021605878099159288154 = ((54360113558161921598803107142848346327 : ℕ) : ZMod 56713727820156410577229101238628035243) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56713727820156410577229101238628035243 - 1) / 127 = 446564785985483547852197647548252246 from by norm_num]
      have h2 : (3 : ZMod 56713727820156410577229101238628035243) ^ 446564785985483547852197647548252246 = ((1024 : ℕ) : ZMod 56713727820156410577229101238628035243) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56713727820156410577229101238628035243 - 1) / 337 = 168289993531621396371599706939549066 from by norm_num]
      have h2 : (3 : ZMod 56713727820156410577229101238628035243) ^ 168289993531621396371599706939549066 = ((16262741045374821133307621766389701814 : ℕ) : ZMod 56713727820156410577229101238628035243) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56713727820156410577229101238628035243 - 1) / 5419 = 10465718365040858198418361549848318 from by norm_num]
      have h2 : (3 : ZMod 56713727820156410577229101238628035243) ^ 10465718365040858198418361549848318 = ((47545762000174170391976693409797500763 : ℕ) : ZMod 56713727820156410577229101238628035243) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56713727820156410577229101238628035243 - 1) / 92737 = 611554480090540028006395518925866 from by norm_num]
      have h2 : (3 : ZMod 56713727820156410577229101238628035243) ^ 611554480090540028006395518925866 = ((25499935037649012188329682365827475352 : ℕ) : ZMod 56713727820156410577229101238628035243) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56713727820156410577229101238628035243 - 1) / 649657 = 87297955413635827178386596678906 from by norm_num]
      have h2 : (3 : ZMod 56713727820156410577229101238628035243) ^ 87297955413635827178386596678906 = ((31216958263131545345602498431503910922 : ℕ) : ZMod 56713727820156410577229101238628035243) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_77158673929).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (56713727820156410577229101238628035243 - 1) / 77158673929 = 735027248813831938623143898 from by norm_num]
      have h2 : (3 : ZMod 56713727820156410577229101238628035243) ^ 735027248813831938623143898 = ((4890363098866336102523420127418625199 : ℕ) : ZMod 56713727820156410577229101238628035243) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_18533742247 : Nat.Prime 18533742247 := by
  refine lucas_primality 18533742247 (6 : ZMod 18533742247) ?_ (fun q hq hd => ?_)
  · rw [show 18533742247 - 1 = 18533742246 from by norm_num]
    reduce_mod_char
  · have e : 18533742247 - 1 = [2 ^ 1, 3 ^ 3, 181 ^ 1, 1896229 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18533742247 - 1) / 2 = 9266871123 from by norm_num]
      have h2 : (6 : ZMod 18533742247) ^ 9266871123 = ((18533742246 : ℕ) : ZMod 18533742247) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18533742247 - 1) / 3 = 6177914082 from by norm_num]
      have h2 : (6 : ZMod 18533742247) ^ 6177914082 = ((17436423204 : ℕ) : ZMod 18533742247) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18533742247 - 1) / 181 = 102396366 from by norm_num]
      have h2 : (6 : ZMod 18533742247) ^ 102396366 = ((4318986892 : ℕ) : ZMod 18533742247) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18533742247 - 1) / 1896229 = 9774 from by norm_num]
      have h2 : (6 : ZMod 18533742247) ^ 9774 = ((16378712013 : ℕ) : ZMod 18533742247) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_116503103764643 : Nat.Prime 116503103764643 := by
  refine lucas_primality 116503103764643 (2 : ZMod 116503103764643) ?_ (fun q hq hd => ?_)
  · rw [show 116503103764643 - 1 = 116503103764642 from by norm_num]
    reduce_mod_char
  · have e : 116503103764643 - 1 = [2 ^ 1, 7 ^ 1, 449 ^ 1, 18533742247 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (116503103764643 - 1) / 2 = 58251551882321 from by norm_num]
      have h2 : (2 : ZMod 116503103764643) ^ 58251551882321 = ((116503103764642 : ℕ) : ZMod 116503103764643) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (116503103764643 - 1) / 7 = 16643300537806 from by norm_num]
      have h2 : (2 : ZMod 116503103764643) ^ 16643300537806 = ((10593569056013 : ℕ) : ZMod 116503103764643) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (116503103764643 - 1) / 449 = 259472391458 from by norm_num]
      have h2 : (2 : ZMod 116503103764643) ^ 259472391458 = ((12829831376547 : ℕ) : ZMod 116503103764643) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_18533742247).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (116503103764643 - 1) / 18533742247 = 6286 from by norm_num]
      have h2 : (2 : ZMod 116503103764643) ^ 6286 = ((65489195555553 : ℕ) : ZMod 116503103764643) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_59649589127497217 : Nat.Prime 59649589127497217 := by
  refine lucas_primality 59649589127497217 (3 : ZMod 59649589127497217) ?_ (fun q hq hd => ?_)
  · rw [show 59649589127497217 - 1 = 59649589127497216 from by norm_num]
    reduce_mod_char
  · have e : 59649589127497217 - 1 = [2 ^ 9, 116503103764643 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (59649589127497217 - 1) / 2 = 29824794563748608 from by norm_num]
      have h2 : (3 : ZMod 59649589127497217) ^ 29824794563748608 = ((59649589127497216 : ℕ) : ZMod 59649589127497217) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_116503103764643).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (59649589127497217 - 1) / 116503103764643 = 512 from by norm_num]
      have h2 : (3 : ZMod 59649589127497217) ^ 512 = ((20416608684428934 : ℕ) : ZMod 59649589127497217) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_13562889751591 : Nat.Prime 13562889751591 := by
  refine lucas_primality 13562889751591 (6 : ZMod 13562889751591) ?_ (fun q hq hd => ?_)
  · rw [show 13562889751591 - 1 = 13562889751590 from by norm_num]
    reduce_mod_char
  · have e : 13562889751591 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 1, 503 ^ 1, 15643 ^ 1, 57457 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13562889751591 - 1) / 2 = 6781444875795 from by norm_num]
      have h2 : (6 : ZMod 13562889751591) ^ 6781444875795 = ((13562889751590 : ℕ) : ZMod 13562889751591) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13562889751591 - 1) / 3 = 4520963250530 from by norm_num]
      have h2 : (6 : ZMod 13562889751591) ^ 4520963250530 = ((4765861943083 : ℕ) : ZMod 13562889751591) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13562889751591 - 1) / 5 = 2712577950318 from by norm_num]
      have h2 : (6 : ZMod 13562889751591) ^ 2712577950318 = ((601171651600 : ℕ) : ZMod 13562889751591) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13562889751591 - 1) / 503 = 26963995530 from by norm_num]
      have h2 : (6 : ZMod 13562889751591) ^ 26963995530 = ((1996861145169 : ℕ) : ZMod 13562889751591) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13562889751591 - 1) / 15643 = 867026130 from by norm_num]
      have h2 : (6 : ZMod 13562889751591) ^ 867026130 = ((1205480546483 : ℕ) : ZMod 13562889751591) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13562889751591 - 1) / 57457 = 236052870 from by norm_num]
      have h2 : (6 : ZMod 13562889751591) ^ 236052870 = ((2259943784594 : ℕ) : ZMod 13562889751591) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2368179743873 : Nat.Prime 2368179743873 := by
  refine lucas_primality 2368179743873 (3 : ZMod 2368179743873) ?_ (fun q hq hd => ?_)
  · rw [show 2368179743873 - 1 = 2368179743872 from by norm_num]
    reduce_mod_char
  · have e : 2368179743873 - 1 = [2 ^ 7, 17 ^ 1, 61 ^ 1, 2437 ^ 1, 7321 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2368179743873 - 1) / 2 = 1184089871936 from by norm_num]
      have h2 : (3 : ZMod 2368179743873) ^ 1184089871936 = ((2368179743872 : ℕ) : ZMod 2368179743873) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2368179743873 - 1) / 17 = 139304690816 from by norm_num]
      have h2 : (3 : ZMod 2368179743873) ^ 139304690816 = ((1193340574061 : ℕ) : ZMod 2368179743873) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2368179743873 - 1) / 61 = 38822618752 from by norm_num]
      have h2 : (3 : ZMod 2368179743873) ^ 38822618752 = ((785714625728 : ℕ) : ZMod 2368179743873) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2368179743873 - 1) / 2437 = 971760256 from by norm_num]
      have h2 : (3 : ZMod 2368179743873) ^ 971760256 = ((2248662558652 : ℕ) : ZMod 2368179743873) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2368179743873 - 1) / 7321 = 323477632 from by norm_num]
      have h2 : (3 : ZMod 2368179743873) ^ 323477632 = ((694132211396 : ℕ) : ZMod 2368179743873) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_487824887233 : Nat.Prime 487824887233 := by
  refine lucas_primality 487824887233 (5 : ZMod 487824887233) ?_ (fun q hq hd => ?_)
  · rw [show 487824887233 - 1 = 487824887232 from by norm_num]
    reduce_mod_char
  · have e : 487824887233 - 1 = [2 ^ 6, 3 ^ 5, 1091 ^ 1, 28751 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (487824887233 - 1) / 2 = 243912443616 from by norm_num]
      have h2 : (5 : ZMod 487824887233) ^ 243912443616 = ((487824887232 : ℕ) : ZMod 487824887233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (487824887233 - 1) / 3 = 162608295744 from by norm_num]
      have h2 : (5 : ZMod 487824887233) ^ 162608295744 = ((487808110017 : ℕ) : ZMod 487824887233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (487824887233 - 1) / 1091 = 447135552 from by norm_num]
      have h2 : (5 : ZMod 487824887233) ^ 447135552 = ((416102338830 : ℕ) : ZMod 487824887233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (487824887233 - 1) / 28751 = 16967232 from by norm_num]
      have h2 : (5 : ZMod 487824887233) ^ 16967232 = ((455985488374 : ℕ) : ZMod 487824887233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_20988936657440586486151264256610222593863921 : Nat.Prime 20988936657440586486151264256610222593863921 := by
  refine lucas_primality 20988936657440586486151264256610222593863921 (17 : ZMod 20988936657440586486151264256610222593863921) ?_ (fun q hq hd => ?_)
  · rw [show 20988936657440586486151264256610222593863921 - 1 = 20988936657440586486151264256610222593863920 from by norm_num]
    reduce_mod_char
  · have e : 20988936657440586486151264256610222593863921 - 1 = [2 ^ 4, 3 ^ 3, 5 ^ 1, 7 ^ 1, 13 ^ 1, 19 ^ 1, 37 ^ 1, 73 ^ 1, 97 ^ 1, 109 ^ 1, 241 ^ 1, 257 ^ 1, 433 ^ 1, 577 ^ 1, 673 ^ 1, 38737 ^ 1, 487824887233 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (20988936657440586486151264256610222593863921 - 1) / 2 = 10494468328720293243075632128305111296931960 from by norm_num]
      have h2 : (17 : ZMod 20988936657440586486151264256610222593863921) ^ 10494468328720293243075632128305111296931960 = ((20988936657440586486151264256610222593863920 : ℕ) : ZMod 20988936657440586486151264256610222593863921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (20988936657440586486151264256610222593863921 - 1) / 3 = 6996312219146862162050421418870074197954640 from by norm_num]
      have h2 : (17 : ZMod 20988936657440586486151264256610222593863921) ^ 6996312219146862162050421418870074197954640 = ((7920938469487222010241041770462202339453515 : ℕ) : ZMod 20988936657440586486151264256610222593863921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (20988936657440586486151264256610222593863921 - 1) / 5 = 4197787331488117297230252851322044518772784 from by norm_num]
      have h2 : (17 : ZMod 20988936657440586486151264256610222593863921) ^ 4197787331488117297230252851322044518772784 = ((14891142251128800403435317645829282867637391 : ℕ) : ZMod 20988936657440586486151264256610222593863921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (20988936657440586486151264256610222593863921 - 1) / 7 = 2998419522491512355164466322372888941980560 from by norm_num]
      have h2 : (17 : ZMod 20988936657440586486151264256610222593863921) ^ 2998419522491512355164466322372888941980560 = ((10997568074433174947756193752723073120083103 : ℕ) : ZMod 20988936657440586486151264256610222593863921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (20988936657440586486151264256610222593863921 - 1) / 13 = 1614533589033891268165481865893094045681840 from by norm_num]
      have h2 : (17 : ZMod 20988936657440586486151264256610222593863921) ^ 1614533589033891268165481865893094045681840 = ((13873559622079669176898401003754281559750131 : ℕ) : ZMod 20988936657440586486151264256610222593863921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (20988936657440586486151264256610222593863921 - 1) / 19 = 1104680876707399288744803381926853820729680 from by norm_num]
      have h2 : (17 : ZMod 20988936657440586486151264256610222593863921) ^ 1104680876707399288744803381926853820729680 = ((1442739611923739593329097228196359627367645 : ℕ) : ZMod 20988936657440586486151264256610222593863921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (20988936657440586486151264256610222593863921 - 1) / 37 = 567268558309205040166250385313789799834160 from by norm_num]
      have h2 : (17 : ZMod 20988936657440586486151264256610222593863921) ^ 567268558309205040166250385313789799834160 = ((281474976710656 : ℕ) : ZMod 20988936657440586486151264256610222593863921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (20988936657440586486151264256610222593863921 - 1) / 73 = 287519680238912143645907729542605788957040 from by norm_num]
      have h2 : (17 : ZMod 20988936657440586486151264256610222593863921) ^ 287519680238912143645907729542605788957040 = ((10965435924437416214585862318667021319422579 : ℕ) : ZMod 20988936657440586486151264256610222593863921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (20988936657440586486151264256610222593863921 - 1) / 97 = 216380790282892644187126435635156933957360 from by norm_num]
      have h2 : (17 : ZMod 20988936657440586486151264256610222593863921) ^ 216380790282892644187126435635156933957360 = ((16731003607909342756877052269575691584939931 : ℕ) : ZMod 20988936657440586486151264256610222593863921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (20988936657440586486151264256610222593863921 - 1) / 109 = 192559051903124646661938204189084610952880 from by norm_num]
      have h2 : (17 : ZMod 20988936657440586486151264256610222593863921) ^ 192559051903124646661938204189084610952880 = ((16105268146835462263504226839462064712776848 : ℕ) : ZMod 20988936657440586486151264256610222593863921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (20988936657440586486151264256610222593863921 - 1) / 241 = 87091023474857205336727237579295529435120 from by norm_num]
      have h2 : (17 : ZMod 20988936657440586486151264256610222593863921) ^ 87091023474857205336727237579295529435120 = ((13391138121565710102619447529507705871239320 : ℕ) : ZMod 20988936657440586486151264256610222593863921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (20988936657440586486151264256610222593863921 - 1) / 257 = 81669014231286328739888187768911371960560 from by norm_num]
      have h2 : (17 : ZMod 20988936657440586486151264256610222593863921) ^ 81669014231286328739888187768911371960560 = ((18838610500145205296884146894616480198225096 : ℕ) : ZMod 20988936657440586486151264256610222593863921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (20988936657440586486151264256610222593863921 - 1) / 433 = 48473294820878952623905922070693354720240 from by norm_num]
      have h2 : (17 : ZMod 20988936657440586486151264256610222593863921) ^ 48473294820878952623905922070693354720240 = ((11533324766679953745625232445835621367892113 : ℕ) : ZMod 20988936657440586486151264256610222593863921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (20988936657440586486151264256610222593863921 - 1) / 577 = 36375973409775713147575847931733488030960 from by norm_num]
      have h2 : (17 : ZMod 20988936657440586486151264256610222593863921) ^ 36375973409775713147575847931733488030960 = ((7648367024257701528395809381751652164763997 : ℕ) : ZMod 20988936657440586486151264256610222593863921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (20988936657440586486151264256610222593863921 - 1) / 673 = 31187127277029103248367406027652633869040 from by norm_num]
      have h2 : (17 : ZMod 20988936657440586486151264256610222593863921) ^ 31187127277029103248367406027652633869040 = ((12162322699511857256811179327299344583174534 : ℕ) : ZMod 20988936657440586486151264256610222593863921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (20988936657440586486151264256610222593863921 - 1) / 38737 = 541831754070800177766767283388239218160 from by norm_num]
      have h2 : (17 : ZMod 20988936657440586486151264256610222593863921) ^ 541831754070800177766767283388239218160 = ((16074248300848647125039438012333307408552295 : ℕ) : ZMod 20988936657440586486151264256610222593863921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_487824887233).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (20988936657440586486151264256610222593863921 - 1) / 487824887233 = 43025555289916219677412204416240 from by norm_num]
      have h2 : (17 : ZMod 20988936657440586486151264256610222593863921) ^ 43025555289916219677412204416240 = ((18241056990718302638725719682948784540200111 : ℕ) : ZMod 20988936657440586486151264256610222593863921) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_212480658612043 : Nat.Prime 212480658612043 := by
  refine lucas_primality 212480658612043 (5 : ZMod 212480658612043) ?_ (fun q hq hd => ?_)
  · rw [show 212480658612043 - 1 = 212480658612042 from by norm_num]
    reduce_mod_char
  · have e : 212480658612043 - 1 = [2 ^ 1, 3 ^ 1, 167 ^ 1, 443 ^ 1, 11197 ^ 1, 42751 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (212480658612043 - 1) / 2 = 106240329306021 from by norm_num]
      have h2 : (5 : ZMod 212480658612043) ^ 106240329306021 = ((212480658612042 : ℕ) : ZMod 212480658612043) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (212480658612043 - 1) / 3 = 70826886204014 from by norm_num]
      have h2 : (5 : ZMod 212480658612043) ^ 70826886204014 = ((55114146269250 : ℕ) : ZMod 212480658612043) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (212480658612043 - 1) / 167 = 1272339273126 from by norm_num]
      have h2 : (5 : ZMod 212480658612043) ^ 1272339273126 = ((119045787643629 : ℕ) : ZMod 212480658612043) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (212480658612043 - 1) / 443 = 479640312894 from by norm_num]
      have h2 : (5 : ZMod 212480658612043) ^ 479640312894 = ((5546413964721 : ℕ) : ZMod 212480658612043) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (212480658612043 - 1) / 11197 = 18976570386 from by norm_num]
      have h2 : (5 : ZMod 212480658612043) ^ 18976570386 = ((154413000536194 : ℕ) : ZMod 212480658612043) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (212480658612043 - 1) / 42751 = 4970191542 from by norm_num]
      have h2 : (5 : ZMod 212480658612043) ^ 4970191542 = ((60564608744440 : ℕ) : ZMod 212480658612043) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_18717738334417 : Nat.Prime 18717738334417 := by
  refine lucas_primality 18717738334417 (5 : ZMod 18717738334417) ?_ (fun q hq hd => ?_)
  · rw [show 18717738334417 - 1 = 18717738334416 from by norm_num]
    reduce_mod_char
  · have e : 18717738334417 - 1 = [2 ^ 4, 3 ^ 2, 11 ^ 1, 19 ^ 1, 23 ^ 1, 131 ^ 1, 151 ^ 1, 1367 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18717738334417 - 1) / 2 = 9358869167208 from by norm_num]
      have h2 : (5 : ZMod 18717738334417) ^ 9358869167208 = ((18717738334416 : ℕ) : ZMod 18717738334417) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18717738334417 - 1) / 3 = 6239246111472 from by norm_num]
      have h2 : (5 : ZMod 18717738334417) ^ 6239246111472 = ((1819224690458 : ℕ) : ZMod 18717738334417) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18717738334417 - 1) / 11 = 1701612575856 from by norm_num]
      have h2 : (5 : ZMod 18717738334417) ^ 1701612575856 = ((6892191680092 : ℕ) : ZMod 18717738334417) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18717738334417 - 1) / 19 = 985144122864 from by norm_num]
      have h2 : (5 : ZMod 18717738334417) ^ 985144122864 = ((12835695315599 : ℕ) : ZMod 18717738334417) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18717738334417 - 1) / 23 = 813814710192 from by norm_num]
      have h2 : (5 : ZMod 18717738334417) ^ 813814710192 = ((17914967141951 : ℕ) : ZMod 18717738334417) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18717738334417 - 1) / 131 = 142883498736 from by norm_num]
      have h2 : (5 : ZMod 18717738334417) ^ 142883498736 = ((12753705593516 : ℕ) : ZMod 18717738334417) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18717738334417 - 1) / 151 = 123958532016 from by norm_num]
      have h2 : (5 : ZMod 18717738334417) ^ 123958532016 = ((18493820077975 : ℕ) : ZMod 18717738334417) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (18717738334417 - 1) / 1367 = 13692566448 from by norm_num]
      have h2 : (5 : ZMod 18717738334417) ^ 13692566448 = ((11082255859751 : ℕ) : ZMod 18717738334417) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_604462909806215075725313 : Nat.Prime 604462909806215075725313 := by
  refine lucas_primality 604462909806215075725313 (3 : ZMod 604462909806215075725313) ?_ (fun q hq hd => ?_)
  · rw [show 604462909806215075725313 - 1 = 604462909806215075725312 from by norm_num]
    reduce_mod_char
  · have e : 604462909806215075725313 - 1 = [2 ^ 40, 7 ^ 1, 79 ^ 1, 8191 ^ 1, 121369 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (604462909806215075725313 - 1) / 2 = 302231454903107537862656 from by norm_num]
      have h2 : (3 : ZMod 604462909806215075725313) ^ 302231454903107537862656 = ((604462909806215075725312 : ℕ) : ZMod 604462909806215075725313) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (604462909806215075725313 - 1) / 7 = 86351844258030725103616 from by norm_num]
      have h2 : (3 : ZMod 604462909806215075725313) ^ 86351844258030725103616 = ((354530240461750714755047 : ℕ) : ZMod 604462909806215075725313) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (604462909806215075725313 - 1) / 79 = 7651429238053355388928 from by norm_num]
      have h2 : (3 : ZMod 604462909806215075725313) ^ 7651429238053355388928 = ((4294967296 : ℕ) : ZMod 604462909806215075725313) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (604462909806215075725313 - 1) / 8191 = 73795984593604575232 from by norm_num]
      have h2 : (3 : ZMod 604462909806215075725313) ^ 73795984593604575232 = ((391678817428242717096838 : ℕ) : ZMod 604462909806215075725313) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (604462909806215075725313 - 1) / 121369 = 4980373157941608448 from by norm_num]
      have h2 : (3 : ZMod 604462909806215075725313) ^ 4980373157941608448 = ((121344057661516551604919 : ℕ) : ZMod 604462909806215075725313) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3139258129883 : Nat.Prime 3139258129883 := by
  refine lucas_primality 3139258129883 (2 : ZMod 3139258129883) ?_ (fun q hq hd => ?_)
  · rw [show 3139258129883 - 1 = 3139258129882 from by norm_num]
    reduce_mod_char
  · have e : 3139258129883 - 1 = [2 ^ 1, 7 ^ 1, 2411 ^ 1, 3673 ^ 1, 25321 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3139258129883 - 1) / 2 = 1569629064941 from by norm_num]
      have h2 : (2 : ZMod 3139258129883) ^ 1569629064941 = ((3139258129882 : ℕ) : ZMod 3139258129883) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3139258129883 - 1) / 7 = 448465447126 from by norm_num]
      have h2 : (2 : ZMod 3139258129883) ^ 448465447126 = ((2065522733013 : ℕ) : ZMod 3139258129883) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3139258129883 - 1) / 2411 = 1302056462 from by norm_num]
      have h2 : (2 : ZMod 3139258129883) ^ 1302056462 = ((2208521256750 : ℕ) : ZMod 3139258129883) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3139258129883 - 1) / 3673 = 854685034 from by norm_num]
      have h2 : (2 : ZMod 3139258129883) ^ 854685034 = ((1095636135186 : ℕ) : ZMod 3139258129883) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3139258129883 - 1) / 25321 = 123978442 from by norm_num]
      have h2 : (2 : ZMod 3139258129883) ^ 123978442 = ((2464713005596 : ℕ) : ZMod 3139258129883) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1023398150341859 : Nat.Prime 1023398150341859 := by
  refine lucas_primality 1023398150341859 (6 : ZMod 1023398150341859) ?_ (fun q hq hd => ?_)
  · rw [show 1023398150341859 - 1 = 1023398150341858 from by norm_num]
    reduce_mod_char
  · have e : 1023398150341859 - 1 = [2 ^ 1, 163 ^ 1, 3139258129883 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1023398150341859 - 1) / 2 = 511699075170929 from by norm_num]
      have h2 : (6 : ZMod 1023398150341859) ^ 511699075170929 = ((1023398150341858 : ℕ) : ZMod 1023398150341859) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1023398150341859 - 1) / 163 = 6278516259766 from by norm_num]
      have h2 : (6 : ZMod 1023398150341859) ^ 6278516259766 = ((560643952889895 : ℕ) : ZMod 1023398150341859) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_3139258129883).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1023398150341859 - 1) / 3139258129883 = 326 from by norm_num]
      have h2 : (6 : ZMod 1023398150341859) ^ 326 = ((48210328145420 : ℕ) : ZMod 1023398150341859) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2812085643403 : Nat.Prime 2812085643403 := by
  refine lucas_primality 2812085643403 (3 : ZMod 2812085643403) ?_ (fun q hq hd => ?_)
  · rw [show 2812085643403 - 1 = 2812085643402 from by norm_num]
    reduce_mod_char
  · have e : 2812085643403 - 1 = [2 ^ 1, 3 ^ 3, 7 ^ 1, 379 ^ 1, 19628971 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2812085643403 - 1) / 2 = 1406042821701 from by norm_num]
      have h2 : (3 : ZMod 2812085643403) ^ 1406042821701 = ((2812085643402 : ℕ) : ZMod 2812085643403) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2812085643403 - 1) / 3 = 937361881134 from by norm_num]
      have h2 : (3 : ZMod 2812085643403) ^ 937361881134 = ((1861256251728 : ℕ) : ZMod 2812085643403) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2812085643403 - 1) / 7 = 401726520486 from by norm_num]
      have h2 : (3 : ZMod 2812085643403) ^ 401726520486 = ((2411702389629 : ℕ) : ZMod 2812085643403) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2812085643403 - 1) / 379 = 7419751038 from by norm_num]
      have h2 : (3 : ZMod 2812085643403) ^ 7419751038 = ((1756790367693 : ℕ) : ZMod 2812085643403) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2812085643403 - 1) / 19628971 = 143262 from by norm_num]
      have h2 : (3 : ZMod 2812085643403) ^ 143262 = ((2629013928282 : ℕ) : ZMod 2812085643403) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_11248342573613 : Nat.Prime 11248342573613 := by
  refine lucas_primality 11248342573613 (2 : ZMod 11248342573613) ?_ (fun q hq hd => ?_)
  · rw [show 11248342573613 - 1 = 11248342573612 from by norm_num]
    reduce_mod_char
  · have e : 11248342573613 - 1 = [2 ^ 2, 2812085643403 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11248342573613 - 1) / 2 = 5624171286806 from by norm_num]
      have h2 : (2 : ZMod 11248342573613) ^ 5624171286806 = ((11248342573612 : ℕ) : ZMod 11248342573613) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_2812085643403).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (11248342573613 - 1) / 2812085643403 = 4 from by norm_num]
      have h2 : (2 : ZMod 11248342573613) ^ 4 = ((16 : ℕ) : ZMod 11248342573613) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_57912614113275649087721 : Nat.Prime 57912614113275649087721 := by
  refine lucas_primality 57912614113275649087721 (6 : ZMod 57912614113275649087721) ?_ (fun q hq hd => ?_)
  · rw [show 57912614113275649087721 - 1 = 57912614113275649087720 from by norm_num]
    reduce_mod_char
  · have e : 57912614113275649087721 - 1 = [2 ^ 3, 5 ^ 1, 83 ^ 1, 383 ^ 1, 4049 ^ 1, 11248342573613 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (57912614113275649087721 - 1) / 2 = 28956307056637824543860 from by norm_num]
      have h2 : (6 : ZMod 57912614113275649087721) ^ 28956307056637824543860 = ((57912614113275649087720 : ℕ) : ZMod 57912614113275649087721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (57912614113275649087721 - 1) / 5 = 11582522822655129817544 from by norm_num]
      have h2 : (6 : ZMod 57912614113275649087721) ^ 11582522822655129817544 = ((2789656255697642251826 : ℕ) : ZMod 57912614113275649087721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (57912614113275649087721 - 1) / 83 = 697742338714164446840 from by norm_num]
      have h2 : (6 : ZMod 57912614113275649087721) ^ 697742338714164446840 = ((2048 : ℕ) : ZMod 57912614113275649087721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (57912614113275649087721 - 1) / 383 = 151207869747456002840 from by norm_num]
      have h2 : (6 : ZMod 57912614113275649087721) ^ 151207869747456002840 = ((13840262541632795827357 : ℕ) : ZMod 57912614113275649087721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (57912614113275649087721 - 1) / 4049 = 14302942482903346280 from by norm_num]
      have h2 : (6 : ZMod 57912614113275649087721) ^ 14302942482903346280 = ((49137993049991644527724 : ℕ) : ZMod 57912614113275649087721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_11248342573613).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (57912614113275649087721 - 1) / 11248342573613 = 5148546440 from by norm_num]
      have h2 : (6 : ZMod 57912614113275649087721) ^ 5148546440 = ((12190088266157509011350 : ℕ) : ZMod 57912614113275649087721) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_13455809771 : Nat.Prime 13455809771 := by
  refine lucas_primality 13455809771 (6 : ZMod 13455809771) ?_ (fun q hq hd => ?_)
  · rw [show 13455809771 - 1 = 13455809770 from by norm_num]
    reduce_mod_char
  · have e : 13455809771 - 1 = [2 ^ 1, 5 ^ 1, 13 ^ 1, 83 ^ 1, 1247063 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13455809771 - 1) / 2 = 6727904885 from by norm_num]
      have h2 : (6 : ZMod 13455809771) ^ 6727904885 = ((13455809770 : ℕ) : ZMod 13455809771) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13455809771 - 1) / 5 = 2691161954 from by norm_num]
      have h2 : (6 : ZMod 13455809771) ^ 2691161954 = ((1965912534 : ℕ) : ZMod 13455809771) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13455809771 - 1) / 13 = 1035062290 from by norm_num]
      have h2 : (6 : ZMod 13455809771) ^ 1035062290 = ((3658939577 : ℕ) : ZMod 13455809771) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13455809771 - 1) / 83 = 162118190 from by norm_num]
      have h2 : (6 : ZMod 13455809771) ^ 162118190 = ((1932386723 : ℕ) : ZMod 13455809771) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (13455809771 - 1) / 1247063 = 10790 from by norm_num]
      have h2 : (6 : ZMod 13455809771) ^ 10790 = ((2765812487 : ℕ) : ZMod 13455809771) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_62357403192785191176690552862561408838653121833643 : Nat.Prime 62357403192785191176690552862561408838653121833643 := by
  refine lucas_primality 62357403192785191176690552862561408838653121833643 (5 : ZMod 62357403192785191176690552862561408838653121833643) ?_ (fun q hq hd => ?_)
  · rw [show 62357403192785191176690552862561408838653121833643 - 1 = 62357403192785191176690552862561408838653121833642 from by norm_num]
    reduce_mod_char
  · have e : 62357403192785191176690552862561408838653121833643 - 1 = [2 ^ 1, 167 ^ 1, 499 ^ 1, 1163 ^ 1, 2657 ^ 1, 155377 ^ 1, 13455809771 ^ 1, 57912614113275649087721 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62357403192785191176690552862561408838653121833643 - 1) / 2 = 31178701596392595588345276431280704419326560916821 from by norm_num]
      have h2 : (5 : ZMod 62357403192785191176690552862561408838653121833643) ^ 31178701596392595588345276431280704419326560916821 = ((62357403192785191176690552862561408838653121833642 : ℕ) : ZMod 62357403192785191176690552862561408838653121833643) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62357403192785191176690552862561408838653121833643 - 1) / 167 = 373397623908893360339464388398571310411096537926 from by norm_num]
      have h2 : (5 : ZMod 62357403192785191176690552862561408838653121833643) ^ 373397623908893360339464388398571310411096537926 = ((4722366482869645213696 : ℕ) : ZMod 62357403192785191176690552862561408838653121833643) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62357403192785191176690552862561408838653121833643 - 1) / 499 = 124964735857284952257896899524171159997300845358 from by norm_num]
      have h2 : (5 : ZMod 62357403192785191176690552862561408838653121833643) ^ 124964735857284952257896899524171159997300845358 = ((5654690063819526687114185670138774069384207763612 : ℕ) : ZMod 62357403192785191176690552862561408838653121833643) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62357403192785191176690552862561408838653121833643 - 1) / 1163 = 53617715556995005310997895840551512329022460734 from by norm_num]
      have h2 : (5 : ZMod 62357403192785191176690552862561408838653121833643) ^ 53617715556995005310997895840551512329022460734 = ((52975413414649427173654278002932500914073322812877 : ℕ) : ZMod 62357403192785191176690552862561408838653121833643) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62357403192785191176690552862561408838653121833643 - 1) / 2657 = 23469101690924046359311461370930150108638736106 from by norm_num]
      have h2 : (5 : ZMod 62357403192785191176690552862561408838653121833643) ^ 23469101690924046359311461370930150108638736106 = ((19479191169619287166628604435995117003532175761136 : ℕ) : ZMod 62357403192785191176690552862561408838653121833643) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62357403192785191176690552862561408838653121833643 - 1) / 155377 = 401329689675982875050300577708164070864111946 from by norm_num]
      have h2 : (5 : ZMod 62357403192785191176690552862561408838653121833643) ^ 401329689675982875050300577708164070864111946 = ((25099234347126700213636254703795719764041584271199 : ℕ) : ZMod 62357403192785191176690552862561408838653121833643) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_13455809771).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62357403192785191176690552862561408838653121833643 - 1) / 13455809771 = 4634236382204068183291988132741670047102 from by norm_num]
      have h2 : (5 : ZMod 62357403192785191176690552862561408838653121833643) ^ 4634236382204068183291988132741670047102 = ((19230407800519824566556629448312403520362982478802 : ℕ) : ZMod 62357403192785191176690552862561408838653121833643) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_57912614113275649087721).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (62357403192785191176690552862561408838653121833643 - 1) / 57912614113275649087721 = 1076749930003429718271634202 from by norm_num]
      have h2 : (5 : ZMod 62357403192785191176690552862561408838653121833643) ^ 1076749930003429718271634202 = ((13225062437438194656646142161181233982784987732573 : ℕ) : ZMod 62357403192785191176690552862561408838653121833643) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_4651012967 : Nat.Prime 4651012967 := by
  refine lucas_primality 4651012967 (5 : ZMod 4651012967) ?_ (fun q hq hd => ?_)
  · rw [show 4651012967 - 1 = 4651012966 from by norm_num]
    reduce_mod_char
  · have e : 4651012967 - 1 = [2 ^ 1, 17 ^ 1, 3943 ^ 1, 34693 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4651012967 - 1) / 2 = 2325506483 from by norm_num]
      have h2 : (5 : ZMod 4651012967) ^ 2325506483 = ((4651012966 : ℕ) : ZMod 4651012967) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4651012967 - 1) / 17 = 273588998 from by norm_num]
      have h2 : (5 : ZMod 4651012967) ^ 273588998 = ((1226657812 : ℕ) : ZMod 4651012967) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4651012967 - 1) / 3943 = 1179562 from by norm_num]
      have h2 : (5 : ZMod 4651012967) ^ 1179562 = ((231159441 : ℕ) : ZMod 4651012967) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4651012967 - 1) / 34693 = 134062 from by norm_num]
      have h2 : (5 : ZMod 4651012967) ^ 134062 = ((3498147279 : ℕ) : ZMod 4651012967) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_4929910764223610387 : Nat.Prime 4929910764223610387 := by
  refine lucas_primality 4929910764223610387 (5 : ZMod 4929910764223610387) ?_ (fun q hq hd => ?_)
  · rw [show 4929910764223610387 - 1 = 4929910764223610386 from by norm_num]
    reduce_mod_char
  · have e : 4929910764223610387 - 1 = [2 ^ 1, 13 ^ 2, 31 ^ 1, 101161 ^ 1, 4651012967 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4929910764223610387 - 1) / 2 = 2464955382111805193 from by norm_num]
      have h2 : (5 : ZMod 4929910764223610387) ^ 2464955382111805193 = ((4929910764223610386 : ℕ) : ZMod 4929910764223610387) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4929910764223610387 - 1) / 13 = 379223904940277722 from by norm_num]
      have h2 : (5 : ZMod 4929910764223610387) ^ 379223904940277722 = ((386776397614436881 : ℕ) : ZMod 4929910764223610387) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4929910764223610387 - 1) / 31 = 159029379491084206 from by norm_num]
      have h2 : (5 : ZMod 4929910764223610387) ^ 159029379491084206 = ((876272047249366236 : ℕ) : ZMod 4929910764223610387) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4929910764223610387 - 1) / 101161 = 48733313868226 from by norm_num]
      have h2 : (5 : ZMod 4929910764223610387) ^ 48733313868226 = ((1202432423557561686 : ℕ) : ZMod 4929910764223610387) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_4651012967).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (4929910764223610387 - 1) / 4651012967 = 1059964958 from by norm_num]
      have h2 : (5 : ZMod 4929910764223610387) ^ 1059964958 = ((419207815607921260 : ℕ) : ZMod 4929910764223610387) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2432188932809 : Nat.Prime 2432188932809 := by
  refine lucas_primality 2432188932809 (3 : ZMod 2432188932809) ?_ (fun q hq hd => ?_)
  · rw [show 2432188932809 - 1 = 2432188932808 from by norm_num]
    reduce_mod_char
  · have e : 2432188932809 - 1 = [2 ^ 3, 17 ^ 1, 19 ^ 1, 41 ^ 1, 22957307 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2432188932809 - 1) / 2 = 1216094466404 from by norm_num]
      have h2 : (3 : ZMod 2432188932809) ^ 1216094466404 = ((2432188932808 : ℕ) : ZMod 2432188932809) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2432188932809 - 1) / 17 = 143069937224 from by norm_num]
      have h2 : (3 : ZMod 2432188932809) ^ 143069937224 = ((250587381542 : ℕ) : ZMod 2432188932809) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2432188932809 - 1) / 19 = 128009943832 from by norm_num]
      have h2 : (3 : ZMod 2432188932809) ^ 128009943832 = ((1013065432818 : ℕ) : ZMod 2432188932809) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2432188932809 - 1) / 41 = 59321681288 from by norm_num]
      have h2 : (3 : ZMod 2432188932809) ^ 59321681288 = ((840301574809 : ℕ) : ZMod 2432188932809) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2432188932809 - 1) / 22957307 = 105944 from by norm_num]
      have h2 : (3 : ZMod 2432188932809) ^ 105944 = ((1624432081126 : ℕ) : ZMod 2432188932809) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1050705618973489 : Nat.Prime 1050705618973489 := by
  refine lucas_primality 1050705618973489 (7 : ZMod 1050705618973489) ?_ (fun q hq hd => ?_)
  · rw [show 1050705618973489 - 1 = 1050705618973488 from by norm_num]
    reduce_mod_char
  · have e : 1050705618973489 - 1 = [2 ^ 4, 3 ^ 3, 2432188932809 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1050705618973489 - 1) / 2 = 525352809486744 from by norm_num]
      have h2 : (7 : ZMod 1050705618973489) ^ 525352809486744 = ((1050705618973488 : ℕ) : ZMod 1050705618973489) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1050705618973489 - 1) / 3 = 350235206324496 from by norm_num]
      have h2 : (7 : ZMod 1050705618973489) ^ 350235206324496 = ((930838502012717 : ℕ) : ZMod 1050705618973489) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_2432188932809).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1050705618973489 - 1) / 2432188932809 = 432 from by norm_num]
      have h2 : (7 : ZMod 1050705618973489) ^ 432 = ((820171737968308 : ℕ) : ZMod 1050705618973489) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3855260977 : Nat.Prime 3855260977 := by
  refine lucas_primality 3855260977 (5 : ZMod 3855260977) ?_ (fun q hq hd => ?_)
  · rw [show 3855260977 - 1 = 3855260976 from by norm_num]
    reduce_mod_char
  · have e : 3855260977 - 1 = [2 ^ 4, 3 ^ 1, 7 ^ 1, 43 ^ 1, 266837 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3855260977 - 1) / 2 = 1927630488 from by norm_num]
      have h2 : (5 : ZMod 3855260977) ^ 1927630488 = ((3855260976 : ℕ) : ZMod 3855260977) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3855260977 - 1) / 3 = 1285086992 from by norm_num]
      have h2 : (5 : ZMod 3855260977) ^ 1285086992 = ((5187086 : ℕ) : ZMod 3855260977) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3855260977 - 1) / 7 = 550751568 from by norm_num]
      have h2 : (5 : ZMod 3855260977) ^ 550751568 = ((3786448216 : ℕ) : ZMod 3855260977) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3855260977 - 1) / 43 = 89657232 from by norm_num]
      have h2 : (5 : ZMod 3855260977) ^ 89657232 = ((16777216 : ℕ) : ZMod 3855260977) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3855260977 - 1) / 266837 = 14448 from by norm_num]
      have h2 : (5 : ZMod 3855260977) ^ 14448 = ((1243426723 : ℕ) : ZMod 3855260977) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_47635010587 : Nat.Prime 47635010587 := by
  refine lucas_primality 47635010587 (3 : ZMod 47635010587) ?_ (fun q hq hd => ?_)
  · rw [show 47635010587 - 1 = 47635010586 from by norm_num]
    reduce_mod_char
  · have e : 47635010587 - 1 = [2 ^ 1, 3 ^ 2, 173 ^ 1, 2437 ^ 1, 6277 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (47635010587 - 1) / 2 = 23817505293 from by norm_num]
      have h2 : (3 : ZMod 47635010587) ^ 23817505293 = ((47635010586 : ℕ) : ZMod 47635010587) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (47635010587 - 1) / 3 = 15878336862 from by norm_num]
      have h2 : (3 : ZMod 47635010587) ^ 15878336862 = ((40922807174 : ℕ) : ZMod 47635010587) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (47635010587 - 1) / 173 = 275346882 from by norm_num]
      have h2 : (3 : ZMod 47635010587) ^ 275346882 = ((47601456155 : ℕ) : ZMod 47635010587) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (47635010587 - 1) / 2437 = 19546578 from by norm_num]
      have h2 : (3 : ZMod 47635010587) ^ 19546578 = ((30710277692 : ℕ) : ZMod 47635010587) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (47635010587 - 1) / 6277 = 7588818 from by norm_num]
      have h2 : (3 : ZMod 47635010587) ^ 7588818 = ((35717200669 : ℕ) : ZMod 47635010587) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_58745093521 : Nat.Prime 58745093521 := by
  refine lucas_primality 58745093521 (19 : ZMod 58745093521) ?_ (fun q hq hd => ?_)
  · rw [show 58745093521 - 1 = 58745093520 from by norm_num]
    reduce_mod_char
  · have e : 58745093521 - 1 = [2 ^ 4, 3 ^ 1, 5 ^ 1, 29 ^ 1, 61 ^ 1, 179 ^ 1, 773 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (58745093521 - 1) / 2 = 29372546760 from by norm_num]
      have h2 : (19 : ZMod 58745093521) ^ 29372546760 = ((58745093520 : ℕ) : ZMod 58745093521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (58745093521 - 1) / 3 = 19581697840 from by norm_num]
      have h2 : (19 : ZMod 58745093521) ^ 19581697840 = ((49792440108 : ℕ) : ZMod 58745093521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (58745093521 - 1) / 5 = 11749018704 from by norm_num]
      have h2 : (19 : ZMod 58745093521) ^ 11749018704 = ((24503522696 : ℕ) : ZMod 58745093521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (58745093521 - 1) / 29 = 2025692880 from by norm_num]
      have h2 : (19 : ZMod 58745093521) ^ 2025692880 = ((40443354632 : ℕ) : ZMod 58745093521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (58745093521 - 1) / 61 = 963034320 from by norm_num]
      have h2 : (19 : ZMod 58745093521) ^ 963034320 = ((57618891522 : ℕ) : ZMod 58745093521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (58745093521 - 1) / 179 = 328184880 from by norm_num]
      have h2 : (19 : ZMod 58745093521) ^ 328184880 = ((58208222609 : ℕ) : ZMod 58745093521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (58745093521 - 1) / 773 = 75996240 from by norm_num]
      have h2 : (19 : ZMod 58745093521) ^ 75996240 = ((56833696861 : ℕ) : ZMod 58745093521) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_43717618369 : Nat.Prime 43717618369 := by
  refine lucas_primality 43717618369 (7 : ZMod 43717618369) ?_ (fun q hq hd => ?_)
  · rw [show 43717618369 - 1 = 43717618368 from by norm_num]
    reduce_mod_char
  · have e : 43717618369 - 1 = [2 ^ 6, 3 ^ 2, 23 ^ 1, 3299941 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (43717618369 - 1) / 2 = 21858809184 from by norm_num]
      have h2 : (7 : ZMod 43717618369) ^ 21858809184 = ((43717618368 : ℕ) : ZMod 43717618369) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (43717618369 - 1) / 3 = 14572539456 from by norm_num]
      have h2 : (7 : ZMod 43717618369) ^ 14572539456 = ((4841435582 : ℕ) : ZMod 43717618369) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (43717618369 - 1) / 23 = 1900766016 from by norm_num]
      have h2 : (7 : ZMod 43717618369) ^ 1900766016 = ((21902536539 : ℕ) : ZMod 43717618369) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (43717618369 - 1) / 3299941 = 13248 from by norm_num]
      have h2 : (7 : ZMod 43717618369) ^ 13248 = ((21440435857 : ℕ) : ZMod 43717618369) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_23592342593 : Nat.Prime 23592342593 := by
  refine lucas_primality 23592342593 (3 : ZMod 23592342593) ?_ (fun q hq hd => ?_)
  · rw [show 23592342593 - 1 = 23592342592 from by norm_num]
    reduce_mod_char
  · have e : 23592342593 - 1 = [2 ^ 6, 7 ^ 1, 13 ^ 1, 47 ^ 1, 79 ^ 1, 1091 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (23592342593 - 1) / 2 = 11796171296 from by norm_num]
      have h2 : (3 : ZMod 23592342593) ^ 11796171296 = ((23592342592 : ℕ) : ZMod 23592342593) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (23592342593 - 1) / 7 = 3370334656 from by norm_num]
      have h2 : (3 : ZMod 23592342593) ^ 3370334656 = ((2962982513 : ℕ) : ZMod 23592342593) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (23592342593 - 1) / 13 = 1814795584 from by norm_num]
      have h2 : (3 : ZMod 23592342593) ^ 1814795584 = ((21198800312 : ℕ) : ZMod 23592342593) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (23592342593 - 1) / 47 = 501964736 from by norm_num]
      have h2 : (3 : ZMod 23592342593) ^ 501964736 = ((23592338497 : ℕ) : ZMod 23592342593) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (23592342593 - 1) / 79 = 298637248 from by norm_num]
      have h2 : (3 : ZMod 23592342593) ^ 298637248 = ((9044877779 : ℕ) : ZMod 23592342593) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (23592342593 - 1) / 1091 = 21624512 from by norm_num]
      have h2 : (3 : ZMod 23592342593) ^ 21624512 = ((12462473494 : ℕ) : ZMod 23592342593) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_88114244437 : Nat.Prime 88114244437 := by
  refine lucas_primality 88114244437 (2 : ZMod 88114244437) ?_ (fun q hq hd => ?_)
  · rw [show 88114244437 - 1 = 88114244436 from by norm_num]
    reduce_mod_char
  · have e : 88114244437 - 1 = [2 ^ 2, 3 ^ 2, 983 ^ 1, 2489947 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (88114244437 - 1) / 2 = 44057122218 from by norm_num]
      have h2 : (2 : ZMod 88114244437) ^ 44057122218 = ((88114244436 : ℕ) : ZMod 88114244437) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (88114244437 - 1) / 3 = 29371414812 from by norm_num]
      have h2 : (2 : ZMod 88114244437) ^ 29371414812 = ((21612683043 : ℕ) : ZMod 88114244437) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (88114244437 - 1) / 983 = 89638092 from by norm_num]
      have h2 : (2 : ZMod 88114244437) ^ 89638092 = ((17822603986 : ℕ) : ZMod 88114244437) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (88114244437 - 1) / 2489947 = 35388 from by norm_num]
      have h2 : (2 : ZMod 88114244437) ^ 35388 = ((82355390884 : ℕ) : ZMod 88114244437) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3011347479614249131 : Nat.Prime 3011347479614249131 := by
  refine lucas_primality 3011347479614249131 (11 : ZMod 3011347479614249131) ?_ (fun q hq hd => ?_)
  · rw [show 3011347479614249131 - 1 = 3011347479614249130 from by norm_num]
    reduce_mod_char
  · have e : 3011347479614249131 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 1, 19 ^ 1, 59957 ^ 1, 88114244437 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3011347479614249131 - 1) / 2 = 1505673739807124565 from by norm_num]
      have h2 : (11 : ZMod 3011347479614249131) ^ 1505673739807124565 = ((3011347479614249130 : ℕ) : ZMod 3011347479614249131) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3011347479614249131 - 1) / 3 = 1003782493204749710 from by norm_num]
      have h2 : (11 : ZMod 3011347479614249131) ^ 1003782493204749710 = ((2895214250005825179 : ℕ) : ZMod 3011347479614249131) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3011347479614249131 - 1) / 5 = 602269495922849826 from by norm_num]
      have h2 : (11 : ZMod 3011347479614249131) ^ 602269495922849826 = ((2867232291538393259 : ℕ) : ZMod 3011347479614249131) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3011347479614249131 - 1) / 19 = 158491972611276270 from by norm_num]
      have h2 : (11 : ZMod 3011347479614249131) ^ 158491972611276270 = ((1433616283207887958 : ℕ) : ZMod 3011347479614249131) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3011347479614249131 - 1) / 59957 = 50225119329090 from by norm_num]
      have h2 : (11 : ZMod 3011347479614249131) ^ 50225119329090 = ((2607332680629660854 : ℕ) : ZMod 3011347479614249131) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_88114244437).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3011347479614249131 - 1) / 88114244437 = 34175490 from by norm_num]
      have h2 : (11 : ZMod 3011347479614249131) ^ 34175490 = ((1746373792546638637 : ℕ) : ZMod 3011347479614249131) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_30327152671 : Nat.Prime 30327152671 := by
  refine lucas_primality 30327152671 (3 : ZMod 30327152671) ?_ (fun q hq hd => ?_)
  · rw [show 30327152671 - 1 = 30327152670 from by norm_num]
    reduce_mod_char
  · have e : 30327152671 - 1 = [2 ^ 1, 3 ^ 2, 5 ^ 1, 19 ^ 1, 17735177 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (30327152671 - 1) / 2 = 15163576335 from by norm_num]
      have h2 : (3 : ZMod 30327152671) ^ 15163576335 = ((30327152670 : ℕ) : ZMod 30327152671) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (30327152671 - 1) / 3 = 10109050890 from by norm_num]
      have h2 : (3 : ZMod 30327152671) ^ 10109050890 = ((29604117504 : ℕ) : ZMod 30327152671) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (30327152671 - 1) / 5 = 6065430534 from by norm_num]
      have h2 : (3 : ZMod 30327152671) ^ 6065430534 = ((12694515794 : ℕ) : ZMod 30327152671) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (30327152671 - 1) / 19 = 1596165930 from by norm_num]
      have h2 : (3 : ZMod 30327152671) ^ 1596165930 = ((1666875589 : ℕ) : ZMod 30327152671) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (30327152671 - 1) / 17735177 = 1710 from by norm_num]
      have h2 : (3 : ZMod 30327152671) ^ 1710 = ((28134759737 : ℕ) : ZMod 30327152671) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_420778751 : Nat.Prime 420778751 := by
  refine lucas_primality 420778751 (7 : ZMod 420778751) ?_ (fun q hq hd => ?_)
  · rw [show 420778751 - 1 = 420778750 from by norm_num]
    reduce_mod_char
  · have e : 420778751 - 1 = [2 ^ 1, 5 ^ 4, 7 ^ 1, 19 ^ 1, 2531 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (420778751 - 1) / 2 = 210389375 from by norm_num]
      have h2 : (7 : ZMod 420778751) ^ 210389375 = ((420778750 : ℕ) : ZMod 420778751) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (420778751 - 1) / 5 = 84155750 from by norm_num]
      have h2 : (7 : ZMod 420778751) ^ 84155750 = ((524288 : ℕ) : ZMod 420778751) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (420778751 - 1) / 7 = 60111250 from by norm_num]
      have h2 : (7 : ZMod 420778751) ^ 60111250 = ((201341668 : ℕ) : ZMod 420778751) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (420778751 - 1) / 19 = 22146250 from by norm_num]
      have h2 : (7 : ZMod 420778751) ^ 22146250 = ((33554432 : ℕ) : ZMod 420778751) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (420778751 - 1) / 2531 = 166250 from by norm_num]
      have h2 : (7 : ZMod 420778751) ^ 166250 = ((152440542 : ℕ) : ZMod 420778751) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1046183622564446793972631570534611069350392574077339085483 : Nat.Prime 1046183622564446793972631570534611069350392574077339085483 := by
  refine lucas_primality 1046183622564446793972631570534611069350392574077339085483 (5 : ZMod 1046183622564446793972631570534611069350392574077339085483) ?_ (fun q hq hd => ?_)
  · rw [show 1046183622564446793972631570534611069350392574077339085483 - 1 = 1046183622564446793972631570534611069350392574077339085482 from by norm_num]
    reduce_mod_char
  · have e : 1046183622564446793972631570534611069350392574077339085483 - 1 = [2 ^ 1, 11 ^ 1, 31 ^ 1, 191 ^ 1, 2281 ^ 1, 174763 ^ 1, 524287 ^ 1, 420778751 ^ 1, 30327152671 ^ 1, 3011347479614249131 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1046183622564446793972631570534611069350392574077339085483 - 1) / 2 = 523091811282223396986315785267305534675196287038669542741 from by norm_num]
      have h2 : (5 : ZMod 1046183622564446793972631570534611069350392574077339085483) ^ 523091811282223396986315785267305534675196287038669542741 = ((1046183622564446793972631570534611069350392574077339085482 : ℕ) : ZMod 1046183622564446793972631570534611069350392574077339085483) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1046183622564446793972631570534611069350392574077339085483 - 1) / 11 = 95107602051313344906602870048601006304581143097939916862 from by norm_num]
      have h2 : (5 : ZMod 1046183622564446793972631570534611069350392574077339085483) ^ 95107602051313344906602870048601006304581143097939916862 = ((392627861128721398270385662931499492095119081969670164202 : ℕ) : ZMod 1046183622564446793972631570534611069350392574077339085483) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1046183622564446793972631570534611069350392574077339085483 - 1) / 31 = 33747858792401509482988115178535840946786857228301260822 from by norm_num]
      have h2 : (5 : ZMod 1046183622564446793972631570534611069350392574077339085483) ^ 33747858792401509482988115178535840946786857228301260822 = ((668720009492427274422763613743367331285779503336716402562 : ℕ) : ZMod 1046183622564446793972631570534611069350392574077339085483) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1046183622564446793972631570534611069350392574077339085483 - 1) / 191 = 5477401165258883738076605081333042247907814523965126102 from by norm_num]
      have h2 : (5 : ZMod 1046183622564446793972631570534611069350392574077339085483) ^ 5477401165258883738076605081333042247907814523965126102 = ((1046183622564446793972631570534611069350383566878084344491 : ℕ) : ZMod 1046183622564446793972631570534611069350392574077339085483) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1046183622564446793972631570534611069350392574077339085483 - 1) / 2281 = 458651303184764048212464520181767237768694683944471322 from by norm_num]
      have h2 : (5 : ZMod 1046183622564446793972631570534611069350392574077339085483) ^ 458651303184764048212464520181767237768694683944471322 = ((499429585860639984181308667942268674119909093647835184918 : ℕ) : ZMod 1046183622564446793972631570534611069350392574077339085483) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1046183622564446793972631570534611069350392574077339085483 - 1) / 174763 = 5986299288547614735227889029912573424296862459887614 from by norm_num]
      have h2 : (5 : ZMod 1046183622564446793972631570534611069350392574077339085483) ^ 5986299288547614735227889029912573424296862459887614 = ((248040500576282970343340937908980153625899322235683007836 : ℕ) : ZMod 1046183622564446793972631570534611069350392574077339085483) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1046183622564446793972631570534611069350392574077339085483 - 1) / 524287 = 1995440708170232704554245233115852709203914218886486 from by norm_num]
      have h2 : (5 : ZMod 1046183622564446793972631570534611069350392574077339085483) ^ 1995440708170232704554245233115852709203914218886486 = ((294798488655519398464719949555363020029762437035584062431 : ℕ) : ZMod 1046183622564446793972631570534611069350392574077339085483) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_420778751).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1046183622564446793972631570534611069350392574077339085483 - 1) / 420778751 = 2486303360324501733151043956909818075272514352982 from by norm_num]
      have h2 : (5 : ZMod 1046183622564446793972631570534611069350392574077339085483) ^ 2486303360324501733151043956909818075272514352982 = ((878592421611204831865755714371582403555501104121970642104 : ℕ) : ZMod 1046183622564446793972631570534611069350392574077339085483) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_30327152671).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1046183622564446793972631570534611069350392574077339085483 - 1) / 30327152671 = 34496598936069859374522076132645029917269432342 from by norm_num]
      have h2 : (5 : ZMod 1046183622564446793972631570534611069350392574077339085483) ^ 34496598936069859374522076132645029917269432342 = ((789307095480842102922449012624163433968993390143946051487 : ℕ) : ZMod 1046183622564446793972631570534611069350392574077339085483) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_3011347479614249131).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1046183622564446793972631570534611069350392574077339085483 - 1) / 3011347479614249131 = 347413783911268175208721342252213146622 from by norm_num]
      have h2 : (5 : ZMod 1046183622564446793972631570534611069350392574077339085483) ^ 347413783911268175208721342252213146622 = ((736362618765011735680597310066553278420759964667086924968 : ℕ) : ZMod 1046183622564446793972631570534611069350392574077339085483) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_197002597249 : Nat.Prime 197002597249 := by
  refine lucas_primality 197002597249 (7 : ZMod 197002597249) ?_ (fun q hq hd => ?_)
  · rw [show 197002597249 - 1 = 197002597248 from by norm_num]
    reduce_mod_char
  · have e : 197002597249 - 1 = [2 ^ 7, 3 ^ 2, 59 ^ 1, 197 ^ 1, 14713 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (197002597249 - 1) / 2 = 98501298624 from by norm_num]
      have h2 : (7 : ZMod 197002597249) ^ 98501298624 = ((197002597248 : ℕ) : ZMod 197002597249) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (197002597249 - 1) / 3 = 65667532416 from by norm_num]
      have h2 : (7 : ZMod 197002597249) ^ 65667532416 = ((181261311599 : ℕ) : ZMod 197002597249) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (197002597249 - 1) / 59 = 3339027072 from by norm_num]
      have h2 : (7 : ZMod 197002597249) ^ 3339027072 = ((102617846236 : ℕ) : ZMod 197002597249) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (197002597249 - 1) / 197 = 1000013184 from by norm_num]
      have h2 : (7 : ZMod 197002597249) ^ 1000013184 = ((154407757021 : ℕ) : ZMod 197002597249) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (197002597249 - 1) / 14713 = 13389696 from by norm_num]
      have h2 : (7 : ZMod 197002597249) ^ 13389696 = ((84679904707 : ℕ) : ZMod 197002597249) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_71925114571 : Nat.Prime 71925114571 := by
  refine lucas_primality 71925114571 (2 : ZMod 71925114571) ?_ (fun q hq hd => ?_)
  · rw [show 71925114571 - 1 = 71925114570 from by norm_num]
    reduce_mod_char
  · have e : 71925114571 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 1, 29527 ^ 1, 81197 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (71925114571 - 1) / 2 = 35962557285 from by norm_num]
      have h2 : (2 : ZMod 71925114571) ^ 35962557285 = ((71925114570 : ℕ) : ZMod 71925114571) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (71925114571 - 1) / 3 = 23975038190 from by norm_num]
      have h2 : (2 : ZMod 71925114571) ^ 23975038190 = ((27391352207 : ℕ) : ZMod 71925114571) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (71925114571 - 1) / 5 = 14385022914 from by norm_num]
      have h2 : (2 : ZMod 71925114571) ^ 14385022914 = ((62063425361 : ℕ) : ZMod 71925114571) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (71925114571 - 1) / 29527 = 2435910 from by norm_num]
      have h2 : (2 : ZMod 71925114571) ^ 2435910 = ((36912035711 : ℕ) : ZMod 71925114571) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (71925114571 - 1) / 81197 = 885810 from by norm_num]
      have h2 : (2 : ZMod 71925114571) ^ 885810 = ((49506324629 : ℕ) : ZMod 71925114571) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_242099935645987 : Nat.Prime 242099935645987 := by
  refine lucas_primality 242099935645987 (3 : ZMod 242099935645987) ?_ (fun q hq hd => ?_)
  · rw [show 242099935645987 - 1 = 242099935645986 from by norm_num]
    reduce_mod_char
  · have e : 242099935645987 - 1 = [2 ^ 1, 3 ^ 2, 11 ^ 1, 17 ^ 1, 71925114571 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (242099935645987 - 1) / 2 = 121049967822993 from by norm_num]
      have h2 : (3 : ZMod 242099935645987) ^ 121049967822993 = ((242099935645986 : ℕ) : ZMod 242099935645987) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (242099935645987 - 1) / 3 = 80699978548662 from by norm_num]
      have h2 : (3 : ZMod 242099935645987) ^ 80699978548662 = ((8589934591 : ℕ) : ZMod 242099935645987) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (242099935645987 - 1) / 11 = 22009085058726 from by norm_num]
      have h2 : (3 : ZMod 242099935645987) ^ 22009085058726 = ((206915563557155 : ℕ) : ZMod 242099935645987) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (242099935645987 - 1) / 17 = 14241172685058 from by norm_num]
      have h2 : (3 : ZMod 242099935645987) ^ 14241172685058 = ((22459685976768 : ℕ) : ZMod 242099935645987) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_71925114571).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (242099935645987 - 1) / 71925114571 = 3366 from by norm_num]
      have h2 : (3 : ZMod 242099935645987) ^ 3366 = ((186518681366362 : ℕ) : ZMod 242099935645987) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_33057806959 : Nat.Prime 33057806959 := by
  refine lucas_primality 33057806959 (3 : ZMod 33057806959) ?_ (fun q hq hd => ?_)
  · rw [show 33057806959 - 1 = 33057806958 from by norm_num]
    reduce_mod_char
  · have e : 33057806959 - 1 = [2 ^ 1, 3 ^ 2, 11 ^ 1, 757 ^ 1, 220553 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33057806959 - 1) / 2 = 16528903479 from by norm_num]
      have h2 : (3 : ZMod 33057806959) ^ 16528903479 = ((33057806958 : ℕ) : ZMod 33057806959) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33057806959 - 1) / 3 = 11019268986 from by norm_num]
      have h2 : (3 : ZMod 33057806959) ^ 11019268986 = ((24467872366 : ℕ) : ZMod 33057806959) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33057806959 - 1) / 11 = 3005255178 from by norm_num]
      have h2 : (3 : ZMod 33057806959) ^ 3005255178 = ((27851839265 : ℕ) : ZMod 33057806959) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33057806959 - 1) / 757 = 43669494 from by norm_num]
      have h2 : (3 : ZMod 33057806959) ^ 43669494 = ((26031839672 : ℕ) : ZMod 33057806959) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (33057806959 - 1) / 220553 = 149886 from by norm_num]
      have h2 : (3 : ZMod 33057806959) ^ 149886 = ((25789327052 : ℕ) : ZMod 33057806959) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_267823007376498379256993682056860433753700498963798805883563 : Nat.Prime 267823007376498379256993682056860433753700498963798805883563 := by
  refine lucas_primality 267823007376498379256993682056860433753700498963798805883563 (3 : ZMod 267823007376498379256993682056860433753700498963798805883563) ?_ (fun q hq hd => ?_)
  · rw [show 267823007376498379256993682056860433753700498963798805883563 - 1 = 267823007376498379256993682056860433753700498963798805883562 from by norm_num]
    reduce_mod_char
  · have e : 267823007376498379256993682056860433753700498963798805883563 - 1 = [2 ^ 1, 3 ^ 2, 7 ^ 1, 19 ^ 1, 23 ^ 1, 67 ^ 1, 73 ^ 1, 89 ^ 1, 199 ^ 1, 683 ^ 1, 5347 ^ 1, 20857 ^ 1, 153649 ^ 1, 599479 ^ 1, 33057806959 ^ 1, 242099935645987 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (267823007376498379256993682056860433753700498963798805883563 - 1) / 2 = 133911503688249189628496841028430216876850249481899402941781 from by norm_num]
      have h2 : (3 : ZMod 267823007376498379256993682056860433753700498963798805883563) ^ 133911503688249189628496841028430216876850249481899402941781 = ((267823007376498379256993682056860433753700498963798805883562 : ℕ) : ZMod 267823007376498379256993682056860433753700498963798805883563) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (267823007376498379256993682056860433753700498963798805883563 - 1) / 3 = 89274335792166126418997894018953477917900166321266268627854 from by norm_num]
      have h2 : (3 : ZMod 267823007376498379256993682056860433753700498963798805883563) ^ 89274335792166126418997894018953477917900166321266268627854 = ((36815630904361092209737552665730480048115022627703598762214 : ℕ) : ZMod 267823007376498379256993682056860433753700498963798805883563) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (267823007376498379256993682056860433753700498963798805883563 - 1) / 7 = 38260429625214054179570526008122919107671499851971257983366 from by norm_num]
      have h2 : (3 : ZMod 267823007376498379256993682056860433753700498963798805883563) ^ 38260429625214054179570526008122919107671499851971257983366 = ((35841102619207590198090187545676964691858178623229566806001 : ℕ) : ZMod 267823007376498379256993682056860433753700498963798805883563) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (267823007376498379256993682056860433753700498963798805883563 - 1) / 19 = 14095947756657809434578614845097917565984236787568358204398 from by norm_num]
      have h2 : (3 : ZMod 267823007376498379256993682056860433753700498963798805883563) ^ 14095947756657809434578614845097917565984236787568358204398 = ((162098122350280735903543769103673941662665441846796661083647 : ℕ) : ZMod 267823007376498379256993682056860433753700498963798805883563) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (267823007376498379256993682056860433753700498963798805883563 - 1) / 23 = 11644478581586886054651899219863497119726108650599948081894 from by norm_num]
      have h2 : (3 : ZMod 267823007376498379256993682056860433753700498963798805883563) ^ 11644478581586886054651899219863497119726108650599948081894 = ((195532894955455271964375805556984722262820899210836174133337 : ℕ) : ZMod 267823007376498379256993682056860433753700498963798805883563) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (267823007376498379256993682056860433753700498963798805883563 - 1) / 67 = 3997358319052214615776025105326275130652246253191026953486 from by norm_num]
      have h2 : (3 : ZMod 267823007376498379256993682056860433753700498963798805883563) ^ 3997358319052214615776025105326275130652246253191026953486 = ((260787608071257689816131188533459492786583181793112352135733 : ℕ) : ZMod 267823007376498379256993682056860433753700498963798805883563) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (267823007376498379256993682056860433753700498963798805883563 - 1) / 73 = 3668808320226005195301283315847403202105486287175326107994 from by norm_num]
      have h2 : (3 : ZMod 267823007376498379256993682056860433753700498963798805883563) ^ 3668808320226005195301283315847403202105486287175326107994 = ((150544755313019000406909592466338531119743569782765107761804 : ℕ) : ZMod 267823007376498379256993682056860433753700498963798805883563) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (267823007376498379256993682056860433753700498963798805883563 - 1) / 89 = 3009247273893240216370715528728768918580904482739312425658 from by norm_num]
      have h2 : (3 : ZMod 267823007376498379256993682056860433753700498963798805883563) ^ 3009247273893240216370715528728768918580904482739312425658 = ((5680635253290054345291260478285785844830877650939100096637 : ℕ) : ZMod 267823007376498379256993682056860433753700498963798805883563) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (267823007376498379256993682056860433753700498963798805883563 - 1) / 199 = 1345844258173358689733636593250554943485932155596978924038 from by norm_num]
      have h2 : (3 : ZMod 267823007376498379256993682056860433753700498963798805883563) ^ 1345844258173358689733636593250554943485932155596978924038 = ((267823007376498379256993682056857957873621928203249007635115 : ℕ) : ZMod 267823007376498379256993682056860433753700498963798805883563) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (267823007376498379256993682056860433753700498963798805883563 - 1) / 683 = 392127390009514464505115200668902538438800144895752278014 from by norm_num]
      have h2 : (3 : ZMod 267823007376498379256993682056860433753700498963798805883563) ^ 392127390009514464505115200668902538438800144895752278014 = ((185153421977849516207155827680995619890575121291734573585466 : ℕ) : ZMod 267823007376498379256993682056860433753700498963798805883563) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (267823007376498379256993682056860433753700498963798805883563 - 1) / 5347 = 50088462198709253648212770162120896531456985031568880846 from by norm_num]
      have h2 : (3 : ZMod 267823007376498379256993682056860433753700498963798805883563) ^ 50088462198709253648212770162120896531456985031568880846 = ((199159830018987509148482917892068975782819560271144571588453 : ℕ) : ZMod 267823007376498379256993682056860433753700498963798805883563) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (267823007376498379256993682056860433753700498963798805883563 - 1) / 20857 = 12840917072277814606942210387728840856964112718214451066 from by norm_num]
      have h2 : (3 : ZMod 267823007376498379256993682056860433753700498963798805883563) ^ 12840917072277814606942210387728840856964112718214451066 = ((103660928210981162444432134853328150874384371914374611179862 : ℕ) : ZMod 267823007376498379256993682056860433753700498963798805883563) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (267823007376498379256993682056860433753700498963798805883563 - 1) / 153649 = 1743083309207989503719475441147423242284040240833320138 from by norm_num]
      have h2 : (3 : ZMod 267823007376498379256993682056860433753700498963798805883563) ^ 1743083309207989503719475441147423242284040240833320138 = ((177853284999206938881933068304342199059216080115207607613387 : ℕ) : ZMod 267823007376498379256993682056860433753700498963798805883563) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (267823007376498379256993682056860433753700498963798805883563 - 1) / 599479 = 446759615226719166571295545059727586377004864163379878 from by norm_num]
      have h2 : (3 : ZMod 267823007376498379256993682056860433753700498963798805883563) ^ 446759615226719166571295545059727586377004864163379878 = ((137372747932667430846820751479819210735751035080487091239719 : ℕ) : ZMod 267823007376498379256993682056860433753700498963798805883563) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_33057806959).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (267823007376498379256993682056860433753700498963798805883563 - 1) / 33057806959 = 8101656825229402213262336875540965123635698793718 from by norm_num]
      have h2 : (3 : ZMod 267823007376498379256993682056860433753700498963798805883563) ^ 8101656825229402213262336875540965123635698793718 = ((183884872936239850816029887793344150731632215969868119171573 : ℕ) : ZMod 267823007376498379256993682056860433753700498963798805883563) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_242099935645987).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (267823007376498379256993682056860433753700498963798805883563 - 1) / 242099935645987 = 1106249808211949269625294237354609307299931726 from by norm_num]
      have h2 : (3 : ZMod 267823007376498379256993682056860433753700498963798805883563) ^ 1106249808211949269625294237354609307299931726 = ((57029675977955819176377809079584485433380302731697421519818 : ℕ) : ZMod 267823007376498379256993682056860433753700498963798805883563) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_422542733 : Nat.Prime 422542733 := by
  refine lucas_primality 422542733 (2 : ZMod 422542733) ?_ (fun q hq hd => ?_)
  · rw [show 422542733 - 1 = 422542732 from by norm_num]
    reduce_mod_char
  · have e : 422542733 - 1 = [2 ^ 2, 167 ^ 1, 337 ^ 1, 1877 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (422542733 - 1) / 2 = 211271366 from by norm_num]
      have h2 : (2 : ZMod 422542733) ^ 211271366 = ((422542732 : ℕ) : ZMod 422542733) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (422542733 - 1) / 167 = 2530196 from by norm_num]
      have h2 : (2 : ZMod 422542733) ^ 2530196 = ((190165200 : ℕ) : ZMod 422542733) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (422542733 - 1) / 337 = 1253836 from by norm_num]
      have h2 : (2 : ZMod 422542733) ^ 1253836 = ((307133463 : ℕ) : ZMod 422542733) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (422542733 - 1) / 1877 = 225116 from by norm_num]
      have h2 : (2 : ZMod 422542733) ^ 225116 = ((238631219 : ℕ) : ZMod 422542733) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_20946001591429012199281424246257 : Nat.Prime 20946001591429012199281424246257 := by
  refine lucas_primality 20946001591429012199281424246257 (5 : ZMod 20946001591429012199281424246257) ?_ (fun q hq hd => ?_)
  · rw [show 20946001591429012199281424246257 - 1 = 20946001591429012199281424246256 from by norm_num]
    reduce_mod_char
  · have e : 20946001591429012199281424246257 - 1 = [2 ^ 4, 3 ^ 1, 53 ^ 1, 101 ^ 1, 1181 ^ 1, 7494271 ^ 1, 21797803 ^ 1, 422542733 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (20946001591429012199281424246257 - 1) / 2 = 10473000795714506099640712123128 from by norm_num]
      have h2 : (5 : ZMod 20946001591429012199281424246257) ^ 10473000795714506099640712123128 = ((20946001591429012199281424246256 : ℕ) : ZMod 20946001591429012199281424246257) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (20946001591429012199281424246257 - 1) / 3 = 6982000530476337399760474748752 from by norm_num]
      have h2 : (5 : ZMod 20946001591429012199281424246257) ^ 6982000530476337399760474748752 = ((18620774019600859303474066553440 : ℕ) : ZMod 20946001591429012199281424246257) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (20946001591429012199281424246257 - 1) / 53 = 395207577196773815080781589552 from by norm_num]
      have h2 : (5 : ZMod 20946001591429012199281424246257) ^ 395207577196773815080781589552 = ((1099511627776 : ℕ) : ZMod 20946001591429012199281424246257) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (20946001591429012199281424246257 - 1) / 101 = 207386154370584279200806180656 from by norm_num]
      have h2 : (5 : ZMod 20946001591429012199281424246257) ^ 207386154370584279200806180656 = ((18618526884573147376920849692520 : ℕ) : ZMod 20946001591429012199281424246257) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (20946001591429012199281424246257 - 1) / 1181 = 17735818451675708890162086576 from by norm_num]
      have h2 : (5 : ZMod 20946001591429012199281424246257) ^ 17735818451675708890162086576 = ((4939724079474035098918802580446 : ℕ) : ZMod 20946001591429012199281424246257) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (20946001591429012199281424246257 - 1) / 7494271 = 2794935170002394122027536 from by norm_num]
      have h2 : (5 : ZMod 20946001591429012199281424246257) ^ 2794935170002394122027536 = ((10498289578364974775844072248411 : ℕ) : ZMod 20946001591429012199281424246257) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (20946001591429012199281424246257 - 1) / 21797803 = 960922602678307176153552 from by norm_num]
      have h2 : (5 : ZMod 20946001591429012199281424246257) ^ 960922602678307176153552 = ((8575338685829762854086704852829 : ℕ) : ZMod 20946001591429012199281424246257) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_422542733).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (20946001591429012199281424246257 - 1) / 422542733 = 49571321325810168883632 from by norm_num]
      have h2 : (5 : ZMod 20946001591429012199281424246257) ^ 49571321325810168883632 = ((2042209094624625369291549207003 : ℕ) : ZMod 20946001591429012199281424246257) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_219256122131 : Nat.Prime 219256122131 := by
  refine lucas_primality 219256122131 (6 : ZMod 219256122131) ?_ (fun q hq hd => ?_)
  · rw [show 219256122131 - 1 = 219256122130 from by norm_num]
    reduce_mod_char
  · have e : 219256122131 - 1 = [2 ^ 1, 5 ^ 1, 223 ^ 1, 293 ^ 1, 335567 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (219256122131 - 1) / 2 = 109628061065 from by norm_num]
      have h2 : (6 : ZMod 219256122131) ^ 109628061065 = ((219256122130 : ℕ) : ZMod 219256122131) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (219256122131 - 1) / 5 = 43851224426 from by norm_num]
      have h2 : (6 : ZMod 219256122131) ^ 43851224426 = ((83775092159 : ℕ) : ZMod 219256122131) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (219256122131 - 1) / 223 = 983211310 from by norm_num]
      have h2 : (6 : ZMod 219256122131) ^ 983211310 = ((208026254868 : ℕ) : ZMod 219256122131) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (219256122131 - 1) / 293 = 748314410 from by norm_num]
      have h2 : (6 : ZMod 219256122131) ^ 748314410 = ((198591088661 : ℕ) : ZMod 219256122131) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (219256122131 - 1) / 335567 = 653390 from by norm_num]
      have h2 : (6 : ZMod 219256122131) ^ 653390 = ((208399723861 : ℕ) : ZMod 219256122131) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2030149279 : Nat.Prime 2030149279 := by
  refine lucas_primality 2030149279 (3 : ZMod 2030149279) ?_ (fun q hq hd => ?_)
  · rw [show 2030149279 - 1 = 2030149278 from by norm_num]
    reduce_mod_char
  · have e : 2030149279 - 1 = [2 ^ 1, 3 ^ 3, 19 ^ 1, 97 ^ 1, 20399 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2030149279 - 1) / 2 = 1015074639 from by norm_num]
      have h2 : (3 : ZMod 2030149279) ^ 1015074639 = ((2030149278 : ℕ) : ZMod 2030149279) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2030149279 - 1) / 3 = 676716426 from by norm_num]
      have h2 : (3 : ZMod 2030149279) ^ 676716426 = ((589861502 : ℕ) : ZMod 2030149279) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2030149279 - 1) / 19 = 106849962 from by norm_num]
      have h2 : (3 : ZMod 2030149279) ^ 106849962 = ((618116451 : ℕ) : ZMod 2030149279) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2030149279 - 1) / 97 = 20929374 from by norm_num]
      have h2 : (3 : ZMod 2030149279) ^ 20929374 = ((90941401 : ℕ) : ZMod 2030149279) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2030149279 - 1) / 20399 = 99522 from by norm_num]
      have h2 : (3 : ZMod 2030149279) ^ 99522 = ((1780601521 : ℕ) : ZMod 2030149279) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_79722667 : Nat.Prime 79722667 := by
  refine lucas_primality 79722667 (3 : ZMod 79722667) ?_ (fun q hq hd => ?_)
  · rw [show 79722667 - 1 = 79722666 from by norm_num]
    reduce_mod_char
  · have e : 79722667 - 1 = [2 ^ 1, 3 ^ 2, 4429037 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (79722667 - 1) / 2 = 39861333 from by norm_num]
      have h2 : (3 : ZMod 79722667) ^ 39861333 = ((79722666 : ℕ) : ZMod 79722667) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (79722667 - 1) / 3 = 26574222 from by norm_num]
      have h2 : (3 : ZMod 79722667) ^ 26574222 = ((41469259 : ℕ) : ZMod 79722667) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (79722667 - 1) / 4429037 = 18 from by norm_num]
      have h2 : (3 : ZMod 79722667) ^ 18 = ((68529821 : ℕ) : ZMod 79722667) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_797226671 : Nat.Prime 797226671 := by
  refine lucas_primality 797226671 (13 : ZMod 797226671) ?_ (fun q hq hd => ?_)
  · rw [show 797226671 - 1 = 797226670 from by norm_num]
    reduce_mod_char
  · have e : 797226671 - 1 = [2 ^ 1, 5 ^ 1, 79722667 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (797226671 - 1) / 2 = 398613335 from by norm_num]
      have h2 : (13 : ZMod 797226671) ^ 398613335 = ((797226670 : ℕ) : ZMod 797226671) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (797226671 - 1) / 5 = 159445334 from by norm_num]
      have h2 : (13 : ZMod 797226671) ^ 159445334 = ((741343467 : ℕ) : ZMod 797226671) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_79722667).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (797226671 - 1) / 79722667 = 10 from by norm_num]
      have h2 : (13 : ZMod 797226671) ^ 10 = ((735504437 : ℕ) : ZMod 797226671) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_842118471607630086011 : Nat.Prime 842118471607630086011 := by
  refine lucas_primality 842118471607630086011 (2 : ZMod 842118471607630086011) ?_ (fun q hq hd => ?_)
  · rw [show 842118471607630086011 - 1 = 842118471607630086010 from by norm_num]
    reduce_mod_char
  · have e : 842118471607630086011 - 1 = [2 ^ 1, 5 ^ 1, 599 ^ 1, 977 ^ 1, 180497 ^ 1, 797226671 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (842118471607630086011 - 1) / 2 = 421059235803815043005 from by norm_num]
      have h2 : (2 : ZMod 842118471607630086011) ^ 421059235803815043005 = ((842118471607630086010 : ℕ) : ZMod 842118471607630086011) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (842118471607630086011 - 1) / 5 = 168423694321526017202 from by norm_num]
      have h2 : (2 : ZMod 842118471607630086011) ^ 168423694321526017202 = ((584512806955924046529 : ℕ) : ZMod 842118471607630086011) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (842118471607630086011 - 1) / 599 = 1405873909194707990 from by norm_num]
      have h2 : (2 : ZMod 842118471607630086011) ^ 1405873909194707990 = ((34782143808926996553 : ℕ) : ZMod 842118471607630086011) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (842118471607630086011 - 1) / 977 = 861943164388567130 from by norm_num]
      have h2 : (2 : ZMod 842118471607630086011) ^ 861943164388567130 = ((494874773560635032976 : ℕ) : ZMod 842118471607630086011) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (842118471607630086011 - 1) / 180497 = 4665553840826330 from by norm_num]
      have h2 : (2 : ZMod 842118471607630086011) ^ 4665553840826330 = ((548743515446428057085 : ℕ) : ZMod 842118471607630086011) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_797226671).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (842118471607630086011 - 1) / 797226671 = 1056309958310 from by norm_num]
      have h2 : (2 : ZMod 842118471607630086011) ^ 1056309958310 = ((731114188490758230200 : ℕ) : ZMod 842118471607630086011) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_32605142983704221670173899 : Nat.Prime 32605142983704221670173899 := by
  refine lucas_primality 32605142983704221670173899 (3 : ZMod 32605142983704221670173899) ?_ (fun q hq hd => ?_)
  · rw [show 32605142983704221670173899 - 1 = 32605142983704221670173898 from by norm_num]
    reduce_mod_char
  · have e : 32605142983704221670173899 - 1 = [2 ^ 1, 3 ^ 4, 239 ^ 1, 842118471607630086011 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (32605142983704221670173899 - 1) / 2 = 16302571491852110835086949 from by norm_num]
      have h2 : (3 : ZMod 32605142983704221670173899) ^ 16302571491852110835086949 = ((32605142983704221670173898 : ℕ) : ZMod 32605142983704221670173899) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (32605142983704221670173899 - 1) / 3 = 10868380994568073890057966 from by norm_num]
      have h2 : (3 : ZMod 32605142983704221670173899) ^ 10868380994568073890057966 = ((8483996624131161008676399 : ℕ) : ZMod 32605142983704221670173899) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (32605142983704221670173899 - 1) / 239 = 136423192400436073933782 from by norm_num]
      have h2 : (3 : ZMod 32605142983704221670173899) ^ 136423192400436073933782 = ((274877906944 : ℕ) : ZMod 32605142983704221670173899) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_842118471607630086011).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (32605142983704221670173899 - 1) / 842118471607630086011 = 38718 from by norm_num]
      have h2 : (3 : ZMod 32605142983704221670173899) ^ 38718 = ((12778801390022944251062361 : ℕ) : ZMod 32605142983704221670173899) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_10411181203 : Nat.Prime 10411181203 := by
  refine lucas_primality 10411181203 (3 : ZMod 10411181203) ?_ (fun q hq hd => ?_)
  · rw [show 10411181203 - 1 = 10411181202 from by norm_num]
    reduce_mod_char
  · have e : 10411181203 - 1 = [2 ^ 1, 3 ^ 1, 101 ^ 1, 241 ^ 1, 71287 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (10411181203 - 1) / 2 = 5205590601 from by norm_num]
      have h2 : (3 : ZMod 10411181203) ^ 5205590601 = ((10411181202 : ℕ) : ZMod 10411181203) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (10411181203 - 1) / 3 = 3470393734 from by norm_num]
      have h2 : (3 : ZMod 10411181203) ^ 3470393734 = ((2662179209 : ℕ) : ZMod 10411181203) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (10411181203 - 1) / 101 = 103081002 from by norm_num]
      have h2 : (3 : ZMod 10411181203) ^ 103081002 = ((951279811 : ℕ) : ZMod 10411181203) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (10411181203 - 1) / 241 = 43199922 from by norm_num]
      have h2 : (3 : ZMod 10411181203) ^ 43199922 = ((1341297536 : ℕ) : ZMod 10411181203) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (10411181203 - 1) / 71287 = 146046 from by norm_num]
      have h2 : (3 : ZMod 10411181203) ^ 146046 = ((9763479498 : ℕ) : ZMod 10411181203) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_37831175201 : Nat.Prime 37831175201 := by
  refine lucas_primality 37831175201 (3 : ZMod 37831175201) ?_ (fun q hq hd => ?_)
  · rw [show 37831175201 - 1 = 37831175200 from by norm_num]
    reduce_mod_char
  · have e : 37831175201 - 1 = [2 ^ 5, 5 ^ 2, 7 ^ 2, 13 ^ 1, 61 ^ 1, 1217 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (37831175201 - 1) / 2 = 18915587600 from by norm_num]
      have h2 : (3 : ZMod 37831175201) ^ 18915587600 = ((37831175200 : ℕ) : ZMod 37831175201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (37831175201 - 1) / 5 = 7566235040 from by norm_num]
      have h2 : (3 : ZMod 37831175201) ^ 7566235040 = ((29259737639 : ℕ) : ZMod 37831175201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (37831175201 - 1) / 7 = 5404453600 from by norm_num]
      have h2 : (3 : ZMod 37831175201) ^ 5404453600 = ((10790411899 : ℕ) : ZMod 37831175201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (37831175201 - 1) / 13 = 2910090400 from by norm_num]
      have h2 : (3 : ZMod 37831175201) ^ 2910090400 = ((13312095126 : ℕ) : ZMod 37831175201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (37831175201 - 1) / 61 = 620183200 from by norm_num]
      have h2 : (3 : ZMod 37831175201) ^ 620183200 = ((3674078552 : ℕ) : ZMod 37831175201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (37831175201 - 1) / 1217 = 31085600 from by norm_num]
      have h2 : (3 : ZMod 37831175201) ^ 31085600 = ((7793017209 : ℕ) : ZMod 37831175201) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_3853149761 : Nat.Prime 3853149761 := by
  refine lucas_primality 3853149761 (6 : ZMod 3853149761) ?_ (fun q hq hd => ?_)
  · rw [show 3853149761 - 1 = 3853149760 from by norm_num]
    reduce_mod_char
  · have e : 3853149761 - 1 = [2 ^ 6, 5 ^ 1, 719 ^ 1, 16747 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3853149761 - 1) / 2 = 1926574880 from by norm_num]
      have h2 : (6 : ZMod 3853149761) ^ 1926574880 = ((3853149760 : ℕ) : ZMod 3853149761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3853149761 - 1) / 5 = 770629952 from by norm_num]
      have h2 : (6 : ZMod 3853149761) ^ 770629952 = ((2694843562 : ℕ) : ZMod 3853149761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3853149761 - 1) / 719 = 5359040 from by norm_num]
      have h2 : (6 : ZMod 3853149761) ^ 5359040 = ((803003822 : ℕ) : ZMod 3853149761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (3853149761 - 1) / 16747 = 230080 from by norm_num]
      have h2 : (6 : ZMod 3853149761) ^ 230080 = ((3140195378 : ℕ) : ZMod 3853149761) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1238926361552897 : Nat.Prime 1238926361552897 := by
  refine lucas_primality 1238926361552897 (3 : ZMod 1238926361552897) ?_ (fun q hq hd => ?_)
  · rw [show 1238926361552897 - 1 = 1238926361552896 from by norm_num]
    reduce_mod_char
  · have e : 1238926361552897 - 1 = [2 ^ 11, 157 ^ 1, 3853149761 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1238926361552897 - 1) / 2 = 619463180776448 from by norm_num]
      have h2 : (3 : ZMod 1238926361552897) ^ 619463180776448 = ((1238926361552896 : ℕ) : ZMod 1238926361552897) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1238926361552897 - 1) / 157 = 7891250710528 from by norm_num]
      have h2 : (3 : ZMod 1238926361552897) ^ 7891250710528 = ((196133765836405 : ℕ) : ZMod 1238926361552897) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_3853149761).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1238926361552897 - 1) / 3853149761 = 321536 from by norm_num]
      have h2 : (3 : ZMod 1238926361552897) ^ 321536 = ((437771075092802 : ℕ) : ZMod 1238926361552897) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_611065913 : Nat.Prime 611065913 := by
  refine lucas_primality 611065913 (3 : ZMod 611065913) ?_ (fun q hq hd => ?_)
  · rw [show 611065913 - 1 = 611065912 from by norm_num]
    reduce_mod_char
  · have e : 611065913 - 1 = [2 ^ 3, 1013 ^ 1, 75403 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (611065913 - 1) / 2 = 305532956 from by norm_num]
      have h2 : (3 : ZMod 611065913) ^ 305532956 = ((611065912 : ℕ) : ZMod 611065913) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (611065913 - 1) / 1013 = 603224 from by norm_num]
      have h2 : (3 : ZMod 611065913) ^ 603224 = ((340408484 : ℕ) : ZMod 611065913) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (611065913 - 1) / 75403 = 8104 from by norm_num]
      have h2 : (3 : ZMod 611065913) ^ 8104 = ((306963438 : ℕ) : ZMod 611065913) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_206487726925483 : Nat.Prime 206487726925483 := by
  refine lucas_primality 206487726925483 (2 : ZMod 206487726925483) ?_ (fun q hq hd => ?_)
  · rw [show 206487726925483 - 1 = 206487726925482 from by norm_num]
    reduce_mod_char
  · have e : 206487726925483 - 1 = [2 ^ 1, 3 ^ 2, 18773 ^ 1, 611065913 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (206487726925483 - 1) / 2 = 103243863462741 from by norm_num]
      have h2 : (2 : ZMod 206487726925483) ^ 103243863462741 = ((206487726925482 : ℕ) : ZMod 206487726925483) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (206487726925483 - 1) / 3 = 68829242308494 from by norm_num]
      have h2 : (2 : ZMod 206487726925483) ^ 68829242308494 = ((2152959480421 : ℕ) : ZMod 206487726925483) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (206487726925483 - 1) / 18773 = 10999186434 from by norm_num]
      have h2 : (2 : ZMod 206487726925483) ^ 10999186434 = ((204828111120102 : ℕ) : ZMod 206487726925483) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_611065913).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (206487726925483 - 1) / 611065913 = 337914 from by norm_num]
      have h2 : (2 : ZMod 206487726925483) ^ 337914 = ((51630314293860 : ℕ) : ZMod 206487726925483) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_37239639534523 : Nat.Prime 37239639534523 := by
  refine lucas_primality 37239639534523 (3 : ZMod 37239639534523) ?_ (fun q hq hd => ?_)
  · rw [show 37239639534523 - 1 = 37239639534522 from by norm_num]
    reduce_mod_char
  · have e : 37239639534523 - 1 = [2 ^ 1, 3 ^ 3, 31 ^ 1, 101 ^ 1, 257 ^ 1, 857029 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (37239639534523 - 1) / 2 = 18619819767261 from by norm_num]
      have h2 : (3 : ZMod 37239639534523) ^ 18619819767261 = ((37239639534522 : ℕ) : ZMod 37239639534523) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (37239639534523 - 1) / 3 = 12413213178174 from by norm_num]
      have h2 : (3 : ZMod 37239639534523) ^ 12413213178174 = ((16089517958325 : ℕ) : ZMod 37239639534523) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (37239639534523 - 1) / 31 = 1201278694662 from by norm_num]
      have h2 : (3 : ZMod 37239639534523) ^ 1201278694662 = ((30654602168578 : ℕ) : ZMod 37239639534523) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (37239639534523 - 1) / 101 = 368709302322 from by norm_num]
      have h2 : (3 : ZMod 37239639534523) ^ 368709302322 = ((26562140768659 : ℕ) : ZMod 37239639534523) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (37239639534523 - 1) / 257 = 144901321146 from by norm_num]
      have h2 : (3 : ZMod 37239639534523) ^ 144901321146 = ((26984191928336 : ℕ) : ZMod 37239639534523) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (37239639534523 - 1) / 857029 = 43452018 from by norm_num]
      have h2 : (3 : ZMod 37239639534523) ^ 43452018 = ((37140272816736 : ℕ) : ZMod 37239639534523) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1329987126233 : Nat.Prime 1329987126233 := by
  refine lucas_primality 1329987126233 (3 : ZMod 1329987126233) ?_ (fun q hq hd => ?_)
  · rw [show 1329987126233 - 1 = 1329987126232 from by norm_num]
    reduce_mod_char
  · have e : 1329987126233 - 1 = [2 ^ 3, 337 ^ 1, 3433 ^ 1, 143699 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1329987126233 - 1) / 2 = 664993563116 from by norm_num]
      have h2 : (3 : ZMod 1329987126233) ^ 664993563116 = ((1329987126232 : ℕ) : ZMod 1329987126233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1329987126233 - 1) / 337 = 3946549336 from by norm_num]
      have h2 : (3 : ZMod 1329987126233) ^ 3946549336 = ((342701223758 : ℕ) : ZMod 1329987126233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1329987126233 - 1) / 3433 = 387412504 from by norm_num]
      have h2 : (3 : ZMod 1329987126233) ^ 387412504 = ((588448814282 : ℕ) : ZMod 1329987126233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1329987126233 - 1) / 143699 = 9255368 from by norm_num]
      have h2 : (3 : ZMod 1329987126233) ^ 9255368 = ((597682396658 : ℕ) : ZMod 1329987126233) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_6487031809 : Nat.Prime 6487031809 := by
  refine lucas_primality 6487031809 (7 : ZMod 6487031809) ?_ (fun q hq hd => ?_)
  · rw [show 6487031809 - 1 = 6487031808 from by norm_num]
    reduce_mod_char
  · have e : 6487031809 - 1 = [2 ^ 14, 3 ^ 2, 29 ^ 1, 37 ^ 1, 41 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6487031809 - 1) / 2 = 3243515904 from by norm_num]
      have h2 : (7 : ZMod 6487031809) ^ 3243515904 = ((6487031808 : ℕ) : ZMod 6487031809) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6487031809 - 1) / 3 = 2162343936 from by norm_num]
      have h2 : (7 : ZMod 6487031809) ^ 2162343936 = ((370700344 : ℕ) : ZMod 6487031809) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6487031809 - 1) / 29 = 223690752 from by norm_num]
      have h2 : (7 : ZMod 6487031809) ^ 223690752 = ((1706837087 : ℕ) : ZMod 6487031809) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6487031809 - 1) / 37 = 175325184 from by norm_num]
      have h2 : (7 : ZMod 6487031809) ^ 175325184 = ((2803872759 : ℕ) : ZMod 6487031809) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (6487031809 - 1) / 41 = 158220288 from by norm_num]
      have h2 : (7 : ZMod 6487031809) ^ 158220288 = ((2843121849 : ℕ) : ZMod 6487031809) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_45592577 : Nat.Prime 45592577 := by
  refine lucas_primality 45592577 (3 : ZMod 45592577) ?_ (fun q hq hd => ?_)
  · rw [show 45592577 - 1 = 45592576 from by norm_num]
    reduce_mod_char
  · have e : 45592577 - 1 = [2 ^ 12, 11131 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (45592577 - 1) / 2 = 22796288 from by norm_num]
      have h2 : (3 : ZMod 45592577) ^ 22796288 = ((45592576 : ℕ) : ZMod 45592577) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (45592577 - 1) / 11131 = 4096 from by norm_num]
      have h2 : (3 : ZMod 45592577) ^ 4096 = ((6181419 : ℕ) : ZMod 45592577) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1069660739759 : Nat.Prime 1069660739759 := by
  refine lucas_primality 1069660739759 (17 : ZMod 1069660739759) ?_ (fun q hq hd => ?_)
  · rw [show 1069660739759 - 1 = 1069660739758 from by norm_num]
    reduce_mod_char
  · have e : 1069660739759 - 1 = [2 ^ 1, 13 ^ 1, 73 ^ 1, 563 ^ 1, 1001017 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1069660739759 - 1) / 2 = 534830369879 from by norm_num]
      have h2 : (17 : ZMod 1069660739759) ^ 534830369879 = ((1069660739758 : ℕ) : ZMod 1069660739759) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1069660739759 - 1) / 13 = 82281595366 from by norm_num]
      have h2 : (17 : ZMod 1069660739759) ^ 82281595366 = ((1144950070 : ℕ) : ZMod 1069660739759) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1069660739759 - 1) / 73 = 14652886846 from by norm_num]
      have h2 : (17 : ZMod 1069660739759) ^ 14652886846 = ((1061627935906 : ℕ) : ZMod 1069660739759) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1069660739759 - 1) / 563 = 1899930266 from by norm_num]
      have h2 : (17 : ZMod 1069660739759) ^ 1899930266 = ((368040485674 : ℕ) : ZMod 1069660739759) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1069660739759 - 1) / 1001017 = 1068574 from by norm_num]
      have h2 : (17 : ZMod 1069660739759) ^ 1068574 = ((50491089679 : ℕ) : ZMod 1069660739759) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2663848877152141313 : Nat.Prime 2663848877152141313 := by
  refine lucas_primality 2663848877152141313 (3 : ZMod 2663848877152141313) ?_ (fun q hq hd => ?_)
  · rw [show 2663848877152141313 - 1 = 2663848877152141312 from by norm_num]
    reduce_mod_char
  · have e : 2663848877152141313 - 1 = [2 ^ 17, 19 ^ 1, 1069660739759 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2663848877152141313 - 1) / 2 = 1331924438576070656 from by norm_num]
      have h2 : (3 : ZMod 2663848877152141313) ^ 1331924438576070656 = ((2663848877152141312 : ℕ) : ZMod 2663848877152141313) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2663848877152141313 - 1) / 19 = 140202572481691648 from by norm_num]
      have h2 : (3 : ZMod 2663848877152141313) ^ 140202572481691648 = ((1712054958658763820 : ℕ) : ZMod 2663848877152141313) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_1069660739759).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2663848877152141313 - 1) / 1069660739759 = 2490368 from by norm_num]
      have h2 : (3 : ZMod 2663848877152141313) ^ 2490368 = ((2177351900160986599 : ℕ) : ZMod 2663848877152141313) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_643620696810643 : Nat.Prime 643620696810643 := by
  refine lucas_primality 643620696810643 (2 : ZMod 643620696810643) ?_ (fun q hq hd => ?_)
  · rw [show 643620696810643 - 1 = 643620696810642 from by norm_num]
    reduce_mod_char
  · have e : 643620696810643 - 1 = [2 ^ 1, 3 ^ 2, 127 ^ 1, 50153 ^ 1, 5613799 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (643620696810643 - 1) / 2 = 321810348405321 from by norm_num]
      have h2 : (2 : ZMod 643620696810643) ^ 321810348405321 = ((643620696810642 : ℕ) : ZMod 643620696810643) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (643620696810643 - 1) / 3 = 214540232270214 from by norm_num]
      have h2 : (2 : ZMod 643620696810643) ^ 214540232270214 = ((11262356464105 : ℕ) : ZMod 643620696810643) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (643620696810643 - 1) / 127 = 5067879502446 from by norm_num]
      have h2 : (2 : ZMod 643620696810643) ^ 5067879502446 = ((371599021910739 : ℕ) : ZMod 643620696810643) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (643620696810643 - 1) / 50153 = 12833144514 from by norm_num]
      have h2 : (2 : ZMod 643620696810643) ^ 12833144514 = ((250277297141578 : ℕ) : ZMod 643620696810643) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (643620696810643 - 1) / 5613799 = 114649758 from by norm_num]
      have h2 : (2 : ZMod 643620696810643) ^ 114649758 = ((497809978569278 : ℕ) : ZMod 643620696810643) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_8717008205877092841673 : Nat.Prime 8717008205877092841673 := by
  refine lucas_primality 8717008205877092841673 (10 : ZMod 8717008205877092841673) ?_ (fun q hq hd => ?_)
  · rw [show 8717008205877092841673 - 1 = 8717008205877092841672 from by norm_num]
    reduce_mod_char
  · have e : 8717008205877092841673 - 1 = [2 ^ 3, 3 ^ 2, 188107 ^ 1, 643620696810643 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8717008205877092841673 - 1) / 2 = 4358504102938546420836 from by norm_num]
      have h2 : (10 : ZMod 8717008205877092841673) ^ 4358504102938546420836 = ((8717008205877092841672 : ℕ) : ZMod 8717008205877092841673) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8717008205877092841673 - 1) / 3 = 2905669401959030947224 from by norm_num]
      have h2 : (10 : ZMod 8717008205877092841673) ^ 2905669401959030947224 = ((7343390186032111538464 : ℕ) : ZMod 8717008205877092841673) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8717008205877092841673 - 1) / 188107 = 46340690170366296 from by norm_num]
      have h2 : (10 : ZMod 8717008205877092841673) ^ 46340690170366296 = ((2202464808706072287353 : ℕ) : ZMod 8717008205877092841673) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_643620696810643).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (8717008205877092841673 - 1) / 643620696810643 = 13543704 from by norm_num]
      have h2 : (10 : ZMod 8717008205877092841673) ^ 13543704 = ((7313602266967842624858 : ℕ) : ZMod 8717008205877092841673) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_2937316727 : Nat.Prime 2937316727 := by
  refine lucas_primality 2937316727 (5 : ZMod 2937316727) ?_ (fun q hq hd => ?_)
  · rw [show 2937316727 - 1 = 2937316726 from by norm_num]
    reduce_mod_char
  · have e : 2937316727 - 1 = [2 ^ 1, 2833 ^ 1, 518411 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2937316727 - 1) / 2 = 1468658363 from by norm_num]
      have h2 : (5 : ZMod 2937316727) ^ 1468658363 = ((2937316726 : ℕ) : ZMod 2937316727) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2937316727 - 1) / 2833 = 1036822 from by norm_num]
      have h2 : (5 : ZMod 2937316727) ^ 1036822 = ((559649464 : ℕ) : ZMod 2937316727) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (2937316727 - 1) / 518411 = 5666 from by norm_num]
      have h2 : (5 : ZMod 2937316727) ^ 5666 = ((1096917264 : ℕ) : ZMod 2937316727) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_761145015334071629 : Nat.Prime 761145015334071629 := by
  refine lucas_primality 761145015334071629 (2 : ZMod 761145015334071629) ?_ (fun q hq hd => ?_)
  · rw [show 761145015334071629 - 1 = 761145015334071628 from by norm_num]
    reduce_mod_char
  · have e : 761145015334071629 - 1 = [2 ^ 2, 13 ^ 1, 1439 ^ 1, 3463 ^ 1, 2937316727 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (761145015334071629 - 1) / 2 = 380572507667035814 from by norm_num]
      have h2 : (2 : ZMod 761145015334071629) ^ 380572507667035814 = ((761145015334071628 : ℕ) : ZMod 761145015334071629) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (761145015334071629 - 1) / 13 = 58549616564159356 from by norm_num]
      have h2 : (2 : ZMod 761145015334071629) ^ 58549616564159356 = ((338322455532595746 : ℕ) : ZMod 761145015334071629) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (761145015334071629 - 1) / 1439 = 528940246931252 from by norm_num]
      have h2 : (2 : ZMod 761145015334071629) ^ 528940246931252 = ((329189789386551514 : ℕ) : ZMod 761145015334071629) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (761145015334071629 - 1) / 3463 = 219793536047956 from by norm_num]
      have h2 : (2 : ZMod 761145015334071629) ^ 219793536047956 = ((294223303145502828 : ℕ) : ZMod 761145015334071629) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_2937316727).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (761145015334071629 - 1) / 2937316727 = 259129364 from by norm_num]
      have h2 : (2 : ZMod 761145015334071629) ^ 259129364 = ((48063209786497848 : ℕ) : ZMod 761145015334071629) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_116928085873074369829035993834596371340386703423373313 : Nat.Prime 116928085873074369829035993834596371340386703423373313 := by
  refine lucas_primality 116928085873074369829035993834596371340386703423373313 (5 : ZMod 116928085873074369829035993834596371340386703423373313) ?_ (fun q hq hd => ?_)
  · rw [show 116928085873074369829035993834596371340386703423373313 - 1 = 116928085873074369829035993834596371340386703423373312 from by norm_num]
    reduce_mod_char
  · have e : 116928085873074369829035993834596371340386703423373313 - 1 = [2 ^ 16, 3 ^ 3, 9959563 ^ 1, 761145015334071629 ^ 1, 8717008205877092841673 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (116928085873074369829035993834596371340386703423373313 - 1) / 2 = 58464042936537184914517996917298185670193351711686656 from by norm_num]
      have h2 : (5 : ZMod 116928085873074369829035993834596371340386703423373313) ^ 58464042936537184914517996917298185670193351711686656 = ((116928085873074369829035993834596371340386703423373312 : ℕ) : ZMod 116928085873074369829035993834596371340386703423373313) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (116928085873074369829035993834596371340386703423373313 - 1) / 3 = 38976028624358123276345331278198790446795567807791104 from by norm_num]
      have h2 : (5 : ZMod 116928085873074369829035993834596371340386703423373313) ^ 38976028624358123276345331278198790446795567807791104 = ((49067573676489472842253551286141007228252506114172807 : ℕ) : ZMod 116928085873074369829035993834596371340386703423373313) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (116928085873074369829035993834596371340386703423373313 - 1) / 9959563 = 11740282768739388447970658334567126222343962624 from by norm_num]
      have h2 : (5 : ZMod 116928085873074369829035993834596371340386703423373313) ^ 11740282768739388447970658334567126222343962624 = ((42667818912291893027423909550891575419819132189033998 : ℕ) : ZMod 116928085873074369829035993834596371340386703423373313) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_761145015334071629).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (116928085873074369829035993834596371340386703423373313 - 1) / 761145015334071629 = 153621298855585163717133222561251328 from by norm_num]
      have h2 : (5 : ZMod 116928085873074369829035993834596371340386703423373313) ^ 153621298855585163717133222561251328 = ((113675781698961535315298001192578299458232658608361774 : ℕ) : ZMod 116928085873074369829035993834596371340386703423373313) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_8717008205877092841673).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (116928085873074369829035993834596371340386703423373313 - 1) / 8717008205877092841673 = 13413786371594821026416520658944 from by norm_num]
      have h2 : (5 : ZMod 116928085873074369829035993834596371340386703423373313) ^ 13413786371594821026416520658944 = ((88896328563985109771361010271091762988159944350705466 : ℕ) : ZMod 116928085873074369829035993834596371340386703423373313) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_5209282751 : Nat.Prime 5209282751 := by
  refine lucas_primality 5209282751 (7 : ZMod 5209282751) ?_ (fun q hq hd => ?_)
  · rw [show 5209282751 - 1 = 5209282750 from by norm_num]
    reduce_mod_char
  · have e : 5209282751 - 1 = [2 ^ 1, 5 ^ 3, 7 ^ 1, 2976733 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5209282751 - 1) / 2 = 2604641375 from by norm_num]
      have h2 : (7 : ZMod 5209282751) ^ 2604641375 = ((5209282750 : ℕ) : ZMod 5209282751) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5209282751 - 1) / 5 = 1041856550 from by norm_num]
      have h2 : (7 : ZMod 5209282751) ^ 1041856550 = ((2916606904 : ℕ) : ZMod 5209282751) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5209282751 - 1) / 7 = 744183250 from by norm_num]
      have h2 : (7 : ZMod 5209282751) ^ 744183250 = ((4224756034 : ℕ) : ZMod 5209282751) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (5209282751 - 1) / 2976733 = 1750 from by norm_num]
      have h2 : (7 : ZMod 5209282751) ^ 1750 = ((2197998515 : ℕ) : ZMod 5209282751) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_78068824171447136188657471 : Nat.Prime 78068824171447136188657471 := by
  refine lucas_primality 78068824171447136188657471 (3 : ZMod 78068824171447136188657471) ?_ (fun q hq hd => ?_)
  · rw [show 78068824171447136188657471 - 1 = 78068824171447136188657470 from by norm_num]
    reduce_mod_char
  · have e : 78068824171447136188657471 - 1 = [2 ^ 1, 3 ^ 1, 5 ^ 1, 13 ^ 1, 109 ^ 1, 25741 ^ 1, 13695667 ^ 1, 5209282751 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (78068824171447136188657471 - 1) / 2 = 39034412085723568094328735 from by norm_num]
      have h2 : (3 : ZMod 78068824171447136188657471) ^ 39034412085723568094328735 = ((78068824171447136188657470 : ℕ) : ZMod 78068824171447136188657471) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (78068824171447136188657471 - 1) / 3 = 26022941390482378729552490 from by norm_num]
      have h2 : (3 : ZMod 78068824171447136188657471) ^ 26022941390482378729552490 = ((12575755819311775742793908 : ℕ) : ZMod 78068824171447136188657471) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (78068824171447136188657471 - 1) / 5 = 15613764834289427237731494 from by norm_num]
      have h2 : (3 : ZMod 78068824171447136188657471) ^ 15613764834289427237731494 = ((6671610913403589376691810 : ℕ) : ZMod 78068824171447136188657471) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (78068824171447136188657471 - 1) / 13 = 6005294167034395091435190 from by norm_num]
      have h2 : (3 : ZMod 78068824171447136188657471) ^ 6005294167034395091435190 = ((20967338033158950684450606 : ℕ) : ZMod 78068824171447136188657471) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (78068824171447136188657471 - 1) / 109 = 716227744692175561363830 from by norm_num]
      have h2 : (3 : ZMod 78068824171447136188657471) ^ 716227744692175561363830 = ((69982863744249685193923038 : ℕ) : ZMod 78068824171447136188657471) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (78068824171447136188657471 - 1) / 25741 = 3032859025346611871670 from by norm_num]
      have h2 : (3 : ZMod 78068824171447136188657471) ^ 3032859025346611871670 = ((66419757672515866513209297 : ℕ) : ZMod 78068824171447136188657471) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (78068824171447136188657471 - 1) / 13695667 = 5700257181446302410 from by norm_num]
      have h2 : (3 : ZMod 78068824171447136188657471) ^ 5700257181446302410 = ((3461793783568778776369833 : ℕ) : ZMod 78068824171447136188657471) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq prime_5209282751).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (78068824171447136188657471 - 1) / 5209282751 = 14986482382139970 from by norm_num]
      have h2 : (3 : ZMod 78068824171447136188657471) ^ 14986482382139970 = ((16902179292308980897130870 : ℕ) : ZMod 78068824171447136188657471) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_68244480929 : Nat.Prime 68244480929 := by
  refine lucas_primality 68244480929 (3 : ZMod 68244480929) ?_ (fun q hq hd => ?_)
  · rw [show 68244480929 - 1 = 68244480928 from by norm_num]
    reduce_mod_char
  · have e : 68244480929 - 1 = [2 ^ 5, 13 ^ 1, 103 ^ 1, 643 ^ 1, 2477 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (68244480929 - 1) / 2 = 34122240464 from by norm_num]
      have h2 : (3 : ZMod 68244480929) ^ 34122240464 = ((68244480928 : ℕ) : ZMod 68244480929) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (68244480929 - 1) / 13 = 5249575456 from by norm_num]
      have h2 : (3 : ZMod 68244480929) ^ 5249575456 = ((36315398612 : ℕ) : ZMod 68244480929) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (68244480929 - 1) / 103 = 662567776 from by norm_num]
      have h2 : (3 : ZMod 68244480929) ^ 662567776 = ((26019961902 : ℕ) : ZMod 68244480929) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (68244480929 - 1) / 643 = 106134496 from by norm_num]
      have h2 : (3 : ZMod 68244480929) ^ 106134496 = ((24568934322 : ℕ) : ZMod 68244480929) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (68244480929 - 1) / 2477 = 27551264 from by norm_num]
      have h2 : (3 : ZMod 68244480929) ^ 27551264 = ((5377295970 : ℕ) : ZMod 68244480929) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_1214251009 : Nat.Prime 1214251009 := by
  refine lucas_primality 1214251009 (7 : ZMod 1214251009) ?_ (fun q hq hd => ?_)
  · rw [show 1214251009 - 1 = 1214251008 from by norm_num]
    reduce_mod_char
  · have e : 1214251009 - 1 = [2 ^ 21, 3 ^ 1, 193 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1214251009 - 1) / 2 = 607125504 from by norm_num]
      have h2 : (7 : ZMod 1214251009) ^ 607125504 = ((1214251008 : ℕ) : ZMod 1214251009) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1214251009 - 1) / 3 = 404750336 from by norm_num]
      have h2 : (7 : ZMod 1214251009) ^ 404750336 = ((1178454085 : ℕ) : ZMod 1214251009) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (1214251009 - 1) / 193 = 6291456 from by norm_num]
      have h2 : (7 : ZMod 1214251009) ^ 6291456 = ((566651089 : ℕ) : ZMod 1214251009) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_825753601 : Nat.Prime 825753601 := by
  refine lucas_primality 825753601 (23 : ZMod 825753601) ?_ (fun q hq hd => ?_)
  · rw [show 825753601 - 1 = 825753600 from by norm_num]
    reduce_mod_char
  · have e : 825753601 - 1 = [2 ^ 19, 3 ^ 2, 5 ^ 2, 7 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (825753601 - 1) / 2 = 412876800 from by norm_num]
      have h2 : (23 : ZMod 825753601) ^ 412876800 = ((825753600 : ℕ) : ZMod 825753601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (825753601 - 1) / 3 = 275251200 from by norm_num]
      have h2 : (23 : ZMod 825753601) ^ 275251200 = ((769286199 : ℕ) : ZMod 825753601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (825753601 - 1) / 5 = 165150720 from by norm_num]
      have h2 : (23 : ZMod 825753601) ^ 165150720 = ((50952529 : ℕ) : ZMod 825753601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (825753601 - 1) / 7 = 117964800 from by norm_num]
      have h2 : (23 : ZMod 825753601) ^ 117964800 = ((709772069 : ℕ) : ZMod 825753601) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_31065037602817 : Nat.Prime 31065037602817 := by
  refine lucas_primality 31065037602817 (5 : ZMod 31065037602817) ?_ (fun q hq hd => ?_)
  · rw [show 31065037602817 - 1 = 31065037602816 from by norm_num]
    reduce_mod_char
  · have e : 31065037602817 - 1 = [2 ^ 19, 3 ^ 1, 7 ^ 1, 2821517 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (31065037602817 - 1) / 2 = 15532518801408 from by norm_num]
      have h2 : (5 : ZMod 31065037602817) ^ 15532518801408 = ((31065037602816 : ℕ) : ZMod 31065037602817) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (31065037602817 - 1) / 3 = 10355012534272 from by norm_num]
      have h2 : (5 : ZMod 31065037602817) ^ 10355012534272 = ((8563864821674 : ℕ) : ZMod 31065037602817) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (31065037602817 - 1) / 7 = 4437862514688 from by norm_num]
      have h2 : (5 : ZMod 31065037602817) ^ 4437862514688 = ((8857347445025 : ℕ) : ZMod 31065037602817) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (31065037602817 - 1) / 2821517 = 11010048 from by norm_num]
      have h2 : (5 : ZMod 31065037602817) ^ 11010048 = ((23804604093954 : ℕ) : ZMod 31065037602817) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_231828638827 : Nat.Prime 231828638827 := by
  refine lucas_primality 231828638827 (3 : ZMod 231828638827) ?_ (fun q hq hd => ?_)
  · rw [show 231828638827 - 1 = 231828638826 from by norm_num]
    reduce_mod_char
  · have e : 231828638827 - 1 = [2 ^ 1, 3 ^ 1, 29 ^ 1, 139 ^ 1, 2273 ^ 1, 4217 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (231828638827 - 1) / 2 = 115914319413 from by norm_num]
      have h2 : (3 : ZMod 231828638827) ^ 115914319413 = ((231828638826 : ℕ) : ZMod 231828638827) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (231828638827 - 1) / 3 = 77276212942 from by norm_num]
      have h2 : (3 : ZMod 231828638827) ^ 77276212942 = ((220596364139 : ℕ) : ZMod 231828638827) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (231828638827 - 1) / 29 = 7994090994 from by norm_num]
      have h2 : (3 : ZMod 231828638827) ^ 7994090994 = ((105702497580 : ℕ) : ZMod 231828638827) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (231828638827 - 1) / 139 = 1667831934 from by norm_num]
      have h2 : (3 : ZMod 231828638827) ^ 1667831934 = ((89981218114 : ℕ) : ZMod 231828638827) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (231828638827 - 1) / 2273 = 101992362 from by norm_num]
      have h2 : (3 : ZMod 231828638827) ^ 101992362 = ((158396879870 : ℕ) : ZMod 231828638827) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (231828638827 - 1) / 4217 = 54974778 from by norm_num]
      have h2 : (3 : ZMod 231828638827) ^ 54974778 = ((67309039783 : ℕ) : ZMod 231828638827) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

theorem prime_70525124609 : Nat.Prime 70525124609 := by
  refine lucas_primality 70525124609 (3 : ZMod 70525124609) ?_ (fun q hq hd => ?_)
  · rw [show 70525124609 - 1 = 70525124608 from by norm_num]
    reduce_mod_char
  · have e : 70525124609 - 1 = [2 ^ 21, 33629 ^ 1].prod := by norm_num
    rw [e] at hd
    obtain ⟨x, hx, hqx⟩ := (Prime.dvd_prod_iff hq.prime).mp hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (70525124609 - 1) / 2 = 35262562304 from by norm_num]
      have h2 : (3 : ZMod 70525124609) ^ 35262562304 = ((70525124608 : ℕ) : ZMod 70525124609) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)
    · have h1 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp (hq.dvd_of_dvd_pow hqx)
      subst h1
      rw [show (70525124609 - 1) / 33629 = 2097152 from by norm_num]
      have h2 : (3 : ZMod 70525124609) ^ 2097152 = ((41758406289 : ℕ) : ZMod 70525124609) := by
        push_cast
        reduce_mod_char
      rw [h2]
      exact zmod_ne_one (by norm_num)

-- One more simple prime q with 3^i dividing q + 1 joins the 3-adic count.
theorem bud_cons {m j i q : ℕ} {P S : Finset ℕ}
    (h : S ⊆ P ∧ 3 ^ j ∣ (2 ^ m + 1) * ∏ p ∈ S, (p + 1)) (hq : q ∈ P) (hqS : q ∉ S)
    (h3 : 3 ^ i ∣ q + 1) :
    insert q S ⊆ P ∧ 3 ^ (j + i) ∣ (2 ^ m + 1) * ∏ p ∈ insert q S, (p + 1) := by
  refine ⟨Finset.insert_subset hq h.1, ?_⟩
  rw [Finset.prod_insert hqS, pow_add]
  have e1 : (2 ^ m + 1) * ((q + 1) * ∏ p ∈ S, (p + 1)) =
      ((2 ^ m + 1) * ∏ p ∈ S, (p + 1)) * (q + 1) := by ring
  rw [e1]
  exact mul_dvd_mul h.2 h3

-- a an odd multiple of 21 (e = 5): 3^6 divides (2^21 + 1) * prod (p + 1) over p in {5, 11, 17} (2^21+1 -> 5419 -> 5; 2^21+1 -> 43 -> 11; 2^21+1 -> 5419 -> 271 -> 17).
theorem k18e5_d21 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 5) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 5 * ∏ p ∈ P, p)
    (hd : 2 ^ 21 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 5 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g5419 : 5419 ∈ P := S2 5419 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 5419 ∣ 2 ^ 21 + 1).trans hd)
  have g5 : 5 ∈ P := S1 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 5419 g5419 (by norm_num)
  have g43 : 43 ∈ P := S2 43 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 43 ∣ 2 ^ 21 + 1).trans hd)
  have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43 g43 (by norm_num)
  have g271 : 271 ∈ P := S1 271 (by norm_num) (by norm_num) (hnz (by norm_num)) 5419 g5419 (by norm_num)
  have g17 : 17 ∈ P := S1 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 271 g271 (by norm_num)
  have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 2 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
    ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (by norm_num : 3 ^ 2 ∣ 2 ^ 21 + 1).trans hd⟩
  have b1 := bud_cons b0 g5 (by simp) (by norm_num : 3 ^ 1 ∣ 5 + 1)
  have b2 := bud_cons b1 g11 (by simp) (by norm_num : 3 ^ 1 ∣ 11 + 1)
  have b3 := bud_cons b2 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
  exact budget_kernel3 hP h3P E b3.1 ((pow_dvd_pow 3 (by norm_num)).trans b3.2)

-- a an odd multiple of 21 (e = 7): 3^8 divides (2^21 + 1) * prod (p + 1) over p in {5, 11, 137, 17, 23} (2^21+1 -> 5419 -> 5; 2^21+1 -> 43 -> 11; 3^7+1 -> 547 -> 137; 2^21+1 -> 5419 -> 271 -> 17; 3^7+1 -> 547 -> 137 -> 23).
theorem k18e7_d21 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 7) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 7 * ∏ p ∈ P, p)
    (hd : 2 ^ 21 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 7 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g5419 : 5419 ∈ P := S2 5419 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 5419 ∣ 2 ^ 21 + 1).trans hd)
  have g5 : 5 ∈ P := S1 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 5419 g5419 (by norm_num)
  have g43 : 43 ∈ P := S2 43 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 43 ∣ 2 ^ 21 + 1).trans hd)
  have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43 g43 (by norm_num)
  have g547 : 547 ∈ P := S7 547 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g137 : 137 ∈ P := S1 137 (by norm_num) (by norm_num) (hnz (by norm_num)) 547 g547 (by norm_num)
  have g271 : 271 ∈ P := S1 271 (by norm_num) (by norm_num) (hnz (by norm_num)) 5419 g5419 (by norm_num)
  have g17 : 17 ∈ P := S1 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 271 g271 (by norm_num)
  have g23 : 23 ∈ P := S1 23 (by norm_num) (by norm_num) (hnz (by norm_num)) 137 g137 (by norm_num)
  have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 2 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
    ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (by norm_num : 3 ^ 2 ∣ 2 ^ 21 + 1).trans hd⟩
  have b1 := bud_cons b0 g5 (by simp) (by norm_num : 3 ^ 1 ∣ 5 + 1)
  have b2 := bud_cons b1 g11 (by simp) (by norm_num : 3 ^ 1 ∣ 11 + 1)
  have b3 := bud_cons b2 g137 (by simp) (by norm_num : 3 ^ 1 ∣ 137 + 1)
  have b4 := bud_cons b3 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
  have b5 := bud_cons b4 g23 (by simp) (by norm_num : 3 ^ 1 ∣ 23 + 1)
  exact budget_kernel3 hP h3P E b5.1 ((pow_dvd_pow 3 (by norm_num)).trans b5.2)

-- a an odd multiple of 23 (e = 5): 3^6 divides (2^23 + 1) * prod (p + 1) over p in {2796203, 5, 11, 17} (2^23+1 -> 2796203; 2^23+1 -> 2796203 -> 5419 -> 5; 2^23+1 -> 2796203 -> 43 -> 11; 2^23+1 -> 2796203 -> 5419 -> 271 -> 17).
theorem k18e5_d23 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 5) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 5 * ∏ p ∈ P, p)
    (hd : 2 ^ 23 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 5 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2796203 : 2796203 ∈ P := S2 2796203 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 2796203 ∣ 2 ^ 23 + 1).trans hd)
  have g5419 : 5419 ∈ P := S1 5419 (by norm_num) (by norm_num) (hnz (by norm_num)) 2796203 g2796203 (by norm_num)
  have g5 : 5 ∈ P := S1 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 5419 g5419 (by norm_num)
  have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 2796203 g2796203 (by norm_num)
  have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43 g43 (by norm_num)
  have g271 : 271 ∈ P := S1 271 (by norm_num) (by norm_num) (hnz (by norm_num)) 5419 g5419 (by norm_num)
  have g17 : 17 ∈ P := S1 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 271 g271 (by norm_num)
  have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 1 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
    ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (by norm_num : 3 ^ 1 ∣ 2 ^ 23 + 1).trans hd⟩
  have b1 := bud_cons b0 g2796203 (by simp) (by norm_num : 3 ^ 1 ∣ 2796203 + 1)
  have b2 := bud_cons b1 g5 (by simp) (by norm_num : 3 ^ 1 ∣ 5 + 1)
  have b3 := bud_cons b2 g11 (by simp) (by norm_num : 3 ^ 1 ∣ 11 + 1)
  have b4 := bud_cons b3 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
  exact budget_kernel3 hP h3P E b4.1 ((pow_dvd_pow 3 (by norm_num)).trans b4.2)

-- a an odd multiple of 23 (e = 7): 3^8 divides (2^23 + 1) * prod (p + 1) over p in {2796203, 137, 5, 11, 23, 17} (2^23+1 -> 2796203; 3^7+1 -> 547 -> 137; 2^23+1 -> 2796203 -> 5419 -> 5; 2^23+1 -> 2796203 -> 43 -> 11; 3^7+1 -> 547 -> 137 -> 23; 2^23+1 -> 2796203 -> 5419 -> 271 -> 17).
theorem k18e7_d23 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 7) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 7 * ∏ p ∈ P, p)
    (hd : 2 ^ 23 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 7 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2796203 : 2796203 ∈ P := S2 2796203 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 2796203 ∣ 2 ^ 23 + 1).trans hd)
  have g547 : 547 ∈ P := S7 547 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g137 : 137 ∈ P := S1 137 (by norm_num) (by norm_num) (hnz (by norm_num)) 547 g547 (by norm_num)
  have g5419 : 5419 ∈ P := S1 5419 (by norm_num) (by norm_num) (hnz (by norm_num)) 2796203 g2796203 (by norm_num)
  have g5 : 5 ∈ P := S1 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 5419 g5419 (by norm_num)
  have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 2796203 g2796203 (by norm_num)
  have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43 g43 (by norm_num)
  have g23 : 23 ∈ P := S1 23 (by norm_num) (by norm_num) (hnz (by norm_num)) 137 g137 (by norm_num)
  have g271 : 271 ∈ P := S1 271 (by norm_num) (by norm_num) (hnz (by norm_num)) 5419 g5419 (by norm_num)
  have g17 : 17 ∈ P := S1 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 271 g271 (by norm_num)
  have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 1 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
    ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (by norm_num : 3 ^ 1 ∣ 2 ^ 23 + 1).trans hd⟩
  have b1 := bud_cons b0 g2796203 (by simp) (by norm_num : 3 ^ 1 ∣ 2796203 + 1)
  have b2 := bud_cons b1 g137 (by simp) (by norm_num : 3 ^ 1 ∣ 137 + 1)
  have b3 := bud_cons b2 g5 (by simp) (by norm_num : 3 ^ 1 ∣ 5 + 1)
  have b4 := bud_cons b3 g11 (by simp) (by norm_num : 3 ^ 1 ∣ 11 + 1)
  have b5 := bud_cons b4 g23 (by simp) (by norm_num : 3 ^ 1 ∣ 23 + 1)
  have b6 := bud_cons b5 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
  exact budget_kernel3 hP h3P E b6.1 ((pow_dvd_pow 3 (by norm_num)).trans b6.2)

-- a an odd multiple of 31: 5 divides 59 + 1 and 3033169 + 1 (2^31+1 -> 715827883 -> 59; 2^31+1 -> 715827883 -> 3033169).
theorem k18_d31 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 31 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g715827883 : 715827883 ∈ P := S2 715827883 prime_715827883 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 715827883 ∣ 2 ^ 31 + 1).trans hd)
  have g59 : 59 ∈ P := S1 59 (by norm_num) (by norm_num) (hnz (by norm_num)) 715827883 g715827883 (by norm_num)
  have g3033169 : 3033169 ∈ P := S1 3033169 (by norm_num) (by norm_num) (hnz (by norm_num)) 715827883 g715827883 (by norm_num)
  exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 59 g59 3033169 g3033169 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 40: 17 divides 101 + 1 and 10589741 + 1 (2^40+1 -> 4278255361 -> 2139127681 -> 101; 2^40+1 -> 4278255361 -> 2139127681 -> 10589741).
theorem k18_d40 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 40 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g4278255361 : 4278255361 ∈ P := S2 4278255361 prime_4278255361 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 4278255361 ∣ 2 ^ 40 + 1).trans hd)
  have g2139127681 : 2139127681 ∈ P := S1 2139127681 prime_2139127681 (by norm_num) (hnz (by norm_num)) 4278255361 g4278255361 (by norm_num)
  have g101 : 101 ∈ P := S1 101 (by norm_num) (by norm_num) (hnz (by norm_num)) 2139127681 g2139127681 (by norm_num)
  have g10589741 : 10589741 ∈ P := S1 10589741 (by norm_num) (by norm_num) (hnz (by norm_num)) 2139127681 g2139127681 (by norm_num)
  exact absurd (S3 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 101 g101 10589741 g10589741 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 41: 5 divides 59 + 1 and 1069 + 1 (2^41+1 -> 8831418697 -> 252283 -> 59; 2^41+1 -> 8831418697 -> 252283 -> 1069).
theorem k18_d41 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 41 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g8831418697 : 8831418697 ∈ P := S2 8831418697 prime_8831418697 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 8831418697 ∣ 2 ^ 41 + 1).trans hd)
  have g252283 : 252283 ∈ P := S1 252283 (by norm_num) (by norm_num) (hnz (by norm_num)) 8831418697 g8831418697 (by norm_num)
  have g59 : 59 ∈ P := S1 59 (by norm_num) (by norm_num) (hnz (by norm_num)) 252283 g252283 (by norm_num)
  have g1069 : 1069 ∈ P := S1 1069 (by norm_num) (by norm_num) (hnz (by norm_num)) 252283 g252283 (by norm_num)
  exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 59 g59 1069 g1069 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 43: 5 divides 59 + 1 and 1069 + 1 (2^43+1 -> 2932031007403 -> 8831418697 -> 252283 -> 59; 2^43+1 -> 2932031007403 -> 8831418697 -> 252283 -> 1069).
theorem k18_d43 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 43 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2932031007403 : 2932031007403 ∈ P := S2 2932031007403 prime_2932031007403 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 2932031007403 ∣ 2 ^ 43 + 1).trans hd)
  have g8831418697 : 8831418697 ∈ P := S1 8831418697 prime_8831418697 (by norm_num) (hnz (by norm_num)) 2932031007403 g2932031007403 (by norm_num)
  have g252283 : 252283 ∈ P := S1 252283 (by norm_num) (by norm_num) (hnz (by norm_num)) 8831418697 g8831418697 (by norm_num)
  have g59 : 59 ∈ P := S1 59 (by norm_num) (by norm_num) (hnz (by norm_num)) 252283 g252283 (by norm_num)
  have g1069 : 1069 ∈ P := S1 1069 (by norm_num) (by norm_num) (hnz (by norm_num)) 252283 g252283 (by norm_num)
  exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 59 g59 1069 g1069 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 44: 23 divides 2931542417 + 1 and 367 + 1 (2^44+1 -> 2931542417; 2^44+1 -> 2931542417 -> 367).
theorem k18_d44 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 44 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2931542417 : 2931542417 ∈ P := S2 2931542417 prime_2931542417 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 2931542417 ∣ 2 ^ 44 + 1).trans hd)
  have g367 : 367 ∈ P := S1 367 (by norm_num) (by norm_num) (hnz (by norm_num)) 2931542417 g2931542417 (by norm_num)
  exact absurd (S3 23 (by norm_num) (by norm_num) (hnz (by norm_num)) 2931542417 g2931542417 367 g367 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 47: 7^2 divides 165768537521 + 1 (2^47+1 -> 165768537521).
theorem k18_d47 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 47 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g165768537521 : 165768537521 ∈ P := S2 165768537521 prime_165768537521 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 165768537521 ∣ 2 ^ 47 + 1).trans hd)
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 165768537521 g165768537521 (by norm_num)

-- a an odd multiple of 49: 19^2 divides 4363953127297 + 1 (2^49+1 -> 4363953127297).
theorem k18_d49 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 49 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g4363953127297 : 4363953127297 ∈ P := S2 4363953127297 prime_4363953127297 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 4363953127297 ∣ 2 ^ 49 + 1).trans hd)
  exact S6 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 4363953127297 g4363953127297 (by norm_num)

-- a an odd multiple of 53: 5 divides 29 + 1 and 139 + 1 (2^53+1 -> 28059810762433 -> 1275445943747 -> 29; 2^53+1 -> 28059810762433 -> 1275445943747 -> 1221691517 -> 22623917 -> 139).
theorem k18_d53 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 53 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g28059810762433 : 28059810762433 ∈ P := S2 28059810762433 prime_28059810762433 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 28059810762433 ∣ 2 ^ 53 + 1).trans hd)
  have g1275445943747 : 1275445943747 ∈ P := S1 1275445943747 prime_1275445943747 (by norm_num) (hnz (by norm_num)) 28059810762433 g28059810762433 (by norm_num)
  have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 1275445943747 g1275445943747 (by norm_num)
  have g1221691517 : 1221691517 ∈ P := S1 1221691517 prime_1221691517 (by norm_num) (hnz (by norm_num)) 1275445943747 g1275445943747 (by norm_num)
  have g22623917 : 22623917 ∈ P := S1 22623917 (by norm_num) (by norm_num) (hnz (by norm_num)) 1221691517 g1221691517 (by norm_num)
  have g139 : 139 ∈ P := S1 139 (by norm_num) (by norm_num) (hnz (by norm_num)) 22623917 g22623917 (by norm_num)
  exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 29 g29 139 g139 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 58: 5 divides 2^58 + 1 and 107367629 + 1 (2^58+1 -> 107367629).
theorem k18_d58 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 58 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g107367629 : 107367629 ∈ P := S2 107367629 prime_107367629 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 107367629 ∣ 2 ^ 58 + 1).trans hd)
  exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 2 ^ 58 + 1).trans hd) 107367629 g107367629 (by norm_num)

-- a an odd multiple of 61: 5^2 divides 1549 + 1 (2^61+1 -> 768614336404564651 -> 37171 -> 9293 -> 1549).
theorem k18_d61 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 61 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g768614336404564651 : 768614336404564651 ∈ P := S2 768614336404564651 prime_768614336404564651 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 768614336404564651 ∣ 2 ^ 61 + 1).trans hd)
  have g37171 : 37171 ∈ P := S1 37171 (by norm_num) (by norm_num) (hnz (by norm_num)) 768614336404564651 g768614336404564651 (by norm_num)
  have g9293 : 9293 ∈ P := S1 9293 (by norm_num) (by norm_num) (hnz (by norm_num)) 37171 g37171 (by norm_num)
  have g1549 : 1549 ∈ P := S1 1549 (by norm_num) (by norm_num) (hnz (by norm_num)) 9293 g9293 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1549 g1549 (by norm_num)

-- a an odd multiple of 71: 11 divides 131 + 1 and 2243 + 1 (2^71+1 -> 56409643 -> 14102411 -> 131; 2^71+1 -> 56409643 -> 14102411 -> 8971 -> 2243).
theorem k18_d71 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 71 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g56409643 : 56409643 ∈ P := S2 56409643 prime_56409643 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 56409643 ∣ 2 ^ 71 + 1).trans hd)
  have g14102411 : 14102411 ∈ P := S1 14102411 (by norm_num) (by norm_num) (hnz (by norm_num)) 56409643 g56409643 (by norm_num)
  have g131 : 131 ∈ P := S1 131 (by norm_num) (by norm_num) (hnz (by norm_num)) 14102411 g14102411 (by norm_num)
  have g8971 : 8971 ∈ P := S1 8971 (by norm_num) (by norm_num) (hnz (by norm_num)) 14102411 g14102411 (by norm_num)
  have g2243 : 2243 ∈ P := S1 2243 (by norm_num) (by norm_num) (hnz (by norm_num)) 8971 g8971 (by norm_num)
  exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 131 g131 2243 g2243 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 73: 5 divides 439 + 1 and 19 + 1 (2^73+1 -> 1753 -> 877 -> 439; 2^73+1 -> 1795918038741070627 -> 448979509685267657 -> 24943306093625981 -> 151 -> 19).
theorem k18_d73 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 73 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1753 : 1753 ∈ P := S2 1753 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1753 ∣ 2 ^ 73 + 1).trans hd)
  have g877 : 877 ∈ P := S1 877 (by norm_num) (by norm_num) (hnz (by norm_num)) 1753 g1753 (by norm_num)
  have g439 : 439 ∈ P := S1 439 (by norm_num) (by norm_num) (hnz (by norm_num)) 877 g877 (by norm_num)
  have g1795918038741070627 : 1795918038741070627 ∈ P := S2 1795918038741070627 prime_1795918038741070627 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1795918038741070627 ∣ 2 ^ 73 + 1).trans hd)
  have g448979509685267657 : 448979509685267657 ∈ P := S1 448979509685267657 prime_448979509685267657 (by norm_num) (hnz (by norm_num)) 1795918038741070627 g1795918038741070627 (by norm_num)
  have g24943306093625981 : 24943306093625981 ∈ P := S1 24943306093625981 prime_24943306093625981 (by norm_num) (hnz (by norm_num)) 448979509685267657 g448979509685267657 (by norm_num)
  have g151 : 151 ∈ P := S1 151 (by norm_num) (by norm_num) (hnz (by norm_num)) 24943306093625981 g24943306093625981 (by norm_num)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 151 g151 (by norm_num)
  exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 439 g439 19 g19 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 79: 13 divides 78233 + 1 and 103 + 1 (2^79+1 -> 201487636602438195784363 -> 78233; 2^79+1 -> 201487636602438195784363 -> 617 -> 103).
theorem k18_d79 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 79 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g201487636602438195784363 : 201487636602438195784363 ∈ P := S2 201487636602438195784363 prime_201487636602438195784363 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 201487636602438195784363 ∣ 2 ^ 79 + 1).trans hd)
  have g78233 : 78233 ∈ P := S1 78233 (by norm_num) (by norm_num) (hnz (by norm_num)) 201487636602438195784363 g201487636602438195784363 (by norm_num)
  have g617 : 617 ∈ P := S1 617 (by norm_num) (by norm_num) (hnz (by norm_num)) 201487636602438195784363 g201487636602438195784363 (by norm_num)
  have g103 : 103 ∈ P := S1 103 (by norm_num) (by norm_num) (hnz (by norm_num)) 617 g617 (by norm_num)
  exact absurd (S3 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 78233 g78233 103 g103 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 88: 5^2 divides 43872038849 + 1 (2^88+1 -> 43872038849).
theorem k18_d88 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 88 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g43872038849 : 43872038849 ∈ P := S2 43872038849 prime_43872038849 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 43872038849 ∣ 2 ^ 88 + 1).trans hd)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 43872038849 g43872038849 (by norm_num)

-- a an odd multiple of 89: 5 divides 179 + 1 and 2459 + 1 (2^89+1 -> 179; 2^89+1 -> 62020897 -> 2459).
theorem k18_d89 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 89 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g179 : 179 ∈ P := S2 179 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 179 ∣ 2 ^ 89 + 1).trans hd)
  have g62020897 : 62020897 ∈ P := S2 62020897 prime_62020897 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 62020897 ∣ 2 ^ 89 + 1).trans hd)
  have g2459 : 2459 ∈ P := S1 2459 (by norm_num) (by norm_num) (hnz (by norm_num)) 62020897 g62020897 (by norm_num)
  exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 179 g179 2459 g2459 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 92: 11 divides 291280009243618888211558641 + 1 and 48795889 + 1 (2^92+1 -> 291280009243618888211558641; 2^92+1 -> 291280009243618888211558641 -> 97591777 -> 48795889).
theorem k18_d92 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 92 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g291280009243618888211558641 : 291280009243618888211558641 ∈ P := S2 291280009243618888211558641 prime_291280009243618888211558641 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 291280009243618888211558641 ∣ 2 ^ 92 + 1).trans hd)
  have g97591777 : 97591777 ∈ P := S1 97591777 prime_97591777 (by norm_num) (hnz (by norm_num)) 291280009243618888211558641 g291280009243618888211558641 (by norm_num)
  have g48795889 : 48795889 ∈ P := S1 48795889 prime_48795889 (by norm_num) (hnz (by norm_num)) 97591777 g97591777 (by norm_num)
  exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 291280009243618888211558641 g291280009243618888211558641 48795889 g48795889 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 101: 19 divides 845100400152152934331135470251 + 1 and 683 + 1 (2^101+1 -> 845100400152152934331135470251; 2^101+1 -> 845100400152152934331135470251 -> 683).
theorem k18_d101 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 101 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g845100400152152934331135470251 : 845100400152152934331135470251 ∈ P := S2 845100400152152934331135470251 prime_845100400152152934331135470251 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 845100400152152934331135470251 ∣ 2 ^ 101 + 1).trans hd)
  have g683 : 683 ∈ P := S1 683 (by norm_num) (by norm_num) (hnz (by norm_num)) 845100400152152934331135470251 g845100400152152934331135470251 (by norm_num)
  exact absurd (S3 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 845100400152152934331135470251 g845100400152152934331135470251 683 g683 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 103: 7 divides 2729 + 1 and 13 + 1 (2^103+1 -> 8142767081771726171 -> 2729; 2^103+1 -> 8142767081771726171 -> 2729 -> 13).
theorem k18_d103 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 103 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g8142767081771726171 : 8142767081771726171 ∈ P := S2 8142767081771726171 prime_8142767081771726171 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 8142767081771726171 ∣ 2 ^ 103 + 1).trans hd)
  have g2729 : 2729 ∈ P := S1 2729 (by norm_num) (by norm_num) (hnz (by norm_num)) 8142767081771726171 g8142767081771726171 (by norm_num)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 2729 g2729 (by norm_num)
  exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 2729 g2729 13 g13 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 104: 11 divides 43 + 1 and 9864985215783886392970452961 + 1 (2^104+1 -> 257 -> 43; 2^104+1 -> 78919881726271091143763623681 -> 39459940863135545571881811841 -> 19729970431567772785940905921 -> 9864985215783886392970452961).
theorem k18_d104 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 104 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g257 : 257 ∈ P := S2 257 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 257 ∣ 2 ^ 104 + 1).trans hd)
  have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 257 g257 (by norm_num)
  have g78919881726271091143763623681 : 78919881726271091143763623681 ∈ P := S2 78919881726271091143763623681 prime_78919881726271091143763623681 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 78919881726271091143763623681 ∣ 2 ^ 104 + 1).trans hd)
  have g39459940863135545571881811841 : 39459940863135545571881811841 ∈ P := S1 39459940863135545571881811841 prime_39459940863135545571881811841 (by norm_num) (hnz (by norm_num)) 78919881726271091143763623681 g78919881726271091143763623681 (by norm_num)
  have g19729970431567772785940905921 : 19729970431567772785940905921 ∈ P := S1 19729970431567772785940905921 prime_19729970431567772785940905921 (by norm_num) (hnz (by norm_num)) 39459940863135545571881811841 g39459940863135545571881811841 (by norm_num)
  have g9864985215783886392970452961 : 9864985215783886392970452961 ∈ P := S1 9864985215783886392970452961 prime_9864985215783886392970452961 (by norm_num) (hnz (by norm_num)) 19729970431567772785940905921 g19729970431567772785940905921 (by norm_num)
  exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43 g43 9864985215783886392970452961 g9864985215783886392970452961 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 107: 7 divides 643 + 1 and 13 + 1 (2^107+1 -> 643; 2^107+1 -> 84115747449047881488635567801 -> 13).
theorem k18_d107 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 107 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g643 : 643 ∈ P := S2 643 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 643 ∣ 2 ^ 107 + 1).trans hd)
  have g84115747449047881488635567801 : 84115747449047881488635567801 ∈ P := S2 84115747449047881488635567801 prime_84115747449047881488635567801 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 84115747449047881488635567801 ∣ 2 ^ 107 + 1).trans hd)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 84115747449047881488635567801 g84115747449047881488635567801 (by norm_num)
  exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 643 g643 13 g13 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 107 (e = 7): 23 divides 643 + 1 and 137 + 1 (2^107+1 -> 643; 3^7+1 -> 547 -> 137).
theorem k18e7_d107 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 7) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 7 * ∏ p ∈ P, p)
    (hd : 2 ^ 107 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 7 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g643 : 643 ∈ P := S2 643 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 643 ∣ 2 ^ 107 + 1).trans hd)
  have g547 : 547 ∈ P := S7 547 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g137 : 137 ∈ P := S1 137 (by norm_num) (by norm_num) (hnz (by norm_num)) 547 g547 (by norm_num)
  exact absurd (S3 23 (by norm_num) (by norm_num) (hnz (by norm_num)) 643 g643 137 g137 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 109: 5^2 divides 104124649 + 1 (2^109+1 -> 104124649).
theorem k18_d109 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 109 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g104124649 : 104124649 ∈ P := S2 104124649 prime_104124649 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 104124649 ∣ 2 ^ 109 + 1).trans hd)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 104124649 g104124649 (by norm_num)

-- a an odd multiple of 113 (e = 5): 3^7 divides (2^113 + 1) * prod (p + 1) over p in {227, 11, 317, 53} (2^113+1 -> 227; 2^113+1 -> 48817 -> 11; 2^113+1 -> 48817 -> 317; 2^113+1 -> 48817 -> 317 -> 53).
theorem k18e5_d113 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 5) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 5 * ∏ p ∈ P, p)
    (hd : 2 ^ 113 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 5 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g227 : 227 ∈ P := S2 227 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 227 ∣ 2 ^ 113 + 1).trans hd)
  have g48817 : 48817 ∈ P := S2 48817 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 48817 ∣ 2 ^ 113 + 1).trans hd)
  have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 48817 g48817 (by norm_num)
  have g317 : 317 ∈ P := S1 317 (by norm_num) (by norm_num) (hnz (by norm_num)) 48817 g48817 (by norm_num)
  have g53 : 53 ∈ P := S1 53 (by norm_num) (by norm_num) (hnz (by norm_num)) 317 g317 (by norm_num)
  have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 1 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
    ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (by norm_num : 3 ^ 1 ∣ 2 ^ 113 + 1).trans hd⟩
  have b1 := bud_cons b0 g227 (by simp) (by norm_num : 3 ^ 1 ∣ 227 + 1)
  have b2 := bud_cons b1 g11 (by simp) (by norm_num : 3 ^ 1 ∣ 11 + 1)
  have b3 := bud_cons b2 g317 (by simp) (by norm_num : 3 ^ 1 ∣ 317 + 1)
  have b4 := bud_cons b3 g53 (by simp) (by norm_num : 3 ^ 3 ∣ 53 + 1)
  exact budget_kernel3 hP h3P E b4.1 ((pow_dvd_pow 3 (by norm_num)).trans b4.2)

-- a an odd multiple of 113: 7 divides 48817 + 1 and 636190001 + 1 (2^113+1 -> 48817; 2^113+1 -> 636190001).
theorem k18_d113 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 113 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g48817 : 48817 ∈ P := S2 48817 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 48817 ∣ 2 ^ 113 + 1).trans hd)
  have g636190001 : 636190001 ∈ P := S2 636190001 prime_636190001 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 636190001 ∣ 2 ^ 113 + 1).trans hd)
  exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 48817 g48817 636190001 g636190001 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 127: 13^2 divides 1013 + 1 (2^127+1 -> 56713727820156410577229101238628035243 -> 4051 -> 1013).
theorem k18_d127 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 127 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g56713727820156410577229101238628035243 : 56713727820156410577229101238628035243 ∈ P := S2 56713727820156410577229101238628035243 prime_56713727820156410577229101238628035243 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 56713727820156410577229101238628035243 ∣ 2 ^ 127 + 1).trans hd)
  have g4051 : 4051 ∈ P := S1 4051 (by norm_num) (by norm_num) (hnz (by norm_num)) 56713727820156410577229101238628035243 g56713727820156410577229101238628035243 (by norm_num)
  have g1013 : 1013 ∈ P := S1 1013 (by norm_num) (by norm_num) (hnz (by norm_num)) 4051 g4051 (by norm_num)
  exact S6 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 1013 g1013 (by norm_num)

-- a an odd multiple of 128: 23 divides 367 + 1 and 240073 + 1 (2^128+1 -> 59649589127497217 -> 733 -> 367; 2^128+1 -> 59649589127497217 -> 13562889751591 -> 1440437 -> 240073).
theorem k18_d128 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 128 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g59649589127497217 : 59649589127497217 ∈ P := S2 59649589127497217 prime_59649589127497217 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 59649589127497217 ∣ 2 ^ 128 + 1).trans hd)
  have g733 : 733 ∈ P := S1 733 (by norm_num) (by norm_num) (hnz (by norm_num)) 59649589127497217 g59649589127497217 (by norm_num)
  have g367 : 367 ∈ P := S1 367 (by norm_num) (by norm_num) (hnz (by norm_num)) 733 g733 (by norm_num)
  have g13562889751591 : 13562889751591 ∈ P := S1 13562889751591 prime_13562889751591 (by norm_num) (hnz (by norm_num)) 59649589127497217 g59649589127497217 (by norm_num)
  have g1440437 : 1440437 ∈ P := S1 1440437 (by norm_num) (by norm_num) (hnz (by norm_num)) 13562889751591 g13562889751591 (by norm_num)
  have g240073 : 240073 ∈ P := S1 240073 (by norm_num) (by norm_num) (hnz (by norm_num)) 1440437 g1440437 (by norm_num)
  exact absurd (S3 23 (by norm_num) (by norm_num) (hnz (by norm_num)) 367 g367 240073 g240073 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 136 (e = 5): 3^6 divides (2^136 + 1) * prod (p + 1) over p in {257, 113, 1697, 11, 71} (2^136+1 -> 257; 2^136+1 -> 383521 -> 113; 2^136+1 -> 383521 -> 1697; 2^136+1 -> 257 -> 43 -> 11; 2^136+1 -> 383521 -> 1697 -> 283 -> 71).
theorem k18e5_d136 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 5) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 5 * ∏ p ∈ P, p)
    (hd : 2 ^ 136 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 5 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g257 : 257 ∈ P := S2 257 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 257 ∣ 2 ^ 136 + 1).trans hd)
  have g383521 : 383521 ∈ P := S2 383521 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 383521 ∣ 2 ^ 136 + 1).trans hd)
  have g113 : 113 ∈ P := S1 113 (by norm_num) (by norm_num) (hnz (by norm_num)) 383521 g383521 (by norm_num)
  have g1697 : 1697 ∈ P := S1 1697 (by norm_num) (by norm_num) (hnz (by norm_num)) 383521 g383521 (by norm_num)
  have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 257 g257 (by norm_num)
  have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43 g43 (by norm_num)
  have g283 : 283 ∈ P := S1 283 (by norm_num) (by norm_num) (hnz (by norm_num)) 1697 g1697 (by norm_num)
  have g71 : 71 ∈ P := S1 71 (by norm_num) (by norm_num) (hnz (by norm_num)) 283 g283 (by norm_num)
  have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 0 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
    ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (by norm_num : 3 ^ 0 ∣ 2 ^ 136 + 1).trans hd⟩
  have b1 := bud_cons b0 g257 (by simp) (by norm_num : 3 ^ 1 ∣ 257 + 1)
  have b2 := bud_cons b1 g113 (by simp) (by norm_num : 3 ^ 1 ∣ 113 + 1)
  have b3 := bud_cons b2 g1697 (by simp) (by norm_num : 3 ^ 1 ∣ 1697 + 1)
  have b4 := bud_cons b3 g11 (by simp) (by norm_num : 3 ^ 1 ∣ 11 + 1)
  have b5 := bud_cons b4 g71 (by simp) (by norm_num : 3 ^ 2 ∣ 71 + 1)
  exact budget_kernel3 hP h3P E b5.1 ((pow_dvd_pow 3 (by norm_num)).trans b5.2)

-- a an odd multiple of 136: 11 divides 43 + 1 and 2221 + 1 (2^136+1 -> 257 -> 43; 2^136+1 -> 2368179743873 -> 4441 -> 2221).
theorem k18_d136 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 136 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g257 : 257 ∈ P := S2 257 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 257 ∣ 2 ^ 136 + 1).trans hd)
  have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 257 g257 (by norm_num)
  have g2368179743873 : 2368179743873 ∈ P := S2 2368179743873 prime_2368179743873 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 2368179743873 ∣ 2 ^ 136 + 1).trans hd)
  have g4441 : 4441 ∈ P := S1 4441 (by norm_num) (by norm_num) (hnz (by norm_num)) 2368179743873 g2368179743873 (by norm_num)
  have g2221 : 2221 ∈ P := S1 2221 (by norm_num) (by norm_num) (hnz (by norm_num)) 4441 g4441 (by norm_num)
  exact absurd (S3 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43 g43 2221 g2221 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 137 (e = 5): 61 divides 3^5 + 1 and 1097 + 1 (2^137+1 -> 1097).
theorem k18e5_d137 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 5) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 5 * ∏ p ∈ P, p)
    (hd : 2 ^ 137 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 5 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1097 : 1097 ∈ P := S2 1097 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1097 ∣ 2 ^ 137 + 1).trans hd)
  exact S8 61 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num) 1097 g1097 (by norm_num)

-- a an odd multiple of 137 (e = 7): 3^8 divides (2^137 + 1) * prod (p + 1) over p in {1097, 5, 11, 71, 137} (2^137+1 -> 1097; 2^137+1 -> 15619 -> 5; 2^137+1 -> 15619 -> 11; 2^137+1 -> 15619 -> 71; 3^7+1 -> 547 -> 137).
theorem k18e7_d137 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 7) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 7 * ∏ p ∈ P, p)
    (hd : 2 ^ 137 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 7 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1097 : 1097 ∈ P := S2 1097 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1097 ∣ 2 ^ 137 + 1).trans hd)
  have g15619 : 15619 ∈ P := S2 15619 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 15619 ∣ 2 ^ 137 + 1).trans hd)
  have g5 : 5 ∈ P := S1 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 15619 g15619 (by norm_num)
  have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 15619 g15619 (by norm_num)
  have g71 : 71 ∈ P := S1 71 (by norm_num) (by norm_num) (hnz (by norm_num)) 15619 g15619 (by norm_num)
  have g547 : 547 ∈ P := S7 547 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g137 : 137 ∈ P := S1 137 (by norm_num) (by norm_num) (hnz (by norm_num)) 547 g547 (by norm_num)
  have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 1 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
    ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (by norm_num : 3 ^ 1 ∣ 2 ^ 137 + 1).trans hd⟩
  have b1 := bud_cons b0 g1097 (by simp) (by norm_num : 3 ^ 2 ∣ 1097 + 1)
  have b2 := bud_cons b1 g5 (by simp) (by norm_num : 3 ^ 1 ∣ 5 + 1)
  have b3 := bud_cons b2 g11 (by simp) (by norm_num : 3 ^ 1 ∣ 11 + 1)
  have b4 := bud_cons b3 g71 (by simp) (by norm_num : 3 ^ 2 ∣ 71 + 1)
  have b5 := bud_cons b4 g137 (by simp) (by norm_num : 3 ^ 1 ∣ 137 + 1)
  exact budget_kernel3 hP h3P E b5.1 ((pow_dvd_pow 3 (by norm_num)).trans b5.2)

-- a an odd multiple of 139 (e = 5): 3^7 divides (2^139 + 1) * prod (p + 1) over p in {17, 71, 467} (2^139+1 -> 4506937 -> 17; 2^139+1 -> 4506937 -> 71; 2^139+1 -> 4506937 -> 1867 -> 467).
theorem k18e5_d139 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 5) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 5 * ∏ p ∈ P, p)
    (hd : 2 ^ 139 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 5 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g4506937 : 4506937 ∈ P := S2 4506937 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 4506937 ∣ 2 ^ 139 + 1).trans hd)
  have g17 : 17 ∈ P := S1 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 4506937 g4506937 (by norm_num)
  have g71 : 71 ∈ P := S1 71 (by norm_num) (by norm_num) (hnz (by norm_num)) 4506937 g4506937 (by norm_num)
  have g1867 : 1867 ∈ P := S1 1867 (by norm_num) (by norm_num) (hnz (by norm_num)) 4506937 g4506937 (by norm_num)
  have g467 : 467 ∈ P := S1 467 (by norm_num) (by norm_num) (hnz (by norm_num)) 1867 g1867 (by norm_num)
  have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 1 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
    ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (by norm_num : 3 ^ 1 ∣ 2 ^ 139 + 1).trans hd⟩
  have b1 := bud_cons b0 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
  have b2 := bud_cons b1 g71 (by simp) (by norm_num : 3 ^ 2 ∣ 71 + 1)
  have b3 := bud_cons b2 g467 (by simp) (by norm_num : 3 ^ 2 ∣ 467 + 1)
  exact budget_kernel3 hP h3P E b3.1 ((pow_dvd_pow 3 (by norm_num)).trans b3.2)

-- a an odd multiple of 139 (e = 7): 3^9 divides (2^139 + 1) * prod (p + 1) over p in {17, 71, 137, 23, 467} (2^139+1 -> 4506937 -> 17; 2^139+1 -> 4506937 -> 71; 3^7+1 -> 547 -> 137; 3^7+1 -> 547 -> 137 -> 23; 2^139+1 -> 4506937 -> 1867 -> 467).
theorem k18e7_d139 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 7) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 7 * ∏ p ∈ P, p)
    (hd : 2 ^ 139 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 7 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g4506937 : 4506937 ∈ P := S2 4506937 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 4506937 ∣ 2 ^ 139 + 1).trans hd)
  have g17 : 17 ∈ P := S1 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 4506937 g4506937 (by norm_num)
  have g71 : 71 ∈ P := S1 71 (by norm_num) (by norm_num) (hnz (by norm_num)) 4506937 g4506937 (by norm_num)
  have g547 : 547 ∈ P := S7 547 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g137 : 137 ∈ P := S1 137 (by norm_num) (by norm_num) (hnz (by norm_num)) 547 g547 (by norm_num)
  have g23 : 23 ∈ P := S1 23 (by norm_num) (by norm_num) (hnz (by norm_num)) 137 g137 (by norm_num)
  have g1867 : 1867 ∈ P := S1 1867 (by norm_num) (by norm_num) (hnz (by norm_num)) 4506937 g4506937 (by norm_num)
  have g467 : 467 ∈ P := S1 467 (by norm_num) (by norm_num) (hnz (by norm_num)) 1867 g1867 (by norm_num)
  have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 1 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
    ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (by norm_num : 3 ^ 1 ∣ 2 ^ 139 + 1).trans hd⟩
  have b1 := bud_cons b0 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
  have b2 := bud_cons b1 g71 (by simp) (by norm_num : 3 ^ 2 ∣ 71 + 1)
  have b3 := bud_cons b2 g137 (by simp) (by norm_num : 3 ^ 1 ∣ 137 + 1)
  have b4 := bud_cons b3 g23 (by simp) (by norm_num : 3 ^ 1 ∣ 23 + 1)
  have b5 := bud_cons b4 g467 (by simp) (by norm_num : 3 ^ 2 ∣ 467 + 1)
  exact budget_kernel3 hP h3P E b5.1 ((pow_dvd_pow 3 (by norm_num)).trans b5.2)

-- a an odd multiple of 148: 5^2 divides 4192399 + 1 (2^148+1 -> 20988936657440586486151264256610222593863921 -> 212480658612043 -> 4192399).
theorem k18_d148 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 148 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g20988936657440586486151264256610222593863921 : 20988936657440586486151264256610222593863921 ∈ P := S2 20988936657440586486151264256610222593863921 prime_20988936657440586486151264256610222593863921 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 20988936657440586486151264256610222593863921 ∣ 2 ^ 148 + 1).trans hd)
  have g212480658612043 : 212480658612043 ∈ P := S1 212480658612043 prime_212480658612043 (by norm_num) (hnz (by norm_num)) 20988936657440586486151264256610222593863921 g20988936657440586486151264256610222593863921 (by norm_num)
  have g4192399 : 4192399 ∈ P := S1 4192399 (by norm_num) (by norm_num) (hnz (by norm_num)) 212480658612043 g212480658612043 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 4192399 g4192399 (by norm_num)

-- a an odd multiple of 151: 7^2 divides 2351 + 1 (2^151+1 -> 18717738334417 -> 2351).
theorem k18_d151 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 151 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g18717738334417 : 18717738334417 ∈ P := S2 18717738334417 prime_18717738334417 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 18717738334417 ∣ 2 ^ 151 + 1).trans hd)
  have g2351 : 2351 ∈ P := S1 2351 (by norm_num) (by norm_num) (hnz (by norm_num)) 18717738334417 g18717738334417 (by norm_num)
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 2351 g2351 (by norm_num)

-- a an odd multiple of 158: 5 divides 2^158 + 1 and 19 + 1 (2^158+1 -> 604462909806215075725313 -> 19).
theorem k18_d158 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 158 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g604462909806215075725313 : 604462909806215075725313 ∈ P := S2 604462909806215075725313 prime_604462909806215075725313 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 604462909806215075725313 ∣ 2 ^ 158 + 1).trans hd)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 604462909806215075725313 g604462909806215075725313 (by norm_num)
  exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 2 ^ 158 + 1).trans hd) 19 g19 (by norm_num)

-- a an odd multiple of 163: 5 divides 1023398150341859 + 1 and 170579 + 1 (2^163+1 -> 1023398150341859; 2^163+1 -> 1023398150341859 -> 170579).
theorem k18_d163 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 163 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1023398150341859 : 1023398150341859 ∈ P := S2 1023398150341859 prime_1023398150341859 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1023398150341859 ∣ 2 ^ 163 + 1).trans hd)
  have g170579 : 170579 ∈ P := S1 170579 (by norm_num) (by norm_num) (hnz (by norm_num)) 1023398150341859 g1023398150341859 (by norm_num)
  exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1023398150341859 g1023398150341859 170579 g170579 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 164 (e = 5): 3^10 divides (2^164 + 1) * prod (p + 1) over p in {17, 13121} (2^164+1 -> 17; 2^164+1 -> 13121).
theorem k18e5_d164 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 5) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 5 * ∏ p ∈ P, p)
    (hd : 2 ^ 164 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 5 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g17 : 17 ∈ P := S2 17 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 17 ∣ 2 ^ 164 + 1).trans hd)
  have g13121 : 13121 ∈ P := S2 13121 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 13121 ∣ 2 ^ 164 + 1).trans hd)
  have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 0 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
    ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (by norm_num : 3 ^ 0 ∣ 2 ^ 164 + 1).trans hd⟩
  have b1 := bud_cons b0 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
  have b2 := bud_cons b1 g13121 (by simp) (by norm_num : 3 ^ 8 ∣ 13121 + 1)
  exact budget_kernel3 hP h3P E b2.1 ((pow_dvd_pow 3 (by norm_num)).trans b2.2)

-- a an odd multiple of 164 (e = 7): 3^10 divides (2^164 + 1) * prod (p + 1) over p in {17, 13121} (2^164+1 -> 17; 2^164+1 -> 13121).
theorem k18e7_d164 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 7) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 7 * ∏ p ∈ P, p)
    (hd : 2 ^ 164 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 7 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g17 : 17 ∈ P := S2 17 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 17 ∣ 2 ^ 164 + 1).trans hd)
  have g13121 : 13121 ∈ P := S2 13121 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 13121 ∣ 2 ^ 164 + 1).trans hd)
  have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 0 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
    ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (by norm_num : 3 ^ 0 ∣ 2 ^ 164 + 1).trans hd⟩
  have b1 := bud_cons b0 g17 (by simp) (by norm_num : 3 ^ 2 ∣ 17 + 1)
  have b2 := bud_cons b1 g13121 (by simp) (by norm_num : 3 ^ 8 ∣ 13121 + 1)
  exact budget_kernel3 hP h3P E b2.1 ((pow_dvd_pow 3 (by norm_num)).trans b2.2)

-- a an odd multiple of 166: 5^2 divides 499 + 1 (2^166+1 -> 997 -> 499).
theorem k18_d166 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 166 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g997 : 997 ∈ P := S2 997 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 997 ∣ 2 ^ 166 + 1).trans hd)
  have g499 : 499 ∈ P := S1 499 (by norm_num) (by norm_num) (hnz (by norm_num)) 997 g997 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 499 g499 (by norm_num)

-- a an odd multiple of 167: 11^2 divides 62357403192785191176690552862561408838653121833643 + 1 (2^167+1 -> 62357403192785191176690552862561408838653121833643).
theorem k18_d167 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 167 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g62357403192785191176690552862561408838653121833643 : 62357403192785191176690552862561408838653121833643 ∈ P := S2 62357403192785191176690552862561408838653121833643 prime_62357403192785191176690552862561408838653121833643 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 62357403192785191176690552862561408838653121833643 ∣ 2 ^ 167 + 1).trans hd)
  exact S6 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 62357403192785191176690552862561408838653121833643 g62357403192785191176690552862561408838653121833643 (by norm_num)

-- a an odd multiple of 169: 5 divides 1050705618973489 + 1 and 59 + 1 (2^169+1 -> 4929910764223610387 -> 1050705618973489; 2^169+1 -> 4929910764223610387 -> 1050705618973489 -> 59).
theorem k18_d169 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 169 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g4929910764223610387 : 4929910764223610387 ∈ P := S2 4929910764223610387 prime_4929910764223610387 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 4929910764223610387 ∣ 2 ^ 169 + 1).trans hd)
  have g1050705618973489 : 1050705618973489 ∈ P := S1 1050705618973489 prime_1050705618973489 (by norm_num) (hnz (by norm_num)) 4929910764223610387 g4929910764223610387 (by norm_num)
  have g59 : 59 ∈ P := S1 59 (by norm_num) (by norm_num) (hnz (by norm_num)) 1050705618973489 g1050705618973489 (by norm_num)
  exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1050705618973489 g1050705618973489 59 g59 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 172: 17 divides 2^172 + 1 and 517207 + 1 (2^172+1 -> 3855260977 -> 517207).
theorem k18_d172 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 172 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g3855260977 : 3855260977 ∈ P := S2 3855260977 prime_3855260977 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 3855260977 ∣ 2 ^ 172 + 1).trans hd)
  have g517207 : 517207 ∈ P := S1 517207 (by norm_num) (by norm_num) (hnz (by norm_num)) 3855260977 g3855260977 (by norm_num)
  exact S4 17 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 17 ∣ 2 ^ 172 + 1).trans hd) 517207 g517207 (by norm_num)

-- a an odd multiple of 173 (e = 5): 31 divides 4153 + 1 and 61 + 1 (2^173+1 -> 4153; 3^5+1 -> 61).
theorem k18e5_d173 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 5) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 5 * ∏ p ∈ P, p)
    (hd : 2 ^ 173 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 5 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g4153 : 4153 ∈ P := S2 4153 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 4153 ∣ 2 ^ 173 + 1).trans hd)
  have g61 : 61 ∈ P := S7 61 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  exact absurd (S3 31 (by norm_num) (by norm_num) (hnz (by norm_num)) 4153 g4153 61 g61 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 173: 29 divides 347 + 1 and 47635010587 + 1 (2^173+1 -> 347; 2^173+1 -> 47635010587).
theorem k18_d173 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 173 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g347 : 347 ∈ P := S2 347 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 347 ∣ 2 ^ 173 + 1).trans hd)
  have g47635010587 : 47635010587 ∈ P := S2 47635010587 prime_47635010587 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 47635010587 ∣ 2 ^ 173 + 1).trans hd)
  exact absurd (S3 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 347 g347 47635010587 g47635010587 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 178: 5 divides 2^178 + 1 and 1069 + 1 (2^178+1 -> 1069).
theorem k18_d178 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 178 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1069 : 1069 ∈ P := S2 1069 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1069 ∣ 2 ^ 178 + 1).trans hd)
  exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 2 ^ 178 + 1).trans hd) 1069 g1069 (by norm_num)

-- a an odd multiple of 179: 5^2 divides 199 + 1 (2^179+1 -> 58745093521 -> 126457 -> 1193 -> 199).
theorem k18_d179 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 179 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g58745093521 : 58745093521 ∈ P := S2 58745093521 prime_58745093521 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 58745093521 ∣ 2 ^ 179 + 1).trans hd)
  have g126457 : 126457 ∈ P := S1 126457 (by norm_num) (by norm_num) (hnz (by norm_num)) 58745093521 g58745093521 (by norm_num)
  have g1193 : 1193 ∈ P := S1 1193 (by norm_num) (by norm_num) (hnz (by norm_num)) 126457 g126457 (by norm_num)
  have g199 : 199 ∈ P := S1 199 (by norm_num) (by norm_num) (hnz (by norm_num)) 1193 g1193 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 199 g199 (by norm_num)

-- a an odd multiple of 181: 7^2 divides 31675363 + 1 (2^181+1 -> 31675363).
theorem k18_d181 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 181 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g31675363 : 31675363 ∈ P := S2 31675363 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 31675363 ∣ 2 ^ 181 + 1).trans hd)
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 31675363 g31675363 (by norm_num)

-- a an odd multiple of 184: 17 divides 43717618369 + 1 and 67 + 1 (2^184+1 -> 43717618369; 2^184+1 -> 43717618369 -> 937 -> 67).
theorem k18_d184 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 184 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g43717618369 : 43717618369 ∈ P := S2 43717618369 prime_43717618369 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 43717618369 ∣ 2 ^ 184 + 1).trans hd)
  have g937 : 937 ∈ P := S1 937 (by norm_num) (by norm_num) (hnz (by norm_num)) 43717618369 g43717618369 (by norm_num)
  have g67 : 67 ∈ P := S1 67 (by norm_num) (by norm_num) (hnz (by norm_num)) 937 g937 (by norm_num)
  exact absurd (S3 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 43717618369 g43717618369 67 g67 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 188: 17 divides 2^188 + 1 and 3739 + 1 (2^188+1 -> 23592342593 -> 7477 -> 3739).
theorem k18_d188 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 188 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g23592342593 : 23592342593 ∈ P := S2 23592342593 prime_23592342593 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 23592342593 ∣ 2 ^ 188 + 1).trans hd)
  have g7477 : 7477 ∈ P := S1 7477 (by norm_num) (by norm_num) (hnz (by norm_num)) 23592342593 g23592342593 (by norm_num)
  have g3739 : 3739 ∈ P := S1 3739 (by norm_num) (by norm_num) (hnz (by norm_num)) 7477 g7477 (by norm_num)
  exact S4 17 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 17 ∣ 2 ^ 188 + 1).trans hd) 3739 g3739 (by norm_num)

-- a an odd multiple of 191: 19 divides 1046183622564446793972631570534611069350392574077339085483 + 1 and 379 + 1 (2^191+1 -> 1046183622564446793972631570534611069350392574077339085483; 2^191+1 -> 1046183622564446793972631570534611069350392574077339085483 -> 379).
theorem k18_d191 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 191 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1046183622564446793972631570534611069350392574077339085483 : 1046183622564446793972631570534611069350392574077339085483 ∈ P := S2 1046183622564446793972631570534611069350392574077339085483 prime_1046183622564446793972631570534611069350392574077339085483 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1046183622564446793972631570534611069350392574077339085483 ∣ 2 ^ 191 + 1).trans hd)
  have g379 : 379 ∈ P := S1 379 (by norm_num) (by norm_num) (hnz (by norm_num)) 1046183622564446793972631570534611069350392574077339085483 g1046183622564446793972631570534611069350392574077339085483 (by norm_num)
  exact absurd (S3 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 1046183622564446793972631570534611069350392574077339085483 g1046183622564446793972631570534611069350392574077339085483 379 g379 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 193 (e = 5): 31 divides 35679139 + 1 and 61 + 1 (2^193+1 -> 35679139; 3^5+1 -> 61).
theorem k18e5_d193 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 5) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 5 * ∏ p ∈ P, p)
    (hd : 2 ^ 193 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 5 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g35679139 : 35679139 ∈ P := S2 35679139 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 35679139 ∣ 2 ^ 193 + 1).trans hd)
  have g61 : 61 ∈ P := S7 61 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  exact absurd (S3 31 (by norm_num) (by norm_num) (hnz (by norm_num)) 35679139 g35679139 61 g61 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 193 (e = 7): 547 divides 3^7 + 1 and 6563 + 1 (2^193+1 -> 6563).
theorem k18e7_d193 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 7) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 7 * ∏ p ∈ P, p)
    (hd : 2 ^ 193 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 7 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g6563 : 6563 ∈ P := S2 6563 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 6563 ∣ 2 ^ 193 + 1).trans hd)
  exact S8 547 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num) 6563 g6563 (by norm_num)

-- a an odd multiple of 194: 5 divides 2^194 + 1 and 389 + 1 (2^194+1 -> 389).
theorem k18_d194 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 194 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g389 : 389 ∈ P := S2 389 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 389 ∣ 2 ^ 194 + 1).trans hd)
  exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 2 ^ 194 + 1).trans hd) 389 g389 (by norm_num)

-- a an odd multiple of 197: 5^2 divides 197002597249 + 1 (2^197+1 -> 197002597249).
theorem k18_d197 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 197 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g197002597249 : 197002597249 ∈ P := S2 197002597249 prime_197002597249 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 197002597249 ∣ 2 ^ 197 + 1).trans hd)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 197002597249 g197002597249 (by norm_num)

-- a an odd multiple of 199: 5^2 divides 197002597249 + 1 (2^199+1 -> 267823007376498379256993682056860433753700498963798805883563 -> 197002597249).
theorem k18_d199 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 199 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g267823007376498379256993682056860433753700498963798805883563 : 267823007376498379256993682056860433753700498963798805883563 ∈ P := S2 267823007376498379256993682056860433753700498963798805883563 prime_267823007376498379256993682056860433753700498963798805883563 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 267823007376498379256993682056860433753700498963798805883563 ∣ 2 ^ 199 + 1).trans hd)
  have g197002597249 : 197002597249 ∈ P := S1 197002597249 prime_197002597249 (by norm_num) (hnz (by norm_num)) 267823007376498379256993682056860433753700498963798805883563 g267823007376498379256993682056860433753700498963798805883563 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 197002597249 g197002597249 (by norm_num)

-- a an odd multiple of 202: 5 divides 2^202 + 1 and 809 + 1 (2^202+1 -> 809).
theorem k18_d202 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 202 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g809 : 809 ∈ P := S2 809 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 809 ∣ 2 ^ 202 + 1).trans hd)
  exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 2 ^ 202 + 1).trans hd) 809 g809 (by norm_num)

-- a an odd multiple of 206: 7 divides 41201 + 1 and 17325013 + 1 (2^206+1 -> 41201; 2^206+1 -> 17325013).
theorem k18_d206 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 206 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g41201 : 41201 ∈ P := S2 41201 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 41201 ∣ 2 ^ 206 + 1).trans hd)
  have g17325013 : 17325013 ∈ P := S2 17325013 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 17325013 ∣ 2 ^ 206 + 1).trans hd)
  exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 41201 g41201 17325013 g17325013 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 211 (e = 5): 3^6 divides (2^211 + 1) * prod (p + 1) over p in {4643, 9878177, 23} (2^211+1 -> 4643; 2^211+1 -> 9878177; 2^211+1 -> 9878177 -> 23).
theorem k18e5_d211 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 5) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 5 * ∏ p ∈ P, p)
    (hd : 2 ^ 211 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 5 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g4643 : 4643 ∈ P := S2 4643 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 4643 ∣ 2 ^ 211 + 1).trans hd)
  have g9878177 : 9878177 ∈ P := S2 9878177 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 9878177 ∣ 2 ^ 211 + 1).trans hd)
  have g23 : 23 ∈ P := S1 23 (by norm_num) (by norm_num) (hnz (by norm_num)) 9878177 g9878177 (by norm_num)
  have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 1 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
    ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (by norm_num : 3 ^ 1 ∣ 2 ^ 211 + 1).trans hd⟩
  have b1 := bud_cons b0 g4643 (by simp) (by norm_num : 3 ^ 3 ∣ 4643 + 1)
  have b2 := bud_cons b1 g9878177 (by simp) (by norm_num : 3 ^ 1 ∣ 9878177 + 1)
  have b3 := bud_cons b2 g23 (by simp) (by norm_num : 3 ^ 1 ∣ 23 + 1)
  exact budget_kernel3 hP h3P E b3.1 ((pow_dvd_pow 3 (by norm_num)).trans b3.2)

-- a an odd multiple of 211 (e = 7): 23 divides 9878177 + 1 and 137 + 1 (2^211+1 -> 9878177; 3^7+1 -> 547 -> 137).
theorem k18e7_d211 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 7) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 7 * ∏ p ∈ P, p)
    (hd : 2 ^ 211 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 7 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g9878177 : 9878177 ∈ P := S2 9878177 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 9878177 ∣ 2 ^ 211 + 1).trans hd)
  have g547 : 547 ∈ P := S7 547 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g137 : 137 ∈ P := S1 137 (by norm_num) (by norm_num) (hnz (by norm_num)) 547 g547 (by norm_num)
  exact absurd (S3 23 (by norm_num) (by norm_num) (hnz (by norm_num)) 9878177 g9878177 137 g137 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 212: 17 divides 2^212 + 1 and 20946001591429012199281424246257 + 1 (2^212+1 -> 20946001591429012199281424246257).
theorem k18_d212 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 212 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g20946001591429012199281424246257 : 20946001591429012199281424246257 ∈ P := S2 20946001591429012199281424246257 prime_20946001591429012199281424246257 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 20946001591429012199281424246257 ∣ 2 ^ 212 + 1).trans hd)
  exact S4 17 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 17 ∣ 2 ^ 212 + 1).trans hd) 20946001591429012199281424246257 g20946001591429012199281424246257 (by norm_num)

-- a an odd multiple of 214: 5 divides 2^214 + 1 and 843589 + 1 (2^214+1 -> 843589).
theorem k18_d214 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 214 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g843589 : 843589 ∈ P := S2 843589 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 843589 ∣ 2 ^ 214 + 1).trans hd)
  exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 2 ^ 214 + 1).trans hd) 843589 g843589 (by norm_num)

-- a an odd multiple of 218: 5 divides 2^218 + 1 and 5669 + 1 (2^218+1 -> 5669).
theorem k18_d218 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 218 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g5669 : 5669 ∈ P := S2 5669 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 5669 ∣ 2 ^ 218 + 1).trans hd)
  exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 2 ^ 218 + 1).trans hd) 5669 g5669 (by norm_num)

-- a an odd multiple of 223: 5 divides 2030149279 + 1 and 6269 + 1 (2^223+1 -> 219256122131 -> 2030149279; 2^223+1 -> 219256122131 -> 2030149279 -> 551671 -> 6269).
theorem k18_d223 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 223 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g219256122131 : 219256122131 ∈ P := S2 219256122131 prime_219256122131 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 219256122131 ∣ 2 ^ 223 + 1).trans hd)
  have g2030149279 : 2030149279 ∈ P := S1 2030149279 prime_2030149279 (by norm_num) (hnz (by norm_num)) 219256122131 g219256122131 (by norm_num)
  have g551671 : 551671 ∈ P := S1 551671 (by norm_num) (by norm_num) (hnz (by norm_num)) 2030149279 g2030149279 (by norm_num)
  have g6269 : 6269 ∈ P := S1 6269 (by norm_num) (by norm_num) (hnz (by norm_num)) 551671 g551671 (by norm_num)
  exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 2030149279 g2030149279 6269 g6269 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 226: 5 divides 2^226 + 1 and 58309 + 1 (2^226+1 -> 58309).
theorem k18_d226 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 226 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g58309 : 58309 ∈ P := S2 58309 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 58309 ∣ 2 ^ 226 + 1).trans hd)
  exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 2 ^ 226 + 1).trans hd) 58309 g58309 (by norm_num)

-- a an odd multiple of 227: 5^2 divides 1549 + 1 (2^227+1 -> 297371 -> 24781 -> 12391 -> 1549).
theorem k18_d227 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 227 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g297371 : 297371 ∈ P := S2 297371 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 297371 ∣ 2 ^ 227 + 1).trans hd)
  have g24781 : 24781 ∈ P := S1 24781 (by norm_num) (by norm_num) (hnz (by norm_num)) 297371 g297371 (by norm_num)
  have g12391 : 12391 ∈ P := S1 12391 (by norm_num) (by norm_num) (hnz (by norm_num)) 24781 g24781 (by norm_num)
  have g1549 : 1549 ∈ P := S1 1549 (by norm_num) (by norm_num) (hnz (by norm_num)) 12391 g12391 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1549 g1549 (by norm_num)

-- a an odd multiple of 229 (e = 5): 3^6 divides (2^229 + 1) * prod (p + 1) over p in {18754643, 347, 563, 29, 47} (2^229+1 -> 18754643; 2^229+1 -> 18754643 -> 1562887 -> 347; 2^229+1 -> 18754643 -> 1562887 -> 563; 2^229+1 -> 18754643 -> 1562887 -> 347 -> 29; 2^229+1 -> 18754643 -> 1562887 -> 563 -> 47).
theorem k18e5_d229 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 5) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 5 * ∏ p ∈ P, p)
    (hd : 2 ^ 229 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 5 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g18754643 : 18754643 ∈ P := S2 18754643 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 18754643 ∣ 2 ^ 229 + 1).trans hd)
  have g1562887 : 1562887 ∈ P := S1 1562887 (by norm_num) (by norm_num) (hnz (by norm_num)) 18754643 g18754643 (by norm_num)
  have g347 : 347 ∈ P := S1 347 (by norm_num) (by norm_num) (hnz (by norm_num)) 1562887 g1562887 (by norm_num)
  have g563 : 563 ∈ P := S1 563 (by norm_num) (by norm_num) (hnz (by norm_num)) 1562887 g1562887 (by norm_num)
  have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 347 g347 (by norm_num)
  have g47 : 47 ∈ P := S1 47 (by norm_num) (by norm_num) (hnz (by norm_num)) 563 g563 (by norm_num)
  have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 1 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
    ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (by norm_num : 3 ^ 1 ∣ 2 ^ 229 + 1).trans hd⟩
  have b1 := bud_cons b0 g18754643 (by simp) (by norm_num : 3 ^ 1 ∣ 18754643 + 1)
  have b2 := bud_cons b1 g347 (by simp) (by norm_num : 3 ^ 1 ∣ 347 + 1)
  have b3 := bud_cons b2 g563 (by simp) (by norm_num : 3 ^ 1 ∣ 563 + 1)
  have b4 := bud_cons b3 g29 (by simp) (by norm_num : 3 ^ 1 ∣ 29 + 1)
  have b5 := bud_cons b4 g47 (by simp) (by norm_num : 3 ^ 1 ∣ 47 + 1)
  exact budget_kernel3 hP h3P E b5.1 ((pow_dvd_pow 3 (by norm_num)).trans b5.2)

-- a an odd multiple of 229 (e = 7): 3^8 divides (2^229 + 1) * prod (p + 1) over p in {18754643, 137, 23, 347, 563, 29, 47} (2^229+1 -> 18754643; 3^7+1 -> 547 -> 137; 3^7+1 -> 547 -> 137 -> 23; 2^229+1 -> 18754643 -> 1562887 -> 347; 2^229+1 -> 18754643 -> 1562887 -> 563; 2^229+1 -> 18754643 -> 1562887 -> 347 -> 29; 2^229+1 -> 18754643 -> 1562887 -> 563 -> 47).
theorem k18e7_d229 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 7) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 7 * ∏ p ∈ P, p)
    (hd : 2 ^ 229 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 7 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g18754643 : 18754643 ∈ P := S2 18754643 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 18754643 ∣ 2 ^ 229 + 1).trans hd)
  have g547 : 547 ∈ P := S7 547 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g137 : 137 ∈ P := S1 137 (by norm_num) (by norm_num) (hnz (by norm_num)) 547 g547 (by norm_num)
  have g23 : 23 ∈ P := S1 23 (by norm_num) (by norm_num) (hnz (by norm_num)) 137 g137 (by norm_num)
  have g1562887 : 1562887 ∈ P := S1 1562887 (by norm_num) (by norm_num) (hnz (by norm_num)) 18754643 g18754643 (by norm_num)
  have g347 : 347 ∈ P := S1 347 (by norm_num) (by norm_num) (hnz (by norm_num)) 1562887 g1562887 (by norm_num)
  have g563 : 563 ∈ P := S1 563 (by norm_num) (by norm_num) (hnz (by norm_num)) 1562887 g1562887 (by norm_num)
  have g29 : 29 ∈ P := S1 29 (by norm_num) (by norm_num) (hnz (by norm_num)) 347 g347 (by norm_num)
  have g47 : 47 ∈ P := S1 47 (by norm_num) (by norm_num) (hnz (by norm_num)) 563 g563 (by norm_num)
  have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 1 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
    ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (by norm_num : 3 ^ 1 ∣ 2 ^ 229 + 1).trans hd⟩
  have b1 := bud_cons b0 g18754643 (by simp) (by norm_num : 3 ^ 1 ∣ 18754643 + 1)
  have b2 := bud_cons b1 g137 (by simp) (by norm_num : 3 ^ 1 ∣ 137 + 1)
  have b3 := bud_cons b2 g23 (by simp) (by norm_num : 3 ^ 1 ∣ 23 + 1)
  have b4 := bud_cons b3 g347 (by simp) (by norm_num : 3 ^ 1 ∣ 347 + 1)
  have b5 := bud_cons b4 g563 (by simp) (by norm_num : 3 ^ 1 ∣ 563 + 1)
  have b6 := bud_cons b5 g29 (by simp) (by norm_num : 3 ^ 1 ∣ 29 + 1)
  have b7 := bud_cons b6 g47 (by simp) (by norm_num : 3 ^ 1 ∣ 47 + 1)
  exact budget_kernel3 hP h3P E b7.1 ((pow_dvd_pow 3 (by norm_num)).trans b7.2)

-- a an odd multiple of 232: 5 divides 929 + 1 and 5569 + 1 (2^232+1 -> 929; 2^232+1 -> 5569).
theorem k18_d232 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 232 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g929 : 929 ∈ P := S2 929 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 929 ∣ 2 ^ 232 + 1).trans hd)
  have g5569 : 5569 ∈ P := S2 5569 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 5569 ∣ 2 ^ 232 + 1).trans hd)
  exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 929 g929 5569 g5569 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 233: 7 divides 13 + 1 and 41 + 1 (2^233+1 -> 467 -> 13; 2^233+1 -> 27961 -> 41).
theorem k18_d233 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 233 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g467 : 467 ∈ P := S2 467 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 467 ∣ 2 ^ 233 + 1).trans hd)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 467 g467 (by norm_num)
  have g27961 : 27961 ∈ P := S2 27961 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 27961 ∣ 2 ^ 233 + 1).trans hd)
  have g41 : 41 ∈ P := S1 41 (by norm_num) (by norm_num) (hnz (by norm_num)) 27961 g27961 (by norm_num)
  exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 13 g13 41 g41 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 236: 5 divides 1889 + 1 and 11329 + 1 (2^236+1 -> 1889; 2^236+1 -> 11329).
theorem k18_d236 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 236 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1889 : 1889 ∈ P := S2 1889 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1889 ∣ 2 ^ 236 + 1).trans hd)
  have g11329 : 11329 ∈ P := S2 11329 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 11329 ∣ 2 ^ 236 + 1).trans hd)
  exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1889 g1889 11329 g11329 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 239 (e = 5): 31 divides 61 + 1 and 433 + 1 (3^5+1 -> 61; 2^239+1 -> 340337 -> 433).
theorem k18e5_d239 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 5) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 5 * ∏ p ∈ P, p)
    (hd : 2 ^ 239 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 5 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g61 : 61 ∈ P := S7 61 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g340337 : 340337 ∈ P := S2 340337 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 340337 ∣ 2 ^ 239 + 1).trans hd)
  have g433 : 433 ∈ P := S1 433 (by norm_num) (by norm_num) (hnz (by norm_num)) 340337 g340337 (by norm_num)
  exact absurd (S3 31 (by norm_num) (by norm_num) (hnz (by norm_num)) 61 g61 433 g433 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 239: 5^2 divides 32605142983704221670173899 + 1 (2^239+1 -> 32605142983704221670173899).
theorem k18_d239 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 239 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g32605142983704221670173899 : 32605142983704221670173899 ∈ P := S2 32605142983704221670173899 prime_32605142983704221670173899 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 32605142983704221670173899 ∣ 2 ^ 239 + 1).trans hd)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 32605142983704221670173899 g32605142983704221670173899 (by norm_num)

-- a an odd multiple of 241: 5 divides 839 + 1 and 3102259 + 1 (2^241+1 -> 10411181203 -> 839; 2^241+1 -> 10411181203 -> 3102259).
theorem k18_d241 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 241 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g10411181203 : 10411181203 ∈ P := S2 10411181203 prime_10411181203 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 10411181203 ∣ 2 ^ 241 + 1).trans hd)
  have g839 : 839 ∈ P := S1 839 (by norm_num) (by norm_num) (hnz (by norm_num)) 10411181203 g10411181203 (by norm_num)
  have g3102259 : 3102259 ∈ P := S1 3102259 (by norm_num) (by norm_num) (hnz (by norm_num)) 10411181203 g10411181203 (by norm_num)
  exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 839 g839 3102259 g3102259 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 244: 17 divides 2^244 + 1 and 67 + 1 (2^244+1 -> 37831175201 -> 67).
theorem k18_d244 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 244 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g37831175201 : 37831175201 ∈ P := S2 37831175201 prime_37831175201 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 37831175201 ∣ 2 ^ 244 + 1).trans hd)
  have g67 : 67 ∈ P := S1 67 (by norm_num) (by norm_num) (hnz (by norm_num)) 37831175201 g37831175201 (by norm_num)
  exact S4 17 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 17 ∣ 2 ^ 244 + 1).trans hd) 67 g67 (by norm_num)

-- a an odd multiple of 248: 5 divides 8929 + 1 and 19 + 1 (2^248+1 -> 8929; 2^248+1 -> 8929 -> 19).
theorem k18_d248 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 248 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g8929 : 8929 ∈ P := S2 8929 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 8929 ∣ 2 ^ 248 + 1).trans hd)
  have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 8929 g8929 (by norm_num)
  exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 8929 g8929 19 g19 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 251 (e = 5): 31 divides 238451 + 1 and 61 + 1 (2^251+1 -> 238451; 3^5+1 -> 61).
theorem k18e5_d251 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 5) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 5 * ∏ p ∈ P, p)
    (hd : 2 ^ 251 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 5 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g238451 : 238451 ∈ P := S2 238451 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 238451 ∣ 2 ^ 251 + 1).trans hd)
  have g61 : 61 ∈ P := S7 61 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  exact absurd (S3 31 (by norm_num) (by norm_num) (hnz (by norm_num)) 238451 g238451 61 g61 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 251 (e = 7): 3^8 divides (2^251 + 1) * prod (p + 1) over p in {238451, 137, 641, 23, 107} (2^251+1 -> 238451; 3^7+1 -> 547 -> 137; 2^251+1 -> 238451 -> 641; 3^7+1 -> 547 -> 137 -> 23; 2^251+1 -> 238451 -> 641 -> 107).
theorem k18e7_d251 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 7) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 7 * ∏ p ∈ P, p)
    (hd : 2 ^ 251 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 7 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g238451 : 238451 ∈ P := S2 238451 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 238451 ∣ 2 ^ 251 + 1).trans hd)
  have g547 : 547 ∈ P := S7 547 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g137 : 137 ∈ P := S1 137 (by norm_num) (by norm_num) (hnz (by norm_num)) 547 g547 (by norm_num)
  have g641 : 641 ∈ P := S1 641 (by norm_num) (by norm_num) (hnz (by norm_num)) 238451 g238451 (by norm_num)
  have g23 : 23 ∈ P := S1 23 (by norm_num) (by norm_num) (hnz (by norm_num)) 137 g137 (by norm_num)
  have g107 : 107 ∈ P := S1 107 (by norm_num) (by norm_num) (hnz (by norm_num)) 641 g641 (by norm_num)
  have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 1 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
    ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (by norm_num : 3 ^ 1 ∣ 2 ^ 251 + 1).trans hd⟩
  have b1 := bud_cons b0 g238451 (by simp) (by norm_num : 3 ^ 1 ∣ 238451 + 1)
  have b2 := bud_cons b1 g137 (by simp) (by norm_num : 3 ^ 1 ∣ 137 + 1)
  have b3 := bud_cons b2 g641 (by simp) (by norm_num : 3 ^ 1 ∣ 641 + 1)
  have b4 := bud_cons b3 g23 (by simp) (by norm_num : 3 ^ 1 ∣ 23 + 1)
  have b5 := bud_cons b4 g107 (by simp) (by norm_num : 3 ^ 3 ∣ 107 + 1)
  exact budget_kernel3 hP h3P E b5.1 ((pow_dvd_pow 3 (by norm_num)).trans b5.2)

-- a an odd multiple of 254: 5 divides 2^254 + 1 and 509 + 1 (2^254+1 -> 509).
theorem k18_d254 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 254 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g509 : 509 ∈ P := S2 509 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by norm_num : 509 ∣ 2 ^ 254 + 1).trans hd)
  exact S4 5 (by norm_num) (by norm_num) (hnz (by norm_num)) ((by norm_num : 5 ∣ 2 ^ 254 + 1).trans hd) 509 g509 (by norm_num)

-- a an odd multiple of 256: 5^2 divides 149 + 1 (2^256+1 -> 1238926361552897 -> 206487726925483 -> 11621 -> 149).
theorem k18_d256 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 256 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1238926361552897 : 1238926361552897 ∈ P := S2 1238926361552897 prime_1238926361552897 (by norm_num) (hnz (by norm_num))
    ((by norm_num : 1238926361552897 ∣ 2 ^ 256 + 1).trans hd)
  have g206487726925483 : 206487726925483 ∈ P := S1 206487726925483 prime_206487726925483 (by norm_num) (hnz (by norm_num)) 1238926361552897 g1238926361552897 (by norm_num)
  have g11621 : 11621 ∈ P := S1 11621 (by norm_num) (by norm_num) (hnz (by norm_num)) 206487726925483 g206487726925483 (by norm_num)
  have g149 : 149 ∈ P := S1 149 (by norm_num) (by norm_num) (hnz (by norm_num)) 11621 g11621 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 149 g149 (by norm_num)

-- a an odd multiple of 257: 7 divides 37239639534523 + 1 and 13 + 1 (2^257+1 -> 37239639534523; 2^257+1 -> 37239639534523 -> 1329987126233 -> 13).
theorem k18_d257 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 257 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g37239639534523 : 37239639534523 ∈ P := S2 37239639534523 prime_37239639534523 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 257 = 2 ^ 256 * 2 ^ 1 from pow_add 2 256 1]; norm_num : 37239639534523 ∣ 2 ^ 257 + 1).trans hd)
  have g1329987126233 : 1329987126233 ∈ P := S1 1329987126233 prime_1329987126233 (by norm_num) (hnz (by norm_num)) 37239639534523 g37239639534523 (by norm_num)
  have g13 : 13 ∈ P := S1 13 (by norm_num) (by norm_num) (hnz (by norm_num)) 1329987126233 g1329987126233 (by norm_num)
  exact absurd (S3 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 37239639534523 g37239639534523 13 g13 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 512 (e = 5): 3^7 divides (2^512 + 1) * prod (p + 1) over p in {2424833, 107, 1259} (2^512+1 -> 2424833; 2^512+1 -> 2424833 -> 107; 2^512+1 -> 2424833 -> 1259).
theorem k18e5_d512 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 5) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 5 * ∏ p ∈ P, p)
    (hd : 2 ^ 512 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 5 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2424833 : 2424833 ∈ P := S2 2424833 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 512 = 2 ^ 256 * 2 ^ 256 from pow_add 2 256 256]; norm_num : 2424833 ∣ 2 ^ 512 + 1).trans hd)
  have g107 : 107 ∈ P := S1 107 (by norm_num) (by norm_num) (hnz (by norm_num)) 2424833 g2424833 (by norm_num)
  have g1259 : 1259 ∈ P := S1 1259 (by norm_num) (by norm_num) (hnz (by norm_num)) 2424833 g2424833 (by norm_num)
  have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 0 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
    ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (by rw [show (2:ℕ) ^ 512 = 2 ^ 256 * 2 ^ 256 from pow_add 2 256 256]; norm_num : 3 ^ 0 ∣ 2 ^ 512 + 1).trans hd⟩
  have b1 := bud_cons b0 g2424833 (by simp) (by norm_num : 3 ^ 2 ∣ 2424833 + 1)
  have b2 := bud_cons b1 g107 (by simp) (by norm_num : 3 ^ 3 ∣ 107 + 1)
  have b3 := bud_cons b2 g1259 (by simp) (by norm_num : 3 ^ 2 ∣ 1259 + 1)
  exact budget_kernel3 hP h3P E b3.1 ((pow_dvd_pow 3 (by norm_num)).trans b3.2)

-- a an odd multiple of 512 (e = 7): 3^8 divides (2^512 + 1) * prod (p + 1) over p in {2424833, 107, 137, 1259} (2^512+1 -> 2424833; 2^512+1 -> 2424833 -> 107; 3^7+1 -> 547 -> 137; 2^512+1 -> 2424833 -> 1259).
theorem k18e7_d512 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 7) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 7 * ∏ p ∈ P, p)
    (hd : 2 ^ 512 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 7 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2424833 : 2424833 ∈ P := S2 2424833 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 512 = 2 ^ 256 * 2 ^ 256 from pow_add 2 256 256]; norm_num : 2424833 ∣ 2 ^ 512 + 1).trans hd)
  have g107 : 107 ∈ P := S1 107 (by norm_num) (by norm_num) (hnz (by norm_num)) 2424833 g2424833 (by norm_num)
  have g547 : 547 ∈ P := S7 547 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g137 : 137 ∈ P := S1 137 (by norm_num) (by norm_num) (hnz (by norm_num)) 547 g547 (by norm_num)
  have g1259 : 1259 ∈ P := S1 1259 (by norm_num) (by norm_num) (hnz (by norm_num)) 2424833 g2424833 (by norm_num)
  have b0 : (∅ : Finset ℕ) ⊆ P ∧ 3 ^ 0 ∣ (2 ^ m + 1) * ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
    ⟨Finset.empty_subset _, by rw [Finset.prod_empty, mul_one]; exact (by rw [show (2:ℕ) ^ 512 = 2 ^ 256 * 2 ^ 256 from pow_add 2 256 256]; norm_num : 3 ^ 0 ∣ 2 ^ 512 + 1).trans hd⟩
  have b1 := bud_cons b0 g2424833 (by simp) (by norm_num : 3 ^ 2 ∣ 2424833 + 1)
  have b2 := bud_cons b1 g107 (by simp) (by norm_num : 3 ^ 3 ∣ 107 + 1)
  have b3 := bud_cons b2 g137 (by simp) (by norm_num : 3 ^ 1 ∣ 137 + 1)
  have b4 := bud_cons b3 g1259 (by simp) (by norm_num : 3 ^ 2 ∣ 1259 + 1)
  exact budget_kernel3 hP h3P E b4.1 ((pow_dvd_pow 3 (by norm_num)).trans b4.2)

-- a an odd multiple of 1024: 5 divides 6487031809 + 1 and 36709 + 1 (2^1024+1 -> 6487031809; 2^1024+1 -> 45592577 -> 36709).
theorem k18_d1024 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 1024 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g6487031809 : 6487031809 ∈ P := S2 6487031809 prime_6487031809 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1024 = (2 ^ 256) ^ 4 from pow_mul 2 256 4]; norm_num : 6487031809 ∣ 2 ^ 1024 + 1).trans hd)
  have g45592577 : 45592577 ∈ P := S2 45592577 prime_45592577 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1024 = (2 ^ 256) ^ 4 from pow_mul 2 256 4]; norm_num : 45592577 ∣ 2 ^ 1024 + 1).trans hd)
  have g36709 : 36709 ∈ P := S1 36709 (by norm_num) (by norm_num) (hnz (by norm_num)) 45592577 g45592577 (by norm_num)
  exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 6487031809 g6487031809 36709 g36709 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 1024 (e = 7): 23 divides 45592577 + 1 and 137 + 1 (2^1024+1 -> 45592577; 3^7+1 -> 547 -> 137).
theorem k18e7_d1024 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 7) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 7 * ∏ p ∈ P, p)
    (hd : 2 ^ 1024 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 7 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g45592577 : 45592577 ∈ P := S2 45592577 prime_45592577 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 1024 = (2 ^ 256) ^ 4 from pow_mul 2 256 4]; norm_num : 45592577 ∣ 2 ^ 1024 + 1).trans hd)
  have g547 : 547 ∈ P := S7 547 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g137 : 137 ∈ P := S1 137 (by norm_num) (by norm_num) (hnz (by norm_num)) 547 g547 (by norm_num)
  exact absurd (S3 23 (by norm_num) (by norm_num) (hnz (by norm_num)) 45592577 g45592577 137 g137 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 2048: 5^2 divides 974849 + 1 (2^2048+1 -> 974849).
theorem k18_d2048 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 2048 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g974849 : 974849 ∈ P := S2 974849 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 2048 = (2 ^ 256) ^ 8 from pow_mul 2 256 8]; norm_num : 974849 ∣ 2 ^ 2048 + 1).trans hd)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 974849 g974849 (by norm_num)

-- a an odd multiple of 4096: 11^2 divides 43801 + 1 (2^4096+1 -> 26017793 -> 43801).
theorem k18_d4096 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 4096 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g26017793 : 26017793 ∈ P := S2 26017793 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 4096 = (2 ^ 256) ^ 16 from pow_mul 2 256 16]; norm_num : 26017793 ∣ 2 ^ 4096 + 1).trans hd)
  have g43801 : 43801 ∈ P := S1 43801 (by norm_num) (by norm_num) (hnz (by norm_num)) 26017793 g26017793 (by norm_num)
  exact S6 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43801 g43801 (by norm_num)

-- a an odd multiple of 8192: 179 divides 18257 + 1 and 23627 + 1 (2^8192+1 -> 2663848877152141313 -> 18257; 2^8192+1 -> 2663848877152141313 -> 23627).
theorem k18_d8192 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 8192 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g2663848877152141313 : 2663848877152141313 ∈ P := S2 2663848877152141313 prime_2663848877152141313 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 8192 = (2 ^ 256) ^ 32 from pow_mul 2 256 32]; norm_num : 2663848877152141313 ∣ 2 ^ 8192 + 1).trans hd)
  have g18257 : 18257 ∈ P := S1 18257 (by norm_num) (by norm_num) (hnz (by norm_num)) 2663848877152141313 g2663848877152141313 (by norm_num)
  have g23627 : 23627 ∈ P := S1 23627 (by norm_num) (by norm_num) (hnz (by norm_num)) 2663848877152141313 g2663848877152141313 (by norm_num)
  exact absurd (S3 179 (by norm_num) (by norm_num) (hnz (by norm_num)) 18257 g18257 23627 g23627 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 16384: 7^2 divides 72421 + 1 (2^16384+1 -> 116928085873074369829035993834596371340386703423373313 -> 78068824171447136188657471 -> 68244480929 -> 72421).
theorem k18_d16384 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 16384 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g116928085873074369829035993834596371340386703423373313 : 116928085873074369829035993834596371340386703423373313 ∈ P := S2 116928085873074369829035993834596371340386703423373313 prime_116928085873074369829035993834596371340386703423373313 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 16384 = (2 ^ 256) ^ 64 from pow_mul 2 256 64]; norm_num : 116928085873074369829035993834596371340386703423373313 ∣ 2 ^ 16384 + 1).trans hd)
  have g78068824171447136188657471 : 78068824171447136188657471 ∈ P := S1 78068824171447136188657471 prime_78068824171447136188657471 (by norm_num) (hnz (by norm_num)) 116928085873074369829035993834596371340386703423373313 g116928085873074369829035993834596371340386703423373313 (by norm_num)
  have g68244480929 : 68244480929 ∈ P := S1 68244480929 prime_68244480929 (by norm_num) (hnz (by norm_num)) 78068824171447136188657471 g78068824171447136188657471 (by norm_num)
  have g72421 : 72421 ∈ P := S1 72421 (by norm_num) (by norm_num) (hnz (by norm_num)) 68244480929 g68244480929 (by norm_num)
  exact S6 7 (by norm_num) (by norm_num) (hnz (by norm_num)) 72421 g72421 (by norm_num)

-- a an odd multiple of 32768: 5 divides 1214251009 + 1 and 1020379 + 1 (2^32768+1 -> 1214251009; 2^32768+1 -> 1214251009 -> 1020379).
theorem k18_d32768 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 32768 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g1214251009 : 1214251009 ∈ P := S2 1214251009 prime_1214251009 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 32768 = (2 ^ 256) ^ 128 from pow_mul 2 256 128]; norm_num : 1214251009 ∣ 2 ^ 32768 + 1).trans hd)
  have g1020379 : 1020379 ∈ P := S1 1020379 (by norm_num) (by norm_num) (hnz (by norm_num)) 1214251009 g1214251009 (by norm_num)
  exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 1214251009 g1214251009 1020379 g1020379 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 65536: 5^2 divides 149 + 1 (2^65536+1 -> 825753601 -> 3653777 -> 149).
theorem k18_d65536 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 65536 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g825753601 : 825753601 ∈ P := S2 825753601 prime_825753601 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 65536 = (2 ^ 256) ^ 256 from pow_mul 2 256 256]; norm_num : 825753601 ∣ 2 ^ 65536 + 1).trans hd)
  have g3653777 : 3653777 ∈ P := S1 3653777 (by norm_num) (by norm_num) (hnz (by norm_num)) 825753601 g825753601 (by norm_num)
  have g149 : 149 ∈ P := S1 149 (by norm_num) (by norm_num) (hnz (by norm_num)) 3653777 g3653777 (by norm_num)
  exact S6 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 149 g149 (by norm_num)

-- a an odd multiple of 131072: 17 divides 67 + 1 and 1028941 + 1 (2^131072+1 -> 31065037602817 -> 67; 2^131072+1 -> 31065037602817 -> 231828638827 -> 1028941).
theorem k18_d131072 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 131072 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g31065037602817 : 31065037602817 ∈ P := S2 31065037602817 prime_31065037602817 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 131072 = ((2 ^ 256) ^ 256) ^ 2 from by rw [← pow_mul, ← pow_mul]]; norm_num : 31065037602817 ∣ 2 ^ 131072 + 1).trans hd)
  have g67 : 67 ∈ P := S1 67 (by norm_num) (by norm_num) (hnz (by norm_num)) 31065037602817 g31065037602817 (by norm_num)
  have g231828638827 : 231828638827 ∈ P := S1 231828638827 prime_231828638827 (by norm_num) (hnz (by norm_num)) 31065037602817 g31065037602817 (by norm_num)
  have g1028941 : 1028941 ∈ P := S1 1028941 (by norm_num) (by norm_num) (hnz (by norm_num)) 231828638827 g231828638827 (by norm_num)
  exact absurd (S3 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 67 g67 1028941 g1028941 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 262144: 5 divides 13631489 + 1 and 16829 + 1 (2^262144+1 -> 13631489; 2^262144+1 -> 13631489 -> 16829).
theorem k18_d262144 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 262144 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g13631489 : 13631489 ∈ P := S2 13631489 (by norm_num) (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 262144 = ((2 ^ 256) ^ 256) ^ 4 from by rw [← pow_mul, ← pow_mul]]; norm_num : 13631489 ∣ 2 ^ 262144 + 1).trans hd)
  have g16829 : 16829 ∈ P := S1 16829 (by norm_num) (by norm_num) (hnz (by norm_num)) 13631489 g13631489 (by norm_num)
  exact absurd (S3 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 13631489 g13631489 16829 g16829 (by norm_num) (by norm_num)) (by norm_num)

-- a an odd multiple of 524288: 17^2 divides 3467 + 1 (2^524288+1 -> 70525124609 -> 3467).
theorem k18_d524288 {m e : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hd : 2 ^ 524288 + 1 ∣ 2 ^ m + 1) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g70525124609 : 70525124609 ∈ P := S2 70525124609 prime_70525124609 (by norm_num) (hnz (by norm_num))
    ((by rw [show (2:ℕ) ^ 524288 = ((2 ^ 256) ^ 256) ^ 8 from by rw [← pow_mul, ← pow_mul]]; norm_num : 70525124609 ∣ 2 ^ 524288 + 1).trans hd)
  have g3467 : 3467 ∈ P := S1 3467 (by norm_num) (by norm_num) (hnz (by norm_num)) 70525124609 g70525124609 (by norm_num)
  exact S6 17 (by norm_num) (by norm_num) (hnz (by norm_num)) 3467 g3467 (by norm_num)

-- kernel 3^5: a is no odd multiple of any d in 10..257 outside the exception list.
theorem sieve_e5 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 5) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 5 * ∏ p ∈ P, p) :
    ∀ d, 10 ≤ d → d ≤ 257 → d ∉ ({11, 13} : Finset ℕ) →
      m % (2 * d) ≠ d := by
  intro d lo hi hex h
  interval_cases d
  · exact kill2_d10 hP E (two_pow_add_one_dvd_of_odd_mul (d := 10) (by omega))
  · exact absurd (by decide) hex
  · exact kill2_d12 hP E (two_pow_add_one_dvd_of_odd_mul (d := 12) (by omega))
  · exact absurd (by decide) hex
  · exact kill2_d14 hP E (two_pow_add_one_dvd_of_odd_mul (d := 14) (by omega))
  · exact kill3e5w_d15 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 15) (by omega))
  · exact kill3e5w_d16 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 16) (by omega))
  · exact kill3e5w_d17 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 17) (by omega))
  · exact kill2_d18 hP E (two_pow_add_one_dvd_of_odd_mul (d := 18) (by omega))
  · exact kill3e5w_d19 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 19) (by omega))
  · exact kill2_d20 hP E (two_pow_add_one_dvd_of_odd_mul (d := 20) (by omega))
  · exact k18e5_d21 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 21) (by omega))
  · exact kill2_d22 hP E (two_pow_add_one_dvd_of_odd_mul (d := 22) (by omega))
  · exact k18e5_d23 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 23) (by omega))
  · exact kill2_d24 hP E (two_pow_add_one_dvd_of_odd_mul (d := 24) (by omega))
  · exact kill2_d25 hP E (two_pow_add_one_dvd_of_odd_mul (d := 25) (by omega))
  · exact kill2_d26 hP E (two_pow_add_one_dvd_of_odd_mul (d := 26) (by omega))
  · exact kill2_d27 hP E (two_pow_add_one_dvd_of_odd_mul (d := 27) (by omega))
  · exact kill2_d28 hP E (two_pow_add_one_dvd_of_odd_mul (d := 28) (by omega))
  · exact kill2_d29 hP E (two_pow_add_one_dvd_of_odd_mul (d := 29) (by omega))
  · exact kill2_d10 hP E (two_pow_add_one_dvd_of_odd_mul (d := 10) (by omega))
  · exact k18_d31 hP E (two_pow_add_one_dvd_of_odd_mul (d := 31) (by omega))
  · exact kill2_d32 hP E (two_pow_add_one_dvd_of_odd_mul (d := 32) (by omega))
  · exact kill2_d33 hP E (two_pow_add_one_dvd_of_odd_mul (d := 33) (by omega))
  · exact kill2_d34 hP E (two_pow_add_one_dvd_of_odd_mul (d := 34) (by omega))
  · exact kill2_d35 hP E (two_pow_add_one_dvd_of_odd_mul (d := 35) (by omega))
  · exact kill2_d12 hP E (two_pow_add_one_dvd_of_odd_mul (d := 12) (by omega))
  · exact kill2_d37 hP E (two_pow_add_one_dvd_of_odd_mul (d := 37) (by omega))
  · exact kill2_d38 hP E (two_pow_add_one_dvd_of_odd_mul (d := 38) (by omega))
  · exact kill2_d39 hP E (two_pow_add_one_dvd_of_odd_mul (d := 39) (by omega))
  · exact k18_d40 hP E (two_pow_add_one_dvd_of_odd_mul (d := 40) (by omega))
  · exact k18_d41 hP E (two_pow_add_one_dvd_of_odd_mul (d := 41) (by omega))
  · exact kill2_d14 hP E (two_pow_add_one_dvd_of_odd_mul (d := 14) (by omega))
  · exact k18_d43 hP E (two_pow_add_one_dvd_of_odd_mul (d := 43) (by omega))
  · exact k18_d44 hP E (two_pow_add_one_dvd_of_odd_mul (d := 44) (by omega))
  · exact kill3e5w_d15 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 15) (by omega))
  · exact kill2_d46 hP E (two_pow_add_one_dvd_of_odd_mul (d := 46) (by omega))
  · exact k18_d47 hP E (two_pow_add_one_dvd_of_odd_mul (d := 47) (by omega))
  · exact kill3e5w_d16 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 16) (by omega))
  · exact k18_d49 hP E (two_pow_add_one_dvd_of_odd_mul (d := 49) (by omega))
  · exact kill2_d10 hP E (two_pow_add_one_dvd_of_odd_mul (d := 10) (by omega))
  · exact kill3e5w_d17 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 17) (by omega))
  · exact kill2_d52 hP E (two_pow_add_one_dvd_of_odd_mul (d := 52) (by omega))
  · exact k18_d53 hP E (two_pow_add_one_dvd_of_odd_mul (d := 53) (by omega))
  · exact kill2_d18 hP E (two_pow_add_one_dvd_of_odd_mul (d := 18) (by omega))
  · exact kill2_d55 hP E (two_pow_add_one_dvd_of_odd_mul (d := 55) (by omega))
  · exact kill2_d56 hP E (two_pow_add_one_dvd_of_odd_mul (d := 56) (by omega))
  · exact kill3e5w_d19 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 19) (by omega))
  · exact k18_d58 hP E (two_pow_add_one_dvd_of_odd_mul (d := 58) (by omega))
  · exact kill2_d59 hP E (two_pow_add_one_dvd_of_odd_mul (d := 59) (by omega))
  · exact kill2_d12 hP E (two_pow_add_one_dvd_of_odd_mul (d := 12) (by omega))
  · exact k18_d61 hP E (two_pow_add_one_dvd_of_odd_mul (d := 61) (by omega))
  · exact kill2_d62 hP E (two_pow_add_one_dvd_of_odd_mul (d := 62) (by omega))
  · exact k18e5_d21 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 21) (by omega))
  · exact kill2_d64 hP E (two_pow_add_one_dvd_of_odd_mul (d := 64) (by omega))
  · exact kill2_d65 hP E (two_pow_add_one_dvd_of_odd_mul (d := 65) (by omega))
  · exact kill2_d22 hP E (two_pow_add_one_dvd_of_odd_mul (d := 22) (by omega))
  · exact kill2_d67 hP E (two_pow_add_one_dvd_of_odd_mul (d := 67) (by omega))
  · exact kill2_d68 hP E (two_pow_add_one_dvd_of_odd_mul (d := 68) (by omega))
  · exact k18e5_d23 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 23) (by omega))
  · exact kill2_d10 hP E (two_pow_add_one_dvd_of_odd_mul (d := 10) (by omega))
  · exact k18_d71 hP E (two_pow_add_one_dvd_of_odd_mul (d := 71) (by omega))
  · exact kill2_d24 hP E (two_pow_add_one_dvd_of_odd_mul (d := 24) (by omega))
  · exact k18_d73 hP E (two_pow_add_one_dvd_of_odd_mul (d := 73) (by omega))
  · exact kill2_d74 hP E (two_pow_add_one_dvd_of_odd_mul (d := 74) (by omega))
  · exact kill3e5w_d15 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 15) (by omega))
  · exact kill2_d76 hP E (two_pow_add_one_dvd_of_odd_mul (d := 76) (by omega))
  · exact kill2_d77 hP E (two_pow_add_one_dvd_of_odd_mul (d := 77) (by omega))
  · exact kill2_d26 hP E (two_pow_add_one_dvd_of_odd_mul (d := 26) (by omega))
  · exact k18_d79 hP E (two_pow_add_one_dvd_of_odd_mul (d := 79) (by omega))
  · exact kill3e5w_d16 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 16) (by omega))
  · exact kill2_d27 hP E (two_pow_add_one_dvd_of_odd_mul (d := 27) (by omega))
  · exact kill2_d82 hP E (two_pow_add_one_dvd_of_odd_mul (d := 82) (by omega))
  · exact kill2_d83 hP E (two_pow_add_one_dvd_of_odd_mul (d := 83) (by omega))
  · exact kill2_d12 hP E (two_pow_add_one_dvd_of_odd_mul (d := 12) (by omega))
  · exact kill3e5w_d17 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 17) (by omega))
  · exact kill2_d86 hP E (two_pow_add_one_dvd_of_odd_mul (d := 86) (by omega))
  · exact kill2_d29 hP E (two_pow_add_one_dvd_of_odd_mul (d := 29) (by omega))
  · exact k18_d88 hP E (two_pow_add_one_dvd_of_odd_mul (d := 88) (by omega))
  · exact k18_d89 hP E (two_pow_add_one_dvd_of_odd_mul (d := 89) (by omega))
  · exact kill2_d10 hP E (two_pow_add_one_dvd_of_odd_mul (d := 10) (by omega))
  · exact kill2_d91 hP E (two_pow_add_one_dvd_of_odd_mul (d := 91) (by omega))
  · exact k18_d92 hP E (two_pow_add_one_dvd_of_odd_mul (d := 92) (by omega))
  · exact k18_d31 hP E (two_pow_add_one_dvd_of_odd_mul (d := 31) (by omega))
  · exact kill2_d94 hP E (two_pow_add_one_dvd_of_odd_mul (d := 94) (by omega))
  · exact kill3e5w_d19 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 19) (by omega))
  · exact kill2_d32 hP E (two_pow_add_one_dvd_of_odd_mul (d := 32) (by omega))
  · exact kill2_d97 hP E (two_pow_add_one_dvd_of_odd_mul (d := 97) (by omega))
  · exact kill2_d14 hP E (two_pow_add_one_dvd_of_odd_mul (d := 14) (by omega))
  · exact kill2_d33 hP E (two_pow_add_one_dvd_of_odd_mul (d := 33) (by omega))
  · exact kill2_d20 hP E (two_pow_add_one_dvd_of_odd_mul (d := 20) (by omega))
  · exact k18_d101 hP E (two_pow_add_one_dvd_of_odd_mul (d := 101) (by omega))
  · exact kill2_d34 hP E (two_pow_add_one_dvd_of_odd_mul (d := 34) (by omega))
  · exact k18_d103 hP E (two_pow_add_one_dvd_of_odd_mul (d := 103) (by omega))
  · exact k18_d104 hP E (two_pow_add_one_dvd_of_odd_mul (d := 104) (by omega))
  · exact kill3e5w_d15 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 15) (by omega))
  · exact kill2_d106 hP E (two_pow_add_one_dvd_of_odd_mul (d := 106) (by omega))
  · exact k18_d107 hP E (two_pow_add_one_dvd_of_odd_mul (d := 107) (by omega))
  · exact kill2_d12 hP E (two_pow_add_one_dvd_of_odd_mul (d := 12) (by omega))
  · exact k18_d109 hP E (two_pow_add_one_dvd_of_odd_mul (d := 109) (by omega))
  · exact kill2_d10 hP E (two_pow_add_one_dvd_of_odd_mul (d := 10) (by omega))
  · exact kill2_d37 hP E (two_pow_add_one_dvd_of_odd_mul (d := 37) (by omega))
  · exact kill3e5w_d16 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 16) (by omega))
  · exact k18e5_d113 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 113) (by omega))
  · exact kill2_d38 hP E (two_pow_add_one_dvd_of_odd_mul (d := 38) (by omega))
  · exact k18e5_d23 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 23) (by omega))
  · exact kill2_d116 hP E (two_pow_add_one_dvd_of_odd_mul (d := 116) (by omega))
  · exact kill2_d39 hP E (two_pow_add_one_dvd_of_odd_mul (d := 39) (by omega))
  · exact kill2_d118 hP E (two_pow_add_one_dvd_of_odd_mul (d := 118) (by omega))
  · exact kill3e5w_d17 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 17) (by omega))
  · exact kill2_d24 hP E (two_pow_add_one_dvd_of_odd_mul (d := 24) (by omega))
  · exact kill2_d121 hP E (two_pow_add_one_dvd_of_odd_mul (d := 121) (by omega))
  · exact kill2_d122 hP E (two_pow_add_one_dvd_of_odd_mul (d := 122) (by omega))
  · exact k18_d41 hP E (two_pow_add_one_dvd_of_odd_mul (d := 41) (by omega))
  · exact kill2_d124 hP E (two_pow_add_one_dvd_of_odd_mul (d := 124) (by omega))
  · exact kill2_d25 hP E (two_pow_add_one_dvd_of_odd_mul (d := 25) (by omega))
  · exact kill2_d14 hP E (two_pow_add_one_dvd_of_odd_mul (d := 14) (by omega))
  · exact k18_d127 hP E (two_pow_add_one_dvd_of_odd_mul (d := 127) (by omega))
  · exact k18_d128 hP E (two_pow_add_one_dvd_of_odd_mul (d := 128) (by omega))
  · exact k18_d43 hP E (two_pow_add_one_dvd_of_odd_mul (d := 43) (by omega))
  · exact kill2_d10 hP E (two_pow_add_one_dvd_of_odd_mul (d := 10) (by omega))
  · exact kill2_d131 hP E (two_pow_add_one_dvd_of_odd_mul (d := 131) (by omega))
  · exact kill2_d12 hP E (two_pow_add_one_dvd_of_odd_mul (d := 12) (by omega))
  · exact kill3e5w_d19 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 19) (by omega))
  · exact kill2_d134 hP E (two_pow_add_one_dvd_of_odd_mul (d := 134) (by omega))
  · exact kill3e5w_d15 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 15) (by omega))
  · exact k18e5_d136 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 136) (by omega))
  · exact k18e5_d137 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 137) (by omega))
  · exact kill2_d46 hP E (two_pow_add_one_dvd_of_odd_mul (d := 46) (by omega))
  · exact k18e5_d139 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 139) (by omega))
  · exact kill2_d20 hP E (two_pow_add_one_dvd_of_odd_mul (d := 20) (by omega))
  · exact k18_d47 hP E (two_pow_add_one_dvd_of_odd_mul (d := 47) (by omega))
  · exact kill2_d142 hP E (two_pow_add_one_dvd_of_odd_mul (d := 142) (by omega))
  · exact kill2_d143 hP E (two_pow_add_one_dvd_of_odd_mul (d := 143) (by omega))
  · exact kill3e5w_d16 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 16) (by omega))
  · exact kill2_d29 hP E (two_pow_add_one_dvd_of_odd_mul (d := 29) (by omega))
  · exact kill2_d146 hP E (two_pow_add_one_dvd_of_odd_mul (d := 146) (by omega))
  · exact k18e5_d21 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 21) (by omega))
  · exact k18_d148 hP E (two_pow_add_one_dvd_of_odd_mul (d := 148) (by omega))
  · exact kill2_d149 hP E (two_pow_add_one_dvd_of_odd_mul (d := 149) (by omega))
  · exact kill2_d10 hP E (two_pow_add_one_dvd_of_odd_mul (d := 10) (by omega))
  · exact k18_d151 hP E (two_pow_add_one_dvd_of_odd_mul (d := 151) (by omega))
  · exact kill2_d152 hP E (two_pow_add_one_dvd_of_odd_mul (d := 152) (by omega))
  · exact kill3e5w_d17 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 17) (by omega))
  · exact kill2_d14 hP E (two_pow_add_one_dvd_of_odd_mul (d := 14) (by omega))
  · exact k18_d31 hP E (two_pow_add_one_dvd_of_odd_mul (d := 31) (by omega))
  · exact kill2_d12 hP E (two_pow_add_one_dvd_of_odd_mul (d := 12) (by omega))
  · exact kill2_d157 hP E (two_pow_add_one_dvd_of_odd_mul (d := 157) (by omega))
  · exact k18_d158 hP E (two_pow_add_one_dvd_of_odd_mul (d := 158) (by omega))
  · exact k18_d53 hP E (two_pow_add_one_dvd_of_odd_mul (d := 53) (by omega))
  · exact kill2_d32 hP E (two_pow_add_one_dvd_of_odd_mul (d := 32) (by omega))
  · exact k18e5_d23 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 23) (by omega))
  · exact kill2_d18 hP E (two_pow_add_one_dvd_of_odd_mul (d := 18) (by omega))
  · exact k18_d163 hP E (two_pow_add_one_dvd_of_odd_mul (d := 163) (by omega))
  · exact k18e5_d164 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 164) (by omega))
  · exact kill3e5w_d15 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 15) (by omega))
  · exact k18_d166 hP E (two_pow_add_one_dvd_of_odd_mul (d := 166) (by omega))
  · exact k18_d167 hP E (two_pow_add_one_dvd_of_odd_mul (d := 167) (by omega))
  · exact kill2_d24 hP E (two_pow_add_one_dvd_of_odd_mul (d := 24) (by omega))
  · exact k18_d169 hP E (two_pow_add_one_dvd_of_odd_mul (d := 169) (by omega))
  · exact kill2_d10 hP E (two_pow_add_one_dvd_of_odd_mul (d := 10) (by omega))
  · exact kill3e5w_d19 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 19) (by omega))
  · exact k18_d172 hP E (two_pow_add_one_dvd_of_odd_mul (d := 172) (by omega))
  · exact k18e5_d173 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 173) (by omega))
  · exact k18_d58 hP E (two_pow_add_one_dvd_of_odd_mul (d := 58) (by omega))
  · exact kill2_d25 hP E (two_pow_add_one_dvd_of_odd_mul (d := 25) (by omega))
  · exact kill3e5w_d16 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 16) (by omega))
  · exact kill2_d59 hP E (two_pow_add_one_dvd_of_odd_mul (d := 59) (by omega))
  · exact k18_d178 hP E (two_pow_add_one_dvd_of_odd_mul (d := 178) (by omega))
  · exact k18_d179 hP E (two_pow_add_one_dvd_of_odd_mul (d := 179) (by omega))
  · exact kill2_d12 hP E (two_pow_add_one_dvd_of_odd_mul (d := 12) (by omega))
  · exact k18_d181 hP E (two_pow_add_one_dvd_of_odd_mul (d := 181) (by omega))
  · exact kill2_d14 hP E (two_pow_add_one_dvd_of_odd_mul (d := 14) (by omega))
  · exact k18_d61 hP E (two_pow_add_one_dvd_of_odd_mul (d := 61) (by omega))
  · exact k18_d184 hP E (two_pow_add_one_dvd_of_odd_mul (d := 184) (by omega))
  · exact kill2_d37 hP E (two_pow_add_one_dvd_of_odd_mul (d := 37) (by omega))
  · exact kill2_d62 hP E (two_pow_add_one_dvd_of_odd_mul (d := 62) (by omega))
  · exact kill3e5w_d17 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 17) (by omega))
  · exact k18_d188 hP E (two_pow_add_one_dvd_of_odd_mul (d := 188) (by omega))
  · exact k18e5_d21 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 21) (by omega))
  · exact kill2_d10 hP E (two_pow_add_one_dvd_of_odd_mul (d := 10) (by omega))
  · exact k18_d191 hP E (two_pow_add_one_dvd_of_odd_mul (d := 191) (by omega))
  · exact kill2_d64 hP E (two_pow_add_one_dvd_of_odd_mul (d := 64) (by omega))
  · exact k18e5_d193 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 193) (by omega))
  · exact k18_d194 hP E (two_pow_add_one_dvd_of_odd_mul (d := 194) (by omega))
  · exact kill3e5w_d15 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 15) (by omega))
  · exact kill2_d28 hP E (two_pow_add_one_dvd_of_odd_mul (d := 28) (by omega))
  · exact k18_d197 hP E (two_pow_add_one_dvd_of_odd_mul (d := 197) (by omega))
  · exact kill2_d18 hP E (two_pow_add_one_dvd_of_odd_mul (d := 18) (by omega))
  · exact k18_d199 hP E (two_pow_add_one_dvd_of_odd_mul (d := 199) (by omega))
  · exact k18_d40 hP E (two_pow_add_one_dvd_of_odd_mul (d := 40) (by omega))
  · exact kill2_d67 hP E (two_pow_add_one_dvd_of_odd_mul (d := 67) (by omega))
  · exact k18_d202 hP E (two_pow_add_one_dvd_of_odd_mul (d := 202) (by omega))
  · exact kill2_d29 hP E (two_pow_add_one_dvd_of_odd_mul (d := 29) (by omega))
  · exact kill2_d12 hP E (two_pow_add_one_dvd_of_odd_mul (d := 12) (by omega))
  · exact k18_d41 hP E (two_pow_add_one_dvd_of_odd_mul (d := 41) (by omega))
  · exact k18_d206 hP E (two_pow_add_one_dvd_of_odd_mul (d := 206) (by omega))
  · exact k18e5_d23 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 23) (by omega))
  · exact kill3e5w_d16 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 16) (by omega))
  · exact kill3e5w_d19 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 19) (by omega))
  · exact kill2_d10 hP E (two_pow_add_one_dvd_of_odd_mul (d := 10) (by omega))
  · exact k18e5_d211 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 211) (by omega))
  · exact k18_d212 hP E (two_pow_add_one_dvd_of_odd_mul (d := 212) (by omega))
  · exact k18_d71 hP E (two_pow_add_one_dvd_of_odd_mul (d := 71) (by omega))
  · exact k18_d214 hP E (two_pow_add_one_dvd_of_odd_mul (d := 214) (by omega))
  · exact k18_d43 hP E (two_pow_add_one_dvd_of_odd_mul (d := 43) (by omega))
  · exact kill2_d24 hP E (two_pow_add_one_dvd_of_odd_mul (d := 24) (by omega))
  · exact k18_d31 hP E (two_pow_add_one_dvd_of_odd_mul (d := 31) (by omega))
  · exact k18_d218 hP E (two_pow_add_one_dvd_of_odd_mul (d := 218) (by omega))
  · exact k18_d73 hP E (two_pow_add_one_dvd_of_odd_mul (d := 73) (by omega))
  · exact kill2_d20 hP E (two_pow_add_one_dvd_of_odd_mul (d := 20) (by omega))
  · exact kill3e5w_d17 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 17) (by omega))
  · exact kill2_d74 hP E (two_pow_add_one_dvd_of_odd_mul (d := 74) (by omega))
  · exact k18_d223 hP E (two_pow_add_one_dvd_of_odd_mul (d := 223) (by omega))
  · exact kill2_d32 hP E (two_pow_add_one_dvd_of_odd_mul (d := 32) (by omega))
  · exact kill3e5w_d15 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 15) (by omega))
  · exact k18_d226 hP E (two_pow_add_one_dvd_of_odd_mul (d := 226) (by omega))
  · exact k18_d227 hP E (two_pow_add_one_dvd_of_odd_mul (d := 227) (by omega))
  · exact kill2_d12 hP E (two_pow_add_one_dvd_of_odd_mul (d := 12) (by omega))
  · exact k18e5_d229 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 229) (by omega))
  · exact kill2_d10 hP E (two_pow_add_one_dvd_of_odd_mul (d := 10) (by omega))
  · exact k18e5_d21 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 21) (by omega))
  · exact k18_d232 hP E (two_pow_add_one_dvd_of_odd_mul (d := 232) (by omega))
  · exact k18_d233 hP E (two_pow_add_one_dvd_of_odd_mul (d := 233) (by omega))
  · exact kill2_d18 hP E (two_pow_add_one_dvd_of_odd_mul (d := 18) (by omega))
  · exact k18_d47 hP E (two_pow_add_one_dvd_of_odd_mul (d := 47) (by omega))
  · exact k18_d236 hP E (two_pow_add_one_dvd_of_odd_mul (d := 236) (by omega))
  · exact k18_d79 hP E (two_pow_add_one_dvd_of_odd_mul (d := 79) (by omega))
  · exact kill2_d14 hP E (two_pow_add_one_dvd_of_odd_mul (d := 14) (by omega))
  · exact k18e5_d239 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 239) (by omega))
  · exact kill3e5w_d16 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 16) (by omega))
  · exact k18_d241 hP E (two_pow_add_one_dvd_of_odd_mul (d := 241) (by omega))
  · exact kill2_d22 hP E (two_pow_add_one_dvd_of_odd_mul (d := 22) (by omega))
  · exact kill2_d27 hP E (two_pow_add_one_dvd_of_odd_mul (d := 27) (by omega))
  · exact k18_d244 hP E (two_pow_add_one_dvd_of_odd_mul (d := 244) (by omega))
  · exact kill2_d35 hP E (two_pow_add_one_dvd_of_odd_mul (d := 35) (by omega))
  · exact kill2_d82 hP E (two_pow_add_one_dvd_of_odd_mul (d := 82) (by omega))
  · exact kill3e5w_d19 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 19) (by omega))
  · exact k18_d248 hP E (two_pow_add_one_dvd_of_odd_mul (d := 248) (by omega))
  · exact kill2_d83 hP E (two_pow_add_one_dvd_of_odd_mul (d := 83) (by omega))
  · exact kill2_d10 hP E (two_pow_add_one_dvd_of_odd_mul (d := 10) (by omega))
  · exact k18e5_d251 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 251) (by omega))
  · exact kill2_d12 hP E (two_pow_add_one_dvd_of_odd_mul (d := 12) (by omega))
  · exact k18e5_d23 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 23) (by omega))
  · exact k18_d254 hP E (two_pow_add_one_dvd_of_odd_mul (d := 254) (by omega))
  · exact kill3e5w_d15 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 15) (by omega))
  · exact k18_d256 hP E (two_pow_add_one_dvd_of_odd_mul (d := 256) (by omega))
  · exact k18_d257 hP E (two_pow_add_one_dvd_of_odd_mul (d := 257) (by omega))

-- kernel 3^5: a is no odd multiple of 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288 (factors of Fermat numbers).
theorem fermat_e5 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 5) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 5 * ∏ p ∈ P, p) :
    ∀ d ∈ ({512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288} : Finset ℕ), m % (2 * d) ≠ d := by
  intro d hd h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact k18e5_d512 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 512) h)
  · exact k18_d1024 hP E (two_pow_add_one_dvd_of_odd_mul (d := 1024) h)
  · exact k18_d2048 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2048) h)
  · exact k18_d4096 hP E (two_pow_add_one_dvd_of_odd_mul (d := 4096) h)
  · exact k18_d8192 hP E (two_pow_add_one_dvd_of_odd_mul (d := 8192) h)
  · exact k18_d16384 hP E (two_pow_add_one_dvd_of_odd_mul (d := 16384) h)
  · exact k18_d32768 hP E (two_pow_add_one_dvd_of_odd_mul (d := 32768) h)
  · exact k18_d65536 hP E (two_pow_add_one_dvd_of_odd_mul (d := 65536) h)
  · exact k18_d131072 hP E (two_pow_add_one_dvd_of_odd_mul (d := 131072) h)
  · exact k18_d262144 hP E (two_pow_add_one_dvd_of_odd_mul (d := 262144) h)
  · exact k18_d524288 hP E (two_pow_add_one_dvd_of_odd_mul (d := 524288) h)

-- kernel 3^7: a is no odd multiple of any d in 10..257 outside the exception list.
theorem sieve_e7 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 7) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 7 * ∏ p ∈ P, p) :
    ∀ d, 10 ≤ d → d ≤ 257 → d ∉ ({11, 13} : Finset ℕ) →
      m % (2 * d) ≠ d := by
  intro d lo hi hex h
  interval_cases d
  · exact kill2_d10 hP E (two_pow_add_one_dvd_of_odd_mul (d := 10) (by omega))
  · exact absurd (by decide) hex
  · exact kill2_d12 hP E (two_pow_add_one_dvd_of_odd_mul (d := 12) (by omega))
  · exact absurd (by decide) hex
  · exact kill2_d14 hP E (two_pow_add_one_dvd_of_odd_mul (d := 14) (by omega))
  · exact kill3e7w_d15 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 15) (by omega))
  · exact kill3e7w_d16 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 16) (by omega))
  · exact kill3e7w_d17 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 17) (by omega))
  · exact kill2_d18 hP E (two_pow_add_one_dvd_of_odd_mul (d := 18) (by omega))
  · exact kill3e7w_d19 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 19) (by omega))
  · exact kill2_d20 hP E (two_pow_add_one_dvd_of_odd_mul (d := 20) (by omega))
  · exact k18e7_d21 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 21) (by omega))
  · exact kill2_d22 hP E (two_pow_add_one_dvd_of_odd_mul (d := 22) (by omega))
  · exact k18e7_d23 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 23) (by omega))
  · exact kill2_d24 hP E (two_pow_add_one_dvd_of_odd_mul (d := 24) (by omega))
  · exact kill2_d25 hP E (two_pow_add_one_dvd_of_odd_mul (d := 25) (by omega))
  · exact kill2_d26 hP E (two_pow_add_one_dvd_of_odd_mul (d := 26) (by omega))
  · exact kill2_d27 hP E (two_pow_add_one_dvd_of_odd_mul (d := 27) (by omega))
  · exact kill2_d28 hP E (two_pow_add_one_dvd_of_odd_mul (d := 28) (by omega))
  · exact kill2_d29 hP E (two_pow_add_one_dvd_of_odd_mul (d := 29) (by omega))
  · exact kill2_d10 hP E (two_pow_add_one_dvd_of_odd_mul (d := 10) (by omega))
  · exact k18_d31 hP E (two_pow_add_one_dvd_of_odd_mul (d := 31) (by omega))
  · exact kill2_d32 hP E (two_pow_add_one_dvd_of_odd_mul (d := 32) (by omega))
  · exact kill2_d33 hP E (two_pow_add_one_dvd_of_odd_mul (d := 33) (by omega))
  · exact kill2_d34 hP E (two_pow_add_one_dvd_of_odd_mul (d := 34) (by omega))
  · exact kill2_d35 hP E (two_pow_add_one_dvd_of_odd_mul (d := 35) (by omega))
  · exact kill2_d12 hP E (two_pow_add_one_dvd_of_odd_mul (d := 12) (by omega))
  · exact kill2_d37 hP E (two_pow_add_one_dvd_of_odd_mul (d := 37) (by omega))
  · exact kill2_d38 hP E (two_pow_add_one_dvd_of_odd_mul (d := 38) (by omega))
  · exact kill2_d39 hP E (two_pow_add_one_dvd_of_odd_mul (d := 39) (by omega))
  · exact k18_d40 hP E (two_pow_add_one_dvd_of_odd_mul (d := 40) (by omega))
  · exact k18_d41 hP E (two_pow_add_one_dvd_of_odd_mul (d := 41) (by omega))
  · exact kill2_d14 hP E (two_pow_add_one_dvd_of_odd_mul (d := 14) (by omega))
  · exact k18_d43 hP E (two_pow_add_one_dvd_of_odd_mul (d := 43) (by omega))
  · exact k18_d44 hP E (two_pow_add_one_dvd_of_odd_mul (d := 44) (by omega))
  · exact kill3e7w_d15 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 15) (by omega))
  · exact kill2_d46 hP E (two_pow_add_one_dvd_of_odd_mul (d := 46) (by omega))
  · exact k18_d47 hP E (two_pow_add_one_dvd_of_odd_mul (d := 47) (by omega))
  · exact kill3e7w_d16 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 16) (by omega))
  · exact k18_d49 hP E (two_pow_add_one_dvd_of_odd_mul (d := 49) (by omega))
  · exact kill2_d10 hP E (two_pow_add_one_dvd_of_odd_mul (d := 10) (by omega))
  · exact kill3e7w_d17 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 17) (by omega))
  · exact kill2_d52 hP E (two_pow_add_one_dvd_of_odd_mul (d := 52) (by omega))
  · exact k18_d53 hP E (two_pow_add_one_dvd_of_odd_mul (d := 53) (by omega))
  · exact kill2_d18 hP E (two_pow_add_one_dvd_of_odd_mul (d := 18) (by omega))
  · exact kill2_d55 hP E (two_pow_add_one_dvd_of_odd_mul (d := 55) (by omega))
  · exact kill2_d56 hP E (two_pow_add_one_dvd_of_odd_mul (d := 56) (by omega))
  · exact kill3e7w_d19 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 19) (by omega))
  · exact k18_d58 hP E (two_pow_add_one_dvd_of_odd_mul (d := 58) (by omega))
  · exact kill2_d59 hP E (two_pow_add_one_dvd_of_odd_mul (d := 59) (by omega))
  · exact kill2_d12 hP E (two_pow_add_one_dvd_of_odd_mul (d := 12) (by omega))
  · exact k18_d61 hP E (two_pow_add_one_dvd_of_odd_mul (d := 61) (by omega))
  · exact kill2_d62 hP E (two_pow_add_one_dvd_of_odd_mul (d := 62) (by omega))
  · exact k18e7_d21 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 21) (by omega))
  · exact kill2_d64 hP E (two_pow_add_one_dvd_of_odd_mul (d := 64) (by omega))
  · exact kill2_d65 hP E (two_pow_add_one_dvd_of_odd_mul (d := 65) (by omega))
  · exact kill2_d22 hP E (two_pow_add_one_dvd_of_odd_mul (d := 22) (by omega))
  · exact kill2_d67 hP E (two_pow_add_one_dvd_of_odd_mul (d := 67) (by omega))
  · exact kill2_d68 hP E (two_pow_add_one_dvd_of_odd_mul (d := 68) (by omega))
  · exact k18e7_d23 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 23) (by omega))
  · exact kill2_d10 hP E (two_pow_add_one_dvd_of_odd_mul (d := 10) (by omega))
  · exact k18_d71 hP E (two_pow_add_one_dvd_of_odd_mul (d := 71) (by omega))
  · exact kill2_d24 hP E (two_pow_add_one_dvd_of_odd_mul (d := 24) (by omega))
  · exact k18_d73 hP E (two_pow_add_one_dvd_of_odd_mul (d := 73) (by omega))
  · exact kill2_d74 hP E (two_pow_add_one_dvd_of_odd_mul (d := 74) (by omega))
  · exact kill3e7w_d15 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 15) (by omega))
  · exact kill2_d76 hP E (two_pow_add_one_dvd_of_odd_mul (d := 76) (by omega))
  · exact kill2_d77 hP E (two_pow_add_one_dvd_of_odd_mul (d := 77) (by omega))
  · exact kill2_d26 hP E (two_pow_add_one_dvd_of_odd_mul (d := 26) (by omega))
  · exact k18_d79 hP E (two_pow_add_one_dvd_of_odd_mul (d := 79) (by omega))
  · exact kill3e7w_d16 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 16) (by omega))
  · exact kill2_d27 hP E (two_pow_add_one_dvd_of_odd_mul (d := 27) (by omega))
  · exact kill2_d82 hP E (two_pow_add_one_dvd_of_odd_mul (d := 82) (by omega))
  · exact kill2_d83 hP E (two_pow_add_one_dvd_of_odd_mul (d := 83) (by omega))
  · exact kill2_d12 hP E (two_pow_add_one_dvd_of_odd_mul (d := 12) (by omega))
  · exact kill3e7w_d17 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 17) (by omega))
  · exact kill2_d86 hP E (two_pow_add_one_dvd_of_odd_mul (d := 86) (by omega))
  · exact kill2_d29 hP E (two_pow_add_one_dvd_of_odd_mul (d := 29) (by omega))
  · exact k18_d88 hP E (two_pow_add_one_dvd_of_odd_mul (d := 88) (by omega))
  · exact k18_d89 hP E (two_pow_add_one_dvd_of_odd_mul (d := 89) (by omega))
  · exact kill2_d10 hP E (two_pow_add_one_dvd_of_odd_mul (d := 10) (by omega))
  · exact kill2_d91 hP E (two_pow_add_one_dvd_of_odd_mul (d := 91) (by omega))
  · exact k18_d92 hP E (two_pow_add_one_dvd_of_odd_mul (d := 92) (by omega))
  · exact k18_d31 hP E (two_pow_add_one_dvd_of_odd_mul (d := 31) (by omega))
  · exact kill2_d94 hP E (two_pow_add_one_dvd_of_odd_mul (d := 94) (by omega))
  · exact kill3e7w_d19 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 19) (by omega))
  · exact kill2_d32 hP E (two_pow_add_one_dvd_of_odd_mul (d := 32) (by omega))
  · exact kill2_d97 hP E (two_pow_add_one_dvd_of_odd_mul (d := 97) (by omega))
  · exact kill2_d14 hP E (two_pow_add_one_dvd_of_odd_mul (d := 14) (by omega))
  · exact kill2_d33 hP E (two_pow_add_one_dvd_of_odd_mul (d := 33) (by omega))
  · exact kill2_d20 hP E (two_pow_add_one_dvd_of_odd_mul (d := 20) (by omega))
  · exact k18_d101 hP E (two_pow_add_one_dvd_of_odd_mul (d := 101) (by omega))
  · exact kill2_d34 hP E (two_pow_add_one_dvd_of_odd_mul (d := 34) (by omega))
  · exact k18_d103 hP E (two_pow_add_one_dvd_of_odd_mul (d := 103) (by omega))
  · exact k18_d104 hP E (two_pow_add_one_dvd_of_odd_mul (d := 104) (by omega))
  · exact kill3e7w_d15 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 15) (by omega))
  · exact kill2_d106 hP E (two_pow_add_one_dvd_of_odd_mul (d := 106) (by omega))
  · exact k18e7_d107 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 107) (by omega))
  · exact kill2_d12 hP E (two_pow_add_one_dvd_of_odd_mul (d := 12) (by omega))
  · exact k18_d109 hP E (two_pow_add_one_dvd_of_odd_mul (d := 109) (by omega))
  · exact kill2_d10 hP E (two_pow_add_one_dvd_of_odd_mul (d := 10) (by omega))
  · exact kill2_d37 hP E (two_pow_add_one_dvd_of_odd_mul (d := 37) (by omega))
  · exact kill3e7w_d16 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 16) (by omega))
  · exact k18_d113 hP E (two_pow_add_one_dvd_of_odd_mul (d := 113) (by omega))
  · exact kill2_d38 hP E (two_pow_add_one_dvd_of_odd_mul (d := 38) (by omega))
  · exact k18e7_d23 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 23) (by omega))
  · exact kill2_d116 hP E (two_pow_add_one_dvd_of_odd_mul (d := 116) (by omega))
  · exact kill2_d39 hP E (two_pow_add_one_dvd_of_odd_mul (d := 39) (by omega))
  · exact kill2_d118 hP E (two_pow_add_one_dvd_of_odd_mul (d := 118) (by omega))
  · exact kill3e7w_d17 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 17) (by omega))
  · exact kill2_d24 hP E (two_pow_add_one_dvd_of_odd_mul (d := 24) (by omega))
  · exact kill2_d121 hP E (two_pow_add_one_dvd_of_odd_mul (d := 121) (by omega))
  · exact kill2_d122 hP E (two_pow_add_one_dvd_of_odd_mul (d := 122) (by omega))
  · exact k18_d41 hP E (two_pow_add_one_dvd_of_odd_mul (d := 41) (by omega))
  · exact kill2_d124 hP E (two_pow_add_one_dvd_of_odd_mul (d := 124) (by omega))
  · exact kill2_d25 hP E (two_pow_add_one_dvd_of_odd_mul (d := 25) (by omega))
  · exact kill2_d14 hP E (two_pow_add_one_dvd_of_odd_mul (d := 14) (by omega))
  · exact k18_d127 hP E (two_pow_add_one_dvd_of_odd_mul (d := 127) (by omega))
  · exact k18_d128 hP E (two_pow_add_one_dvd_of_odd_mul (d := 128) (by omega))
  · exact k18_d43 hP E (two_pow_add_one_dvd_of_odd_mul (d := 43) (by omega))
  · exact kill2_d10 hP E (two_pow_add_one_dvd_of_odd_mul (d := 10) (by omega))
  · exact kill2_d131 hP E (two_pow_add_one_dvd_of_odd_mul (d := 131) (by omega))
  · exact kill2_d12 hP E (two_pow_add_one_dvd_of_odd_mul (d := 12) (by omega))
  · exact kill3e7w_d19 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 19) (by omega))
  · exact kill2_d134 hP E (two_pow_add_one_dvd_of_odd_mul (d := 134) (by omega))
  · exact kill3e7w_d15 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 15) (by omega))
  · exact k18_d136 hP E (two_pow_add_one_dvd_of_odd_mul (d := 136) (by omega))
  · exact k18e7_d137 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 137) (by omega))
  · exact kill2_d46 hP E (two_pow_add_one_dvd_of_odd_mul (d := 46) (by omega))
  · exact k18e7_d139 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 139) (by omega))
  · exact kill2_d20 hP E (two_pow_add_one_dvd_of_odd_mul (d := 20) (by omega))
  · exact k18_d47 hP E (two_pow_add_one_dvd_of_odd_mul (d := 47) (by omega))
  · exact kill2_d142 hP E (two_pow_add_one_dvd_of_odd_mul (d := 142) (by omega))
  · exact kill2_d143 hP E (two_pow_add_one_dvd_of_odd_mul (d := 143) (by omega))
  · exact kill3e7w_d16 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 16) (by omega))
  · exact kill2_d29 hP E (two_pow_add_one_dvd_of_odd_mul (d := 29) (by omega))
  · exact kill2_d146 hP E (two_pow_add_one_dvd_of_odd_mul (d := 146) (by omega))
  · exact k18e7_d21 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 21) (by omega))
  · exact k18_d148 hP E (two_pow_add_one_dvd_of_odd_mul (d := 148) (by omega))
  · exact kill2_d149 hP E (two_pow_add_one_dvd_of_odd_mul (d := 149) (by omega))
  · exact kill2_d10 hP E (two_pow_add_one_dvd_of_odd_mul (d := 10) (by omega))
  · exact k18_d151 hP E (two_pow_add_one_dvd_of_odd_mul (d := 151) (by omega))
  · exact kill2_d152 hP E (two_pow_add_one_dvd_of_odd_mul (d := 152) (by omega))
  · exact kill3e7w_d17 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 17) (by omega))
  · exact kill2_d14 hP E (two_pow_add_one_dvd_of_odd_mul (d := 14) (by omega))
  · exact k18_d31 hP E (two_pow_add_one_dvd_of_odd_mul (d := 31) (by omega))
  · exact kill2_d12 hP E (two_pow_add_one_dvd_of_odd_mul (d := 12) (by omega))
  · exact kill2_d157 hP E (two_pow_add_one_dvd_of_odd_mul (d := 157) (by omega))
  · exact k18_d158 hP E (two_pow_add_one_dvd_of_odd_mul (d := 158) (by omega))
  · exact k18_d53 hP E (two_pow_add_one_dvd_of_odd_mul (d := 53) (by omega))
  · exact kill2_d32 hP E (two_pow_add_one_dvd_of_odd_mul (d := 32) (by omega))
  · exact k18e7_d23 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 23) (by omega))
  · exact kill2_d18 hP E (two_pow_add_one_dvd_of_odd_mul (d := 18) (by omega))
  · exact k18_d163 hP E (two_pow_add_one_dvd_of_odd_mul (d := 163) (by omega))
  · exact k18e7_d164 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 164) (by omega))
  · exact kill3e7w_d15 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 15) (by omega))
  · exact k18_d166 hP E (two_pow_add_one_dvd_of_odd_mul (d := 166) (by omega))
  · exact k18_d167 hP E (two_pow_add_one_dvd_of_odd_mul (d := 167) (by omega))
  · exact kill2_d24 hP E (two_pow_add_one_dvd_of_odd_mul (d := 24) (by omega))
  · exact k18_d169 hP E (two_pow_add_one_dvd_of_odd_mul (d := 169) (by omega))
  · exact kill2_d10 hP E (two_pow_add_one_dvd_of_odd_mul (d := 10) (by omega))
  · exact kill3e7w_d19 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 19) (by omega))
  · exact k18_d172 hP E (two_pow_add_one_dvd_of_odd_mul (d := 172) (by omega))
  · exact k18_d173 hP E (two_pow_add_one_dvd_of_odd_mul (d := 173) (by omega))
  · exact k18_d58 hP E (two_pow_add_one_dvd_of_odd_mul (d := 58) (by omega))
  · exact kill2_d25 hP E (two_pow_add_one_dvd_of_odd_mul (d := 25) (by omega))
  · exact kill3e7w_d16 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 16) (by omega))
  · exact kill2_d59 hP E (two_pow_add_one_dvd_of_odd_mul (d := 59) (by omega))
  · exact k18_d178 hP E (two_pow_add_one_dvd_of_odd_mul (d := 178) (by omega))
  · exact k18_d179 hP E (two_pow_add_one_dvd_of_odd_mul (d := 179) (by omega))
  · exact kill2_d12 hP E (two_pow_add_one_dvd_of_odd_mul (d := 12) (by omega))
  · exact k18_d181 hP E (two_pow_add_one_dvd_of_odd_mul (d := 181) (by omega))
  · exact kill2_d14 hP E (two_pow_add_one_dvd_of_odd_mul (d := 14) (by omega))
  · exact k18_d61 hP E (two_pow_add_one_dvd_of_odd_mul (d := 61) (by omega))
  · exact k18_d184 hP E (two_pow_add_one_dvd_of_odd_mul (d := 184) (by omega))
  · exact kill2_d37 hP E (two_pow_add_one_dvd_of_odd_mul (d := 37) (by omega))
  · exact kill2_d62 hP E (two_pow_add_one_dvd_of_odd_mul (d := 62) (by omega))
  · exact kill3e7w_d17 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 17) (by omega))
  · exact k18_d188 hP E (two_pow_add_one_dvd_of_odd_mul (d := 188) (by omega))
  · exact k18e7_d21 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 21) (by omega))
  · exact kill2_d10 hP E (two_pow_add_one_dvd_of_odd_mul (d := 10) (by omega))
  · exact k18_d191 hP E (two_pow_add_one_dvd_of_odd_mul (d := 191) (by omega))
  · exact kill2_d64 hP E (two_pow_add_one_dvd_of_odd_mul (d := 64) (by omega))
  · exact k18e7_d193 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 193) (by omega))
  · exact k18_d194 hP E (two_pow_add_one_dvd_of_odd_mul (d := 194) (by omega))
  · exact kill3e7w_d15 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 15) (by omega))
  · exact kill2_d28 hP E (two_pow_add_one_dvd_of_odd_mul (d := 28) (by omega))
  · exact k18_d197 hP E (two_pow_add_one_dvd_of_odd_mul (d := 197) (by omega))
  · exact kill2_d18 hP E (two_pow_add_one_dvd_of_odd_mul (d := 18) (by omega))
  · exact k18_d199 hP E (two_pow_add_one_dvd_of_odd_mul (d := 199) (by omega))
  · exact k18_d40 hP E (two_pow_add_one_dvd_of_odd_mul (d := 40) (by omega))
  · exact kill2_d67 hP E (two_pow_add_one_dvd_of_odd_mul (d := 67) (by omega))
  · exact k18_d202 hP E (two_pow_add_one_dvd_of_odd_mul (d := 202) (by omega))
  · exact kill2_d29 hP E (two_pow_add_one_dvd_of_odd_mul (d := 29) (by omega))
  · exact kill2_d12 hP E (two_pow_add_one_dvd_of_odd_mul (d := 12) (by omega))
  · exact k18_d41 hP E (two_pow_add_one_dvd_of_odd_mul (d := 41) (by omega))
  · exact k18_d206 hP E (two_pow_add_one_dvd_of_odd_mul (d := 206) (by omega))
  · exact k18e7_d23 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 23) (by omega))
  · exact kill3e7w_d16 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 16) (by omega))
  · exact kill3e7w_d19 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 19) (by omega))
  · exact kill2_d10 hP E (two_pow_add_one_dvd_of_odd_mul (d := 10) (by omega))
  · exact k18e7_d211 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 211) (by omega))
  · exact k18_d212 hP E (two_pow_add_one_dvd_of_odd_mul (d := 212) (by omega))
  · exact k18_d71 hP E (two_pow_add_one_dvd_of_odd_mul (d := 71) (by omega))
  · exact k18_d214 hP E (two_pow_add_one_dvd_of_odd_mul (d := 214) (by omega))
  · exact k18_d43 hP E (two_pow_add_one_dvd_of_odd_mul (d := 43) (by omega))
  · exact kill2_d24 hP E (two_pow_add_one_dvd_of_odd_mul (d := 24) (by omega))
  · exact k18_d31 hP E (two_pow_add_one_dvd_of_odd_mul (d := 31) (by omega))
  · exact k18_d218 hP E (two_pow_add_one_dvd_of_odd_mul (d := 218) (by omega))
  · exact k18_d73 hP E (two_pow_add_one_dvd_of_odd_mul (d := 73) (by omega))
  · exact kill2_d20 hP E (two_pow_add_one_dvd_of_odd_mul (d := 20) (by omega))
  · exact kill3e7w_d17 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 17) (by omega))
  · exact kill2_d74 hP E (two_pow_add_one_dvd_of_odd_mul (d := 74) (by omega))
  · exact k18_d223 hP E (two_pow_add_one_dvd_of_odd_mul (d := 223) (by omega))
  · exact kill2_d32 hP E (two_pow_add_one_dvd_of_odd_mul (d := 32) (by omega))
  · exact kill3e7w_d15 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 15) (by omega))
  · exact k18_d226 hP E (two_pow_add_one_dvd_of_odd_mul (d := 226) (by omega))
  · exact k18_d227 hP E (two_pow_add_one_dvd_of_odd_mul (d := 227) (by omega))
  · exact kill2_d12 hP E (two_pow_add_one_dvd_of_odd_mul (d := 12) (by omega))
  · exact k18e7_d229 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 229) (by omega))
  · exact kill2_d10 hP E (two_pow_add_one_dvd_of_odd_mul (d := 10) (by omega))
  · exact k18e7_d21 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 21) (by omega))
  · exact k18_d232 hP E (two_pow_add_one_dvd_of_odd_mul (d := 232) (by omega))
  · exact k18_d233 hP E (two_pow_add_one_dvd_of_odd_mul (d := 233) (by omega))
  · exact kill2_d18 hP E (two_pow_add_one_dvd_of_odd_mul (d := 18) (by omega))
  · exact k18_d47 hP E (two_pow_add_one_dvd_of_odd_mul (d := 47) (by omega))
  · exact k18_d236 hP E (two_pow_add_one_dvd_of_odd_mul (d := 236) (by omega))
  · exact k18_d79 hP E (two_pow_add_one_dvd_of_odd_mul (d := 79) (by omega))
  · exact kill2_d14 hP E (two_pow_add_one_dvd_of_odd_mul (d := 14) (by omega))
  · exact k18_d239 hP E (two_pow_add_one_dvd_of_odd_mul (d := 239) (by omega))
  · exact kill3e7w_d16 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 16) (by omega))
  · exact k18_d241 hP E (two_pow_add_one_dvd_of_odd_mul (d := 241) (by omega))
  · exact kill2_d22 hP E (two_pow_add_one_dvd_of_odd_mul (d := 22) (by omega))
  · exact kill2_d27 hP E (two_pow_add_one_dvd_of_odd_mul (d := 27) (by omega))
  · exact k18_d244 hP E (two_pow_add_one_dvd_of_odd_mul (d := 244) (by omega))
  · exact kill2_d35 hP E (two_pow_add_one_dvd_of_odd_mul (d := 35) (by omega))
  · exact kill2_d82 hP E (two_pow_add_one_dvd_of_odd_mul (d := 82) (by omega))
  · exact kill3e7w_d19 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 19) (by omega))
  · exact k18_d248 hP E (two_pow_add_one_dvd_of_odd_mul (d := 248) (by omega))
  · exact kill2_d83 hP E (two_pow_add_one_dvd_of_odd_mul (d := 83) (by omega))
  · exact kill2_d10 hP E (two_pow_add_one_dvd_of_odd_mul (d := 10) (by omega))
  · exact k18e7_d251 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 251) (by omega))
  · exact kill2_d12 hP E (two_pow_add_one_dvd_of_odd_mul (d := 12) (by omega))
  · exact k18e7_d23 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 23) (by omega))
  · exact k18_d254 hP E (two_pow_add_one_dvd_of_odd_mul (d := 254) (by omega))
  · exact kill3e7w_d15 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 15) (by omega))
  · exact k18_d256 hP E (two_pow_add_one_dvd_of_odd_mul (d := 256) (by omega))
  · exact k18_d257 hP E (two_pow_add_one_dvd_of_odd_mul (d := 257) (by omega))

-- kernel 3^7: a is no odd multiple of 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288 (factors of Fermat numbers).
theorem fermat_e7 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 7) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 7 * ∏ p ∈ P, p) :
    ∀ d ∈ ({512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288} : Finset ℕ), m % (2 * d) ≠ d := by
  intro d hd h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact k18e7_d512 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 512) h)
  · exact k18e7_d1024 hP h3P E (two_pow_add_one_dvd_of_odd_mul (d := 1024) h)
  · exact k18_d2048 hP E (two_pow_add_one_dvd_of_odd_mul (d := 2048) h)
  · exact k18_d4096 hP E (two_pow_add_one_dvd_of_odd_mul (d := 4096) h)
  · exact k18_d8192 hP E (two_pow_add_one_dvd_of_odd_mul (d := 8192) h)
  · exact k18_d16384 hP E (two_pow_add_one_dvd_of_odd_mul (d := 16384) h)
  · exact k18_d32768 hP E (two_pow_add_one_dvd_of_odd_mul (d := 32768) h)
  · exact k18_d65536 hP E (two_pow_add_one_dvd_of_odd_mul (d := 65536) h)
  · exact k18_d131072 hP E (two_pow_add_one_dvd_of_odd_mul (d := 131072) h)
  · exact k18_d262144 hP E (two_pow_add_one_dvd_of_odd_mul (d := 262144) h)
  · exact k18_d524288 hP E (two_pow_add_one_dvd_of_odd_mul (d := 524288) h)

-- Uniform count for odd a (no factorization needed).  For an odd prime p = 2 mod 3 the number
-- (2^p + 1) / 3 is 2 mod 3, so 2^p + 1 has a prime factor q = 2 mod 3.
theorem root_mod3 {p : ℕ} (hp2 : p % 2 = 1) (hp3 : p % 3 = 2) :
    ∃ q, q.Prime ∧ q ∣ 2 ^ p + 1 ∧ q % 3 = 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, p = 6 * k + 5 := ⟨p / 6, by omega⟩
  have h9 : (2 ^ (6 * k + 5) + 1) % 9 = 6 := by
    have h1 : (2 ^ (6 * k)) % 9 = 1 := by
      rw [pow_mul, Nat.pow_mod]
      norm_num
    rw [pow_add, Nat.add_mod, Nat.mul_mod, h1]
    norm_num
  obtain ⟨q, hq, hqd, hq3⟩ := exists_prime_mod3 ((2 ^ (6 * k + 5) + 1) / 3) (by omega)
  exact ⟨q, hq, hqd.trans (Nat.div_dvd_of_dvd (by omega)), hq3⟩

-- Two different odd primes p, p' cannot share such a factor: it would divide 2^2 - 1 = 3.
theorem root_inj {p p' q : ℕ} (hp : p.Prime) (hp' : p'.Prime) (hne : p ≠ p') (hq : q.Prime)
    (hq3 : q % 3 = 2) (h : q ∣ 2 ^ p + 1) (h' : q ∣ 2 ^ p' + 1) : False := by
  have key : ∀ r : ℕ, q ∣ 2 ^ r + 1 → q ∣ 2 ^ (2 * r) - 1 := by
    intro r hr
    have e1 : 2 ^ (2 * r) - 1 = (2 ^ r + 1) * (2 ^ r - 1) := by
      have := Nat.sq_sub_sq (2 ^ r) 1
      rw [mul_comm 2 r, pow_mul]
      simpa using this
    rw [e1]
    exact hr.mul_right _
  have hg := Nat.dvd_gcd (key p h) (key p' h')
  rw [Nat.pow_sub_one_gcd_pow_sub_one, Nat.gcd_mul_left,
    (Nat.coprime_primes hp hp').mpr hne] at hg
  have h3 : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp (by simpa using hg)
  omega

-- Kernel 3^e, a = m odd: 1 + (number of primes p = 2 mod 3 dividing m) + j <= e, where 3^j
-- divides the product of x + 1 over a set X of simple primes not dividing 2^m + 1.
theorem odd_ledger {m e j : ℕ} {P T X : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (hm : m % 2 = 1) (hT : ∀ p ∈ T, p.Prime ∧ p % 3 = 2 ∧ p ∣ m)
    (hX : X ⊆ P) (hXr : ∀ x ∈ X, ¬ x ∣ 2 ^ m + 1) (hXj : 3 ^ j ∣ ∏ x ∈ X, (x + 1)) :
    1 + T.card + j ≤ e := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have hodd : ∀ p ∈ T, p % 2 = 1 := by
    intro p hp
    obtain ⟨t, rfl⟩ := (hT p hp).2.2
    rcases Nat.mod_two_eq_zero_or_one p with h0 | h1
    · rw [Nat.mul_mod, h0] at hm; simp at hm
    · exact h1
  have hdvd : ∀ p ∈ T, 2 ^ p + 1 ∣ 2 ^ m + 1 := by
    intro p hp
    have hp1 := hodd p hp
    have hpos := (hT p hp).1.pos
    obtain ⟨t, rfl⟩ := (hT p hp).2.2
    have ht : t % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one t with h0 | h1
      · rw [Nat.mul_mod, h0] at hm; simp at hm
      · exact h1
    apply two_pow_add_one_dvd_of_odd_mul
    obtain ⟨s, rfl⟩ : ∃ s, t = 2 * s + 1 := ⟨t / 2, by omega⟩
    rw [show p * (2 * s + 1) = 2 * p * s + p from by ring, Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt (by omega)
  have hex : ∀ p : ℕ, ∃ q : ℕ, p ∈ T → q.Prime ∧ q ∣ 2 ^ p + 1 ∧ q % 3 = 2 := by
    intro p
    by_cases hp : p ∈ T
    · obtain ⟨q, hq⟩ := root_mod3 (hodd p hp) (hT p hp).2.1
      exact ⟨q, fun _ => hq⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose f hf using hex
  have hinj : Set.InjOn f (T : Set ℕ) := by
    intro p hp p' hp' heq
    by_contra hne
    have h1 := hf p hp
    have h2 := hf p' hp'
    rw [← heq] at h2
    exact root_inj (hT p hp).1 (hT p' hp').1 hne h1.1 h1.2.2 h1.2.1 h2.2.1
  have hQd : ∀ q ∈ T.image f, q.Prime ∧ q ∣ 2 ^ m + 1 ∧ q % 3 = 2 := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    exact ⟨(hf p hp).1, (hf p hp).2.1.trans (hdvd p hp), (hf p hp).2.2⟩
  have hQP : T.image f ⊆ P := by
    intro q hq
    obtain ⟨hqp, hqd, hq3⟩ := hQd q hq
    refine S2 q hqp ?_ ?_ hqd
    · rintro rfl
      have := (Nat.dvd_add_right (dvd_pow_self 2 (by omega : m ≠ 0))).mp hqd
      omega
    · intro h3
      rw [Finset.mem_singleton.mp h3] at hq3
      omega
  have hdisj : Disjoint (T.image f) X := by
    rw [Finset.disjoint_left]
    intro q hq hqX
    exact hXr q hqX (hQd q hq).2.1
  have h3Q : 3 ^ T.card ∣ ∏ q ∈ T.image f, (q + 1) := by
    rw [← Finset.card_image_of_injOn hinj, ← Finset.prod_const]
    exact Finset.prod_dvd_prod_of_dvd _ _ (fun q hq => by
      have := (hQd q hq).2.2
      omega)
  by_contra hlt
  refine budget_kernel3 hP h3P E (Finset.union_subset hQP hX) ?_
  rw [Finset.prod_union hdisj]
  have h3 : 3 ^ (1 + T.card + j) ∣ (2 ^ m + 1) * ((∏ q ∈ T.image f, (q + 1)) * ∏ x ∈ X, (x + 1)) := by
    rw [pow_add, pow_add, pow_one, mul_assoc]
    exact mul_dvd_mul (three_dvd_two_pow_add_one hm) (mul_dvd_mul h3Q hXj)
  exact (pow_dvd_pow 3 (by omega)).trans h3

-- e = 5: at most 4 primes p = 2 mod 3 divide an odd a.
theorem odd_count_e5 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 5) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 5 * ∏ p ∈ P, p)
    (hm : m % 2 = 1) : (m.primeFactors.filter (fun p => p % 3 = 2)).card ≤ 4 := by
  have h := odd_ledger (j := 0) (T := m.primeFactors.filter (fun p => p % 3 = 2)) (X := ∅)
    hP h3P E hm
    (fun p hp => ⟨Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1,
      (Finset.mem_filter.mp hp).2, Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hp).1⟩)
    (Finset.empty_subset _) (fun x hx => absurd hx (Finset.notMem_empty x)) (by simp)
  omega

-- e = 7: the same bound, since 137 and 23 (from 3^7 + 1 = 4 * 547, 548 = 4 * 137, 138 = 6 * 23)
-- already use two factors of 3.
theorem odd_count_e7 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 7) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 7 * ∏ p ∈ P, p)
    (hm : m % 2 = 1) : (m.primeFactors.filter (fun p => p % 3 = 2)).card ≤ 4 := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 7 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g547 : 547 ∈ P := S7 547 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g137 : 137 ∈ P := S1 137 (by norm_num) (by norm_num) (hnz (by norm_num)) 547 g547 (by norm_num)
  have g23 : 23 ∈ P := S1 23 (by norm_num) (by norm_num) (hnz (by norm_num)) 137 g137 (by norm_num)
  have h := odd_ledger (j := 2) (T := m.primeFactors.filter (fun p => p % 3 = 2))
    (X := {137, 23}) hP h3P E hm
    (fun p hp => ⟨Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1,
      (Finset.mem_filter.mp hp).2, Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hp).1⟩)
    (by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact g137
      · exact g23)
    (by
      intro x hx hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact S4 137 (by norm_num) (by norm_num) (hnz (by norm_num)) hd 547 g547 (by norm_num)
      · exact S4 23 (by norm_num) (by norm_num) (hnz (by norm_num)) hd 137 g137 (by norm_num))
    (by norm_num [Finset.prod_insert])
  omega

-- Small a.  One more simple prime q with 2^i dividing q + 1 joins the 2-adic count.
theorem two_cons {j i q : ℕ} {P S : Finset ℕ}
    (h : S ⊆ P ∧ 2 ^ j ∣ ∏ p ∈ S, (p + 1)) (hq : q ∈ P) (hqS : q ∉ S)
    (h2 : 2 ^ i ∣ q + 1) :
    insert q S ⊆ P ∧ 2 ^ (j + i) ∣ ∏ p ∈ insert q S, (p + 1) := by
  refine ⟨Finset.insert_subset hq h.1, ?_⟩
  rw [Finset.prod_insert hqS, pow_add, mul_comm]
  exact mul_dvd_mul h2 h.2

-- The left side of the balance equation holds exactly a + 1 factors of 2; 3^e + 1 gives two.
theorem two_budget {m e j : ℕ} {P S : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (h4 : 4 ∣ 1 + 3 ^ e) (h : S ⊆ P ∧ 2 ^ j ∣ ∏ p ∈ S, (p + 1)) (hj : m ≤ j) : False := by
  have h3 : ¬ 2 ∣ 3 ^ e := fun hd => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two Nat.prime_three).mp
      (Nat.prime_two.dvd_of_dvd_pow hd)
    omega
  apply not_two_pow_dvd hP h3 E
  have h1 : 2 ^ (m + 2) ∣ 2 ^ (j + 2) := pow_dvd_pow 2 (by omega)
  have h2 : 2 ^ (j + 2) ∣ (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) := by
    rw [pow_add, mul_comm]
    exact mul_dvd_mul h4 (h.2.trans (Finset.prod_dvd_prod_of_subset _ _ (fun p => p + 1) h.1))
  rw [mul_assoc]
  exact (h1.trans h2).mul_left _

-- a <= 9, a = 11 and a = 13 are impossible: the primes forced by 2^a + 1 (and a base set B with
-- 2^6 dividing its product of p + 1) already hold too many factors of 2.
theorem small_core {m e : ℕ} {P B : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (E : (2 ^ m + 1) * (1 + 3 ^ e) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ e * ∏ p ∈ P, p)
    (h4 : 4 ∣ 1 + 3 ^ e) (hB : B ⊆ P ∧ 2 ^ 6 ∣ ∏ p ∈ B, (p + 1))
    (n5 : 5 ∉ B) (n11 : 11 ∉ B) (n19 : 19 ∉ B) (n43 : 43 ∉ B) (n257 : 257 ∉ B) (n683 : 683 ∉ B)
    (n2731 : 2731 ∉ B) (hsmall : m ≤ 9 ∨ m = 11 ∨ m = 13) : False := by
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ e → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have tail19 : 19 ∈ P → ∀ {j : ℕ} {S : Finset ℕ}, (S ⊆ P ∧ 2 ^ j ∣ ∏ p ∈ S, (p + 1)) →
      19 ∉ S → 5 ∉ S → m ≤ j + 3 → False := by
    intro g19 j S hS a19 a5 hj
    have g5 : 5 ∈ P := S1 5 (by norm_num) (by norm_num) (hnz (by norm_num)) 19 g19 (by norm_num)
    have c1 := two_cons hS g19 a19 (by norm_num : 2 ^ 2 ∣ 19 + 1)
    have c2 := two_cons c1 g5 (by simp [a5]) (by norm_num : 2 ^ 1 ∣ 5 + 1)
    exact two_budget hP E h4 c2 (by omega)
  have tail43 : 43 ∈ P → ∀ {j : ℕ} {S : Finset ℕ}, (S ⊆ P ∧ 2 ^ j ∣ ∏ p ∈ S, (p + 1)) →
      43 ∉ S → 11 ∉ S → m ≤ j + 4 → False := by
    intro g43 j S hS a43 a11 hj
    have g11 : 11 ∈ P := S1 11 (by norm_num) (by norm_num) (hnz (by norm_num)) 43 g43 (by norm_num)
    have c1 := two_cons hS g43 a43 (by norm_num : 2 ^ 2 ∣ 43 + 1)
    have c2 := two_cons c1 g11 (by simp [a11]) (by norm_num : 2 ^ 2 ∣ 11 + 1)
    exact two_budget hP E h4 c2 (by omega)
  have tail683 : 683 ∈ P → ∀ {j : ℕ} {S : Finset ℕ}, (S ⊆ P ∧ 2 ^ j ∣ ∏ p ∈ S, (p + 1)) →
      683 ∉ S → 19 ∉ S → 5 ∉ S → m ≤ j + 5 → False := by
    intro g683 j S hS a683 a19 a5 hj
    have g19 : 19 ∈ P := S1 19 (by norm_num) (by norm_num) (hnz (by norm_num)) 683 g683 (by norm_num)
    have c1 := two_cons hS g683 a683 (by norm_num : 2 ^ 2 ∣ 683 + 1)
    exact tail19 g19 c1 (by simp [a19]) (by simp [a5]) (by omega)
  rcases hsmall with h | rfl | rfl
  · interval_cases m
    · exact two_budget hP E h4 hB (by norm_num)
    · exact two_budget hP E h4 hB (by norm_num)
    · exact two_budget hP E h4 hB (by norm_num)
    · exact two_budget hP E h4 hB (by norm_num)
    · exact two_budget hP E h4 hB (by norm_num)
    · exact two_budget hP E h4 hB (by norm_num)
    · exact two_budget hP E h4 hB (by norm_num)
    · exact tail43 (S2 43 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)) hB n43 n11
        (by norm_num)
    · have g257 : 257 ∈ P := S2 257 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
      have g43 : 43 ∈ P := S1 43 (by norm_num) (by norm_num) (hnz (by norm_num)) 257 g257 (by norm_num)
      have c1 := two_cons hB g257 n257 (by norm_num : 2 ^ 1 ∣ 257 + 1)
      exact tail43 g43 c1 (by simp [n43]) (by simp [n11]) (by norm_num)
    · exact tail19 (S2 19 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)) hB n19 n5
        (by norm_num)
  · exact tail683 (S2 683 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)) hB n683 n19
      n5 (by norm_num)
  · have g2731 : 2731 ∈ P := S2 2731 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
    have g683 : 683 ∈ P := S1 683 (by norm_num) (by norm_num) (hnz (by norm_num)) 2731 g2731 (by norm_num)
    have c1 := two_cons hB g2731 n2731 (by norm_num : 2 ^ 2 ∣ 2731 + 1)
    exact tail683 g683 c1 (by simp [n683]) (by simp [n19]) (by simp [n5]) (by norm_num)

-- Pure arithmetic: below 262 the sieve leaves only a <= 9, a = 11, a = 13.
theorem small_of_sieve {m : ℕ} (hlt : m < 262)
    (hs : ∀ d, 10 ≤ d → d ≤ 257 → d ∉ ({11, 13} : Finset ℕ) → m % (2 * d) ≠ d) :
    m ≤ 9 ∨ m = 11 ∨ m = 13 := by
  by_contra hc
  by_cases h1 : m ≤ 257
  · refine hs m (by omega) h1 ?_ (Nat.mod_eq_of_lt (by omega))
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  · rcases (by omega : m = 258 ∨ m = 259 ∨ m = 260 ∨ m = 261) with rfl | rfl | rfl | rfl
    · exact hs 86 (by norm_num) (by norm_num) (by decide) (by norm_num)
    · exact hs 37 (by norm_num) (by norm_num) (by decide) (by norm_num)
    · exact hs 20 (by norm_num) (by norm_num) (by decide) (by norm_num)
    · exact hs 29 (by norm_num) (by norm_num) (by decide) (by norm_num)

-- e = 5: a >= 262.
theorem lower_e5 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 5) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 5 * ∏ p ∈ P, p) :
    262 ≤ m := by
  by_contra hlt
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 5 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g61 : 61 ∈ P := S7 61 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g31 : 31 ∈ P := S1 31 (by norm_num) (by norm_num) (hnz (by norm_num)) 61 g61 (by norm_num)
  have b0 : (∅ : Finset ℕ) ⊆ P ∧ 2 ^ 0 ∣ ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
    ⟨Finset.empty_subset _, by simp⟩
  have b1 := two_cons b0 g61 (by simp) (by norm_num : 2 ^ 1 ∣ 61 + 1)
  have b2 := two_cons b1 g31 (by simp) (by norm_num : 2 ^ 5 ∣ 31 + 1)
  exact small_core hP E (by norm_num) b2 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (small_of_sieve (by omega) (sieve_e5 hP h3P E))

-- e = 7: a >= 262.
theorem lower_e7 {m : ℕ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (h3P : 3 ∉ P)
    (E : (2 ^ m + 1) * (1 + 3 ^ 7) * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 3 ^ 7 * ∏ p ∈ P, p) :
    262 ≤ m := by
  by_contra hlt
  have hK : ∀ c : ℕ, c.Prime → c ∣ 3 ^ 7 → c ∈ ({3} : Finset ℕ) :=
    prime_dvd_prime_pow (by norm_num)
  have hnz : ∀ {c : ℕ}, c ≠ 3 → c ∉ ({3} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, S5, S6, S7, S8⟩ := facts hP hK E
  have g547 : 547 ∈ P := S7 547 (by norm_num) (by norm_num) (hnz (by norm_num)) (by norm_num)
  have g137 : 137 ∈ P := S1 137 (by norm_num) (by norm_num) (hnz (by norm_num)) 547 g547 (by norm_num)
  have g23 : 23 ∈ P := S1 23 (by norm_num) (by norm_num) (hnz (by norm_num)) 137 g137 (by norm_num)
  have b0 : (∅ : Finset ℕ) ⊆ P ∧ 2 ^ 0 ∣ ∏ p ∈ (∅ : Finset ℕ), (p + 1) :=
    ⟨Finset.empty_subset _, by simp⟩
  have b1 := two_cons b0 g547 (by simp) (by norm_num : 2 ^ 2 ∣ 547 + 1)
  have b2 := two_cons b1 g137 (by simp) (by norm_num : 2 ^ 1 ∣ 137 + 1)
  have b3 := two_cons b2 g23 (by simp) (by norm_num : 2 ^ 3 ∣ 23 + 1)
  exact small_core hP E (by norm_num) b3 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (small_of_sieve (by omega) (sieve_e7 hP h3P E))

-- The step.
theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1.H1 := by
  rintro ⟨A1, h1⟩ ⟨A2, h2⟩
  refine ⟨max A1 A2, fun n h hiff he _ => ?_⟩
  have hn0 : n ≠ 0 := h.2.ne'
  have hs : ∀ r ∈ n.primeFactors, r ≠ 2 → r ≠ 3 → n.factorization r = 1 := by
    intro r hr hr2 hr3
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hpos := hrp.factorization_pos_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hr)
    have : ¬ 2 ≤ n.factorization r := fun he =>
      hr3 ((hiff r).mp ⟨hrp, hr2, (hrp.pow_dvd_iff_le_factorization hn0).mpr he⟩)
    omega
  have h3n : 3 ∣ n := Nat.dvd_of_factorization_pos (by rcases he with he | he <;> omega)
  have h3pf : 3 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3n, hn0⟩
  have ha : n.factorization 2 = padicValNat 2 n := Nat.factorization_def n Nat.prime_two
  obtain ⟨hP, E⟩ := kernel_balance_one h h3pf (by norm_num) hs
  have h3P : 3 ∉ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({3} : Finset ℕ)) := by simp
  rcases he with he | he
  · rw [he] at E
    have s1 := sieve_e5 hP h3P E
    have s2 := fermat_e5 hP h3P E
    have s3 := odd_count_e5 hP h3P E
    have s4 := lower_e5 hP h3P E
    rw [ha] at s1 s2 s3 s4
    exact (h1 n h hiff he s4 s1 s2 s3).trans (le_max_left _ _)
  · rw [he] at E
    have s1 := sieve_e7 hP h3P E
    have s2 := fermat_e7 hP h3P E
    have s3 := odd_count_e7 hP h3P E
    have s4 := lower_e7 hP h3P E
    rw [ha] at s1 s2 s3 s4
    exact (h2 n h hiff he s4 s1 s2 s3).trans (le_max_right _ _)

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H1_R1_H1_R1

